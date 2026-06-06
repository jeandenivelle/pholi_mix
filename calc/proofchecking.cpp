
#include "proofchecking.h"

#include "logic/pretty.h"
#include "logic/replacements.h"
#include "logic/counters.h"
#include "logic/structural.h"
#include "logic/cmp.h"
#include "logic/counters.h"

#include "localexpander.h"
#include "projection.h"
#include "outermost.h"
#include "traverse.h"
#include "saturation.h"
#include "calc/structural.h"
#include "weights.h"

#include "logic/termoperators.h"


#if 0
void
calc::checkproof( const logic::beliefstate& blfs, sequent& seq, 
                  proofterm& prf, errorstack& err,
                  logic::exact::unordered_set& dependencies )
{
   std::cout << "checkproof: " << prf. sel( ) << "\n";

   switch( prf. sel( ))
   {

#if 0
            // We use the last formula. If there are no formulas, 
            // it is an error:

            if( seq. back( ). size( ) == 0 )
            {
               throw std::runtime_error( "orexistselim: No result" );
            }

            auto concl = std::move( seq. back( ). at( -1 ));
               // Conclusion of our current assumption.

            if( concl. vars. size( ))
            {
               std::cout << concl << "\n";
               throw std::runtime_error( "orexistselim: universal variables in conclusion" );
            }


#if 0
            // This was used for testing.

            concl. body = disjunction( 
               {
                  exists( logic::forall( {{ "A", logic::type( logic::type_form ) }}, apply( 5_db, { 3_db, 4_db } ))), 
                  exists( {{ "X", logic::type( logic::type_form ) },
                           { "Y", logic::type( logic::type_obj ) }},
                          apply( "f"_unchecked, { 0_db, 1_db, 2_db, 5_db, 6_db, 7_db } ))
               } );

            std::cout << "concl = " << concl << "\n";
            std::cout << "ss = " << ss << "\n";
#endif

            // concl. body( ) is a disjunction of existentially
            // quantified formulas. For each disjunct separately,
            // we determine its free variables, and 
            // add existential quantifiers for them.

            for( size_t i = 0; i != concl. body. size( ); ++ i )
            {
               // We construct a substitution that normalizes
               // the free variables in concl. body. at(i).

               // In order to do that, we first collect 
               // the free variables of concl. body. at(i) : 
 
               logic::debruijn_counter vars;
               traverse( vars, concl. body. at(i), 0 );

               // We don't care about all free variables, only about the 
               // ones that we assumed by ourselves. 
               // We go through our assumptions, check if they occur
               // in vars. We create a normalizing subsitution for those. 

               auto norm = logic::normalizer( seq. ctxt. size( ) - ss );

               for( size_t v = 0; v + ss < seq. ctxt. size( ); ++ v )
               {
                  if( vars. contains(v))
                     norm. append(v);
               }
 
               // apply norm on the body:

               concl. body. at(i) = 
                  outermost( norm, std::move( concl. body. at(i)), 0 );

               std::vector< logic::vartype > quant;

               // These are the assumptions that we are about to drop:

               for( size_t v = seq. ctxt. size( ) - ss; v -- ; )
               {
                  if( vars. contains(v))
                     quant. push_back( { seq. ctxt. getname(v),
                                         seq. ctxt. gettype(v) } );                          
               }

               for( auto& q : concl. body. at(i). vars )
                  quant. push_back( std::move(q));

               concl. body. at(i). vars = std::move( quant );
            }

            if( seq. size( ) != nrsegments + 1 )
               throw std::logic_error( "something went wrong with the segments" );

            seq. pop_back( );
            seq. ctxt_restore( ss );

            // concl still is a forall without variables:

            for( auto& d : concl. body )
               result. append( std::move(d));
         }

         // If there are more disjunctions than cases in the proof,
         // we copy the missing disjuncts unchanged:

         if( elim. size( ) < disj. size( ))
         {
            std::cout << elim. size( ) << " " << disj. size( ) << "\n";

            for( size_t i = elim. size( ); i < disj. size( ); ++ i )
               result. append( std::move( disj. at(i)) );
         }

         atp::simplify( result );

         seq. back( ). push( forall( std::move( result )));

         return; 
      }
#endif 


#if 0
   case prf_hide: 
      {
         auto hd = prf. view_hide( );
         if( !seq. hasindex( hd. ind( )))
            throw std::logic_error( "hide: wrong index" );

         seq. hide( hd. ind( ));
         return;
      }

#endif

   case prf_orrepl:
      {
         std::cout << "result = " << result << "\n";
         seq. poplevel( ); 

         if( subsumes( result, seq. formula( ind ). get_dnf( )) )
            seq. hide( ind ); 

         seq. append( std::move( result ));
         seq. ugly( std::cout );  
         return;
      }

   case prf_existsrepl:
      {

         for( size_t ind = ff; ind != seq. stack. size( ); ++ ind )
         {
            if( seq. at( ind ). is_dnf( ))
            {
               auto& dnf = seq. at( ind ). get_dnf( );

               for( size_t i = 0; i != dnf. size( ); ++ i )
               {
                  // We need construct a substitution that normalizes
                  // the free variables in concl. body. at(i).

                  // we first collect the free variables of dnf. at(i) :

                  logic::debruijn_counter vars;
                  traverse( vars, seq. at( ind ). get_dnf( ). at(i), 0 );
 
                  auto norm = logic::normalizer( seq. ctxt. size( ) - cc );

                  for( size_t v = 0; v + cc < seq. ctxt. size( ); ++ v )
                  {
                     if( vars. contains(v))
                        norm. append(v);
                  }
 
                  // apply norm to the body:

                  dnf. at(i) = 
                     outermost( norm, std::move( dnf. at(i)), 0 );

                  // We collect the quantification of the variables
                  // that are still there.

                  std::vector< logic::vartype > quant;

                  // These are the assumptions that we are about to drop:

                  for( size_t v = seq. ctxt. size( ) - cc; v -- ; )
                  {
                     if( vars. contains(v))
                        quant. push_back( { seq. ctxt. getname(v),
                                         seq. ctxt. gettype(v) } );                          
                  }

                  for( auto& q : dnf. at(i). vars )
                     quant. push_back( std::move(q));

                  dnf. at(i). vars = std::move( quant );
               }
            }
            else
            {
               seq. maketrivial( ind );
               seq. hide( ind );
            }

            seq. at( ind ). ctxtsize = cc;
               // We decrease the level. 
         }

         {
            auto prt = pretty_printer( std::cout, blfs );
            seq. pretty( prt );
         }

         seq. ctxt. restore( cc );
      }
      return;

#if 0
#if 0
   case prf_forallintro:
      {
         auto intro = prf. view_forallintro( );

         std::vector< logic::exact > exactnames;
            // The names that seq will give to the assumptions.
            // We need them, so that we can subtitute them away later.

         auto seqsize = seq. size( );
         for( size_t i = 0; i != intro. size( ); ++ i )
         {
            logic::exact name = 
               seq. ctxt_assume( intro.var(i).pref, intro.var(i).tp );

            exactnames. push_back( name );
         }
 
         auto res = optform( proofcheck( intro. parent( ), seq, err ), 
                             "forall-intro", seq, err );

         if( !res )
            return { };

         res. musthave( logic::op_kleene_and );
        
         logic::introsubst subst;
         for( const auto& e : exactnames )
            subst. bind(e);

         res. rewr_outermost( subst );

         std::vector< logic::vartype > vars; 
         for( size_t i = 0; i != intro. size( ); ++ i ) 
            vars. push_back( intro. var(i));
 
         res. quantify( vars );
         seq. restore( seqsize );

         return res. value( ); 
      }
#endif
#endif 

#if 0
   case prf_deflocal: 
      {
         seq. ctxt_define( def. name( ), val, tp. value( ));

         for( size_t i = 0; i != def. size( ); ++ i )
         {
            auto sub = def. extr_sub(i); 
            checkproof( blfs, sub, seq, err );
            def. update_sub( i, std::move( sub ));
         }

         // Next we need to apply the substitution:

         if( seq. ctxt. size( ) != cc + 1 )
            throw std::logic_error( "something went wrong with size" );

         if( !seq. ctxt. hasdefinition(0))
            throw std::logic_error( "something went wrong with def" ); 

         if( seq. nrlevels( ) != ll )
            throw std::logic_error( "something went wrong with the levels" );

         auto subst = logic::singlesubst( seq. ctxt. getdefinition(0));
         std::cout << subst << "\n";

         for( size_t i = ff; i != seq. stack. size( ); ++ i )
         {
            auto& f = seq. at(i);
            {
               if( !f. hidden )
               {
                  if( f. is_unf( ))
                  {
                     f. get_unf( ) = 
                          outermost( subst, std::move( f. get_unf( )), 0 );
                  }
                  else
                  {
                     f. get_dnf( ) = 
                          outermost( subst, std::move( f. get_dnf( )), 0 ); 
                  }

               }

               if( f. ctxtsize != cc + 1 )
                  throw std::logic_error( "wrong context size" );

               -- f. ctxtsize; 
            }
         }
 
         seq. ctxt_restore( cc );
         return; 
      }
#endif

   case prf_fake:
      {
         auto trmp = prf. view_fake( ). extr_goal( );
         auto tp = checktype( blfs, trmp, seq, err );

         if( !tp. has_value( ))
            return;  // Error is already created. 

         if( tp. value( ). sel( ) != logic::type_form )
         {
            errorstack::builder bld;
            auto prnt = pretty_printer( bld, blfs ); 
            prnt << "Type of faked formala is not F, instead it is ";
            prnt << tp. value( );
            err. push( std::move( bld ));
            return; 
         }

         std::cout << "faking: " << trmp << "\n";
         seq. append( disjunction( { exists( std::move( trmp )) } ));
         return;
      }

   case prf_nextlabel:
      {
         auto lab = prf. view_nextlabel( ). lab( );
         std::cout << "lab = " << lab << "\n";

         auto ind = seq. find( lab ); 
         if( ind != seq. stack. size( ))
            throw std::logic_error( "already occurs" );
               // Sequent must automatically find an available label.

         seq. nextlabel = lab; 
         return; 
      }
   }

   std::cout << prf. sel( ) << "\n";
   throw std::logic_error( "dont know how to check this rule" );
}

#endif

