
#include "proofchecking.h"

#include "logic/pretty.h"
#include "logic/replacements.h"
#include "logic/counters.h"
#include "logic/structural.h"
#include "logic/cmp.h"
#include "logic/counters.h"

#include "expander.h"
#include "localexpander.h"
#include "projection.h"
#include "outermost.h"
#include "traverse.h"
#include "flatten.h"
#include "saturation.h"
#include "calc/structural.h"
#include "weights.h"

#include "printing.h"

#include "logic/termoperators.h"

std::ostream& calc::operator << ( std::ostream& out, bar b ) 
{
   for( size_t i = 0; i != b. len; ++ i )
      out << '-';
   return out;
}

bool calc::subsumes( const logic::term& tm1, const logic::term& tm2 )
{
   return equal( tm1, tm2 );
}

namespace
{

   template< typename F > F lift( F f, size_t dist )
   {
      // std::cout << "lifting " << f << " over distance " << dist << "\n";
      if( dist != 0 )
      {
         auto lift = logic::lifter( dist );
         return outermost( lift, std::move(f), 0 );
      }
      else
         return f;
   }

   template< typename F > 
   F normalize( const logic::beliefstate& blfs, F f, size_t dist )
   {
      logic::betareduction beta;
      logic::decurrier dec;
      calc::projection proj( blfs );

      do
      {
         beta. used = 0;
         f = outermost( beta, std::move(f), dist );

         dec. used = 0;
         f = outermost( dec, std::move(f), dist ); 

         proj. used = 0;
         f = outermost( proj, std::move(f), dist );
      }
      while( beta. used || proj. used || dec. used );

      return f;
   }

}

std::optional< logic::type >
calc::checktype( const logic::beliefstate& blfs,
                 logic::term& tm, sequent& seq, errorstack& err )
{
   size_t ss = seq. ctxt. size( );

   auto tp = checkandresolve( blfs, err, seq. ctxt, tm );

   if( seq. ctxt. size( ) != ss )
      throw std::logic_error( "context not restored" );

   return tp; 
}


void
calc::checkproof( const logic::beliefstate& blfs, sequent& seq, 
                  proofterm& prf, errorstack& err,
                  logic::exact::unordered_set& dependencies )
{
   std::cout << "checkproof: " << prf. sel( ) << "\n";

   switch( prf. sel( ))
   {

#if 0
#if 0
            // Was part of testing. Should be completely removed later:

            seq. ctxt_assume( "hhhh", logic::type( logic::type_form ));
            seq. ctxt_assume( "ssss", logic::type( logic::type_obj ));

            seq. ugly( std::cout );  
            std::cout << "\n";
#endif

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

            // concl is now a forall without variables, 
            // containing a disjunction:

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

   case prf_cut:
      {
         auto cut = prf. view_cut( );

         auto fm = cut. extr_fm( );  

         auto tp = checktype( blfs, fm, seq, err );
         if( !tp. has_value( ))
            return; 

         if( tp. value( ). sel( ) != logic::type_form )
         {
            errorstack::builder bld;
            auto prnt = pretty_printer( bld, blfs ); 
            prnt << "Type of cut formula is not F, instead it is ";
            prnt << tp. value( );
            err. push( std::move( bld ));
            return;
         }

         auto f1 = logic::term( logic::op_not, 
                      logic::term( logic::op_prop, fm ));
         auto f2 = logic::term( logic::op_not, fm );

         seq. append( 
            disjunction{ exists(f1), exists(f2), exists(fm) } );
         return;
      }

   case prf_chain:
      {
         auto ch = prf. view_chain( );

         for( size_t i = 0; i != ch. size( ); ++ i )
         {
            auto prf = ch. extr_sub(i);
            checkproof( blfs, seq, prf, err, dependencies );
         } 

         return; 
      }

   case prf_flatten: 
      {
         auto flat = prf. view_flatten( ); 

         size_t ind = seq. find( flat. fm( ));
         if( ind == seq. stack. size( ))
         {
            errorstack::builder bld;
            auto prnt = pretty_printer( bld, blfs );
            seq. pretty( prnt );
            prnt << "flatten: unknown formula label " << flat. fm( );
            err. push( std::move( bld ));
            return;  
         }

         // If it is UNF, we know that it is non-trivial. 
         // Hence, we can only flatten into UNF.

         if( seq. at( ind ). is_dnf( ))
         {
            auto f1 = lift( seq. at( ind ). get_dnf( ), 
                            seq. liftdist( ind ));

            auto f2 = flatten(f1);

            if( f1. size( ) != f2. size( ) || !subsumes( f2, f1 ))
            {
               // Note that this is problematic. It relies on 
               // weakness of subsumption. There should be some kind of 
               // weight function based on offending operators.
               // Equality will probably also work. 

               seq. hide( ind );  
               seq. append( std::move(f2) ); 
               return;
            }

            // If f1 is trivial, it might be possible to transform into
            // CNF. I believe this should be put in separate functions.

            if( f1. size( ) == 1 && 
                f1. at(0). vars. size( ) == 0 )
            {
               auto cnf1 = conjunction( { forall( f1. at(0). body ) } );
               auto cnf2 = flatten( cnf1 );

               if( cnf1. size( ) != cnf2. size( ) || !subsumes( cnf2, cnf1 ))
               {
                  seq. hide( ind );
                  seq. append( cnf2 ); 
                  return;    
               } 
#if 0
            // It will simplify into A, which is still trivial.
            // I think one must register the complexity.
#if 0
            if( istrivial(f))
            {
               cnf = flatten( std::move( cnf )); 
               if( !istrivial( cnf ))
               {
                  seq. hide( ind ); 
                  // seq. append( std::move( cnf ));
                  return;
               } 
#endif
#endif 
            }
#if 0
            f = flatten( std::move(f) );
            
            seq. hide( ind );
            return;
#endif 
         }

         if( seq. at( ind ). is_unf( ))
            throw std::logic_error( "this case is not handled" );

         throw std::logic_error( "unreachable" );
      }


#if 0

#if 0
   case prf_copy:
      {
         auto copy = prf. view_copy( );

         // This is not terribly efficient, but I think
         // that the number of segments in a proof is logarithmic in its
         // size.

         for( size_t seg = 0; seg != seq. size( ); ++ seg )
         {
            if( seq. at( seg ). name == copy. segname( ))
            { 
               if( !seq. at( seg ). inrange( copy. ind( )))
                  throw std::logic_error( "copy: wrong index" );

               auto fm = seq. at( seg ). at( copy. ind( ));
                  // Copy, not move!

               seq. back( ). push( lift( std::move( fm ),
                                      seq. ctxt. size( ) -
                                      seq. at( seg ). contextsize ));

               return;  // succesful return. 
            }
         }
         throw std::logic_error( " not found " );
      }

#endif
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
         auto repl = prf. view_orrepl( );

         size_t ind = seq. find( repl. disj( ));
         if( ind == seq. stack. size( ))
         {
            errorstack::builder bld;
            bld << "orrepl: Unknown label for disjunction " << repl. disj( );
            err. push( std::move( bld ));
            return; 
         }

         if( !seq. formula( ind ). is_dnf( ))
         { 
            errorstack::builder bld;
            auto prnt = pretty_printer( bld, blfs ); 
            prnt << "orrepl: Formula not disjunction " << seq. formula( ind );
            err. push( std::move( bld ));
            return;
         }

         size_t alt = repl. alt( );
         if( alt >= seq. formula( ind ). get_dnf( ). size( ))
         {
            errorstack::builder bld;
            auto prnt = pretty_printer( bld, blfs ); 
            prnt << "orrepl: Alternative does not exist "; seq. formula( ind );
            prnt << " ( " << alt << " )";
            err. push( std::move( bld ));
            return;
         }

         // Now we are certain that the rule can be applied.

         // Take the disjunction, and lift it:

         auto disj = seq. formula( ind ). get_dnf( );
         disj = lift( std::move( disj ), seq. liftdist( ind ));
         std::cout << "lifted disjunction = " << disj << "\n";

         auto chosen = std::move( disj. at( alt ));
         std::cout << "chosen: " << chosen << "\n"; 

         size_t lev = seq. nrlevels( ); 
         seq. appendlevel( );

         seq. append( disjunction( { std::move( chosen ) } ));

         seq. hide( ind );
            // We can hide the parent disjunction, since it is 
            // subsumed by chosen.

         for( size_t i = 0; i != repl. size( ); ++ i )
         {
            auto prf = repl. extr_sub(i);
            checkproof( blfs, seq, prf, err, dependencies ); 
            repl. update_sub( i, std::move( prf )); 
         }

         if( lev + 1 != seq. nrlevels( ))
            throw std::logic_error( "levels are not right" );

         if( seq. lastlevel( ). stacksize >= seq. stack. size( ))
         {
            errorstack::builder bld;
            bld << "disjunction elimination has no result"; 
            err. push( std::move( bld ));
            return; 
         }

         if( !seq. back( ). is_dnf( ))
         {
            errorstack::builder bld;
            auto prnt = pretty_printer( bld, blfs );
            prnt << "orrepl: Last formula not disjunction " << seq. back( );
            err. push( std::move( bld ));
            return;
         }

         decltype( disj ) result;
         std::cout << disj << "\n";
         for( size_t i = 0; i != disj. size( ); ++ i )
         {
            if( i != alt ) 
               result. append( disj. at(i));
         }

         for( auto& lit : seq. back( ). get_dnf( ) ) 
         {
            if( !subsumes( lit, result ))
               result. append( std::move( lit ));
         }

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
         auto repl = prf. view_existsrepl( ); 
         auto ind = seq. find( repl. fm( ));

         if( ind == seq. stack. size( )) 
         {
            errorstack::builder bld;
            bld << "existsrepl: Unknown label for existential ";
            bld << repl. fm( );
            err. push( std::move( bld ));
            return;
         }

         if( !seq. at( ind ). is_dnf( ) ||
              seq. at( ind ). get_dnf( ). size( ) != 1 )
         {
            errorstack::builder bld;
            bld << "exists: " << repl. fm( ) << " : ";
            bld << "formula not existential";
            err. push( std::move( bld ));
            return;
         }

         enf< logic::term > mainform = seq. at( ind ). get_dnf( ). at(0); 
         mainform = lift( std::move( mainform ), seq. liftdist( ind ));

         size_t cc = seq. ctxt. size( );
         size_t ff = seq. stack. size( );
         size_t ll = seq. nrlevels( );

         // Assume the existentially quantified variables of alt:

         if( mainform. vars. size( ) != repl. eigen( ). size( ))
         {
            errorstack::builder bld;
            bld << "exists: " << repl. fm( ) << " : ";
            bld << "number of eigenvariables is not right: ";
            bld << "it is " << repl. eigen( ). size( );
            bld << ", but it must be " << mainform. vars. size( );  
            err. push( std::move( bld ));
            return;
         }

         for( size_t v = 0; v != mainform. vars. size( ); ++ v )
         {
            if( repl. eigen( ). at(v). size( ) != 0 ) 
            {
               seq. ctxt. assume( repl. eigen( ). at(v), 
                                  mainform. vars[v]. tp );
            }
            else
               seq. ctxt. assume( "_", mainform. vars[v]. tp );
         }

         seq. hide( ind );

         // Assume the body of alt (without the variables):
 
         seq. append( disjunction( { exists( mainform. body ) } ));

         {
            auto prt = pretty_printer( std::cout, blfs );
            seq. pretty( prt );
         }

         // Check the subproof:

         for( size_t i = 0; i != repl. size( ); ++ i )
         {
            auto subproof = repl. extr_sub(i);
            checkproof( blfs, seq, subproof, err, dependencies );
            repl. update_sub( i, std::move( subproof ));
         }

         if( ll != seq. nrlevels( ))
            throw std::logic_error( "something went wrong with the levels" );

         for( size_t ind = ff; ind != seq. stack. size( ); ++ ind )
         {
            if( seq. at( ind ). ctxtsize != seq. ctxt. size( ))
               throw std::logic_error( "existsrepl: wrong context size" );

            // Formulas that are not DNF, we make trivial:

            if( seq. at( ind ). is_dnf( ))
            {
               auto& dnf = seq. at( ind ). get_dnf( );

               // For each disjunct separately,
               // we determine its free variables, and
               // add existential quantifiers for them.

               for( size_t i = 0; i != dnf. size( ); ++ i )
               {
                  // We need construct a substitution that normalizes
                  // the free variables in concl. body. at(i).

                  // we first collect the free variables of dnf. at(i) :

                  logic::debruijn_counter vars;
                  traverse( vars, seq. at( ind ). get_dnf( ). at(i), 0 );
 
                  // We don't care about all free variables, only about the 
                  // ones that we assumed just now. 
                  // We go through our assumptions, check if they occur
                  // in vars. We create a normalizing subsitution for those. 

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

   case prf_expand:
      {
         auto exp = prf. view_expand( ); 
  
         // The expander checks if exp. ident( ) has a definition
         // for the types with which it is used.
 
         expander def( exp. ident( ), exp. occ( ), blfs, err );
            // We are using unchecked identifier exp. ident( ).
            // The expander will look only at exact overloads. 
            // This guarantees type safety.

         std::cout << def << "\n";

         auto ind = seq. find( exp. fm( ));
         if( ind == seq. stack. size( ))
         {
            errorstack::builder bld;
            auto prnt = pretty_printer( bld, blfs );
            // seq. pretty( prnt );
            prnt << "expand: unknown label " << exp. fm( );
            err. push( std::move( bld ));
            return;
         }

         if( seq. at( ind ). is_dnf( ))
         {
            auto res = seq. at( ind ). get_dnf( );
            res = lift( std::move( res ), seq. liftdist( ind )); 
            res = outermost( def, std::move( res ), 0 );
            seq. hide( ind );
            seq. append( res );
            return;
         } 

         if( seq. at( ind ). is_unf( ))
         {
            std::cout << "it is a UNF\n";
         }

         throw std::logic_error( "should be unreachable: expand " );
         return;
      }

   case prf_expandlocal:
      {
         auto exp = prf. view_expandlocal( );
         auto var = exp. var( );

         if( !seq. ctxt. hasdefinition( var ))
         {
            errorstack::builder bld; 
            auto prnt = pretty_printer( bld, blfs );
            prnt << "expandlocal: variable " << var;
            prnt << " does not have a definition"; 
            err. push( std::move( bld ));
            return;
         }

         auto def = localexpander( var,  
                                   seq. ctxt. getdefinition( var ), 
                                   prf. view_expandlocal( ). occ( ));
    
         auto ind = seq. find( exp. fm( ));
         if( ind == seq. stack. size( )) 
         {
            errorstack::builder bld;
            auto prnt = pretty_printer( bld, blfs );
            // seq. pretty( prnt );
            prnt << "unknown formula label " << exp. fm( ); 
            err. push( std::move( bld )); 
            return; 
         }

         // Now we need to look at the type of formula at hand:

         if( seq. at( ind ). is_dnf( )) 
         {
            auto d = seq. at( ind ). get_dnf( );
            d = lift( std::move(d), seq. liftdist( ind ));
            std::cout << "after the lift " << d << "\n";
            seq. hide( ind );
            seq. append( outermost( def, std::move(d), 0 ));
            return;
         }

         if( seq. at( ind ). is_unf( ))
         {
            throw std::logic_error( "unf: unfinished" ); 

         }

         seq. ugly( std::cout );
         throw std::logic_error( "should be unreachable" );
      }

   case prf_normalize:
      { 
         auto norm = prf. view_normalize( );

         size_t ind = seq. find( norm. fm( ));
         if( ind == seq. stack. size( ))
         {
            errorstack::builder bld;
            auto prnt = pretty_printer( bld, blfs );
            seq. pretty( prnt );
            prnt << "normalize: unknown formula label " << norm. fm( );
            err. push( std::move( bld ));
            return;
         }

         if( seq. at( ind ). is_dnf( ))
         {
            auto d = seq. at( ind ). get_dnf( );
            d = lift( std::move(d), seq. liftdist( ind ));
            seq. hide( ind );
            seq. append( normalize( blfs, std::move(d), 0 ));
            return;
         }

         throw std::logic_error( "normalize not finished" );
         return;
      }

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
   case prf_forallelim:
      {
         auto elim = prf. view_forallelim( );
         auto ind = seq. find( elim. fm( ));
   
         if( ind == seq. stack. size( ))  
         {
            errorstack::builder bld;
            bld << "forallelim: Unknown label for universal ";
            bld << elim. fm( );
            err. push( std::move( bld ));
            return;
         }
         
         if( !seq. at( ind ). is_unf( ))
         {     
            errorstack::builder bld;
            bld << "forallelim " << elim. fm( ) << " : ";
            bld << "formula is not universal";
            err. push( std::move( bld ));
            return;
         }     

         if( seq. at( ind ). get_unf( ). vars. size( ) < elim. size( ))
         {
            errorstack::builder bld;
            bld << "forallelim " << elim. fm( ) << " : ";
            bld << "There are " << elim. size( ) << " instances, ";
            bld << "while the formula has only ";
            bld << seq. at( ind ). get_unf( ). vars. size( ) << " variables";
            return; 
         }

         auto mainform = seq. at( ind ). get_unf( );
         mainform = lift( std::move( mainform ), seq. liftdist( ind ));
         
         size_t errstart = err. size( );
         logic::fullsubst subst;

         size_t cc = seq. ctxt. size( );

         size_t nrcorrecttypes = 0;
         for( size_t i = 0; i != elim. size( ); ++ i )
         {
            std::cout << "i = " << i << "\n";
            auto inst = elim. extr_inst(i);
            auto tp = checktype( blfs, inst, seq, err );

            if( tp. has_value( ))
            {
               if( equal( tp. value( ), mainform. vars[i]. tp ))
               {
                  subst. append( std::move( inst )); 
                  ++ nrcorrecttypes;
               }
               else
               {
                  auto bld = errorstack::builder( ); 
                  auto prt = pretty_printer( bld, blfs );
                  prt << "true type of instance " << inst << " is wrong\n";
                  prt << "It is " << tp. value( ) << ", but it must be ";
                  prt << mainform. vars. at(i). tp;
                  err. push( std::move( bld ));
               }
            }
            else
               std::cout << "had no value\n";
         }

         if( nrcorrecttypes != elim. size( ))
         {
            auto bld = errorstack::builder( );
            bld << "unable to instantiate";
            err. push( std::move( bld ));
            return;
         }

         // We do not remove the outermost forall, because its 
         // presence is required by the data structure. 
         // We remove the variables It is allowed that some variables remain. 

         mainform. vars. erase( mainform. vars. begin( ),
                                mainform. vars. begin( ) + elim. size( ));

         mainform = outermost( subst, std::move( mainform ), 0 ); 

         // We append mainform as CNF. The append function will 
         // convert formula into a DNF is the quantification is empty.
      
         seq. hide( ind );  
         seq. append( conjunction( { mainform } ));
         return;  
      }
#if 0
   case prf_deflocal: 
      {
         auto def = prf. view_deflocal( );
         auto val = def. extr_val( );

         std::cout << "val = " << val << "\n";
         auto tp = checktype( blfs, val, seq, err );

         if( !tp. has_value( ))
            throw std::logic_error( "def local, no type" );

         def. update_val( val );

         size_t cc = seq. ctxt. size( );
         size_t ff = seq. stack. size( );
         size_t ll = seq. nrlevels( );

         seq. ctxt_define( def. name( ), val, tp. value( ));

         for( size_t i = 0; i != def. size( ); ++ i )
         {
            auto sub = def. extr_sub(i); 
            checkproof( blfs, sub, seq, err );
            def. update_sub( i, std::move( sub ));
         }

         // We need to apply the substitution:

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

   case prf_import:
      {
         auto imp = prf. view_import( );

         // We need to make the types exact:

         std::vector< logic::type > types;

         bool alltypescorrect = true;

         // In the future, we will have const_iterator:

         for( size_t i = 0; i != imp. size( ); ++ i )
         {
            auto tp = imp. extr_tp(i);
            bool b = checkandresolve( blfs, err, tp );
            if(b)
               types. push_back( tp );
            else
            {
               errorstack::builder bld;
               auto prnt = pretty_printer( bld, blfs ); 
               prnt << "Bad structural type: " << tp; 
               err. push( std::move( bld ));  

               alltypescorrect = false;
            }

            imp. update_tp( i, tp );
         }

         if( !alltypescorrect )
            return; 

         std::optional< logic::exact >
         optex = findformula( blfs, err, imp. ident( ), types );

         if( !optex. has_value( ))
            return;

         const auto& fm = blfs. at( optex. value( )). view_form( ). fm( );

         seq. append( disjunction( { exists( fm ) } ));
         return;  
      }
#if 0 
   case prf_simplify:
      {
         saturation sat; 

         for( size_t i = 0; i != seq. stack. size( ); ++ i )
         {
            const auto& fm = seq. at(i);
            if( !fm. hidden && fm. is_dnf( )) 
               sat. initial( lift( fm. get_dnf( ), seq. liftdist(i)), i );
         }
     
         sat. saturate( );
         std::cout << "after saturation\n";
         std::cout << sat << "\n";

         for( auto& rm : sat. removed_initials )
            seq. hide( rm );

         for( auto& cls : sat. checked ) 
         {
            // We don't add initial ones, because they are already there.

            if( !cls. seqind )
               seq. append( make_dnf( cls. disj ));
         } 
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
#if 0

   case prf_nop:
      {
         return;   // Truly nothing was done. 
      }

#endif
   case prf_show:
      {
         auto show = prf. view_show( ); 

         auto out = pretty_printer( std::cout, blfs );
         out << bar( 75 ) << "\n";
         out << "proof state " << show. comment( ) << ":\n";
         seq. pretty( out );
         out << bar( 75 ) << "\n";
         return;
      } 
   }

   std::cout << prf. sel( ) << "\n";
   throw std::logic_error( "dont know how to check this rule" );
}


