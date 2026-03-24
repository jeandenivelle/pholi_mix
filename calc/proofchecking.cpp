
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

#include "printing.h"

#include "logic/termoperators.h"

void calc::printbar( std::ostream& out ) 
{
   for( short unsigned int i = 0; i < 70; ++ i )
      out << '-';
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
   if( seq. ctxt. size( ) != seq. db. size( ))
   {
      std::cout << seq. db << "\n";
      throw std::logic_error( "De Bruijn index wrong size" );
   }

   tm = replace_debruijn( seq. db, std::move(tm) );

   size_t ss = seq. ctxt. size( );
   size_t ee = err. size( );

   auto tp = checkandresolve( blfs, err, seq. ctxt, tm );

   if( seq. ctxt. size( ) != ss )
      throw std::logic_error( "context not restored" );

   if( ee != err. size( ))
      std::cout << ( err. size( ) - ee ) << " errors were created\n";

   if( !tp. has_value( ))
   {
      seq. ugly( std::cout );
      std::cout << "the term is " << tm << "\n";
      throw std::logic_error( "term has no type" ); 
   }

   return tp; 
}

#if 0

// Function should be moved, and also used when a proof is started.

bool 
calc::applicable( const logic::belief& blf, 
                  const std::vector< logic::type > & tps )
{
   if( blf. sel( ) != logic::bel_axiom && 
       blf. sel( ) != logic::bel_thm )
   {
      return false;
   }

   const auto& fm = blf. view_form( );

   if( tps. size( ) > fm. size( ))
      return false;

   for( size_t i = 0; i != tps. size( ); ++ i )
   {
      if( !equal( fm. tp(i), tps. at(i)) )
         return false; 
   }

   return true;
}

#endif

void
calc::checkproof( const logic::beliefstate& blfs,
                  proofterm& prf, sequent& seq, errorstack& err )
{
   std::cout << "checkproof: " << prf. sel( ) << "\n";

   switch( prf. sel( ))
   {

   case prf_flatten: 
      {
         auto flat = prf. view_flatten( ); 
         if( !seq. hasindex( flat. ind( )))
            throw std::logic_error( "flatten: index out of range" );

         // If it is UNF, we know that it is non-trivial. 
         // Hence, we can only flatten into UNF.

         if( seq. at( flat. ind( )). is_dnf( ))
         {
            auto f = lift( seq. at( flat. ind( )). get_dnf( ), 
                           seq. liftdist( flat. ind( )));
            std::cout << "f = " << f << "\n"; 
            if( istrivial(f))
            {
               auto cnf = conjunction( { forall( f. at(0). body ) } );
               cnf = flatten( std::move( cnf )); 
               if( !istrivial( cnf ))
               {
                  seq. hide( flat. ind( )); 
                  seq. append( std::move( cnf ));
                  return;
               } 

            }
            f = flatten( std::move(f) );
            std::cout << "after flattening " << f << "\n";
            if( !istrivial(f))
            {
               seq. hide( flat. ind( ));
               seq. append( std::move(f)); 
               return;
            }

            
         }

#if 0
         auto fm = std::move( seq. back( ). at( flat. ind( )) );
         seq. back( ). erase( flat. ind( )); 

         anf< logic::term > conj;
         conj. append( std::move(fm));
         conj = flatten( std::move( conj ));

         for( auto& c : conj )
            seq. back( ). push( std::move(c) );
#endif
         throw std::logic_error( "this is flatten" );
         return;
      }

#if 0
   case prf_orexistselim:
      {
         auto elim = prf. view_orexistselim( ); 
         auto mainform = std::move( seq. back( ). at( elim. ind( )) );
            // Should be a universally quantified disjunction,
            // without variables.

         std::cout << "mainform = " << mainform << "\n";
         seq. back( ). erase( elim. ind( ));

         if( mainform. vars. size( ))
         {
            std::cout << "orexistselim\n";
            throw std::runtime_error( "there are universal variables" );
         }

         const dnf< logic::term > disj = std::move( mainform. body );
            // It is a disjunction of existential formulas. 

         dnf< logic::term > result;
            // This will be our result.

         size_t ss = seq. ctxt. size( ); 
         size_t nrsegments = seq. size( );

         if( disj. size( ) < elim. size( ))
         {
            std::cout << elim. name( ) << "\n";  
            throw std::runtime_error( "disjunction is too small" );
         }

         for( size_t i = 0; i != elim. size( ); ++ i )
         {
            const auto& sub = disj. at(i);
 
            // Assume the existential variables:
 
            for( size_t v = 0; v != sub. vars. size( ); ++ v )
               seq. assume( sub. vars[v]. pref, sub. vars[v]. tp );

            // Create a new segment in the sequent:

            seq. push_back( elim. name( ));

            seq. back( ). push( forall( disjunction{ exists( sub. body ) } ));
            auto subproof = elim. extr_branch(i);
            checkproof( blfs, subproof, seq, err );
            elim. update_branch( i, std::move( subproof ));

            std::cout << "==============================\n";
            std::cout << "disjunction is " << disj << "\n";
            std::cout << "number options = " << disj. size( ) << "\n";
            std::cout << "choice was: " << i << "\n";

#if 0
            // Was part of testing. Should be completely removed later:

            seq. assume( "hhhh", logic::type( logic::type_form ));
            seq. assume( "ssss", logic::type( logic::type_obj ));

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
            seq. ctxt. restore( ss );

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
   case prf_existsrepl:
      {
         auto repl = prf. view_existsrepl( ); 
         size_t ind = repl. ind( ); 

         if( !seq. hasindex( ind ))
            throw std::logic_error( "existsrepl: index out of range" );

         if( !seq. at( ind ). is_dnf( ))
            throw std::logic_error( "existsrepl: formula is not DNF" );

         if( seq. at( ind ). get_dnf( ). size( ) != 1 )
            throw std::logic_error( "existsrepl: formula not a singleton" ); 

         enf< logic::term > mainform = seq. at( ind ). get_dnf( ). at(0); 

         mainform = lift( std::move( mainform ), seq. liftdist( ind ));
         std::cout << "mainform = " << mainform << "\n\n\n";

         size_t ss = seq. ctxt. size( );

         // Assume the existentially quantified variables of alt:

         for( size_t v = 0; v != mainform. vars. size( ); ++ v )
         {
            if( v < repl. eigen( ). size( ))
               seq. assume( repl. eigen( ). at(v), mainform. vars[v]. tp );
            else
               seq. assume( mainform. vars[v]. pref, mainform. vars[v]. tp );
         }

         seq. hide( ind );

         // Assume the body of alt (without the variables):
 
         seq. append( disjunction( { exists( mainform. body ) } ));

         for( size_t i = 0; i != repl. size( ); ++ i )
         {
            auto subproof = repl. extr_sub(i);
            checkproof( blfs, subproof, seq, err );
            repl. update_sub( i, std::move( subproof ));
         }

#if 0
#if 0
            // Was part of testing. Should be completely removed later:

            seq. assume( "hhhh", logic::type( logic::type_form ));
            seq. assume( "ssss", logic::type( logic::type_obj ));

            seq. ugly( std::cout );  
            std::cout << "\n";
#endif

         // We use the last formula. If there are no formulas, 
         // it is an error:

         if( seq. back( ). size( ) == 0 )
         {
            throw std::runtime_error( "orexistselimintro: No result" );
         }

         auto concl = std::move( seq. back( ). at( -1 ));
            // Conclusion of our current assumption.

         if( concl. vars. size( ))
         {
            std::cout << concl << "\n";
            throw std::runtime_error( "orexistselimintro: universal variables in conclusion" );
         }

         // concl is a forall without variables, 
         // containing a disjunctive normal form.

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
 
#if 0
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
#endif
            throw std::logic_error( "this loop is not finished" );
         }

         if( seq. size( ) != nrsegments + 1 )
            throw std::logic_error( "something went wrong with the segments" );

         seq. pop_back( );
   
         seq. restore( ss );

         atp::simplify( concl. body );

         for( size_t i = 0; i != disj. size( ); ++ i )
         {
            if( i == elim. alt( )) 
            {
               for( auto& b : concl. body )
                  mainform. body. append( std::move(b));
            }
            else
               mainform. body. append( disj. at(i));
         }

         seq. back( ). push( std::move( mainform ));
         return; 
#endif
         throw std::logic_error( "existsrepl is not finished" ); 
      }

   case prf_cut:
      {
         auto cut = prf. view_cut( );

         auto fm = cut. extr_fm( );  

         auto tp = checktype( blfs, fm, seq, err );
         if( !tp. has_value( ) || tp. value( ). sel( ) != logic::type_form )
         {
            std::cout << "wrong type!\n";
            throw std::logic_error( "cut: type is not FORM" ); 
         }
         cut. update_fm( fm );

         auto f1 = logic::term( logic::op_not, 
                      logic::term( logic::op_prop, fm ));
         auto f2 = logic::term( logic::op_not, fm );
         auto f3 = std::move( fm );

         seq. append( disjunction{ exists(f1), exists(f2), exists(f3) } );
         return;
      }

   case prf_chain:
      {
         auto ch = prf. view_chain( );

         for( size_t i = 0; i != ch. size( ); ++ i )
         {
            auto step = ch. extr_step(i);
            checkproof( blfs, step, seq, err );
            ch. update_step( i, std::move( step ));
         } 

         return; 
      }

   case prf_expand:
      {
         auto exp = prf. view_expand( ); 
         size_t ind = exp. ind( );
   
         expander def( exp. ident( ), exp. occ( ), blfs, err );
            // We are using unchecked identifier exp. ident( ).
            // The expander will look only at exact overloads. 
            // This guarantees type safety.

         if( !seq. hasindex( ind ))
            throw std::logic_error( "expand: index out of range" );

         if( seq. at( ind ). is_unf( ))
         {
            std::cout << "it is a UNF\n";
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
 
#if 0
         seq. back( ). at( exp. ind( )) =
            outermost( def, std::move( seq. back( ). at( exp. ind( ))), 0 );

#endif
         throw std::logic_error( "expand unfinished" );
         return;
      }

   case prf_expandlocal:
      {
         auto exp = prf. view_expandlocal( );
         auto ind = exp. ind( );
         auto name = exp. name( );

         // We have an identifier, but we need a De Bruijn index:

         size_t var = seq. ctxt. size( );
         {  
            auto p = seq. db. find( name );
            if( p == seq. db. end( ))
            {
               throw std::logic_error( "did not find the variable" );
            }

            var = p -> second;
         }

         auto p = seq. defs. find( var );
         if( p == seq. defs. end( ))
         {
            throw std::logic_error( "variable is not a definition" );
         }

         auto def = localexpander( seq. ctxt. size( ) - var - 1,  
                                   p -> second, 
                                   prf. view_expandlocal( ). occ( ));
        
         if( !seq. hasindex( ind ))
            throw std::logic_error( "expandlocal: index out of range" );

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


         }
#if 0
         seq. back( ). at( exp. ind( )) =
            outermost( def, std::move( seq. back( ). at( exp. ind( ))), 0 );
#endif
         seq. ugly( std::cout );
         throw std::logic_error( "not finished epxand local" );
         return;
      }

   case prf_normalize:
      { 
         auto ind = prf. view_normalize( ). ind( );

         if( !seq. hasindex( ind ))
            throw std::logic_error( "normalize: index out of range" );

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

   case prf_orrepl:
      {
         auto repl = prf. view_orrepl( );
         size_t ind = repl. ind( );
         size_t alt = repl. alt( );

         if( !seq. hasindex( ind ))
         {
            throw std::logic_error( "orrepl: wrong index" );

         } 

         if( !seq. at( ind ). is_dnf( ))
         {
            throw std::logic_error( "orrepl: formula is not DNF" );
         }

         if( alt >= seq. at( ind ). get_dnf( ). size( ))
         {
            throw std::logic_error( "orrepl: alternative does not exist" ); 
         }

         // Now we are certain that the rule will be applied.

         auto chosen = seq. at( ind ). get_dnf( ). at( alt );
         chosen = lift( std::move( chosen ), seq. liftdist( ind ));
         std::cout << "chosen after lift: " << chosen << "\n"; 

         size_t lev = seq. nrlevels( ); 
         seq. appendlevel( );

         seq. hide( repl. ind( ));
         seq. append( disjunction( { std::move( chosen ) } ));

         for( size_t i = 0; i != repl. size( ); ++ i )
         {
            auto prf = repl. extr_sub(i);
            checkproof( blfs, prf, seq, err ); 
            repl. update_sub( i, std::move( prf )); 
         }

         seq. ugly( std::cout );

         if( lev + 1 != seq. nrlevels( ))
            throw std::logic_error( "levels are not right" );

         if( seq. lastlevel( ). stacksize >= seq. nrformulas( ))
            throw std::logic_error( "there is no formula" );

         if( !seq. at( -1 ). is_dnf( ))
            throw std::logic_error( "last formula not DNF" );

         std::cout << "chosen " << chosen << "\n";
         // chosen = seq. at( -1 ). get_dnf( ); 
         std::cout << "becomes " << chosen << "\n"; 
         throw std::logic_error( "orrepl not finished" );
      }

   case prf_deflocal: 
      {
         auto def = prf. view_deflocal( );
         auto val = def. extr_val( );

         std::cout << "val = " << val << "\n";
         auto tp = checktype( blfs, val, seq, err );

         if( !tp. has_value( ))
            throw std::logic_error( "def local, no type" );

         def. update_val( val );

         size_t ss = seq. ctxt. size( );
         size_t ff = seq. stack. size( );

         seq. define( def. name( ), val, tp. value( ));

         for( size_t i = 0; i != def. size( ); ++ i )
         {
            auto sub = def. extr_sub(i); 
            checkproof( blfs, sub, seq, err );
            def. update_sub( i, std::move( sub ));
         }

#if 0
         // We need to apply the substitution:

         if( seq. ctxt. size( ) != ss + 1 )
            throw std::logic_error( "something went wrong with size" );
 
         if( !seq. defs. contains(ss))
            throw std::logic_error( "something went wrong with def" ); 

         auto subst = logic::singlesubst( seq. defs. at(ss));
         std::cout << subst << "\n";

         for( auto& fm : seq. back( ))
            fm = outermost( subst, std::move( fm ), 0 );

         seq. restore(ss);
         -- seq. back( ). contextsize;

         std::cout << "deflocal is not terribly well tested\n";
         return; 
#endif
         throw std::logic_error( "deflocal" );
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
               seq. assume( intro.var(i).pref, intro.var(i).tp );

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
         size_t ind = elim. ind( );

         if( !seq. hasindex( ind ))
            throw std::logic_error( "forallelim: index out of range" );

         if( !seq. at( ind ). is_unf( ))
            throw std::logic_error( "forallelim: formula not UNF" );

         if( seq. at( ind ). get_unf( ). vars. size( ) < elim. size( ))
            throw std::runtime_error( "forallelim: Too many values" ); 

         auto mainform = seq. at( ind ). get_unf( );
         mainform = lift( std::move( mainform ), seq. liftdist( ind ));
         
         size_t errstart = err. size( );
         logic::fullsubst subst;

         size_t ss = seq. ctxt. size( );

         bool alltypescorrect = true;

         for( size_t i = 0; i != elim. size( ); ++ i )
         {
            std::cout << "i = " << i << "\n";
            auto inst = elim. extr_value(i);
            auto tp = checktype( blfs, inst, seq, err );

            if( tp. has_value( ))
               std::cout << "found type: " << tp. value( ) << "\n";
            else
               std::cout << "(no type)\n";

            std::cout << "must be: " << mainform. vars[i]. tp << "\n";

            if( ! tp. has_value( ) ||  
                !equal( tp. value( ), mainform. vars[i]. tp ))
            {
               alltypescorrect = false; 
            }

            elim. update_value( i, inst ); 
            subst. append( std::move( inst ));

#if 0
            // I am keeping this because of the nice error message.

            if( tp. has_value( )) 
            {
               if( logic::equal( tp. value( ), q. var(i). tp ))
               {
                  subst. push( std::move( tm ));
               }
               else
               {
                  auto bld = errorstack::builder( ); 
                  bld << "true type of instance ";
                  printing::pretty( bld, seq, tm );
                  bld << " is wrong\n"; 
                  bld << "It is "; 
                  printing::pretty( bld, seq, tp. value( ));
                  bld << ", but must be ";
                  printing::pretty( bld, seq, q. var(i). tp ); 
                  err. push( std::move( bld ));
               }
            }
#endif
         }

         if( !alltypescorrect )
         {
            seq. ugly( std::cout );
            throw std::runtime_error( "we cannot do forallinst, types wrong" );
         }

         // We do not remove the outermost forall, because its 
         // its presence is required by the data structure. 
         // We remove the variables It is allowed that some variables remain. 

         mainform. vars. erase( mainform. vars. begin( ),
                                mainform. vars. begin( ) + elim. size( ));

         mainform = outermost( subst, std::move( mainform ), 0 ); 

         // We append mainform as CNF. The append function will 
         // convert formula into a DNF is the quantification is empty.
        
         seq. append( conjunction( { mainform } ));
         return;  
      }

#if 0 
   case prf_import:
      {
         auto imp = prf. view_import( );

         // We need to make the types exact:

         std::vector< logic::type > types;

         bool alltypescorrect = true;

         for( size_t i = 0; i != imp. size( ); ++ i )
         {
            auto tp = imp. extr_tp(i);
            bool b = checkandresolve( blfs, err, tp );
            if(b)
               types. push_back( tp );
            else
               alltypescorrect = false;

            imp. update_tp( i, tp );
         }

         if( !alltypescorrect )
            throw std::logic_error( "import : failed type checking" );

         const auto& ident = imp. ident( );
         const auto& overcands = blfs. getformulas( ident ); 

         size_t nrapplicable = 0;
         size_t lastapplicable = 0;
 
         for( size_t i = 0; i != overcands. size( ); ++ i )
         {
            auto ex = overcands. at(i);
            const auto& form = blfs. at(ex);
            if( applicable( form, types ))
            {
               ++ nrapplicable;
               lastapplicable = i;
            }
         }

         // If nrapplicable == 1, we found a usable overload,
         // otherwise it's error.

         if( nrapplicable == 0 )
         {
            std::cout << imp. ident( ) << "\n";
            throw std::runtime_error( "no overload found" );
         }

         if( nrapplicable > 1 )
         {
            std::cout << imp. ident( ) << "\n";
            throw std::runtime_error( "too many overloads" );
         }

         std::cout << lastapplicable << "\n";
         const auto& picked = blfs. at( overcands. at( lastapplicable ));
         const auto& fm = picked. view_form( ). fm( );

         seq. back( ). push( forall( disjunction{ exists( fm ) } )); 
         return;  
      }

#endif  
   case prf_simplify:
      {
         saturation sat; 
         for( size_t i = 0; i != seq. nrformulas( ); ++ i )
         {
            const auto& fm = seq. at(i);
            if( !fm. hidden && fm. is_dnf( )) 
               sat. initial( lift( fm. get_dnf( ), seq. liftdist(i)), i );
         }
     
         std::cout << sat << "\n"; 
#if 0
         std::vector< forall< disjunction< exists< logic::term >>>> ignored;
         conjunction< atp::clause > simp; 

         auto& last = seq. back( );
         for( auto& f : last )
         {
            if( f. vars. size( ))
               ignored. push_back( std::move(f));
            else
               simp. append( std::move( f. body ));
         }
 
#if 0 
         std::cout << "before simplification: " << simp << "\n";
         std::cout << "ignoring\n";
         for( const auto& ig : ignored )
            std::cout << "   " << ig << "\n"; 
#endif
         atp::simplify( simp );

#if 0
         std::cout << "after simplification: " << simp << "\n";
#endif

         seq. back( ). clear( );
         for( auto& ig : ignored )
            seq. back( ). push( std::move(ig) );

         for( auto& s : simp )
            seq. back( ). push( forall( std::move(s)) );

         return;

#endif
         throw std::logic_error( "simplify not finished" );
      }

   case prf_fake:
      {
         auto trmp = prf. view_fake( ). extr_goal( );
         auto tp = checktype( blfs, trmp, seq, err );

         if( tp. has_value( ))
            std::cout << "found type: " << tp. value( ) << "\n";
         else
         {
            throw std::logic_error( "fake: Not a formula" ); 
         }

         prf. view_fake( ). update_goal( trmp );

         // auto cls = disjunction( { exists( std::move(res) ) } ); 
         // seq. back( ). push( forall( std::move( cls ))); 
         seq. append( disjunction( { exists( std::move( trmp )) } ));

         std::cout << "faking: " << trmp << "\n";
         return;
      }


   case prf_nop:
      {
         return;   // Truly nothing was done. 
      }


   case prf_show:
      {
         auto show = prf. view_show( ); 
         printbar( std::cout );
         std::cout << "\n"; 

         std::cout << "proof state " << show. comment( ) << ":\n";
         auto out = pretty_printer( std::cout, blfs );
         seq. pretty( out );
         return;
      } 

   }

   std::cout << prf. sel( ) << "\n";
   throw std::logic_error( "dont know how to check proof term" );
}


