
#include "tests.h"
#include "errorstack.h"

#include "logic/replacements.h" 
#include "logic/pretty.h"
#include "logic/cmp.h"
#include "logic/termoperators.h"

#include "calc/proofterm.h"
#include "calc/proofchecking.h"
#include "calc/flatten.h"
#include "calc/removelets.h"
#include "calc/expander.h"
#include "calc/projection.h"
#include "calc/proofoperators.h"
#include "calc/saturation.h"

#include "natded/eval.h"

#include "parsing/parser.h"

void tests::add_settheory( logic::beliefstate& blfs )
{
   using namespace logic;

   type O = type( logic::type_obj );
   type T = type( logic::type_form );

   type O2O = type( type_func, O, { O } );
   type O2T = type( type_func, T, { O } );

   logic::structdef setdef;
   setdef. append( fielddecl( identifier( ) + "setlike", 
                              type( type_func, T, { O2T } )));
   setdef. append( fielddecl( identifier( ) + "mat", 
                              type( type_func, O, { O2T } )));

   blfs. append( belief( bel_struct, identifier( ) + "Settheory", setdef ));

   auto typed = forall( {{ "P", O2T }}, 
      implies( apply( "strict"_unchecked, { 0_db } ), 
         prop( apply( "setlike"_unchecked, { 1_db, 0_db } )) ) );

   auto empty = 
      forall( {{ "P", O2T }},
         lazy_implies( apply( "strict"_unchecked, { 0_db } ),
               implies( 
                  forall( {{ "x", O }}, ! apply( 1_db, { 0_db } )),
                  apply( "setlike"_unchecked, { 1_db, 0_db } ))) );

   auto singleton =
      forall( {{ "P", O2T }},
         lazy_implies( apply( "strict"_unchecked, { 0_db } ),
            implies( exists( {{ "x", O }}, forall( {{ "x1", O }},
                implies( apply( 2_db, { 0_db } ), 0_db == 1_db ))),
                apply( "setlike"_unchecked, { 1_db, 0_db } ) )));
        
   auto setunion =
      forall( {{ "P1", O2T }, { "P2", O2T }, { "Q", O2T }},
         lazy_implies(
            apply( "strict"_unchecked, { 2_db } ) &&
            apply( "strict"_unchecked, { 1_db } ) &&
            apply( "strict"_unchecked, { 0_db } ),
            implies(
               apply( "setlike"_unchecked, { 3_db, 2_db } ) &&
               apply( "setlike"_unchecked, { 3_db, 1_db } ),
               implies(
                  forall( {{ "x", O }},
                     implies( apply( 1_db, { 0_db } ),
                              apply( 3_db, { 0_db } ) ||
                              apply( 2_db, { 0_db } ))),
                     apply( "setlike"_unchecked, { 3_db, 0_db } )))));

   auto repl = apply( "setlike"_unchecked, { 3_db, 0_db } );

   {
      auto f1 = forall( {{ "x", O }}, 
         implies( apply( 3_db, { 0_db } ), 
                  apply( "setlike"_unchecked, { 4_db, apply( 2_db, { 0_db } ) } )));

      auto f2 = forall( {{ "x", O }}, 
         implies( apply( 3_db, { 0_db } ), 
            apply( "setlike"_unchecked, { 4_db, apply( 2_db, { 0_db } ) } )));

      auto f3 = forall( {{ "y", O }},
         implies( apply( 1_db, { 0_db } ), 
            exists( {{ "x", O }}, 
               lazy_and( apply( 4_db, { 0_db } ), 
                         apply( 3_db, { 0_db, 1_db } ))) ));

      repl = implies( f3, repl );
      repl = implies( f2, repl );
      repl = implies( apply( "setlike"_unchecked, { 3_db, 2_db } ), repl );
      repl = lazy_implies( apply( "strict"_unchecked, { 0_db } ), repl );
      repl = lazy_implies( f1, repl );
      repl = lazy_implies( apply( "strict"_unchecked, { 2_db } ), repl );

      repl = forall( {{ "Q", O2T }}, repl );
      repl = forall( {{ "F", type( type_func, O2T, { O } ) }}, repl );
      repl = forall( {{ "P", O2T }}, repl );
   }

   auto ext = apply( "mat"_unchecked, { 2_db, 1_db } ) == 
                 apply( "mat"_unchecked, { 2_db, 0_db } );

   {
      auto eq = forall( {{ "x", O }}, 
         equiv( apply( 2_db, { 0_db } ),
                apply( 1_db, { 0_db } )) );
      ext = implies( eq, ext );
      ext = lazy_implies( apply( "strict"_unchecked, { 1_db } ) &&
                          apply( "strict"_unchecked, { 0_db } ), ext );
      ext = forall( {{ "P1", O2T }, { "P2", O2T }}, ext );
   }

   auto bij =  forall( {{ "x", O }}, equiv( apply( 2_db, { 0_db } ),
                                            apply( 1_db, { 0_db } )) );
   bij = implies( apply( "mat"_unchecked, { 2_db, 1_db } ) ==
                  apply( "mat"_unchecked, { 2_db, 0_db } ), bij );
   bij = implies( apply( "setlike"_unchecked, { 2_db, 1_db } ) &&
                  apply( "setlike"_unchecked, { 2_db, 0_db } ), bij );
   bij = lazy_implies( apply( "strict"_unchecked, { 1_db } ) &&
                       apply( "strict"_unchecked, { 0_db } ), bij ); 
   bij = forall( {{ "P1", O2T }, { "P2", O2T }}, bij ); 

   auto powset = exists( {{ "P1", O2T }}, apply( "strict"_unchecked, { 0_db } ) &&
      forall( {{ "x", O }}, implies( apply( 1_db, { 0_db } ), apply( 3_db, { 0_db } )) &&
          2_db == apply( "mat"_unchecked, { 5_db, 1_db } )));

   powset = forall( {{ "y", O }}, implies( apply( 1_db, { 0_db } ), powset ));

   powset = implies( powset, apply( "setlike"_unchecked, { 2_db, 0_db } ));
   powset = implies( apply( "setlike"_unchecked, { 2_db, 1_db } ) &&
                     apply( "setlike"_unchecked, { 2_db, 0_db } ), powset );
   powset = lazy_implies( apply( "strict"_unchecked, { 1_db } ), powset );
   powset = forall( {{ "P", O2T }, { "Q", O2T }}, powset );

   auto settheory = lambda( {{ "t", type( type_unchecked, identifier( ) + "Settheory" ) }}, 
      lazy_and( typed, empty && singleton && setunion && repl && ext && bij && powset ));

   blfs. append( belief( bel_def, identifier( ) + "settheory", settheory, 
                                     type( type_func, T, 
                                     { type( type_unchecked, 
                                             identifier( ) + "Settheory" ) } ) ));
}


void tests::flatten( )
{
   using namespace logic;

   auto O = type( type_obj );
   auto T = type( type_form );

   auto N2T = type( type_func, T, { } );

   auto O2T = type( type_func, T, { O } );
   auto O2O = type( type_func, O, { O } );
   auto OO2T = type( type_func, T, { O, O } );
   auto OOO2T = type( type_func, T, { O, type( type_struct, exact(44)), O } );

   term tm =  lazy_implies( "left"_unchecked, "right"_unchecked );
   tm = term( op_exists, tm, { { "x", O }, { "y", T }} );

   auto cnf_pos = calc::cnf( calc::conjunction( { calc::forall( prop( tm )) } )); 
   auto dnf_pos = calc::dnf( calc::disjunction( { calc::exists( ! ! prop( tm )) } ));
   auto cnf_neg = calc::cnf( calc::conjunction( { calc::forall( ! prop( tm )) } ));
   auto dnf_neg = calc::dnf( calc::disjunction( { calc::exists( ! prop( tm )) } ));

   std::cout << cnf_pos << "\n";
   std::cout << dnf_pos << "\n"; 
   std::cout << cnf_neg << "\n";
   std::cout << dnf_neg << "\n";

   cnf_pos = flatten( std::move( cnf_pos ));
   dnf_pos = flatten( std::move( dnf_pos ));

   cnf_neg = flatten( std::move( cnf_neg ));
   dnf_neg = flatten( std::move( dnf_neg ));

   std::cout << "\n";

   std::cout << "positive:\n";
   std::cout << "   " << cnf_pos << "\n";
   std::cout << "   " << dnf_pos << "\n";
   std::cout << "negative:\n";
   std::cout << "   " << cnf_neg << "\n";
   std::cout << "   " << dnf_neg << "\n";

}



void tests::pretty( const logic::beliefstate& blfs )
{
   using namespace logic;

   auto O = type( type_obj );
   auto T = type( type_form );

   auto N2T = type( type_func, T, { } );

   auto O2T = type( type_func, T, { O } );
   auto O2O = type( type_func, O, { O } );
   auto OO2T = type( type_func, T, { O, O } );
   auto OOO2T = type( type_func, T, { O, type( type_struct, exact(44)), O } );
 
   term tm = ( 0_db && 1_db ) || ( 0_db != 1_db );
   tm = term( op_meta_implies, "xxxx"_unchecked, 4_db || 5_db ) && term( op_exact, exact(23) );

   tm = lambda( {{ "x1", OOO2T }, { "x2", O2T }, { "y1", O }, { "s", O }}, tm );
   tm = forall( {{ "yy", O2O }, { "zz", O }}, tm );
   tm = apply( tm, { term( op_exact, exact(21)), term( op_false ) } );

   std::cout << "\n";
   std::cout << "pretty: ";
   std::cout << tm << "\n";
   std::cout << "\n\n"; 

   pretty::uniquenamestack un;
   pretty::print( std::cout, blfs, un, tm, {0,0} );
}


void tests::saturate( )
{
   using namespace logic;

   type O = type( logic::type_obj );
   type T = type( logic::type_form );
   type O2T = type( type_func, T, { O } );
   type O2O = type( type_func, O, { O } );
   type OT2O = type( type_func, O, { O, T } );

   calc::saturation sat;

   auto cl1 = calc::disjunction( { 
      calc::exists( "t1"_unchecked == "t2"_unchecked ),
      calc::exists( "A"_unchecked ) } );
   sat. initial( cl1, 10 );

   auto cl2 = calc::disjunction( {
      calc::exists( "t2"_unchecked == "t3"_unchecked ),
      calc::exists( "A"_unchecked ) } );
   sat. initial( cl2, 11 );

   auto cl3 = calc::disjunction( 
      { calc::exists( prop( apply( "f"_unchecked, { "t1"_unchecked, "t3"_unchecked  } ))),
        calc::exists( apply( "f"_unchecked, { "t1"_unchecked, "t3"_unchecked  } )),
        calc::exists( prop( "A"_unchecked )) } );
   sat. initial( cl3, 12 );

   auto cl4 = calc::disjunction( 
      { calc::exists( !prop( apply( "f"_unchecked, { "t3"_unchecked, "t1"_unchecked  } ))),
        calc::exists( prop( "A"_unchecked )) } );
   sat. initial( cl4, 13 );

   sat. saturate( );
   std::cout << sat << "\n";

   for( const auto& lit : sat. checked )
      std::cout << make_dnf( lit. disj ) << "\n";
}


void tests::cmp( )
{
   std::cout << "testing compare\n";

   using namespace logic;

   std::cout << ( ( 1_db == 3_db ) <=> ( 1_db == 3_db ) ) << "\n";

   type O = type( logic::type_obj );
   type T = type( logic::type_form );
   type O2T = type( type_func, T, { O } );
   type O2O = type( type_func, O, { O } );
   type OT2O = type( type_func, O, { O, T } );

   type Seq = type( type_unchecked, identifier( ) + "Seq" );
   type X = type( type_unchecked, identifier( ) + "X" );

   auto tm1 = "aba"_unchecked || 3_db;
   tm1 = term( op_lambda, tm1, { { "x", T }, { "y", Seq }, { "z", O }} );

   auto tm2 = "aba"_unchecked || 3_db;
   tm2 = term( op_lambda, tm2, { { "x", T }, { "y", Seq }, { "t", O }} );
 
   tm1 = apply( tm2, { 2_db, "bba"_unchecked, 1_db } );
   tm2 = apply( tm1, { 2_db, "bba"_unchecked, term( op_exact, exact(12)) } );
   std::cout << ( tm1 <=> tm2 ) << "\n";
   std::cout << "weights\n";
   std::cout << weight(tm1) << "\n" << weight( tm2 ) << "\n";
  
   // bool b = equal( tm1, tm2 );
   // std::cout << "result = " << b << "\n"; 

   tm1 = lift( tm1, 1 );
   tm2 = lift( tm2, 4 );
   // b = equal( tm1, 6, tm2, 3, 0 );
   // std::cout << "lifted result = " << b << "\n";
}


void tests::parser( logic::beliefstate& blfs ) {
   lexing::filereader inp( &std::cin, "std::cin" );

   parsing::tokenizer tok( std::move( inp ));
   parsing::parser prs( tok, blfs );  

   prs. debug = 0;
   prs. checkattrtypes = 0;

   auto res = prs. parse( parsing::sym_File, std::cout );

}


void tests::betareduction( logic::beliefstate& blfs, errorstack& err ) 
{
   using namespace logic;

   type O = type( type_obj );
   type T = type( type_form );

   type O2O = type( type_func, O, { O } );
   type O2T = type( type_func, T, { O } );
   
   logic::betareduction beta;
   std::cout << beta << "\n";

   term body = term( op_apply, "func"_unchecked, { 0_db, 1_db, 2_db, 3_db } );
   body = term( op_forall, body, {{ "haha", T }} ); 
   term lambda = term( op_lambda, body, { { "x", O }, { "y", O } } );

   auto first = term( op_apply, "first"_unchecked, { 1_db } ); 
   auto second = term( op_apply, "second"_unchecked, { 2_db } );
   auto third =  term( op_apply, "third"_unchecked, { 3_db } );

   term appl = term( op_apply, lambda, { first, second, third } );

   std::cout << "appl = " << appl << "\n";

   beta. used = 0;

   auto res = beta( appl, 0 );
   std::cout << "res = " << res << "\n";
   std::cout << "used = " << beta. used << "\n";
   std::cout << beta << "\n";
}


void tests::smallproofs( const logic::beliefstate& blfs, errorstack& err )
{
#if 0
   auto O = logic::type( logic::type_obj );
   auto T = logic::type( logic::type_form );
   auto Nat = logic::type( logic::type_unchecked, identifier( ) + "Nat" );

   using namespace calc;

   // This is the first proof that passed!

   if constexpr( true ) 
   {
      // This proof was completed on 16 december 2025, 05.23 CET.

      auto id = identifier( ) + "resolve";

      const auto& f = blfs. getformulas( id );
      if( f. size( ) != 1 )
         throw std::runtime_error( "cannot continue" );
      auto seq = sequent( );

      auto nr = seq. define( "goal",
                             blfs. at( f. front( )). view_form( ). fm( ),
                             logic::type( logic::type_form ));
      seq. push_back( "start" );
 
      auto prf = chain( 
      { 
         proofterm( prf_cut, "goal"_unchecked ),

         // We expand the 'goal' before the split,
         // that saves an existsintro:

         proofterm( prf_expandlocal, -1, "goal", 0 ),
         proofterm( prf_flatten, -1 ),
         proofterm( prf_orexistselimintro, -1, 0, "prop", { },
         {
            proofterm( prf_flatten, -1 ),
            proofterm( prf_orexistselimintro, -1, 0, "nr", { },
            {
               proofterm( prf_copy, "prop", 0 ),
               proofterm( prf_forallelim, -1, { 0_db } ),
               proofterm( prf_simplify ), 
            }),

            proofterm( prf_orexistselimintro, -1, 0, "nr", { },
            {
               proofterm( prf_copy, "prop", 1 ),
               proofterm( prf_forallelim, -1, { 0_db } ),
               proofterm( prf_simplify ) 
            }),
            proofterm( prf_orexistselimintro, -1, 0, "nr", { },
            {
               proofterm( prf_copy, "prop", 0 ),
               proofterm( prf_forallelim, -1, { 0_db } ),
               proofterm( prf_simplify ) 
            }),
            proofterm( prf_orexistselimintro, -1, 0, "nr", { },
            {
               proofterm( prf_copy, "prop", 2 ),
               proofterm( prf_forallelim, -1, { 0_db } ),
               proofterm( prf_simplify ) 
            }),
            proofterm( prf_orexistselimintro, -1, 0, "nr", { },
            {
               proofterm( prf_copy, "prop", 1 ),
               proofterm( prf_forallelim, -1, { 0_db } ),
               proofterm( prf_simplify ) 
            }),
            proofterm( prf_orexistselimintro, -1, 0, "nr", { },
            {
               proofterm( prf_copy, "prop", 2 ),
               proofterm( prf_forallelim, -1, { 0_db } ),
               proofterm( prf_simplify ),
            }) 
         }),
         proofterm( prf_expandlocal, -1, "goal", 0 ),
         proofterm( prf_flatten, -1 ),
         proofterm( prf_orexistselimintro, -1, 0, "negated", { }, 
         {
            // This is the refutation of the negated goal:

            proofterm( prf_flatten, -1 ),
            proofterm( prf_orexistselimintro, -1, 0, "aa", { },
            {
               proofterm( prf_flatten, -1 ),
               proofterm( prf_copy, "negated", 3 ),
               proofterm( prf_forallelim, -1, { 0_db } ), 
               proofterm( prf_copy, "negated", 4 ),
               proofterm( prf_forallelim, -1, { 0_db } ),
               proofterm( prf_simplify) 
            }) 
         }) 
      });
      prf. print( indentation( ), std::cout );

      // checkproof( blfs, prf, seq, err );
      std::cout << "FINAL STATE" << id << " :\n";
      seq. ugly( std::cout );
   }

   if constexpr( true )
   {
      auto id = identifier( ) + "minhomrel_succ";

      const auto& f = blfs. getformulas( id );
      std::cout << f. size( ) << "\n";
      if( f. size( ) != 1 )
         throw std::runtime_error( "cannot continue minhomrel_succ" );
    
      auto seq = sequent( );
      auto nr = seq. define( "goal",
                             blfs. at( f. front( )). view_form( ). fm( ),
                             logic::type( logic::type_form ));

      seq. push_back( "goal" );
      seq. ugly( std::cout );

#if 0
      auto splitprop = orexistselim( -1, "prop",
         {
            chain( { calc::show( "NOTPROP" ) } ),
            chain( { proofterm( prf_cut, -1 ), 
                   orexistselim( -1, "truth", 
                   {
                      chain( { 
                         proofterm( prf_expandlocal, -1, "goal", 0 ),
                         proofterm( prf_flatten, -1 ),
                         orexistselim( -1, "exists",
                         {
                            chain( 
                            {
                               proofterm( prf_flatten, -1 ),

                               proofterm( prf_flatten, 2 ),
                               orexistselim( -1, "R",
                               {
                                  chain(
                                  {
                                     proofterm( prf_copy, "R", -2 ),
                                     proofterm( prf_expand, -1, identifier( ) + "homrel", 0 ),
                                     proofterm( prf_normalize, -1 ),
                                     proofterm( prf_flatten, -1 ),
                                     proofterm( prf_forallelim, -1, { 2_db, 1_db } ), 
                                     proofterm( prf_copy, "exists", 2 ),  
                                     proofterm( prf_forallelim, -1, { 0_db } ),
                                     proofterm( prf_copy, "exists", 0 ),
                                     proofterm( prf_copy, "exists", 1 ),
                                     proofterm( prf_simplify ) 
                                  } )
                               })
                            } )
                         } ) } ), 
                      chain( { calc::show( "GAL" ) } )
                   } ) } )
         } );

#endif
      auto prf = chain( 
      { 
         proofterm( prf_cut, "goal"_unchecked ), 
         proofterm( prf_expandlocal, -1, "goal", 0 ),
         proofterm( prf_flatten, -1 ),
         proofterm( prf_orexistselimintro, -1, 0, "notprop", { },
         {
            proofterm( prf_import, identifier( ) + "gen_prop", { Nat, O } ),
            proofterm( prf_flatten, -1 ),
            proofterm( prf_forallelim, -1, { 3_db, 1_db } ),
            proofterm( prf_simplify ) 
         }),
         proofterm( prf_orexistselimintro, -1, 0, "notprop", { },
         {
            proofterm( prf_import, identifier( ) + "gen_prop", { Nat, O } ),
            proofterm( prf_flatten, -1 ),
            proofterm( prf_forallelim, -1, { 2_db, 0_db } ),
            proofterm( prf_simplify ) 
         }),
         proofterm( prf_flatten, -1 ),
         proofterm( prf_orexistselimintro, -1, 0, "notprop", { },
         {
            proofterm( prf_flatten, -1 ),
            proofterm( prf_import, identifier( ) + "minhomrel_prop", { Nat, Nat } ), 
            proofterm( prf_flatten, -1 ),
            proofterm( prf_forallelim, -1, { 3_db, 2_db } ),
            proofterm( prf_copy, "notprop", -1 ), 
            proofterm( prf_forallelim, -1, { 1_db, 0_db } ),
            proofterm( prf_simplify ),
            proofterm( prf_copy, "notprop", 0 ),
            proofterm( prf_forallelim, -1, 
                 { apply( "succ"_unchecked, { 3_db, 1_db } ),
                   apply( "succ"_unchecked, { 2_db, 0_db } ) } ),
            proofterm( prf_simplify ),
            proofterm( prf_import, identifier( ) + "gen_succ", { Nat, O } ), 
            proofterm( prf_flatten, -1 ),
            proofterm( prf_copy, "notprop", -1 ),
            proofterm( prf_forallelim, -1, { 3_db, 1_db } ),
            proofterm( prf_forallelim, -2, { 2_db, 0_db } ),
            proofterm( prf_simplify )
         }),
         proofterm( prf_expandlocal, -1, "goal", 0 ),
         proofterm( prf_flatten, -1 ),
         proofterm( prf_orexistselimintro, -1, 0, "negated", { },
         {
            proofterm( prf_flatten, -1 ),
            proofterm( prf_expand, 2, identifier( ) + "minhomrel", 0 ),
            proofterm( prf_expand, 3, identifier( ) + "minhomrel", 0 ),
            proofterm( prf_expand, 2, identifier( ) + "minimal", 0 ),
            proofterm( prf_expand, 3, identifier( ) + "minimal", 0 ),
            proofterm( prf_normalize, 2 ), 
            proofterm( prf_normalize, 3 ),
            proofterm( prf_flatten, -1 ),
            proofterm( prf_orexistselimintro, -1, 0, "R", { "R" },
            {
               proofterm( prf_flatten, -1 ),
               proofterm( prf_copy, "R", -2 ),
               proofterm( prf_expand, -1, identifier( ) + "homrel", 0 ),
               proofterm( prf_normalize, -1 ),
               proofterm( prf_flatten, -1 ),

               proofterm( prf_show, "NEG" )

            }),
            proofterm( prf_show, "NEGATED" ) 
         }),
         proofterm( prf_show, "XXXX" ) 
      });

      prf. print( indentation( ), std::cout );

      // checkproof( blfs, prf, seq, err );
      std::cout << "\n";
      std::cout << "FINAL STATE " << id << "\n";
      seq. ugly( std::cout );
   }
#endif
}


void 
tests::bigproof( const logic::beliefstate& blfs, errorstack& err )
{
   auto O = logic::type( logic::type_obj );
   auto T = logic::type( logic::type_form );
   auto Nat = logic::type( logic::type_unchecked, identifier( ) + "Nat" );

   using namespace calc;

   auto id = identifier( ) + "just";
   const auto& f = blfs. getformulas( id );
   std::cout << f. size( ) << "\n";
   if( f. size( ) != 1 )
      throw std::runtime_error( "cannot continue" );

   auto seq = sequent( );

   auto nr = seq. define( "goal",
                          blfs. at( f. front( )). view_form( ). fm( ),
                          logic::type( logic::type_form ));

   seq. ugly( std::cout );

   std::cout << "start of a big proof --------------------------\n";

   logic::term indhyp = logic::term( logic::op_false );  
      // Called Q in the paper. 
   {
      using namespace logic;
      auto disj1 = 
         "x1"_unchecked == apply( "0"_unchecked, { "n1"_unchecked } ) &&
         "x2"_unchecked == apply( "0"_unchecked, { "n2"_unchecked } );

      // Left and right of the lazy-and inside the exists:

      auto la1 =
         apply( "gen"_unchecked, { "n1"_unchecked, "y1"_unchecked } ) && 
         apply( "gen"_unchecked, { "n2"_unchecked, "y2"_unchecked } );

      auto la2 = 
         apply( "minhomrel"_unchecked, { "n1"_unchecked, "n2"_unchecked, "y1"_unchecked, "y2"_unchecked } ) &&
         "x1"_unchecked == apply( "succ"_unchecked, { "n1"_unchecked, "y1"_unchecked } ) &&
         "x2"_unchecked == apply( "succ"_unchecked, { "n2"_unchecked, "y2"_unchecked } );

      auto disj2 = logic::exists( { { "y1", O }, { "y2", O }}, lazy_and( la1, la2 ));

      indhyp = disj1 || disj2; 
      indhyp = lambda( {{ "x1", O }, { "x2", O }}, indhyp );
      indhyp = lambda( {{ "n1", Nat }, { "n2", Nat }}, indhyp );
   }

#if 0
   auto propproof = chain(
      { 
         proofterm( prf_expandlocal, -1, "goal", 0 ),
         proofterm( prf_flatten, -1 ),
         proofterm( prf_import, identifier( ) + "gen_prop", { Nat, O } ),
         proofterm( prf_import, identifier( ) + "minhomrel_prop", { Nat, Nat } ), 
         proofterm( prf_orexistselimintro, -3, 0, "prop", { },
         {
            proofterm( prf_copy, "notprop", 0 ),
            proofterm( prf_flatten, -1 ),
            proofterm( prf_forallelim, -1, { "s1"_unchecked, "x1"_unchecked } ), 
            proofterm( prf_simplify ),
         }),
         proofterm( prf_orexistselimintro, -1, 0, "prop", { },
         {
            proofterm( prf_copy, "notprop", 0 ),
            proofterm( prf_flatten, -1 ),
            proofterm( prf_forallelim, -1, { "s2"_unchecked, "x2"_unchecked } ),
            proofterm( prf_simplify ),
         }), 
         proofterm( prf_orexistselimintro, -1, 0, "final", { },
         {
            proofterm( prf_flatten, -1 ),
            proofterm( prf_copy, "notprop", 1 ),
            proofterm( prf_flatten, -1 ),
            proofterm( prf_forallelim, -1, { "s1"_unchecked, "s2"_unchecked } ),
            proofterm( prf_forallelim, -1, { "x1"_unchecked, "x2"_unchecked } ),
            proofterm( prf_simplify ),
            proofterm( prf_erase, -1 ),
            proofterm( prf_orexistselimintro, -1, 0, "finaler", { },
            {
               proofterm( prf_copy, "notprop", 0 ),
               proofterm( prf_flatten, -1 ),
               proofterm( prf_forallelim, -1, { "s1"_unchecked, "y1"_unchecked } ),
               proofterm( prf_simplify ),
            }),
            proofterm( prf_orexistselimintro, -1, 0, "finaler2", { },
            {
               proofterm( prf_copy, "notprop", 0 ),
               proofterm( prf_flatten, -1 ),
               proofterm( prf_forallelim, -1, { "s2"_unchecked, "y2"_unchecked } ),
               proofterm( prf_simplify ),
            }),

            proofterm( prf_orexistselimintro, -1, 0, "finaler3", { },
            {
               proofterm( prf_flatten, -1 ),
               proofterm( prf_copy, "notprop", 1 ),
               proofterm( prf_flatten, -1 ),
               proofterm( prf_forallelim, -1, { "s1"_unchecked, "s2"_unchecked } ),
               proofterm( prf_forallelim, -1, { "y1"_unchecked, "y2"_unchecked } ),
               proofterm( prf_simplify ),
            })
         }),
         proofterm( prf_show, "PROP-UNFINISHED" ) 
      } );

#endif

#if 0
   auto mainproof =
      chain( { proofterm( prf_expandlocal, -1, "goal", 0 ),  
               proofterm( prf_flatten, -1 ),
               proofterm( prf_show, "BEFORE" ),
               proofterm( prf_orexistselimintro, -1, 0, "outermost", { },
               { 
                  proofterm( prf_flatten, -1 ),
                  proofterm( prf_expand, -3, identifier( ) + "minhomrel", 0 ),
                  proofterm( prf_expand, -3, identifier( ) + "minimal", 0 ),
                  proofterm( prf_normalize, -3 ),
                  proofterm( prf_flatten, -3 ),
                  proofterm( prf_deflocal, "Q", indhyp, 
                  { 
                     proofterm( prf_forallelim, -1, 
                     { apply( "Q"_unchecked, { "s1"_unchecked, "s2"_unchecked } ) } ),
                        proofterm( prf_orexistselimintro, -1, 1, "inductive", { }, 
                              {
                                 proofterm( prf_expand, -1, identifier( ) + "homrel", 0 ),
                                 proofterm( prf_normalize, -1 ),
                                 proofterm( prf_flatten, -1 ),
                                 proofterm( prf_orexistselimintro, -1, 0, "base", { },
                                 {
                                    proofterm( prf_expandlocal, -1, "Q", 0 ),
                                    proofterm( prf_normalize, -1 ),
                                    proofterm( prf_flatten, -1 ),
                                    proofterm( prf_simplify ),
                                 }),
                                 proofterm( prf_orexistselimintro, -1, 0, "step", { "a1", "a2" },
                                 {
                                    proofterm( prf_flatten, -1 ),
                                    proofterm( prf_expandlocal, -1, "Q", 0 ),
                                    proofterm( prf_normalize, -1 ),
                                    proofterm( prf_flatten, -1 ),
                                    proofterm( prf_erase, 3 ),
                                    proofterm( prf_expandlocal, -2, "Q", 0 ),
                                    proofterm( prf_normalize, -2 ),
                                    proofterm( prf_flatten, -2 ),
                                    proofterm( prf_orexistselimintro, -1, 1, "cases", { "b1", "b2" },
                                    {
                                       proofterm( prf_copy, "step", 2 ),
                                       proofterm( prf_forallelim, -1, { "a1"_unchecked, "a2"_unchecked } ),  
                                       proofterm( prf_flatten, 0 ),
                                       proofterm( prf_copy, "step", 0 ), 
                                       proofterm( prf_copy, "step", 1 ),
                                       proofterm( prf_simplify ),
                                       proofterm( prf_import, identifier( ) + "minhomrel_succ", { Nat, Nat } ), 
                                       proofterm( prf_flatten, -1 ),
                                       proofterm( prf_forallelim, -1, { "s1"_unchecked, "s2"_unchecked } ),
                                       proofterm( prf_forallelim, -1, { "b1"_unchecked, "b2"_unchecked } ),
                                       proofterm( prf_simplify ) 
                                    }),
                                    proofterm( prf_forallelim, -2, { "a1"_unchecked, "a2"_unchecked } ),
                                    proofterm( prf_flatten, -1 ), 
                                    proofterm( prf_simplify ),
                                    proofterm( prf_import, identifier( ) + "minhomrel_zero", { Nat, Nat } ),
                                    proofterm( prf_flatten, -1 ),
                                    proofterm( prf_forallelim, -1, { "s1"_unchecked, "s2"_unchecked } ),
                                    proofterm( prf_simplify ) 
                                 }),
                              }), 
 
                              proofterm( prf_orexistselimintro, -1, 1, "cases", { },
                              {
                                 proofterm( prf_expandlocal, -1, "Q", 0 ), 
                                 proofterm( prf_normalize, -1 ),
                                 proofterm( prf_flatten, -1 ),
                                 proofterm( prf_orexistselimintro, -1, 1, "quant", { },
                                 {
                                    proofterm( prf_copy, "outermost", 3 ),
                                    proofterm( prf_forallelim, -1, { "y1"_unchecked, "y2"_unchecked } ),
                                    proofterm( prf_flatten, -2 ),
                                    proofterm( prf_simplify ),
                                 }),
                                 proofterm( prf_flatten, -1 ),
                                 proofterm( prf_copy, "outermost", 2 ),
                                 proofterm( prf_simplify ) 
                              }),
                              proofterm( prf_expand, -1, identifier( ) + "stricton", 0 ), 
                              proofterm( prf_expand, -1, identifier( ) + "prod", 0 ), 
                              proofterm( prf_normalize, -1 ),
                              proofterm( prf_erase, -2 ),
                              proofterm( prf_erase, -2 ),
                              proofterm( prf_erase, -2 ),
                              proofterm( prf_erase, -2 ),
                              proofterm( prf_flatten, -1 ),
                              proofterm( prf_orexistselimintro, -1, 0, "stricton", { "y1", "y2" },
                              { 
                                 proofterm( prf_expandlocal, -1, "Q", 0 ),
                                 proofterm( prf_normalize, -1 ),
                                 proofterm( prf_flatten, -1 ), 
                                 proofterm( prf_import, identifier( ) + "gen_prop", { Nat } ), 
                                 proofterm( prf_flatten, -1 ),
                                 proofterm( prf_orexistselimintro, -2, 0, "gp", { "z1", "z2" },
                                 {
                                    proofterm( prf_copy, "stricton", 2 ),
                                    proofterm( prf_forallelim, -1, { "s1"_unchecked, "z1"_unchecked } ),   
                                    proofterm( prf_simplify ),
                                 }),

                                 proofterm( prf_orexistselimintro, -1, 0, "gp", { "z1", "z2" },
                                 {
                                    proofterm( prf_copy, "stricton", 2 ),
                                    proofterm( prf_forallelim, -1, { "s2"_unchecked, "z2"_unchecked } ),
                                    proofterm( prf_simplify ),
                                 }),
                                 proofterm( prf_orexistselimintro, -1, 0, "gp", { "z1", "z2" },
                                 {
                                    proofterm( prf_flatten, -1 ),
                                    proofterm( prf_import, identifier( ) + "minhomrel_prop", { Nat, Nat } ),
                                    proofterm( prf_flatten, -1 ),
                                    proofterm( prf_forallelim, -1, { "s1"_unchecked, "s2"_unchecked } ),
                                    proofterm( prf_forallelim, -1, { "z1"_unchecked, "z2"_unchecked } ),
                                    proofterm( prf_simplify ),
                                 }),
                              })  
                           } ),
               }),
               proofterm( prf_show, "AFTER DEFLOCAL" )
             });

#endif

   auto proof = chain( 
      { proofterm( prf_cut, "goal"_unchecked ),
        proofterm( prf_orrepl, -1, 1, 
        { prf_nop,
          proofterm( prf_expandlocal, -1, "goal", 0 ),
          proofterm( prf_flatten, -1 ),
          proofterm( prf_existsrepl, -1, std::vector<std::string> { }, 
          { 
             proofterm( prf_flatten, -1 ),
             proofterm( prf_expand, -3, identifier( ) + "minhomrel", 0 ),
             proofterm( prf_expand, -1, identifier( ) + "minimal", 0 ),
             proofterm( prf_normalize, -1 ), 
             proofterm( prf_deflocal, "Q", indhyp, 
             {
                proofterm( prf_show, "before" ),
                proofterm( prf_flatten, -1 ),
                proofterm( prf_forallelim, -1,
                   { apply( "Q"_unchecked, { "s1"_unchecked, "s2"_unchecked } ) } ),
                proofterm( prf_flatten, -1 ),
                proofterm( prf_orrepl, -1, 1, 
                { 
                   proofterm( prf_expand, -1, identifier( ) + "homrel", 0 ),
                   proofterm( prf_normalize, -1 ),
                   proofterm( prf_flatten, -1 ),

                   proofterm( prf_show, "induction" ), 
                   proofterm( prf_orrepl, -1, 0, 
                   {
                      proofterm( prf_expandlocal, -1, "Q", 0 ),
                      proofterm( prf_normalize, -1 ),
                      proofterm( prf_flatten, -1 ), 
                      proofterm( prf_hide, -1 ), 
                      proofterm( prf_flatten, -2 ), 
                      proofterm( prf_show, "base-case" ),
                  
                      proofterm( prf_simplify ) 
                   }) 
                    
                } ) 
             } 
             ),
             proofterm( prf_normalize, -1 ),
             proofterm( prf_show, "before existsrepl" )
          } ) 
        } ) } );
#if 0
        orexistselim( -1, "notprop", 
        { propproof, 
          chain(
           { proofterm( prf_cut, -1 ),
             orexistselim( -1, "false_true", { mainproof } )
           }
       ) })
      });
#endif
   proof. print( indentation( ), std::cout );

   checkproof( blfs, proof, seq, err );
   std::cout << "\n";
   std::cout << "FINAL STATE\n";
   seq. ugly( std::cout );
}


void tests::natded( )
{
   using namespace logic;

   auto O = type( type_obj );
   auto T = type( type_form );

   auto O2T = type( type_func, T, { O } );
   auto O2O = type( type_func, O, { O } );

   auto OO2T = type( type_func, T, { O, O } );
   auto OOO2T = type( type_func, T, { O, O, O } );
   auto tp = type( type_func, T, {O} );

   std::vector< std::pair< logic::term, logic::term >> check;

   check. push_back( { logic::term( logic::op_true ),
                       logic::forall( {{ "P", T }}, lazy_implies( prop( 0_db ), implies( 0_db, 0_db ) )) } );

   check. push_back( { logic::term( logic::op_false ),
                       logic::forall( {{ "P", T }}, lazy_implies( prop( 0_db ), 0_db )) } );

   check. push_back( { ! 0_db, implies( 0_db, logic::term( logic::op_false )) } );
   
   check. push_back( { 1_db && 0_db, logic::forall( {{ "R", T }}, 
                   lazy_implies( prop( 0_db ),
                      implies( implies( 2_db, implies( 1_db, 0_db )), 0_db ))) } );

   check. push_back( { lazy_and( 1_db, 0_db ), logic::forall( {{ "R", T }},
                   lazy_implies( prop( 0_db ),
                      implies( lazy_implies( 2_db, implies( 1_db, 0_db )), 0_db ))) } );

   check. push_back( { 1_db || 0_db, logic::forall( {{ "R", T }},
                  lazy_implies( prop( 0_db ),
                     implies( implies( 2_db, 0_db ),
                        implies( implies( 1_db, 0_db ), 0_db )))) } );

   check. push_back( { equiv( 1_db, 0_db ), 
                  lazy_implies( 0_db, 1_db ) && lazy_implies( 1_db, 0_db ) } );
 
   for( const auto& p : check )
   {
      auto fm = logic::forall( {{ "P", T }, { "Q", T }}, p. first == p. second );
      natded::interpretation intp;
      std::cout << eval( intp, fm ) << "\n"; 
   }
}

