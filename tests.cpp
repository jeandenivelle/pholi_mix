
#include "tests.h"
#include "errorstack.h"

#include "logic/replacements.h" 
#include "logic/pretty.h"
#include "logic/cmp.h"
#include "logic/termoperators.h"

#include "calc/flatten.h"
#include "calc/removelets.h"
#include "calc/expander.h"
#include "calc/projection.h"
#include "calc/saturation.h"
#include "calc/structural.h"
#include "calc/proofchecker.h"

#include "labeled/eval.h"

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

   {
      auto fm = ( "aaaa"_unchecked && "bbbb"_unchecked )
                          || logic::op_false;
      fm = ( "aaaa"_unchecked || "bbbb"_unchecked ) && prop( 1_db == 1_db );

      auto dnf = calc::disjunction{ calc::exists( {}, fm ) };
      auto cnf = calc::conjunction{ calc::forall( {}, fm ) };
      std::cout << dnf << "\n";
      std::cout << cnf << "\n";

      dnf = flatten( std::move( dnf ));
      cnf = flatten( std::move( cnf )); 
      std::cout << dnf << "\n";
      std::cout << cnf << "\n";
      return; 
   }

   auto N2T = type( type_func, T, { } );

   auto O2T = type( type_func, T, { O } );
   auto O2O = type( type_func, O, { O } );
   auto OO2T = type( type_func, T, { O, O } );
   auto OOO2T = type( type_func, T, { O, type( type_struct, exact(44)), O } );

   term tm =  lazy_implies( "left"_unchecked, "right"_unchecked );
   tm = term( op_exists, tm, { { "x", O }, { "y", T }} );

   auto cnf_pos = calc::conjunction( { calc::forall( prop( tm )) } ); 
   auto dnf_pos = calc::disjunction( { calc::exists( ! ! prop( tm )) } );
   auto cnf_neg = calc::conjunction( { calc::forall( ! prop( tm )) } );
   auto dnf_neg = calc::disjunction( { calc::exists( ! prop( tm )) } );

   std::cout << "pos CNF: " << cnf_pos << "\n";
   std::cout << "pos DNF: " << dnf_pos << "\n"; 
   std::cout << "neg CNF: " << cnf_neg << "\n";
   std::cout << "neg DNF: " << dnf_neg << "\n";

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
   auto O = logic::type( logic::type_obj );
   auto F = logic::type( logic::type_form );
   auto Nat = logic::type( logic::type_unchecked, identifier( ) + "Nat" );
   auto Net = logic::type( logic::type_unchecked, identifier( ) + "Net" );
      // So that we can test generation of error messages.

   using namespace calc;

   // This is the first proof that passed!

#if 0
   if constexpr( true ) 
   {
      // This proof was completed on 16 december 2025, 05.23 CET.

      auto id = identifier( ) + "resolve";

      const auto& f = blfs. getformulas( id );
      if( f. size( ) != 1 )
         throw std::runtime_error( "cannot continue" );
      auto seq = sequent( );

      nr = seq. ctxt_define( "goal",
                             blfs. at( f. front( )). view_form( ). fm( ),
                             logic::type( logic::type_form ));
      seq. push_back( "start" );
 
      auto prf = chain( 
      { 
         proofterm( prf_cut, "goal"_unchecked ),

         // We expand the 'goal' before the branch,
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

      checkproof( blfs, prf, seq, err, calc::prf_fake( op_false ));
      std::cout << "FINAL STATE" << id << " :\n";
      seq. ugly( std::cout );
   }
#endif

   if constexpr( true )
   {
      auto id = identifier( ) + "induction";
      auto name = calc::findformula( blfs, err, id, { } ); 

      if( name. has_value( ))
      {
         calc::proofchecker check( blfs, err );
         check. setgoal( name. value( ));
         check. show( "initial" );
         check. cut( label( "initial" ), 
                     check. replacedebruijn( "goal"_unchecked ));
         check. branch( check. labelof(-1), 0, { } );

         check. expand( check. labelof(-1), 
                        check. replacedebruijn( "goal"_unchecked ). view_debruijn( ). index( ), 0 );

         check. rename( label( "initial2" ), label( "flatten" ));
         auto res = check. flatten( label( "flatten" ));
         check. branch( res. value( ), 0, { "s", "P" } );
         check. expand( check. labelof(-1), identifier( ) + "stricton", 0 ); 
         check. normalize( check. labelof(-1));

         res = check. flatten( check. labelof(-1));
         res = check. branch( res. value( ), 0, { "yy" } ); 
         res = check. import( identifier( ) + "gen_prop", { Nat, O },
                              label( "gen_prop" ));
         check. flatten( label( "gen_prop" )); 
         {
            auto tm1 = check. replacedebruijn( "s"_unchecked );
            auto tm2 = check. replacedebruijn( "yy"_unchecked );
            res = check. instantiate( label( "gen_prop1" ), { tm1, tm2 } );
         }

         res = check. simplify( label( "simplified" ));
         res = check. merge( );
         res = check. merge( );

         res = check. branch( label( "flatten2" ), 0, { "s", "P" } );
         res = check. flatten( label( "flatten3" ));

         res = check. rename( label( "flatten4" ), label( "propP" ));
         res = check. expand( check. labelof( -1 ), identifier( ) + "stricton", 0 );
         res = check. normalize( check. labelof( -1 ));
         res = check. flatten( check. labelof( -1 )); 

         res = check. flatten( label( "flatten5" ));
         res = check. branch( label( "flatten6" ), 0, {} );

         {
            auto tm = apply( "0"_unchecked, { "s"_unchecked } );
            tm =  check. replacedebruijn( tm );
            res = res = check. instantiate( label( "propP3" ), { tm } ); 
         }

         res = check. import( identifier( ) + "gen_0", { Nat },
                              label( "gen_0" ));
 
         {
            auto tm = "s"_unchecked;
            tm =  check. replacedebruijn( tm );
            res = check. flatten( res. value( ));  
            res = check. instantiate( label( "gen_1" ), { tm } );
         }
         check. flatten( label( "propP4" ));
 
         check. simplify( label( "close" ));
         check. merge( );

         check. branch( label( "flatten7" ), 0, { } );
         check. import( identifier( ) + "gen_prop", { Nat, O },
                        label( "genprop" ));
         check. flatten( check. labelof( -1 ));
         {
            auto tm1 = "s"_unchecked;
            auto tm2 = "x"_unchecked;

            tm1 = check. replacedebruijn( tm1 );
            tm2 = check. replacedebruijn( tm2 ); 
            res = check. instantiate( check. labelof( -1 ), { tm1, tm2 } );

         }

         check. simplify( label( "close" )); 
         check. merge( );

         if( !res. has_value( ))
            std::cout << "failed\n"; 

         check. branch( label( "flatten8" ), 0, { "x" } );
         check. flatten( label( "flatten9" ));
         check. flatten( label( "flatten11" ));

         check. instantiate( label( "propP3" ),
                             { check. replacedebruijn( "x"_unchecked ) } );
         check. flatten( check. labelof( -1 ));

         check. instantiate( label( "propP3" ),
                             { check. replacedebruijn( apply( "succ"_unchecked, { "s"_unchecked, "x"_unchecked } )) } );

         check. flatten( check. labelof( -1 ));

         check. import( identifier( ) + "gen_succ", { Nat, O },
                       label( "gen_succ" ));
         check. flatten( label( "gen_succ" ));
         check. instantiate( label( "gen_succ1" ),
                             { check. replacedebruijn( "s"_unchecked ),
                               check. replacedebruijn( "x"_unchecked ) } );
         check. flatten( label( "gen_succ2" ));
         check. simplify( label( "res" ));
         check. merge( );

         check. branch( label( "flatten9" ), 0, { "x" } );
         check. instantiate( label( "propP3" ),
                             { check. replacedebruijn( "x"_unchecked ) } );

         check. simplify( label( "simp" ));
         check. merge( );
         check. merge( ); 
         check. merge( );

         // This was only the refutation of !# goal.
         // Here comes the real proof:

         check. branch( check. labelof(-1), 0, { } ); 
         check. expand( check. labelof(-1),
                        check. replacedebruijn( "goal"_unchecked ). view_debruijn( ). index( ), 0 );
         check. flatten( check. labelof( -1 ));
         check. branch( check. labelof( -1 ), 0, { "s", "P" } );
         check. flatten( check. labelof( -1 ));
         check. flatten( check. labelof( -1 )); 
         check. branch( check. labelof( -1 ), 0, { "x" } );
         check. flatten( check. labelof( -1 ) );
         check. copy( check. labelof( -2 ));
         check. show( "this is probably the point" );
         check. expand( check. labelof( -1 ), identifier( ) + "gen", 0 ); 
         check. normalize( check. labelof( -1 )); 
         check. flatten( check. labelof( -1 ) );
         check. instantiate( check. labelof( -1 ), 
                             { check. replacedebruijn( lambda( {{ "x", O }},
                                lazy_and( apply( "gen"_unchecked, { "s"_unchecked, "x"_unchecked } ),
                                          apply( "P"_unchecked, { "x"_unchecked } )) )) } );
         check. normalize( check. labelof( -1 ));
         check. flatten( check. labelof( -1 ) );

         check. branch( check. labelof( -1 ), 0, { } );
         check. expand( check. labelof( -1 ), identifier( ) + "strict", 0 );
         check. normalize( check. labelof( -1 )); 
         check. flatten( check. labelof( -1 ));
         check. branch( check. labelof( -1 ), 0, { "xx" } );

         check. import( identifier( ) + "gen_prop", { Nat, O },
                       label( "gen_prop" ));
         check. flatten( check. labelof( -1 ));
         check. instantiate( check. labelof( -1 ),
                             { check. replacedebruijn( "s"_unchecked ),
                               check. replacedebruijn( "xx"_unchecked ) } );
         check. simplify( label( "emtpy" ));
         check. merge( );
         check. show( "before" );
         check. branch( check. labelof( -1 ), 0, { "xx" } );
         {
            auto prob = check. replacedebruijn( "stricton"_unchecked );
            std::cout << "prob = " << prob << "\n"; 
         }

         check. expand( label( "initial6" ), 
                        identifier( ) + "stricton", 0 );
         check. normalize( check. labelof( -1 )); 
         check. flatten( check. labelof( -1 ));
         check. instantiate( check. labelof( -1 ),
                           { check. replacedebruijn( "xx"_unchecked ) } );
         check. simplify( label( "contr" )); 
         check. merge( ); 
         check. merge( );

         check. expand( check. labelof( -1 ), 
                        identifier( ) + "isclosed", 0 );
         check. normalize( check. labelof( -1 ));
         check. flatten( check. labelof( -1 ));

         check. import( identifier( ) + "gen_0", { Nat }, label( "gen_0" ));
         check. flatten( check. labelof( -1 ));
         check. instantiate( check. labelof( -1 ),
                           { check. replacedebruijn( "s"_unchecked ) } );
         check. simplify( label( "final" ));
         check. branch( check. labelof( -1 ), 0, { "xx" } );
         check. flatten( check. labelof( -1 ));
         check. flatten( check. labelof( -1 ));
         check. instantiate( label( "initial8" ), 
                           { check. replacedebruijn( "xx"_unchecked ) } );
         check. flatten( check. labelof( -1 ));
         check. simplify( label( "final" ));
         check. import( identifier( ) + "gen_succ", { Nat, O }, label( "gen_succ" ));
         check. flatten( check. labelof( -1 ));
        
         check. instantiate( check. labelof( -1 ),
                             { check. replacedebruijn( "s"_unchecked ),
                               check. replacedebruijn( "xx"_unchecked ) } );
         check. flatten( check. labelof( -1 ));
         check. simplify( label( "closed" ));  
         check. merge( );
         check. flatten( check. labelof( -1 )); 
         check. simplify( label( "contr" )); 
         
         check. merge( );
         check. merge( );
         check. merge( );
         check. show( "finished" );
      }
      else
      { 
         errorstack::builder bld;
         bld << "no formula with name " << id << " was found"; 
         err. push( std::move( bld ));
      } 
   }

}


void 
tests::bigproof( logic::beliefstate& blfs, errorstack& err )
{
   auto O = logic::type( logic::type_obj );
   auto T = logic::type( logic::type_form );
   auto Nat = logic::type( logic::type_unchecked, identifier( ) + "Nat" );

   using namespace calc;
   auto id = identifier( ) + "justification";
   auto name = calc::findformula( blfs, err, id, { } );

   if( name. has_value( ))
   {
      calc::proofchecker check( blfs, err );
      check. setgoal( name. value( ));
      check. show( "initial" );

      check. cut( label( "initial" ),
                     check. replacedebruijn( "goal"_unchecked ));

      check. branch( check. labelof( -1 ), 1, { } );
      check. expand( check. labelof(-1),
                     check. replacedebruijn( "goal"_unchecked ). view_debruijn( ). index( ), 0 );
      check. flatten( check. labelof( -1 ));

      check. branch( check. labelof( -1 ), 0, { "s1", "s2", "x1", "x2" } );
      check. show( "unfinished" );

#if 0
      last = check. expand( last. value( ), 0, 0 );
      last = check. flatten( last. value( )); 
      last = check. branch( last. value( ), 0, { "s1", "s2", "x1", "x2" } );
      last = check. flatten( last. value( )); 
     
      last = check. expand( label( "form7" ), identifier( ) + "minhomrel", 0 ); 
      last = check. expand( last. value( ), identifier( ) + "minimal", 0 );
      last = check. normalize( last. value( ));
      last = check. flatten( last. value( )); 

      logic::term indhyp = logic::term( logic::op_false );  

      // Called Q in the report:
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
            apply( "minhomrel"_unchecked, 
              { "n1"_unchecked, "n2"_unchecked, "y1"_unchecked, "y2"_unchecked } ) &&
                "x1"_unchecked == apply( "succ"_unchecked, { "n1"_unchecked, "y1"_unchecked } ) &&
                "x2"_unchecked == apply( "succ"_unchecked, { "n2"_unchecked, "y2"_unchecked } );

         auto disj2 = logic::exists( { { "y1", O }, { "y2", O }}, lazy_and( la1, la2 ));

         indhyp = disj1 || disj2; 
         indhyp = lambda( {{ "x1", O }, { "x2", O }}, indhyp );
         indhyp = lambda( {{ "n1", Nat }, { "n2", Nat }}, indhyp );
      }
      indhyp = check. replacedebruijn( indhyp ); 
      check. deflocal( "Q", indhyp );
      auto val = check. replacedebruijn( 
                apply( "Q"_unchecked, { "s1"_unchecked, "s2"_unchecked } ));

      last = check. instantiate( last. value( ), { val } );
      last = check. flatten( last. value( ));
      last = check. branch( last. value( ), 1 );
      check. show( "!homrel( s1, s2, Q( s1, s2 )", std::cout );

      last = check. expand( last. value( ), identifier( ) + "homrel", 0 );
      last = check. normalize( last. value( ));
      last = check. flatten( last. value( ));
      last = check. branch( last. value( ), 0 );

      last = check. expand( last. value( ),
                           check. replacedebruijn( "Q"_unchecked ). view_debruijn( ). index( ), 0 );
      last = check. normalize( last. value( ));
      last = check. flatten( last. value( ));
      last = check. flatten( last. value( ));  
      check. simplify( );
      last = check. merge( );  
      last = check. branch( last. value( ), 0, { "y1", "y2" } ); 
      check. setlabel( label( "induction" ));
      last = check. flatten( last. value( ));
      last = check. expand( label( "induction3" ), 
                           check. replacedebruijn( "Q"_unchecked ). view_debruijn( ). index( ), 0 );
      last = check. normalize( last. value( ));
      last = check. flatten( last. value( )); 
 
      last = check. expand( label( "induction2" ),
                            check. replacedebruijn( "Q"_unchecked ). view_debruijn( ). index( ), 0 );
      last = check. normalize( last. value( ));
      last = check. flatten( last. value( ));
      std::cout << last. value( ) << "\n";
      check. setlabel( label( "step" ));
      last = check. branch( last. value( ), 1, { "z1", "z2" } );
      {
         auto tm1 = check. replacedebruijn( "y1"_unchecked );
         auto tm2 = check. replacedebruijn( "y2"_unchecked );
         last = check. instantiate( label( "induction" ) + 7, { tm1, tm2 } );
      }

      check. flatten( label( "step" ));
      check. flatten( label( "step1" ));

      check. simplify( ); 
      check. hide( label( "induction6" ));
      check. hide( label( "induction7" ));
      last = check. import( identifier( ) + "minhomrel_succ", 
                            { Nat, Nat }, label( "minhomrel" ));
      last = check. flatten( last. value( )); 
      {
         auto s1 = check. replacedebruijn( "s1"_unchecked );
         auto s2 = check. replacedebruijn( "s2"_unchecked );

         auto z1 = check. replacedebruijn( "z1"_unchecked );
         auto z2 = check. replacedebruijn( "z2"_unchecked );

         last = check. instantiate( last. value( ), { s1, s2, z1, z2 } );
      }
      last = check. flatten( last. value( ));
      check. simplify( );
       
      check. setlabel( label( "base" ));
      last = check. merge( );
      last = check. import( identifier( ) + "minhomrel_zero", { Nat, Nat },
                            label( "minhomrel" ));
      last = check. flatten( last. value( ));
      {
         auto tm1 = check. replacedebruijn( "s1"_unchecked );
         auto tm2 = check. replacedebruijn( "s2"_unchecked );
         last = check. instantiate( last. value( ), { tm1, tm2 } );
      }

      {
         auto tm1 = check. replacedebruijn( "y1"_unchecked );
         auto tm2 = check. replacedebruijn( "y2"_unchecked );
         last = check. instantiate( label( "induction" ) + 7, { tm1, tm2 } );
      }
      last = check. flatten( last. value( ));
      last = check. flatten( label( "base" ));
      check. simplify( ); 
      check. merge( );
      last = check. merge( );

      last = check. expand( last. value( ), identifier( ) + "stricton", 0 );
      last = check. expand( last. value( ), identifier( ) + "prod", 0 );
      last = check. normalize( last. value( ));
      last = check. flatten( last. value( ));  

      last = check. branch( last. value( ), 0, { "y1", "y2" } );
      last = check. flatten( last. value( )); 

      check. setlabel( label( "qqqq" ));
      
      last = check. expand( last. value( ) + 2,
                            check. replacedebruijn( "Q"_unchecked ). view_debruijn( ). index( ), 0 );
      last = check. normalize( last. value( ));
      last = check. flatten( last. value( ));

      last = check. import( identifier( ) + "gen_prop", { Nat, O },
                            label( "genprop" ));

      // This is the proof of #Q, which is long and boring.
      // Perhaps it shouldn't be here. One could also consider using cut. 

      last = check. branch( check. labelof(-2), 0, { "y1", "y2" } );
      {
         auto tm1 = check. replacedebruijn( "s1"_unchecked );
         auto tm2 = check. replacedebruijn( "y3"_unchecked );
         last = check. instantiate( label( "genprop" ), { tm1, tm2 } );
      }
      check. show( "this is the point", std::cout );

#if 0
   auto proof = chain( 
      { 
             {
                {
                   proofterm( prf_orrepl, -1, 0,
                   {
                      proofterm( prf_flatten, 8 ),
                      proofterm( prf_flatten, 25 ), 
                      proofterm( prf_simplify ) 
                   }),
                   proofterm( prf_existsrepl, -1, { "y1", "y2" },
                   {
                      proofterm( prf_forallelim, 9, { "y1"_unchecked, "y2"_unchecked } ),
                      proofterm( prf_simplify ) 
                   })  
                }),
                proofterm( prf_existsrepl, -1, { "y1", "y2" },
                {
                   proofterm( prf_expandlocal, -1, "Q", 0 ),
                   proofterm( prf_normalize, -1 ),
                   proofterm( prf_flatten, -1 ),
                   proofterm( prf_flatten, -1 ),
                   proofterm( prf_import, identifier( ) + "gen_prop", { Nat, O } ),
                   proofterm( prf_flatten, -1 ),
                   proofterm( prf_orrepl, -3, 0,
                   {
                      proofterm( prf_existsrepl, -1, { "y" },
                      {
                         proofterm( prf_forallelim, -3, { "s1"_unchecked, "y"_unchecked } ), 
                         proofterm( prf_simplify ),
                      }) 
                   }),
                   proofterm( prf_orrepl, -1, 0,
                   {
                      proofterm( prf_existsrepl, -1, { "", "y" },
                      {
                         proofterm( prf_forallelim, -4, { "s2"_unchecked, "y"_unchecked } ),
                         proofterm( prf_simplify ), 
                      })
                   }),
                   proofterm( prf_existsrepl, -1, { "y1a", "y2a", "y1", "y2" },  
                   {
                      proofterm( prf_flatten, -1 ),
                      proofterm( prf_flatten, -1 ),    // This makes sense when there is an alternation.
                      proofterm( prf_import, identifier( ) + "minhomrel_prop", { Nat, Nat } ),
                      proofterm( prf_flatten, -1 ),
                      proofterm( prf_forallelim, -1, { "s1"_unchecked, "s2"_unchecked } ),
                      proofterm( prf_forallelim, -1, { "y1a"_unchecked, "y2a"_unchecked } ),
                      proofterm( prf_flatten, -1 ),
                      proofterm( prf_simplify ) 
                   }) 
                }),
             }),
             proofterm( prf_normalize, -1 ),
          } ) 
        } ),
        proofterm( prf_orrepl, -1, 0,
        { 
           proofterm( prf_expandlocal, -1, "goal", 0 ),
           proofterm( prf_flatten, -1 ),
           proofterm( prf_orrepl, -1, 0,
           {
              proofterm( prf_existsrepl, -1, { "s1", "s2", "x1", "x2" },
              {
                 proofterm( prf_import, identifier( ) + "gen_prop", { Nat, O } ),
                 proofterm( prf_flatten, -1 ),
                 proofterm( prf_forallelim, -1, { "s1"_unchecked, "x1"_unchecked } ),
                 proofterm( prf_simplify )  
              })
           }),
           proofterm( prf_orrepl, -1, 0,
           {
              proofterm( prf_existsrepl, -1, { "s1", "s2", "x1", "x2" },
              {
                 proofterm( prf_import, identifier( ) + "gen_prop", { Nat, O } ),
                 proofterm( prf_flatten, -1 ),
                 proofterm( prf_forallelim, -1, { "s2"_unchecked, "x2"_unchecked } ),
                 proofterm( prf_simplify )  
              })
           }), 
           proofterm( prf_existsrepl, -1, { "s1", "s2", "x1", "x2" },
           {
              proofterm( prf_flatten, -1 ),
              proofterm( prf_flatten, -1 ),
              proofterm( prf_orrepl, -1, 0,
              {  
                  proofterm( prf_import, identifier( ) + "minhomrel_prop", { Nat, Nat } ),
                  proofterm( prf_flatten, -1 ), 
                  proofterm( prf_forallelim, -1, { "s1"_unchecked, "s2"_unchecked, 
                                                   "x1"_unchecked, "x2"_unchecked } ),
                  proofterm( prf_flatten, -1 ),
                  proofterm( prf_simplify ), 
              }),
              proofterm( prf_orrepl, -1, 0,
              {  
                 proofterm( prf_existsrepl, -1, { "x", "" },
                 {
                    proofterm( prf_simplify ),
                    proofterm( prf_import, identifier( ) + "gen_prop", { Nat, O } ),
                    proofterm( prf_flatten, -1 ),
                    proofterm( prf_forallelim, -1, { "s1"_unchecked, "x"_unchecked } ),
                    proofterm( prf_simplify )
                 })
              }),
              proofterm( prf_orrepl, -1, 0,
              {  
                 proofterm( prf_existsrepl, -1, { "", "x" },
                 {
                    proofterm( prf_import, identifier( ) + "gen_prop", { Nat, O } ),
                    proofterm( prf_flatten, -1 ),
                    proofterm( prf_forallelim, -1, { "s2"_unchecked, "x"_unchecked } ),
                    proofterm( prf_simplify )
                 })
              }),
              proofterm( prf_existsrepl, -1, { "y1", "y2" },
              {
                 proofterm( prf_flatten, -1 ),
                 proofterm( prf_flatten, -1 ),
                 proofterm( prf_import, identifier( ) + "minhomrel_prop", { Nat, Nat } ),
                 proofterm( prf_flatten, -1 ),
                 proofterm( prf_forallelim, -1, { "s1"_unchecked, "s2"_unchecked,
                                                  "y1"_unchecked, "y2"_unchecked } ),
                 proofterm( prf_flatten, -1 ),
                 proofterm( prf_simplify ) 
              }) 
           }),
        }), 
        proofterm( prf_show, "END" ) } 
   ); 

   proof. print( indentation( ), std::cout );

   checkproof( blfs, proof, seq, err );
   std::cout << "\n";
   std::cout << "FINAL STATE\n";
   seq. ugly( std::cout );
#endif
#endif
   }
   else
      std::cout << id << " not found\n";
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

