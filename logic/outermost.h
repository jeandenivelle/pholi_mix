
// Written by Hans de Nivelle, Sept 2022 
// Rewritten Dec. 2024. I changed the interface
// to use only SAR, and I adapted it for PHOLI.
// July 2025. I renamed from 'topdown' to 'outermost', to use standard
// terminology.

#ifndef LOGIC_OUTERMOST_
#define LOGIC_OUTERMOST_    

#include <iostream>
#include <concepts>
#include <cstdint>

namespace logic
{

   template< typename R >
   concept replacement =
      requires( R r, term t, size_t vardepth )
         { { r. used } -> std::same_as< uint64_t& > ;
           { r( t, vardepth ) } -> std::same_as< term > ; 
         };


   template< replacement R >
   term outermost( R& repl, term t, size_t vardepth )
   {
      if constexpr( false )
      {
         std::cout << "entering (non-const) outermost " << t;
         std::cout << " at vardepth " << vardepth << "\n";
      }

      {
         auto u = repl. used;  
         t = repl( std::move(t), vardepth );
         if( u != repl. used )
            return t;
      }

      switch( t. sel( ))
      {
      case op_exact:
      case op_debruijn:
      case op_unchecked:
      case op_false: 
      case op_error:
      case op_true:
         return t; 

      case op_not:
      case op_prop:
         {
            auto p = t. view_unary( );
            p. update_sub( outermost( repl, p. extr_sub( ), vardepth ));
         }
         return t;

      case op_and:
      case op_or:
      case op_implies:
      case op_equiv:
      case op_lazy_and:
      case op_lazy_implies:
      case op_meta_implies:
      case op_equals:
         {
            auto bin = t. view_binary( );
            bin. update_sub1( outermost( repl, bin. extr_sub1( ), vardepth ));
            bin. update_sub2( outermost( repl, bin. extr_sub2( ), vardepth ));
         }
         return t;

      case op_forall:
      case op_exists:
         {
            auto q = t. view_quant( );
            q. update_body( outermost( repl, q. extr_body( ), 
                            vardepth + q. size( ) ));
         }
         return t;

      case op_let:
         {
            auto let = t. view_let( );
            let. update_val( outermost( repl, let. extr_val( ), vardepth ));
            let. update_body( outermost( repl, let. extr_body( ), 
                              vardepth + 1 ));
         }
         return t;

      case op_apply:
         {
            auto ap = t. view_apply( );
            ap. update_func( outermost( repl, ap. extr_func( ), vardepth ));
            for( size_t i = 0; i != ap. size( ); ++ i )
            {
               ap. update_arg( i, outermost( repl, ap. extr_arg(i), 
                               vardepth ));
            }
         } 
         return t;

      case op_lambda:
         {
            auto lam = t. view_lambda( );
            lam. update_body( outermost( repl, lam. extr_body( ), 
                              vardepth + lam. size( ) ));
         }
         return t;
      }

      std::cout << "selector = " << t. sel( ) << "\n"; 
      throw std::runtime_error( 
            "outermost-(not const) const: case not implemented" );
   }
}


#endif



