
#include "removelets.h"
#include "util.h"

#include "logic/replacements.h"

logic::term
calc::removelets( sequent& seq, 
                  logic::context& ctxt, logic::term f )
{
   if constexpr( false )
   {
      std::cout << "removelets\n";
      std::cout << ctxt << "\n";
      std::cout << f << "\n";
   }

   switch( f. sel( ))
   {
   case logic::op_exact:
   case logic::op_debruijn:
   case logic::op_unchecked:
   case logic::op_false:
   case logic::op_error:
   case logic::op_true:
      return f;

   case logic::op_not:
   case logic::op_prop:
      {
         auto un = f. view_unary( );
         un. update_sub( removelets( seq, ctxt, un. extr_sub( )));
         return f;
      }

   case logic::op_and:
   case logic::op_or:
   case logic::op_implies:
   case logic::op_equiv:
   case logic::op_lazy_and:
   case logic::op_lazy_or:
   case logic::op_lazy_implies:
   case logic::op_equals:
      {
         auto bin = f. view_binary( );
         bin. update_sub1( removelets( seq, ctxt, bin. extr_sub1( )));
         bin. update_sub2( removelets( seq, ctxt, bin. extr_sub2( )));
         return f;
      }

   case logic::op_forall:
   case logic::op_exists:
      {
         auto quant = f. view_quant( );
         size_t ss = ctxt. size( );
         for( size_t i = 0; i != quant. size( ); ++ i )
            ctxt. append( quant. var(i). pref, quant. var(i). tp );

         quant. update_body( 
            removelets( seq, ctxt, quant. extr_body( )));
             
         ctxt. restore( ss );
         return f;
      }

   case logic::op_let:
      {
         auto let = f. view_let( );
         
         auto pr = norm_debruijns( let. val( ));

         // First element counts de free variables of let. val( ).
         // We don't care about number of occurrens, only about
         // occurs/does not occur.
         // Second element is let. val( ) with variables
         // normalized to #0,#1, etc.

         logic::type tp = functype( let. var( ). tp, ctxt, pr. first );
         logic::term def = abstraction( pr. second, ctxt, pr. first ); 

#if 0
         auto ex = seq. define( let. var( ). pref, def, tp );

         auto tm = application( 
            logic::term( logic::op_exact, ex ), pr. first );

         std::cout << tm << "\n";

         auto subst = logic::singlesubst( tm );
         std::cout << subst << "\n";    
         f = outermost( subst, let. extr_body( ), 0 ); 
#endif

         throw std::runtime_error( "this is not implemented" );
         return removelets( seq, ctxt, f );
      }

   case logic::op_apply:
      {
         auto ap = f. view_apply( );
         for( size_t i = 0; i != ap. size( ); ++ i ) 
            ap. update_arg( i, removelets( seq, ctxt, ap. extr_arg(i)));
         
         ap. update_func( removelets( seq, ctxt, ap. extr_func( ))); 
         return f;  
      }

   case logic::op_lambda:
      {
         auto lam = f. view_lambda( );
         size_t ss = ctxt. size( );
         for( size_t i = 0; i != lam. size( ); ++ i )
            ctxt. append( lam. var(i). pref, lam. var(i). tp );

         lam. update_body(
            removelets( seq, ctxt, lam. extr_body( )));

         ctxt. restore( ss );
         return f;
      }
   }

   std::cout << "removelets: " << f. sel( ) << "\n";
   throw std::logic_error( "unknown selector" ); 
}

