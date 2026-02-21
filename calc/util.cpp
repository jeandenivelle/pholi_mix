
#include "util.h"
#include "logic/replacements.h"


logic::term
calc::quantify( logic::selector op, const logic::context& ctxt,
                const logic::term& body )
{
   if( ctxt. size( ) == 0 )
      return body;
   else
   {
      auto res = logic::term( op, body,
                              std::initializer_list< logic::vartype > ( ));
      auto q = res. view_quant( );

      // We need to do in reverse order, because context looks back:

      for( size_t i = ctxt. size( ); i -- ; )
         q. push_back( logic::vartype( ctxt. getname(i), ctxt. gettype(i) ));
      return res;
   }
}

std::pair< logic::debruijn_counter, logic::term > 
calc::norm_debruijns( logic::term ff )
{
   if constexpr( false )
   {
      std::cout << "normalizing:\n\n";
      std::cout << "   " << ff << "\n";
   }

   auto freevars = count_debruijn( ff );
      // In increasing order. That means that the
      // nearest De Bruijn variable is first.

   // The normalizing substitution replaces the variables
   // in f by #0,#1,#2, ...

   logic::sparse_subst norm;
   size_t var = 0;
   for( const auto& f : freevars )
   {
      norm. assign( f. first, logic::term( logic::op_debruijn, var ));
      ++ var;
   }

   // std::cout << "normalizer = " << norm << "\n";

   ff = outermost( norm, std::move(ff), 0 );

   return std::pair( std::move( freevars ), std::move( ff ));
}


logic::term
calc::application( logic::term fm, const logic::debruijn_counter& vars )
{
   if( vars. size( ))
   {
      fm = logic::term( logic::op_apply, fm,
                         std::initializer_list< logic::term > ( ));

      auto appl = fm. view_apply( );

      // We need to iterate in reverse order, because we want the
      // type of the furthest De Bruijn variable first:

      auto it = vars. end( ); 
      while( it != vars. begin( ))
      {
         -- it;
         size_t vv = it -> first;
         appl. push_back( logic::term( logic::op_debruijn, vv ));
      }
   }

   return fm;
}


logic::type
calc::functype( logic::type tp, const logic::context& ctxt,
                const logic::debruijn_counter& used )
{
   // We won't create a functional type without arguments: 

   if( used. size( ))
   {
      tp = logic::type( logic::type_func, tp, { } );
      auto fun = tp. view_func( );

      auto it = used. end( );
      while( it != used. begin( ))
      {
         -- it;
         size_t vv = it -> first; 
         fun. push_back( ctxt. gettype( vv ));
      } 
   } 
   return tp;  
}


logic::term
calc::abstraction( logic::term fm, const logic::context& ctxt,
                   const logic::debruijn_counter& used )
{
   if( used. size( ))
   {
      fm = logic::term( logic::op_lambda, fm, 
                        std::initializer_list< logic::vartype > ( ));
      auto lam = fm. view_lambda( ); 

      auto it = used. end( );
      while( it != used. begin( ))
      {
         -- it;
         size_t vv = it -> first;
         lam. push_back( 
                 logic::vartype( ctxt. getname( vv ), ctxt. gettype( vv )) );
      }
   }

   return fm;
}

