
#include "counters.h"

void 
logic::debruijn_counter::operator( ) ( const term& t, size_t vardepth )
{
   // std::cout << "de Bruijn " << t << " / " << vardepth << "\n";

   if( t. sel( ) == op_debruijn )
   {
      auto v = t. view_debruijn( ). index( ); 

      // If we don't enter this if, the index is local, 
      // and we don't count it:

      if( v >= vardepth )
      {
         v -= vardepth; 
         ++ occ[v]; 
      }
   }
}

void logic::debruijn_counter::print( std::ostream& out ) const
{
   out << "DeBruijnCounter:\n";
   for( const auto& p : occ )
      out << "   #" << p. first << " : " << p. second << "\n";
}


void
logic::debruijn_cmp::operator( ) (  const term& t, size_t vardepth )
{
   if( t. sel( ) == op_debruijn )
   {
      auto ind = t. view_debruijn( ). index( );

      // If we don't enter this if, the index is local,
      // and we ignore it:

      if( ind >= vardepth )
      {
         ind -= vardepth;
         if( ind < nearest )
            nearest = ind;
      }
   }
}

void logic::debruijn_cmp::print( std::ostream& out ) const
{
   out << "Nearest DeBruijn:\n";
   out << "   #" << nearest;
}


void logic::exactcounter::operator( ) ( const term& t, size_t vardepth )
{
   switch( t. sel( ))
   {
   case op_exact:
      {
         auto ex = t. view_exact( ). ex( );
         ++ occ[ ex ]; 
         return;
      }

   case op_forall:
   case op_exists:
      {
         auto quant = t. view_quant( );
         for( size_t i = 0; i != quant. size( ); ++ i )
            count( quant. var(i). tp );
         return;
      }

   case op_let:
      count( t. view_let( ). var( ). tp );
      return;

   case op_lambda:
      {
         auto lmb = t. view_lambda( );
         for( size_t i = 0; i != lmb. size( ); ++ i )
            count( lmb. var(i). tp );
         return;
      }
   }

}


void logic::exactcounter::count( const type& tp )
{
   switch( tp. sel( ))
   {
   case type_prop:
   case type_obj:
      return;

   case type_struct:
      ++ occ[ tp. view_struct( ). def( ) ];
      return;

   case type_unchecked:
      return;

   case type_func:
      {
         auto f = tp. view_func( );
         count( f. result( ));
         for( size_t i = 0; i != f. size( ); ++ i )
            count( f. arg(i));
         return;
      }
   }
   std::cout << "exactcounter::count: " << tp. sel( ) << "\n";
   throw std::logic_error( "unknown type constructor" );
}


void logic::exactcounter::print( std::ostream& out ) const
{
   out << "ExactCounter{";
   for( auto p = occ. begin( ); p != occ. end( ); ++ p )
   {
      if( p == occ. begin( ))
         out << " ";
      else
         out << ", ";
      out << p -> first << " : " << p -> second;
   }
   out << " }";
}

