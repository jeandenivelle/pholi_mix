
#include "context.h"

void logic::context::restore( size_t s )
{
   while( vect. size( ) > s )
   {
      vect. pop_back( );
      defs. erase( vect. size( ));
   }
}


void logic::context::print( std::ostream& out ) const
{
   out << "Context:\n";
   // for( auto ind = 1 - (ssize_t) size( ); const auto& b : vect ) 

   for( auto ind = 1 - (ssize_t) size( ); const auto& b : vect ) 
   {
      out << "   #" << ind << " (" << b. first << ")   ";

      if( auto p = defs. find( size( ) + ind - 1 ); p != defs. end( )) 
      {
         out << ":= " << ( p -> second ) << " "; 
      }

      out << ": " << b. second << "\n";

      ++ ind; 
   }
}


