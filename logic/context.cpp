
#include "context.h"

void logic::context::restore( size_t s )
{
   while( vect. size( ) > s )
      vect. pop_back( );
}

void logic::context::print( std::ostream& out ) const
{
   out << "Context:\n";
   for( auto ind = 1 - (ssize_t) size( ); const auto& b : vect ) 
   {
      out << "   #" << ind << " : ";
      out << b. first << "    " << b. second << "\n";

      ++ ind;
   }
}

