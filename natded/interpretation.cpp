
#include "interpretation.h"

void natded::interpretation::restore( size_t ss )
{
   while( values. size( ) > ss )
      values. pop_back( );
}

void natded::interpretation::print( std::ostream& out ) const
{
   out << "Interpretation:\n";
   for( auto ind = 1 - (ssize_t) size( ); const auto& v : values )
   {
      out << "   #" << ind << " : " << v << "\n";
      ++ ind;
   }
}


