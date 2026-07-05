
#include "position.h"


void logic::position::extend( unsigned int p )
{
   vect. push_back(p);
}

void logic::position::restore( size_t s )
{
   while( vect. size( ) > s )
      vect. pop_back( );
}

size_t
logic::position::firstdifference( const position& other ) const
{
   size_t diff = 0;
   while( diff < vect. size( ) && diff < other. vect. size( ) &&
          vect[ diff ] == other. vect[ diff ] )
   {
      ++ diff;
   }
   return diff;
}

void logic::position::print( std::ostream& out ) const
{
   out << '[';
   for( auto p = vect. begin( ); p != vect. end( ); ++ p )
   {
      if( p != vect. begin( ))
         out << ',';
      out << *p;
   }
   out << ']';
}

std::strong_ordering
logic::operator <=> ( const position& pos1, const position& pos2 )
{
   for( unsigned int i = 0; i != pos1. size( ) && i != pos2. size( ); ++ i )
   {
      auto ord = ( pos1[i] <=> pos2[i] );
      if( !is_eq( ord )) 
         return ord;  
   }

   return pos1. size( ) <=> pos2. size( ); 
}


