
#include "prefix.h"

void 
calc::prefix::print( std::ostream& out ) const
{
   if( this -> isempty( ))
   {
      out << "EMPTY";
      return;
   }

   if( F( ). subset( *this )) 
      out << 'F';
   if( E( ). subset( *this ))
      out << 'E';
   if( T( ). subset( *this ))
      out << 'T';
}


