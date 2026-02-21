
#include "structdef.h"

void logic::structdef::print( std::ostream& out ) const
{
   out << "struct(";
   for( auto p = begin( ); p != end( ); ++ p )
   {
      if( p == repr. begin( )) 
         out << " ";
      else
         out << ", ";
      out << *p;  
   }
   out << " )"; 
}

