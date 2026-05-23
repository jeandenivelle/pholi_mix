
#include "label.h"

calc::label::label( std::string_view str )
   : index(0) 
{
   uint64_t pow = 1;
   while( str. size( ) && isdigit( str. back( )))
   {
      index += pow * ( str. back( ) - '0' );
      str. remove_suffix(1);
      pow *= 10; 
         // If this gets too big, we just let it overflow.
         // Some number will be produced.
   }

   if( str. size( ))
      base = std::string( str );
   else
      base = "form";
}

bool calc::operator == ( const label& lab1, const label& lab2 )
{
   return lab1. base == lab2. base && lab1. index == lab2. index;
}

bool calc::operator < ( const label& lab1, const label& lab2 )
{
   if( lab1. base < lab2. base ) return true;
   if( lab1. base == lab2. base ) return lab1. index < lab2. index;
   return false;
}

size_t 
calc::label::hash::operator( ) ( const label& lab ) const
{
   std::hash< std::string > str;
   std::hash< size_t > sz;
   return str( lab. base ) + 19 * sz( lab. index );
}

bool 
calc::label::equal_to::operator( ) 
              ( const label& lab1, const label& lab2 ) const
{
   return lab1. base == lab2. base && lab1. index == lab2. index;
}

std::ostream& calc::operator << ( std::ostream& out, const calc::label& lab )
{
   out << lab. base;
   if( lab. index != 0 )
      out << lab. index; 
   return out;
}

