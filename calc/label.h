
#ifndef CALC_LABEL_
#define CALC_LABEL_

#include <string>
#include <string_view> 
#include <iostream>
#include <cstdint>

namespace calc
{
   struct label
   {
      std::string base;
      uint64_t index;

      label( ) = delete;
      label( std::string_view str );

      label( const char* c ) 
         : label( std::string_view(c))
      { }

      label& operator ++ ( )
         { ++ index; return *this; }

      label operator ++ ( int )
         { auto copy = *this; ++ index; return copy; }  
   };

   bool operator < ( const label& lab1, const label& lab2 );
   bool operator == ( const label& lab1, const label& lab2 );

   inline  
   bool operator > ( const label& lab1, const label& lab2 )
      { return lab2 < lab1; }  

   inline 
   bool operator <= ( const label& lab1, const label& lab2 )
      { return !( lab2 < lab1 ); }

   inline
   bool operator >= ( const label& lab1, const label& lab2 )
      { return !( lab1 < lab2 ); }

   inline 
   bool operator != ( const label& lab1, const label& lab2 )
      { return !( lab1 == lab2 ); }

   std::ostream& operator << ( std::ostream& out, const label& lab );
}

#endif

