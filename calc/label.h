
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

      explicit label( const char* c ) 
         : label( std::string_view(c))
      { }

      label& operator ++ ( )
         { ++ index; return *this; }

      label operator ++ ( int )
         { auto copy = *this; ++ index; return copy; }  

      struct hash
      {
         hash( ) noexcept = default; 
         size_t operator( ) ( const label& lab ) const;
      };

      struct equal_to
      {
         equal_to( ) noexcept = default;
         bool operator( ) ( const label& lab1, const label& lab2 ) const;
      };

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

