
#ifndef PARSING_LOCATION_
#define PARSING_LOCATION_

#include <iostream>
#include <cstdint>

namespace parsing
{

   struct location
   {
      uint64_t line;
      uint64_t column;

      location() = delete; 

      location( uint64_t line, uint64_t column )
         : line( line ),
           column( column )
      { }

      void merge( const location& loc )
      { } 
   };


   inline
   std::ostream& operator << ( std::ostream& out, location loc )
   {
      out << ( loc. line + 1 ) << "/" << ( loc. column + 1 );
      return out;
   }

}

#endif
 
