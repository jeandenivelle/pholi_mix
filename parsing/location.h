
#ifndef PARSING_LOCATION_
#define PARSING_LOCATION_

#include <iostream>

namespace parsing
{

   struct location
   {
      // Note that using 'long' on microsoft compilers
      // is useless, because it is just 'unsigned int'.

      long unsigned int line;
      long unsigned int column;

      location() = delete; 

      location( long unsigned int line,
                long unsigned int column )
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
 
