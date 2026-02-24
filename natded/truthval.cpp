
#include "truthval.h"

const char*
natded::getcstring( truthval val ) 
{
   switch( val )
   {
   case ffff: 
      return "ffff"; 
   case eeee:
      return "eeee"; 
   case tttt:
      return "tttt"; 
   }
   return "???"; 
}

