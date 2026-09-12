
#ifndef LOGIC_PROOFSTATUS_
#define LOGIC_PROOFSTATUS_

#include <iostream>
#include <string>
#include <cstdint>

#include "exact.h"

namespace logic
{
   // We don't to store any proofs, only whether the formula was proven. 

   struct proofstatus
   {
      std::string calcname;  
         // Name of the calculus used. 

      uint64_t nrsteps; 
      uint64_t distance; 
         // Using some unspecified measure. A distance of zero means
         // that the proof is complete. 

      exact::unordered_map< uint64_t > dependencies;

      proofstatus( ) noexcept 
         : distance( 9999999 )
      { }

   };

   std::ostream& 
   operator << ( std::ostream& out, const proofstatus& stat );
}

#endif


