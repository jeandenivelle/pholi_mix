
#ifndef LOGIC_PROOFSTATUS_
#define LOGIC_PROOFSTATUS_

#include <iostream>
#include <string>
#include <cstdint>

#include "exact.h"

namespace logic
{
   // We don't try to store the proof itself:

   struct proofstatus
   {
      std::string calcname;  
         // Name of the calculus used. The formula is proven
         // if calc is nonempty, and nrgaps == 0.

      uint64_t nrsteps; 
         // Number of proof steps, using some arbitrary measure.
      uint64_t nrgaps;
         // Nr of gaps in the proof. If this number is zero, 
         // then the proof is complete. 

      exact::unordered_map< uint64_t > dependencies;
         // Exact identifiers that we depend on.

      proofstatus( ) 
         : nrsteps(0),
           nrgaps(1)
      { }

   };

   std::ostream& operator << ( std::ostream& out, const proofstatus& stat );
}

#endif


