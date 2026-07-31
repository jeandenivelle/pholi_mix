
#ifndef LOGIC_PROOFSTATUS_
#define LOGIC_PROOFSTATUS_

#include <iostream>
#include <string>
#include <cstdint>

#include "exact.h"

namespace logic
{
   // We don't try to store the proof itself, only the fact
   // that the formula was proven. 

   struct proofstatus
   {
      std::string calcname;  
         // Name of the calculus used. The formula is proven
         // if calc is nonempty, and nrfakes == 0.

      uint64_t nrsteps;
         // Using some unspecified measure.

      uint64_t nrfakes;
         // Number of fakes in the proof. If this number is zero, 
         // and proven is true, then the proof is complete. 

      exact::unordered_map< uint64_t > dependencies;
         // Exact identifiers that the proof depends on.

      proofstatus( const char* calcname ) 
         : calcname( calcname ),
           nrsteps(0), 
           nrfakes(0)
      { }

   };

   std::ostream& operator << ( std::ostream& out, const proofstatus& stat );
}

#endif


