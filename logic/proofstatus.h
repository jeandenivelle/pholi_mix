
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
         // Name of the calculus used. 

      uint64_t nrsteps;
         // Using some unspecified measure. It depends on the calculus.

      uint64_t nrgaps;
         // Number of gaps in the proof. 

      uint64_t nrfakes;
         // Number of fakes in the proof. If both nrgaps and  
         // nrfakes are zero, then the goal is proven. 
         // Technically, a fake is also a gap, but it is convenient to 
         // count them separately.

      exact::unordered_map< uint64_t > dependencies;
         // Exact identifiers that the proof depends on.

      proofstatus( ) noexcept 
         : nrsteps(0), 
           nrgaps(1), 
           nrfakes(0)
      { }

   };

   std::ostream& operator << ( std::ostream& out, const proofstatus& stat );
}

#endif


