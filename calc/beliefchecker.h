

#include <vector>

namespace calc

   // We are checking a belief. We know its name, and 
   // its universally quantified types that we used
   // for overload resolution.
   // The types are resolved.

   struct beliefchecker 
   {
      identifier name;
      std::vector< logic::type > types; 
      
      proofchecker chk;

   };

}
 
