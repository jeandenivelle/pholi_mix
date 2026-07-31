
#ifndef CALC_PROOFCHECKERWITHNAME_
#define CALC_PROOFCHECKERWITHNAME_

#include <vector>

#include "logic/exact.h"
#include "proofchecker.h"

namespace calc
{
   // One can use this class if one knows the 
   // name of the formula being proven, and its universal types.  
   // We assume that the universal types have been checked and resolved.

   struct proofcheckerwithname : public proofchecker
   {
      logic::exact name;  
      std::vector< logic::type > types; 

      proofcheckerwithname( logic::exact name, 
                   const logic::term& goal,
                   std::vector< logic::type > types,
                   const logic::beliefstate* blfs )
         : proofchecker( blfs, goal ),
           name( name ),
           types( std::move( types )) 
      { }

   };

}

#endif
 
