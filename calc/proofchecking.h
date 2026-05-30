
// Written by Hans de Nivelle, July/August 2025.

#ifndef CALC_PROOFCHECKING_
#define CALC_PROOFCHECKING_

#include <optional>

#include "errorstack.h"
#include "sequent.h"
#include "proofterm.h"

namespace calc
{

   struct bar
   {
      size_t len;
      bar( size_t len = 70 )
         : len( len )
      { }
   };

   std::ostream& operator << ( std::ostream& out, bar b );

   std::optional< logic::type >
   checktype( const logic::beliefstate& blfs,
              logic::term& tm, sequent& seq, errorstack& err );

   void checkproof( const logic::beliefstate& blfs, sequent& seq, 
                    proofterm& prf, errorstack& err, 
                    logic::exact::unordered_set& dependencies );
      // In case of failure, we vent our frustration into err.
      // As with type checkin,
      // we may try to recover from these errors, and check
      // other parts of the proof. 
      // The proofterm is not const, because we resolve overloads.
}

#endif

