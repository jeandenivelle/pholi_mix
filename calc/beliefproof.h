
#ifndef CALC_BELIEFPROOF_
#define CALC_BELIEFPROOF_

#include <vector>

#include "identifier.h"
#include "proofchecker.h"

namespace calc
{
   // We are checking a belief. We know its name, and 
   // its universally quantified types that we used
   // for overload resolution.
   // The types are resolved.

   struct beliefproof
   {
      identifier name;
      std::vector< logic::type > types; 

      proofchecker check;

      beliefproof( identifier&& name, 
                   std::vector< logic::type > && types,
                   const logic::beliefstate* blfs )
         : name( std::move( name )),
           types( std::move( types )),
           check( blfs ) 
      { }

      bool init( ) { return true; }
        // Resolve types, look up the name, return true if it succeeded.

      bool has_errors( ) const 
         { return check. err. size( ); }

   };

}

#endif
 
