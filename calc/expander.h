
#ifndef CALC_EXPANDER_
#define CALC_EXPANDER_

#include "errorstack.h"
#include "logic/beliefstate.h"

namespace calc
{

   struct expander
   {
      const identifier ident;
      uint64_t i;      // Counts occurrences of ident. 
      size_t repl;     // The occurrence that will be replaced.
      uint64_t used;   // Number of replacements made, one at most.
 
      const logic::beliefstate& blfs; 
      errorstack& err; 

      expander( identifier ident, size_t repl, 
                const logic::beliefstate& blfs, errorstack& err ) noexcept
         : ident( ident ), i(0), repl( repl ), used(0),
           blfs( blfs ),
           err( err )
      { } 

      logic::term operator( ) ( logic::term tm, size_t vardepth );
      
      void print( std::ostream& out ) const;
   }; 

}

#endif


