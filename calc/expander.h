
#ifndef CALC_EXPANDER_
#define CALC_EXPANDER_

#include "errorstack.h"
#include "logic/beliefstate.h"

namespace calc
{

   struct expander
   {
      const identifier ident;
      size_t i;      // Counter.
      size_t repl;   // The occurrence that will be replaced.
 
      const logic::beliefstate& blfs; 
      errorstack& err; 

      expander( identifier ident, size_t repl, 
                const logic::beliefstate& blfs, errorstack& err ) noexcept
         : ident( ident ), i(0), repl( repl ),
           blfs( blfs ),
           err( err )
      { } 

      logic::term 
      operator( ) ( logic::term tm, size_t vardepth, bool& change );
      
      void print( std::ostream& out ) const;
   }; 

}

#endif


