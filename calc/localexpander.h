
#ifndef CALC_LOCALEXPANDER_
#define CALC_LOCALEXPANDER_

#include "logic/term.h"

namespace calc
{

   // Expands a local definition #var := value.
   // Only the i-th occurrence is expanded.
   // Value will be lifted over ( var + 1 ).

   struct localexpander
   {
      size_t var; 
      logic::term value;

      size_t i;      // Counter.
      size_t repl;   // Occurrence that will be replaced.
 
      localexpander( size_t var, const logic::term& value, size_t repl )
      noexcept
         : var( var ), value( value ), i(0), repl( repl ) 
      { } 

      logic::term 
      operator( ) ( logic::term tm, size_t vardepth, bool& change );
      
      void print( std::ostream& out ) const;
   }; 

}

#endif


