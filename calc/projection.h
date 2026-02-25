
// Written by Hans de Nivelle, July 2025.

#ifndef CALC_PROJECTION_
#define CALC_PROJECTION_

#include "logic/beliefstate.h"

namespace calc
{

   // Reduce terms of form F(C(t_1, ... tn )), where
   // F is a field selection function, and C a constructor of the same
   // type. The result is ti, where is the index of field F. 

   struct projection
   {
      size_t counter;     // Nr. replacements made. 
      const logic::beliefstate& blfs;
 
      projection( const logic::beliefstate& blfs ) noexcept
         : counter(0),
           blfs( blfs )
      { }

      logic::term 
      operator( ) ( logic::term t, size_t vardepth, bool& change );
         // Not const, because we count the reductions.

      void print( std::ostream& out ) const;

      const logic::belief* 
      getfuncbelief( const logic::term& tm, logic::selector required ) const; 
         // Assume that tm has form f( t1 ... tn ), i.e. an application
         // term, where f is an exact identifier. In that case, we
         // return the belief of f.
         // We return nullptr, if tm does not have the right form.

   };
}

#endif
 

