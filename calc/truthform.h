
#ifndef CALC_TRUTHFORM_
#define CALC_TRUTHFORM_

#include <concepts>
#include <iostream>
#include "truthset.h"


namespace calc
{

   template< typename F >
   struct truthform
   {
      F fm;
      truthset lab;

      truthform( const F& fm, truthset lab ) 
         : fm( fm ), lab( lab )
      { }

      truthform( F&& fm, truthset lab )
         : fm( std::move( fm )), lab( lab )
      { }

      void print( std::ostream& out ) const
         { out << fm << " / " << lab; }
 
   };

}

#endif

