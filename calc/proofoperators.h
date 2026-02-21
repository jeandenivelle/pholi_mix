
// Helper functions that make it easy to construct terms
// in code. Probably, all of these functions can go away
// when we have a good (even a temporary) parser with which 
// the test cases can be entered. 

#ifndef CALC_PROOFOPERATORS_
#define CALC_PROOFOPERATORS_

#include "proofterm.h"

namespace calc
{

   inline proofterm chain( std::initializer_list< proofterm > sub )
   {
      return proofterm( prf_chain, sub );
   }

   inline proofterm orexistselim( ssize_t ind, const std::string& name, 
                                  std::initializer_list< proofterm > sub )
   {
      return proofterm( prf_orexistselim, ind, name, sub );
   }
 
   inline proofterm show( const std::string& label )
      { return proofterm( prf_show, label ); }

}

#if 0
inline calc::proofterm operator "" _assumption( const char* c, size_t len )
   { return calc::proofterm( calc::prf_ident, identifier() + c ); }
#endif

#endif 

