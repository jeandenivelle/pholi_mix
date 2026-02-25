
#ifndef CALC_PRINTING_
#define CALC_PRINTING_

#include <string_view>

#include "errorstack.h"
#include "sequent.h"

namespace calc
{
   namespace printing
   {
      errorstack::builder makeheader( const sequent& seq, 
                                      std::string_view rule );

      void 
      pretty( std::ostream& out, const sequent& seq, const logic::type& tp );

      void 
      pretty( std::ostream& out, const sequent& seq, const logic::term& tm );

      const char* viewpretty( logic::selector op ); 
   }
}

#endif

