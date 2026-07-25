
// Reads all proof in a single file.

#ifndef CALC_FILECHECKER_
#define CALC_FILECHECKER_

#include <filesystem>
#include <optional>
#include <string_view>

#include "errorstack.h"
#include "logic/term.h"
#include "parsing/parser.h"

namespace calc
{

   struct filechecker
   {
      std::filesystem::path file; 
      errorstack err;

      explicit filechecker( const std::filesystem::path& file )
         : file( file )
      { }
      
      // ~filechecker( ); Should crash if there are unprocessed errors. 

      std::optional< logic::type > parsetype( errorstack& err );
      std::optional< logic::term > parseterm( errorstack& err );

      void move_errors( errorstack& global );
         // Move our errors to global, and append a header.

      bool check( logic::beliefstate& blfs, std::string_view sub );
         // Check the current file, the proofs of the theorems whose names
         // contains sub. We return true if we could read the file.
         // It doesn't mean that all proofs passed. 
   };

}

#endif

