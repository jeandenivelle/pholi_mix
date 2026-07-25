
// Reads all proof in a single file.

#ifndef CALC_PROOFPARSER_
#define CALC_PROOFPARSER_

#include <filesystem>
#include <optional>

#include "errorstack.h"
#include "logic/term.h"
#include "parsing/parser.h"

namespace calc
{

   struct parse_error 
   {
      parsing::location loc;
      std::string cause;

      parse_error( parsing::location loc, const char* c )
         : loc( loc ), cause(c) 
      { }
   };

   struct proofparser
   {
      parsing::tokenizer tok;
      std::optional< parsing::symbol > lookahead;
      errorstack err; 
     
      proofparser( ) = delete;
     
      explicit proofparser( parsing::tokenizer&& tok ) noexcept
         : tok( std::move( tok ))
      { }
     
      // ~filescanner( ); Should crash if there are unprocessed errors. 

      logic::type parse_type( );
      std::optional< logic::term > parseterm( errorstack& err );
         // Both use Maphoon constructed parser.

      identifier parse_identifier( );

      void move_errors( errorstack& global );
         // Move our errors to global, and append a header.

      const parsing::symbol& getlookahead( );
      void resetlookahead( );

      void check( logic::beliefstate& blfs );
   };


   bool checkfile( logic::beliefstate& blfs, 
                   errorstack& err, 
                   const std::filesystem::path& file );
      // Check the current file, the proofs of the theorems whose names
      // contains sub. We return true if we could read the file.
      // It doesn't mean that all proofs passed. 
}

#endif

