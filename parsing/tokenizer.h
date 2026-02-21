
#ifndef PARSING_TOKENIZER_
#define PARSING_TOKENIZER_ 

#include "symbol.h"
#include "lexing2023/includes.h"

namespace parsing 
{

   struct tokenizer
   {
      lexing::filereader inp;

   public:
      tokenizer( ) = delete;

      tokenizer( lexing::filereader&& inp );

      lexing::classifier< char, symbolval > buildclassifier( );

      location getlocation( ) const 
         { return location( inp.line, inp.column ); }

      symbol read( );

      void test( );
   };

}

#endif
