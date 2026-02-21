
#ifndef LOGIC_CONTEXT_
#define LOGIC_CONTEXT_   

#include <iostream>
#include <vector>
#include <string>

#include "type.h"
#include "util/print.h"

namespace logic 
{

   class context 
   {
      std::vector< std::pair< std::string, type >> vect; 
         // As usual, the string is only a suggestion.
 
   public:
      context( ) noexcept = default;
      context( context&& ) noexcept = default;
      context& operator = ( context&& ) noexcept = default; 

      void append( const std::string& name, const type& tp )
         { vect. push_back( std::pair( name, tp )); } 
            // The name is only a suggestion. When terms are printed, 
            // the pretty printer interprets trailing digits as an index, 
            // and may decide to replace them by another index. 
            // This is done in order to ensure uniqueness of names.
            // See in class uniquenamestack. 

      void restore( size_t s );

      size_t size( ) const 
         { return vect. size( ); } 

      // Correctly index a De Bruijn index.
      // The name is only a suggestion. If you want to print,
      // the name should be made unique with help of a localnamestack. 

      const std::string getname( size_t index ) const 
         { return vect[ vect. size( ) - index - 1 ]. first; }

      const type& gettype( size_t index ) const
         { return vect[ vect. size( ) - index - 1 ]. second; } 

      void print( std::ostream& out ) const;
   };

}

#endif


