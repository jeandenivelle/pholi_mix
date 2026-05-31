
// Written by Hans de Nivelle, May/June 2026.
// This should become the trusted core.

#ifndef CALC_PROOFCHECKER_
#define CALC_PROOFCHECKER_

#include <optional>

#include "logic/beliefstate.h"
#include "errorstack.h"
#include "sequent.h"

namespace calc
{

   struct bar
   {
      size_t len;
      bar( size_t len = 70 )
         : len( len )
      { }
   };

   std::ostream& operator << ( std::ostream& out, bar b );

   struct proofchecker
   {
      const logic::beliefstate& blfs; 
      errorstack& err;

      sequent seq;
      indexedstack< std::string, size_t > db;
      uint64_t nrfakes;  

      explicit proofchecker( const logic::beliefstate& blfs,
                             errorstack& err )
         : blfs( blfs ), err( err ),
           nrfakes(0) 
      { }

      void setgoal( logic::exact fname ); 

      // The functions that follow return a label if they succeed.

      std::optional< label > cut( logic::term fm );

      // If you want to parse expressions, you must set the
      // names of the eigenvariables.

      std::optional< label >  
      orexists( label fm, size_t choice,
                const std::vector< std::string > & eigen = { } );

      std::optional< label > 
      expand( label fm, const identifier& ident, size_t occ ); 

      std::optional< label > 
      expand( label fm, size_t var, size_t occ );
         // var must be a De Bruijn index. 

      std::optional< label > flatten( label fm );
      std::optional< label > normalize( label fm );

      bool deflocal( std::string_view name, logic::term val );

      logic::term replacedebruijn( logic::term tm );

      void show( std::string_view label, 
                 std::ostream& out = std::cout ) const;

   private: 
      std::optional< logic::type > checktype( logic::term& tm );

      void define( const std::string& name, 
                   const logic::term& val, const logic::type& tp );
   }; 

} 

#endif

