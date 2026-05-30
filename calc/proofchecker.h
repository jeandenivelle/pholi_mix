
#include <optional>

#include "logic/beliefstate.h"
#include "errorstack.h"
#include "sequent.h"

namespace calc
{

   struct proofchecker
   {
      const logic::beliefstate& blfs; 
      errorstack& err;

      sequent seq;
      indexedstack< std::string, size_t > db;
      uint64_t nrfakes;  

      std::ostream* show; 

      explicit proofchecker( const logic::beliefstate& blfs,
                             errorstack& err )
         : blfs( blfs ), err( err ),
           nrfakes(0),
           show( nullptr ) 
      { }

      void setgoal( logic::exact fname ); 

      std::optional< label > cut( logic::term fm );

      std::optional< label >  
      orexists( label fm, size_t choice,
                const std::vector< std::string > & eigen = { } );

      std::optional< label > expand( label fm, size_t var, size_t occ );
         // var must be a De Bruijn index. 

      logic::term replacedebruijn( logic::term tm );

   private: 
      std::optional< logic::type > checktype( logic::term& tm );

      void define( const std::string& name, 
                   const logic::term& val, const logic::type& tp );
   }; 

};


