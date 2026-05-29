
#include "logic/beliefstate.h"
#include "errorstack.h"
#include "sequent.h"

namespace calc
{

   struct proofchecker
   {

      logic::beliefstate blfs;
      sequent seq;
      errorstack err;
      uint64_t nrfakes;  

      std::ostream* out; 

      proofchecker( logic::beliefstate&& blfs, errorstack&& err )
         : blfs( std::move( blfs )),
           err( std::move( err )),
           nrfakes(0),
           out( nullptr ) 
      { }

      void setgoal( logic::exact fname ); 
   };   
};

