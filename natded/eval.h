
#ifndef NATDED_EVAL_
#define NATDED_EVAL_

#include <iostream>

#include "logic/term.h"

#include "truthval.h"
#include "interpretation.h"

namespace natded
{
   truthval operator ! ( truthval tv );
   truthval prop( truthval tv );

   truthval operator && ( truthval tv1, truthval tv2 );
   truthval operator || ( truthval tv1, truthval tv2 );
  
   truthval lazy_and( truthval tv1, truthval tv2 );
   truthval lazy_implies( truthval tv1, truthval tv2 );

   truthval eval( interpretation& intp, const logic::term& fm ); 
} 

#endif

