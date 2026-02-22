
#ifndef CALC_REMOVELETS_
#define CALC_REMOVELETS_

// Remove let operators by taking the definition out of the term,
// and putting it in the beliefstate.

#include "sequent.h"
#include "logic/context.h"

namespace calc
{

   logic::term
   removelets( sequent& seq, logic::context& ctxt, logic::term f );
      // Replace lets by global definitions.
      // Since lets are rare, we try to reuse parts of f as much as possible. 
      // We cannot handle Kleene operators.

}

#endif

