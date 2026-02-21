
#ifndef CALC_UTIL_
#define CALC_UTIL_

#include "logic/context.h"
#include "logic/term.h"
#include "logic/counters.h"

namespace calc
{
   // We won't add a quantifier if ctxt is empty:

   logic::term
   quantify( logic::selector op, const logic::context& ctxt,
             const logic::term& body );

   std::pair< logic::debruijn_counter, logic::term >
   norm_debruijns( logic::term ff );
      // De Debruijn counts the variables in ff, but we 
      // use it only for checking which variables occur.
      // Lowest DeBruijn is mentioned first.
      // The return term is the normalization of ff,
      // where the lowest DeBruin is mapped to #0, etc. 

   logic::term
   application( logic::term fm, const logic::debruijn_counter& vars );
      // Apply f on the domain of vars, from far to near. 
      // If the De Bruijn counter is empty, we won't create
      // an empty application term.  

   logic::type
   functype( logic::type tp, const logic::context& ctxt,
             const logic::debruijn_counter& used ); 
      // Returns a functional type of form tp( T1, ..., Tn  ), where
      // the Ti are the types of the used variables in ctxt.
      // If n == 0, tp is returned unchanged. We don't create
      // a functional type without arguments. 

   logic::term
   abstraction( logic::term fm, const logic::context& ctxt, 
                const logic::debruijn_counter& vars );
      // Create lambda( v1:T1, ..., vn:Tn ), where 
      // vi:Ti are the types (and suggested names) of the used variables
      // in ctxt. As above, we don't create an empty lambda term, when
      // vars is empty.
  
}

#endif

