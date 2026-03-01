
#ifndef CALC_FLATTEN_
#define CALC_FLATTEN_

#include "logic/term.h"
#include "logic/context.h"

#include "normalforms.h"

#include "polarity.h"

namespace calc
{

   logic::term apply( const logic::term& f, polarity pol );
      // If pol is positive, we return f.
      // If pol is negative, we return either not(f),
      // or remove a negation from f.

   logic::term apply_prop( const logic::term& f, polarity pol );
      // Returns prop(f) or not( prop(f)).

   bool decomp_cnf( logic::selector op, polarity pol );
   bool decomp_dnf( logic::selector op, polarity pol );
      // True if the operator is decomposable.
      // We don't need to specify what we become, because
      // that is always clear from op.

   cnf< logic::term > flatten( cnf< logic::term > conj );
   dnf< logic::term > flatten( dnf< logic::term > disj );
   
   void 
   extract( std::vector< logic::vartype > & ctxt,
            polarity pol,
            const logic::term& fm,
            cnf< logic::term > & conj );

   void 
   extract( std::vector< logic::vartype > & ctxt, 
            polarity pol, 
            const logic::term& fm,
            dnf< logic::term > & disj );

   void
   extract_prop( std::vector< logic::vartype > & ctxt,
                 polarity pol,
                 const logic::term& fm,
                 cnf< logic::term > & conj );

   void 
   extract_prop( std::vector< logic::vartype > & ctxt,
                 polarity pol, 
                 const logic::term& fm,
                 dnf< logic::term > & disj );

}

#endif

