
#ifndef CALC_ALTERNATING_
#define CALC_ALTERNATING_

#include "logic/term.h"
#include "logic/context.h"

#include "propositional.h"
#include "quantifiers.h"

#include "polarity.h"
#include "kleene.h"

namespace calc
{

   logic::term apply( const logic::term& f, polarity pol );
      // If pol is positive, we return f.
      // If pol is negative, we return either not(f),
      // or try to remove a negation from f.

   logic::term apply_prop( const logic::term& f, polarity pol );
      // Return prop(f) or not( prop(f)).


   template< typename F >
   using dnf = disjunction< exists<F>> ;

   template< typename F >
   using anf = conjunction< forall< dnf<F>>> ;


   kleene kleening( logic::selector sel, polarity pol );

   anf< logic::term > flatten( anf< logic::term > conj );
   dnf< logic::term > flatten( dnf< logic::term > disj );

   void extract( std::vector< logic::vartype > & ctxt,
            polarity pol,
            const logic::term& fm,
            conjunction< forall< logic::term >> & conj );

   void extract( std::vector< logic::vartype > & ctxt, 
            polarity pol, 
            const logic::term& fm,
            dnf< logic::term > & disj );

   void
   extract_prop( std::vector< logic::vartype > & ctxt,
                 polarity pol,
                 const logic::term& fm,
                 conjunction< forall< logic::term >> & conj );

   void 
   extract_prop( std::vector< logic::vartype > & ctxt,
                 polarity pol, 
                 const logic::term& fm,
                 dnf< logic::term > & disj );

}

#endif

