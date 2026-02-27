
// Written by Hans de Nivelle, 27 Feb 2026.

#ifndef CALC_NORMALFORMS_
#define CALC_NORMALFORMS_

#include "propositional.h"
#include "quantifiers.h"

namespace calc
{

   template< typename F > using unf = forall<F> ;
   template< typename F > using enf = exists<F> ; 

   template< typename F > using cnf = conjunction< forall<F>> ;    
   template< typename F > using dnf = disjunction< exists<F>> ;
   
   template< typename F > using anf = cnf< dnf<F>> ;

}

#endif

