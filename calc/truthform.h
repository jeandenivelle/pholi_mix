
#ifndef CALC_TRUTHFORM_
#define CALC_TRUTHFORM_

#include <concepts>
#include <iostream>
#include "truthset.h"

// We finally understood that a clause is not a set of literals.
// It is a mapping from atoms to sets of truth values.
// We represent the truth values by bits, and sets of truth values
// by their bitwise ors.

namespace calc
{

   template< typename F, std::equivalence_relation<F,F> E = std::equal_to<F>>
   struct truthform
   {
      F fm;
      truthset lab;

      truthform( const F& fm, truthset lab = truthset::tttt ) 
         : fm( fm ), lab( lab )
      { }

      truthform( F&& fm, truthset lab = truthset::tttt )
         : fm( std::move( fm )), lab( lab )
      { }

      bool subsumes( const truthform& other ) const
      { 
         E eq; 
         return lab. implies( other. lab ) ? eq( fm, other. fm ) : false;
      }

      bool conflicts( const truthform& other ) const
      {
         E eq; 
         return lab. conflicts( other. lab ) ? eq( fm, other. fm ) : false;
      }

      bool trivially_false( ) const
      {
         return lab == truthset::empty;
      }

      bool trivially_true( ) const
      {
         return lab == truthset::all;
      }

      // Merge from into *this (disjunctively), and make from trivially false.

      bool try_join( truthform& from ) 
      {
         E eq;
         if( eq( fm, from. fm ))
         {
            lab |= from. lab;
            from. lab = truthset::empty;
            return true;
         }
         return false;
      } 

      void print( std::ostream& out ) const
         { out << fm << " / " << lab; }
 
   };

}

#endif

