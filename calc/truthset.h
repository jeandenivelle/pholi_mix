
#ifndef CALC_TRUTHSET_
#define CALC_TRUTHSET_

#include <iostream>
#include <vector>
#include <cstdint>

// We finally understood that a clause is not a set of literals.
// It is a mapping from atoms to sets of truth values.
// We represent the truth values by bits, and sets of truth values
// by their bitwise ors.

namespace calc
{
   struct truthset
   {
      uint8_t val;

      truthset( ) = delete;

      truthset( uint8_t val )
         : val( val )
      { }

      static constexpr uint8_t empty = 0;
      static constexpr uint8_t ffff = 1;
      static constexpr uint8_t eeee = 2;
      static constexpr uint8_t tttt = 4;

      static constexpr uint8_t ffee = ffff | eeee;
      static constexpr uint8_t eett = eeee | tttt;
      static constexpr uint8_t fftt = ffff | tttt;

      static constexpr uint8_t all = ffff | eeee | tttt;

      bool isempty( ) const
         { return val == empty; }

      bool istrivial( ) const 
         { return val == all; }

      bool subsetof( truthset s ) const 
         { return ! ( val & ~s. val ); }

      bool disjointwith( truthset s ) const
         { return ! ( val & s. val ); } 

      truthset& operator &= ( truthset s ) 
         { val &= s. val; return *this; }

      truthset& operator |= ( truthset s ) 
         { val |= s. val; return *this; }

      void print( std::ostream& out ) const; 
   };


   inline truthset operator & ( truthset s1, truthset s2 )
      { return s1. val & s2. val; }

   inline truthset operator | ( truthset s1, truthset s2 ) 
      { return s1. val | s2. val; }

#if 0
   inline bool operator == ( truthset s1, truthset s2 )
      { return s1. val == s2. val; }
#endif

   inline std::ostream& operator << ( std::ostream& out, truthset s )
      { s. print( out ); return out; }

}

#endif

