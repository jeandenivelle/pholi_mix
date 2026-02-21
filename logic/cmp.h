
// Written by Akhmetzhan Kussainov and Hans de Nivelle Spring 2023.
// Revised in August 2024 by Hans de Nivelle. 
// Almost completely rewritten in August 2025 by Hans de Nivelle.
// I removed Knuth-Bendix order, and replaced it by just equality.
// In September 2025, I replace the simple equality test by KBO again.

#ifndef LOGIC_CMP_
#define LOGIC_CMP_ 

#include <iostream>
#include <compare>

#include "term.h"

namespace logic
{

   using weight_type = uint_least64_t; 

   weight_type weight( const type& tp );
   weight_type weight( const term& t );

   // This implements a total, but not well-founded order:

   std::strong_ordering operator <=> ( const type& tp1, const type& tp2 );
   std::strong_ordering operator <=> ( const term& tm1, const term& tm2 );
 
   inline bool equal( const type& tp1, const type& tp2 ) 
      { return is_eq( tp1 <=> tp2 ); }

   inline bool equal( const term& tm1, const term& tm2 )
      { return is_eq( tm1 <=> tm2 ); }

   std::strong_ordering kbo( const term& tm1, const term& tm2 );
      // Compare first by weight, then by <=> .

   bool equal( const term& t1, size_t lift1, 
               const term& t2, size_t lift2, size_t vardepth );

   std::ostream& 
   operator << ( std::ostream& out, std::strong_ordering ord );

}

#endif

