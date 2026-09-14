
#ifndef PARTIAL_ORDER_MIN_
#define PARTIAL_ORDER_MIN_

#include <concepts>
#include <iterator>

// Find the minimal element in a partially ordered set.
// A partial order is transitive and irreflexive.
// (For example : string s1 is a strict prefix of string s2.) 
// If there is no minimum, or the minimum is not unique,
// we return the end iterator. 

template< std::forward_iterator Iter, 
          std::relation< std::iter_value_t< Iter >, 
                         std::iter_value_t< Iter >> R >
Iter partial_order_min( Iter it1, Iter it2, R&& r )
{

   if( it1 == it2 )
      return it1;

   // I think we need two passes:

   auto min = it1; 
   auto i = it1; ++ i;
   while( i != it2 )
   { 
      if( r( *i, *min ))
         min = i; 
      ++ i;
   }

   // Now we have a candidate. We check if it is really the minimal 
   // element. If it is not, we return it2 (expressing failure).

   for( auto i = it1; i != it2; ++ i )
   {
      if( i != min && !r( *min, *i ))
         return it2;
   }

   return min;
}

#endif

