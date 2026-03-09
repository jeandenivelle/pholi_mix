
#ifndef CALC_DISJUNCTION_MAP_
#define CALC_DISJUNCTION_MAP_

#include <iostream>
#include <vector>

#include "truthset.h"

// We finally understood that a clause is not a set of literals.
// It is a mapping from atoms to sets of truth values.
// We represent the truth values by bits, and sets of truth values
// by their bitwise ors.

namespace calc
{

   template< typename F, typename E = std::equal_to<F>> 
   class disjunction_map
   {
      std::vector< std::pair< F, truthset >> map;

      F f;
      E eq;

   public:
      disjunction_map( ) noexcept = default;

      bool isempty( ) const { return map. empty( ); }
      size_t size( ) const { return map. size( ); }

      using iterator = std::vector< std::pair< F, truthset >> :: iterator;
      iterator begin( ) { return map. begin( ); }
      iterator end( ) { return map. end( ); }

      void append( F f, truthset s = truthset::tttt ) 
         { map. push_back( std::pair( std::move(f), s )); }

      // Remove F-s with empty truthset:

      void remove_empty( )
      {
         auto p1 = begin( );
         auto p2 = p1; 
         while( p2 != end( ))
         {
            if( p2 -> second. implies( truthset::empty ))
               ++ p2;
            else
               *p1 ++ = std::move( *p2 ++ );
         }
 
         map. erase( p1, end( )); 
      }

      // Merge equal F-s, where equality is determined by our
      // E object. This is a quadratic procedure: 
      // After merge( ), one can do remove_empty( ).
 
      void merge( )
      {
         for( auto p2 = begin( ); p2 != end( ); ++ p2 )    
         {
            for( auto p1 = begin( ); p1 != p2; ++ p1 )
            {
               if( eq( p1 -> first, p2 -> first ))
               {
                  ( p1 -> second ) |= p2 -> second;
                  ( p2 -> second ) = truthset::empty;
               }
             } 
         }
      }

      void print( std::ostream& out ) const
      {
         out << "Disjunction Map:\n";
         for( auto& p : map )
            out << "   " << p. first << " -> " << p. second << "\n";
      }

   };


}

#endif

