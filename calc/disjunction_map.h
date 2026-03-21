
#ifndef CALC_DISJUNCTION_MAP_
#define CALC_DISJUNCTION_MAP_

#include <iostream>
#include <vector>
#include <concepts>

#include "truthset.h"
#include "logic/replacements.h"
#include "logic/outermost.h"

// We finally understood after trying to implement resolution since
// 1998 that a clause is not a set of literals.
// It is a mapping from atoms to sets of truth values.
// We represent the truth values by bits, and sets of truth values
// by their bitwise ors.

namespace calc
{

   template< typename S, typename F >
   concept simplifier =
      requires( S simpl, std::pair< F, truthset > lit )
      {{ S( lit ) } ;
       { simpl. usable( ) } -> std::convertible_to< bool > ;
       { simpl. used } -> std::same_as< uint64_t& > ; 
       { simpl. operator( ) ( lit ) } -> 
                std::convertible_to< std::pair< F, truthset >> ;
      };


   template< typename F, typename E = std::equal_to<F>> 
   class disjunction_map
   {
      std::vector< std::pair< F, truthset >> map;
      E eq;

   public:
      disjunction_map( ) noexcept = default;

      bool isempty( ) const { return map. empty( ); }
      size_t size( ) const { return map. size( ); }

      // In general, we have no iterator stability!

      using iterator = std::vector< std::pair< F, truthset >> :: iterator;
      iterator begin( ) { return map. begin( ); }
      iterator end( ) { return map. end( ); }

      using const_iterator = 
         std::vector< std::pair< F, truthset >> :: const_iterator;
      const_iterator begin( ) const { return map. cbegin( ); }
      const_iterator end( ) const { return map. cend( ); }

      void append( F f, truthset s ) 
         { map. push_back( std::pair( std::move(f), s )); }

      iterator erase( iterator it ) 
         { return map. erase( it ); }

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

      // True if the clause is very obviously trivial:

      bool istrivial( ) const
      {
         for( const auto& lit : map )
         {
            if( lit. second == truthset::all )
               return true;
         }
         return false; 
      }

      void print( std::ostream& out ) const
      {
         out << "Disjunction Map:\n";
         for( auto& p : map )
            out << "   " << p. first << " -> " << p. second << "\n";
      }

   };


   template< typename F, typename E = std::equal_to<F>>
   bool subsumes( const std::pair<F,truthset> & lit1,
                  const std::pair<F,truthset> & lit2 )
   {
      E eq;
      return lit1. second. implies( lit2. second ) &&
             eq( lit1. first, lit2. first );
   }


   template< typename F, typename E = std::equal_to<F>>
   bool 
   subsumes( const std::pair<F, truthset > & lit,
             const disjunction_map<F,E> & disj, 
             typename disjunction_map<F,E> :: const_iterator skip )
   {
      for( auto q = disj. begin( ); q != disj. end( ); ++ q )
      {
         if( q != skip && subsumes<F,E> ( lit, *q ))
            return true;
      }
      return false;
   }


   template< typename F, typename E = std::equal_to<F>>
   bool 
   subsumes( const disjunction_map<F,E> & disj1, 
             typename disjunction_map<F,E> :: const_iterator skip1,
             const disjunction_map<F,E> & disj2,
             typename disjunction_map<F,E> :: const_iterator skip2 )
   {
      for( auto p1 = disj1. begin( ); p1 != disj1. end( ); ++ p1 )
      {
         if( p1 != skip1 && !subsumes( *p1, disj2, skip2 ))
            return false;
      }
      return true;
   }


   template< typename F, typename E = std::equal_to<F>>
   bool 
   conflicts( const std::pair<F,truthset> & lit1,
              const std::pair<F,truthset> & lit2 ) 
   {
      E eq;
      return lit1. second. conflicts( lit2. second ) &&
             eq( lit1. first, lit2. first );
   }


   template< typename F, simplifier<F> S, typename E = std::equal_to<F>>
   bool simplify( const disjunction_map<F,E> & from,
                  disjunction_map<F,E> & into )
   {
      for( auto p = from. begin( ); p != from. end( ); ++ p )
      {
         auto simpl = S( *p );
         if( simpl. usable( ))
         {
            for( auto q = into. begin( ); q != into. end( ); ++ q )
            {
               *q = simpl( std::move(*q));
               if( simpl. used && subsumes( from, p, into, q ))
                  return true;
            }
         }
      }
      return false; 
   }


}

#endif

