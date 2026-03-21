
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

#if 0
   // This was a nice idea, but we are not using it any more:

   // Deduction rules are not symmetric, because we assume
   // that we are simplifying the into argument, using
   // the form argument.

   template< typename R, typename F >
   concept deduction_rule =
      requires( const R r, std::pair< F, truthset > from,
                     std::pair< F, truthset > into ) 
      {{ R( from ) } ;
       { r. used } -> std::same_as< uint64_t& > ; 
       { r. simplify( into ) } -> std::convertible_to< bool > ;
       { r. apply( into ) } -> 
                std::convertible_to< std::pair< F, truthset >> ;
      };
#endif 

   template< typename F, typename E = std::equal_to<F>> 
   class disjunction_map
   {
      std::vector< std::pair< F, truthset >> map;
      E eq;

   public:
      disjunction_map( ) noexcept = default;

      bool isempty( ) const { return map. empty( ); }
      size_t size( ) const { return map. size( ); }

      using iterator = std::vector< std::pair< F, truthset >> :: iterator;
      iterator begin( ) { return map. begin( ); }
      iterator end( ) { return map. end( ); }

      using const_iterator = 
         std::vector< std::pair< F, truthset >> :: const_iterator;
      const_iterator begin( ) const { return map. cbegin( ); }
      const_iterator end( ) const { return map. cend( ); }

      void append( F f, truthset s ) 
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

      bool is_trivial( ) const
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

      bool inconflict( const std::pair<F,truthset> & lit1,
                       const std::pair<F,truthset> & lit2 ) const
      {
         return lit1. second. conflicts( lit2. second ) &&
                eq( lit1. first, lit2. first );
      }

   };


   template< typename F, typename E = std::equal_to<F>>
   bool subsumes( const std::pair<F,truthset> & lit1,
                  const std::pair<F,truthset> & lit2 )
   {
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
         if( q != skip && subsumes( lit, *q ))
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

#if 0

   resolvent( disjunction_map<F,E> & disj1, 
              typename disjunction_map<F,E> :: const_iterator it1,
              disjunction_map<F,E> & disj2, 
              typename disjunction_map<F,E> :: const_iterator it2 )
   {

      if( eq( it1 -> first, it2 -> first ) && 
          it1 -> second. contradictions( it2 -> second ))
      { 
         for( auto p1 = disj1. begin( ); p1 != disj1. end( ); ++ p1 )
         {
         
            if( p == it )
            {
               for( const auto& at : other )
               {
                  if( !eq( p -> first, at. first ) ||
                      ! p -> second. contradicts( at. second ))  
                  {
                     res. append( at. first, at. second );
                  }
               }
            }
            else
               res. append( p -> first, p -> second );
         }
      }
         return res;
   }
#endif

}

#endif

