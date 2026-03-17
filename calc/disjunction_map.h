
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
   // It was a nice idea, but we are not using it any more:

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

      bool contradicting( const std::pair<F,truthset> & lit1,
                          const std::pair<F,truthset> & lit2 ) const
      {
         return lit1. second. contradicts( lit2. second ) &&
                eq( lit1. first, lit2. first );
      }


      bool implies( const std::pair<F,truthset> & lit1,
                    const std::pair<F,truthset> & lit2 ) const
      {
         return lit1. second. implies( lit2. second ) &&
                eq( lit1. first, lit2. first );
      }

      bool implies( const disjunction_map& other ) const;
         // A weak approximation of course. 

      bool implies( const disjunction_map& other,
                    const_iterator without ) const;

   };


#if 0
   template< typename F, typename E >
   disjunction_map<F,E> 
   unitresolve( const std::pair<F,truthset> & lit, 
                const disjunction_map<F,E> & disj )
   {
      disjunction_map<F,E> res;
      for( const auto& lit2 : disj )
      {
         if( !contradicting( lit, lit2 ))
            res. append( lit2. first, lit2. second );
      }
      return res; 
   }

   template< typename F, typename E, logic::replacement R >
   disjunction_map<F,E> :: const_iterator
   findreplaceable( R& repl, disjunction_map<F,E> & disj )
   {
      E eq; 
      for( auto p = disj. begin( ); p != disj. end( ); ++ p )
      {
         auto f = outermost( repl, p -> first, 0 );
         if( !eq( p -> first, f ))
            return p; 
      }
      return disj. end( ); 
   }


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

