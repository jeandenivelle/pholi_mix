
#ifndef CALC_DISJUNCTION_MAP_
#define CALC_DISJUNCTION_MAP_

#include <iostream>
#include <vector>
#include <concepts>

#include "logic/replacements.h"
#include "logic/outermost.h"
#include "truthform.h"

// We finally understood after trying to implement resolution since
// 1998 that a clause is not a set of literals.
// It is a mapping from atoms to sets of truth values.
// We represent the truth values by bits, and sets of truth values
// by their bitwise ors.

namespace calc
{

   template< typename S, typename F >
   concept simplifier =
      requires( S simpl, truthform<F> lit )
      {{ S( lit ) } ;
       { simpl. usable( ) } -> std::convertible_to< bool > ;
       { simpl. used( ) } -> std::same_as< uint64_t > ; 
       { simpl. operator( ) ( lit ) } -> 
                std::convertible_to< truthform<F> > ;
      };


   template< typename F > 
   class disjunction_map
   {
      std::vector<truthform<F>> map;

   public:
      disjunction_map( ) noexcept = default;

      bool isempty( ) const { return map. empty( ); }
      size_t size( ) const { return map. size( ); }

      // In general, we have no iterator stability!

      using iterator = std::vector<truthform<F>> :: iterator;
      iterator begin( ) { return map. begin( ); }
      iterator end( ) { return map. end( ); }

      using const_iterator = std::vector<truthform<F>> :: const_iterator;
      const_iterator begin( ) const { return map. cbegin( ); }
      const_iterator end( ) const { return map. cend( ); }

      void insert( truthform<F> && fm ) 
         { map. push_back( std::move(fm) ); }

      void insert( const truthform<F> & fm )
         { map. push_back( fm ); } 

      iterator erase( iterator it ) 
         { return map. erase( it ); }

      iterator erase( iterator it1, iterator it2 )
         { return map. erase( it1, it2 ); }

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

      // True if the clause is very obviously trivial:

      bool istrivial( ) const
      {
         for( const auto& lit : map )
         {
            if( lit. second. istrivial( ))
               return true;
         }
         return false; 
      }

      // 1. Merge equivalent F-s, where equivalence is determined by equiv. 
      // 2. Remove F-s, whose label is empty. 
      // This is a quadratic procedure. 

      template< bool equiv( const F&, const F& ) >  
      void merge_equiv( )
      {
         for( auto from = begin( ); from != end( ); ++ from )    
         { 
            // Look for the first occurrence of the same formula:

            auto into = begin( );
            while( into != from && !equiv( from -> fm, into -> fm ))
               ++ into;
            
            if( into != from )
            {
               ( into -> lab ) |= ( from -> lab );
               ( from -> lab ) = truthset::empty;
            } 
         }
      }

      // Remove literals that cannot be true:

      void remove_nevertrue( )
      {
         auto from = begin( );
         auto into = begin( );
         while( from != end( ))
         {
            if( !from -> lab. isempty( ))
            {
               if( from != into )
                  *into = std::move( *from );
               ++ into;
            }
            ++ from;
         }
         erase( into, end( ));
      }

      void print( std::ostream& out, const_iterator skip ) const
      {
         out << '{';
         bool first = true;  
         for( auto p = begin( ); p != end( ); ++ p ) 
         {
            if( p != skip )
            {
               if( first ) 
                  out << ' ';
               else
                  out << ", ";

               out << *p;

               first = false;
            }
         } 
         out << " }";
      }

   };

   template< typename F, bool equiv( const F&, const F& ) >
   bool 
   subsumes( const truthform<F> & lit,
             const disjunction_map<F> & disj, 
             typename disjunction_map<F> :: const_iterator skip )
   {
      for( auto q = disj. begin( ); q != disj. end( ); ++ q )
      {
         if( q != skip && lit. lab. subsetof( q -> lab ) && 
             equiv( lit. fm, q -> fm ))
         {
            return true;
         }
      }
      return false;
   }


   template< typename F, bool equiv( const F&, const F& ) >
   bool 
   subsumes( const disjunction_map<F> & disj1, 
             typename disjunction_map<F> :: const_iterator skip1,
             const disjunction_map<F> & disj2,
             typename disjunction_map<F> :: const_iterator skip2 )
   {
#if 0
      std::cout << "subsumes\n";
      disj1. print( std::cout, skip1 ); std::cout << "\n";
      disj2. print( std::cout, skip2 );
      std::cout << "?\n";
#endif
      for( auto p1 = disj1. begin( ); p1 != disj1. end( ); ++ p1 )
      {
         if( p1 != skip1 && !subsumes<F,equiv>( *p1, disj2, skip2 ))
            return false;
      } 
      return true;
   }


   template< typename F, bool equiv( const F&, const F& ), simplifier<F> S >
   bool simplify( const disjunction_map<F> & from,
                  disjunction_map<F> & into )
   {
      for( auto p = from. begin( ); p != from. end( ); ++ p )
      {
         auto simpl = S(*p); 
         if( simpl. usable( ))
         {
            for( auto q = into. begin( ); q != into. end( ); ++ q )
            {
               uint64_t uu = simpl. used( );
               auto smp = simpl(*q);

               if( uu != simpl. used( ) && 
                   subsumes<F,equiv>( from, p, into, q ))
               {
                  *q = std::move( smp ); 
                  return true;
               }
            }
         }
      }
      return false; 
   }

   template< typename F >
   std::ostream& operator << ( std::ostream& out, 
                               const disjunction_map<F> & from )
   {
      from. print( std::cout, from. end( ));
      return out;
   }

}

#endif

