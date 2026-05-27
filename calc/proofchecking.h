
// Written by Hans de Nivelle, July/August 2025.

#ifndef CALC_PROOFCHECKING_
#define CALC_PROOFCHECKING_

#include <optional>

#include "errorstack.h"
#include "sequent.h"
#include "proofterm.h"

namespace calc
{

   struct bar
   {
      size_t len;
      bar( size_t len = 70 )
         : len( len )
      { }
   };

   std::ostream& operator << ( std::ostream& out, bar b );


   std::optional< logic::type >
   checktype( const logic::beliefstate& blfs,
              logic::term& tm, sequent& seq, errorstack& err );

   bool applicable( const logic::belief& blf, 
                    const std::vector< logic::type > & tps );
      // True if blf (as theorem) is applicable on tps.


   // A few nice subsumption functions.
   // I think that all templates must be moved somewhere else. 

   bool subsumes( const logic::term& tm1, const logic::term& tm2 );
      // For the moment just equality.

   template< typename F > 
   bool subsumes( const exists<F> & ex1, const exists<F> & ex2 )
   {
      if( ex1. vars. size( ) != ex2. vars. size( ))
         return false;

      for( size_t i = 0; i != ex1. vars. size( ); ++ i )
      {
         if( !equal( ex1. vars. at(i). tp, ex2. vars. at(i). tp ))
            return false; 
      }

      return subsumes( ex1. body, ex2. body );
   }

   template< typename F >
   bool subsumes( const forall<F> & forall1, const forall<F> & forall2 )
   {
      if( forall1. vars. size( ) != forall2. vars. size( ))
         return false;

      for( size_t i = 0; i != forall1. vars. size( ); ++ i )
      {
         if( !equal( forall1. vars. at(i). tp, forall2. vars. at(i). tp ))
            return false;
      }

      return subsumes( forall1. body, forall2. body );
   }


   template< typename F > 
   bool subsumes( const F& lit, const disjunction<F> & disj )
   {
      for( const auto& d : disj )
      {
         if( subsumes( lit, d ))
            return true;
      }
      return false;
   }

   template< typename F >
   bool subsumes( const conjunction<F> & conj, const F& lit )
   {
      for( const auto& c : conj )
      {
         if( subsumes( c, lit ))
            return true;
      }
      return false;
   }

   template< typename F >
   bool
   subsumes( const conjunction<F> & conj1, const conjunction<F> & conj2 )
   {
      for( const auto& lit : conj2 )
      {
         if( !subsumes( conj1, lit ))
            return false;
      }
      return true;
   }


   template< typename F >
   bool 
   subsumes( const disjunction<F> & disj1, const disjunction<F> & disj2 )
   {
      for( const auto& lit : disj1 )
      {
         if( !subsumes( lit, disj2 ))
            return false;
      }
      return true;
   }

   void checkproof( const logic::beliefstate& blfs, sequent& seq, 
                    proofterm& prf, errorstack& err, 
                    logic::exact::unordered_set& dependencies );
      // In case of failure, we vent our frustration into err.
      // As with type checkin,
      // we may try to recover from these errors, and check
      // other parts of the proof. 
      // The proofterm is not const, because we resolve overloads.
}

#endif

