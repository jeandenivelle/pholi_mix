
// Written by Hans de Nivelle, May 2026.

#ifndef CALC_SUBSUMPTION_
#define CALC_SUBSUMPTION_

#include "logic/cmp.h"

namespace calc
{

   // For the moment just equality:

   inline bool subsumes( const logic::term& tm1, const logic::term& tm2 )
      { return equal( tm1, tm2 ); }


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

}

#endif

