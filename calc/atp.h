
// Written by Hans de Nivelle, December 2025.

#ifndef CALC_ATP_
#define CALC_ATP_

#include <iostream>

#include "logic/term.h"
#include "propositional.h"
#include "quantifiers.h"
#include "prefix.h"

namespace calc
{

   namespace atp
   {
      using literal = exists< logic::term > ;
      using clause = disjunction< literal > ;
     
 
      std::pair< prefix, const logic::term* > 
      decompose( const logic::term& tm );
         // Assumes ANF.

      bool inconflict( const logic::term& tm1, const logic::term& tm2 );
         // If yes, then it cannot occur that [tm1] = [tm2] = T.

      bool subsumes( const logic::term& tm1, const logic::term& tm2 );

      bool subsumes( const exists< logic::term > & ex1,
                     const exists< logic::term > & ex2 );
         // Very incomplete! If yes, then [ex1] = T implies
         // [ex2] = T.  
   
      bool trivially_true( const logic::term& tm );
         // Catches a few trivial cases:
         //    TRUE, ( t = t ), # t1 = t2, # # t, and # FALSE, # TRUE.

      bool istruthconstant( const clause& cls );
         // True if cls equals { T }.

      void maketruthconstant( clause& cls );
         // Make cls equal to { T }.

      void simplify( clause& cls );
         // Remove redundant literals, and direct equalities using
         // KBO.
 
      bool subsumes( const literal& lit, const clause& cls,
                     clause::const_iterator skip );

      bool subsumes( const clause& cls1, clause::const_iterator skip1,
                     const clause& cls2, clause::const_iterator skip2 );

         // True if cls1 \ skip1 is a subset of cls2 \ skip2.
         // If you want the full clause, use end( ).

      // True if it happened:
 
      bool rewrite( const clause& from, clause& into );
      bool resolve( const clause& from, clause& into );

      void simplify( conjunction< clause > & simp );
         // This is the main function that should be called. 

   }

}

#endif

