
// Written by Hans de Nivelle, July/August 2025.

#ifndef CALC_PROOFCHECKING_
#define CALC_PROOFCHECKING_

#include <string_view>
#include <optional>

#include "errorstack.h"
#include "sequent.h"
#include "proofterm.h"

namespace calc
{
   void printbar( std::ostream& out );

   errorstack::builder
   errorheader( const sequent& seq, std::string_view rule );

   template< typename T > 
   bool istrivial( const cnf<T> & c )
   {
      return c. size( ) == 1 && c. at(0). vars. size( ) == 0; 
   }

   template< typename T >
   bool istrivial( const dnf<T> & d )
   {
      return d. size( ) == 1 && d. at(0). vars. size( ) == 0; 
   }


   std::optional< logic::type >
   checktype( const logic::beliefstate& blfs,
              logic::term& tm, sequent& seq, errorstack& err );

   bool applicable( const logic::belief& blf, 
                    const std::vector< logic::type > & tps );
      // True if blf (as theorem) is applicable on tps.

   // Replace fm. at( pos ) by becomes:

   template< typename T >
   disjunction<T> replace( const disjunction<T> & fm, 
                           size_t pos, const disjunction<T> & becomes )
   {
      disjunction<T> res; 
      for( size_t i = 0; i != fm. size( ); ++ i )
      {
         if( i != pos )
            res. append( fm. at(i)); 
         else
         {
            for( const auto& d : becomes )
               res. append(d);
         }
      }
      return res;
   }

   template< typename T, bool implies( const T&, const T& ) >
   bool subsumes( const T& t, disjunction<T> & disj )
   {
      for( const auto& d : disj )
      {
         if( implies( t, d ))
            return true;
      }
      return false;
   }

   template< typename T, bool implies( const T&, const T& ) > 
   disjunction<T> remove_subsuming( const disjunction<T> & disj ) 
   {
      disjunction<T> res;
      for( const auto& d : disj )
      {
         if( !implies( d, res ))
            res. append(d);
      }
      return res; 
   }
 
      
   void checkproof( const logic::beliefstate& blfs,
                    proofterm& prf, sequent& seq, errorstack& err );
      // In case of failure, we vent our frustration into err, and 
      // return nothing. As with type checking,
      // we may try to recover from these errors, and check
      // other parts of the proof. 
      // The proofterm is not const, because we resolve overloads.
}

#endif

