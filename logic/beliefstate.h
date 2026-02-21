
// Written by Hans de Nivelle September 2024.
// Made a lot of changes in December 2024.
// The main data structure now is a vector of beliefs.
// An exact name is an index into this vector.
// Added a backtrack method on July 21/22 2025.

#ifndef LOGIC_BELIEFSTATE_
#define LOGIC_BELIEFSTATE_  

#include <vector>
#include <unordered_map>

#include "identifier.h"
#include "exact.h"
#include "belief.h"
#include "util/print.h"

namespace logic 
{

   class beliefstate
   {
      std::vector< belief > vect; 

      using identifier2exact = 
         std::unordered_map< identifier, std::vector< exact >, 
                             identifier::hash, identifier::equal_to > ;

      identifier2exact functions;

      identifier2exact structdefs;
         // In PHOLI, an identifier can be declared as type only once, 
         // so there is no need to use a set here. Our approach
         // is that this is a problem of the type checker, not ours.
         // We are only a dumb data structure, our job is to store.
         // If we are asked to store something, we just store it without 
         // asking any questions.

      identifier2exact formulas;

      const std::vector< exact > empty;
         // This is an empty vector, so that we can return
         // a reference when somebody tries to look up an identifier
         // that has no overloads. Since we always return it 
         // as a const-reference, it is harmless that it will
         // be shared.

      static void remove_candidates( identifier2exact& overloads,
                                     const identifier& id, exact ex );

   public:  
      beliefstate( ) noexcept = default; 
      beliefstate( beliefstate&& ) noexcept = default;
      beliefstate& operator = ( beliefstate&& ) noexcept = default;

      exact append( belief&& bel );
         // If one adds a name with a pattern that overlaps with an 
         // existing
         // pattern, it will be added without complaints. It will only 
         // be detected during type checking, when the overlapping 
         // pattern is used, and causes an ambiguous overload.

      const std::vector< exact > & 
      getstructdefs( const identifier& id ) const;

      const std::vector< exact > & 
      getfunctions( const identifier& id ) const;

      const std::vector< exact > & 
      getformulas( const identifier& id ) const;

      belief& at( exact id )
         { return vect. at( id. nr ); }

      const belief& at( exact id ) const
         { return vect. at( id. nr ); } 

      bool contains( exact ex ) const
         { return ex. nr < vect. size( ); } 

      bool contains( const identifier& id ) const
      {
         return !getfunctions( id ). empty( ) || 
                !getstructdefs( id ). empty( ) ||
                !getformulas( id ). empty( );
      }

      using iterator = std::vector< belief > :: iterator;
      using const_iterator = std::vector< belief > :: const_iterator;

      iterator begin( ) { return vect. begin( ); }
      iterator end( ) { return vect. end( ); }

      const_iterator begin( ) const { return vect. begin( ); }
      const_iterator end( ) const { return vect. end( ); }

      void print( std::ostream& out ) const;
   };

}

#endif


