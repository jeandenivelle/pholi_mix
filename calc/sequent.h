
// Written by Hans de Nivelle, November 2025.

#ifndef CALC_SEQUENT_
#define CALC_SEQUENT_

#include <map>
#include <vector>
#include <string>

#include "errorstack.h"
#include "indexedstack.h"
#include "logic/beliefstate.h"
#include "logic/context.h"
#include "propositional.h"
#include "quantifiers.h"
#include "pretty.h"

namespace calc
{
 
   struct sequent
   {

      // A sequent consists of segments. A segment is created 
      // either when new variables are assumed, or when new
      // formulas are assumed. 

      struct segment
      {
         std::vector< forall< disjunction< exists< logic::term >>>> stack; 
         std::string name; 
         size_t contextsize;   
            // At the moment when the segment was created.

         segment( const std::string& name, size_t contextsize )
            : name( name ), contextsize( contextsize )
         { }

         void push( forall< disjunction< exists< logic::term >>> form )
            { stack. push_back( std::move( form )); }

         // We use Python style indexing. That means that -1 is the last
         // element, and 0 is the first element: 

         const forall< disjunction< exists< logic::term >>> & 
         at( ssize_t ind ) const; 

         forall< disjunction< exists< logic::term >>> &
            at( ssize_t ind );

         void erase( ssize_t ind );

         using iterator = 
         std::vector< forall< disjunction< exists< logic::term >>>> 
                 :: iterator;

         using const_iterator =
         std::vector< forall< disjunction< exists< logic::term >>>>
                 :: const_iterator;

         iterator begin( ) { return stack. begin( ); }
         iterator end( ) { return stack. end( ); }
            // Be careful with those, because the order is from
            // bottom of stack to top of stack. They are useful
            // for copying or processing.

         void clear( ) { stack. clear( ); }    
            // Forget about everything. Used to think that it was so easy.

         size_t size( ) const { return stack. size( ); } 

         bool inrange( ssize_t ind ) const;
            // True if ind can be used as an index.

         iterator find( ssize_t ind );
         const_iterator find( ssize_t ind ) const; 
      };

       
      logic::context ctxt;
      indexedstack< std::string, size_t > db;
         // db is needed because we typecheck terms during 
         // proofchecking. 'db' stands for De Bruijn. 
         // size_t looks from the beginning!

      std::map< size_t, logic::term > defs;
         // If a position in ctxt is a definition, its value is here.

      std::vector< segment > seg;
         // Stack of stacks of derived formulas. 

      sequent( ) noexcept { } 
      sequent( sequent&& ) noexcept = default;
      sequent& operator = ( sequent&& ) noexcept = default;

      size_t size( ) const { return seg. size( ); }

      void ugly( std::ostream& out ) const;  
      void pretty( pretty_printer& out ) const;

      // The number returned can be used for restoring the context:

      size_t assume( const std::string& name, const logic::type& tp );

      size_t define( const std::string& name, const logic::term& val,
                     const logic::type& tp );

      void restore( size_t ss );

      void push_back( const std::string& name );
      void pop_back( );
         // Add or remove a segment.

      const segment& back( ) const;
      segment& back( );

      const segment& at( size_t ind ) const { return seg. at( ind ); }
      segment& at( size_t ind ) { return seg. at( ind ); }
   };

}

#endif

