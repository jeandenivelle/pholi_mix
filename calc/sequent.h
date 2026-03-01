
// Written by Hans de Nivelle, November 2025.
// Rewritten Feb 2026.

#ifndef CALC_SEQUENT_
#define CALC_SEQUENT_

#include <map>
#include <vector>
#include <variant>

#include "errorstack.h"
#include "indexedstack.h"
#include "logic/beliefstate.h"
#include "logic/context.h"
#include "normalforms.h"
#include "pretty.h"

namespace calc
{
 
   struct sequent
   {

      struct seqform
      {
         std::variant< unf< logic::term >, dnf< logic::term >> fm; 
            // In case we are UNF, there must be at least one
            // quantified variable.

         size_t ctxtsize;  // context size at moment of creation. 
         bool blocked;     // True if formula is blocked/subsumed.
         std::string comment;  

         seqform( dnf< logic::term > d, size_t ctxtsize ) 
            : fm( std::move(d)), 
              ctxtsize( ctxtsize ),
              blocked( false )
         { }
 
         bool is_unf( ) const 
            { return holds_alternative< unf< logic::term >> ( fm ); } 
         bool is_dnf( ) const 
            { return holds_alternative< dnf< logic::term >> ( fm ); }

         const unf< logic::term > & get_unf( ) const 
            { return get< unf< logic::term >> ( fm ); }
         const dnf< logic::term > & get_dnf( ) const 
            { return get< dnf< logic::term >> ( fm ); }

         void ugly( std::ostream& out ) const; 
      };
 
      logic::context ctxt;
      indexedstack< std::string, size_t > db;
         // db is needed because we typecheck terms during 
         // proofchecking. 'db' stands for De Bruijn. 
         // We look from the beginning!

      std::vector< seqform > stack;

      std::map< size_t, logic::term > defs;
         // If a position in ctxt is a definition, its value is here.
         // We look from the beginning of course. 

      struct level
      {
         size_t ctxtsize; 
         size_t stacksize; 
            // Sizes of context and stack.

         std::vector< size_t > blocking;
            // Indices of formulas that are blocked at this level.
 
         level( size_t ctxtsize, size_t stacksize )
            : ctxtsize( ctxtsize ),
              stacksize( stacksize )
         { }
 
#if 0 
         void push( forall< disjunction< exists< logic::term >>> form )
            { stack. push_back( std::move( form )); }

         // We use Python style indexing. That means that -1 is the last
         // element, and 0 is the first element: 

         forall< disjunction< exists< logic::term >>> &
            at( ssize_t ind );

         void erase( ssize_t ind );

         using iterator = 
         std::vector< forall< disjunction< exists< logic::term >>>> 
                 :: iterator;

         using const_iterator =
         std::vector< forall< disjunction< exists< logic::term >>>>
                 :: const_iterator;

         void clear( ) { stack. clear( ); }    
            // Forget about everything. Used to think that it was so easy.

         size_t size( ) const { return stack. size( ); } 
#endif

         bool inrange( ssize_t ind ) const;
            // True if ind can be used as an index.

         // iterator find( ssize_t ind );
         // const_iterator find( ssize_t ind ) const; 
      };

      std::vector< level > levels;

      sequent( ) noexcept = default;
      sequent( sequent&& ) noexcept = default;
      sequent& operator = ( sequent&& ) noexcept = default;

      void ugly( std::ostream& out ) const;  
      void pretty( pretty_printer& out ) const;

      size_t assume( const std::string& name, const logic::type& tp );

      size_t define( const std::string& name, const logic::term& val,
                     const logic::type& tp );

      void restore( size_t ss );

      void append( unf< logic::term > u ); 
      void append( dnf< logic::term > d );
     
      bool hasindex( ssize_t ind ) const; 
      const seqform& at( ssize_t ind ) const; 
      seqform& at( ssize_t ind );
         // We use Python style circular indexing.

      size_t nrlevels( ) const { return levels. size( ); }
      void appendlevel( ) 
         { levels. push_back( level( ctxt. size( ), stack. size( ))); }

      void block( ssize_t ind );
         // If we have a choice level, we register the blocking,
         // so that it can be restored.

      size_t liftdist( ssize_t ind ) const;
         // The distance over which the formula at ind must be lifted
         // so that it can be put at the end of the context. 

#if 0
      const segment& back( ) const;
      segment& back( );

      const segment& at( size_t ind ) const { return seg. at( ind ); }
      segment& at( size_t ind ) { return seg. at( ind ); }
#endif

   };

}

#endif

