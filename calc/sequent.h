
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

         size_t ctxtsize;      // sizs of context at moment of creation. 
         bool hidden;          // True if formula is hidden.
         std::string comment;  

         seqform( unf< logic::term > u, size_t ctxtsize )
            : fm( std::move(u)),
              ctxtsize( ctxtsize ),
              hidden( false )
         { }

         seqform( dnf< logic::term > d, size_t ctxtsize ) 
            : fm( std::move(d)), 
              ctxtsize( ctxtsize ),
              hidden( false )
         { }
 
         bool is_unf( ) const 
            { return holds_alternative< unf< logic::term >> ( fm ); } 
         bool is_dnf( ) const 
            { return holds_alternative< dnf< logic::term >> ( fm ); }

         const unf< logic::term > & get_unf( ) const 
            { return get< unf< logic::term >> ( fm ); }
         const dnf< logic::term > & get_dnf( ) const 
            { return get< dnf< logic::term >> ( fm ); }

         void print( std::ostream& out ) const; 
         void print( pretty_printer& out ) const; 
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

         std::vector< size_t > hidden;
            // Indices of formulas that are hidden by us.
 
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

         void clear( ) { stack. clear( ); }    
            // Forget about everything. Used to think that it was so easy.

         size_t size( ) const { return stack. size( ); } 
#endif

         bool inrange( ssize_t ind ) const;
            // True if ind can be used as an index.

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

      void append( cnf< logic::term > c ); 
         // We append the components separately, and trivial ones
         // are appended as dnf.
      void append( dnf< logic::term > d );
     
      bool hasindex( ssize_t ind ) const; 
      const seqform& at( ssize_t ind ) const; 
      seqform& at( ssize_t ind );
         // We use Python style circular indexing.

      size_t nrlevels( ) const { return levels. size( ); }
      void appendlevel( ) 
         { levels. push_back( level( ctxt. size( ), stack. size( ))); }
      void poplevel( ) 
         { levels. pop_back( ); }
      const level& lastlevel( ) const 
         { return levels. back( ); }

      void hide( ssize_t ind );
         // If we have a choice level, we register the hiding,
         // so that it can be undone. 

      size_t liftdist( ssize_t ind ) const;
         // The distance over which the formula at ind must be lifted
         // in order to put it at the end of the context. 

      size_t nrformulas( ) const { return stack. size( ); }

   };

}

#endif

