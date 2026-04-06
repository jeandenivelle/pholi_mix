
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
         unf< logic::term > & get_unf( )
            { return get< unf< logic::term >> ( fm ); }

         const dnf< logic::term > & get_dnf( ) const 
            { return get< dnf< logic::term >> ( fm ); }
         dnf< logic::term > & get_dnf( ) 
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

      void restore( size_t cc );
         // Restore context to size cc.
         // If there are definitions, we remove those as well.

      void append( cnf< logic::term > c ); 
         // We append the components separately, and trivial 
         // components are appended as dnf.

      void append( dnf< logic::term > d );
     
      bool hasindex( ssize_t ind ) const; 
      const seqform& at( ssize_t ind ) const; 
      seqform& at( ssize_t ind );
         // We use Python style circular indexing.

      size_t nrlevels( ) const { return levels. size( ); }

      void appendlevel( ) 
         { levels. push_back( level( ctxt. size( ), stack. size( ))); }

      void poplevel( );  
          // Also unhide everything that was hidden at our level,
          // and restore the stack. We don't restore ctxt,
          // but we require that it was restored in advance.
 
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

