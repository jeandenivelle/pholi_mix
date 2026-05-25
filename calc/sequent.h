
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
#include "label.h"

namespace calc
{
 
   struct sequent
   {

      struct seqform
      {
         std::variant< unf< logic::term >, dnf< logic::term >> fm; 
            // In case we are UNF, there must be at least one
            // quantified variable.

         size_t ctxtsize;      // size of context at moment of creation. 
         bool hidden;          // True if formula is hidden.

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

      label nextlabel = label( "form" );
      indexedstack< label, seqform, label::hash, label::equal_to > stack;

      struct level
      {
         size_t ctxtsize; 
         size_t stacksize; 
            // Sizes of context and stack.

         std::vector< size_t > hidden;
            // Formulas that are hidden by us.
 
         level( size_t ctxtsize, size_t stacksize )
            : ctxtsize( ctxtsize ),
              stacksize( stacksize )
         { }
 
      };

      std::vector< level > levels;

      sequent( ) noexcept = default;
      sequent( sequent&& ) noexcept = default;
      sequent& operator = ( sequent&& ) noexcept = default;

      void ugly( std::ostream& out ) const;  
      void pretty( pretty_printer& out ) const;

      void append( cnf< logic::term > c ); 
         // We append the components separately, and trivial 
         // components are appended as dnf.

      void append( dnf< logic::term > d );
     
      size_t find( const label& lab ) 
         { return stack. find( lab ); }
            // Returns stack. size( ) if not found. 
            // Otherwise a valid index into stack. 
 
      const seqform& formula( size_t ind ) const
         { return stack. at( ind ). second; } 
      seqform& at( size_t ind )
         { return stack. at( ind ). second; } 

      const seqform& back( ) const 
         { return stack. back( ). second; }

      void maketrivial( ssize_t ind );
         // This is different from hiding, because it is permanent.

      size_t stacksize( ) const { return stack. size( ); }

      void appendlevel( ) 
         { levels. push_back( level( ctxt. size( ), stack. size( ))); }

      void poplevel( );  
          // Also unhide everything that was hidden at our level,
          // and restore the stack. We don't restore ctxt,
          // but we require that it was restored in advance.
 
      const level& lastlevel( ) const 
         { return levels. back( ); }

      size_t nrlevels( ) const { return levels. size( ); }

      void hide( size_t );
         // If we have a choice level, we register the hiding,
         // so that it can be undone. 

      size_t liftdist( size_t ) const;
         // The distance over which the formula at it must be lifted
         // in order to put it at the end of the context. 

   };

}

#endif

