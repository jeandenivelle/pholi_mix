
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

         size_t ctxtsize;      // size of ctxt at moment of creation. 
         bool hidden;          // True if the formula is hidden.

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
      indexedstack< label, seqform, label::hash, label::equal_to > stack;

      struct decision
      {
         size_t ctxtsize; 
         size_t stacksize; 
            // Sizes of context and stack just before our creation. 

         size_t parent;    // Must be DNF.
         size_t choice;    

         std::vector< size_t > hidden;
            // Formulas that are hidden by us.
 
         decision( size_t ctxtsize, size_t stacksize,
                   size_t parent, size_t choice )
            : ctxtsize( ctxtsize ),
              stacksize( stacksize ),
              parent( parent ),
              choice( choice ) 
         { }

         void print( std::ostream& out ) const
         { 
            out << ctxtsize << ',' << stacksize << " / ";
            out << parent << '[' << choice << ']';
         }

      };

      std::vector< decision > decisions;

      sequent( ) noexcept = default;
      sequent( sequent&& ) noexcept = default;
      sequent& operator = ( sequent&& ) noexcept = default;

      void print( std::ostream& out ) const;
      void print( pretty_printer& prt ) const;

      label append( label lab, unf< logic::term > u ); 
         // If the quantifier is empty, we append as dnf.
 
      label append( label lab, dnf< logic::term > d );
         // Both methods look for the first free label >= lab.
         // and return the label where the formula was added.
 
      size_t size( ) const 
         { return stack. size( ); }
 
      size_t find( const label& lab ) const; 
            // Returns size( ) lab does not exist, or is hidden. 

      const seqform& at( size_t ind ) const
         { return stack. at( ind ). second; } 

      void pushdecision( size_t parent, size_t choice ) 
         { decisions. push_back( decision( ctxt. size( ), stack. size( ), 
                                 parent , choice )); }

      void popdecision( );  
         // Also restores the context, the stack, and undoes hidings.

      size_t nrdecisions( ) const { return decisions. size( ); }

      void hide( size_t ind );
         // If we have a decision, we register the hiding,
         // so that it can be undone when we undo the decision.

      size_t liftdist( size_t ) const;
         // The distance over which the formula at it must be lifted
         // in order to put it at the end of the context. 

   };

   inline pretty_printer& operator << ( pretty_printer& prnt,
                                        const sequent::seqform& fm )
   {
      fm. print( prnt ); 
      return prnt;
   }

}

#endif

