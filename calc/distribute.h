
#ifndef CALC_DISTRIBUTE_
#define CALC_DISTRIBUTE_

#include <vector>
#include <list>

#include "logic/context.h"
#include "logic/term.h"

namespace calc
{

   struct disj_stack
   {
      struct markedform
      {
         logic::term form;
         size_t level; 
         bool active;

         markedform( const logic::term& form, size_t level, bool active )
            : form( form ), level( level ), active( active )
         { }

         void print( std::ostream& out ) const;  
      };

      std::list< markedform > lst; 
         // True means available, false means blocked.

      disj_stack( ) noexcept = default;

      void append( const logic::term& f, size_t level ) 
         { lst. push_back( markedform( f, level, true )); }

      using iterator = std::list< markedform > :: iterator;
      using const_iterator = std::list< markedform > :: const_iterator;

      const_iterator begin( ) const { return lst. begin( ); }
      const_iterator end( ) const { return lst. end( ); }

      iterator begin( ) { return lst. begin( ); }
      iterator end( ) { return lst. end( ); }

      size_t size( ) const { return lst. size( ); }
      void restore( size_t dd );

      iterator 
      findbest( bool pref( const logic::term& , const logic::term& ));
         // cmp must be a function that returns true if first
         // is more preferred than second.

      void print( std::ostream& out ) const; 
   };

   // The disjunction is input. We use a vector(stack) of 
   // formulas and bool. If the bool is false, the 
   // formula is considered removed.
     
   void distr( logic::context& ctxt, disj_stack& disj, 
               std::vector< logic::term > & conj );

}

#endif 


