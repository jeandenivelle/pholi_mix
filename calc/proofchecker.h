
// Written by Hans de Nivelle, May/June 2026.
// This class will become the trusted core.

#ifndef CALC_PROOFCHECKER_
#define CALC_PROOFCHECKER_

#include <optional>
#include <string_view>

#include "logic/beliefstate.h"
#include "bar.h"
#include "indexedstack.h"
#include "errortree.h"
#include "sequent.h"

namespace calc
{

   struct proofchecker
   {
      const logic::beliefstate* blfs; 
      errorvector errors;

      sequent seq;
      indexedstack< std::string, size_t > db;

      uint64_t nrfakes;

      logic::exact::unordered_map< uint64_t > dependencies;
         // Exact identifiers occurring in the proof. 

      explicit proofchecker( const logic::beliefstate* blfs,
                             const logic::term& goal )
         : blfs( blfs ),
           nrfakes(0)
      { 
         define( "goal", goal, logic::type( logic::type_prop ));
      }

      void setname( size_t ind, const std::string& name );

      size_t cut( logic::term fm );
         // Returns the index of the added formula, or size( ) if 
         // not succesful. 

      // If you want to parse expressions, you must set the
      // names of the eigenvariables:

      size_t branch( size_t disj, size_t choice, 
                     const std::vector< std::string > & eigen = { } );

      size_t expand( size_t ind, const identifier& ident, size_t occ ); 
         // ident must have a definition.

      size_t expand( size_t ind, size_t var, size_t occ );
         // var must be a De Bruijn index. (Looking backwards)

#if 0
      bool import( const identifier& ident, 
                   std::vector< logic::type > argtypes, label name );
         // Imported formula will be called 'name'.
#endif
      size_t flatten( size_t ind );
#if 0
      std::optional< label > normalize( label fm );

      bool def( std::string_view name, logic::term val );
         // Introduce a local definition.

      bool removedef( );
         // Remove the last local definition by substituting it away.

      bool
      instantiate( label lab, const std::vector< logic::term > & values );

      bool simplify( label names );
         // We always simplify everything. The return value
         // is empty if no simplification was possible. 
         // Since we do not know how to resolve names from parents,
         // the caller has to provide names for the results.

      size_t nrdecisions( ) const { return seq. decisions. size( ); }

      std::optional< label > merge( );
         // Merge (resolve) the last choice. Name of the result will
         // be derived from the original disjunction.

      std::optional< label > rename( label was, label becomes );

      std::optional< label > copy( label lab );

      bool fake( logic::term donald, label name );

#endif
      void show( std::string_view label, 
                 std::ostream& out = std::cout ) const;
      logic::term replacedebruijn( logic::term tm );

      // Each of these 3 methods creates an error when
      // it cannot find an index:

      size_t lookup( ssize_t ref );
         // >= 0 starts looking from the beginning.
         // < 0 looks from the end.
         // We ignore hidden formulas. We are not const
         // because we may log an error.

      size_t lookup( const std::string& name );
      size_t move( size_t ind, ssize_t disp );
         // Steps over disp (not hidden) formulas. We are not const
         // because we might log an error. 
 
 
#if 0
      bool isfinished( ) const;
#endif

   private: 
      void assume( const std::string& name, const logic::type& tp );
      void define( const std::string& name, 
                   const logic::term& val, const logic::type& tp );

      std::optional< cnf< logic::term >> 
      try_flatten( const cnf< logic::term > & conj );

      std::optional< dnf< logic::term >> 
      try_flatten( const dnf< logic::term > & disj );

#if 0
      size_t try2find( label lab, std::string_view descr ); 
         // If we don't find, we return seq. stack. size( ) and
         // write that we could not find {descr} into err. 
#endif

      bool check_dnf( size_t ind, std::string_view descr );
      bool check_unf( size_t ind, std::string_view descr );
         // Report error if not. 
   }; 

} 

#endif

