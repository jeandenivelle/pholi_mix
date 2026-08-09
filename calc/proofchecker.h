
// Written by Hans de Nivelle, May/June 2026.
// This class will become the trusted core.

#ifndef CALC_PROOFCHECKER_
#define CALC_PROOFCHECKER_

#include <optional>
#include <string_view>

#include "logic/beliefstate.h"
#include "bar.h"
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


      bool cut( logic::term fm, const label& lab );

      // If you want to parse expressions, you must set the
      // names of the eigenvariables:

      bool 
      branch( label disj, size_t choice, 
              const std::vector< std::string > & eigen = { } );

      bool expand( label fm, const identifier& ident, size_t occ ); 

      bool expand( label fm, size_t var, size_t occ );
         // var must be a De Bruijn index. (Looking backwards)

      bool import( const identifier& ident, 
                   std::vector< logic::type > argtypes, label name );
         // Imported formula will be called 'name'.

      std::optional< label > flatten( label fm );
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

      label labelof( ssize_t cnt ) const;
         // >= 0 looks from the beginning,
         // < 0 looks from the end. Hidden formulas are ignored.

      void hide( label lab );

      void show( std::string_view label, 
                 std::ostream& out = std::cout ) const;

      logic::term replacedebruijn( logic::term tm );

      bool isfinal( ) const;

   private: 
      void assume( const std::string& name, const logic::type& tp );

      void define( const std::string& name, 
                   const logic::term& val, const logic::type& tp );

      std::optional< cnf< logic::term >> 
      try_flatten( const cnf< logic::term > & conj );

      std::optional< dnf< logic::term >> 
      try_flatten( const dnf< logic::term > & disj );

      size_t try2find( label lab, std::string_view descr ); 
         // If we don't find, we return seq. stack. size( ) and
         // write that we could not find {descr} into err. 

      bool is_dnf( const label& lab, size_t ind, std::string_view descr );
      bool is_unf( const label& lab, size_t ind, std::string_view descr );
   }; 

} 

#endif

