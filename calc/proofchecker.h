
// Written by Hans de Nivelle, May/June 2026.
// This will become the trusted core.

#ifndef CALC_PROOFCHECKER_
#define CALC_PROOFCHECKER_

#include <optional>
#include <string_view>

#include "logic/beliefstate.h"
#include "errorstack.h"
#include "sequent.h"

namespace calc
{

   struct bar
   {
      size_t len;
      bar( size_t len = 70 )
         : len( len )
      { }
   };

   std::ostream& operator << ( std::ostream& out, bar b );


   struct proofchecker
   {
      const logic::beliefstate& blfs; 
      errorstack& err;

      sequent seq;
      indexedstack< std::string, size_t > db;
      uint64_t nrfakes;  

      explicit proofchecker( const logic::beliefstate& blfs,
                             errorstack& err )
         : blfs( blfs ), err( err ),
           nrfakes(0) 
      { }

      void setgoal( logic::exact fname ); 

      // The functions that follow return a label if they succeed.

      std::optional< label > cut( const label& lab, logic::term fm );

      // If you want to parse expressions, you must set the
      // names of the eigenvariables.

      std::optional< label >  
      branch( label disj, size_t choice, 
              const std::vector< std::string > & eigen = { } );

      std::optional< label > 
      expand( label fm, const identifier& ident, size_t occ ); 

      std::optional< label > 
      expand( label fm, size_t var, size_t occ );
         // var must be a De Bruijn index. 

      std::optional< label >
      import( const identifier& ident, 
              std::vector< logic::type > argtypes, label name );
         // Imported formula will be called 'name'.

      std::optional< label > flatten( label fm );
      std::optional< label > normalize( label fm );

      bool deflocal( std::string_view name, logic::term val );

      std::optional< label > 
      instantiate( label lab, const std::vector< logic::term > & values );

      std::optional< label > simplify( label names );
         // We always simplify everything. The return value
         // is empty if no simplification was possible. 
         // Since we do not know how to resolve names from parents,
         // the caller has to provide names for the results.

      size_t nrdecisions( ) const { return seq. decisions. size( ); }

      std::optional< label > resolve( );
         // Resolve the last choice. Name of the result will
         // be derived from the original disjunction.

      std::optional< label > rename( label was, label becomes );

      std::optional< label > 
      fake( logic::term trmp, label name );

      label labelof( ssize_t cnt ) const;
         // >= 0 looks from the beginning,
         // < 0 looks from the end. Hidden formulas are ignored.

      void hide( label lab );

      void show( std::string_view label, 
                 std::ostream& out = std::cout ) const;

      logic::term replacedebruijn( logic::term tm );

   private: 
       
      std::optional< logic::type > gettype( logic::term& tm );

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

