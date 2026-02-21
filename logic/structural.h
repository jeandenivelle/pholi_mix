
// Written by Hans de Nivelle, Dec. 2024.
// Everything related to structural type checking.

#ifndef LOGIC_STRUCTURAL_
#define LOGIC_STRUCTURAL_

#include <iostream>
#include <optional>

#include "errorstack.h"
#include "term.h"
#include "beliefstate.h"
#include "context.h"
#include "indexedstack.h"

namespace logic
{

   void checkformula( const beliefstate& blfs, 
                      const identifier& name, term& fm,
                      const char* descr, errorstack& err );
      // blfs is const, but at the same time fm occurs in
      // blfs, which is not const. 
      // descr is used when an error is produced.

   void checkandresolve( beliefstate& everything, errorstack& err );

   void uncheck( type& tp );
      // Make type tp unchecked again.

   void uncheck( term& t );
      // Make term t unchecked again.


   logic::term
   replace_debruijn( indexedstack< std::string, size_t > & db, term t );

   term replace_debruijn( term t );
      // These functions also replace the reserved identifiers
      // FF,EE,TT by their respective formulas.

   // Technically seen, we should return std::optional<T> ,
   // where T is some unit type. 
   // This is because a structural type by itself can have only one kind.
   // This is a bit overdone, so we just use bool.

   bool
   checkandresolve( const beliefstate& blfs, errorstack& errors, type& tp );
    
   std::optional< type > 
   checkandresolve( const beliefstate& blfs, errorstack& errors,
                    context& ctxt, term& t );
      // Check and resolve overloads. 
      // We won't look at dependencies. Dependencies are checked by a separate
      // function. In case of error, we return the empty optional.
      // We don't throw exceptions.

   std::optional<type >
   checkandresolve( const beliefstate& blfs, errorstack& errors, term& t );
   
   std::optional< type >
   try_apply( type ftype, const std::vector< type > & argtypes, size_t pos );
      // Try to apply ftype on argtypes[ pos ... ].

   std::optional< type >
   try_apply( const beliefstate& blfs, exact name, 
              const std::vector< type > & argtypes, size_t pos ); 

}

#endif


