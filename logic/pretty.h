
// Everything related to pretty printing. 
// Written by Alikhan Balpykov and Hans de Nivelle.
// May 2023.

#ifndef LOGIC_PRETTY_
#define LOGIC_PRETTY_

#include <iostream>
#include "term.h"
#include "context.h"
#include "beliefstate.h"

#include "uniquenamestack.h"

#include <functional>

namespace logic { 
namespace pretty 
{

   struct attractions
   {
      unsigned int left;
      unsigned int right;
         // Higher number means : more attraction. Zero means:
         // No. attraction. at. all. Not. even. the. slighest.

      attractions( ) = delete;

      attractions( unsigned int left, unsigned int right )
         : left( left ), right( right )
      { }

      void print( std::ostream& out ) const
         { out << left << '/' << right; } 

   };

   attractions getattractions( selector sel );

   inline 
   std::ostream& operator << ( std::ostream& out, 
                               std::pair< unsigned int, unsigned int > env )
   { 
      out << env. first << '/' << env. second; 
      return out; 
   }

   std::pair< unsigned int, unsigned int > 
   inline 
   between( std::pair< unsigned int, unsigned int > env, attractions attr )
      { return { env. first, attr. left }; }
      
   std::pair< unsigned int, unsigned int >
   inline between( attractions attr1, attractions attr2 )
      { return { attr1. right, attr2. left }; }

   std::pair< unsigned int, unsigned int >
   inline
   between( attractions attr, std::pair< unsigned int, unsigned int > env )
      { return { attr. right, env. second }; }


   struct parentheses
   {
      bool needed = false;
    
      parentheses( ) noexcept { }

      operator bool( ) const { return needed; }

      // Checks if env pulls harder than attr, either to the left
      // or to the right. If yes, we make needed = true.

      // env. first is surrounding attraction from the left.
      // env. second is surrounding attraction from the right.

      void check( attractions attr,
                  std::pair< unsigned, unsigned int > env );

      void opening( std::ostream& out ) const;
      void closing( std::ostream& out ) const;
         // print opening/closing parentheses. 
         // Don't change our state. 
   };


   void print( std::ostream& out, const beliefstate& blfs,
               uniquenamestack& names, 
               const std::function< vartype( size_t ) > & vt, size_t sz ); 
      // Prints a sequence of vartypes nicely, combining
      // types wherever possible. This can used when printing
      // a quantifier, a lambda, or a definition.

   // env. first is the left attraction of the operator to the right of us.
   // env. second is the right attraction of the operator to the left of us.

   void print( std::ostream& out, const beliefstate& blfs, 
               const type& tp, std::pair< unsigned int, unsigned int > env );
 
   void print( std::ostream& out, const beliefstate& blfs,
               uniquenamestack& names,
               const term& t, std::pair< unsigned int, unsigned int > env );

      // env specifies how hard our environment wants to rip us apart.
      // If it is too much for us, we shield ourselves with parentheses.
      // Unchecked names are printed with quotes.
      // Exact names will be prefixed with :: if they conflict with a local
      // variable.

   // This the main function that you should call: 

   void print( std::ostream& out, const beliefstate& blfs,
               context& ctxt, const term& t );

   uniquenamestack getnames( const logic::context& ctxt, size_t ss );

   void print( std::ostream& out, 
               uniquenamestack& names, const logic::belief& );

   uniquenamestack 
   print( std::ostream& out, const beliefstate& blfs, const context& cxt ); 
      // Print a context. Since a term is often printed
      // together with its context, we remember the uniquenamestack,
      // so that it can be used for printing the term. 

   void print( std::ostream& out, const beliefstate& blfs, const belief& bel ); 

}}

#endif

