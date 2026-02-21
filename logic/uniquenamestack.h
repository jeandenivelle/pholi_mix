
// Written by Hans de Nivelle, probably Spring 2023.

#ifndef LOGIC_PRETTY_UNIQUENAMESTACK_
#define LOGIC_PRETTY_UNIQUENAMESTACK_

#include <iostream>
#include <vector>
#include <string>
#include <unordered_map>

namespace logic {
namespace pretty   
{

   struct uniquename
   {
      std::string base;
      size_t index;

      uniquename( ) = delete;
      uniquename( const std::string& base, size_t index )
         : base( base ), index( index )
      { }

      uniquename( std::string&& base, size_t index )
         : base( std::move( base )), index( index )
      { }

      void print( std::ostream& out ) const
      {
         if( index )
            out << base << index;
         else
            out << base;
      }
   };

   class uniquenamestack
   {
      std::vector< uniquename > names; 
      std::unordered_map< std::string, std::vector< size_t >> indices;
         // indices[ base ] is a vector of indices that have been used
         // for base.
       
   public:
      uniquenamestack( ) noexcept = default;
      uniquenamestack( uniquenamestack&& ) noexcept = default;
      uniquenamestack& operator = ( uniquenamestack&& ) noexcept = default; 

      size_t size( ) const { return names. size( ); } 

      void restore( size_t s );

      // Correctly looks up a De Bruijn index:

      const uniquename& getname( size_t index ) const
         { return names[ names. size( ) - index - 1 ]; }

      const uniquename& extend( std::string name );

      bool issafe( std::string s ) const;
         // True if the base of s is not in the indices.
         // This may sometimes return false for a name that
         // is safe in principle, but better safe than sorry.

      void print( std::ostream& out ) const;
   };

}}


#endif


