
// Written by Hans de Nivelle, probably Spring 2023.
// I made some changes changes on 2026.08.06.
// Proposed names are always extended, we never use a part of
// a proposed name as counter.  
// If the proposed name ends in a digit, we append letters.
// Otherwise, we append digits.


#ifndef LOGIC_PRETTY_UNIQUENAMESTACK_
#define LOGIC_PRETTY_UNIQUENAMESTACK_

#include <iostream>
#include <vector>
#include <string>
#include <unordered_set>
#include <unordered_map>

namespace logic {
namespace pretty   
{

   class uniquenamestack
   {
      std::vector< std::pair< std::string, std::string >> names; 
         // Each first string is the name with which extend was called.
         // Each second string is the unique string that was added. 

      std::unordered_set< std::string > used; 
         // Set of all second strings. 

      std::unordered_map< std::string, std::vector< size_t >> renamings; 
         // For each string, the indices in names, of which it is the
         // first string of the pair.
 
   public:
      uniquenamestack( ) noexcept = default;
      uniquenamestack( uniquenamestack&& ) noexcept = default;
      uniquenamestack& operator = ( uniquenamestack&& ) noexcept = default; 

      size_t size( ) const { return names. size( ); } 

      void restore( size_t s );

      // Correctly looks up a De Bruijn index:

      const std::string& getname( size_t index ) const
         { return names. at( names. size( ) - index - 1 ). second; }

      const std::string& extend( std::string name );

      bool contains( std::string s ) const { return used. contains(s); } 
      
      void print( std::ostream& out ) const;
   };

}}


#endif


