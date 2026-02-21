
// A filehasher keeps track of files that have been read,
// so that we can avoid including the same file more than once. 
// Before a file is read, call contains with the path. 
// If the name is not there, we read the hash value, and check if
// there is a file with the hash value.
// If not, we return false.
// If 

#include <set> 
#include <map>
#include <filesystem>

#include "errorstack.h"
#include "logic/beliefstate.h"

struct filehasher
{
   std::set< std::filesystem::path > known_names;
   std::multimap< std::uintmax_t, 
      std::multimap< std::uintmax_t, std::filesystem::path >> known_files;
      // Maps file size, file hash to paths.

   static std::uintmax_t hash( const std::filesystem::path& file );

   static short int compare( const std::filesystem::path& file1, 
                             const std::filesystem::path& file2 );

   filehasher( ) noexcept = default;

   bool insert( std::filesystem::path file );
      // Returns true if the file was inserted, in that case it 
      // was unknown, and you should read it. We cannot 
      // handle non-existing files. 

   void print( std::ostream& out ) const; 
};


