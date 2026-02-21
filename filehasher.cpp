
#include "filehasher.h"
#include <fstream>

std::uintmax_t 
filehasher::hash( const std::filesystem::path& file )
{
   std::uintmax_t hv = 0;

   auto in = std::ifstream( file );
   if( !in )
      return 0;

   auto c = in. get( );
   while( in )
   {
      hv ^= hv << 13;
      hv ^= hv >> 7;
      hv ^= hv << 17;
      hv ^= c;

      c = in. get( );
   }

   return hv; 
}


short int
filehasher::compare( const std::filesystem::path& file1,
                     const std::filesystem::path& file2 )
{
   auto in1 = std::ifstream( file1 );
   auto in2 = std::ifstream( file2 ); 

   if( !in1 || !in2 ) 
   {
      if( in1 ) return 1;
      if( in2 ) return -1;
      return 0;
   }

   auto c1 = in1. get( );
   auto c2 = in2. get( );

   while( in1 && in2 )
   {
      if( c1 < c2 ) return -1;
      if( c1 > c2 ) return 1;

      c1 = in1. get( );
      c2 = in2. get( );
   }

   if( in1 ) return 1;
   if( in2 ) return -1;
   return 0;       
}

bool filehasher::insert( std::filesystem::path file )
{
   file = canonical( file );

   // std::cout << "inserting " << file << "\n";

   if( !known_names. insert( file ). second )
      return false;

   uintmax_t s = 0;
   if( exists( file ))
      s = file_size( file );

   uintmax_t h = 0;
   if( exists( file ))
      h = hash( file );

   // std::cout << "size = " << s << "\n";
   // std::cout << "hash = " << h << "\n";

   auto same_size = known_files. equal_range(s);
   for( auto p = same_size. first; p != same_size. second; ++ p )
   {
      auto same_hash = p -> second. equal_range(h);       
      for( auto q = same_hash. first; q != same_hash. second; ++ q )
      {
         auto c = compare( file, q -> second );
         if( c == 0 )
            return false;   // File with same contents occurs. 
      }

      p -> second. insert( std::pair( h, file ));
      return true; 
   }

   // Being here means that we have no file with the same length:

   auto p = known_files. insert( 
      std::pair( s, 
                 std::multimap< std::uintmax_t, std::filesystem::path > ( ))
   );

   p -> second. insert( std::pair( h, file ));
   return true;
}


void filehasher::print( std::ostream& out ) const
{
   out << "filehasher:\n";
   for( const auto& f : known_names )
      out << "   " << f << "\n";

   out << "\n";
   for( const auto& p : known_files )
   {
      out << "size " << p. first << ":\n";
      for( const auto& q : p. second ) 
         out << "   hash " << q. first << ": " << q. second << "\n";
   }
   out << "\n";
}

