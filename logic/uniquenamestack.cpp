
#include "uniquenamestack.h"
#include "util/print.h"

namespace
{

   // last is inclusive. It must be the case that first != last.

   void increase( std::string& str, const char first, const char last )
   {
      size_t i = str. size( );
      while( i && str[ i - 1 ] == last )
      {
         -- i;
         str[i] = first; 
      }
      std::cout << i << "\n";
      if( i == 0 || str[ i - 1 ] < first || str[ i - 1 ] > last )
         str. insert( i, 1, first + 1 );
      else
         ++ str[ i - 1 ];
   }

}

const std::string&
logic::pretty::uniquenamestack::extend( std::string name )
{
   // We insert the name in used. It's either there or not.
   // It it was not there, it will have been inserted.

   if( used. insert( name ). second )
   {
      renamings[ name ]. push_back( names. size( ));  
      names. push_back( { name, name } );  
   }
   else
   {
      auto range = 
         ( name. empty( ) || isdigit( name. back( )) ) ?
               std::pair( 'a', 'z' ) : std::pair( '0', '9' );

      // std::cout << range. first << " ... " << range. second << "\n";

      auto& ren = renamings[ name ];
      auto name2 = 
         ren. size( ) ? 
            names. at( ren. back( )). second : name; 
         
      do 
         increase( name2, range. first, range. second );
      while( used. contains( name2 ));

      ren. push_back( names. size( )); 
      names. push_back( { name, name2 } );
      used. insert( name2 );
   } 

   return names. back( ). second;
}


void logic::pretty::uniquenamestack::restore( size_t s )
{
   while( names. size( ) > s )
   {

      auto p = renamings. find( names. back( ). first ); 
      p -> second. pop_back( );  
      if( p -> second. size( ) == 0 )
         renamings. erase(p);  

      used. erase( names. back( ). second );

      names. pop_back( );
   }
}


void 
logic::pretty::uniquenamestack::print( std::ostream& out ) const
{
   out << "Uniquenamestack:\n";
   for( auto ind = 1 - (ssize_t) size( ); const auto& n : names ) 
   {
      out << "   #" << ind << " : ";
      out << n. first << " --> ";
      out << n. second << "\n";
      ++ ind;
   }

   if constexpr( false )
   {
      out << "{";
      for( auto p = used. begin( ); p != used. end( ); ++ p )
      {
         if( p != used. begin( ))
            out << ", ";
         else
            out << " ";
         out << *p;
      }
      out << " }\n";
   }
 
   if( used. size( ) != names. size( ))
      throw std::logic_error( "sizes not right" ); 
}

