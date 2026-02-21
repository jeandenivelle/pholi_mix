
#include "uniquenamestack.h"
#include "util/print.h"

namespace
{

   void increase( std::string& val )
   {
      constexpr char first = '0';
      constexpr char last = '9';

      size_t i = val. size( );
      while( i -- )
      {
         if( val[i] == last )
            val[i] = first;
         else
         {
            ++ val[i];
            return;
         }
      }

      val. insert( val. begin( ), first );
      ++ val. front( );
   }


   size_t split( std::string& base ) 
   {
      size_t k = base. size( );
      while( k != 0 && isdigit( base[ k - 1 ] ))
         -- k; 

      size_t index = 0;
      for( size_t i = k; i != base. size( ); ++ i )
      {
         index *= 10;
         index += ( base[i] - '0' ) & 0X0F;
      }

      while( base. size( ) > k )
         base. pop_back( ); 

      return index;
   }
}


const logic::pretty::uniquename&
logic::pretty::uniquenamestack::extend( std::string name )
{
   size_t index = split( name );
   if( name. empty( ))
      name = "V";

   auto& inds = indices[ name ];
      // Indices given out for this name.

   if( inds. size( ) && inds. back( ) + 1 > index )
      index = inds. back( ) + 1;

   inds. push_back( index );

   names. push_back( uniquename( name, index ));
   return names. back( ); 
}


void logic::pretty::uniquenamestack::restore( size_t s )
{
   while( names. size( ) > s )
   {
      const auto& base = names. back( ). base;

      auto it = indices. find( base );
      it -> second. pop_back( ); 
      if( it -> second. empty( ))
         indices. erase( it ); 
            // Otherwise, base will be considered unsafe forever.

      names. pop_back( );
   }
}


bool
logic::pretty::uniquenamestack::issafe( std::string s ) const
{
   split(s);   // We are ignoring the returned index.
   return indices. find(s) == indices. end( );
}


void 
logic::pretty::uniquenamestack::print( std::ostream& out ) const
{
   out << "Uniquenamestack:\n";
   for( auto ind = 1 - (ssize_t) size( ); const auto& n : names ) 
   {
      out << "   #" << ind << " : ";
      out << n << "\n";

      ++ ind;
   }
}

