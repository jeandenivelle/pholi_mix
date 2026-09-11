
// Written by Hans de Nivelle, September 2026.

#include <vector>
#include <iostream>

#include "type.h"

#ifndef LOGIC_TYPESEQUENCE_
#define LOGIC_TYPESEQUENCE_

namespace logic
{
   struct typesequence
   {

      std::vector< type > repr;

      typesequence( ) noexcept = default;
      explicit typesequence( std::vector< type > && repr ) noexcept
         : repr( std::move( repr ))
      { }

      type& at( size_t i ) 
         { return repr. at(i); }

      const type& at( size_t i ) const 
         { return repr. at(i); } 
 
      void append( type tp ) 
         { repr. push_back( std::move(tp) ); } 

      using iterator = std::vector< type > :: iterator;
      using const_iterator = std::vector< type > :: const_iterator;

      iterator begin( ) { return repr. begin( ); }
      iterator end( ) { return repr. end( ); }

      const_iterator begin( ) const { return repr. begin( ); }
      const_iterator end( ) const { return repr. end( ); }

      size_t size( ) const { return repr. size( ); }
 
      void print( std::ostream& out ) const; 
   };
   
   bool isprefix( const typesequence& tp1, const typesequence& tp2 );
      // True if tp1 is a prefix of tp2.

   inline 
   bool operator == ( const typesequence& tp1, const typesequence& tp2 )
   {
      return tp1. size( ) == tp2. size( ) && isprefix( tp1, tp2 );
   }

}

#endif

