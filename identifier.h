
// Written by Hans de Nivelle, December 2020, as part of the Easy Project. 
// Rewritten in November 2021, because the previous version was incomplete.
// I keep on struggling with this simple class. Rewritten one more time
// on October 30th 2022.

#ifndef IDENTIFIER_
#define IDENTIFIER_     

#include <vector>
#include <string> 
#include <compare>
#include <iostream>

#include "identifier.h"
#include "util/hashbuilder.h"

class identifier
{
   std::vector< std::string > repr; 

public: 
   identifier( ) = default; 
   identifier( const identifier& ) = default;
   identifier( identifier&& ) noexcept = default;
   identifier& operator = ( const identifier& ) = default;
   identifier& operator = ( identifier&& ) noexcept = default;
   ~identifier( ) = default;

   using const_iterator = std::vector< std::string > :: const_iterator;
 
   const_iterator begin( ) const { return repr. begin( ); }
   const_iterator cbegin( ) const { return repr. begin( ); }
   const_iterator end( ) const { return repr. end( ); }
   const_iterator cend( ) const { return repr. end( ); }

   identifier& operator += ( const std::string& s )
      { repr. push_back(s); return *this; } 

   identifier& operator += ( std::string&& s ) 
      { repr. push_back( std::move(s)); return *this; }

   identifier& operator += ( const char* c ) 
      { repr. push_back( std::string(c) ); return *this; }

   size_t size( ) const { return repr. size( ); }
   bool isempty( ) const { return repr. empty( ); }

   const std::string& at( size_t i ) const 
      { return repr. at(i); }

   struct equal_to
   {
      equal_to( ) = default;
      bool operator( ) ( const identifier& id1, const identifier& id2 ) const;
   };

   struct hash
   {
      hash( ) = default;  
      size_t operator( ) ( const identifier& id ) const;
   };

};

inline identifier operator + ( identifier id, const std::string& s ) 
   { id += s; return id; }

inline identifier operator + ( identifier id, std::string&& s )
   { id += std::move(s); return id; }

inline identifier operator + ( identifier id, const char* c ) 
   { id += c; return id; }

std::strong_ordering
operator <=> ( const identifier& id1, const identifier& id2 );

inline bool operator == ( const identifier& id1, const identifier& id2 )
   { return is_eq( id1 <=> id2 ); }

inline bool operator != ( const identifier& id1, const identifier& id2 )
   { return !is_eq( id1 <=> id2 ); }
 
std::ostream& operator << ( std::ostream& out, const identifier& id );
util::hashbuilder& operator << ( util::hashbuilder&, const identifier& id );

#endif

