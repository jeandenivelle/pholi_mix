
// Written by Hans de Nivelle, Nov. 2024.
// Changed the interface on 12.12.2024.
// Changed the interface again on 29.07.2026, because
// the old, stack-based approach was incompatible with value
// semantics. Now there is a single class, and errors have
// to be collected in a container of choice first. 
// As a general rule, one should not collect single errors,
// one should always put them in a list or container.

// Any error that is unreported will be aggressively printed 
// when destroyed, and cause the destructor to crash. 

#ifndef ERRORTREE_
#define ERRORTREE_

#include <string>
#include <vector>
#include <iostream> 
#include <sstream>
#include <concepts>
#include <cstdint>

#include "util/indentation.h"

class errortree
{
   std::string header; 

   uint8_t ser;
      // Should be between 0 and 99 (inclusive). 

   bool reported = false; 
      // Will become true if the header was reported. Does not
      // extend to the subtrees.

   std::vector< errortree* > sub;
      // We are move only, move constructor is overloaded. 

   uint8_t limit99( uint8_t ser );

   template< typename S > void push_sub( S s1, S s2 )
   {
      for( auto s = s1; s != s2; ++ s )
         sub. push_back( new errortree( std::move( *s )));

      if( s1 != s2 )
         reported = false; 
   }

   void printheader( indentation ind, std::ostream& out ) const;
      // print without recursing.

public:
   using builder = std::ostringstream;
      // You can whine into the builder, and then construct
      // from the builder. 


   template< std::forward_iterator S >
   requires std::convertible_to< std::iter_value_t<S>, errortree&& >
   errortree( std::string meh, S s1, S s2, uint8_t ser = 99 )
      : header( std::move( meh )),
        ser( limit99( ser ))
   {
      push_sub( s1, s2 );
   }

   errortree( std::string meh, uint8_t ser = 99 )
      : header( std::move( meh )), 
        ser( limit99( ser ))
   { }


   template< std::forward_iterator S >
   requires std::convertible_to< std::iter_value_t<S>, errortree&& >
   errortree( const char* meh, S s1, S s2, uint8_t ser = 99 )
      : header( meh ),
        ser( limit99( ser ))
   {
      push_sub( s1, s2 );
   }

   errortree( const char* meh, uint8_t ser = 99 )
      : header( meh ),
        ser( limit99( ser ))
   { }


   template< std::forward_iterator S >
   requires std::convertible_to< std::iter_value_t<S>, errortree&& >
   errortree( builder&& meh, S s1, S s2, uint8_t ser = 99 )
      : header( std::move( meh ). str( )),
        ser( limit99( ser ))
   {
      push_sub( s1, s2 );
   }

   errortree( builder&& meh, uint8_t ser = 99 )
      : header( std::move( meh ). str( )),
        ser( limit99( ser ))
   { }

   
   errortree( errortree&& other ) noexcept
      : header( std::move( other. header )),
        ser( other. ser ), 
        reported( other. reported ),
        sub( std::move( other. sub ))
   { 
      other. header. clear( );
      other. reported = true;
      other. sub. clear( );
   }

   errortree& operator = ( const errortree& ) = delete;
 
   size_t nrsubtrees( ) const { return sub. size( ); }

   void print( indentation ind, std::ostream& out ) const;
   void print( std::ostream& out ) const { print( indentation(0), out ); }

   void report( indentation ind, std::ostream& out );
   void report( std::ostream& out ) { report( indentation(0), out ); } 

   ~errortree( );

};

using errorvector = std::vector< errortree > ;


std::ostream& operator << ( std::ostream& out, const errortree& tr );
std::ostream& operator << ( std::ostream& out, const errorvector& v );
   // Do not count as reported.

#endif

