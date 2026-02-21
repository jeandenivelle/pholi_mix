
// Written by Hans de Nivelle, August 2024.

#ifndef LOGIC_STRUCTDEF_
#define LOGIC_STRUCTDEF_

#include <vector>

#include "type.h"
#include "identifier.h"
#include "util/print.h"

namespace logic
{
   struct fielddecl
   {
      identifier name;
      type tp;

      fielddecl( const identifier& name, const type& tp )
         : name( name ), tp( tp )
      { }

      fielddecl( identifier&& name, type&& tp )
         : name( std::move( name )), tp( std::move( tp ))
      { }

      void print( std::ostream& out ) const
         { out << name << " : " << tp; }
   };

   // Field names do not need to be unique, because they
   // are subject to overload resolution. A structdef is
   // just a vector of field definitions. 
   // Class structdef behaves like a vector to the outside. 
   // The offset of a field in the struct is the index in the vector.

   struct structdef
   {
      std::vector< fielddecl > repr;

      structdef( ) noexcept = default;

      size_t append( const fielddecl& fld )
      { 
         size_t offset = repr. size( );
         repr. push_back( fld ); 
         return offset;
      }

      size_t append( fielddecl&& fld )
      {
         size_t offset = repr. size( );
         repr. push_back( std::move( fld )); 
         return offset;
      }

      // Needed because the thing is needed in a tree generated
      // by TreeGen:

      bool very_equal_to( const structdef& def ) const
         { return repr. data( ) == def. repr. data( ); } 

      using const_iterator = std::vector< fielddecl > :: const_iterator;
      const_iterator begin( ) const { return repr. begin( ); }
      const_iterator end( ) const { return repr. end( ); }

      using iterator = std::vector< fielddecl > :: iterator;
      iterator begin( ) { return repr. begin( ); }
      iterator end( ) { return repr. end( ); }
      
      size_t size( ) const { return repr. size( ); }
      const fielddecl& at( size_t offset ) const { return repr. at( offset ); }
      fielddecl& at( size_t offset ) { return repr. at( offset ); }

      void print( std::ostream& out ) const;
   };
}

#endif

