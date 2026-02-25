
#include "printing.h"
#include "logic/pretty.h"


errorstack::builder
calc::printing::makeheader( const sequent& seq, std::string_view rule )
{
   throw std::logic_error( "i dont think this is called" );

   errorstack::builder bld;
   for( unsigned int i = 0; i < 60; ++ i )
      bld. put( '-' );
   bld. put( '\n' );

   bld << "Error applying " << rule << ":\n";
   // bld << seq << "\n";
   return bld;
}

