
#include "filechecker.h"

bool
calc::filechecker::check( logic::beliefstate& blfs, std::string_view sub )
{
   if( !exists( file ))
   {
      errorstack::builder bld;
      bld << "file " << file. string( ) << " does not exist";
      err. push( std::move( bld ));
      return false;
   }

   std::ifstream in( file );
   if( !in )
   {
      errorstack::builder bld;
      bld << "could not open file " << file. string( ) << "\n";
      err. push( std::move( bld )); 
      return false; 
   }

   parsing::tokenizer tok( lexing::filereader( &in, file. string( )) );
#if 0
#if 0
   if( !src )
   {
      err. push( "there is no file" );
      return;
   }
#endif
#endif
   std::cout << "check was entered " << sub << "\n";

   auto sym = tok. read( );
   while( sym.val != parsing::symbolval::sym_EOF )
   {
      std::cout << sym << "\n";
      if( sym.val == parsing::symbolval::sym_SEQCALC )
      {


      }

      sym = tok.read( );
   }
   std::cout << sym << "\n";

   return true;
}
