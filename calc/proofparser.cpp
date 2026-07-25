
#include "proofparser.h"

identifier calc::proofparser::parse_identifier( )
{
   identifier res;

   if( getlookahead( ). val != parsing::sym_VARIABLE )
      throw parse_error( tok. getlocation( ), "identifier expected" );
  
   res += getlookahead( ). get< std::string > ( ); 
   resetlookahead( );

   while( getlookahead( ). val == parsing::sym_SEP )
   {
      resetlookahead( );

      if( getlookahead( ). val != parsing::sym_VARIABLE )
         throw parse_error( tok. getlocation( ), "identifier expected" );

      res += getlookahead( ). get< std::string > ( );
      resetlookahead( ); 
   } 

   return res; 
}

logic::type
calc::proofparser::parse_type( )
{


}

void calc::proofparser::check( logic::beliefstate& blfs )
{
   auto id = parse_identifier( ); 

   std::vector< logic::type > types;
   if( getlookahead( ). val == parsing::sym_LPAR )
   {
      resetlookahead( );
      types. push_back( parse_type( )); 

   } 

}

const parsing::symbol& calc::proofparser::getlookahead( )
{
   if( !lookahead. has_value( ))
      lookahead = tok. read( );

   return lookahead. value( );
}

void calc::proofparser::resetlookahead( )
{
   lookahead. reset( );
}


bool
calc::checkfile( logic::beliefstate& blfs, errorstack& err, 
                 const std::filesystem::path& file )
{

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

   auto sym = tok. read( );
   while( sym.val != parsing::symbolval::sym_EOF )
   {
      std::cout << sym << "\n";
      if( sym.val == parsing::symbolval::sym_SEQCALC )
      {
         auto prs = proofparser( std::move( tok )); 
         std::cout << "\n\n";
         std::cout << "constructed the parser\n";
      }

      sym = tok.read( );
   }
   std::cout << sym << "\n";

   return true;
}
