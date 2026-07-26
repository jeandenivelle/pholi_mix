
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


bool
calc::checkfile( logic::beliefstate& blfs, errorstack& err, 
                 const std::filesystem::path& file )
{

#if 0
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
#endif
   return true;
}
