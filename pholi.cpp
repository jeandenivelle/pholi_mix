
#include <filesystem>

#include "identifier.h"
#include "tests.h"

#include "logic/exact.h"
#include "logic/structural.h"
#include "logic/pretty.h"
#include "logic/termoperators.h"
#include "logic/replacements.h"
#include "logic/cmp.h"

#include "parsing/parser.h"

#include "calc/beliefproof.h"

void
includebeliefs( logic::beliefstate& blfs, 
                const std::filesystem::path& file,
                errorvector& errs ) 
{
   if( !exists( file ))
   {
      errortree::builder bld;
      bld << "file " << file. string( ) << " does not exist";
      errs. push_back( errortree( std::move( bld )));
      return;
   }

   // We already checked existence of file, but one never knows ...

   std::ifstream in( file );
   if( !in )
   {
      errortree::builder bld; 
      bld << "could not open file " << file. string( ) << "\n";
      errs. push_back( errortree( std::move( bld )));  
      return; 
   }

   lexing::filereader inp( &in, file );

   parsing::tokenizer tok( std::move( inp )); 
   parsing::parser prs( tok, blfs );

   prs. debug = 0;
   prs. checkattrtypes = 0;

   errortree::builder parse_err;

   auto res = prs. parse( parsing::sym_BeliefSeq, parse_err );

   if( parse_err. view( ). size( ))
   {
      errortree::builder header;
      header << "there were parse errors in file "
             << file. string( ) << ":\n\n"; 
      header << parse_err. str( ); 
      errs. push_back( errortree( std::move( header ))); 
   }
}


bool
checkproofs( logic::beliefstate& blfs,  
             const std::filesystem::path& file,
             errorvector& errs )
{
   if( !exists( file ))
   {
      errortree::builder bld;
      bld << "proof file " << file. string( ) << " does not exist";
      errs. push_back( errortree( std::move( bld )));
      return false;
   }

   std::ifstream in( file );
   if( !in )
   {
      errortree::builder bld;
      bld << "could not open proof file " << file. string( ) << "\n";
      errs. push_back( errortree( std::move( bld )));
      return false;
   }

   parsing::tokenizer tok( lexing::filereader( &in, file. string( )) );
   parsing::parser prs( tok, blfs );

   prs. debug = 0;
   prs. checkattrtypes = 0;

   errortree::builder parse_err;

   auto res = prs. parse( parsing::sym_ProofSeq, parse_err );

   if( parse_err. view( ). size( ))
   {
      errortree::builder header;
      header << "there were parse errors in proof file "
             << file. string( ) << ":\n\n";
      header << parse_err. str( ); 
      errs. push_back( errortree( std::move( header )));
      return false; 
   }

   return true;
}


#include "calc/pretty.h"
#include "calc/fitch_diagram.h"

template< typename T >
concept has_equality =
   requires( T t1, T t2 )
      { { t1 == t2 } -> std::convertible_to<bool> ; };

template< typename T >
bool compare( const T& t1, const T& t2 )
{
   if constexpr( has_equality<T> )
      return t1 == t2;
   else
      return &t1 == &t2;
}

int main( int argc, char* argv[] )
{

#if 0
   logic::vartype var1 = { "aaaa", logic::type_obj };
   logic::vartype var2 = { "bbbb", logic::type_obj };
   std::cout << compare( var1, var2 ) << "\n";
   std::vector< logic::vartype > v1;
   std::vector< logic::vartype > v2;
   // std::cout << compare( v1, v2 ) << "\n";

   std::cout << has_equality< std::vector< logic::vartype >> << "\n";
   std::cout << std::equality_comparable< std::vector< logic::vartype >> << "\n";
   return 0;
#endif

   errorvector err;
   logic::beliefstate blfs;  

   includebeliefs( blfs, "examples/standard.phl", err ); 
   includebeliefs( blfs, "examples/natural.phl", err );
   includebeliefs( blfs, "examples/orders.phl", err );
   includebeliefs( blfs, "examples/multiset.phl", err );
   includebeliefs( blfs, "examples/knaster_tarski.phl", err );

   // includebeliefs( blfs, "examples/automata.phl", err );

   std::cout << "(before type checking)\n";
   std::cout << blfs << "\n";

   checkandresolve( blfs, err );
   std::cout << "(after type checking)\n";

   tests::pretty( blfs );

   std::cout << blfs << "\n";

   // tests::truthtables( );

   tests::smallproofs( blfs, err );
   tests::bigproof( blfs, err );

   checkproofs( blfs, "examples/knaster_tarski.prf", err );

   std::cout << err << "\n";

   return 0;
}


