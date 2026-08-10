
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

#include "calc/namedproofchecker.h"

void
includebeliefs( logic::beliefstate& blfs, 
                const std::filesystem::path& file,
                errorvector& errors ) 
{
   if( !exists( file ))
   {
      errortree::builder bld;
      bld << "file " << file. string( ) << " does not exist";
      errors. push_back( std::move( bld ));
      return;
   }

   // We already checked existence of file, but one never knows ...

   std::ifstream in( file );
   if( !in )
   {
      errortree::builder bld; 
      bld << "could not open file " << file. string( ) << "\n";
      errors. push_back( std::move( bld ));  
      return; 
   }

   lexing::filereader inp( &in, file );

   parsing::tokenizer tok( std::move( inp )); 
   parsing::parser prs( tok, blfs );

   prs. debug = 0;
   prs. checkattrtypes = 0;

   errortree::builder parse_errors;

   auto res = prs. parse( parsing::sym_BeliefSeq, parse_errors );

   if( parse_errors. view( ). size( ))
   {
      errorvector vect;
      vect. push_back( std::move( parse_errors ));

      errortree::builder header;
      header << "syntax errors in file " << file. string( ) << " :"; 
      transfer( std::move( header ), std::move( vect ), errors ); 
   }
}


void
checkproofs( logic::beliefstate& blfs,  
             const std::filesystem::path& file,
             errorvector& errors )
{
   if( !exists( file ))
   {
      errortree::builder bld;
      bld << "proof file " << file. string( ) << " does not exist";
      errors. push_back( std::move( bld ));
      return;
   }

   std::ifstream in( file );
   if( !in )
   {
      errortree::builder bld;
      bld << "could not open proof file " << file. string( ) << "\n";
      errors. push_back( std::move( bld ));
      return;
   }

   parsing::tokenizer tok( lexing::filereader( &in, file. string( )) );
   parsing::parser prs( tok, blfs );

   prs. debug = 0;
   prs. checkattrtypes = 2;

   errortree::builder syntax_errors;

   auto res = prs. parse( parsing::sym_ProofSeq, syntax_errors );
 
   // If there are syntax errors, we merge them into errors. 

   if( syntax_errors. view( ). size( ))
   {
      errorvector vect;
      vect. push_back( std::move( syntax_errors ));

      errortree::builder header;
      header << "syntax errors in proof file " << file. string( ) << " :";
      transfer( std::move( header ), std::move( vect ), errors );
   }

   // If there are proof errors, we also move them into errors.

   if( prs. prooferrors. size( ))
   {
      errortree::builder header;
      header << "proof errors in proof file " << file. string( ) << " :";
      transfer( std::move( header ), std::move( prs. prooferrors ), errors );
   }

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

   checkproofs( blfs, "examples/knaster_tarski.prf", err );

   // tests::smallproofs( blfs, err );
   // tests::bigproof( blfs, err );

   std::cout << "Errors:\n";
   for( auto& e : err )
   {
      e. report( std::cout ); 
   }
   std::cout << "\n";

   return 0;
}


