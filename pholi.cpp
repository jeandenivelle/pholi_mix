
#include "errorstack.h"
#include "filehasher.h"

#include "identifier.h"
#include "tests.h"

#include "logic/exact.h"
#include "logic/structural.h"
#include "logic/pretty.h"
#include "logic/termoperators.h"
#include "logic/replacements.h"
#include "logic/cmp.h"

#include "parsing/parser.h"

void
includefile( logic::beliefstate& blfs, 
             filehasher& seen, const std::filesystem::path& file,
             errorstack& err ) 
{
   if( !exists( file ))
   {
      errorstack::builder bld;
      bld << "file " << file. string( ) << " does not exist";
      err. push( std::move( bld ));
      return;
   }

   // If the file was read already, we ignore it:

   if( !seen. insert( file ))
      return;
 
   std::cout << "file " << file << " is new and will be read\n";

   // We checked existence of file, but one never knows ...

   std::ifstream in( file );
   if( !in )
   {
      errorstack::builder bld; 
      bld << "could not open file " << file. string( ) << "\n";
      err. push( std::move( bld ));  
      return; 
   }

   lexing::filereader inp( &in, file );

   parsing::tokenizer tok( std::move( inp ));
   parsing::parser prs( tok, blfs );

   prs. debug = 0;
   prs. checkattrtypes = 0;

   errorstack::builder bld;

   auto res = prs. parse( parsing::sym_File, bld );

   if( bld. view( ). size( ))
   {
      size_t s = err. size( );
      err. push( std::move( bld ));

      errorstack::builder header;
      header << "there were parse errors in file "
             << file. string( ) << ": ";
      err. addheader( s, std::move( header ));       
   }

}


#include "calc/proofchecking.h"
#include "calc/quantifiers.h"
#include "calc/propositional.h"
#include "calc/saturation.h"
#include "calc/truthform.h"

#include "calc/pretty.h"

#if 0
struct rewriter
{
   rewriter( ) noexcept = default;

#endif

int main( int argc, char* argv[] )
{
   tests::saturate( );
   return 0;

   using tf = calc::truthform< std::string > ;
 
   calc::disjunction_map< std::string > cl1;
   calc::disjunction_map< std::string > cl2;

   cl1. insert( tf( "de", calc::truthset::ffff ));
   cl1. insert( { "hans", calc::truthset::ffff } );
   cl1. insert( { "hans", calc::truthset::tttt } );
   cl1. insert( { "aa", calc::truthset::empty } );
   cl1. insert( { "aa", calc::truthset::tttt } );
   cl1. insert( { "de", calc::truthset::tttt } );
   cl1. insert( { "aa", calc::truthset::eeee } );

   cl2. insert( { "hans", calc::truthset::ffff } );
   cl2. insert( { "deX", calc::truthset::ffee } );
   cl2. insert( { "nivelle", calc::truthset::tttt } );

   std::cout << cl1 << "\n";
   // std::cout << cl2 << "\n";

   cl1. merge_equiv< []( const std::string& s1, const std::string& s2 ) 
      { return s1 == s2; } > ( );

   std::cout << cl1 << "\n"; 

   cl1. remove_nevertrue( );

   std::cout << cl1 << "\n";

   return 0;

   errorstack err;
   logic::beliefstate blfs;  
   filehasher seen;

   includefile( blfs, seen, "examples/standard.phl", err ); 
   includefile( blfs, seen, "aa1", err );
   includefile( blfs, seen, "examples/natural.phl", err );
   // includefile( blfs, seen, "examples/automata.phl", err );

   seen. print( std::cout );

   std::cout << "(before type checking)\n";
   std::cout << blfs << "\n";

   checkandresolve( blfs, err );
   std::cout << "(after type checking)\n";

   tests::pretty( blfs );

   std::cout << blfs << "\n";

   // tests::clausify( blfs, err );

   // tests::truthtables( );

   // tests::smallproofs( blfs, err );
   tests::bigproof( blfs, err );

   std::cout << err << "\n";

   return 0;
}


