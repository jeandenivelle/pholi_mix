
#include "tokenizer.h"

parsing::tokenizer::tokenizer( lexing::filereader&& inp )
   :inp( std::move(inp) )
{ }

lexing::classifier< char, parsing::symbolval >
parsing::tokenizer::buildclassifier()
{
   using namespace lexing;

   classifier<char, symbolval> cls( symbolval::sym_SCANERROR );   

   auto letter = range( 'a', 'z' ) | range( 'A', 'Z' );
   auto digit = range('0', '9');
   cls.insert( ( just('_') | letter | digit ).plus(), symbolval::sym_VARIABLE );

   // Single-double char tokens:

   cls.insert( just( ']' ), sym_RBRACKET );
   cls.insert( just( '[' ), sym_LBRACKET );
   cls.insert( just( ')' ), sym_RPAR );
   cls.insert( just( '(' ), sym_LPAR );
   cls.insert( just( '}' ), sym_RBRACE );
   cls.insert( just( '{' ), sym_LBRACE );
   cls.insert( just( '<' ), sym_LEXISTS );
   cls.insert( just( '>' ), sym_REXISTS );

   cls.insert( word( ":=" ), symbolval::sym_ASSIGN );
   cls.insert( word( "==" ), symbolval::sym_EQ );
   cls.insert( word( "!=" ), symbolval::sym_NE );

   cls. insert( just('!'), symbolval::sym_NOT );
   cls. insert( just( '#' ), symbolval::sym_PROP );

   cls.insert( just( '&' ), symbolval::sym_AND );
   cls.insert( just( '|' ), symbolval::sym_OR ) ;
   cls.insert( word( "->" ), symbolval::sym_IMPLIES );
   cls.insert( word( "<->" ), symbolval::sym_EQUIV );

   cls.insert( just( '.' ), symbolval::sym_DOT );
   cls.insert( just( ',' ), symbolval::sym_COMMA );
   cls.insert( just( ':' ), symbolval::sym_COLON );
   cls.insert( just( ';' ), symbolval::sym_SEMICOLON );
   cls.insert( word( "::" ), symbolval::sym_SEP );

   // Keywords:

   cls.insert( word( "struct" ), symbolval::sym_STRUCT);
   cls.insert( word( "end" ), symbolval::sym_END );
   cls.insert( word( "def" ), symbolval::sym_DEF );
   cls.insert( word( "symbol" ), symbolval::sym_SYMBOL );

   cls.insert( word( "thm" ), symbolval::sym_THM );
   cls.insert( word( "axiom" ), symbolval::sym_AXIOM );

   cls.insert( word( "??" ), symbolval::sym_LAMBDA );
   cls.insert( word( "let" ), symbolval::sym_LET );
   cls.insert( word( "in" ), symbolval::sym_IN );
   cls.insert( word( "eof" ), symbolval::sym_EOF );

   cls.insert( ( just( ' ' ) | just( '\f' ) | just( '\n' ) | just( '\r' ) | 
                 just( '\t' ) | just( '\v' ) ).plus(), symbolval::sym_WHITESPACE );

   cls.insert( word( "//" ) * 
          every<char>( ). without( '\n' ). star( ) * just( '\n' ),
          symbolval::sym_COMMENT );

   cls.insert( word( "/*" ) *
      ( every<char>( ). without( '*' ) | 
        ( just( '*' ). plus( ) * 
        every<char>( ). without( '/' ). without( '*' ))).star( )
           * ( just( '*' ).plus() * just( '/' )),
                 symbolval::sym_COMMENT);

   return minimize( make_deterministic( cls ));
}

parsing::symbol
parsing::tokenizer::read( )
{
   static auto cls = buildclassifier( );

restart:
   location startloc = getlocation();

   if( !inp.has(1))
      return symbol( sym_EOF, startloc );

   if( !inp.good( ))
      return symbol( sym_FILEBAD, startloc );

   auto p = readandclassify( cls, inp );
  
   if( p.first == sym_SCANERROR )
   {
      if( p. second == 0 )
         p. second = 1;
      std::string attr = std::string( inp.view( p.second ));
      inp.commit( p.second );
      return symbol( sym_SCANERROR, startloc, attr ); 
   }

   if( p.first == sym_WHITESPACE || p.first == sym_COMMENT )
   {
      inp.commit( p.second );
      goto restart; 
   }

   if( p.first == sym_VARIABLE )
   {
      std::string_view v = inp. view( p. second );      
      std::string attr = std::string(v);
      
      inp.commit( p.second );
      return symbol( sym_VARIABLE, startloc, attr);
   }

   // All the remaining tokens have no attribute:

   inp.commit( p. second );
   return symbol( p. first, startloc );
}


void parsing::tokenizer::test() {
   auto sym = read( );
   while( sym.val != symbolval::sym_EOF && 
          sym.val != symbolval::sym_SCANERROR ) 
   {
      std::cout << sym << "\n";
      sym = read();
   }
   std::cout << sym << "\n";
}


