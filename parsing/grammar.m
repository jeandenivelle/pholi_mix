%startsymbol File EOF

%symbol File
%symbol{} Statement Expr

%symbol{ logic::term } Term DotTerm ApplTerm EqTerm
%symbol{ logic::term } UnTermWith UnTermWithout
%symbol{ logic::term } AndTermWith AndTermWithout
%symbol{ logic::term } OrTermWith OrTermWithout
%symbol{ logic::term } ImpliesTermWith ImpliesTermWithout
%symbol{ logic::term } EquivTermWith EquivTermWithout

%symbol{ logic::term } GreedyPrefTerm
   // Greedy Prefix Term that grabs everything to its right.

%symbol{ std::vector< logic::term > } ArgSeq

%symbol{ logic::type } StructType func 
%symbol{ std::vector< logic::type > } StructTypeSeq

%symbol{ std::string } VARIABLE
%symbol{ identifier } Identifier IdentifierStart

%symbol{ std::vector< std::string > } VarSeq
%symbol{ std::vector< logic::vartype > } VarTypeSeq VarsOneType 
   // VarsOneType has form v1, ..., vn : T 

%symbol{ std::vector< std::vector< logic::vartype >> } ParSeqSeq 
   // Used in definitions. A definition can have form
   // def x( ) ( ) ( ) := t, so we need a vector of vector of vartypes.

%symbol{ std::vector< std::pair< logic::vartype, logic::term >> } LetDefSeq 
   // Symbols that are defined in the scope of a let,
   // first is the declaration, second is the given value. 

%symbol{ logic::fielddecl } FieldDecl 
%symbol{ logic::structdef } FieldDeclSeq 

%symbol{ } STRUCT END DEF SYMBOL THM AXIOM 

%symbol{ } EOF FILEBAD WHITESPACE COMMENT 
%symbol{ } LPAR RPAR LBRACE RBRACE LBRACKET RBRACKET LEXISTS REXISTS
%symbol{ } EQ NE ASSIGN
%symbol{ } NOT PROP
%symbol{ } AND OR IMPLIES EQUIV 
%symbol{ } COLON SEMICOLON COMMA DOT SEP
%symbol{ } LET IN LAMBDA
%symbol{ std::string } SCANERROR

%symbolcode_h { #include "location.h" }
%symbolcode_h { #include <vector> }
%symbolcode_h { #include <string> }
%symbolcode_h { #include "logic/type.h" }
%symbolcode_h { #include "identifier.h" }
%symbolcode_h { #include "logic/beliefstate.h"}

%parsercode_cpp
{
   namespace
   {
      logic::term 
      abstract( const std::vector< std::vector< logic::vartype >> & abstr,
                logic::term tm )
      {
         for( size_t i = abstr. size( ); i -- ; ) 
         {
            tm = logic::term( logic::op_lambda, tm,
                              abstr[i]. begin( ), abstr[i]. end( ));
         }
         return tm;
      }

      logic::type
      abstract( const std::vector< std::vector< logic::vartype >> & abstr,
                logic::type tp )
      {
         for( size_t i = abstr. size( ); i -- ;  )
         {
            tp = logic::type( logic::type_func, tp, { } );
            auto f = tp. view_func( );
            for( const auto& vt : abstr[i] )
               f. push_back( vt. tp );
         }
         return tp;  
      }
   }
}

%symbolspace parsing
%parserspace parsing

%parsercode_h { #include "tokenizer.h" }

%infotype{ location }

%parameter { tokenizer }              tok
%parameter { logic::beliefstate }     blfs

%source{ tok. read( ); }

%rules 

//------------------------- file --------------------------------


File => 
    | File STRUCT Identifier : id ASSIGN 
      FieldDeclSeq : def END SEMICOLON
       { 
          blfs. append( logic::belief( logic::bel_struct, id, def ));
       }
    | File DEF Identifier : id ParSeqSeq : abstr ASSIGN 
      Term : tm COLON StructType : tp SEMICOLON
       { 
          tm = abstract( abstr, std::move(tm) ); 
          tp = abstract( abstr, std::move(tp) );
          blfs. append( logic::belief( logic::bel_def, id, tm, tp )); 
       }
    | File SYMBOL Identifier : id ParSeqSeq : abstr COLON StructType : tp SEMICOLON 
      {
         tp = abstract( abstr, std::move(tp) ); 
         blfs. append( logic::belief( logic::bel_symbol, id, tp ));
      }
    | File AXIOM Identifier : id COLON Term : f SEMICOLON 
       { 
          blfs. append( logic::belief( logic::bel_axiom, id, f, 
                                       logic::proof( ), { } )); 
       } 
    | File THM Identifier : id COLON Term : f SEMICOLON
       { 
          blfs. append( logic::belief( logic::bel_thm, id, f, 
                                       logic::proof( ), { } )); 
       } 
    | File _recover_ SEMICOLON
       { std::cout << "recovered!!!\n"; } 
    ;

// ----------------------- struct ---------------------------------

FieldDeclSeq => 
   { return logic::structdef( ); }
|
   FieldDeclSeq : seq FieldDecl : decl
   { seq. append( std::move( decl )); return seq; }
;

FieldDecl => Identifier: id COLON StructType : tp SEMICOLON
{
   return logic::fielddecl( std::move( id ), std::move( tp ));
}
;

// -------------------------- def ------------------------------

ParSeqSeq => 
   { 
      return std::vector< std::vector< logic::vartype >> ( ); 
   }
| ParSeqSeq : abstr LPAR RPAR 
   { 
      abstr. push_back( std::vector< logic::vartype > ( )); 
      return std::move( abstr ); 
   }
| ParSeqSeq : abstr LPAR VarTypeSeq : pars RPAR 
   { 
      abstr. push_back( pars ); 
      return std::move( abstr ); 
   }
; 

// ----------------------------- used in let --------------------

LetDefSeq => VARIABLE : v ASSIGN Term : val COLON StructType : tp 
{
   std::vector< std::pair< logic::vartype, logic::term >> res;
   res. push_back( std::pair( logic::vartype( v, tp ), val ));
   return res;
}
| LetDefSeq : defs COMMA 
    VARIABLE : v ASSIGN Term : val COLON StructType : tp 
{
   defs. push_back( std::pair( logic::vartype( v, tp ), val ));
   return std::move( defs ); 
}
;

// ----------------------------- term ---------------------------

Term => EquivTermWith : tm { return tm; }
;

VarSeq => VARIABLE : v 
{ 
   std::vector< std::string > res; 
   res. push_back(v); 
   return res; 
} 
| VarSeq : seq COMMA VARIABLE : v 
{
   seq. push_back(v);
   return std::move( seq );
}
;   

VarsOneType => VarSeq : seq COLON StructType : tp 
{
   std::vector< logic::vartype > res;
   for( const auto& v : seq )
      res. push_back( logic::vartype( v, tp ));
   return res; 
}
;

VarTypeSeq => VarsOneType : vot
{ 
   return std::move( vot ); 
}
| VarTypeSeq : seq COMMA VarsOneType : vot
{
   for( auto& v : vot )
      seq. push_back( std::move(v) );
   return std::move( seq ); 
}
;

StructType => 
   Identifier : id { return logic::type( logic::type_unchecked, id ); }
|
   StructType : f LPAR StructTypeSeq : tps RPAR 
   {
      return logic::type( logic::type_func, f, tps.begin( ), tps.end( ));
   }
; 

StructTypeSeq => StructType:t 
   { return std::vector< logic::type > {t}; }
| StructTypeSeq:v COMMA StructType : t 
   { v.push_back(t); return std::move(v); }
;

IdentifierStart => 
   { return identifier( ); }
|
   SEP 
   { return identifier( ) + ""; }
;

Identifier => IdentifierStart : id VARIABLE : v { return id + v; } 
           | Identifier : id SEP VARIABLE : v  { return id + v; } 
           ;


// These are these greedy prefix operators that eat everything
// they find to the right of them:

GreedyPrefTerm => LBRACKET VarTypeSeq : vars RBRACKET Term : body
{
   return logic::term( logic::op_forall, body, vars. begin( ), vars. end( ));
}
| LEXISTS VarTypeSeq : vars REXISTS Term : body
{
   return logic::term( logic::op_exists, body, vars. begin( ), vars. end( ));
}
| LAMBDA LPAR VarTypeSeq : vars RPAR Term : body
{
   return logic::term( logic::op_lambda, body, vars. begin( ), vars. end( ));
}
| LBRACE Term : t1 RBRACE AND Term : t2 
{
   return logic::term( logic::op_lazy_and, t1, t2 );
}
| LBRACE Term : t1 RBRACE IMPLIES Term : t2
{
   return logic::term( logic::op_lazy_implies, t1, t2 );
}
| LBRACE Term : t1 RBRACE OR Term : t2
{
   return logic::term( logic::op_or, t1, t2 );
}
| LET LetDefSeq : defs IN Term : tm 
{
   size_t i = defs. size( );
   while(i)
   { 
      -- i;
      tm = logic::term( logic::op_let, defs[i]. first, defs[i]. second, tm );
   }
   return tm;
}
;


EquivTermWith => ImpliesTermWith : t { return std::move(t); }
|  ImpliesTermWithout : t1 EQUIV ImpliesTermWith : t2
{
   return logic::term( logic::op_equiv, t1, t2 );
};

EquivTermWithout => ImpliesTermWithout : t { return std::move(t); }
|  ImpliesTermWithout : t1 EQUIV ImpliesTermWithout : t2 
{
   return logic::term( logic::op_equiv, t1, t2 );
};


ImpliesTermWith => OrTermWith : t { return std::move(t); }
|
   OrTermWithout : t1 IMPLIES ImpliesTermWith : t2 
{
   return logic::term( logic::op_implies, t1, t2 );
}
;

ImpliesTermWithout => OrTermWithout : t { return std::move(t); }
|
   OrTermWithout : t1 IMPLIES ImpliesTermWithout : t2 
{
   return logic::term( logic::op_implies, t1, t2 );
}
;


OrTermWith => AndTermWith : t { return std::move(t); }
| OrTermWithout : t1 OR AndTermWith : t2 
      { return logic::term( logic::op_or, t1, t2 ); }
;

OrTermWithout => AndTermWithout : t { return std::move(t); }
| OrTermWithout : t1 OR AndTermWithout : t2 
      { return logic::term( logic::op_or, t1, t2 ); }
;


AndTermWith => UnTermWith : t { return std::move(t); }
| AndTermWithout : t1 AND UnTermWith : t2 
      { return logic::term( logic::op_and, t1, t2 ); }
;

AndTermWithout => UnTermWithout : t { return std::move(t); }
| AndTermWithout : t1 AND UnTermWithout : t2 
   { return logic::term( logic::op_and, t1, t2 ); }
;

UnTermWith =>
   EqTerm : t { return std::move(t); }
|
   NOT UnTermWith : t { return logic::term( logic::op_not, t ); }
|
   PROP UnTermWith : t { return logic::term( logic::op_prop, t ); }
|
   GreedyPrefTerm : gr { return std::move(gr); }    
;

UnTermWithout =>
   EqTerm : t { return std::move(t); }
|
   NOT UnTermWithout : t { return logic::term( logic::op_not, t ); }
|
   PROP UnTermWithout : t { return logic::term( logic::op_prop, t ); }
;

EqTerm =>
   DotTerm : t { return std::move(t); }
|
   DotTerm : t1  EQ  DotTerm : t2 
      { return logic::term( logic::op_equals, t1, t2 ); }

|
   DotTerm : t1  NE  DotTerm : t2 
   { return logic::term( logic::op_not, 
               logic::term( logic::op_equals, t1, t2 ));
   }
;


DotTerm => 
   ApplTerm : tm { return std::move( tm ); } 
|
   DotTerm : first DOT Identifier : func
{
   logic::term tm = logic::term( logic::op_apply, 
                                 logic::term( logic::op_unchecked, func ),
                                 std::initializer_list< logic::term > ( ));
   auto fv = tm. view_apply( );
   fv. push_back( std::move( first )); 
   return tm;
}
| 
   DotTerm : first DOT Identifier : func LPAR ArgSeq : rest RPAR 
{
   logic::term tm = logic::term( logic::op_apply, 
                                 logic::term( logic::op_unchecked, func ),
                                 std::initializer_list< logic::term > ( ));
   auto fv = tm. view_apply( );
   fv. push_back( std::move( first ));
   for( auto& a : rest )
      fv. push_back( std::move(a) ); 
   return tm; 
}
;

ApplTerm =>  
   ApplTerm : func LPAR ArgSeq : args RPAR
      { return logic::term( logic::op_apply, 
                            func, args. begin( ), args. end( )); }

| Identifier : id  { return logic::term( logic::op_unchecked, id ); }
| LPAR Term : tm RPAR { return std::move(tm); } 
; 

ArgSeq => ArgSeq : args COMMA Term : t 
   { args. push_back( std::move(t)); return std::move( args ); } 
            | Term : t
   { std::vector< logic::term > res;
     res. push_back( std::move(t)); 
     return res;
   } 
            ;

%end
 
