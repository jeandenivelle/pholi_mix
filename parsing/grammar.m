
%startsymbol BeliefSeq EOF
%startsymbol ProofSeq EOF

%symbol BeliefSeq
%symbol ProofSeq

%symbol{ logic::term } Term DotTerm ApplTerm EqTerm
%symbol{ logic::term } UnTermWith UnTermWithout
%symbol{ logic::term } AndTermWith AndTermWithout
%symbol{ logic::term } OrTermWith OrTermWithout
%symbol{ logic::term } ImpliesTermWith ImpliesTermWithout
%symbol{ logic::term } EquivTermWith EquivTermWithout

%symbol{ logic::term } GreedyPrefTerm
   // Greedy Prefix Term that grabs everything to its right.

%symbol{ std::vector< logic::term > } TermSeq

%symbol{ logic::type } StructType 
%symbol{ std::vector< logic::type > } StructTypeSeq

%symbol{ std::string } VARIABLE QUOTEDSTRING FORMNAME
%symbol{ int32_t }     INTEGER
%symbol{ size_t }      FormIndex
%symbol{ std::vector< std::string > } QuotedStringSeq EigenNames
%symbol{ identifier }  Identifier IdentifierStart

%symbol{ std::vector< std::string > } VarSeq
%symbol{ std::vector< logic::vartype > } VarTypeSeq VarsOneType 
   // VarsOneType has form v1, ..., vn : T 
   // VarTypeSeq consists of many VarsOneType, separated by commas.

%symbol{ std::vector< std::vector< logic::vartype >> } ParSeqSeq 
   // Used in definitions. A definition can have form
   // def x( ) ( ) ( ) := t, so we need a vector of vector of vartypes.

%symbol{ std::pair< logic::vartype, logic::term > } LetDef
   // A single v:T := t.

%symbol{ std::vector< std::pair< logic::vartype, logic::term >> } LetDefSeq 
   // Symbols that are defined in the scope of a let,
   // first is the declaration, second is the given value. 

%symbol{ logic::fielddecl } FieldDecl 
%symbol{ logic::structdef } FieldDeclSeq 

%symbol{ } STRUCT END DEF SYMBOL THM AXIOM 

%symbol{ } EOF FILEBAD WHITESPACE COMMENT 
%symbol{ } LPAR RPAR LBRACE RBRACE LBRACKET RBRACKET LT GT
%symbol{ } FALSE TRUE 
%symbol{ } EQ NE ASSIGN
%symbol{ } NOT PROP
%symbol{ } AND OR IMPLIES EQUIV 
%symbol{ } COLON SEMICOLON COMMA DOT SEP
%symbol{ } FORALL EXISTS LET LAMBDA
%symbol{ std::string } SCANERROR

%symbol{ } PRF_SEQCALC PRF_SHOW PRF_SETNAME PRF_CUT PRF_FAKE PRF_BRANCH 
%symbol{ } PRF_EXPAND PRF_FLATTEN PRF_NORMALIZE PRF_INSTANTIATE 
%symbol{ } PRF_IMPORT PRF_SIMPLIFY

%symbol{ } SequentProof SeqProofStart SeqBranchStart SeqProofScript

%symbolcode_h { #include "location.h" }
%symbolcode_h { #include <vector> }
%symbolcode_h { #include <string> }
%symbolcode_h { #include <variant> } 
%symbolcode_h { #include "logic/type.h" }
%symbolcode_h { #include "identifier.h" }
%symbolcode_h { #include "logic/beliefstate.h" }
%symbolcode_h { #include "calc/namedproofchecker.h" }


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
%parsercode_h { #include "logic/structural.h" } 
%parsercode_h { #include "calc/structural.h" }

%infotype{ location }

%parameter { tokenizer }              tok
%parameter { logic::beliefstate }     blfs
%localvar  { errorvector }            prooferrors
%localvar  { std::optional< calc::namedproofchecker > } currentproof

%source{ tok. read( ); }

%rules 

//------------------------- file --------------------------------


BeliefSeq => 
    | BeliefSeq STRUCT Identifier : id ASSIGN 
      FieldDeclSeq : def END SEMICOLON
       { 
          blfs. append( logic::belief( logic::bel_struct, id, def ));
       }
    | BeliefSeq DEF Identifier : id ParSeqSeq : abstr COLON StructType : tp 
      ASSIGN Term : tm SEMICOLON
       { 
          tm = abstract( abstr, std::move(tm) ); 
          tp = abstract( abstr, std::move(tp) );
          blfs. append( logic::belief( logic::bel_def, id, tp, tm )); 
       }
    | BeliefSeq SYMBOL Identifier : id ParSeqSeq : abstr COLON 
      StructType : tp SEMICOLON 
      {
         tp = abstract( abstr, std::move(tp) ); 
         blfs. append( logic::belief( logic::bel_symbol, id, tp ));
      }
    | BeliefSeq AXIOM Identifier : id COLON Term : f SEMICOLON 
       { 
          blfs. append( logic::belief( logic::bel_axiom, id, f, 
                                       logic::proofstatus( ), { } )); 
       } 
    | BeliefSeq THM Identifier : id COLON Term : f SEMICOLON
       { 
          blfs. append( logic::belief( logic::bel_thm, id, f, 
                                       logic::proofstatus( ), { } ));
       } 
    | BeliefSeq _recover_ SEMICOLON
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

LetDefSeq => LetDef : def 
{
   std::vector< std::pair< logic::vartype, logic::term >> res;
   res. push_back( std::move( def ));
   return res;
}
| LetDefSeq : defs SEMICOLON LetDef : def  
{
   defs. push_back(  std::move( def ));
   return std::move( defs ); 
}
;

LetDef => VARIABLE : v COLON StructType : tp ASSIGN Term : val 
{
   return std::pair( logic::vartype( v, tp ), val );
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
| VarTypeSeq : seq SEMICOLON VarsOneType : vot
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

StructTypeSeq => StructType : t 
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

GreedyPrefTerm 
=> FORALL LBRACE VarTypeSeq : vars RBRACE COLON Term : body
{
   return logic::term( logic::op_forall, body, vars. begin( ), vars. end( ));
}
| EXISTS LBRACE VarTypeSeq : vars RBRACE COLON Term : body
{
   return logic::term( logic::op_exists, body, vars. begin( ), vars. end( ));
}
| LAMBDA LBRACE VarTypeSeq : vars RBRACE COLON Term : body
{
   return logic::term( logic::op_lambda, body, vars. begin( ), vars. end( ));
}
| LBRACKET Term : t1 RBRACKET Term : t2
{
   return logic::term( logic::op_lazy_implies, t1, t2 );
}
| LT Term : t1 GT Term : t2 
{
   return logic::term( logic::op_lazy_and, t1, t2 );
}
| LET LBRACE LetDefSeq : defs RBRACE COLON Term : tm 
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
   DotTerm : first DOT Identifier : func LPAR TermSeq : rest RPAR 
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
   ApplTerm : func LPAR TermSeq : args RPAR
      { return logic::term( logic::op_apply, 
                            func, args. begin( ), args. end( )); }

| Identifier : id  { return logic::term( logic::op_unchecked, id ); }
| LPAR Term : tm RPAR { return std::move(tm); } 
| FALSE { return logic::term( logic::op_false ); } 
| TRUE { return logic::term( logic::op_true ); }
; 

TermSeq => TermSeq : args COMMA Term : t 
   { args. push_back( std::move(t)); return std::move( args ); } 
            | Term : t
   { std::vector< logic::term > res;
     res. push_back( std::move(t)); 
     return res;
   } 
;

ProofSeq => 
   | ProofSeq SequentProof 
;

SequentProof 
   => SeqProofStart LBRACE SeqProofScript RBRACE 
   {
      if( currentproof. has_value( ))
      {
         auto& prf = currentproof. value( );
         auto fm = blfs. at( prf. name ). view_form( );

         auto stat = fm. extr_status( ); 
         stat. calcname = "seqcalc";
         stat. nrsteps = prf. nrsteps;

         if( prf. errors. size( ))
         {
            errortree::builder bld = prf. errorheader( );
            transfer( std::move( bld ), std::move( prf. errors ), 
                      prooferrors ); 
         }

         stat. dependencies = std::move( prf. dependencies );
         if( prf. qed( ) < prf. size( ))
         {
            ++ stat. nrsteps; 
            stat. distance = 0; 
         }
         else
            stat. distance = 1;

         stat. distance += prf. nrfakes;
         if( stat. distance )
         {
            errortree::builder bld = prf. errorheader( );
            bld << " the proof is not complete";
            prooferrors. push_back( std::move( bld ));
         } 

         fm. update_status( std::move( stat )); 
      }
   }
   ;

SeqProofScript =>

   | SeqProofScript : prf PRF_SHOW QUOTEDSTRING : header SEMICOLON
      { if( currentproof. has_value( ))
           currentproof. value( ). show( header ); 
      }
   | SeqProofScript PRF_SETNAME FormIndex : ind VARIABLE : name SEMICOLON
      {
         if( currentproof. has_value( ))
            currentproof. value( ). setname( ind, name ); 
      }
   | SeqProofScript PRF_CUT Term : fm SEMICOLON 
      { 
        if( currentproof. has_value( ))
        {
           auto& prf = currentproof. value( );
           prf. cut( prf. replacedebruijn( std::move(fm)));
        }
      }
   | SeqProofScript PRF_FAKE Term : fm SEMICOLON 
      {
         if( currentproof. has_value( ))
         {
            auto& prf = currentproof. value( );
            prf. fake( prf. replacedebruijn( std::move(fm)));
         }
      }
   | SeqProofScript SeqBranchStart LBRACE SeqProofScript RBRACE 
      {
         if( currentproof. has_value( ))
         {
            currentproof. value( ). merge( );
         }
      }
   | SeqProofScript PRF_EXPAND FormIndex : ind Identifier : id 
     INTEGER : occ SEMICOLON
      {
         if( currentproof. has_value( ))
         { 
            auto& prf = currentproof. value( );
            if( id. size( ) == 1 )
            {
               size_t var = prf. db. find( id. at(0));
               if( var < prf. db. size( ))
               {
                  var = prf. db. size( ) - var - 1;
                  prf. expand( ind, var, occ );
                  return; 
               } 
            } 
            prf. expand( ind, id, occ );
            return;
         }
      }
   | SeqProofScript PRF_FLATTEN FormIndex : ind SEMICOLON 
      {
         if( currentproof. has_value( ))
            currentproof. value( ). flatten( ind ); 
      }
   | SeqProofScript PRF_NORMALIZE FormIndex : ind SEMICOLON 
      {
         if( currentproof. has_value( ))
            currentproof. value( ). normalize( ind );
      }
   | SeqProofScript PRF_INSTANTIATE FormIndex : ind 
                  LBRACE TermSeq : values RBRACE SEMICOLON
      {
         if( currentproof. has_value( ))
         {
            auto& prf = currentproof. value( );         
            for( auto& v : values )
               v = prf. replacedebruijn( std::move(v));    

            prf. inst( ind, values );
         }   
      }
   | SeqProofScript PRF_SIMPLIFY SEMICOLON 
      {
         if( currentproof. has_value( ))
         {
            currentproof. value( ). simplify( );            
         }
      }
   | SeqProofScript PRF_IMPORT Identifier : id 
                    LPAR StructTypeSeq : tps RPAR SEMICOLON
      {
         if( currentproof. has_value( ))
         {
            auto seq = logic::typesequence( std::move( tps )); 
            currentproof. value( ). import( id, std::move( seq )); 
         }
      }
    | SeqProofScript PRF_IMPORT Identifier : id SEMICOLON 
      {
         if( currentproof. has_value( ))
         {
            currentproof. value( ). import( id, logic::typesequence( ));
         }
      }
;

SeqProofStart => 
   PRF_SEQCALC Identifier : ident LBRACE StructTypeSeq : tps RBRACE COLON
{
   auto seq = logic::typesequence( std::move( tps ));

   errorvector errors;
   if( !checkandresolve( blfs, errors, seq )) 
   {
      errortree::builder bld;
      bld << "unable to start proof of " << ident << ":";
      transfer( std::move( bld ), std::move( errors ), prooferrors );
      return; 
   }

   auto ex = calc::findformula( blfs, errors, ident, seq );
   if( !ex. has_value( )) 
   {
      std::cout << "obviously failed, but where are the errors?\n"; 
      currentproof. reset( );
   }
   else
   {
      currentproof. emplace( &blfs, ex. value( ), 
             calc::getgoal( blfs. at( ex. value( ))) );
   }
}
|
   PRF_SEQCALC Identifier : ident COLON 
{
   errorvector errors;
   auto ex = calc::findformula( blfs, errors, ident, { } );
   if( !ex. has_value( ))
      currentproof. reset( );
   else
      currentproof. emplace( &blfs, ex. value( ),
              calc::getgoal( blfs. at( ex. value( ))) );
}
;

SeqBranchStart => PRF_BRANCH FormIndex : ind INTEGER : choice 
                  EigenNames : eigen COLON
{  
   if( currentproof. has_value( ))
      currentproof. value( ). branch( ind, choice, eigen );
}
;


FormIndex
   => INTEGER : ind
      { 
        if( currentproof. has_value( ))
           return currentproof. value( ). lookup( ind ); 
        return 0u;
      }
   | FORMNAME : str 
      { 
         if( currentproof. has_value( ))
            return currentproof. value( ). lookup( str ); 
         return 0u; 
      }
   | FORMNAME : str LBRACKET INTEGER : offset RBRACKET 
      {
         if( currentproof. has_value( ))
         {
            auto& prf = currentproof. value( ); 
               // Not const, because we could log errors in prf. 
            return prf. move( prf. lookup( str ), offset );
         } 
         return 0u;
      }
;

EigenNames
   => LBRACE RBRACE 
          { return std::vector< std::string > ( ); } 
   | LBRACE QuotedStringSeq : seq RBRACE 
          { return std::move( seq ); } 
;

QuotedStringSeq => 
   QuotedStringSeq : seq COMMA QUOTEDSTRING : str
      { seq. push_back( str ); return std::move( seq ); } 
   | QUOTEDSTRING : str
      { std::vector< std::string > seq; seq. push_back( str ); return seq; } 
;

%end
 
