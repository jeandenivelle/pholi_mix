
#include "atp.h"
#include "outermost.h"

#include "logic/cmp.h"
#include "logic/replacements.h"


std::pair< calc::prefix, const logic::term* > 
calc::atp::decompose( const logic::term& tm )
{
   if( tm. sel( ) == logic::op_prop )
   {
      return std::pair( prefix::F( ) | prefix::T( ), 
                        & tm. view_unary( ). sub( ) );   
   }

   if( tm. sel( ) == logic::op_not )
   {
      const auto& sub = tm. view_unary( ). sub( );
      if( sub. sel( ) == logic::op_prop )
         return std::pair( prefix::E( ), & sub. view_unary( ). sub( ));
      else
         return std::pair( prefix::F( ), & sub );
   }

   return std::pair( prefix::T( ), & tm );
}


bool
calc::atp::inconflict( const logic::term& tm1, const logic::term& tm2 )
{
   auto dec1 = decompose( tm1 );
   auto dec2 = decompose( tm2 );

   if( ( dec1. first & dec2. first ). isempty( ))
   {
      if( logic::equal( *dec1. second, *dec2. second ))
         return true; 
   }

   return false;
}


bool
calc::atp::subsumes( const logic::term& tm1, const logic::term& tm2 )
{
   auto dec1 = decompose( tm1 );
   auto dec2 = decompose( tm2 );

   if( dec1. first. subset( dec2. first ))
   {
      if( logic::equal( *dec1. second, *dec2. second ))
         return true;
   }

   return false;
}


bool
calc::atp::subsumes( const literal& lit1, const literal& lit2 )
{
   if( lit1. vars. size( ) != lit2. vars. size( ))
      return false;

   for( size_t i = 0; i != lit1. vars. size( ); ++ i )
   {
      if( !equal( lit1. vars[i]. tp, lit2. vars[i]. tp ))
         return false;
   }

   return subsumes( lit1. body, lit2. body );
}


bool calc::atp::trivially_true( const logic::term& tm )
{
   // Truth constant:

   if( tm. sel( ) == logic::op_true )
      return true;

   // equality t == t:

   if( tm. sel( ) == logic::op_equals )
   {
      auto bin = tm. view_binary( );
      if( equal( bin. sub1( ), bin. sub2( )))
         return true;
   }

   // # ( t1 == t2 ), # # t, # FALSE, # TRUE:

   if( tm. sel( ) == logic::op_prop )
   {
      const auto& sub = tm. view_unary( ). sub( ); 
      
      if( sub. sel( ) == logic::op_equals ||
          sub. sel( ) == logic::op_prop ||
          sub. sel( ) == logic::op_false ||
          sub. sel( ) == logic::op_true )
      {
         return true;
      }
   }

   return false;
}

bool calc::atp::istruthconstant( const clause& cls )
{
   if( cls. size( ) != 1 )
      return false;

   auto p = cls. begin( );
   return p -> vars. size( ) == 0 && p -> body. sel( ) == logic::op_true;
}

void calc::atp::maketruthconstant( clause& cls )
{
   if( cls. size( ) == 0 )
      cls. append( exists( logic::term( logic::op_true )));
   else
   {
      while( cls. size( ) > 1 )
         cls. remove_last( );

      cls. begin( ) -> body = logic::term( logic::op_true );
      cls. begin( ) -> vars. clear( );
   }
}

void calc::atp::simplify( clause& cls )
{
   auto p1 = cls. begin( );
   auto p2 = cls. begin( );
      // We copy from p1 to p2:

   while( p1 != cls. end( ))
   {
      // If *p1 is trivially true, we replace the clause by 
      // { TRUE }:

      if( p1 -> vars. size( ) == 0 && trivially_true( p1 -> body ))
      {
         maketruthconstant( cls );
         return;
      }

      if( p1 -> body. sel( ) == logic::op_not )
      {
         // We allow variables, because exists( x1, ... xn; FALSE )
         // is still FALSE.

         const auto& sub = p1 -> body. view_unary( ). sub( );
         if( trivially_true( sub ))
            goto skip;
      }

      // Check if a later literal subsumes:

      for( auto s = p1 + 1; s != cls. end( ); ++ s )
      {
         if( subsumes( *p1, *s ))
            goto skip;
      }

      // Check if an earlier literal subsumes:
      // (This approach has problem that in case of equivalent literals,
      //  the latter is taken.)

      for( auto s = cls. begin( ); s != p2; ++ s )
      {
         if( subsumes( *p1, *s ))
            goto skip;
      }

      // Check if *p1 is an equality that needs to be flipped.
      // We also flip inside an exists, even when it is useless:

      if( p1 -> body. sel( ) == logic::op_equals )
      {
         auto bin = p1 -> body. view_binary( );
         if( is_lt( logic::kbo( bin. sub1( ), bin. sub2( ))) )
         {
            p1 -> body = logic::term( logic::op_equals,
                                      bin. sub2( ), bin. sub1( ));
         } 
      }

      if( p1 != p2 )
         *p2 = std::move( *p1 ); 
      ++ p2;

   skip:
      ++ p1; 
   }

   while( p2 != cls. end( ))
      cls. remove_last( );
}


bool 
calc::atp::subsumes( const literal& lit, const clause& cls,
                     clause::const_iterator skip )
{
   for( auto q = cls. begin( ); q != cls. end( ); ++ q )
   {
      if( q != skip && subsumes( lit, *q ))
         return true;
   } 
   
   return false;
}

bool 
calc::atp::subsumes( const clause& cls1, clause::const_iterator skip1,
                     const clause& cls2, clause::const_iterator skip2 )
{
   for( auto p1 = cls1. begin( ); p1 != cls1. end( ); ++ p1 )
   {
      if( p1 != skip1 && !subsumes( *p1, cls2, skip2 ))
         return false;
   }
   return true; 
}

bool 
calc::atp::resolve( const clause& from, clause& into )
{
   for( auto p = from. begin( ); p != from. end( ); ++ p ) 
   {
      for( auto q = into. begin( ); q != into. end( ); ++ q )
      { 
         if( p -> vars. size( ) == 0 && 
             q -> vars. size( ) == 0 &&
             inconflict( p -> body, q -> body ))
         {
            if( subsumes( from, p, into, q )) 
            {
               into. erase( q ); 
               return true; 
            }
         }
      }
   }

   return false;
}


bool 
calc::atp::rewrite( const clause& from, clause& into )
{
   for( auto p = from. begin( ); p != from. end( ); ++ p )
   {
      // exists( V, t1 == t2 ) can be used only when V is empty:

      if( p -> vars. size( ) == 0 && 
          p -> body. sel( ) == logic::op_equals )
      {
         auto bin = p -> body. view_binary( );
         auto rewr = logic::rewriterule( bin. sub1( ), bin. sub2( ));

         for( auto q = into. begin( ); q != into. end( ); ++ q )
         { 
            *q = outermost( rewr, std::move(*q), 0 );
            if( rewr. counter )
            {
               if( subsumes( from, p, into, q ))
                  return true; 
            }
         }
      }
   }

   return false;
}


void calc::atp::simplify( conjunction< clause > & simp )
{
   std::cout << "starting simplification on conjunction of clauses\n";

   for( auto s = simp. begin( ); s != simp. end( ); ++ s )
      simplify( *s );

   std::cout << "after clausewise simplification:\n";
   for( const auto& cl : simp )
      std::cout << "   " << cl << "\n";
   std::cout << "\n";
 
   bool fixedpoint = false;
   while( !fixedpoint )
   {
      fixedpoint = true;

      for( auto from = simp. cbegin( ); from != simp. cend( ); ++ from )
      {
         if( !istruthconstant( *from ))  
         {
            std::cout << "picked: " << *from << "\n";
            for( auto into = simp. begin( ); into != simp. end( ); ++ into )
            {
               if( into != from && !istruthconstant( *into ))
               {
                  if( subsumes( *from, from -> end( ),
                                *into, into -> end( ) ))
                  { 
                     std::cout << "deleting: " << *into << "\n";
                     maketruthconstant( *into );
                     fixedpoint = false;
                  }
                  else
                  {
                     if( resolve( *from, *into ) || rewrite( *from, *into ))
                     {
                        std::cout << "   resolved or rewrote: " << *into << "\n";
                        simplify( *into );  
                        std::cout << "   simplified: " << *into << "\n";
                        fixedpoint = false;
                     }
                  }
               }
            }
         }
      }

   }

   // We remove the clauses that were replaced by { TRUE }:

   auto p1 = simp. begin( );
   auto p2 = simp. cbegin( );
   while( p2 != simp. cend( ))
   {
      if( !istruthconstant( *p2 ))
      {
         if( p1 != p2 )
            *p1 = std::move( *p2 );
         ++ p1; 
      }
      
      ++ p2;       
   }

   while( p1 != simp. end( ))
      simp. remove_last( );
}


