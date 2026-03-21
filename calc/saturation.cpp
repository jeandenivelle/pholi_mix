
#include "saturation.h"
#include "outermost.h"

#include "logic/cmp.h"
#include "logic/replacements.h"

namespace calc
{
   namespace
   {
      void insert( saturation::clause& cl, const enf< logic::term > & lit )
      {
   
         // If there are variables, we just insert lit:
   
         if( lit. vars. size( ) != 0 )
         {
            cl. append( lit, truthset::tttt );
            return;
         }

         // There are no variables.

         if( lit. body. sel( ) == logic::op_prop )
         {
            auto un = lit. body. view_unary( );
            cl. append( exists( un. sub( )), truthset::fftt );
            return; 
         }

         if( lit. body. sel( ) == logic::op_not )
         {
            auto un = lit. body. view_unary( );
            if( un. sub( ). sel( ) == logic::op_prop )
            {
               auto un2 = un. sub( ). view_unary( );
               cl. append( exists( un2. sub( )), truthset::eeee ); 
            }
            else
            {
               cl. append( exists( un. sub( )), truthset::ffff );
               return;
            } 

         }

         cl. append( lit, truthset::tttt ); 
         return;
      }
   }
}


void calc::saturation::insert( dnf< logic::term > disj, size_t ind )
{
   clause cl;
   for( const auto& d : disj )
      calc::insert( cl, d );

   std::cout << "YOU FORGOT THE LIFTING\n";
   raw. push_back( std::pair( std::move(cl), ind ));
}

void 
calc::saturation::direct( 
         std::pair< exists< logic::term >, truthset > & lit )
{
   if( lit. first. body. sel( ) == logic::op_equals )
   {
      // An equality cannot be error:

      lit. second &= truthset::fftt;
 
      // We compare the terms:

      auto eq = lit. first. body. view_binary( );
      auto c = kbo( eq. sub1( ), eq. sub2( ));

      // Check if equality must be swapped.
      // It's an equivalence, so that the truth set does not 
      // matter:

      if( is_lt(c))
      {
         logic::term s1 = eq. extr_sub1( );
         logic::term s2 = eq. extr_sub2( ); 
            
         eq. update_sub1( std::move( s2 ));
         eq. update_sub2( std::move( s1 )); 
         return;
      }

      if( is_eq(c))
      {
         if( truthset( truthset::tttt ). implies( lit. second ))
         {
            lit. first. body = logic::term( logic::op_true );

            // A non-empty existential quantifier is not a tautology.

            if( lit. first. vars. size( ) == 0 )
               lit. second = truthset::all;
            return; 
         }       
         else
         {
            lit. second = truthset::empty;
               // This will result in removal.
         }
      }
   }
}

#if 0

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

#endif

void calc::saturation::print( std::ostream& out ) const
{
   out << "Saturation:\n";
   if( raw. size( ))
   {
      for( const auto& r : raw )
         out << r. second  << " : " << r. first << "\n";
   }

}

