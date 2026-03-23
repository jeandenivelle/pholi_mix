
#include "saturation.h"
#include "outermost.h"

#include "logic/cmp.h"
#include "logic/replacements.h"
#include "outermost.h"

bool calc::exists_equal_to::operator( ) (
       const exists< logic::term > & lit1,
          const exists< logic::term > & lit2  ) const
{
   if( lit1. vars. size( ) != lit2. vars. size( )) 
      return false;

   for( size_t i = 0; i != lit1. vars. size( ); ++ i )
      if( !equal( lit1. vars[i]. tp, lit2.vars[i]. tp ))
         return false;

    return equal( lit1. body, lit2. body );
}

void calc::saturation::clause::print( std::ostream& out ) const
{
   out << nr;
   if( seqind. has_value( ))
      out << ", initial(" << seqind. value( ) << ")";
   out << " :\n";
   out << cl; 
}

calc::saturation::littype
calc::saturation::makeliteral( const exists< logic::term > & lit )
{
   if( lit. vars. size( ) == 0 )
   {
      if( lit. body. sel( ) == logic::op_prop )
      {
         auto un = lit. body. view_unary( );
         return littype( exists( un. sub( )), truthset::fftt );
      }

      if( lit. body. sel( ) == logic::op_not )
      {
         auto un = lit. body. view_unary( );
         if( un. sub( ). sel( ) == logic::op_prop )
         {
            auto un2 = un. sub( ). view_unary( );
            return littype( exists( un2. sub( )), truthset::eeee ); 
         }
         else
            return littype( exists( un. sub( )), truthset::ffff );
      }
   }

   return littype( lit, truthset::tttt ); 
}


void 
calc::saturation::direct( littype & lit )
{
   if( lit. fm. body. sel( ) == logic::op_equals )
   {
      // An equality cannot be error:

      lit. lab &= truthset::fftt;
 
      // We compare the terms:

      auto eq = lit. fm. body. view_binary( );
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
         if( truthset( truthset::tttt ). implies( lit. lab ))
         {
            lit. fm. body = logic::term( logic::op_true );

            // A non-empty existential quantifier cannot be a tautology.

            if( lit. fm. vars. size( ) == 0 )
               lit. lab = truthset::all; 
            return; 
         }       
         else
            lit. lab = truthset::empty;
      }
   }
}


calc::saturation::demodulator::demodulator( 
   const littype & lit )
{
   std::cout << "constructing demodulator from " << lit << "\n";
   if( lit. lab. implies( truthset::tttt ) &&
       lit. fm. vars. size( ) == 0 &&
       lit. fm. body. sel( ) == logic::op_equals )
   {
      std::cout << "going on\n";
      auto eq = lit. fm. body. view_binary( );
      rewr. emplace( eq. sub1( ), eq. sub2( )); 
   }
}

auto
calc::saturation::demodulator::operator( ) ( littype lit )
-> littype 
{ 
   lit = outermost( rewr. value( ), std::move( lit. fm ), 0 ); 
   return lit; 
}

void 
calc::saturation::initial( dnf< logic::term > disj, 
                           size_t index, size_t liftdist )
{
   clauses. push_back( clause( notcreated ++ , index ));
   for( const auto& d : disj )
      clauses. back( ). cl. insert( makeliteral(d) );

   std::cout << "YOU FORGOT THE LIFTING\n";
}



#if 0
{
   for( auto p = from. begin( ); p != from. end( ); ++ p )
   {
      if( p -> first. vars. size( ) == 0 &&
          p -> second == truthset::tttt &&
          p -> first. body. sel( ) == logic::op_equals )
      {
         auto eq = p -> first. body. view_binary( );
         logic::rewriterule rewr( eq. sub1( ), eq. sub2( ))
         {
            for( auto q = into. begin( ); q != into. end( ); ++ q )
            {
               auto lit = rewr( *q, 0 );
               if( rewr. used && subsumes( from, p, into, q ))
               { 
                  *q = std::move(lit);
                  return true;
               }
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


void calc::saturation::saturate( )
{
   std::cout << "starting simplification on conjunction of clauses\n";
restart: 
   if( notsimplified < notcreated )
   {
      for( auto& cl : clauses )
      {
         if( cl. nr >= notsimplified )
            normalize( cl. cl );
      }

      notsimplified = notcreated; 
   }

   if( notsubsumed < notcreated )
   {

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
   out << "   notsaturated =  " << notsaturated << "\n";
   out << "   notsubsumed =   " << notsubsumed << "\n";
   out << "   notnormalized = " << notnormalized << "\n";
   out << "   notcreated =    " << notcreated << "\n";

   for( const auto& cl : clauses )
      out << cl << "\n";
}

