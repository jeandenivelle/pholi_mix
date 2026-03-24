
#include "saturation.h"
#include "outermost.h"

#include "logic/cmp.h"
#include "logic/replacements.h"
#include "outermost.h"

void calc::saturation::clause::print( std::ostream& out ) const
{
   out << nr;
   if( seqind. has_value( ))
      out << ", initial(" << seqind. value( ) << ")";
   out << " :\n";
   out << disj; 
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

namespace
{
   // A cheap equivalence relation.

   bool 
   cheapequiv( const calc::exists< logic::term > & lit1,
               const calc::exists< logic::term > & lit2  ) 
   {
      if( lit1. vars. size( ) != lit2. vars. size( )) 
         return false;

      for( size_t i = 0; i != lit1. vars. size( ); ++ i )
      {
         if( !equal( lit1. vars[i]. tp, lit2.vars[i]. tp ))
            return false;
      }
      return equal( lit1. body, lit2. body );
   }
}

calc::saturation::resolver::resolver( const littype& from )
   : fld_used(0) 
{
   std::cout << "setting resolver from " << from << "\n";
   if( from. fm. vars. size( ) == 0 &&
       from. fm. body. sel( ) != logic::op_equals &&
       !from. lab. istrivial( ))
   {
      ( this -> from ) = from;
   }
}

auto
calc::saturation::resolver::operator( ) ( littype lit )
-> littype
{
   if( !from. has_value( )) 
      throw std::logic_error( "resolver: there is no from" );
 
   if( lit. fm. vars. size( ) == 0 )
   {
      auto lab = ( from. value( ). lab ) & lit. lab;

      if( !lit. lab. implies( lab )) 
      {
         if( cheapequiv( from. value( ). fm, lit. fm ))
         { 
            ++ fld_used; 
            return truthform( lit. fm, lab );
         }
      }
   }
   return lit;
}

calc::saturation::demodulator::demodulator( const littype& lit )
{
   if( lit. lab. implies( truthset::tttt ) &&
       lit. fm. vars. size( ) == 0 &&
       lit. fm. body. sel( ) == logic::op_equals )
   {
      auto eq = lit. fm. body. view_binary( );
      rewr. emplace( eq. sub1( ), eq. sub2( )); 
   }
}

auto
calc::saturation::demodulator::operator( ) ( littype lit )
-> littype 
{
   if( !rewr. has_value( ))
      throw std::logic_error( "demodulator: there is no from" );

   return outermost( rewr. value( ), std::move( lit. fm ), 0 ); 
}

void 
calc::saturation::initial( dnf< logic::term > disj, size_t index )
{
   clauses. push_back( clause( notcreated ++ , index ));
   for( const auto& d : disj )
      clauses. back( ). disj. insert( makeliteral(d));
}

void calc::saturation::normalize( clause& cls )
{
   // First direct equalities.

   for( auto& lit : cls. disj )
      direct( lit );

   for( auto from = cls. disj. begin( ); from != cls. disj. end( ); ++ from )
   {
      auto into = cls. disj. begin( ); 
      while( into != from )
      {
         if( cheapequiv( from -> fm, into -> fm ))
         {
            from -> lab |= into -> lab;
            into= cls. disj. erase( into );
         }
         else
            ++ into;
      }
   } 

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

#endif

void calc::saturation::saturate( )
{
   std::cout << "starting saturation\n";

restart: 
   if( notnormalized < notcreated )
   {
      for( auto& cl : clauses )
      {
         if( cl. nr >= notnormalized )
            normalize( cl );
      }

      notnormalized = notcreated; 
   }

   if( notsubsumed < notnormalized )
   {
      for( auto from = clauses. begin( ); from != clauses. end( ); ++ p )
      {
         if( from -> nr >= notsubsumed && from -> nr < notnormalized )
         {

         }

      }

   }

   notsubsumed = notnormalized;

#if 0
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

#endif
}


bool calc::saturation::simplify( const clause& from, clause& into )
{
   if( calc::simplify<exists<logic::term>, cheapequiv,resolver> ( from. disj, into. disj ) ||
       calc::simplify<exists<logic::term>, cheapequiv,demodulator> ( from. disj, into. disj ))
   {
      into. nr = notcreated ++ ;
      return true;
   }
   else
      return false;   

}

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

