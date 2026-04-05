
#include "saturation.h"
#include "outermost.h"

#include "logic/cmp.h"
#include "logic/replacements.h"
#include "outermost.h"

void calc::saturation::clause::print( std::ostream& out ) const
{
   out << '#' << nr; 
   if( seqind. has_value( ))
      out << ", initial(" << seqind. value( ) << ") ";
   out << " : ";
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

   // Default is to add lit / tttt:

   return littype( lit, truthset::tttt ); 
}


void calc::saturation::direct( littype& lit )
{
   if( lit. fm. body. sel( ) == logic::op_equals )
   {
      // An equality cannot be error:

      lit. lab &= truthset::fftt;
 
      // We compare the terms with KBO:

      auto eq = lit. fm. body. view_binary( );
      auto c = kbo( eq. sub1( ), eq. sub2( ));

      // Check if equality must be swapped.
      // It's an equivalence, so that the truth set and the variables 
      // do not matter:

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
         lit. fm. body = logic::term( logic::op_true );

         if( lit. lab. disjointwith( truthset::tttt ))
         {
            lit. lab = truthset::empty; 
               // We are a contraction, even if we have variables. 
         }
         else
         {
            if( lit. fm. vars. size( ) == 0 )
               lit. lab = truthset::all; 
         }
      }
   }
}


void calc::saturation::normalize( clause& cls )
{
   for( auto& lit : cls. disj )
      direct( lit );

   cls. disj. merge_equiv< cheapequiv > ( ); 
   cls. disj. remove_nevertrue( ); 
}


bool 
calc::saturation::cheapequiv( const exists< logic::term > & lit1,
                              const exists< logic::term > & lit2 ) 
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


calc::saturation::resolver::resolver( const littype& from )
   : fld_used(0) 
{
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
      auto newlab = ( from. value( ). lab ) & lit. lab;

      if( !lit. lab. subsetof( newlab )) 
      {
         if( cheapequiv( from. value( ). fm, lit. fm ))
         { 
            ++ fld_used; 
            lit. lab = newlab; 
            return lit;
         }
      }
   }
   return lit;
}

calc::saturation::demodulator::demodulator( const littype& lit )
{
   if( lit. lab. subsetof( truthset::tttt ) &&
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
      throw std::logic_error( "demodulator: there is no equation" );

   lit. fm = outermost( rewr. value( ), std::move( lit. fm ), 0 ); 
   return lit; 
}

void 
calc::saturation::initial( dnf< logic::term > disj, size_t index )
{
   notnormalized. push_back( clause( nrgenerated ++, index ));
   for( const auto& d : disj )
      notnormalized. back( ). disj. insert( makeliteral(d));
}


namespace calc
{
   namespace
   {

      bool simplify( const saturation::clause& from, 
                     saturation::clause& into )
      {
         return  
            simplify< exists< logic::term >, 
                      saturation:: cheapequiv,
                      saturation:: resolver> ( from. disj, into. disj ) ||
            simplify< exists<logic::term>, 
                      saturation::cheapequiv, 
                      saturation::demodulator> ( from. disj, into. disj );
      }


      bool subsumes( const saturation::clause& from, 
                     const saturation::clause& into )
      {
         return subsumes< exists< logic::term >, 
                          saturation::cheapequiv > 
              ( from. disj, from. disj. end( ), 
                into. disj, into. disj. end( ));
      }
   }
}


auto calc::saturation::pick( )
-> std::list< clause > :: iterator 
{
   auto p = unchecked. begin( );
   auto picked = p ++;
   while( p != unchecked. end( )) 
   {
      if( p -> disj. size( ) < picked -> disj. size( ))
         picked = p;

      ++ p;
   }
 
   return picked; 
}


void calc::saturation::saturate( )
{
   std::cout << "Starting saturation process:\n";

norm: 
   if( notnormalized. size( ))
   {
      for( auto& cl : notnormalized )
         normalize( cl );

      unchecked. splice( unchecked. end( ), notnormalized ); 
   }

select:
   if( unchecked. size( ) == 0 )
      return;

   auto picked = pick( );
   std::cout << "picked " << *picked << "\n";

   for( const auto& cl : checked )
   {
      if( subsumes( cl, *picked ))
      {
         std::cout << "deleting " << *picked << "\n";
         rememberinitial( *picked );
         unchecked. erase( picked );
         goto select;
      }
   }

   {
      auto p = checked. begin( );
      while( p != checked. end( ))
      {
         if( subsumes( *picked, *p ))
         {
            std::cout << "deleting " << *p << "\n";
            rememberinitial( *p ); 
            p = checked. erase(p);
         }
         else
            ++ p;
      }
   }

   for( const auto& cl : checked )
   { 
      if( simplify( cl, *picked ))
      {
         rememberinitial( *picked );
         ( picked -> nr ) = nrgenerated ++ ;  
         std::cout << "created " << *picked << "\n";
         notnormalized. splice( notnormalized. end( ), 
                                unchecked, picked );
         goto norm;
      }
   }

   {
      auto p = checked. begin( );
      while( p != checked. end( ))
      {
         auto p1 = p;
         ++ p1;

         if( simplify( *picked, *p ))
         {
            std::cout << "created " << *p << "\n";
            rememberinitial( *p ); 
            ( picked -> nr ) = nrgenerated ++ ;  
 
            notnormalized. splice( notnormalized. end( ),
                                   checked, p );
         }
         p = p1;
      }
   }

   checked. splice( checked. end( ), unchecked, picked );
   goto norm;
}


void calc::saturation::rememberinitial( clause& cl )
{
   if( cl. seqind. has_value( ))
   {  
      removed_initials. insert( cl. seqind. value( ));
      cl. seqind. reset( );
   }
}

   
void calc::saturation::print( std::ostream& out ) const
{
   out << "Saturation:\n";

   if( notnormalized. size( ))
   {
      out << "Not normalized:\n";
      for( const auto& cl : notnormalized )
         out << "   " << cl << "\n";
   }

   if( unchecked. size( ))
   {
      out << "Unchecked:\n";
      for( const auto& cl : unchecked )
         out << "   " << cl << "\n";
   }

   if( checked. size( ))
   {
      out << "Checked:\n";
      for( const auto& cl : checked )
         out << "   " << cl << "\n";
   }

   if( removed_initials. size( ))
   {
      out << "Removed initials: ";
      for( auto& r : removed_initials )
         out << r << " ";
      out << '\n';
   }
}

auto
calc::make_dnf( const disjunction_map< exists< logic::term >> & disj )
-> dnf< logic::term >
{
   dnf< logic::term > res; 
   for( const auto& lit : disj )
   {
      auto lab = lit. lab;

      // We remove the things that we handled from lab:
  
      if( !lab. subsetof( truthset::tttt ) && lit. fm. vars. size( ))
      {
         throw 
         std::logic_error( "make_dnf: cannot handle existential variables" );
      }
          
      if( truthset( truthset::fftt ). subsetof( lab ))
      {
         res. append( exists( logic::term( logic::op_prop, lit. fm. body )));
         lab &= truthset::eeee;
      }

      if( truthset( truthset::tttt ). subsetof( lab ))
      {
         res. append( lit. fm );
         lab &= truthset::ffee;
      }

      if( truthset( truthset::ffff ). subsetof( lab ))
      {
         res. append( exists( logic::term( logic::op_not, lit. fm. body )));
         lab &= truthset::eett;
      }

      if( truthset( truthset::eeee ). subsetof( lab ))
      {
         res. append( 
            exists( logic::term( logic::op_not, 
                        logic::term( logic::op_prop, lit. fm. body ))));
         lab &= truthset::fftt;
      }  
      
      if( !lab. isempty( ))
      { 
         std::cout << lit << "\n";
         throw std::logic_error( "not fully handled" );
      }
   }

   return res; 
}

