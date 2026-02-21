
#include "distribute.h"
#include "logic/replacements.h"
#include "logic/outermost.h"
#include "util.h"

namespace
{
   // or > forall > and > (everything else):

   bool isbetter( const logic::term& good, const logic::term& bad )
   {
      switch( good. sel( ))
      {
      case logic::op_kleene_or:
         return bad. sel( ) != logic::op_kleene_or;  

      case logic::op_kleene_forall:
         return bad. sel( ) != logic::op_kleene_or &&
                bad. sel( ) != logic::op_kleene_forall;

      case logic::op_kleene_and:
         return bad. sel( ) != logic::op_kleene_or &&
                bad. sel( ) != logic::op_kleene_forall &&
                bad. sel( ) != logic::op_kleene_and; 

      default:
         return false; 
      }
   }
}

void 
calc::disj_stack::markedform::print( std::ostream& out ) const
{
   out << "   " << form << "      (level = " << level << ")    ";
   if( active )
      out << "(active)";
   else
      out << "(inactive)";
}

void 
calc::disj_stack::restore( size_t dd )
{
   while( lst. size( ) > dd )
      lst. pop_back( );
}

calc::disj_stack::iterator
calc::disj_stack::findbest( bool pref( const logic::term& ,
                                       const logic::term& ))
{
   auto best = lst. end( );
   for( auto p = lst. begin( ); p != lst. end( ); ++ p )
   {
      if( p -> active )
      {
         if( best == lst. end( ) || pref( p -> form, best -> form ))
         {
            best = p; 
         } 
      }
   }
   return best;
}

void
calc::disj_stack::print( std::ostream& out ) const
{
   out << "Disjunction Stack:\n";
   for( const auto& p : lst )
      out << "   " << p << "\n";
   out << "\n"; 
}

void
calc::distr( logic::context& ctxt, disj_stack& disj,
             std::vector< logic::term > & conj )
{
   if constexpr ( false )
   {
      std::cout << "------------------------------\n";
      std::cout << "distr:\n";
      std::cout << ctxt << "\n";
      std::cout << disj << "\n";
   }

   auto best = disj. findbest( isbetter );
   if( best == disj. end( ))
   {
      conj. push_back( logic::term( logic::op_kleene_or,
                                    std::initializer_list< logic::term > ( )));

   }

   if constexpr ( false )
      std::cout << "best = " << ( best -> form ) << "\n";
   
   if( best -> form. sel( ) == logic::op_kleene_forall )
   {
      auto all = best -> form. view_quant( ); 
      size_t ss = ctxt. size( );
      size_t dd = disj. size( );
 
      for( size_t i = 0; i != all. size( ); ++ i )
         ctxt. append( all. var(i). pref, all. var(i). tp );

      ( best -> active ) = false;
      disj. append( all. body( ), ctxt. size( ));
      distr( ctxt, disj, conj );
      ctxt. restore( ss );
      disj. restore( dd );
      ( best -> active ) = true;
      return;
   }

   if( best -> form. sel( ) == logic::op_kleene_or )
   {
      auto kl = best -> form. view_kleene( );
      size_t dd = disj. size( ); 
      for( size_t i = 0; i != kl. size( ); ++ i )
         disj. append( kl. sub(i), ctxt. size( ));

      ( best -> active ) = false;
      distr( ctxt, disj, conj );
      disj. restore( dd );
      ( best -> active ) = true;
      return;
   }

   if( best -> form. sel( ) == logic::op_kleene_and )
   {
      auto kl = best -> form. view_kleene( );
      size_t dd = disj. size( ); 
      ( best -> active ) = false;
      for( size_t i = 0; i != kl. size( ); ++ i )
      {
         disj. append( kl. sub(i), ctxt. size( ));
         distr( ctxt, disj, conj );
         disj. restore( dd );
      }
      ( best -> active ) = true;  
      return; 
   }

   logic::term clause = logic::term( logic::op_kleene_or,
                                     std::initializer_list< logic::term > ( ));
   auto cl = clause. view_kleene( );
   for( const auto& d : disj ) 
   {
      if( d. active )
      {
         if( ctxt. size( ) == d. level )
         {
            cl. push_back( d. form ); 
         }
         else
         {
            logic::lifter lft( ctxt. size( ) - d. level );
            bool c = false;
            cl. push_back( outermost( lft, d. form, 0, c ));
         }
      }
   }
   conj. push_back( quantify( logic::op_kleene_forall, ctxt, clause ));
}

