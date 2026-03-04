
#include "flatten.h"

namespace
{

   void 
   print( std::ostream& out, const std::vector< logic::vartype > & ctxt )
   {
      out << "[";  
      for( auto p = ctxt. begin( ); p != ctxt. end( ); ++ p )
      {
         if( p == ctxt. begin( ))
            out << " ";
         else
            out << ", ";
         out << *p;
      }
      out << " ] :   ";
   }


   void appendvars( std::vector< logic::vartype > & ctxt,
                    const logic::term& fm )
   {
      auto quant = fm. view_quant( );
      for( size_t i = 0; i != quant. size( ); ++ i )
         ctxt. push_back( quant. var(i));
   }


   void
   restore( std::vector< logic::vartype > & ctxt, size_t ss )
   {
      while( ctxt. size( ) > ss )
         ctxt. pop_back( ); 
   }

}


logic::term calc::apply( const logic::term& f, polarity pol )
{
   switch( pol )
   {
   case pol_pos:
      return f;
   case pol_neg:
      if( f. sel( ) == logic::op_not )
         return f. view_unary( ). sub( );
      else
         return logic::term( logic::op_not, f );
   }
   std::cout << pol << "\n";
   throw std::logic_error( "cannot apply unknown polarity" );
}



logic::term calc::apply_prop( const logic::term& f, polarity pol )
{
   if( f. sel( ) == logic::op_not )
      return apply_prop( f. view_unary( ). sub( ), pol );

   switch( pol )
   {
   case pol_pos:
      return logic::term( logic::op_prop, f );
   case pol_neg:
      return logic::term( logic::op_not, logic::term( logic::op_prop, f ));
   }
   std::cout << pol << "\n";
   throw std::logic_error( "cannot apply unknown polarity" );
}


bool calc::decomp_cnf( logic::selector op, polarity pol )
{

   if( pol == pol_pos )
   {
      switch( op ) 
      {
      case logic::op_true:
      case logic::op_and: 
      case logic::op_equiv:
      case logic::op_lazy_and:
      case logic::op_forall:
         return true; 
      }
      return false;
   }

   if( pol == pol_neg )
   {
      switch( op )
      {
      case logic::op_false:
      case logic::op_or:
      case logic::op_implies:
      case logic::op_lazy_implies:
      case logic::op_exists:
         return true;
      }
      return false;
   }

   throw std::logic_error( "decomp_cnf : unknown polarity" );
}

bool calc::decomp_dnf( logic::selector op, polarity pol )
{
   if( pol == pol_pos )
   {
      switch( op )
      {
      case logic::op_false:
      case logic::op_error:
      case logic::op_or:
      case logic::op_implies:
      case logic::op_lazy_implies:
      case logic::op_exists:
         return true; 
      }  
      return false;
   }  
 
   if( pol == pol_neg )
   {
      switch( op ) 
      {
      case logic::op_error:
      case logic::op_true:
      case logic::op_and:
      case logic::op_equiv:
      case logic::op_lazy_and:
      case logic::op_forall:
         return true;
      }
      return false; 
   }
 
   throw std::logic_error( "decomp_dnf : unknown polarity" );
}


calc::cnf< logic::term >
calc::flatten( cnf< logic::term > conj )
{
   cnf< logic::term > result; 
   for( auto& c : conj )
   {
      auto ctxt = std::move( c. vars );
      auto ss = ctxt. size( );

      extract( ctxt, pol_pos, c. body, result );

      if( ctxt. size( ) != ss ) 
         throw std::logic_error( "flatten: stack not restored" );
   }

   return result;
}


calc::dnf< logic::term >
calc::flatten( dnf< logic::term > disj ) 
{
   dnf< logic::term > result;
   for( auto& d : disj )
   {
      auto ctxt = std::move( d. vars );
      auto ss = ctxt. size( );

      extract( ctxt, pol_pos, d. body, result );

      if( ctxt. size( ) != ss )
         throw std::logic_error( "flatten: stack not restored" );
   }

   return result;
}

void 
calc::extract( std::vector< logic::vartype > & ctxt,
               polarity pol,
               const logic::term& fm,
               cnf< logic::term > & conj )
{
   // std::cout << "extract-conj " << pol << " :  " << fm << " " << "\n";

   using namespace logic;

   switch( fm. sel( ))
   {
   case op_exact:
   case op_debruijn:
   case op_unchecked:
   case op_equals:
   case op_let:
   case op_apply:
   case op_lambda:
      conj. append( forall( ctxt, apply( fm, pol ) ));
      return;

   case op_false:
   case op_error:
   case op_true:
      // Doing nothing means that the operator is transformed:

      if( decomp_cnf( fm. sel( ), pol ))
         return;  
      else
      {
         conj. append( forall( ctxt, apply( fm, pol ) ));
         return;
      }

   case op_not:
      extract( ctxt, -pol, fm. view_unary( ). sub( ), conj );
      return;

   case op_prop:
      extract_prop( ctxt, pol, fm. view_unary( ). sub( ), conj );
      return;

   case op_and:
   case op_or:
   case op_lazy_and:
      {
         if( decomp_cnf( fm. sel( ), pol ))
         {
            auto bin = fm. view_binary( );
            extract( ctxt, pol, bin. sub1( ), conj );
            extract( ctxt, pol, bin. sub2( ), conj );
         }
         else
            conj. append( forall( ctxt, apply( fm, pol ) ));
         return;
      }

   case op_implies:
   case op_lazy_implies:
      {
         if( decomp_cnf( fm. sel( ), pol ))
         {
            auto bin = fm. view_binary( );
            extract( ctxt, -pol, bin. sub1( ), conj );
            extract( ctxt, pol, bin. sub2( ), conj );
         }
         else
            conj. append( forall( ctxt, apply( fm, pol ) ));
         return;
      }

   case op_equiv:
      {
         // We always interpret as ( A -> B ) && ( B -> A ):

         if( decomp_cnf( fm. sel( ), pol ))
         {
            auto bin = fm. view_binary( ); 
            auto impl1 = term( op_implies, bin. sub1( ), bin. sub2( ));
            auto impl2 = term( op_implies, bin. sub2( ), bin. sub1( ));
            extract( ctxt, pol, impl1, conj );
            extract( ctxt, pol, impl2, conj );
         }
         else
            conj. append( forall( ctxt, apply( fm, pol ) ));  
         return;
      }

   case op_forall:
   case op_exists:
      {
         if( decomp_cnf( fm. sel( ), pol )) 
         {
            auto ss = ctxt. size( );
            appendvars( ctxt, fm );
            extract( ctxt, pol, fm. view_quant( ). body( ), conj );
            restore( ctxt, ss );
         }
         else
            conj. append( forall( ctxt, apply( fm, pol )));
         return;
      }
 
   }

   std::cout << "extract-conj " << pol << " :  " << fm. sel( ) << "\n";
   throw std::logic_error( "operator not implemented" );
}


void
calc::extract( std::vector< logic::vartype > & ctxt, 
               polarity pol,
               const logic::term& fm,
               dnf< logic::term > & disj )
{
   // std::cout << "extract-disj " << pol << " :  " << fm << " " << "\n";

   using namespace logic;

   switch( fm. sel( ))
   {
   case op_exact:
   case op_debruijn:
   case op_unchecked:
   case op_equals:
   case op_let:
   case op_apply:
   case op_lambda:
      disj. append( exists( ctxt, apply( fm, pol ) ));
      return;

   case op_false:
   case op_error:
   case op_true:
      // Doing nothing means that the operator is transformed:

      if( decomp_dnf( fm. sel( ), pol ))
         return;
      else
      {
         disj. append( exists( ctxt, apply( fm, pol ) ));
         return;
      }

   case op_not:
      extract( ctxt, -pol, fm. view_unary( ). sub( ), disj );
      return;

   case op_prop:
      extract_prop( ctxt, pol, fm. view_unary( ). sub( ), disj );
      return;

   case op_and:
   case op_or:
   case op_lazy_and:
      {
         if( decomp_dnf( fm. sel( ), pol ))
         {
            auto bin = fm. view_binary( );
            extract( ctxt, pol, bin. sub1( ), disj );
            extract( ctxt, pol, bin. sub2( ), disj );
         }
         else
            disj. append( exists( ctxt, apply( fm, pol ) ));
         return;
      }

   case op_implies:
   case op_lazy_implies:
      {
         if( decomp_dnf( fm. sel( ), pol ))
         {
            auto bin = fm. view_binary( );
            extract( ctxt, -pol, bin. sub1( ), disj );
            extract( ctxt, pol, bin. sub2( ), disj );
         }
         else
            disj. append( exists( ctxt, apply( fm, pol ) ));
         return;
      }

   case op_equiv:
      {
         // We always interpret as ( A -> B ) && ( B -> A ):

         if( decomp_dnf( fm. sel( ), pol ))
         {
            auto bin = fm. view_binary( );
            auto impl1 = term( op_implies, bin. sub1( ), bin. sub2( ));
            auto impl2 = term( op_implies, bin. sub2( ), bin. sub1( ));
            extract( ctxt, pol, impl1, disj );
            extract( ctxt, pol, impl2, disj );
         }
         else
            disj. append( exists( ctxt, apply( fm, pol ) )); 
         return;
      }

   case op_forall:
   case op_exists:
      if( decomp_dnf( fm. sel( ), pol ))
      {
         auto ss = ctxt. size( );
         appendvars( ctxt, fm );
         extract( ctxt, pol, fm. view_quant( ). body( ), disj );
         restore( ctxt, ss );
      }
      else
         disj. append( exists( ctxt, apply( fm, pol )));
      return;
   }

   std::cout << "extract-disj " << pol << " :  " << fm. sel( ) << "\n";
   throw std::logic_error( "operator not implemented" );
}


void
calc::extract_prop( std::vector< logic::vartype > & ctxt,
                    polarity pol, const logic::term& fm,
                    conjunction< forall< logic::term >> & conj )
{
   std::cout << "extract-conj-prop " << pol << " :  " << fm << " " << "\n";

   using namespace logic;

   switch( fm. sel( ))
   {
   case op_exact:
   case op_debruijn:
   case op_unchecked:
   case op_let:
   case op_apply:
   case op_lambda:
      conj. append( forall( ctxt, apply_prop( fm, pol ) ));
      return;

   case op_false:
   case op_true:
   case op_prop:
   case op_equals:
      if( pol == pol_neg )
         conj. append( forall( ctxt, logic::term( logic::op_false )));
      return;    

   case op_error:
      if( pol == pol_pos )
         conj. append( forall( ctxt, logic::term( logic::op_false )));
      return;
 
   case op_not:
      extract_prop( ctxt, pol, fm. view_unary( ). sub( ), conj );
      return;

   case op_and:
   case op_or:
   case op_implies:
   case op_equiv:
      if( pol == pol_pos )
      {
         auto bin = fm. view_binary( );
         extract_prop( ctxt, pol, bin. sub1( ), conj );
         extract_prop( ctxt, pol, bin. sub2( ), conj );
      }
      else
         conj. append( forall( ctxt, apply_prop( fm, pol ) ));
      return;

   case op_lazy_and:
   case op_lazy_implies:
      if( pol == pol_pos )
      {
         auto bin = fm. view_binary( );
         extract_prop( ctxt, pol, bin. sub1( ), conj );

         conj. append( forall( ctxt, 
                        term( op_implies, bin. sub1( ), 
                              term( op_prop, bin. sub2( ) )) ));
      } 
      else
         conj. append( forall( ctxt, apply_prop( fm, pol ) ));

      return;

   case op_forall:
   case op_exists:
      if( pol == pol_pos )
      {
         auto ss = ctxt. size( );
         appendvars( ctxt, fm );
         extract_prop( ctxt, pol, fm. view_quant( ). body( ), conj );
         restore( ctxt, ss );
      }
      else
         conj. append( forall( ctxt, apply_prop( fm, pol_neg )));
      return;
   }

   std::cout << "extract-conj-prop " << pol << " :  " << fm. sel( ) << "\n";
   throw std::logic_error( "operator not implemented" );
}


void
calc::extract_prop( std::vector< logic::vartype > & ctxt,
                    polarity pol, const logic::term& fm,
                    dnf< logic::term > & disj )
{
   // std::cout << "extract-disj-prop " << pol << " :  " << fm << " " << "\n";

   using namespace logic;

   switch( fm. sel( ))
   {
   case op_exact:
   case op_debruijn:
   case op_unchecked:
   case op_let:
   case op_apply:
   case op_lambda:
      disj. append( exists( ctxt, apply_prop( fm, pol ) ));
      return;

   case op_false:
   case op_true:
   case op_prop:
   case op_equals:
      if( pol == pol_pos )
         disj. append( exists( ctxt, logic::term( logic::op_true )));
      return;

   case op_error:
      if( pol == pol_neg )
         disj. append( exists( ctxt, logic::term( logic::op_true )));
      return;

   case op_not:
      extract_prop( ctxt, pol, fm. view_unary( ). sub( ), disj );
      return;

   case op_and:
   case op_or:
   case op_implies:
   case op_equiv:
      if( pol == pol_pos )
         disj. append( exists( ctxt, apply_prop( fm, pol ) ));
      else 
      {
         auto bin = fm. view_binary( ); 
         extract_prop( ctxt, pol, bin. sub1( ), disj );
         extract_prop( ctxt, pol, bin. sub2( ), disj );
      }
      return;

   case op_lazy_and:
   case op_lazy_implies:
      if( pol == pol_neg )
      {
         auto bin = fm. view_binary( );
         extract_prop( ctxt, pol, bin. sub1( ), disj );

         disj. append( exists( ctxt, 
            term( op_not, 
               term( op_implies, bin. sub1( ),
                  term( op_prop, bin. sub2( ) )))) );
      }
      else
         disj. append( exists( ctxt, apply_prop( fm, pol ) ));
      return;

   case op_forall:
   case op_exists:
      {
         if( pol == pol_pos )
            disj. append( exists( ctxt, apply_prop( fm, pol ) ));
         else
         {
            size_t ss = ctxt. size( ); 
            appendvars( ctxt, fm );
            extract_prop( ctxt, pol, fm. view_quant( ). body( ), disj );
            restore( ctxt, ss );
         }
         return;
      }

   }

   std::cout << "extract-disj-prop " << pol << " :  " << fm. sel( ) << "\n";
   throw std::logic_error( "operator not implemented" );
}


