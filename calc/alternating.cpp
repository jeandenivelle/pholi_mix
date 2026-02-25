
#include "alternating.h"

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


calc::kleene 
calc::kleening( logic::selector sel, polarity pol )
{
   using namespace logic;

   if( pol == pol_pos )
   {
      switch( sel )
      {
      case op_false:
      case op_or:
      case op_lazy_or:
         return kleene_or;

      case op_true:
      case op_and:
      case op_lazy_and:
         return kleene_and;

      case op_forall:
         return kleene_forall;
      case op_exists:
         return kleene_exists;
      }
   }

   if( pol == pol_neg )
   {
      switch( sel )
      {
      case op_false:
      case op_or:
      case op_lazy_or:
         return kleene_and;
         
      case op_true:
      case op_and:
      case op_lazy_and:
         return kleene_or;

      case op_forall:
         return kleene_exists;
      case op_exists:
         return kleene_forall;
      }
   }
   throw std::logic_error( "Kleening: operator not implemented" );
}


calc::dnf< logic::term >
calc::flatten( dnf< logic::term > disj ) 
{
   disjunction< exists< logic::term >> result;
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


calc::anf< logic::term >
calc::flatten( anf< logic::term > conj )
{
   anf< logic::term > result; 
   for( auto& all : conj )
   {
      all. body = flatten( std::move( all. body ));
         // This is flatten for disjunction. It is not a recursion!

      if( all. body. size( ) == 1 && all. body. at(0). vars. size( ) == 0 )
      {
         auto vars = std::move( all. vars ); 
         auto ss = vars. size( );

         conjunction< forall< logic::term >> cls;
         extract( vars, pol_pos, all. body. at(0). body, cls );

         if( vars. size( ) != ss )
            throw std::logic_error( "flatten: context not properly restored" );

         std::cout << "tried forall:\n";
         std::cout << cls << "\n\n";

         for( auto& aa : cls )
         {
            dnf< logic::term > disj;
            disj. append( exists( std::move( aa. body )) );

            result. append( forall( 
               std::move( aa. vars ), flatten( std::move( disj ))));
         }
      }
      else
         result. append( std::move( all ));
   }

   return result;
}



void 
calc::extract( std::vector< logic::vartype > & ctxt,
               polarity pol,
               const logic::term& fm,
               conjunction< forall< logic::term >> & conj )
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
   case op_true:
      if( kleening( fm. sel( ), pol ) == kleene_or )
      {
         conj. append( forall( ctxt, term( op_false )));
         return;
      }
      else
         return;

   case op_error:
      return;

   case op_not:
      extract( ctxt, -pol, fm. view_unary( ). sub( ), conj );
      return;

   case op_prop:
      extract_prop( ctxt, pol, fm. view_unary( ). sub( ), conj );
      return;

   case op_and:
   case op_or:
   case op_lazy_and:
   case op_lazy_or:
      {
         if( kleening( fm. sel( ), pol ) == kleene_and )
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
         if( pol == pol_pos )
            conj. append( forall( ctxt, fm ));
         else
         {
            auto bin = fm. view_binary( );
            extract( ctxt, pol_pos, bin. sub1( ), conj );
            extract( ctxt, pol_neg, bin. sub2( ), conj );
         }
         return;
      }

   case op_equiv:
      {
         auto bin = fm. view_binary( ); 
         if( pol == pol_pos )
         {
            auto impl1 = logic::term( op_implies, bin. sub1( ), bin. sub2( ));
            auto impl2 = logic::term( op_implies, bin. sub2( ), bin. sub1( ));
            conj. append( forall( ctxt, impl1 ));
            conj. append( forall( ctxt, impl2 ));
         }
         else
         {
            auto disj1 = logic::term( op_or, 
                            apply( bin. sub1( ), pol_neg ),
                            apply( bin. sub2( ), pol_neg ));

            auto disj2 = logic::term( op_or, bin. sub1( ), bin. sub2( ));
            conj. append( forall( ctxt, disj1 )); 
            conj. append( forall( ctxt, disj2 ));
         }
         return;
      }

   case op_forall:
   case op_exists:
      {
         if( kleening( fm. sel( ), pol ) == kleene_forall ) 
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
   case op_true:
      if( kleening( fm. sel( ), pol ) == kleene_and )
      {
         disj. append( exists( ctxt, term( op_true )));
         return;
      }
      else 
         return;

   case op_error:
      return;

   case op_not:
      extract( ctxt, -pol, fm. view_unary( ). sub( ), disj );
      return;

   case op_prop:
      extract_prop( ctxt, pol, fm. view_unary( ). sub( ), disj );
      return;

   case op_and:
   case op_or:
   case op_lazy_and:
   case op_lazy_or:
      {
         if( kleening( fm. sel( ), pol ) == kleene_or )
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
         if( pol == pol_pos )
         {
            auto bin = fm. view_binary( );
            extract( ctxt, pol_neg, bin. sub1( ), disj );
            extract( ctxt, pol_pos, bin. sub2( ), disj );
         }
         else
            disj. append( exists( ctxt, apply( fm, pol ) ));
         return;
      }

   case op_equiv:
      {
         auto bin = fm. view_binary( );
         if( pol == pol_pos )
         {
            auto conj1 = logic::term( op_and, bin. sub1( ), bin. sub2( ));
            auto conj2 = logic::term( op_and,
                            apply( bin. sub1( ), pol_neg ),
                            apply( bin. sub2( ), pol_neg ));

            disj. append( exists( ctxt, conj1 ));
            disj. append( exists( ctxt, conj2 ));
         }
         else
         {
            auto conj1 = logic::term( op_and, bin. sub1( ), 
                                      apply( bin. sub2( ), pol_neg ));
            auto conj2 = logic::term( op_and, bin. sub2( ), 
                                      apply( bin. sub1( ), pol_neg ));
            disj. append( exists( ctxt, conj1 ));
            disj. append( exists( ctxt, conj2 ));
         }

         return;
      }

   case op_forall:
   case op_exists:
      if( kleening( fm. sel( ), pol ) == kleene_exists )
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
   case op_lazy_or:
   case op_lazy_implies:
      if( pol == pol_pos )
      {
         auto bin = fm. view_binary( );
         extract_prop( ctxt, pol, bin. sub1( ), conj );
         auto op = op_implies;
         if( fm. sel( ) == op_lazy_or )
            op = op_or;

         conj. append( forall( ctxt, term( op, bin. sub1( ), 
                                     term( op_prop, bin. sub2( ) )) ));
      } 
      else
         conj. append( forall( ctxt, apply_prop( fm, pol ) ));
            // Can think of nothing better.
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
   case op_lazy_or:
   case op_lazy_implies:
      if( pol == pol_pos )
         disj. append( exists( ctxt, apply_prop( fm, pol ) ));
      else
      {
         auto bin = fm. view_binary( );
         extract_prop( ctxt, pol, bin. sub1( ), disj );
         pol = pol_pos;
         if( fm. sel( ) == op_lazy_or )
            pol = pol_neg; 

         disj. append( exists( ctxt, 
            term( op_and, apply( bin. sub1( ), pol ),
                          apply_prop( bin. sub2( ), pol_neg )) ));
      }
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




#if 0
   throw std::logic_error( "rank: not in ANF" );
}
#endif


