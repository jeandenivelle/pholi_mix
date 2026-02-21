
// I put all the printing functions in this file, so that the
// treedefs.rec file will be not too big.

#include "type.h"
#include "term.h"
#include "belief.h"

void logic::type::print( std::ostream& out ) const
{
   switch( sel( ))
   {
   case type_form:
      out << "Form";
      break;

   case type_obj:
      out << "Obj";
      break;

   case type_struct:
      out << view_struct( ). def( );
      break;

   case type_unchecked:
      out << '\'' << view_unchecked( ). id( ) << '\'';
      break;

   case type_func:
      {
         auto f = view_func( );
         out << f. result( ) << '(';
         for( size_t i = 0; i != f. size( ); ++ i )
         {
            if(i) out << ',';
            out << f. arg(i);
         }
         out << ')';
      }
      break;

   default:
      out << "unknown selector in type::print: " << sel( ) << "\n";
      throw std::logic_error( "reached the unreachable" );
   }
}


void logic::term::print( std::ostream& out ) const 
{
   switch( sel( ) )
   {

   case op_exact:
      {
         auto e = view_exact( );
         out << e. ex( );
      }
      return;

   case op_debruijn:
      { 
         auto p = view_debruijn( );
         out << '#' << p. index( ); 
      }
      return;

   case op_unchecked:
      {
         auto p = view_unchecked( );
         out << p. id( );  
      }
      return;

   case op_false:
   case op_error:
   case op_true:
      out << sel( );
      return;

   case op_not:
   case op_prop:
      {
         out << sel( ) << "( ";
         auto p = view_unary( );
         out << p. sub( ) << " )";
      }
      return;

   case op_and:
   case op_or:
   case op_implies:
   case op_equiv:
   case op_lazy_and:
   case op_lazy_implies:
   case op_meta_implies:
   case op_equals:
      {
         auto p = view_binary( );
         out << sel( ) << "( ";
         out << p. sub1( ) << ", " << p. sub2( ) << " )";
      }
      return;

   case op_forall:
   case op_exists:
      {
         auto p = view_quant( );
         out << sel( ) << "(";
         for( size_t i = 0; i != p. size( ); ++ i )
         {
            if(i) 
               out << ", ";
            else
               out << " ";
            out << p. var(i);
         }
         out << " ) : " << p. body( );
      }
      return;

   case op_let:
      {
         auto let = view_let( ); 
         out << "let( " << let. var( ) << " := " << let. val( ); 
         out << " in " << let. body( );
         out << " )"; 
      }
      return;

   case op_apply:
      {
         auto ap = view_apply( );
         out << "{" << ap. func( ) << "}(";
         for( size_t i = 0; i != ap. size( ); ++ i )
         {
            if(i)
               out << ", ";
            else
               out << " ";
            out << ap. arg(i);
         }
         out << " )";
      }
      return;

   case op_lambda:
      {
         auto p = view_lambda( );
         out << sel( ) << '(';
         for( size_t i = 0; i != p. size( ); ++ i )
         {
            if(i)
               out << ", ";
            else
               out << " ";
            out << p. var(i);
         }
         out << " ) : ";
         out << p. body( );
      }
      return;

   case op_named:
      {
         auto p = view_named( );
         out << "( " << p. lab( ) << " / " << p. sub( ) << " )";
      }
      return;

   default:
      std::cout << sel( ) << "\n";
      throw std::logic_error( "term::print( ) : unknown selector" );
   }
}


void logic::belief::print( std::ostream& out ) const
{
   switch( sel( ))
   {
   case bel_empty:
      out << "empty belief (should not be used)";
      return;

   case bel_struct:
      out << ident( ) << " := " << view_struct( ). def( );
      return;

   case bel_symbol:
      out << "symbol " << ident( ) << " : " << view_symbol( ). tp( );
      return;

   case bel_def:
      {
         auto d = view_def( );
         out << ident( ) << " := " << d. val( );
         out << " : " << d. tp( );
      }
      return;

   case bel_axiom:
   case bel_thm:
      if( sel( ) == bel_axiom )
         out << "axiom ";
      if( sel( ) == bel_thm )
         out << "theorem ";

      out << ident( ) << " : " << view_form( ). fm( );
      return;

   case bel_fld:
      {
         auto f = view_field( );
         out << ident( ) << " : field at offset " << f. offset( );
         out << " in " << f. sdef( );
      }
      return;

   case bel_constr:
      {
         auto c = view_constr( );
         out << ident( ) << " : " << "constructor of " << c. tp( );
      }
      return;

   }
   out << "belief has selector: " << sel( ) << "\n";
   throw std::runtime_error( "wrong selector for belief" );
}



