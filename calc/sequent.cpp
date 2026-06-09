
#include "sequent.h"

void calc::sequent::seqform::print( std::ostream& out ) const
{
   if( is_dnf( ))
      out << get_dnf( );

   if( is_unf( ))
      out << get_unf( );

   out << " / " << ctxtsize;
   if( hidden ) out << "      (hidden)";
}


void calc::sequent::seqform::print( pretty_printer& out ) const
{
   if( !hidden )
   {
      if( is_dnf( ))
         out << get_dnf( ); 
      if( is_unf( ))
         out << get_unf( ); 
   }
   else
      out << "   (hidden)";
}

void calc::sequent::append( label lab, cnf< logic::term > c )
{
   for( auto& u : c )
   {
      if( u. vars. size( ) == 0 )
         append( lab, disjunction( { exists( std::move( u. body )) } ));
      else
         stack. push( lab, seqform( std::move(u), ctxt. size( )));
     
      ++ lab;  
   }

}

void calc::sequent::append( label lab, dnf< logic::term > d )
{
   stack. push( lab, seqform( std::move(d), ctxt. size( )));
}


size_t calc::sequent::find( const label& lab ) const
{
   auto s = stack. find( lab );
   if( s != stack. size( ))
   {
      if( stack. at(s). second. hidden )
         return stack. size( );
   }
   return s;
}


void calc::sequent::popdecision( )
{
   if( decisions. empty( ))
      throw std::logic_error( "popdecision( ): there is no decision" );

   if( decisions. back( ). ctxtsize > ctxt. size( ))
      throw std::logic_error( "popdecision( ): context too small" ); 

   ctxt. restore( decisions. back( ). ctxtsize );

   for( auto h : decisions. back( ). hidden )
      stack. at(h). second. hidden = false; 
  
   stack. restore( decisions. back( ). stacksize );

   decisions. pop_back( );  
}

void calc::sequent::hide( size_t ind ) 
{
   if( !stack. at( ind ). second. hidden )
   {
      stack. at( ind ). second. hidden = true;
      if( decisions. size( ) > 0 )
         decisions. back( ). hidden. push_back( ind ); 
   }
}

size_t calc::sequent::liftdist( size_t ind ) const
{
   return ctxt. size( ) - stack. at( ind ). second. ctxtsize; 
}


void calc::sequent::print( std::ostream& out ) const
{
   out << "Sequent\n";
   out << ctxt;
   out << "\n";

   out << "Decisions;\n";
   for( const auto& dec : decisions )
   {
      out << "   ";
      dec. print( out ); 
      out << "\n";
   }

   out << "Stack:\n";
   for( size_t i = 0; i != stack. size( ); ++ i )
   {
      out << "   " << stack. at(i). first;
      out << " : " << stack. at(i). second << "\n";
   }
   out << "\n";
}

namespace calc
{
   namespace  
   {
      void print_ctxt( pretty_printer& pret, 
                       const logic:: context& ctxt, size_t nr )
      {
         while( pret. names. size( ) < nr )
         {
            size_t var = ctxt. size( ) - pret. names. size( ) - 1;
            pret << "   " << pret. names. extend( ctxt. getname( var ));
            pret << " : " << ctxt. gettype( var ); 
            if( ctxt. hasdefinition( var ))
            {
               // Perhaps one should change the printing order:

               pret. names. restore( pret. names. size( ) - 1 );
               pret << " := " << ctxt. getdefinition( var );
               pret. names. extend( ctxt. getname( var ));
            }
            pret << '\n';
         }
      } 
   }
}


void 
calc::sequent::print( pretty_printer& prt ) const
{
   prt << "Sequent:\n";

   prt << "   Decisions: "; 
   for( size_t i = 0; i != decisions. size( ); ++ i )
   {
      if(i) prt << ", ";
      prt << decisions. at(i). choice << "/";
      prt << at( decisions. at(i). parent ). get_dnf( ). size( );
   }
   prt << "\n"; 
   if( prt. names. size( ) != 0 )
      throw std::logic_error( "sequent: pretty-print, names not empty" );

   for( size_t ind = 0; ind != stack. size( ); ++ ind )
   { 
      print_ctxt( prt, ctxt, stack. at( ind ). second. ctxtsize );
      
      prt << "      " << stack. at( ind ). first;
      prt << "   : ";
      stack. at( ind ). second. print( prt ); 
      prt << '\n';
   }

   print_ctxt( prt, ctxt, ctxt. size( ));
   prt. names. restore(0); 
}


