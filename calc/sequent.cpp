
#include "sequent.h"

void calc::sequent::seqform::print( std::ostream& out ) const
{
   if( is_dnf( ))
      out << get_dnf( );

   if( is_unf( ))
      out << get_unf( );

   out << " / " << ctxtsize;
   if( hidden ) out << "      (hidden)";
   if( name. size( )) out << "   (" << name << ")";
}


void calc::sequent::seqform::print( pretty_printer& out ) const
{
   if( !hidden )
   {
      if( is_dnf( ))
         out << get_dnf( ); 
      if( is_unf( ))
         out << get_unf( ); 
      if( !name. empty( )) 
         out << "      " << "(" << name << ")";
   }
   else
      out << "   (hidden)";
}

size_t calc::sequent::append( unf< logic::term > u )
{
   if( u. vars. size( ) == 0 )
      return append( disjunction( { exists( std::move( u. body )) } ));
   else 
   {
      size_t pos = stack. size( );
      stack. push_back( seqform( std::move(u), ctxt. size( )));
      return pos;
   }
}

size_t calc::sequent::append( dnf< logic::term > d )
{
   size_t pos = stack. size( );
   stack. push_back( seqform( std::move(d), ctxt. size( )));
   return pos;
}


void calc::sequent::popdecision( )
{
   if( decisions. empty( ))
      throw std::logic_error( "popdecision( ): there is no decision" );

   if( decisions. back( ). ctxtsize > ctxt. size( ))
      throw std::logic_error( "popdecision( ): context too small" ); 

   ctxt. restore( decisions. back( ). ctxtsize );

   for( auto h : decisions. back( ). hidden )
      stack. at(h). hidden = false; 

   if( stack. size( ) < decisions. back( ). stacksize )
      throw std::logic_error( "popdecision( ): stack too small" );
 
   while( stack. size( ) > decisions. back( ). stacksize )
   {
      if( stack. back( ). name. size( ))
         index. erase( stack. back( ). name );
      stack. pop_back( );
   }
 
   decisions. pop_back( );  
}

void calc::sequent::hide( size_t ind ) 
{
   if( !stack. at( ind ). hidden )
   {
      stack. at( ind ). hidden = true;
      if( decisions. size( ) > 0 )
         decisions. back( ). hidden. push_back( ind ); 
   }
}

size_t calc::sequent::liftdist( size_t ind ) const
{
   return ctxt. size( ) - stack. at( ind ). ctxtsize; 
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
      out << "   " << stack. at(i) << "\n";
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
      print_ctxt( prt, ctxt, stack. at( ind ). ctxtsize );
      
      prt << "      ";
      stack. at( ind ). print( prt ); 
      prt << '\n';
   }

   print_ctxt( prt, ctxt, ctxt. size( ));
   prt. names. restore(0); 
}


