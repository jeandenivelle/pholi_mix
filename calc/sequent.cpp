
#include "sequent.h"
#include "logic/pretty.h"

#if 0
void calc::sequent::seqform::print( std::ostream& out ) const
{
   if( is_dnf( ))
      out << get_dnf( );

   if( is_unf( ))
      out << get_unf( );

   out << " / " << ctxtsize;
   if( hidden ) out << "   (hidden)";
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

void calc::sequent::append( cnf< logic::term > c )
{
   for( auto& u : c )
   {
      if( u. vars. size( ) == 0 )
         append( disjunction( { exists( std::move( u. body )) } ));
      else
         stack. push( nextlabel ++, seqform( std::move(u), ctxt. size( )));
   }
}

void calc::sequent::append( dnf< logic::term > d )
{
   stack. push( nextlabel ++, seqform( std::move(d), ctxt. size( )));
}


void
calc::sequent::maketrivial( size_t ind )
{
   if( ind >= stack. size( ))
      throw std::logic_error( "maketrivial: Not a valid index" );

   auto tr = exists( logic::term( logic::op_true ));
   stack. at( ind ). second. fm = disjunction( { std::move( tr ) } ); 
   stack. at( ind ). second. hidden = true;
}


void calc::sequent::hide( size_t ind ) 
{
   if( !stack. at( ind ). second. hidden )
   {
      stack. at( ind ). second. hidden = true;
      if( levels. size( ) > 0 )
         levels. back( ). hidden. push_back( ind ); 
   }
}

void calc::sequent::poplevel( )
{
   if( levels. empty( ))
      throw std::logic_error( "poplevel( ): there is no level" );
 
   if( levels. back( ). ctxtsize != ctxt. size( ))
      throw std::logic_error( "poplevel( ): context not restored" );

   for( auto h : levels. back( ). hidden )
      stack. at(h). second. hidden = false; 
  
   stack. restore( levels. back( ). stacksize );

   levels. pop_back( );  
}


size_t calc::sequent::liftdist( size_t ind ) const
{
   return ctxt. size( ) - stack. at( ind ). second. ctxtsize; 
}

#if 0

calc::sequent::segment& calc::sequent::back( )
{  
   if( seg. size( ) == 0 )
      throw std::logic_error( "back: there are no segments" );

   return seg. back( );
}

#if 0

logic::exact
calc::sequent::getexactname( size_t i ) const
{
   if( i >= size( )) throw std::logic_error( "sequent::getexactname" ); 
   switch( steps[i]. sel( ))
   {
   case seq_belief:
      return steps[i]. view_belief( ). name( ); 


   }
   std::cout << steps[i]. sel( ) << "\n";
   throw std::logic_error( "cannot get exact name" );
}

#endif

#endif

void calc::sequent::ugly( std::ostream& out ) const
{
   out << "Sequent:\n";
   out << ctxt;
   out << "\n";

   out << "Stack:\n";
   for( size_t i = 0; i != stack. size( ); ++ i )
   {
      out << "   " << stack. at(i). first;
      out << " : " << stack. at(i). second << "\n";
   }
   out << "\n";
}


void 
calc::sequent::pretty( pretty_printer& out ) const
{
   out << "Sequent:\n";

   size_t db = 0;

   for( size_t ind = 0; ind != stack. size( ); ++ ind )
   { 
      while( db < stack. at( ind ). second. ctxtsize )
      {
         size_t ind = ctxt. size( ) - db - 1;
         out << "   " << out. names. extend( ctxt. getname( ind ));
         out << " : " << ctxt. gettype( ind ); 
         if( ctxt. hasdefinition( ind ))
         {
            // Perhaps one should change the printing order:
            out. names. restore( out. names. size( ) - 1 );
            out << " := " << ctxt. getdefinition( ind );
            out. names. extend( ctxt. getname( ind ));
         }
         out << '\n';
         ++ db;
      }

      out << "      " << stack. at( ind ). first;
      out << "   : ";
      stack. at( ind ). second. print( out ); 
      out << '\n';
   }
}

#endif

