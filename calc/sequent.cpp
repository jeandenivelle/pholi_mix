
#include "sequent.h"
#include "logic/pretty.h"

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
         stack. push_back( seqform( std::move(u), ctxt. size( )));
   }
}

void calc::sequent::append( dnf< logic::term > d )
{
   stack. push_back( seqform( std::move(d), ctxt. size( )));
}

bool
calc::sequent::hasindex( ssize_t ind ) const
{
   ssize_t ss = stack. size( );
   return ind >= -ss && ind < ss;
}

const calc::sequent::seqform& calc::sequent::at( ssize_t ind ) const 
{
   if( !hasindex( ind ))
      throw std::range_error( "sequent: index out of range" );
  
   auto it = ind >= 0 ? ( stack. begin( ) + ind ) : ( stack. end( ) + ind );
   return *it;
}

calc::sequent::seqform& calc::sequent::at( ssize_t ind ) 
{     
   if( !hasindex( ind ))
      throw std::range_error( "sequent: index out of range" ); 
 
   auto it = ind >= 0 ? ( stack. begin( ) + ind ) : ( stack. end( ) + ind );
   return *it;
}           

void
calc::sequent::maketrivial( ssize_t ind )
{
   size_t k = ( ind >= 0 ) ? ind : stack. size( ) + ind;
   auto tr = exists( logic::term( logic::op_true ));
   stack. at(k). fm = disjunction( { std::move( tr ) } ); 
   stack. at(k). hidden = true;
}

void calc::sequent::hide( ssize_t ind ) 
{
   size_t k = ( ind >= 0 ) ? ind : stack. size( ) + ind;
      // This is the real index in stack.

   if( !stack[k]. hidden )
   {
      stack[k]. hidden = true;
      if( levels. size( ) > 0 )
         levels. back( ). hidden. push_back(k); 
   }
}

void calc::sequent::poplevel( )
{
   if( stack. back( ). ctxtsize != ctxt. size( ))
      throw std::logic_error( "poplevel( ): context not restored" );

   for( auto h : levels. back( ). hidden )
      stack[h]. hidden = false; 
  
   while( stack. size( ) > levels. back( ). stacksize )
      stack. pop_back( ); 

   levels. pop_back( );  
}

size_t calc::sequent::liftdist( ssize_t ind ) const
{
   size_t k = ( ind >= 0 ) ? ind : stack. size( ) + ind;
   return ctxt. size( ) - stack[k]. ctxtsize; 
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
      out << "   " << i << " : " << stack[i] << "\n";
   }
}


void 
calc::sequent::pretty( pretty_printer& out ) const
{
   out << "Sequent:\n";

   size_t db = 0;

   for( size_t ind = 0; ind != stack. size( ); ++ ind )
   { 
      while( db < stack[ ind ]. ctxtsize )
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

      out << "      " << ind << " : ";
      stack[ ind ]. print( out ); 
      out << '\n';
   }
}


