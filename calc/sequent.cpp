
#include "sequent.h"
#include "logic/pretty.h"


void calc::sequent::seqform::ugly( std::ostream& out ) const
{
   if( is_dnf( ))
      out << get_dnf( );

   out << " / " << ctxtsize;
   if( blocked ) out << "   (blocked)";
   out << "\n";
}


#if 0

void calc::sequent::segment::erase( ssize_t ind )
{
   auto it = find( ind );
   stack. erase( it );
}

auto
calc::sequent::segment::find( ssize_t ind ) 
   -> segment::iterator
{
   if( !inrange( ind ))
      throw std::range_error( "segment: index out of range" );

   if( ind >= 0 )
      return stack. begin( ) + ind;
   else
      return stack. end( ) + ind;
}

auto
calc::sequent::segment::find( ssize_t ind ) const
   -> segment::const_iterator
{
   if( !inrange( ind ))
      throw std::range_error( "segment: index out of range" );

   if( ind >= 0 )
      return stack. begin( ) + ind;
   else
      return stack. end( ) + ind;
}

#endif

size_t
calc::sequent::assume( const std::string& name,
                       const logic::type& tp )
{
   size_t nr = ctxt. size( );
   ctxt. append( name, tp );
   db. push( name, nr );
   return nr;
}

size_t 
calc::sequent::define( const std::string& name,
                       const logic::term& val, 
                       const logic::type& tp )
{
   size_t nr = assume( name, tp );
   defs. insert( std::pair( nr, val ));
   return nr;
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

void calc::sequent::block( ssize_t ind ) 
{
   size_t k = ( ind >= 0 ) ? ind : stack. size( ) + ind;
      // This is the real index in stack.

   if( !stack[k]. blocked )
   {
      stack[k]. blocked = true;
      if( levels. size( ) > 0 )
         levels. back( ). blocking. push_back(k); 
   }
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

void calc::sequent::restore( size_t ss )
{
   for( size_t dd = ss; dd < ctxt. size( ); ++ dd )
   {
      if( defs. contains( dd ))
         defs. erase(dd);
   }

   ctxt. restore(ss);
   db. restore(ss);
}

#endif

void calc::sequent::ugly( std::ostream& out ) const
{
   out << "Sequent:\n";
   out << ctxt;
   out << "\n";
   out << "Definitions:\n";
   for( const auto& def : defs )
      out << "   #" << def. first << " := " << def. second << "\n";

   out << "Stack:\n";
   for( size_t i = 0; i != stack. size( ); ++ i )
   {
      out << "   " << i << " : "; stack[i]. ugly( out );
   }
}

#if 0

void 
calc::sequent::pretty( pretty_printer& out ) const
{
   out << "Sequent:\n";

   size_t db = 0;

   for( const auto& s : seg )
   {
      out << "   segment " << s. name << ":\n";
      while( db < s. contextsize )
      {
         size_t ind = ctxt. size( ) - db - 1;
         out << "      " << out. names. extend( ctxt. getname( ind ));
         out << " : " << ctxt. gettype( ind ); 
         if( auto p = defs. find( db ); p != defs. end( ))
         {
            out. names. restore( out. names. size( ) - 1 );
            out << " := " << ( p -> second );
            out. names. extend( ctxt. getname( ind ));
         }
         out << '\n';
         ++ db;
      }
      for( size_t i = 0; i != s. stack. size( ); ++ i )
         out << "      " << i << " : " << s. at(i) << '\n';
   }
}

#endif

