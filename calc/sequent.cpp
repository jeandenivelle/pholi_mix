
#include "sequent.h"
#include "logic/pretty.h"

auto calc::sequent::segment::at( ssize_t ind ) const 
   -> const forall< disjunction< exists< logic::term >>> & 
{
   auto it = find( ind );
   return *it; 
}

auto calc::sequent::segment::at( ssize_t ind ) 
   -> forall< disjunction< exists< logic::term >>> &
{
   auto it = find( ind );
   return *it; 
}

void calc::sequent::segment::erase( ssize_t ind )
{
   auto it = find( ind );
   stack. erase( it );
}

bool
calc::sequent::segment::inrange( ssize_t ind ) const
{
   ssize_t ss = stack. size( );
   return ind >= -ss && ind < ss;
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

void calc::sequent::push_back( const std::string& name )
{
   seg. push_back( segment( name,  ctxt. size( )));
}

void calc::sequent::pop_back( )
{
   if( seg. size( ) == 0 )
      throw std::logic_error( "pop_back( ) : nothing to pop" );

   seg. pop_back( );
}

const calc::sequent::segment& calc::sequent::back( ) const 
{
   if( seg. size( ) == 0 )
      throw std::logic_error( "back: there are no segments" );

   return seg. back( );
}

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

void calc::sequent::ugly( std::ostream& out ) const
{
   out << "Sequent:\n";
   out << ctxt;
   out << "\n";
   out << "Definitions:\n";
   for( const auto& def : defs )
      out << "   #" << def. first << " := " << def. second << "\n";
  
   out << "\n"; 
   out << "Segments:\n";
   for( const auto& s : seg ) 
   {
      out << "   segment " << s. name << ", ";
      out << "contextsize = " << s. contextsize << ":\n";
      for( size_t i = 0; i != s. stack. size( ); ++ i )
         out << "      " << i << " : " << s. stack[i] << "\n";
   } 
}


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


