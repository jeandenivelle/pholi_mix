
#include "errortree.h"
#include <list>
#include <string_view>

uint8_t errortree::limit99( uint8_t ser )
{
   if( ser > 99 )
      return 99;
   else
      return ser;
}

void errortree::printheader( indentation ind, std::ostream& out ) const
{
   if( ser < 99 )
      out << ind << "seriousness " << (int) ser << ": ";
   else
      out << ind;  

   std::string_view vw = header; 

   while( vw. size( ) && isspace( vw. front( )))
      vw. remove_prefix(1);

   while( vw. size( ) && isspace( vw. back( )))
      vw. remove_suffix(1);

   if( !vw. empty( ))
   {
      for( char c : vw )
      {
         out << c;
         if( c == '\n' )
            out << ind;
      }
      out << '\n';
   }
}

void errortree::print( indentation ind, std::ostream& out ) const
{
   printheader( ind, out );
   for( auto p = sub. begin( ); p != sub. end( ); ++ p )
   {
      out << '\n';
      (*p) -> print( ind + 6, out );
   }
}

void errortree::report( indentation ind, std::ostream& out )
{
   printheader( ind, out );
   for( auto p = sub. begin( ); p != sub. end( ); ++ p )
   {
      out << '\n';
      (*p) -> report( ind + 6, out );
   }

   reported = true;
}


errortree::~errortree( )
{
   if( !reported )
   {
      std::cerr << "UNREPORTED ERROR:\n";
      report( indentation(3), std::cerr );
      std::cerr << "\n";
   }

   for( auto& s : sub )
      delete s; 
}

void transfer( errorvector from, errorvector& into )
{
   for( auto& e : from )
      into. push_back( std::move(e)); 
}

void transfer( errortree::builder header,
               errorvector from, errorvector& into )
{
   auto tr = errortree( std::move( header ), 
                        from. begin( ), from. end( ));

   into. push_back( std::move( tr ));
}


std::ostream& operator << ( std::ostream& out, const errortree& tr )
{  
   tr. print( indentation(0), out );
   return out;
}

std::ostream& operator << ( std::ostream& out, const errorvector& vect )
{
   for( auto p = vect. begin( ); p != vect. end( ); ++ p )
   {
      if( p != vect. begin( ))
         out << '\n';
      out << *p;
   }
   out << '\n';
   return out;
}


