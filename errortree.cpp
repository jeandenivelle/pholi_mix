
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
      if( p != sub. begin( ))
         out << '\n';
      (*p) -> print( ind + 6, out );
   }
}

void errortree::report( indentation ind, std::ostream& out )
{
   printheader( ind, out );
   for( auto p = sub. begin( ); p != sub. end( ); ++ p )
   {
      if( p != sub. begin( ))
         out << '\n';
      (*p) -> report( ind + 6, out );
   }

   reported = true;
}


errortree::~errortree( )
{
   if( !reported )
   {
      report( std::cerr );
      std::cerr << "\n\n";
      std::cerr << "unreported errors going out of scope\n";
      std::abort( );
   }

   for( auto& s : sub )
      delete s; 
}


std::ostream& operator << ( std::ostream& out, const errortree& tr )
{  
   tr. print( indentation(0), out );
   return out;
}

