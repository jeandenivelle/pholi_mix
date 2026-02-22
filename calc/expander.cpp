
#include "expander.h"

logic::term
calc::expander::operator( ) ( logic::term tm, size_t vardepth, bool& change )
{
   if( tm. sel( ) == logic::op_exact )
   {
      auto ex = tm. view_exact( ). ex( );
      const auto& bl = blfs. at( ex );
         // We get the belief of t, and check if it an overload
         // of id:

      if( bl. ident( ) == ident )
      {
         std::cout << "found overload " << i << "/" << repl << "\n";

         if( i++ == repl )
         {
            if( bl. sel( ) == logic::bel_def )
            {
               change = true; 
               return bl. view_def( ). val( ); 
            }
            else
            {
               errorstack::builder bld;
               bld << "cannot expand identifer " << ident;
               bld << ", it is not a definition"; 
               err. push( std::move( bld ));                     
            }
         }
      }

      return tm;
   }

   if( tm. sel( ) == logic::op_unchecked )
   {
      auto un = tm. view_unchecked( );
      if( un. id( ) == ident )
      {
         if( i == repl )
         {
            errorstack::builder bld;
            bld << "cannot expand unchecked identifier " << ident;
            err. push( std::move( bld ));  
         }

         ++ i;
      }

      return tm;
   }

   return tm;
}

void calc::expander::print( std::ostream& out ) const
{
   out << "Expander " << i << "/" << repl << ": " << ident;
}


