
#include "localexpander.h"
#include "logic/replacements.h"


logic::term
calc::localexpander::operator( ) ( logic::term tm, 
                                   size_t vardepth, bool& change )
{
   if( tm. sel( ) == logic::op_debruijn )
   {
      size_t ind = tm. view_debruijn( ). index( );
      if( var + vardepth == ind )
      {
         if( i ++ == repl )
         {
            change = true;
            return lift( value, vardepth + 1 );
         }
      }
   }

   return tm;
}


void calc::localexpander::print( std::ostream& out ) const
{
   out << "Local Expander " << i << "/" << repl;
   out << " :   #" << var << " := " << value;
}


