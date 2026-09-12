
#include "proofstatus.h"

std::ostream& 
logic::operator << ( std::ostream& out, const proofstatus& stat )
{
   if( stat. calcname. size( ))
   {
      if( stat. distance )
         out << "(attempted with " << stat. calcname;
      else
         out << "(proven with " << stat. calcname;
      out << " in " << stat. nrsteps << " steps";

      for( auto p = stat. dependencies. begin( ); 
                p != stat. dependencies. end( ); ++ p )
      {
         if( p != stat. dependencies. begin( ))
            out << " ";
         else
            out << ", ";
         out << ( p -> first ) << " : " << ( p -> second );
      }
      out << " )";
   }
   else
      out << "(no proof)";

   return out;
}


