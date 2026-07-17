
#include "proofstatus.h"

std::ostream& 
logic::operator << ( std::ostream& out, const proofstatus& stat )
{
   if( stat. calcname. empty( ))
      out << "(no proof)";
   else
   {
      if( stat. nrgaps )
         out << "(incompletely proven ";
      else
         out << "(proven "; 
      out << "using " << stat. calcname;
      out << " in " << stat. nrsteps << " steps";
      if( stat. nrgaps )
         out << " with " << stat. nrgaps << " gaps";
      out << ")";
   }
   return out;
}

