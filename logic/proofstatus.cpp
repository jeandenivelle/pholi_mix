
#include "proofstatus.h"

std::ostream& 
logic::operator << ( std::ostream& out, const proofstatus& stat )
{
   if( stat. calcname. empty( ))
      out << "(no proof calculus)\n";
   else
      out << "proven with " << stat. calcname << "\n";

   if( stat. nrgaps )
      out << "the proof has " << stat. nrgaps << " gaps\n";
   if( stat. nrfakes )
      out << "the proof used " << stat. nrfakes << " fakes\n";

   if( stat. nrgaps == 0 && stat. nrfakes == 0 )
      out << "the proof is complete and uses " << stat. nrsteps << " steps\n";

   return out;
}

