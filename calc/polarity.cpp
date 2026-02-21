
#include "polarity.h"

const char* calc::getcstring( polarity pol )
{
   switch( pol )
   {
   case pol_pos:       return "positive"; 
   case pol_neg:       return "negative";
   default:            return "???";
   }
}

calc::polarity calc::operator - ( polarity pol )
{
   switch( pol )
   {
   case pol_pos:       return pol_neg;
   case pol_neg:       return pol_pos;
   }
   std::cout << pol << "\n";
   throw std::logic_error( "cannot negate unknown polarity" ); 
}

