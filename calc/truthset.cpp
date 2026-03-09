
#include "truthset.h"

void calc::truthset::print( std::ostream& out ) const
{
   switch( val )
   {
   case empty: out << "{}"; return;

   case ffff:  out << "{F}"; return;
   case eeee:  out << "{E}"; return;
   case tttt:  out << "{T}"; return;

   case ffee:  out << "{F,E}"; return;
   case fftt:  out << "{F,T}"; return;
   case eett:  out << "{E,T}"; return;

   case all:   out << "{F,E,T}"; return;
   }

   out << "???"; 
}


