
#include "typesequence.h"
#include "cmp.h"

void logic::typesequence::print( std::ostream& out ) const 
{
   out << '(';
   for( size_t i = 0; i != repr. size( ); ++ i )
   {
      if( i == 0 )
         out << " ";
      else
         out << ", ";
      out << repr. at(i);
   }
   out << " )";
}


bool 
logic::isprefix( const typesequence& seq1, const typesequence& seq2 )
{
   if( seq1. size( ) > seq2. size( ))
      return false;

   for( size_t i = 0; i != seq1. size( ); ++ i )
   {
      if( !equal( seq1. at(i), seq2. at(i)) ) 
         return false;
   }

   return true;
}

