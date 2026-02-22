
#ifndef CALC_QUANTIFIERS_
#define CALC_QUANTIFIERS_

#include <iostream>
#include <vector>

namespace calc
{

   // We are only a dumb data structure.
   // We have no algorithms.

   template< typename F > struct forall
   {
      std::vector< logic::vartype > vars;
      F body; 

      forall( ) noexcept = default;

      explicit forall( F body ) 
         : body( std::move( body )) 
      { }

      explicit forall( std::vector< logic::vartype > vars, F body ) 
         : vars( std::move( vars )),
           body( std::move( body ))
      { }

      void print( std::ostream& out ) const
      {
         out << "forall(";
         for( auto p = vars. begin( ); p != vars. end( ); ++ p )
         {
            if( p != vars. begin( ))
               out << ", ";
            else
               out << ' ';
            out << *p;
         }
         out << " ): " << body;
      } 
   };


   template< typename F > struct exists
   {
      std::vector< logic::vartype > vars;
      F body;

      exists( ) noexcept = default;

      explicit exists( F body ) 
        : body( std::move( body )) 
      { }

      explicit exists( std::vector< logic::vartype > vars, F body )
         : vars( std::move( vars )),
           body( std::move( body ))
      { }

      void print( std::ostream& out ) const
      {
         out << "exists(";
         for( auto p = vars. begin( ); p != vars. end( ); ++ p )
         {
            if( p != vars. begin( ))
               out << ", ";
            else
               out << ' ';
            out << *p;
         }
         out << " ): " << body;
      }
   };

}

#endif

