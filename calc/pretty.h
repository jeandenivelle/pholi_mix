
// Written by Hans de Nivelle, December 2025.

#ifndef CALC_PRETTY_
#define CALC_PRETTY_

#include "logic/pretty.h"

#include "quantifiers.h"
#include "propositional.h"

namespace calc
{

   struct pretty_printer
   {
      std::ostream& out;
      const logic::beliefstate& blfs;
      logic::pretty::uniquenamestack names;

      pretty_printer( std::ostream& out,
                      const logic::beliefstate& blfs )
         : out( out ),
           blfs( blfs ) 
      { }  
   };

   // Default is to print into print. out:

   template< typename T >
   pretty_printer& operator << ( pretty_printer& print, const T& t )
   {
      print. out << t;
      return print;
   }

   template< typename T >
   void printquantifier( pretty_printer& print, 
                         const char* qname, 
                         const std::vector< logic::vartype > & vars,
                         const T& body )
   {
      size_t ns = print. names. size( );
      if( vars. size( ))
      {
         print << qname;
         logic::pretty::print( print. out, print. blfs, print. names,
            [&vars]( size_t i ) { return vars. at(i); }, vars. size( ));
         print << " IN ";
      }

      print << body;
      print. names. restore( ns );
   }

   inline pretty_printer&
   operator << ( pretty_printer& print, const logic::type& tp )
   {
      logic::pretty::print( print. out, print. blfs, tp, {0,0} );
      return print;
   }

   inline pretty_printer&
   operator << ( pretty_printer& print, const logic::term& tm )
   {
      logic::pretty::print( print. out, print. blfs, print. names, 
                            tm, {0,0} );
      return print;
   }

   template< typename F >
   pretty_printer& operator << ( pretty_printer& print, 
                                 const conjunction<F> & conj )
   {
      print << '{';
      for( auto p = conj. begin( ); p != conj. end( ); ++ p )
      {
         if( p != conj. begin( ))
            print << "; ";
         else
            print << ' ';
         print << *p;
      }
      print << " }";
      return print;
   }

   template< typename F >
   pretty_printer& operator << ( pretty_printer& print, 
                                 const disjunction<F> & disj )
   {
      print << '{';
      for( auto p = disj. begin( ); p != disj. end( ); ++ p )
      {
         if( p != disj. begin( ))
            print << "; ";
         else
            print << ' ';
         print << *p;
      }
      print << " }";
      return print;
   }

   template< typename F > 
   pretty_printer& 
   operator << ( pretty_printer& print, const forall<F> & all )
   {
      printquantifier( print, "FORALL", all. vars, all. body );
      return print;
   }

   template< typename F >
   pretty_printer&
   operator << ( pretty_printer& print, const exists<F> & ex )
   {
      printquantifier( print, "EXISTS", ex. vars, ex. body );
      return print;
   }

}

#endif

