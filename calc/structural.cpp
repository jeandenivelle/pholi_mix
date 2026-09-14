
#include "partial_order_min.h"
#include "structural.h"
#include "logic/pretty.h"

bool
calc::fits( const logic::belief& bl, 
            const logic::typesequence& univtypes )
{
   if( bl. sel( ) == logic::bel_axiom || bl. sel( ) == logic::bel_thm )
   { 
      auto fm = bl. view_form( );  
      if( isprefix( univtypes, fm. tps( ) ))
         return true;
   }
   return false;
}

bool  
calc::fitsbetter( const logic::belief& bl1, const logic::belief& bl2,
                  const logic::typesequence& univtypes )
{
   bool f1 = fits( bl1, univtypes );
   if( f1 )
   { 
      bool f2 = fits( bl2, univtypes );
      if( f2 )
      {
         // Both fit, we look at length of tps( ).

         auto fm1 = bl1. view_form( );
         auto fm2 = bl2. view_form( );

         return fm1. tps( ). size( ) < fm2. tps( ). size( ) &&
                isprefix( fm1. tps( ), fm2. tps( ));
      } 
      else
         return true;
   }
   else
      return false; 
}


std::optional< logic::exact >
calc::findformula( const logic::beliefstate& blfs, errorvector& errs,
                   const identifier& ident,
                   const logic::typesequence& univtypes )
{
   const auto& candidates = blfs. getformulas( ident );   
   if( candidates. size( ) == 0 )
   {
      errortree::builder bld;
      bld << "findformula: " << ident << " does not occur as formula"; 
      errs. push_back( std::move( bld ));
      return { };
   }

   // This loop is in principle unnecessary, but we want to generate
   // a nicer error message when there is no fit:

   size_t nrfits = 0;
   auto best = candidates. end( );

   for( auto p = candidates. begin( ); p != candidates. end( ); ++ p )
   {
      if( fits( blfs. at( *p ), univtypes ))
      {
         ++ nrfits;
         best = p;
      }
   }

   if( nrfits == 0 )
   {
      errortree::builder bld;
      bld << "findformula: no occurrence of " << ident;
      bld << " fits to ";
      logic::pretty::print( bld, blfs, univtypes ); 
      errs. push_back( std::move( bld ));
      return { };
   }

   // Now we need to look for the best fit:

   auto better = [&blfs,&univtypes] ( logic::exact ex1, logic::exact ex2 )
   {
      return fitsbetter( blfs. at(ex1), blfs. at(ex2), univtypes );
   };
   
   best = partial_order_min( candidates. begin( ), candidates. end( ),
                             better );
                                  
   if( best != candidates. end( ))
      return *best;
   else
   {
      errortree::builder bld;
      bld << "findformula: there is no most specific occurrence of " << ident;
      bld << " for the types ";
      logic::pretty::print( bld, blfs, univtypes );
      errs. push_back( std::move( bld ));
      return { };
   }
}


logic::term calc::getgoal( const logic::belief& blf )
{
   switch( blf. sel( ))
   {
   case logic::bel_thm:
      return blf. view_form( ). fm( );
   case logic::bel_axiom:
      return logic::term( logic::op_prop, blf. view_form( ). fm( ));
   }

   throw std::logic_error( "unable to get goal from belief" );
}


