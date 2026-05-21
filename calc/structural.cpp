
#include "structural.h"
#include "logic/cmp.h"

std::optional< logic::exact >
calc::checkandresolve( const logic::beliefstate& blfs, errorstack& err,
                       const identifier& ident,
                       std::vector< logic::type > & types )
{
   std::cout << "ident " << ident << "\n";
   const auto& candidates = blfs. getformulas( ident );   
   if( candidates. size( ) == 0 )
   {
      errorstack::builder bld;
      bld << "Import: Identifier " << ident << " is not used as formula"; 
      err. push( std::move( bld ));
      return { };
   }
  
   size_t nrfits = 0; 
   auto cand = candidates. end( );

   for( auto p = candidates. begin( ); p != candidates. end( ); ++ p )
   {
      if( applicable( blfs. at( *p ), types ))
      {
         cand = p; 
         ++ nrfits; 
      } 
   }

   if( nrfits == 0 )
   {
      errorstack::builder bld;
      bld << "Import: No suitable formula found for " << ident;
      err. push( std::move( bld ));
      return { };
   }

   if( nrfits > 1 )
   {
      errorstack::builder bld;
      bld << "Import: More than suitable formula found for " << ident;
      err. push( std::move( bld ));
      return { };
   }
  
   return *cand; 
}


// True if blf is applicable on tps as a theorem or axiom:

bool           
calc::applicable( const logic::belief& blf,
                  const std::vector< logic::type > & tps )
{
   if( blf. sel( ) == logic::bel_axiom || blf. sel( ) == logic::bel_thm )
   { 
      const auto& fm = blf. view_form( ); 
            
      if( tps. size( ) > fm. size( ))
         return false;
         
      for( size_t i = 0; i != tps. size( ); ++ i )
      {        
         if( !equal( fm. tp(i), tps. at(i)) )
            return false;
      }        

      return true;
   }
   else
      return false; 
}

