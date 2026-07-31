
#include "structural.h"
#include "logic/structural.h"
#include "logic/cmp.h"


// True if blf is applicable on types as a theorem or axiom:

bool           
calc::applicable( const logic::belief& blf,
                  const std::vector< logic::type > & types )
{
   std::cout << "applicable " << blf << "\n";

   if( blf. sel( ) == logic::bel_axiom || blf. sel( ) == logic::bel_thm )
   { 
      const auto& fm = blf. view_form( ); 
            
      if( types. size( ) > fm. size( ))
         return false;
         
      for( size_t i = 0; i != types. size( ); ++ i )
      {        
         if( !equal( fm. tp(i), types. at(i)) )
            return false;
      }        

      return true;
   }
   else
      return false; 
}


std::optional< logic::exact >
calc::findformula( const logic::beliefstate& blfs, errorvector& errs,
                   const identifier& ident,
                   const std::vector< logic::type > & types )
{
   const auto& candidates = blfs. getformulas( ident );   
   if( candidates. size( ) == 0 )
   {
      errortree::builder bld;
      bld << "Import: Identifier " << ident << " does not occur as formula"; 
      errs. push_back( std::move( bld ));
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
      errortree::builder bld;
      bld << "Import: No suitable formula found for identifier " << ident;
      errs. push_back( std::move( bld ));
      return { };
   }

   if( nrfits > 1 )
   {
      errortree::builder bld;
      bld << "Import: More than suitable formula found for " << ident;
      errs. push_back( std::move( bld ));
      return { };
   }
  
   return *cand; 
}


logic::term calc::proofobligation( const logic::belief& blf )
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

