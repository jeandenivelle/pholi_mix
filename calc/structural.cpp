
#include "structural.h"
#include "logic/structural.h"
#include "logic/cmp.h"
#include "proofchecking.h"

std::optional< logic::exact >
calc::findformula( const logic::beliefstate& blfs, errorstack& err,
                   const identifier& ident,
                   const std::vector< logic::type > & types )
{
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
   std::cout << "applicable " << blf << "\n";

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

void 
calc::checkproof( const logic::beliefstate& blfs, errorstack& err,
                  logic::exact fname, proofterm prf )
{
   std::cout << "checking proof of " << fname << "\n";

   auto& blf = blfs. at( fname );

   sequent seq;

   switch( blf. sel( ))
   {
   case logic::bel_thm:
      {
         seq. ctxt. define( "goal", blf. view_form( ). fm( ),
                            logic::type( logic::type_form ));
         break;
      } 

   default:
      throw std::logic_error( "belief not a formula" ); 
   }

   seq. ugly( std::cout ); 

   logic::exact::unordered_set dependencies;
   checkproof( blfs, seq, prf, err, dependencies );

   seq. ugly( std::cout ); 
   // The last formula must be a DNF that subsumes #0 (the goal). 
}

calc::proofterm 
calc::replace_debruijn( indexedstack< std::string, size_t > & db, 
                        proofterm prf )
{
   using namespace calc;

   switch( prf. sel( ))
   {

   case prf_cut:
      {
         auto ct = prf. view_cut( );
         ct. update_fm( replace_debruijn( db, ct. extr_fm( )) );
         return prf; 
      }

   case prf_chain:
      {
         auto ch = prf. view_chain( );
         for( size_t i = 0; i != ch. size( ); ++ i )
         {
            ch. update_sub( i, replace_debruijn( db, ch. extr_sub(i)) );
         }
         return prf; 
      }

   case prf_fake: 
      {
         auto fk = prf. view_fake( );
         fk. update_goal( replace_debruijn( db, fk. extr_goal( )) );
         return prf;  
      }
   }
   std::cout << prf. sel( ) << "\n";
   throw std::logic_error( "unknown selector in replace_debruijn" );
}

calc::proofterm calc::replace_debruijn( proofterm prf )
{
   indexedstack< std::string, size_t > debruijn;
   debruijn. push( "goal", 0 );

   prf = replace_debruijn( debruijn, std::move( prf ));

   if( debruijn. size( ) != 1 )
      throw std::logic_error( "Wrong De Bruijn stack after check" );

   return prf;
}

