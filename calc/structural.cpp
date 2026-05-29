
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
      bld << "Import: Identifier " << ident << " does not occur as formula"; 
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

#if 0

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

   case prf_flatten:
      return prf;

   case prf_orrepl:
      {
         auto repl = prf. view_orrepl( );
         for( size_t i = 0; i != repl. size( ); ++ i )
            repl. update_sub( i, replace_debruijn( db, repl. extr_sub(i)) );

         return prf;
      }

   case prf_existsrepl:
      {
         auto repl = prf. view_existsrepl( );
         size_t ss = db. size( );
         for( size_t i = 0; i != repl. eigen( ). size( ); ++ i )
            db. push( repl. eigen( ). at(i), db. size( ));

         for( size_t i = 0; i != repl. size( ); ++ i )
            repl. update_sub( i, replace_debruijn( db, repl. extr_sub(i)) );
      
         db. restore( ss ); 
         return prf;
      }

   case prf_expand:
      {
         auto exp = prf. view_expand( );
         const auto& id = exp. ident( );
         if( id. size( ) == 1 )
         {
            auto s = db. find( id. at(0)); 
            if( s != db. size( ))
            {
               return proofterm( prf_expandlocal, exp. fm( ), 
                                 db. size( ) - db. at(s). second - 1,
                                 exp. occ( ));
            }
         }
         return prf;
      }

   case prf_normalize:
      return prf;

   case prf_forallelim:
      {
         auto elim = prf. view_forallelim( ); 
         for( size_t i = 0; i != elim. size( ); ++ i )
            elim. update_inst( i, replace_debruijn( db, elim. extr_inst(i)) ); 
         return prf;
      }

   case prf_import:
      {
         auto imp = prf. view_import( );
         const auto& id = imp. ident( ); 
         if( id. size( ) == 1 )
         {
            // Oh, so very useless! We do this only so that
            // we can complain later.

            auto s = db. find( id. at(0));
            if( s != db. size( ))
            {
               auto res = proofterm( prf_importlocal, 
                                 db. size( ) - db. at(s). second - 1, { } );

               // This loop reveals that repeated fields must have
               // const_iterators. Next version of TreeGen will have them.

               for( size_t i = 0; i != imp. size( ); ++ i )
                  res. view_importlocal( ). push_back( imp. tp(i));
 
               return res; 
            }
         }                                 
      }
      return prf;

   case prf_simplify:
      return prf;

   case prf_fake: 
      {
         auto fk = prf. view_fake( );
         fk. update_goal( replace_debruijn( db, fk. extr_goal( )) );
         return prf;  
      }

   case prf_show:
      return prf; 

   case prf_nextlabel:
      return prf;

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

#endif

