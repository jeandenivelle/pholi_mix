
// Written by Hans de Nivelle, Dec. 2024.

#ifndef LOGIC_COUNTERS_
#define LOGIC_COUNTERS_

#include "term.h"
#include <map>

namespace logic
{

   // A counter does not only count. It can also
   // check presence. 

   template< typename F >
   concept counter = 
      requires( F f, term t, size_t d )
         { { f( t, d ) } -> std::same_as< void > ; };


   template< counter C >
   void traverse( C& counter, const term& tm, size_t vardepth )
   {
      // std::cout << "traverse " << tm << " / " << vardepth << "\n";

      counter( tm, vardepth );

      switch( tm. sel( ))
      {
      case op_exact:
      case op_debruijn:
      case op_unchecked:
      case op_false:
      case op_error:
      case op_true:
         return;

      case op_not:
      case op_prop:
         {
            auto un = tm. view_unary( );
            traverse( counter, un. sub( ), vardepth );
         }
         return;

      case op_and:
      case op_or:
      case op_implies:
      case op_equiv:
      case op_lazy_and:
      case op_lazy_implies:
      case op_equals:
         {
            auto bin = tm. view_binary( );
            traverse( counter, bin. sub1( ), vardepth );
            traverse( counter, bin. sub2( ), vardepth );
         }
         return;

      case op_forall:
      case op_exists:
         {
            auto q = tm. view_quant( ); 
            traverse( counter, q. body( ), vardepth + q. size( ));
         }
         return;

      case op_let:
         {
            auto let = tm. view_let( );
            traverse( counter, let. val( ), vardepth ); 
            traverse( counter, let. body( ), vardepth + 1 );
         }
         return;

      case op_apply:
         {
            auto ap = tm. view_apply( );
            traverse( counter, ap. func( ), vardepth );
            for( size_t i = 0; i != ap. size( ); ++ i )
               traverse( counter, ap. arg(i), vardepth );
         }
         return;

      case op_lambda:
         {
            auto lam = tm. view_lambda( );
            traverse( counter, lam. body( ), vardepth + lam. size( ));
         }
         return; 
      }

      std::cout << "traverse: " << tm. sel( ) << "\n";
      throw std::logic_error( "dont know how to traverse" );
   }


   class debruijn_counter
   {
      std::map< size_t, size_t > occ;
         // It must be an ordered map. We use the debruijn counter 
         // to introduce a new predicate for a subformula, and we want 
         // the variables in this predicated to be ordered in the same 
         // order as they were quantified in the surrounding scope. 

   public:
      void operator( ) ( const term& t, size_t vardepth );

      debruijn_counter( ) = default;
      debruijn_counter( debruijn_counter&& ) = default;
      debruijn_counter& operator = ( debruijn_counter&& ) = default;
         // Preventing accidental copying.

      size_t size( ) const { return occ. size( ); }

      using const_iterator = std::map< size_t, size_t > :: const_iterator;

      const_iterator begin( ) const { return occ. begin( ); }
      const_iterator end( ) const { return occ. end( ); }

      bool contains( size_t v ) const { return occ. contains(v); }

      void print( std::ostream& out ) const;
   };


   inline debruijn_counter count_debruijn( const term& t )
   {
      debruijn_counter db;
      traverse( db, t, 0 );
      return db;
   }


   // Can be used for finding the nearest De Bruijn index: 

   struct debruijn_cmp 
   {
      size_t nearest; 

      void operator( ) ( const term& t, size_t vardepth );

      debruijn_cmp( ) = delete;

      debruijn_cmp( size_t upperbound ) noexcept
         : nearest( upperbound ) 
      { } 

      void print( std::ostream& out ) const;
   };

   inline size_t 
   nearest_debruijn( const term& t, size_t upperbound )
   {
      auto near = debruijn_cmp( upperbound );
      traverse( near, t, 0 );
      return near. nearest;
   }


   // Counts exact identifiers. 
   // We also look inside structural types.

   struct exactcounter
   {
      exact::unordered_map< uint64_t > occ;

      exactcounter( ) = default;
      exactcounter( exact::unordered_map< uint64_t > && occ )
         : occ( std::move( occ ))
      { }

      exactcounter( exactcounter&& ) noexcept = default;
      exactcounter& operator = ( exactcounter&& ) noexcept = default;
 
      void operator( ) ( const term& t, size_t vardepth );

      void count( const term& tm ) 
         { traverse( *this, tm, 0 ); }
   
      void count( const type& tp );
         // Counts in structural type. We don't have a template for that.

      void print( std::ostream& out ) const; 
   };

}

#endif

