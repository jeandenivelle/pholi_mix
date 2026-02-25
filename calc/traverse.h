
// Written by Hans de Nivelle, December 2025.

#ifndef CALC_TRAVERSE_
#define CALC_TRAVERSE_

namespace calc
{

   template< logic::counter C, typename F >
   void traverse( C& counter, const forall<F> & all, size_t vardepth )
   {
      traverse( counter, all. body, vardepth + all. vars. size( ));
   }

   template< logic::counter C, typename F >
   void traverse( C& counter, const exists<F> & ex, size_t vardepth )
   {
      traverse( counter, ex. body, vardepth + ex. vars. size( ));
   }

   template< logic::counter C, typename F >
   void traverse( C& counter, const conjunction<F> & conj, size_t vardepth )
   {
      for( const auto& f : conj )
         traverse( counter, f, vardepth );
   }

   template< logic::counter C, typename F >
   void traverse( C& counter, const disjunction<F> & disj, size_t vardepth )
   {
      for( const auto& f : disj )
         traverse( counter, f, vardepth );
   }

}

#endif

