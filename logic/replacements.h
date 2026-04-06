
#ifndef LOGIC_REPLACEMENTS_
#define LOGIC_REPLACEMENTS_   

#include "term.h"
#include "outermost.h"
#include "util/print.h"

#include <vector>
#include <unordered_map>

namespace logic
{

   struct has_used
   {
      uint64_t used;

      has_used( ) noexcept 
         : used(0)
      { }
   };

   // The boolean should be assignend true when a 
   // replacement happened, and not changed when there was 
   // no replacement. 

   struct lifter : public has_used
   {
      size_t dist;

      lifter( ) = delete;

      explicit lifter( size_t dist )
         : dist( dist )
      { }

      term operator( ) ( term t, size_t vardepth );

      void print( std::ostream& out ) const; 
   };


   // Sinker is the opposite of lifter. If term contains a 
   // DeBruijn index less than dist, we crash. 

   struct sinker : public has_used
   {
      size_t dist;

      sinker( ) = delete;

      explicit sinker( size_t dist )
         : dist( dist )
      { }

      term operator( ) ( term t, size_t vardepth );

      void print( std::ostream& out ) const;
   };

   term lift( logic::term tm, size_t dist );
   term sink( logic::term tm, size_t dist );


   // A sparse subst replace some, but not
   // necessarily all, De Bruijn indices. 
   // Variables that are not in the domain of the substitution,
   // are not changed.
   // It is currently not used.

   class sparse_subst : public has_used
   {
      std::unordered_map< size_t, term > repl;

   public:
      sparse_subst( ) noexcept = default;
      sparse_subst( sparse_subst&& ) noexcept = default;
      sparse_subst& operator = ( sparse_subst&& ) = default;

      void assign( size_t var, const term& val )
         { repl. insert( std::pair( var, val )); }
      void assign( size_t var, term&& val )
         { repl. insert( std::pair( var, std::move( val ))); }

      term operator( ) ( term t, size_t vardepth );
 
      void print( std::ostream& out ) const;      
   };


   // A single subst replaces #0 by value. 
   // The other variables are decreased by one.

   struct singlesubst : public has_used
   {
      term value; 

      singlesubst( const term& value ) 
         : value( value ) 
      { }

      term operator( ) ( term t, size_t vardepth );

      void print( std::ostream& out ) const;
   };

    
   // A fullsubst completely removes the nearest DeBruijn indices 
   // #0,#1,#2, ... 
   // DeBruijn that are not in the domain of fullsubst are shifted down. 

   class fullsubst : public has_used
   {
      std::vector< term > values;

   public:
      fullsubst( ) noexcept
      { }

      fullsubst( std::vector< term > && values ) noexcept
         : values( std::move( values ))
      { }

      term operator( ) ( term t, size_t vardepth );

      void print( std::ostream& out ) const;

      size_t size( ) const { return values. size( ); } 
      void append( term val ) { values. push_back( std::move( val )); }
   };

   // Argument substitution works like fullsubst, but it uses
   // the arguments of an application term. 
   // If you have a beta-redux 
   // apply( lambda ( T1, ..., Tn ) t, u1 ... um ), 
   // there is no need to construct fullsubst( u1, ..., um ).
   // Instead one can use the application term to get the ui.

   struct argsubst : public has_used
   {
      term argterm;    // Term from which we take the arguments.
      size_t arity;    // In case of incomplete application, 
                       // we don't use all arguments of argterm.

      argsubst( const term& argterm, size_t arity )
         : argterm( argterm ),
           arity( arity )
      { }

      term operator( ) ( term t, size_t vardepth );

      void print( std::ostream& out ) const;
   };

   // A normalizer normalizes De Bruijn indices. 
   // This is needed if you want to move a term to another context
   // that assumes only De Bruijn indices that occurring in the term.
   // For example, you have p( #0, #2, #3 ) in a context 
   // ( O2T, T, O, T2O ). (with #0 at the end).  
   // You want to put p( #0, #2, #3 ) in a modified context
   // where only #0 and #2, #3 are assumed.
   // In that case, you need p( #0, #1, #2 ) in a context
   // ( O2T, T, T2O ).
   // We need a #0 -> #0, #2 -> #1. 
   // #3 is outside of the affected context, but it still
   // should be decreased by 1. 
   // Below we would have values = { 0, 1 } and
   // domain = 3.

   class normalizer : public has_used
   {
      std::vector< size_t > freevars;
      size_t border;   // Supremum of affected indices.
                       // Variables >= border will be decreased.

   public:
      normalizer( ) = delete;
      normalizer( size_t border )
         : border( border )
      { }      

      void append( size_t var ) { freevars. push_back( var ); }
      term operator( ) ( term t, size_t vardepth );

      void print( std::ostream& out ) const;        
   };


   // This is both complete and incomplete beta-reduction:

   struct betareduction : public has_used
   {
      betareduction( ) noexcept
      { }

      term operator( ) ( term t, size_t vardepth );
         // Not const method, because we count the reductions.

      void print( std::ostream& out ) const; 
   };

   // A decurrier replaces f( t_1, ..., t_m )( u_1, ..., u_n ) by
   // f( t_1, ..., t_m, u_1, ..., u_n ).
   // It is the opposite of Currying.

   struct decurrier : public has_used
   {
      decurrier( ) noexcept 
      { } 

      term operator( ) ( term t, size_t vardepth ); 

      void print( std::ostream& out ) const; 
   };


   // A few very simple, logical simplifications: 
   // t == t         ==> TRUE
   // ## t           ==> TRUE
   // ! TRUE         ==> FALSE
   // ! ERROR        ==> ERROR
   // ! FALSE        ==> TRUE
   // EXISTS x FALSE ==> FALSE
   // FORALL x TRUE  ==> TRUE
 
   struct simplifier : public has_used
   {
      simplifier( ) noexcept
      { } 

      term operator( ) ( term t, size_t vardepth );

      void print( std::ostream& out ) const;
   };

 
   struct rewriterule : public has_used
   {
      term from;
      term to; 
     
      rewriterule( const term& from, const term& to )
         : from( from ), to( to ) 
      { }

      rewriterule( term&& from, term&& to )
         : from( std::move( from )),
           to( std::move( to )) 
      { }

      void swap( ) 
         { std::swap( from, to ); } 

      term operator( ) ( term t, size_t vardepth );

      void print( std::ostream& out ) const;
   };

}

#endif 


