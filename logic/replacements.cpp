
// Written by Hans de Nivelle, September 2022
// Made additions in April 2023.

#include "replacements.h"
#include "cmp.h"


logic::term 
logic::lifter::operator( ) ( term t, size_t vardepth, bool& change ) const
{
   if( t. sel( ) == op_debruijn )
   {
      auto db = t. view_debruijn( );
      if( size_t ind = db. index( ); ind >= vardepth )
      {
         change = true;
         return term( op_debruijn, ind + dist );
      }
   }
   return t; 
}


void 
logic::lifter::print( std::ostream& out ) const
{
   out << "lifter(" << dist << ")";
}


logic::term
logic::sinker::operator( ) ( term t, size_t vardepth, bool& change ) const
{
   if( t. sel( ) == op_debruijn )
   {
      auto db = t. view_debruijn( );
      size_t ind = db. index( );
      if( ind >= vardepth )
      {
         ind -= vardepth; 
         if( ind < dist )
            throw std::logic_error( "sinker. DeBruijn index too small" );

         change = true;
         return term( op_debruijn, ind - dist );
      }  
   }     
   return t; 
}
   
void
logic::sinker::print( std::ostream& out ) const
{
   out << "sinker(" << dist << ")";
}


logic::term logic::lift( term tm, size_t dist )
{
   if( dist == 0 )
      return tm;
   else
      return outermost( lifter( dist ), std::move( tm ), 0 );
}

logic::term logic::sink( term tm, size_t dist )
{
   if( dist == 0 )
      return tm;
   else
      return outermost( sinker( dist ), std::move( tm ), 0 );
}

 
logic::term
logic::sparse_subst::operator( ) ( term t, size_t vardepth, 
                                   bool& change ) const
{
   // std::cout << "sparse-subst " << t << " [" << vardepth << "]\n";

   if( t. sel( ) == op_debruijn )
   {
      size_t ind = t. view_debruijn( ). index( );
      if( ind >= vardepth )
      {
         ind -= vardepth;
         auto p = repl. find( ind );
         if( p != repl. end( ))
         {
            change = true;
            return lift( p -> second, vardepth );
         }
      }
   }

   return t;
}


void logic::sparse_subst::print( std::ostream& out ) const
{
   out << "Sparse subst:\n";
   for( const auto& r : repl )
      out << "   #" << r. first << " := " << r. second << "\n";
}

logic::term
logic::singlesubst::operator( ) ( term t, size_t vardepth, 
                                  bool& change ) const
{
   if( t. sel( ) == op_debruijn )
   {
      size_t ind = t. view_debruijn( ). index( );
      if( ind >= vardepth )
      {
         change = true;

         if( ind == vardepth )
            return lift( value, vardepth );
         else
            return term( op_debruijn, ind - 1 );
      }
   }
   return t;
}

void logic::singlesubst::print( std::ostream& out ) const
{
   out << "singlesubst( #0 := " << value << " )";
}

logic::term
logic::fullsubst::operator( ) ( term t, size_t vardepth, bool& change ) const
{
   if( t. sel( ) == op_debruijn ) 
   {
      size_t ind = t. view_debruijn( ). index( ); 
      if( ind >= vardepth )
      {
         change = true; 

         if( ind < vardepth + values. size( ))
         {
            ind -= vardepth; 
            ind = values. size( ) - ind - 1;   // Because we look backwards.

            return lift( values[ ind ], vardepth );
         }
         else
         {
            ind -= values. size( );
            return term( op_debruijn, ind );
         }   
      }
   }
   return t;
}

void logic::fullsubst::print( std::ostream& out ) const
{
   out << "Full Substitution:\n";
   for( auto i = 1 - (ssize_t) values. size( ); const auto& t: values )
   {
      out << "   #" << i << " := " << t << "\n";
      ++ i;
   }
}

logic::term
logic::argsubst::operator( ) ( term t, size_t vardepth, bool& change ) const
{
   if( t. sel( ) == op_debruijn )
   {
      size_t ind = t. view_debruijn( ). index( );
      if( ind >= vardepth )
      {
         change = true;

         if( ind < vardepth + arity )
         {
            ind -= vardepth;
            ind = arity - ind - 1;   // Because we look backwards.

            return lift( argterm. view_apply( ). arg( ind ), vardepth );
         }
         else
         {
            ind -= arity;
            return term( op_debruijn, ind );
         }
      }
   }
   return t;
}

void logic::argsubst::print( std::ostream& out ) const
{
   out << "Argument Substitution:\n";
   for( size_t i = 0; i < arity; ++ i )
   {
      out << "   #" << (ssize_t)(1 + i) - (ssize_t)arity << " := ";
      out << argterm. view_apply( ). arg(i) << "\n";
   }
}


logic::term
logic::normalizer::operator( ) ( term t, size_t vardepth, bool& change ) const
{
   // std::cout << t << " / " << vardepth << "\n";

   if( t. sel( ) == op_debruijn )
   {  
      size_t ind = t. view_debruijn( ). index( );
      if( ind >= vardepth )
      {
         change = true; 
         ind -= vardepth;

         if( ind < border )
         {
            // Promises O( log( used. size( )) ) complexity:

            auto p = std::lower_bound( used. begin( ), used. end( ), ind );
            if( p == used. end( ) || *p != ind )
               throw std::logic_error( "normalizer: variable not found" );

            ind = p - used. begin( ); 
         }
         else
         {
            ind += ( used. size( ) - border );
         }

         return term( op_debruijn, ind + vardepth ); 
      }
   }
   return t; 
}


void logic::normalizer::print( std::ostream& out ) const
{
   out << "Normalizer(" << border << "):\n";
   for( size_t i = 0; i < used. size( ); ++ i )
   {
      out << "   #" << used[i] << " := #" << i << "\n"; 
   }
}

logic::term 
logic::betareduction::operator( ) ( term t, size_t vardepth, bool& change ) 
{
   if( t. sel( ) == op_apply )
   {
      auto appl = t. view_apply( );
      auto f = appl. func( );

      if( f. sel( ) == op_lambda )
      {
         auto lamb = f. view_lambda( );
         auto body = lamb. body( );

         if( lamb. size( ) > appl. size( ))
         {
            throw std::logic_error( 
                          "too few arguments in lambda-application" );
         }

         argsubst subst( t, lamb. size( ));
         auto res = outermost( subst, lamb. extr_body( ), 0 );

         change = true;
         ++ counter;

         // If too many arguments were given, we construct
         // an application term with the remaining arguments:

         if( lamb. size( ) < appl. size( ))
         {
            res = term( op_apply, res, std::initializer_list< term > ( ));
            for( size_t i = lamb. size( ); i != appl. size( ); ++ i )
               res. view_apply( ). push_back( appl. arg(i)); 
         }
         
         return res;
      }
   }
   return t;
};


void logic::betareduction::print( std::ostream& out ) const
{
  out << "betareduction(" << counter << ")";
}

logic::term
logic::rewriterule::operator( ) ( const term& t, size_t vardepth,
                                  bool& change ) 
{
   if( equal( from, vardepth, t, 0, 0 ))
   {
      change = true;
      ++ counter;
      return lift( to, vardepth );
   }

   return t;
}

void
logic::rewriterule::print( std::ostream& out ) const
{
   out << "rewrite rule: " << from << " --> " << to << "\n";
}


