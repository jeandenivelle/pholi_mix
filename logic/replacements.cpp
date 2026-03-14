
// Written by Hans de Nivelle, September 2022
// Made additions in April 2023.

#include "replacements.h"
#include "cmp.h"


logic::term 
logic::lifter::operator( ) ( term t, size_t vardepth ) 
{
   if( t. sel( ) == op_debruijn )
   {
      auto db = t. view_debruijn( );
      if( size_t ind = db. index( ); ind >= vardepth )
      {
         ++ used; 
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
logic::sinker::operator( ) ( term t, size_t vardepth ) 
{
   if( t. sel( ) == op_debruijn )
   {
      auto db = t. view_debruijn( );
      size_t ind = db. index( );
      if( ind >= vardepth )
      {
         ind -= vardepth; 
         if( ind < dist )
            throw std::logic_error( "sinker: DeBruijn index too small" );

         ++ used;
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
   {
      auto lift = lifter( dist );
      return outermost( lift, std::move( tm ), 0 );
   }
}

logic::term logic::sink( term tm, size_t dist )
{
   if( dist == 0 )
      return tm;
   else
   {
      auto sink = sinker( dist );
      return outermost( sink, std::move( tm ), 0 );
   }
}

 
logic::term
logic::sparse_subst::operator( ) ( term t, size_t vardepth )
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
            ++ used;
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
logic::singlesubst::operator( ) ( term t, size_t vardepth ) 
{
   if( t. sel( ) == op_debruijn )
   {
      size_t ind = t. view_debruijn( ). index( );
      if( ind >= vardepth )
      {
         ++ used;

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
logic::fullsubst::operator( ) ( term t, size_t vardepth ) 
{
   if( t. sel( ) == op_debruijn ) 
   {
      size_t ind = t. view_debruijn( ). index( ); 
      if( ind >= vardepth )
      {
         ++ used; 

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
logic::argsubst::operator( ) ( term t, size_t vardepth ) 
{
   if( t. sel( ) == op_debruijn )
   {
      size_t ind = t. view_debruijn( ). index( );
      if( ind >= vardepth )
      {
         ++ used;

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
logic::normalizer::operator( ) ( term t, size_t vardepth ) 
{
   // std::cout << t << " / " << vardepth << "\n";

   if( t. sel( ) == op_debruijn )
   {  
      size_t ind = t. view_debruijn( ). index( );
      if( ind >= vardepth )
      {
         ++ used; 
         ind -= vardepth;

         if( ind < border )
         {
            // Promises O( log( used. size( )) ) complexity:

            auto p = std::lower_bound( freevars. begin( ), 
                                       freevars. end( ), ind );
            if( p == freevars. end( ) || *p != ind )
               throw std::logic_error( "normalizer: variable not found" );

            ind = p - freevars. begin( ); 
         }
         else
         {
            ind += ( freevars. size( ) - border );
         }

         return term( op_debruijn, ind + vardepth ); 
      }
   }
   return t; 
}


void logic::normalizer::print( std::ostream& out ) const
{
   out << "Normalizer(" << border << "):\n";
   for( size_t i = 0; i < freevars. size( ); ++ i )
   {
      out << "   #" << freevars[i] << " := #" << i << "\n"; 
   }
}

logic::term 
logic::betareduction::operator( ) ( term t, size_t vardepth ) 
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

         ++ used;

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
  out << "betareduction(" << used << ")";
}


logic::term
logic::decurrier::operator( ) ( term t, size_t vardepth )
{
   if( t. sel( ) == op_apply )
   {
      auto ap1 = t. view_apply( );
      if( ap1. func( ). sel( ) == op_apply )
      {
         auto res = ap1. extr_func( );   
         auto ap2 = res. view_apply( );
         
         for( size_t i = 0; i != ap1. size( ); ++ i )
            ap2. push_back( ap1. extr_arg(i));

         ++ used; 
         return res;
      }
   }   
   return t; 
}

void logic::decurrier::print( std::ostream& out ) const
{
   out << "decurrier("<< used << ")";
}

logic::term
logic::simplifier::operator( ) ( term t, size_t vardepth )
{
   if( t. sel( ) == op_not )
   {
      const auto& sub = t. view_unary( ). sub( ); 
      if( sub. sel( ) == op_false )
      {
         ++ used; 
         return term( op_true );
      }

      if( sub. sel( ) == op_error )
      {
         ++ used; 
         return term( op_error );
      }

      if( sub. sel( ) == op_true )
      {
         ++ used; 
         return term( op_false ); 
      }
   }

   if( t. sel( ) == op_exists )
   {
      const auto& sub = t. view_quant( ). body( );
      if( sub. sel( ) == op_false )
      {
         ++ used; 
         return term( op_false );
      }
   }

   if( t. sel( ) == op_forall )
   {
      const auto& sub = t. view_quant( ). body( );
      if( sub. sel( ) == op_true )
      {
         ++ used; 
         return term( op_true );
      }
   }

   if( t. sel( ) == op_equals )
   {
      auto bin = t. view_binary( );
      if( equal( bin. sub1( ), bin. sub2( )))
      {  
         ++ used;   
         return term( op_true );
      }
   }
  
   return t;
}


void logic::simplifier::print( std::ostream& out ) const
{
   out << "simplifier(" << used << ")";
}

logic::term
logic::rewriterule::operator( ) ( term t, size_t vardepth ) 
{
   if( equal( from, vardepth, t, 0, 0 ))
   {
      ++ used;
      return lift( to, vardepth );
   }

   return t;
}

void
logic::rewriterule::print( std::ostream& out ) const
{
   out << "rewrite rule: " << from << " --> " << to << "\n";
}


