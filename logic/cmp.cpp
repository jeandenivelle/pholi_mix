
#include "cmp.h"
#include "counters.h"

logic::weight_type logic::weight( const type& tp )
{
   switch( tp. sel( )) 
   {
   case type_form:
   case type_obj:
      return 1;
   case type_struct:
      return 1;
   case type_unchecked:
      return 1; 
   case type_func:
      {
         auto f = tp. view_func( ); 
         weight_type w = weight( f. result( ));
         for( size_t i = 0; i != f. size( ); ++ i )
            w += weight( f. arg(i));
         return w + 1; 
      }
   }

   std::cout << "the selector is " << tp. sel( ) << "\n";
   throw std::logic_error( "wrong selector in type" );  
}


namespace logic
{
   namespace 
   {
      struct weight_counter
      {
         weight_type val;

         weight_counter( ) noexcept : val(0) 
            { }

         void operator( ) ( const term& tm, size_t vardepth ) 
         { 
            if( tm. option_is_lambda( ))
            {
               val += tm. view_lambda( ). size( ); 
               return;  
            }

            if( tm. option_is_quant( ))
            {
               val += tm. view_quant( ). size( );
               return;
            }

            val += 1;
         }
      };
   }
}

logic::weight_type logic::weight( const term& t ) 
{
   weight_counter cnt;

   traverse( cnt, t, 0 );
   return cnt. val; 
}


std::strong_ordering 
logic::operator <=> ( const type& tp1, const type& tp2 ) 
{
   // Selector is still an enum type:

   if( auto c = ( tp1. sel( ) <=> tp2. sel( )); !is_eq(c)) 
      return c;

   switch( tp1. sel()) 
   {
   case type_form:
   case type_obj:
      return std::strong_ordering::equal;

   case type_struct:
      {
         exact name1 = tp1. view_struct( ). def( );
         exact name2 = tp2. view_struct( ). def( );
         return name1 <=> name2;
      } 
  
   case type_unchecked:
      { 
         const identifier& id1 = tp1. view_unchecked( ). id( );
         const identifier& id2 = tp2. view_unchecked( ). id( ); 
         return id1 <=> id2;
      }

   case logic::type_func:
      {
         auto func1 = tp1. view_func( );
         auto func2 = tp2. view_func( );

         if( auto c = func1. result( ) <=> func2. result( ); !is_eq(c))
            return c;

         if( auto c = func1. size( ) <=> func2. size( ); !is_eq(c))
            return c;

         for( size_t i = 0; i < func1. size( ); ++i ) 
         {
            if( auto c = ( func1. arg(i) <=> func2. arg(i) ); !is_eq(c))
               return c;
         }

         return std::strong_ordering::equal;
      }

   default:
      std::cout << "the selector is " << tp1. sel( ) << "\n";
      throw std::logic_error("unknown selector in operator <=>");
   }
}


std::strong_ordering
logic::operator <=> ( const term& t1, const term& t2 ) 
{
   // std::cout << t1 << " <=> " << t2 << "\n";

   // Selector is still an enum type:

   if( auto c = ( t1. sel( ) <=> t2. sel( )); !is_eq(c))
      return c;

   switch( t1.sel( )) 
   {
   case op_exact:
      return t1.view_exact( ).ex( ) <=> t2.view_exact( ).ex( );

   case op_debruijn:
      return t1.view_debruijn( ).index( ) <=> t2.view_debruijn( ).index( ); 

   case op_unchecked:
      return t1.view_unchecked( ).id( ) <=> t2.view_unchecked( ).id( );

   case op_false:
   case op_error:
   case op_true:
      return std::strong_ordering::equal;

   case op_not:
   case op_prop:
      return t1.view_unary( ).sub( ) <=> t2.view_unary( ).sub( );

   case op_and: 
   case op_or:
   case op_implies:
   case op_equiv:
   case op_lazy_and:
   case op_lazy_implies:
   case op_meta_implies:
      {
         auto bin1 = t1. view_binary( );
         auto bin2 = t2. view_binary( );

         if( auto c = ( bin1.sub1( ) <=> bin2.sub1( ) ); !is_eq(c)) 
            return c;
         return ( bin1.sub2( ) <=> bin2.sub2( ) );
      } 

   case op_equals:
      {
         // We need to consider commutativity of equality.

         auto eq1 = t1. view_binary( );
         auto eq2 = t2. view_binary( );

         // We use some trickery, we sort the equalities:

         std::pair< const term* , const term* > decr1 =
            is_gt( eq1. sub1( ) <=> eq1. sub2( )) ?
               std::pair( &eq1.sub1( ), &eq1.sub2( )) :
               std::pair( &eq1.sub2( ), &eq1.sub1( ));

         std::pair< const term* , const term* > decr2 =
            is_gt( eq2. sub1( ) <=> eq2. sub2( )) ?
               std::pair( &eq2.sub1( ), &eq2.sub2( )) :
               std::pair( &eq2.sub2( ), &eq2.sub1( ));

         // First compare the bigger elements:

         if( auto c = *decr1. first <=> *decr2. first; !is_eq(c))
            return c; 
      
         // Otherwise, we compare the smaller ones:

         if( auto c = *decr1. second <=> *decr2. second; !is_eq(c))
            return c;

         // The job is finished.

         return std::strong_ordering::equal; 
      }

   case op_forall:
   case op_exists:
      {
         auto quant1 = t1. view_quant( );
         auto quant2 = t2. view_quant( );

         if( auto c = quant1. size( ) <=> quant2. size( ); !is_eq(c))
            return c;

         for( size_t i = 0; i != quant1. size( ); ++ i )
         {
            if( auto c = quant1.var(i).tp <=> quant2.var(i).tp; !is_eq(c))
               return c;
         }

         return quant1. body( ) <=> quant2. body( );
      }

   case op_let:
      {
         auto let1 = t1. view_let( );
         auto let2 = t2. view_let( );

         if( auto c = let1.var( ).tp <=> let2.var( ).tp; !is_eq(c))
            return c;
         if( auto c = let1.val( ) <=> let2.val( ); !is_eq(c))
            return c;
         return let1.body( ) <=> let2.body( );
      }

   case op_apply: 
      {
         auto ap1 = t1. view_apply( );
         auto ap2 = t2. view_apply( );

         if( auto c = ap1.func( ) <=> ap2.func( ); !is_eq(c))
            return c;

         if( auto c = ap1. size( ) <=> ap2. size( ); !is_eq(c))
            return c;

         for( size_t i = 0; i != ap1. size( ); ++ i )
         {
            if( auto c = ap1.arg(i) <=> ap2.arg(i); !is_eq(c))
               return c; 
         }

         return std::strong_ordering::equal;
      } 

   case op_lambda:
      {
         auto lamb1 = t1. view_lambda( );
         auto lamb2 = t2. view_lambda( );

         if( auto c = lamb1. size( ) <=> lamb2. size( ); !is_eq(c))
            return c;

         for( size_t i = 0; i != lamb1. size( ); ++ i )
         {
            if( auto c = lamb1.var(i).tp <=> lamb2.var(i).tp; !is_eq(c))
               return c;
         }

         return lamb1.body( ) <=> lamb2.body( );
      }

   }

   std::cout << t1. sel( ) << "\n";
   throw std::logic_error( "operator <=>: operator not implemented" ); 
}

bool
logic::equal( const term& t1, size_t lift1,
              const term& t2, size_t lift2, size_t vardepth )
{
   // std::cout << t1 << " / " << lift1 << " == ";
   // std::cout << t2 << " / " << lift2 << " [" << vardepth << "]?\n";

   if( t1. sel( ) != t2. sel( ) )
      return false;

   switch( t1. sel( ))
   {
   case op_exact:
      return t1. view_exact( ). ex( ) == t2. view_exact( ). ex( );

   case op_debruijn:
      {
         size_t ind1 = t1. view_debruijn( ). index( );
         size_t ind2 = t2. view_debruijn( ). index( );

         if( ind1 >= vardepth )
            ind1 += lift1;

         if( ind2 >= vardepth )
            ind2 += lift2;

         return ind1 == ind2;
      }

   case op_unchecked:
      return t1. view_unchecked( ). id( ) == t2. view_unchecked( ). id( );

   case op_false:
   case op_error:
   case op_true:
      return true;

   case op_not:
   case op_prop:
      {
         auto un1 = t1. view_unary( );
         auto un2 = t2. view_unary( );
         return equal( un1. sub( ), lift1, un2. sub( ), lift2, vardepth );
      }

   case op_and:
   case op_or:
   case op_implies:
   case op_equiv:
   case op_lazy_and:
   case op_lazy_implies:
   case op_meta_implies:
      {
         auto bin1 = t1. view_binary( );
         auto bin2 = t2. view_binary( );
         if( !equal( bin1. sub1( ), lift1, bin2. sub1( ), lift2, vardepth ))
            return false;
         return equal( bin1. sub2( ), lift1, bin2. sub2( ), lift2, vardepth );
      }

   case op_equals:
      {
         // equals is separate because
         // we consider commutativity of equality:
         
         auto eq1 = t1. view_binary( );
         auto eq2 = t2. view_binary( );

         if( equal( eq1. sub1( ), lift1, eq2. sub1( ), lift2, vardepth ) &&
             equal( eq1. sub2( ), lift1, eq2. sub2( ), lift2, vardepth ))
         {
            return true;
         }

         return equal( eq1. sub1( ), lift1, eq2. sub2( ), lift2, vardepth ) &&
                equal( eq1. sub2( ), lift1, eq2. sub1( ), lift2, vardepth );
      }

   case op_forall:
   case op_exists:
      {
         auto quant1 = t1. view_quant( );
         auto quant2 = t2. view_quant( );

         if( quant1. size( ) != quant2. size( ))
            return false;

         for( size_t i = 0; i != quant1. size( ); ++ i )
         {
            if( !equal( quant1.var(i).tp, quant2.var(i).tp ))
               return false;
         }

         return equal( quant1. body( ), lift1, 
                       quant2. body( ), lift2, vardepth + quant1. size( ));
      }

   case op_let:
      {
         auto let1 = t1. view_let( );
         auto let2 = t2. view_let( );

         if( !equal( let1.var( ).tp, let2.var( ).tp ))
            return false;
         if( !equal( let1.val( ), lift1, let2.val( ), lift2, vardepth ))
            return false;
         return  equal( let1.body( ), lift1, let2.body( ), lift2, 
                        vardepth + 1 );
      }

   case op_apply:
      {
         auto ap1 = t1. view_apply( );
         auto ap2 = t2. view_apply( );

         if( ap1. size( ) != ap2. size( ))
            return false;

         for( size_t i = 0; i != ap1. size( ); ++ i )
         {
            if( !equal( ap1.arg(i), lift1, ap2.arg(i), lift2, vardepth ))
               return false;
         }

         return equal( ap1.func( ), lift1, ap2.func( ), lift2, vardepth );
      }

   case op_lambda:
      {
         auto lamb1 = t1. view_lambda( );
         auto lamb2 = t2. view_lambda( );

         if( lamb1. size( ) != lamb2. size( ))
            return false;

         for( size_t i = 0; i != lamb1. size( ); ++ i )
         {
            if( !equal( lamb1.var(i).tp, lamb2.var(i).tp ))
               return false;
         }

         return equal( lamb1.body( ), lift1, lamb2.body( ), lift2, 
                       vardepth + lamb1. size( ));
      }

   }

   std::cout << t1. sel( ) << "\n";
   throw std::logic_error( "equal: operator not implemented" );
}


std::strong_ordering 
logic::kbo( const term& tm1, const term& tm2 )
{
   weight_type w1 = weight( tm1 );
   weight_type w2 = weight( tm2 );

   if( auto c = w1 <=> w2; !is_eq(c))
      return c;

   return tm1 <=> tm2;
}


// Why is this not in STL? chren etogo znayet:

std::ostream&
logic::operator << ( std::ostream& out, std::strong_ordering ord )
{
   if( is_lt( ord ))
   {
      out << "lt"; return out;
   }

   if( is_gt( ord ))
   {
      out << "gt"; return out; 
   }

   if( is_eq( ord ))
   {
      out << "eq"; return out;
   }

   out << "???"; return out;
}

