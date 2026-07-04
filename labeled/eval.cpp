
#include "eval.h"


natded::truthval natded::operator ! ( truthval tv )
{
   switch( tv )
   {
   case ffff:
      return tttt;
   case eeee:
      return eeee;
   case tttt:
      return ffff; 
   }
   std::abort( );
}

natded::truthval natded::prop( truthval tv )
{
   if( tv == eeee )
      return ffff;

   return tttt;
}

natded::truthval natded::operator && ( truthval tv1, truthval tv2 )
{
   if( tv1 == eeee || tv2 == eeee )
      return eeee;
   if( tv1 == ffff || tv2 == ffff )
      return ffff;
   return tttt;
}

natded::truthval natded::operator || ( truthval tv1, truthval tv2 )
{
   if( tv1 == eeee || tv2 == eeee )
      return eeee;
   if( tv1 == tttt || tv2 == tttt )
      return tttt;
   return ffff;
}

natded::truthval natded::implies( truthval tv1, truthval tv2 )
{
   if( tv1 == eeee || tv2 == eeee )
      return eeee;
   if( tv1 == ffff || tv2 == tttt )
      return tttt;
   return ffff;
}

natded::truthval natded::equiv( truthval tv1, truthval tv2 )
{
   if( tv1 == eeee || tv2 == eeee )
      return eeee;

   if( tv1 == tv2 )
      return tttt;
   else
      return ffff;
}

natded::truthval natded::lazy_and( truthval tv1, truthval tv2 )
{
   if( tv1 != tttt )
      return tv1; 
   return tv2;
}

natded::truthval natded::lazy_implies( truthval tv1, truthval tv2 )
{
   if( tv1 == ffff )
      return tttt;
   if( tv1 == eeee )
      return eeee;
   return tv2;
}

natded::truthval natded::meta_implies( truthval tv1, truthval tv2 )
{
   if( tv1 != tttt )
      return tttt;
   if( tv2 != tttt )
      return ffff;
   return tttt;
}


namespace natded
{
   namespace
   {
      template< typename Q >
      truthval eval( interpretation& intp, 
                     logic::selector sel,
                     const Q& q, size_t pos )
      {
         if( pos < q. size( ))
         {
            if( q. var( pos ). tp. sel( ) != logic::type_form )
            {
               std::cout << q. var( pos ). tp << "\n";
               throw std::logic_error( "eval : type is not F" );
            }

            size_t ss = intp. size( ); 

            // As soon as we see an error, we are out:

            intp. append( eeee );
            truthval res1 = eval( intp, sel, q, pos + 1 );
            intp. restore( ss );

            if( res1 == eeee )
               return res1;

            intp. append( ffff );
            truthval res2 = eval( intp, sel, q, pos + 1 );
            intp. restore( ss );

            if( res2 == eeee )
               return res2;

            intp. append( tttt );
            truthval res3 = eval( intp, sel, q, pos + 1 );
            intp. restore( ss );

            if( res3 == eeee )
               return res3;

            if( sel == logic::op_forall )
            {
               if( res1 == tttt && res2 == tttt && res3 == tttt )
                  return tttt;
               else
                  return ffff;
            }

            if( sel == logic::op_exists )
            {
               if( res1 == tttt || res2 == tttt || res3 == tttt )
                  return tttt;
               else
                  return ffff;
            }

            throw std::logic_error( "problem in quantifier" );
         }
         else
            return eval( intp, q. body( ));  
      }

   }
}

natded::truthval
natded::eval( interpretation& intp, const logic::term& fm ) 
{

   switch( fm. sel( ))
   {
   case logic::op_false:
      return ffff;

   case logic::op_error:
      return eeee;

   case logic::op_true:
      return tttt;

   case logic::op_debruijn:
      {
         size_t ind = fm. view_debruijn( ). index( );
         if( ind >= intp. size( ))
            throw std::out_of_range( "eval: De Bruijn index too high" );
         return intp. getvalue( ind ); 
      }

   case logic::op_not:
      {
         auto un = fm. view_unary( );
         return ! eval( intp, un. sub( ));
      }

   case logic::op_prop:
      {
         auto un = fm. view_unary( );
         return prop( eval( intp, un. sub( )) ); 
      }

   case logic::op_and:
      {
         auto bin = fm. view_binary( );
         return eval( intp, bin. sub1( )) && eval( intp, bin. sub2( ));
      }

   case logic::op_or:
      {
         auto bin = fm. view_binary( );
         return eval( intp, bin. sub1( )) || eval( intp, bin. sub2( ));
      }

   case logic::op_implies:
      {
         auto bin = fm. view_binary( ); 
         return implies( eval( intp, bin. sub1( )),
                         eval( intp, bin. sub2( )) );
      }

   case logic::op_equiv:
      {
         auto bin = fm. view_binary( );
         return equiv( eval( intp, bin. sub1( )),
                       eval( intp, bin. sub2( )) );
      }

   case logic::op_lazy_and:
      {
         auto bin = fm. view_binary( );
         return lazy_and( eval( intp, bin. sub1( )),
                          eval( intp, bin. sub2( )) );
      }

   case logic::op_lazy_implies:
      {
         auto bin = fm. view_binary( ); 
         return lazy_implies( eval( intp, bin. sub1( )), 
                              eval( intp, bin. sub2( )) );
      }

   case logic::op_meta_implies:
      {
         auto bin = fm. view_binary( );
         return meta_implies( eval( intp, bin. sub1( )),
                              eval( intp, bin. sub2( )) );
      }

   case logic::op_equals: 
      {
         // Equality is not type correct, but useful to have:

         auto bin = fm. view_binary( );
         if( eval( intp, bin. sub1( )) == eval( intp, bin. sub2( )) )
            return tttt;
         else
            return ffff;
      }

   case logic::op_forall:
   case logic::op_exists:
      {
         auto qnt = fm. view_quant( );
         return eval( intp, fm. sel( ), qnt, 0 );
      }
   }

   std::cout << fm. sel( ) << "\n";
   throw std::logic_error( "don't know how to evaluate" );
}


