
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

#if 0

semantics::value 
semantics::eval( interpretation& interpr, const logic::term& t )
{
   std::cout << "Eval:\n";
   std::cout << interpr << "\n";
   std::cout << t << "\n";

   using namespace logic;
   switch( t. sel( ))
   {
   case op_debruijn:
      {
         auto db = t. view_debruijn( ); 
         const auto& f = interpr. local( db. index( )); 
         return f( {} );
      }
#if 0
        case op_true:
           return tt;
        case op_false:
            return ff;
        case op_error:
            return ee;
        case op_not:
            return TABLE_NOT[ eval( interpr, t. view_unary( ). sub( ) ) ];
        case op_prop: 
           return TABLE_PROP[ eval(interpr, t.view_unary().sub()) ];
#endif 
#if 0
        case op_lazy_and:
            return TABLE_AND[ eval(interpr, t. view_binary().sub1()) ][ eval( interpr, t.view_binary().sub2() ) ];
        case op_or:
        case op_lazy_or: // TODO : op_lazy_or is the same as op_or?
            return TABLE_OR[ eval(interpr, t. view_binary().sub1()) ][ eval( interpr, t.view_binary().sub2() ) ];
        case op_equiv:
            return TABLE_EQUIV[ eval(interpr, t. view_binary().sub1()) ][ eval( interpr, t.view_binary().sub2() ) ];
#endif

   case op_forall:
   case op_kleene_forall:
   case op_exists:
   case op_kleene_exists: 
      {
         const auto bottom = lattice::bottom( t. sel( ));
         auto current = lattice::top( t. sel( ));
         update_quant( current, bottom, interpr, t, 0 ); 
         return current; 
      }
   case op_apply:
      {
         auto a = t. view_apply( );
         const auto& f = eval_func( interpr, a. func( )); 
         std::vector< value > args;
         for( size_t i = 0; i != a. size( ); ++ i )
            args. push_back( eval( interpr, a. arg(i)) );
         return f( args );  
      }
   }
   std::cout << t. sel( ) << "\n";
   throw std::logic_error( "dont know how to evaluate" );
}

void
semantics::update_quant( value& current, const value& worst,
                         interpretation& interpr, 
                         const logic::term& quant, size_t ind )
{
   std::cout << "eval quant: " << quant << "\n";
   std::cout << "ind = " << ind << "\n";
   auto q = quant. view_quant( );

   if( ind < q. size( ))
   {
      function& f = 
         interpr. push( zero_function( q. var( ind). tp, interpr. nrobjects ));

      if( f. can_exist( ))
      {
         bool first = true;
         while( first || !f. allzeroes( ))
         {
            update_quant( current, worst, interpr, quant, ind + 1 );
            if( current == worst )
            {
               interpr. pop( );
               return; 
            } 
       
            ++ f;
            first = false;
         }
      }
      interpr. pop( ); 
      return; 
   }
   else
   {
      auto val = eval( interpr, q. body( )); 
      current = lattice::merge( quant. sel( ), current, val );  
   }
}

const semantics::function&
semantics::eval_func( interpretation& interpr, const logic::term& t )
{
   std::cout << "Eval func " << t << "\n";
   switch( t. sel( ))
   {
   case logic::op_unchecked:
      return interpr. at( t. view_unchecked( ). id( ));    
   case logic::op_debruijn:
      return interpr. local( t. view_debruijn( ). index( )); 
   }
   throw std::logic_error( "dont know how to evaluate function" ); 
}

namespace
{
   std::pair< semantics::primtype, unsigned int > 
   convtype( logic::selector sel, unsigned int nrobjects )
   {
      if( sel == logic::type_obj )
         return { semantics::prim_obj, nrobjects };

      if( sel == logic::type_form )
         return { semantics::prim_truthval, 3 };

      throw std::logic_error( "cannot convert type" );
   }
}

semantics::function 
semantics::zero_function( logic::type tp, unsigned int nrobjects )
{
   std::vector< std::pair< primtype, unsigned >> argtypes;
 
   while( tp. sel( ) == logic::type_func )
   {
      auto f = tp. view_func( );
      for( size_t i = 0; i != f. size( ); ++ i )
         argtypes. push_back( convtype( f. arg(i). sel( ), nrobjects ));
      tp = f. result( ); 
   }

   return function( std::move( argtypes ), convtype( tp. sel( ), nrobjects )); 
}

void 
semantics::check_preceq( std::vector< identtype > :: const_iterator id1,
                         std::vector< identtype > :: const_iterator id2, 
                         const logic::term& from, const logic::term& into,
                         interpretation& interpr )
{
   std::cout << "entering check_preceq:\n";
 
   if( id1 != id2 )
   {
      std::cout << *id1 << "\n";
      function& f = interpr. extend( id1 -> id, 
                             zero_function( id1 -> tp, interpr. nrobjects ));

      if( f. can_exist( ))
      {
         ++ id1;
         bool first = true;
         while( first || !f. allzeroes( ))
         {
            std::cout << f << "\n";

            ++ f;
            first = false;
            check_preceq( id1, id2, from, into, interpr );  
         }
         -- id1;
         interpr. retract( id1 -> id );  
      }
      else
         throw std::runtime_error( "range is empty" );
   }
   else
   {
      std::cout << interpr << "\n";
      value from_val = eval( interpr, from );
      value into_val = eval( interpr, into );

      std::cout << "from val " << from_val << "\n";
      std::cout << "into val " << into_val << "\n";

      // if( from_val != into_val )
      //   throw std::runtime_error( "equivalence failed" );

      if( !preceq( from_val, into_val ))
         throw std::runtime_error( "preceq failed" );
   }
}

#endif

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
         {
            std::cout << intp; 
            return eval( intp, q. body( ));  
         }
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


