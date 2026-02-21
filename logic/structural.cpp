
#include "structural.h"
#include "pretty.h"
#include "cmp.h"

void 
logic::checkformula( const beliefstate& blfs, 
                     const identifier& name, term& fm, 
                     const char* descr, errorstack& err )
{
   const size_t errstart = err. size( );

   fm = replace_debruijn( std::move( fm ));
   auto tp = checkandresolve( blfs, err, fm );

   if( tp. has_value( ) && tp. value( ). sel( ) != type_form )
   {
      errorstack::builder bld;
      bld << "Formula " << name << " does not have type Form. ";
      bld << "Instead it has type ";
      pretty::print( bld, blfs, tp. value( ), {0,0} );
      err. push( std::move( bld )); 
   }

   if( err. size( ) > errstart )
   {
      errorstack::builder bld;
      bld << "In " << descr << " " << name << ": ";
      err. addheader( errstart, std::move( bld ));
   }
}


void logic::checkandresolve( beliefstate& everything, errorstack& err )
{
   // The identifiers that have a repeated struct definition,
   // that we already complained about. It is a bit tricky
   // to get out the exact identifier. If it would be easier,
   // we could check that we are the first overload.

   std::unordered_set< identifier, identifier::hash, identifier::equal_to > 
      complained;

   for( const auto& blf : everything )
   {
      if( blf. sel( ) == bel_struct )
      {
         const auto& id = blf. ident( );
         const auto& sdef = everything. getstructdefs( id );

         if( sdef. size( ) > 1 && !complained. contains( id ))
         {
            errorstack::builder bld;
            bld << "identifier " << id << " has " << sdef. size( ); 
            bld << " struct-defs: ";
            for( auto p = sdef. begin( ); p != sdef. end( ); ++ p )
            {
               if( p != sdef. begin( ))
                  bld << ", ";
               bld << *p;
            }
            err. push( std::move( bld ));

            complained. insert( id );
         }

      }
   }      
   complained. clear( );

   // We check that certain identifiers are not used as
   // struct:

   const static identifier F = identifier( ) + "Form";
   const static identifier O = identifier( ) + "Obj";

   for( const auto& blf : everything )
   {
      if( blf. sel( ) == bel_struct )
      {
         const auto& id = blf. ident( );
         if( id == F || id == O )
         {
            errorstack::builder bld;
            bld << "identifier cannot be used for a struct def: " << id;
            err. push( std::move( bld ));
         }
      }
   }

   // We check and overload structural types:

   for( auto& blf : everything )
   {
      size_t errstart = err. size( );

      switch( blf. sel( ))
      {
      case bel_struct:
         {
            auto str = blf. view_struct( ). extr_def( );
               // We need to extract the complete structdef. Frightening! 

            for( auto& fld : str )
            {
               size_t errstartfield = err. size( );
 
               checkandresolve( everything, err, fld. tp );
               if( err. size( ) > errstartfield ) 
               {
                  errorstack::builder bld;
                  bld << "In type of field " << fld. name << ":";
                  err. addheader( errstartfield, std::move( bld ));
               }
            }

            blf. view_struct( ). update_def( std::move( str ));
 
            if( err. size( ) > errstart )
            {
                errorstack::builder bld;
                bld << "In a definition of struct " << blf. ident( ) << ":";
                err. addheader( errstart, std::move( bld ));
            }
         }
         break;

      case bel_symbol:
         {
            auto sym = blf. view_symbol( );
            auto tp = sym. extr_tp( );
            checkandresolve( everything, err, tp ); 
            sym. update_tp( tp );

            if( err. size( ) > errstart )
            {
               errorstack::builder bld;
               bld << "In a declaration of symbol " << blf. ident( ) << ":";
               err. addheader( errstart, std::move( bld ));
            }
         }
         break;

      case bel_def:
         {
            // We check the type, but not the term:

            auto def = blf. view_def( );
            {
               auto tp = def. extr_tp( );
               checkandresolve( everything, err, tp );
               def. update_tp( tp );
            }

            if( err. size( ) > errstart )
            {
               errorstack::builder bld;
               bld << "In a definition of " << blf. ident( ) << ":";
               err. addheader( errstart, std::move( bld ));
            }
         }
         break;

      case bel_fld:
         {
            // There is not much to check because field functions
            // are automatically generated from struct definitions:

            auto sdef = blf. view_field( ). sdef( );
            if( everything. at( sdef ). sel( ) != bel_struct )
            {
               // This actually means that the data structure is rotten:

               throw std::logic_error( "field does not refer to struct" );
            }
         }
         break; 

      case bel_constr:
         {
            // Again, there is not much to check.

            auto sdef = blf. view_constr( ). tp( );
            if( everything. at( sdef ). sel( ) != bel_struct )
            {
               // This means that the data structure is corrupted:
               throw std::runtime_error( "constr does not construct struct" );
            }            
         }
         break;
      }
   }

   // Finally, we type check terms:

   for( auto& blf : everything )
   {
      size_t errstart = err. size( );

      switch( blf. sel( ))
      {
      case bel_def:
         {
            auto def = blf. view_def( );
            auto tm = def. extr_val( );

            tm = replace_debruijn( std::move(tm));
            auto tp = checkandresolve( everything, err, tm );
            def. update_val( tm );

            if( tp. has_value( ) && !equal( tp. value( ), def. tp( )))
            {
               errorstack::builder bld;
               bld << "Declared type differs from true type:\n";
               bld << "Declared :   "; 
               pretty::print( bld, everything, def. tp( ), {0,0} );
               bld << "\n";
               bld << "True :   ";
               pretty::print( bld, everything, tp. value( ), {0,0} ); 
               err. push( std::move( bld ));   
            }

            if( err. size( ) > errstart )
            {
               errorstack::builder bld;
               bld << "In a definition of " << blf. ident( ) << ":";
               err. addheader( errstart, std::move( bld ));
            }
         }
         break; 

      case bel_axiom:
      case bel_thm:
         {
            auto f = blf. view_form( ); 
            term fm = f. extr_fm( );
            checkformula( everything, blf. ident( ), fm, "formula", err );
            {
               auto univ = fm;
               while( univ. sel( ) == op_forall )
               {
                  auto all = univ. view_quant( );
                  for( size_t i = 0; i != all. size( ); ++ i )
                     f. push_back( all. var(i). tp );
                  univ = all. body( );
               }
            }
            f. update_fm( fm );
         }
         break; 

      } 
   
   }

}


#if 0

logic::correctness
logic::checkproofterm( std::ostream& out, const beliefstate& state, 
                       const term& proof, size_t cutoff )
{
   correctness corr;

   checker check( &state, cutoff, proof );

   context ctxt;
   position pos;
}

#endif


logic::term
logic::replace_debruijn( indexedstack< std::string, size_t > & db, term t )
{
   if constexpr( false )
   {
      std::cout << "replacing De Bruijn:\n";
      std::cout << db << "\n";
      std::cout << t << "\n";
   }

   static const identifier ff = identifier( ) + "FF";
   static const identifier ee = identifier( ) + "EE";
   static const identifier tt = identifier( ) + "TT";

   switch ( t. sel( ))
   {
   case op_debruijn:
      return t;

   case op_unchecked:
      {
         auto un = t. view_unchecked( );
         const auto& id = un. id( );

         if( id == ff )
            return logic::term( op_false );
         if( id == ee )
            return logic::term( op_error );
         if( id == tt )
            return logic::term( op_true );
 
         if( id. size( ) != 1 )
            return t;
 
         auto p = db. find( id. at(0));  
         if( p != db. end( )) 
            return term( op_debruijn, db. size( ) - ( p -> second ) - 1 );

         return t;
      }
   case op_not:
   case op_prop:
      {
         auto un = t. view_unary( );
         un. update_sub( replace_debruijn( db, un. extr_sub( )));
         return t;
      }
   case op_and:
   case op_or:
   case op_implies:
   case op_equiv:
   case op_lazy_and:
   case op_lazy_implies: 
   case op_meta_implies:
   case op_equals:
      {
         auto bin = t. view_binary( );
         bin. update_sub1( replace_debruijn( db, bin. extr_sub1( )));
         bin. update_sub2( replace_debruijn( db, bin. extr_sub2( )));
         return t;
      }
   case op_forall:
   case op_exists:
      {
         size_t dbsize = db. size( );

         auto quant = t. view_quant( );
         for( size_t i = 0; i != quant. size( ); ++ i )
            db. push( quant. var(i). pref, db. size( ));  
 
         quant. update_body( replace_debruijn( db, quant. extr_body( )));
        
         db. restore( dbsize );
         return t;
      }

   case op_let:
      {
         auto let = t. view_let( ); 

         let. update_val( replace_debruijn( db, let. extr_val( )));
         
         size_t dbsize = db. size( );

         db. push( let. var( ). pref, db. size( ));
         let. update_body( replace_debruijn( db, let. extr_body( )));

         db. restore( dbsize ); 
         return t; 
      }

   case op_apply:
      {
         auto ap = t. view_apply( );
         
         ap. update_func( replace_debruijn( db, ap. extr_func( )));
         for( size_t i = 0; i != ap. size( ); ++ i )
            ap. update_arg( i, replace_debruijn( db, ap. extr_arg(i) ));

         return t;
      }
 
   case op_lambda:
      {
         size_t dbsize = db. size( );

         auto lamb = t. view_lambda( );
         for( size_t i = 0; i != lamb. size( ); ++ i )
            db. push( lamb. var(i). pref, db. size( ));  
      
         lamb. update_body( replace_debruijn( db, lamb. extr_body( ))); 

         db. restore( dbsize );
         return t;
      }

   }

   std::cout << t. sel( ) << "\n";
   throw std::logic_error( "replace De Bruijn: unhandled selector" ); 
}

logic::term logic::replace_debruijn( term t ) 
{
   indexedstack< std::string, size_t > debruijn;
   t = replace_debruijn( debruijn, std::move(t));

   if( debruijn. size( ) > 0 )
      throw std::logic_error( "non-empty De Bruijn stack after check" );

   return t;
}

bool 
logic::checkandresolve( const beliefstate& blfs, errorstack& errors, type& tp ) 
{
   if constexpr( false )
   {
      std::cout << "checking type ";
      pretty::print( std::cout, blfs, tp, {0,0} );
      std::cout << "\n";
   }

   const static identifier F = identifier( ) + "Form";
   const static identifier O = identifier( ) + "Obj";
 
   switch( tp. sel( ))
   {
   case type_form:
   case type_obj:
      return true;
 
   case type_unchecked:
      {
         auto id = tp. view_unchecked( );
         auto& defs = blfs. getstructdefs( id. id( ));

         if( id. id( ) == O )
         {
            tp = type( type_obj );
            return true;
         }

         if( id. id( ) == F )
         {
            tp = type( type_form );
            return true;
         }
 
         if( defs. size( ) == 0 ) 
         {
            errorstack::builder bld;

            bld << "identifier without struct-def used as type: ";
            bld << id. id( ); 
            errors. push( std::move( bld ));

            return false;
         }

         if( defs. size( ) > 1 )
         {
            errorstack::builder bld;

            bld << "identifier used as type has " << defs. size( );
            bld << " struct-defs: ";
            bld << id. id( ); 
            errors. push( std::move( bld ));

            return false;
         }

         tp = type( type_struct, defs[0] );
         return true;
      }

   case type_func:
      {
         bool correct = true; 

         auto func = tp. view_func( );
         {
            type res = func. extr_result( );
            if( !checkandresolve( blfs, errors, res ))
               correct = false;

            func. update_result( res );
         }
           
         for( size_t i = 0; i != func. size( ); ++ i )
         {
            type arg = func. extr_arg(i);
            if( !checkandresolve( blfs, errors, arg ))
               correct = false;

            func. update_arg( i, arg );
         }
         return correct;
      }
   } 
   std::cout << "checkandresolve: " << tp. sel( ) << "\n";
   throw std::runtime_error( "not implemented for this case" );
}

std::optional< logic::type >
logic::checkandresolve( const beliefstate& blfs, errorstack& errors,
                        term& t )
{
   context ctxt;
   auto tp = checkandresolve( blfs, errors, ctxt, t );
   if( ctxt. size( ) > 0 )
      throw std::logic_error( "non empty context after type check" );
   return tp;
}

namespace logic
{
   namespace
   {
      errorstack::builder errorheader( const beliefstate& blfs,
                                       context& ctxt, 
                                       const term& t )
      {
         errorstack::builder res;
         res << '\n';
         for( unsigned int i = 0; i != 70; ++ i )
            res. put( '-' );
         res. put( '\n' );
 
         auto un = pretty::print( res, blfs, ctxt );
         res << "Term:\n   ";
         pretty::print( res, blfs, un, t, {0,0} );
         res << "\n";
         return res; 
      }
   }
}


std::optional< logic::type > 
logic::checkandresolve( const beliefstate& blfs, errorstack& errors,  
                        context& ctxt, term& t ) 
{
   if constexpr( false )
   {
      std::cout << "\n";
      std::cout << "checking term\n";
      auto un = pretty::print( std::cout, blfs, ctxt );
      std::cout << "term:\n   ";
      pretty::print( std::cout, blfs, un, t, {0,0} );
      std::cout << '\n';
   }

   switch ( t. sel( )) 
   {
   case op_exact:
      {
         auto err = errorheader( blfs, ctxt, t );
         err << "Can't check an exact identifier!\n";
         err << "(The term must be made unchecked first. ";
         err << "This is an internal problem) \n";
         errors. push( std::move( err ));
         return { };
      }

   case op_unchecked:
      {
         auto un = t. view_unchecked( );
         const auto& ident = un. id( );

         const auto& overcands = blfs. getfunctions( ident ); 

         if( overcands. size( ) == 0 )
         { 
            auto err = errorheader( blfs, ctxt, t );
            err << "unknown identifier " << ident << " used as constant";
            errors. push( std::move( err ));
            return { };
         } 

         if( overcands. size( ) > 1 )
         {
            auto err = errorheader( blfs, ctxt, t );
            err << "identifier with multiple overloads ";
            err << "used without arguments: " << ident << "\n";
            errors. push( std::move( err ));
            return { };
         }

         const std::vector< type > empty;
         auto tp = try_apply( blfs, overcands[0], empty, 0 );
         if( !tp. has_value( ))
            throw std::runtime_error( "I believe that this cannot happen" );

         t = term( op_exact, overcands[0] );
         return tp;
      }

   case op_debruijn:
      {
         size_t index = t. view_debruijn( ). index( );
         if( index >= ctxt. size( ) ) 
         {
            // This means that the data structure is corrupted.
            // We don't try to pretty print, because it would crash.

            errorstack::builder err;  
            err << "De Bruijn index #" << index << " is out of range\n";
            errors. push( std::move( err ));
            return { }; 
         }
         return ctxt. gettype( index ); 
      }

   case op_false:
   case op_error:
   case op_true:
      return type( type_form );

   case op_not:
   case op_prop:
      {
         auto un = t. view_unary( );

         std::optional< type > tp;
         {
            auto sub = un. extr_sub( );
            tp = checkandresolve( blfs, errors, ctxt, sub );
            un. update_sub( sub );
         }

         if( tp. has_value( ) && tp. value( ). sel( ) != type_form )
         {
            auto err = errorheader( blfs, ctxt, t );
            err << "argument of logical operator has wrong type ";
            pretty::print( err, blfs, tp. value( ), {0,0} ); 
            errors. push( std::move( err ));
         }

         return type( type_form );
      }

   case op_and:
   case op_or:
   case op_implies:
   case op_equiv:
   case op_lazy_and:
   case op_lazy_implies:
   case op_meta_implies:
      {
         auto bin = t. view_binary( );

         std::optional< type > tp1;
         {  
            auto sub1 = bin. extr_sub1( );
            tp1 = checkandresolve( blfs, errors, ctxt, sub1 );
            bin. update_sub1( sub1 );
         }

         std::optional< type > tp2; 
         {
            auto sub2 = bin. extr_sub2( );
            tp2 = checkandresolve( blfs, errors, ctxt, sub2 );
            bin. update_sub2( sub2 );
         }

         if( tp1. has_value( ) && tp1. value( ). sel( ) != type_form )
         {
            auto err = errorheader( blfs, ctxt, t );
            err << "first argument of logical operator has wrong type ";
            pretty::print( err, blfs, tp1. value( ), {0,0} ); 
            errors. push( std::move( err ));
         }

         if( tp2. has_value( ) && tp2. value( ). sel( ) != type_form )
         {
            auto err = errorheader( blfs, ctxt, t );
            err << "second argument of logical operator has wrong type ";
            pretty::print( err, blfs, tp2. value( ), {0,0} ); 
            errors. push( std::move( err ));
         }

         return type( type_form ); 
      }

   case op_equals:
      {
         auto bin = t. view_binary( );

         std::optional< type > tp1;
         {
            auto sub1 = bin. extr_sub1( );
            tp1 = checkandresolve( blfs, errors, ctxt, sub1 );
            bin. update_sub1( sub1 );
         }

         std::optional< type > tp2;
         {
            auto sub2 = bin. extr_sub2( );
            tp2 = checkandresolve( blfs, errors, ctxt, sub2 );
            bin. update_sub2( sub2 );
         }

         if( tp1. has_value( ) && tp1. value( ). sel( ) != type_obj )
         {
            auto err = errorheader( blfs, ctxt, t ); 
            err << "first argument of equality must be O, but is ";
            pretty::print( err, blfs, tp1. value( ), {0,0} );
            err << "\n";
            errors. push( std::move( err ));
         }

         if( tp2. has_value( ) && tp2. value( ). sel( ) != type_obj )
         {
            auto err = errorheader( blfs, ctxt, t );
            err << "second argument of equality must be O, but is ";
            pretty::print( err, blfs, tp2. value( ), {0,0} ); 
            errors. push( std::move( err ));
         }

         return type( type_form ); 
      }

   case op_forall:
   case op_exists:
      {
         auto quant = t. view_quant( );

         const size_t contextsize = ctxt. size( );
         const size_t errstart = errors. size( );
            // If we produce errors, they start here.

         bool correct = true;

         for( size_t i = 0; i != quant. size( ); ++ i )
         {
            auto vt = quant. extr_var(i);
             
            if( !checkandresolve( blfs, errors, vt. tp ))
               correct = false;

            quant. update_var( i, vt );
         }

         if( !correct )
         {
            auto err = errorheader( blfs, ctxt, t );  
            err << "In structural type of quantifier:";
            errors. addheader( errstart, std::move( err ));
            return type( type_form ); 
         }

         for( size_t i = 0; i != quant. size( ); ++ i )
            ctxt. append( quant. var(i). pref, quant. var(i). tp );

         std::optional< type > bodytype; 

         {
            auto bod = quant. extr_body( );
            bodytype = checkandresolve( blfs, errors, ctxt, bod ); 
            quant. update_body( bod );
         }

         ctxt. restore( contextsize );

         // If the body has a type, and this type is not T, we need to
         // complain:

         if( bodytype. has_value( ) &&
             bodytype. value( ). sel( ) != type_form )
         {
            auto err = errorheader( blfs, ctxt, t );
            err << "body of quantifier does have type Form. Instead it is: ";
            pretty::print( err, blfs, bodytype. value( ), {0,0} );
            errors. push( std::move( err ));
         }

         // Whatever happened, the result is always form:

         return type_form; 
      }

   case op_let:
      {
         auto let = t. view_let( ); 
         size_t contextsize = ctxt. size( );

         // Check the type (possibly resolving ambiguities): 

         auto vt = let. extr_var( );
         bool decltype_ok = checkandresolve( blfs, errors, vt.tp );
         let. update_var( vt );

         // Check the value (possibly resolving ambiguities):

         auto val = let. extr_val( );
         auto valtype = checkandresolve( blfs, errors, ctxt, val );
         let. update_val( val );
     
         // If we have a declared type, the value has a type,
         // and these types differ, we create an error message,
         // and replace the declared type by the type of the value. 

         if( decltype_ok && valtype. has_value( ) &&
             !equal( let. var( ). tp, valtype. value( )) )
         {
            auto err = errorheader( blfs, ctxt, t );
            err << "let: declared type ";
            pretty::print( err, blfs, let. var( ). tp, {0,0} ); 
            err << " differs from true type ";
            pretty::print( err, blfs, valtype. value( ), {0,0} );
            errors. push( std::move( err ));

            vt = let. extr_var( );
            vt. tp = valtype. value( );
            let. update_var( vt );
         }

         // If the value has a type, while the declared type was rejected,
         // we replace the declared type.

         if( !decltype_ok && valtype. has_value( ))
         {
            auto err = errorheader( blfs, ctxt, t );
            err << "let: replaced ill-formed type by ";
            pretty::print( err, blfs, valtype. value( ), {0,0} );
            errors. push( std::move( err ));

            vt = let. extr_var( );
            vt. tp = valtype. value( );
            let. update_var( vt ); 

            decltype_ok = true; 
         }

         if( !decltype_ok )
         {
            ctxt. restore( contextsize );
                // The context was not yet extended, but why not restore?

            return { };
         }

         ctxt. append( let. var( ). pref, let. var( ). tp );  

         std::optional< type > bodytype;
         {
            auto bod = let. extr_body( );
            bodytype = checkandresolve( blfs, errors, ctxt, bod );
            let. update_body( bod );
         }

         ctxt. restore( contextsize ); 
         return bodytype; 
      }

   case op_apply:
      {
         auto ap = t. view_apply( );
         std::vector< type > argtypes;

         // We first deal with the arguments:

         for( size_t i = 0; i != ap. size( ); ++ i )
         {
            auto arg = ap. extr_arg(i);

            auto tp = checkandresolve( blfs, errors, ctxt, arg );
            if( tp. has_value( ))  
               argtypes. push_back( std::move( tp. value( )) ); 
           
            ap. update_arg( i, arg ); 
         }

         // If some subterms did not have a type, we cannot return a type
         // by ourselves, so we quietly give up. 

         if( argtypes. size( ) < ap. size( ))
            return { };

         // If ap. func( ) is still an inexact identifier, we treat this
         // separately, because we cannot simply recurse. 
         // In order to find the correct overload of an identifier, 
         // we need to know the types of the arguments.

         if( ap. func( ). sel( ) == op_unchecked )
         {
            const identifier& ident = ap. func( ). view_unchecked( ). id( );

            const auto& overcands = blfs. getfunctions( ident );
               // overload candidates.

            if( overcands. size( ) == 0 )
            {
               auto err = errorheader( blfs, ctxt, t );
               err << "unknown identifier '" << ident << "' used as function";
               errors. push( std::move( err ));
               return { };
            }

            std::vector< std::pair< exact, type >> results;
               // These will be the overloads that can be applied,
               // together with their return types.

            for( const auto& cand : overcands )
            {
               auto res = try_apply( blfs, cand, argtypes, 0 );
               if( res. has_value( ))
                  results. push_back( { cand, std::move( res. value( )) } ); 
            } 

#if 0
            std::cout << "applicable candidates\n";
            for( const auto& cand : results ) 
            {
               std::cout << "   " << cand. first << " --> " 
                         << cand. second << "\n";
            }
#endif

            if( results. size( ) == 0 )
            {
               auto err = errorheader( blfs, ctxt, t );
               err << "no applicable overload found for '" << ident;
               err << "' in application term,\n"; 
               err << "the arguments have types:  ";
               for( size_t i = 0; i != argtypes. size( ); ++ i )  
               {
                  if(i) err << ", ";
                  logic::pretty::print( err, blfs, argtypes[i], {0,0} ); 
               }

               errors. push( std::move( err )); 
               return { };
            }
 
            if( results. size( ) > 1 )
            {
               auto err = errorheader( blfs, ctxt, t );
               err << "cannot resolve " << ident;
               err << " in application term\n"; 
               err << "   candidates are ";
               for( size_t i = 0; i != results. size( ); ++ i )
               {
                  if(i) err << ", ";
                  err << results[i]. first;
               }
               err << "\n";
               errors. push( std::move( err ));
               return { };
            }
 
            ap. update_func( term( op_exact, results. front( ). first )); 
            return results. front( ). second;
         }

         std::optional< type > ftype;
         {
            auto func = ap. extr_func( );
            ftype = checkandresolve( blfs, errors, ctxt, func );
            ap. update_func( func );  
         }

         if( !ftype. has_value( ))
            return ftype;  // Nothing can be done.

         auto res = try_apply( ftype. value( ), argtypes, 0 ); 

         if( res. has_value( ))
            return res;
         else
         { 
            auto err = errorheader( blfs, ctxt, t );
            err << "cannot apply function of type ";
            pretty::print( err, blfs, ftype. value( ), {0,0} ); 
            err << " on argument(s)\n";
            for( size_t i = 0; i != argtypes. size( ); ++ i )
            {
               err << "   "; 
               pretty::print( err, blfs, argtypes[i], {0,0} );
            }
            errors. push( std::move( err ));

            return { };
         }
      }

   case op_lambda:
      {
         auto lamb = t. view_lambda( );

         bool correct = true;

         size_t errstart = errors. size( );

         for( size_t i = 0; i != lamb. size( ); ++ i ) 
         {
            auto vt = lamb. extr_var(i);
               // We need to extract, because we must resolve overloads.

             if( !checkandresolve( blfs, errors, vt. tp ))
               correct = false;

            lamb. update_var( i, vt );
         }

         if( !correct )
         {
            auto err = errorheader( blfs, ctxt, t ); 
            err << "\n";
            err << "In structural type of lambda";
            errors. addheader( errstart, std::move( err ));
            return { };
         }

         size_t contextsize = ctxt. size( );

         for( size_t i = 0; i != lamb. size( ); ++ i )
            ctxt. append( lamb. var(i). pref, lamb. var(i). tp );

         std::optional< type > bodytype;

         {
            auto bod = lamb. extr_body( );
            bodytype = checkandresolve( blfs, errors, ctxt, bod );
            lamb. update_body( bod );
         }

         ctxt. restore( contextsize );

         if( bodytype. has_value( ))
         {
            bodytype. value( ) = type( type_func, bodytype. value( ), { } );
            auto func = bodytype. value( ). view_func( );
            for( size_t i = 0; i != lamb. size( ); ++ i )
               func. push_back( lamb. var(i). tp ); 
            return bodytype; 
         }
         else
            return { };
      }

   }
   std::cout << "typechecking: selector = " << t. sel( ) << "\n";
   throw std::logic_error( "typechecking: selector not implemented" );
}


std::optional< logic::type > 
logic::try_apply( type ftype, 
                  const std::vector< type > & argtypes, size_t pos )
{
   if( pos > argtypes. size( ))
      throw std::logic_error( "pos > size( )" );

   if constexpr( false )
   {
      std::cout << "trying to apply " << ftype << " on\n";
      for( size_t i = pos; i != argtypes. size( ); ++ i ) 
         std::cout << "   " << i << " : " << argtypes[i] << "\n";
      std::cout << "\n";
   }

   while( pos != argtypes. size( ))
   {
      if( ftype. sel( ) != type_func )
         return { };

      auto fun = ftype. view_func( );

      // args [ pos ... ] must be long enough to contain
      // the required types: 

      if( pos + fun. size( ) > argtypes. size( ))
         return { };  

      for( size_t i = 0; i != fun. size( ); ++ i )
      {
         if( !equal( fun. arg(i), argtypes[ pos ] ))
            return { };

         ++ pos; 
      }

      ftype = fun. result( ); 
   }

   return ftype; 
}


std::optional< logic::type >
logic::try_apply( const beliefstate& blfs, exact name, 
                  const std::vector< type > & argtypes, size_t pos )
{

   if constexpr( false )
   {
      std::cout << "trying to apply belief " << name << " on\n";
      for( size_t i = pos; i != argtypes. size( ); ++ i )
         std::cout << "   arg[" << i << "] : " << argtypes[i];
      std::cout << "\n";
   }

   const auto& bel = blfs. at( name );
   switch( bel. sel( )) 
   {
   case bel_def: 
      {
         const auto& tp = bel. view_def( ). tp( ); 
         return try_apply( tp, argtypes, 0 );
      }

   case bel_symbol:
      {
         const auto& tp = bel. view_symbol( ). tp( );
         return try_apply( tp, argtypes, 0 );
      }

   case bel_fld:
      {
         auto fld = bel. view_field( ); 
         exact structtype = fld. sdef( );

         const belief& parentblf = blfs. at( structtype );
            // The belief in the parent.
         if( parentblf. sel( ) != bel_struct )
            throw std::logic_error( "parent type not a structdef" );
            
         const structdef& parentdef = parentblf. view_struct( ). def( ); 

         auto ftype = parentdef. at( fld. offset( )). tp;
           // Type with which the field was declared.

         if( pos == argtypes. size( ))
         {
            return type( type_func, ftype, 
                                    { type( type_struct, structtype ) } );
         }
           
         if( pos + 1 <= argtypes. size( ) && 
             argtypes[ pos ]. sel( ) == type_struct &&
             argtypes[ pos ]. view_struct( ). def( ) == structtype )
         {
            return try_apply( ftype, argtypes, pos + 1 );
         }

         return { };
      }  

   case bel_constr:
      {
         const auto& structblf = 
            blfs. at( bel. view_constr( ). tp( ));
               // Belief in the struct that we are trying to construct.

         if( structblf. sel( ) != bel_struct )
            throw std::runtime_error( "constructed type not a structdef" );

         const structdef& sdef =
            structblf. view_struct( ). def( ); 

         if( pos + sdef. size( ) != argtypes. size( ))
            return { };
               // No currying for constructors.

         for( size_t i = 0; i != sdef. size( ); ++ i )
         {
            if( !equal( sdef. at(i). tp, argtypes[ pos + i ] ))
               return { };
         }
            
         return type( type_struct, bel. view_constr( ). tp( )); 
      }

   case bel_axiom:
   case bel_thm:
      return { };   // They cannot be used in usual terms. 
   }

   std::cout << bel. sel( ) << " " << bel. ident( ) << "\n";
   throw std::runtime_error( "try_apply, belief is not implemented" );
}

