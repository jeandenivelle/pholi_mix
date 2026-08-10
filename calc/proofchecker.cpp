
#include "proofchecker.h"

#include "outermost.h"
#include "expander.h"
#include "localexpander.h"
#include "traverse.h"
#include "flatten.h"
#include "subsumption.h"
#include "saturation.h"
#include "structural.h"

#include "logic/structural.h"
#include "logic/replacements.h"
#include "logic/counters.h"
#include "logic/structural.h"

#include "projection.h"

namespace
{

   template< typename F > F lift( F f, size_t dist )
   {
      // std::cout << "lifting " << f << " over distance " << dist << "\n";
      if( dist != 0 )
      {
         auto lift = logic::lifter( dist );
         return outermost( lift, std::move(f), 0 );
      }
      else
         return f;
   }


   template< typename F >
   F normalize( const logic::beliefstate& blfs, F f, size_t dist )
   {
      logic::betareduction beta;
      logic::decurrier dec;
      calc::projection proj( blfs );

      do
      {
         beta. used = 0;
         f = outermost( beta, std::move(f), dist );

         dec. used = 0;
         f = outermost( dec, std::move(f), dist );

         proj. used = 0;
         f = outermost( proj, std::move(f), dist );
      }
      while( beta. used || proj. used || dec. used );

      return f;
   }
}


void calc::proofchecker::setname( size_t ind, const std::string& name )
{
   if( ind < seq. size( ))
   {
      seq. at( ind ). name = name; 
      seq. index. insert( std::pair( name, ind ));
   }
}

size_t calc::proofchecker::cut( logic::term fm )
{
   auto tp = checkandresolve( *blfs, errors, seq. ctxt, fm );
   if( !tp. has_value( ))
      return seq. size( ); 
   
   if( tp. value( ). sel( ) != logic::type_prop )
   {
      errortree::builder bld;
      auto prt = pretty_printer( &bld, blfs ); 
      prt << "Type of cut formula is not Prop, instead it is ";
      prt << tp. value( );
      errors. push_back( std::move( bld ));
      return seq. size( );
   }

   auto f1 = logic::term( logic::op_not,
             logic::term( logic::op_prop, fm ));
   auto f2 = logic::term( logic::op_not, fm );

   return seq. append( disjunction{ exists(f1), exists(f2), exists(fm) } );
}


size_t
calc::proofchecker::branch( size_t disj, size_t choice,
                            const std::vector< std::string > & eigen )
{
   if( disj >= seq. size( ))
      return seq. size( );

   if( !check_dnf( disj, "main formula of branch" ))
      return seq. size( ); 

   if( choice >= seq. at( disj ). get_dnf( ). size( ))
   {
      errortree::builder bld;
      auto prt = pretty_printer( &bld, blfs, seq. ctxt );
      prt << "branch: Choice " << choice;
      prt << " does not exist in " << seq. at( disj );
      errors. push_back( std::move( bld ));
      return seq. size( );
   }

   // Now we are certain that the rule can be applied.

   // Take the main formula, and lift it:

   dnf< logic::term > mainform = seq. at( disj ). get_dnf( );
   mainform = lift( std::move( mainform ), seq. liftdist( disj ));

   enf< logic::term > ex = std::move( mainform. at( choice ));
  
   // Assume the existentially quantified variables of alt:

   if( eigen. size( ) > ex. vars. size( ))
   { 
      errortree::builder bld;
      bld << "branch " << disj << ": ";
      bld << "there are too many eigenvariables (" << eigen. size( ) << "), ";
      bld << "but the formula has only " << ex. vars. size( );
      bld << " variables";
      errors. push_back( std::move( bld ));
      return seq. size( );
   }
   
   seq. pushdecision( disj, choice );
   seq. hide( disj );

   for( size_t v = 0; v != ex. vars. size( ); ++ v )
   {
      if( v < eigen. size( ))
         assume( eigen. at(v), ex. vars. at(v). tp );
      else 
         assume( ex. vars. at(v). pref, ex. vars. at(v). tp );
   }

   return seq. append( disjunction( { exists( std::move( ex. body )) } ));
}


size_t
calc::proofchecker::expand( size_t ind, const identifier& ident, size_t occ )
{
   if( ind >= seq. size( ))
      return seq. size( );
#if 0
   // The expander will check if ident has a definition
   // for the types with which it is used. We don't need
   // to do anything.

   expander def( ident, occ, blfs );
      // We are using unchecked identifier exp. ident( ).
      // The expander will look only at exact overloads.
      // This guarantees type safety.

   std::cout << def << "\n";

   seq. hide( ind );

   if( seq. at( ind ). is_dnf( ))
   {
      auto res = seq. at( ind ). get_dnf( );
      res = lift( std::move( res ), seq. liftdist( ind ));
      seq. append( lab, outermost( def, std::move( res ), 0 ));
      transfer( std::move( def. errs ), errors );
   }

   if( seq. at( ind ). is_unf( ))
   {
      auto res = seq. at( ind ). get_unf( );
      res = lift( std::move( res ), seq. liftdist( ind )); 
      seq. append( lab, outermost( def, std::move( res ), 0 )); 
      transfer( std::move( def. errs ), errors );
   }

   return true;
#endif
}


size_t
calc::proofchecker::expand( size_t ind, size_t var, size_t occ ) 
{
   if( ind >= seq. size( ))
      return seq. size( );

   if( !seq. ctxt. hasdefinition( var ))
   {
      errortree::builder bld;
      auto prt = pretty_printer( &bld, blfs, seq. ctxt );
      prt << "expandlocal: variable ";
      prt << logic::term( logic::op_debruijn, var );
      prt << " does not have a definition";
      errors. push_back( std::move( bld ));
      return seq. size( );
   }

   auto def = localexpander( var, seq. ctxt. getdefinition( var ), occ );
   seq. hide( ind );

   // Now we need to look at the type of formula at hand:

   if( seq. at( ind ). is_dnf( ))
   {
      auto res = seq. at( ind ). get_dnf( );
      res = lift( std::move( res ), seq. liftdist( ind ));
      return seq. append( outermost( def, std::move( res ), 0 ));
   }

   if( seq. at( ind ). is_unf( ))
   {
       throw std::logic_error( "unf: unfinished !!" );
   }

}
#if 0

bool
calc::proofchecker::import( const identifier& ident, 
                            std::vector< logic::type > argtypes,
                            label name )
{
   size_t nrcorrect = 0;

   for( auto& tp : argtypes )
   {
      bool b = checkandresolve( *blfs, errors, tp );
      if( b )
         ++ nrcorrect;
      else
      {
         errortree::builder bld; 
         auto prt = pretty_printer( &bld, blfs );
         prt << "Bad structural type while importing " << ident << " : ";
         prt << tp;
         errors. push_back( std::move( bld ));
      }
   }
 
   if( nrcorrect != argtypes. size( ))
      return { };

   auto ex = findformula( *blfs, errors, ident, argtypes );
   if( !ex. has_value( ))
      return false;  
         // We can return quietly because findformula created an error. 

   const auto& fm = blfs -> at( ex. value( )). view_form( ). fm( );
   seq. append( name, disjunction( { exists( fm ) } ));

   return true;
}

#endif

size_t calc::proofchecker::flatten( size_t ind )
{
   if( ind >= seq. size( ))
      return seq. size( );

   std::cout << "flatten " << ind << "\n";

   if( seq. at( ind ). is_unf( ))
   {
#if 0
      auto f = lift( seq. at( ind ). get_unf( ), seq. liftdist( ind )); 
      auto f2 = try_flatten( conjunction( { f } ));
      if( f2. has_value( ))
      {
         seq. hide( ind ); 

         for( auto& u : f2. value( ))
         {
            ++ lab; 
            lab = seq. append( lab, std::move(u));
         }
         return lab; 
      }

      return { };
#endif
      throw std::logic_error( "its an UNF" );
   }

   if( seq. at( ind ). is_dnf( ))
   {
      auto f = lift( seq. at( ind ). get_dnf( ), seq. liftdist( ind ));
      auto f2 = try_flatten(f);
      if( f2. has_value( )) 
      {
         seq. hide( ind );

         return seq. append( std::move( f2. value( )) );
      }

      // If f is trivial, it may still be possible to flatten forall(f):

      if( f. size( ) == 1 && f. at(0). vars. size( ) == 0 )
      {
         auto cnf1 = conjunction( { forall( f. at(0). body ) } );
         auto cnf2 = try_flatten( cnf1 );

         if( cnf2. has_value( ))
         {
            seq. hide( ind );

            size_t pos = seq. size( );
            for( auto& u : cnf2. value( ))
               seq. append( std::move(u)); 
            
            return pos;
         }
      }

      return seq. size( ); 
   }

   throw std::logic_error( "flatten: unreachable" );
}

#if 0

std::optional< calc::label > calc::proofchecker::normalize( label lab )
{
   size_t ind = try2find( lab, "formula formalization" );
   if( ind == seq. stack. size( ))
      return { };

   seq. hide( ind );

   ++ lab;
   if( seq. at( ind ). is_dnf( ))
   {        
      auto res = seq. at( ind ). get_dnf( );
      res = lift( std::move( res ), seq. liftdist( ind ));
      return seq. append( lab, ::normalize( *blfs, std::move( res ), 0 ));
   }

   if( seq. at( ind ). is_unf( ))
   {
      auto res = seq. at( ind ). get_unf( );
      res = lift( std::move( res ), seq. liftdist( ind ));
      return seq. append( lab, ::normalize( *blfs, std::move( res ), 0 ));
   }
 
   throw std::logic_error( "unreachable" );
}

bool 
calc::proofchecker::def( std::string_view name, logic::term val )
{
   std::cout << "val in define = " << val << "\n";

   errorvector type_errors;

   auto tp = checkandresolve( *blfs, type_errors, seq. ctxt, val );

   if( type_errors. size( ) || !tp. has_value( ))
   {
      errortree::builder bld;
      auto prt = pretty_printer( &bld, blfs, seq. ctxt );
      prt << "type errors for let " << name << " := " << val;
      transfer( std::move( bld ), std::move( type_errors ), errors ); 
      return false;
   }

   define( std::string( name ), val, tp. value( ));
   return true;
}


bool
calc::proofchecker::removedef( )
{
   std::cout << seq << "\n";

   if( seq. ctxt. size( ) == 0 || !seq. ctxt. hasdefinition(0))
   {
      errortree::builder bld;
      auto prt = pretty_printer( &bld, blfs, seq. ctxt );
      prt << "removedef: Last variable is not definition"; 
      errors. push_back( std::move( bld ));
      return false;
   }

   auto subst = logic::singlesubst( seq. ctxt. getdefinition(0));
   std::cout << subst << "\n";

   size_t s = seq. stack. size( );
   while( s && seq. at( s - 1 ). ctxtsize == seq. ctxt. size( ))
   {
      -- s; 
      if( seq. at(s). is_dnf( ))
      {
         seq. at(s). get_dnf( ) = 
            outermost( subst, std::move( seq. at(s). get_dnf( )), 0 ); 
      }

      if( seq. at(s). is_unf( ))
      {
         seq. at(s). get_unf( ) =
            outermost( subst, std::move( seq. at(s). get_unf( )), 0 );

      }
      
      -- seq. at(s). ctxtsize;

   }

   seq. ctxt. restore( seq. ctxt. size( ) - 1 );
   return true;
}


bool
calc::proofchecker::instantiate( label lab,
                                 const std::vector< logic::term > & values )
{
   size_t ind = try2find( lab, "instantiated formula" );
   if( ind == seq. stack. size( ))   
      return false;
   
   if( !is_unf( lab, ind, "instantiated formula" ))
      return false;
 
   if( seq. at( ind ). get_unf( ). vars. size( ) < values. size( ))
   {
      errortree::builder bld;
      bld << "forallelim " << lab << " : ";
      bld << "There are " << values. size( ) << " instances, ";
      bld << "while the formula has only ";
      bld << seq. at( ind ). get_unf( ). vars. size( ) << " variables";
      errors. push_back( std::move( bld ));
      return false;
   }

   auto mainform = seq. at( ind ). get_unf( );
   mainform = lift( std::move( mainform ), seq. liftdist( ind ));

   logic::fullsubst subst;

   size_t nrcorrecttypes = 0;
   for( size_t i = 0; i != values. size( ); ++ i )
   {
      auto inst = values. at(i);
      auto tp = checkandresolve( *blfs, errors, seq. ctxt, inst );

      if( tp. has_value( ))
      {
         if( equal( tp. value( ), mainform. vars[i]. tp ))
         {
            subst. append( std::move( inst ));
            ++ nrcorrecttypes;
         }
         else
         {
            errortree::builder bld;
            auto prt = pretty_printer( &bld, blfs, seq. ctxt );
            prt << "structtype of value " << inst << " is wrong.\n";
            prt << "It is " << tp. value( ) << ", but it must be ";
            prt << mainform. vars. at(i). tp;
            errors. push_back( std::move( bld ));
         }
      }
   }

   if( nrcorrecttypes != values. size( ))
   {
      errortree::builder bld; 
      bld << "unable to instantiate, typechecking failed";
      errors. push_back( std::move( bld ));
      return false;
   }

   // We do not remove the outermost forall, because its
   // presence is required by the data structure.
   // It is not obligatory to instantiate all variables. 

   mainform. vars. erase( mainform. vars. begin( ),
                          mainform. vars. begin( ) + values. size( ));

   mainform = outermost( subst, std::move( mainform ), 0 );

   // We append mainform as CNF. The append function will
   // convert formula into a DNF is the quantification is empty.

   ++ lab; 
   seq. append( lab, std::move( mainform ) );

   return true;
}

bool
calc::proofchecker::simplify( label names )
{
   saturation sat; 

   for( size_t i = 0; i != seq. stack. size( ); ++ i )
   {
      const auto& fm = seq. at(i);
      if( !fm. hidden && fm. is_dnf( ))
         sat. initial( lift( fm. get_dnf( ), seq. liftdist(i)), i );
   }

   sat. saturate( );
   std::cout << "after saturation\n";
   std::cout << sat << "\n";

   for( auto rm : sat. removed_initials )
      seq. hide( rm );

   auto lab = names;

   for( auto& cls : sat. checked )
   {
      // We don't add initial ones, because they are already there.

      if( !cls. seqind )
         lab = seq. append( lab , make_dnf( cls. disj ));
   }

   if( lab != names )  
      return true;         // Something was simplified.
   else
      return false;        // Nothing was simplified.
}

std::optional< calc::label > calc::proofchecker::merge( )
{  
   if( seq. nrdecisions( ) == 0 )
   {
      errortree::builder bld;
      bld << "merge: there is no decision";
      errors. push_back( std::move( bld ));
      return { };
   }

   size_t nrassumed = seq. ctxt. size( ) - seq. decisions. back( ). ctxtsize;
      // This is the number of variables that were assumed 
      // for the decision.

   for( size_t var = 0; var != nrassumed; ++ var )
   {
      if( seq. ctxt. hasdefinition(var)) 
      {
         errortree::builder bld;
         auto prt = pretty_printer( &bld, blfs, seq. ctxt );
         prt << "Cannot merge, because ";
         prt << "variable " << logic::term( logic::op_debruijn, var );
         prt << " is defined (while it must be assumed)\n"; 
         prt << seq. ctxt << "\n";
         errors. push_back( std::move( bld )); 
         return { };
      }
   }

   // We check the context sizes. It never hurts to do that:

   for( size_t i = seq. decisions. back( ). stacksize;
        i != seq. stack. size( ); ++ i )
   {
      if( seq. stack. at(i). second. ctxtsize != 
          seq. ctxt. size( ))
      {
         throw std::logic_error( "merge: wrong context size" );
      }
   }

   for( size_t var = 0; var != nrassumed; ++ var ) 
   {
      if( seq. ctxt. hasdefinition( var ))
         throw std::logic_error( "merge: variable cannot be definition" );
   }

   // Very unlikely, but who knows?

   while( seq. decisions. back( ). stacksize < seq. stack. size( ) &&
          seq. stack. back( ). second. hidden )
   {
      throw std::logic_error( "unlikely thing happened" );
      seq. stack. pop( );
   }
   
   if( seq. decisions. back( ). stacksize >= seq. stack. size( ))
   {
      throw std::logic_error( "merge: there is no usable result" );
   }

   if( !seq. stack. back( ). second. is_dnf( ))
   {
      errortree::builder bld;
      auto prt = pretty_printer( &bld, blfs, seq. ctxt );
      prt << "Resolve: Last formula is not DNF: ";
      prt << seq. stack. back( ). second;
      errors. push_back( std::move( bld )); 
      return { };
   }

   dnf< logic::term > resolvent;

   size_t parind = seq. decisions. back( ). parent;

   {
      const dnf< logic::term > & parent = 
         seq. stack. at( parind ). second. get_dnf( ); 

      for( size_t i = 0; i != parent. size( ); ++ i )
      {
         if( i != seq. decisions. back( ). choice )
         {
            if( !subsumes( parent. at(i), resolvent ))
               resolvent. append( parent. at(i));
         } 
      }

      std::cout << "parent = " << parent << "\n";
   }

   std::cout << "resolvent = " << resolvent << "\n";

   // For each disjunct separately,
   // we determine its free variables, and
   // prepend existential quantifiers for them:

   for( auto lit : seq. stack. back( ). second. get_dnf( ))
   {
      // Collect the free variables of lit. Note that
      // lit may contain free variables. That is unproblematic. 
 
      logic::debruijn_counter varsinlit;
      traverse( varsinlit, lit, 0 );

      // We don't care about all free variables, only about the
      // ones that are assumed in the last decision. 
      // We go through the assumptions, check if they occur
      // in vars. We create a normalizing subsitution for those.

      auto norm = logic::normalizer( nrassumed );

      // Store this in a variable: 
      // seq. ctxt. size( ) - seq. decisions. back( ). ctxtsize;

      for( size_t var = 0; var != nrassumed; ++ var )
      {
         if( varsinlit. contains( var ))
            norm. append( var );
      }

      // Apply norm to lit, to obtain the free variables normalized.

      lit = outermost( norm, std::move( lit ), 0 );

      // We need to collect the types of the variables that  
      // occur in varsinlit. 
      // Unfortunately, it needs to be done backwards:

      std::vector< logic::vartype > quant;

      for( size_t var = nrassumed; var != 0; )
      {
         -- var; 
         if( varsinlit. contains( var ))
         {
            quant. push_back( { seq. ctxt. getname( var ),
                                seq. ctxt. gettype( var ) } );
         }
      }

      // If lit contains (existentially quantified) variables, we add
      // them to quant.

      for( auto& q : lit. vars )
         quant. push_back( std::move(q));

      lit. vars = std::move( quant );  
     
      if( !subsumes( lit, resolvent ))
         resolvent. append( std::move( lit ));  
   }

   seq. popdecision( );
   db. restore( seq. ctxt. size( ));
 
   if( subsumes( resolvent, seq. stack. at( parind ). second. get_dnf( )))
      seq. hide( parind );

   label lab = seq. stack. at( parind ). first + 1; 
   return seq. append( lab, std::move( resolvent ));  
}


std::optional< calc::label > 
calc::proofchecker::rename( label was, label becomes ) 
{
   size_t ind = try2find( was, "formula to rename" );
   if( ind == seq. stack. size( ))
      return { };

   seq. hide( ind );

   if( seq. at( ind ). is_dnf( ))
   {
      auto res = seq. at( ind ). get_dnf( );
      res = lift( std::move( res ), seq. liftdist( ind ));
      return seq. append( becomes, std::move( res ));
   }

   if( seq. at( ind ). is_unf( ))
   {
      auto res = seq. at( ind ). get_unf( ); 
      res = lift( std::move( res ), seq. liftdist( ind )); 
      return seq. append( becomes, std::move( res )); 
   }

   throw std::logic_error( "reached the unreachable" );
}


std::optional< calc::label >
calc::proofchecker::copy( label lab )
{
   size_t ind = try2find( lab, "formula to copy" );
   if( ind == seq. stack. size( ))
      return { };

   if( seq. at( ind ). is_dnf( ))
   {
      auto res = seq. at( ind ). get_dnf( );
      res = lift( std::move( res ), seq. liftdist( ind ));
      return seq. append( lab, std::move( res ));
   }

   if( seq. at( ind ). is_unf( ))
      throw std::logic_error( "not implemented" );
  
   throw std::logic_error( "reached the unreachable" );
}


bool
calc::proofchecker::fake( logic::term donald, label name )
{
   auto tp = checkandresolve( *blfs, errors, seq. ctxt, donald );
   if( !tp. has_value( ))
      return false;  // Error is already created by checktype. 

   if( tp. value( ). sel( ) != logic::type_prop )
   {
      errortree::builder bld;
      auto prt = pretty_printer( &bld, blfs, seq. ctxt );
      prt << "Type of faked formala is not Prop, instead it is ";
      prt << tp. value( );
      errors. push_back( std::move( bld ));
      return false; 
   }
   else
   {
      errortree::builder bld;
      auto prt = pretty_printer( &bld, blfs, seq. ctxt );
      prt << "Faked proof of " << donald; 
      errors. push_back( std::move( bld ));

      name = seq. append( name, 
                     disjunction( { exists( std::move( donald )) } ));
      ++ nrfakes;
      return true;
   }
}


void
calc::proofchecker::hide( label lab )
{
   auto ind = try2find( lab, "hiding" );
   if( ind < seq. stack. size( ))
      seq. hide( ind );
}

#endif

void 
calc::proofchecker::show( std::string_view label, 
                          std::ostream& out ) const
{
   auto prt = pretty_printer( &std::cout, blfs );
   prt << bar( 75 ) << "\n";
   prt << "proof state " << label << " :\n";
   seq. print( prt );   
   prt << bar( 75 ) << "\n";
}

void
calc::proofchecker::assume( const std::string& name,
                            const logic::type& tp )
{
   seq. ctxt. assume( name, tp );
   db. push( name, db. size( ));
}

void 
calc::proofchecker::define( const std::string& name, 
                            const logic::term& val, 
                            const logic::type& tp )
{
   seq. ctxt. define( name, val, tp );
   db. push( name, db. size( ));
}

logic::term calc::proofchecker::replacedebruijn( logic::term tm )
{
   if( db. size( ) != seq. ctxt. size( ))
   {
      std::cout << db. size( ) << " " << seq. ctxt. size( ) << "\n";
      throw std::logic_error( "replacedebruijn: Sizes differ" );
   }

   return logic::replace_debruijn( db, tm );
}

size_t calc::proofchecker::lookup( ssize_t ref ) 
{
   if( ref < 0 )
      return move( seq. size( ), ref );
   else
      return move( 0, ref );
}

size_t calc::proofchecker::lookup( const std::string& name ) 
{
   auto p = seq. index. find( name );

   if( p == seq. index. end( ))
   {
      errortree::builder bld;
      bld << "could not find formula name $" << name; 
      errors. push_back( std::move( bld )); 

      return seq. stack. size( );
   }

   if( seq. stack. at( p -> second ). hidden )
   {
      errortree::builder bld;
      bld << "formula name $" << name << " is hidden"; 
      errors. push_back( std::move( bld ));
   }

   return p -> second;
}

size_t calc::proofchecker::move( size_t ind, ssize_t disp ) 
{
   std::cout << "moving " << ind << " + " << disp << "\n";
   
   if( seq. size( ) == 0 )
      return 0;

   if( disp >= 0 )
   {
      while( disp || seq. at( ind ). hidden )
      {
         if( !seq. at( ind ). hidden )
            -- disp;
 
         ++ ind;
         if( ind == seq. size( ))
         {
            errortree::builder bld;
            bld << "cannot find formula moving forward";
            errors. push_back( std::move( bld ));
            return seq. size( );
         }
      }
      return ind; 
   }
   else
   {
      while( disp < -1 || seq. at( ind - 1 ). hidden ) 
      {
         -- ind;

         if( ! seq. at( ind ). hidden )
            ++ disp; 
         
         if( ind == 0 )
         {
            errortree::builder bld;
            bld << "cannot find formula moving backward";
            errors. push_back( std::move( bld ));

            return seq. size( );
         }
      }
     
      return ind - 1;
   }
}


std::optional< calc::cnf< logic::term >>
calc::proofchecker::try_flatten( const cnf< logic::term > & conj )
{
   auto conj2 = calc::flatten( conj );

   if( conj2. size( ) < conj. size( ) || !subsumes( conj, conj2 ))
      return conj2; 
   else
      return { };
}

std::optional< calc::dnf< logic::term >>
calc::proofchecker::try_flatten( const dnf< logic::term > & disj )
{
   auto disj2 = calc::flatten( disj );
   if( disj2. size( ) < disj. size( ) || !subsumes( disj, disj2 ))
      return disj2;
   else
      return { };
}

#if 0

size_t calc::proofchecker::try2find( label lab, std::string_view descr )
{
   size_t ind = seq. find( lab );
   if( ind == seq. stack. size( ))
   {
      errortree::builder bld;
      bld << "Unknown label " << lab << " used for " << descr; 
      errors. push_back( std::move( bld ));
   }
   return ind;
}

#endif

bool
calc::proofchecker::check_dnf( size_t ind, std::string_view descr )
{
   if( !seq. at( ind ). is_dnf( ))
   {
      errortree::builder bld;
      auto prt = pretty_printer( &bld, blfs, seq. ctxt );
      prt << descr << " is not in DNF : ";
      seq. at( ind ). print( prt );
      errors. push_back( std::move( bld ));
      return false; 
   }
   else
      return true;
}

#if 0

bool
calc::proofchecker::is_unf( const label& lab, size_t ind,
                            std::string_view descr )
{
   if( !seq. at( ind ). is_unf( ))
   {
      errortree::builder bld;
      auto prt = pretty_printer( &bld, blfs, seq. ctxt );
      prt << descr << " is not in UNF : ";
      seq. at( ind ). print( prt );
      errors. push_back( std::move( bld )); 
      return false; 
   }
   else
      return true;
}

#endif

