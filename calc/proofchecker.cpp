
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

std::ostream& calc::operator << ( std::ostream& out, bar b )
{
   for( size_t i = 0; i != b. len; ++ i )
      out << '-';
   return out;
}


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

void calc::proofchecker::setgoal( logic::exact fname )
{
   auto& blf = blfs. at( fname );

   seq = sequent( );
   db. restore(0);
   nrfakes = 0;

   switch( blf. sel( ))
   {
   case logic::bel_thm:
      {
         define( "goal", blf. view_form( ). fm( ),
                         logic::type( logic::type_form ));
         break;
      }

   default:
      throw std::logic_error( "belief not a formula" );
   }
}

std::optional< calc::label > 
calc::proofchecker::cut( const label& lab, logic::term fm )
{
   auto tp = gettype( fm );
   if( !tp. has_value( ))
      return { }; 
   
   if( tp. value( ). sel( ) != logic::type_form )
   {
      errorstack::builder bld;
      auto prt = pretty_printer( bld, blfs ); 
      prt << "Type of cut formula is not F, instead it is ";
      prt << tp. value( );
      err. push( std::move( bld ));
      return { };
   }

   auto f1 = logic::term( logic::op_not,
             logic::term( logic::op_prop, fm ));
   auto f2 = logic::term( logic::op_not, fm );

   seq. append( lab, disjunction{ exists(f1), exists(f2), exists(fm) } );
   return lab;
}

std::optional< calc::label >
calc::proofchecker::branch( label disj, size_t choice,
                            const std::vector< std::string > & eigen )
{
   size_t ind = try2find( disj, "main formula of branch" );
   if( ind == seq. stack. size( ))
      return { };

   if( !is_dnf( disj, ind, "main formula of branch" ))
      return { }; 

   if( choice >= seq. at( ind ). get_dnf( ). size( ))
   {
      errorstack::builder bld;
      auto prt = pretty_printer( bld, blfs, seq. ctxt );
      prt << "branch: Choice " << choice;
      prt << " does not exist in " << seq. at( ind );
      err. push( std::move( bld ));
      return { };
   }

   // Now we are certain that the rule can be applied.

   // Take the main formula, and lift it:

   dnf< logic::term > mainform = seq. at( ind ). get_dnf( );
   mainform = lift( std::move( mainform ), seq. liftdist( ind ));

   enf< logic::term > ex = std::move( mainform. at( choice ));
  
   // Assume the existentially quantified variables of alt:

   if( eigen. size( ) > ex. vars. size( ))
   { 
      errorstack::builder bld;
      bld << "exists " << disj << " : ";
      bld << "there are too many eigenvariables: ";
      bld << "it is " << eigen. size( );
      bld << ", but the formula has only " << ex. vars. size( );
      bld << " variables";
      err. push( std::move( bld ));
      return { };
   }
   
   seq. pushdecision( ind, choice );
   seq. hide( ind );

   for( size_t v = 0; v != ex. vars. size( ); ++ v )
   {
      if( v < eigen. size( ))
         assume( eigen. at(v), ex. vars. at(v). tp );
      else 
         assume( ex. vars. at(v). pref, ex. vars. at(v). tp );
   }

   ++ disj; 
   seq. append( disj, disjunction( { exists( std::move( ex. body )) } ));
   return disj;
}


std::optional< calc::label >
calc::proofchecker::expand( label lab, 
                            const identifier& ident, size_t occ )
{
   auto ind = try2find( lab, "formula to expand" );
   if( ind == seq. stack. size( ))
      return { }; 

   // The expander will check if ident has a definition
   // for the types with which it is used. We don't need
   // to do anything.

   expander def( ident, occ, blfs, err );
      // We are using unchecked identifier exp. ident( ).
      // The expander will look only at exact overloads.
      // This guarantees type safety.

   std::cout << def << "\n";

   seq. hide( ind );
   ++ lab;
 
   if( seq. at( ind ). is_dnf( ))
   {
      auto res = seq. at( ind ). get_dnf( );
      res = lift( std::move( res ), seq. liftdist( ind ));
      seq. append( lab, outermost( def, std::move( res ), 0 ));
   }

   if( seq. at( ind ). is_unf( ))
   {
      std::cout << "it is a UNF\n";
      throw std::logic_error( "fix it" ); 
   }

   return lab; 
}


std::optional< calc::label >
calc::proofchecker::expand( label lab, size_t var, size_t occ ) 
{

   if( !seq. ctxt. hasdefinition( var ))
   {
      errorstack::builder bld;
      auto prt = pretty_printer( bld, blfs, seq. ctxt );
      prt << "expandlocal: variable ";
      prt << logic::term( logic::op_debruijn, var );
      prt << " does not have a definition";
      err. push( std::move( bld ));
      return { };
   }

   auto def = localexpander( var, seq. ctxt. getdefinition( var ), occ );

   auto ind = try2find( lab, "formula to expand" );
   if( ind == seq. stack. size( ))
      return { };

   // Now we need to look at the type of formula at hand:

   seq. hide( ind );
   ++ lab;

   if( seq. at( ind ). is_dnf( ))
   {
      auto res = seq. at( ind ). get_dnf( );
      res = lift( std::move( res ), seq. liftdist( ind ));
      seq. append( lab, outermost( def, std::move( res ), 0 ));
   }

   if( seq. at( ind ). is_unf( ))
   {
       throw std::logic_error( "unf: unfinished" );

   }

   return lab;
}


std::optional< calc::label >
calc::proofchecker::import( const identifier& ident, 
                            std::vector< logic::type > argtypes,
                            label name )
{
   size_t nrcorrect = 0;

   for( auto& tp : argtypes )
   {
      bool b = checkandresolve( blfs, err, tp );
      if( b )
         ++ nrcorrect;
      else
      {
         errorstack::builder bld; 
         auto prt = pretty_printer( bld, blfs );
         prt << "Bad structural type while importing " << ident << " : ";
         prt << tp;
         err. push( std::move( bld ));
      }
   }
 
   if( nrcorrect != argtypes. size( ))
      return { };

   auto ex = findformula( blfs, err, ident, argtypes );
   if( !ex. has_value( ))
      return { };  
         // We can return quietly because findformula created an error. 

   const auto& fm = blfs. at( ex. value( )). view_form( ). fm( );
   seq. append( name, disjunction( { exists( fm ) } ));
   return name; 
}

std::optional< calc::label > 
calc::proofchecker::flatten( label lab )
{
   size_t ind = try2find( lab, "formula to flatten" ); 
   if( ind == seq. stack. size( ))
      return { };

   if( seq. at( ind ). is_unf( ))
   {
      auto f = lift( seq. at( ind ). get_unf( ), seq. liftdist( ind )); 
      auto f2 = try_flatten( conjunction( { f } ));
      if( f2. has_value( ))
      {
         seq. hide( ind ); 

         ++ lab;
         seq. append( lab, std::move( f2. value( )) );
         return lab; 
      }

      return { };
   }

   if( seq. at( ind ). is_dnf( ))
   {
      auto f = lift( seq. at( ind ). get_dnf( ), seq. liftdist( ind ));
      auto f2 = try_flatten(f);
      if( f2. has_value( )) 
      {
         seq. hide( ind );

         ++ lab; 
         seq. append( lab, std::move( f2. value( )) );
         return lab;
      }

      // If f is trivial, it may still be possible to flatten forall(f):

      if( f. size( ) == 1 && f. at(0). vars. size( ) == 0 )
      {
         auto cnf1 = conjunction( { forall( f. at(0). body ) } );
         auto cnf2 = try_flatten( cnf1 );

         if( cnf2. has_value( ))
         {
            seq. hide( ind );
 
            ++ lab; 
            seq. append( lab, std::move( cnf2. value( )) );
            return lab;
         }
      }

      return { };
   }

   throw std::logic_error( "flatten: unreachable" );
}


std::optional< calc::label > calc::proofchecker::normalize( label lab )
{
   size_t ind = try2find( lab, "formula formalization" );
   if( ind == seq. stack. size( ))
      return { };

   ++ lab;
   seq. hide( ind );

   if( seq. at( ind ). is_dnf( ))
   {        
      auto res = seq. at( ind ). get_dnf( );
      res = lift( std::move( res ), seq. liftdist( ind ));
      seq. append( lab, ::normalize( blfs, std::move( res ), 0 ));
   }

   if( seq. at( ind ). is_unf( ))
   {
      throw std::logic_error( "normalize not finished" );
   }

   return lab;
}

bool 
calc::proofchecker::deflocal( std::string_view name, logic::term val )
{
   std::cout << "val = " << val << "\n";
   auto tp = gettype( val );

   if( !tp. has_value( ))
      throw std::logic_error( "def local, no type" );

   define( std::string( name ), val, tp. value( ));
   return true;
}

std::optional< calc::label > 
calc::proofchecker::instantiate( label lab,
                                 const std::vector< logic::term > & values )
{
   size_t ind = try2find( lab, "instantiated formula" );
   if( ind == seq. stack. size( ))   
      return { };
   
   if( !is_unf( lab, ind, "instantiated formula" ))
      return { };
 
   if( seq. at( ind ). get_unf( ). vars. size( ) < values. size( ))
   {
      errorstack::builder bld;
      bld << "forallelim " << lab << " : ";
      bld << "There are " << values. size( ) << " instances, ";
      bld << "while the formula has only ";
      bld << seq. at( ind ). get_unf( ). vars. size( ) << " variables";
      return { };
   }

   auto mainform = seq. at( ind ). get_unf( );
   mainform = lift( std::move( mainform ), seq. liftdist( ind ));

   logic::fullsubst subst;

   size_t nrcorrecttypes = 0;
   for( size_t i = 0; i != values. size( ); ++ i )
   {
      auto inst = values. at(i);
      auto tp = gettype( inst );

      if( tp. has_value( ))
      {
         if( equal( tp. value( ), mainform. vars[i]. tp ))
         {
            subst. append( std::move( inst ));
            ++ nrcorrecttypes;
         }
         else
         {
            auto bld = errorstack::builder( );
            auto prt = pretty_printer( bld, blfs, seq. ctxt );
            prt << "structtype of value " << inst << " is wrong.\n";
            prt << "It is " << tp. value( ) << ", but it must be ";
            prt << mainform. vars. at(i). tp;
            err. push( std::move( bld ));
         }
      }
   }

   if( nrcorrecttypes != values. size( ))
   {
      auto bld = errorstack::builder( );
      bld << "unable to instantiate, typechecking failed";
      err. push( std::move( bld ));
      return { };
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
   seq. append( lab, conjunction( { mainform } ));
   return lab;
}

std::optional< calc::label > 
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
         seq. append( lab ++ , make_dnf( cls. disj ));
   }

   if( lab != names )  
      return names;      // Something was simplified.
   else
      return { };        // Nothing was simplified.
}

std::optional< calc::label > calc::proofchecker::resolve( )
{  
   if( seq. decisions. size( ) == 0 )
      throw std::logic_error( "resolve: no decision" ); 

   if( seq. decisions. size( ) == 0 )
      throw std::logic_error( "there is no decision to resolve" );

   std::cout << seq. decisions. back( ) << "\n";
   std::cout << seq << "\n";

   // We check the context sizes. It never hurts to do that:

   for( size_t i = seq. decisions. back( ). stacksize;
        i != seq. stack. size( ); ++ i )
   {
      if( seq. stack. at(i). second. ctxtsize != 
          seq. ctxt. size( ))
      {
         throw std::logic_error( "resolve: wrong context size" );
      }
   }

   size_t nrassumed = seq. ctxt. size( ) - seq. decisions. back( ). ctxtsize;
      // This is the number of variables that were assumed 
      // in the decision.
   std::cout << "nrassumed = " << nrassumed << "\n";

   for( size_t var = 0; var != nrassumed; ++ var ) 
   {
      if( seq. ctxt. hasdefinition( var ))
         throw std::logic_error( "resolve: variable cannot be definition" );
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
      throw std::logic_error( "resolve: there is no usable result" );
   }

   if( !seq. stack. back( ). second. is_dnf( ))
   {
      errorstack::builder bld;
      auto prt = pretty_printer( bld, blfs, seq. ctxt );
      prt << "Resolve: Last formula is not DNF: ";
      prt << seq. stack. back( ). second;
      err. push( std::move( bld )); 
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
   seq. append( lab, std::move( resolvent ));  
   return lab;
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
      seq. append( becomes, std::move( res ));
   }

   if( seq. at( ind ). is_unf( ))
      throw std::logic_error( "not implemented" );

   return becomes;  
}


std::optional< calc::label > 
calc::proofchecker::fake( logic::term trmp, label name )
{
   auto tp = gettype( trmp );
   if( !tp. has_value( ))
      return { } ;  // Error is already created by checktype. 

   if( tp. value( ). sel( ) != logic::type_form )
   {
      errorstack::builder bld;
      auto prt = pretty_printer( bld, blfs, seq. ctxt );
      prt << "Type of faked formala is not F, instead it is ";
      prt << tp. value( );
      err. push( std::move( bld ));
      return { }; 
   }
   else
   {
      errorstack::builder bld;
      auto prt = pretty_printer( bld, blfs, seq. ctxt );
      prt << "Faked proof of " << trmp; 
      err. push( std::move( bld ));

      seq. append( name, disjunction( { exists( std::move( trmp )) } ));
      ++ nrfakes;
      return name;
   }
}


calc::label calc::proofchecker::labelof( ssize_t cnt ) const
{
   if( seq. size( ) == 0 )
      return label( "(doesnotexist)" );

   if( cnt >= 0 )
   {
      size_t ind = 0;
      while( cnt || seq. at( ind ). hidden )
      {
         if( !seq. at( ind ). hidden )
            -- cnt;
 
         ++ ind;
         if( ind == seq. size( ))
            return label( "(doesnotexist)" );
      }
      return seq. stack. at( ind ). first; 
   }
   else
   {
      size_t ind = seq. size( );
      while( cnt < -1 || seq. at( ind - 1 ). hidden ) 
      {
         -- ind;

         if( ! seq. at( ind ). hidden )
            ++ cnt; 
         
         if( ind == 0 )
            return label( "(doesnotexist)" );     
      }
     
      return seq. stack. at( ind - 1 ). first; 
   }

}

void
calc::proofchecker::hide( label lab )
{
   auto ind = try2find( lab, "for hiding" );
   if( ind < seq. stack. size( ))
      seq. hide( ind );
}

void 
calc::proofchecker::show( std::string_view label, 
                          std::ostream& out ) const
{
   auto prt = pretty_printer( std::cout, blfs );
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


std::optional< logic::type >
calc::proofchecker::gettype( logic::term& tm ) 
{
   size_t ss = seq. ctxt. size( );

   auto tp = checkandresolve( blfs, err, seq. ctxt, tm );

   if( seq. ctxt. size( ) != ss )
      throw std::logic_error( "context not restored" );

   return tp; 
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


size_t calc::proofchecker::try2find( label lab, std::string_view descr )
{
   size_t ind = seq. find( lab );
   if( ind == seq. stack. size( ))
   {
      errorstack::builder bld;
      bld << "Unknown label " << lab << " used for " << descr; 
      err. push( std::move( bld ));
   }
   return ind;
}

bool
calc::proofchecker::is_dnf( const label& lab, size_t ind, 
                            std::string_view descr )
{
   if( !seq. at( ind ). is_dnf( ))
   {
      errorstack::builder bld;
      auto prt = pretty_printer( bld, blfs, seq. ctxt );
      prt << descr << " is not in DNF : ";
      seq. at( ind ). print( prt );
      err. push( std::move( bld ));
      return false; 
   }
   else
      return true;
}

bool
calc::proofchecker::is_unf( const label& lab, size_t ind,
                            std::string_view descr )
{
   if( !seq. at( ind ). is_unf( ))
   {
      errorstack::builder bld;
      auto prt = pretty_printer( bld, blfs, seq. ctxt );
      prt << descr << " is not in UNF : ";
      seq. at( ind ). print( prt );
      err. push( std::move( bld )); 
      return false; 
   }
   else
      return true;
}


