
#include "proofchecker.h"

#include "outermost.h"
#include "expander.h"
#include "localexpander.h"
#include "flatten.h"
#include "subsumption.h"
#include "saturation.h"

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
   std::cout << "setting goal: " << fname << "\n";

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


std::optional< calc::label > calc::proofchecker::cut( logic::term fm )
{
   auto tp = checktype( fm );
   if( !tp. has_value( ))
      return { }; 
   
   if( tp. value( ). sel( ) != logic::type_form )
   {
      errorstack::builder bld;
      auto prnt = pretty_printer( bld, blfs ); 
      prnt << "Type of cut formula is not F, instead it is ";
      prnt << tp. value( );
      err. push( std::move( bld ));
      return { };
   }

   auto f1 = logic::term( logic::op_not,
             logic::term( logic::op_prop, fm ));
   auto f2 = logic::term( logic::op_not, fm );

   auto lab = seq. nextlabel; 
   seq. append( disjunction{ exists(f1), exists(f2), exists(fm) } );
   return lab;
}


std::optional< calc::label >
calc::proofchecker::orexists( label fm, size_t choice,
                              const std::vector< std::string > & eigen )
{
   size_t ind = seq. find( fm );
   if( ind == seq. stack. size( ))
   {
      errorstack::builder bld;
      bld << "ordisjrepl: Unknown label for disjunction " << fm;
      err. push( std::move( bld )); 
      return { };
   }  

   if( !seq. at( ind ). is_dnf( ))
   {
      errorstack::builder bld;
      auto prnt = pretty_printer( bld, blfs, seq. ctxt );
      prnt << "ordisjrepl: Main formula is not in DNF : ";
      seq. at( ind ). print( prnt );
      err. push( std::move( bld ));
      return { };
   }

   if( choice >= seq. at( ind ). get_dnf( ). size( ))
   {
      errorstack::builder bld;
      auto prnt = pretty_printer( bld, blfs, seq. ctxt );
      prnt << "orrepl: Alternative " << choice;
      prnt << " does not exist in " << seq. at( ind );
      err. push( std::move( bld ));
      return { };
   }

   // Now we are certain that the rule can be applied.

   // Take the main formula, and lift it:

   dnf< logic::term > mainform = seq. at( ind ). get_dnf( );
   mainform = lift( std::move( mainform ), seq. liftdist( ind ));
   std::cout << "lifted mainform : " << mainform << "\n";

   enf< logic::term > ex = std::move( mainform. at( choice ));
   std::cout << "ex: " << ex << "\n";
  
   // Assume the existentially quantified variables of alt:

   if( eigen. size( ) > ex. vars. size( ))
   {
      errorstack::builder bld;
      bld << "exists " << fm << " : ";
      bld << "there are too many eigenvariables: ";
      bld << "it is " << eigen. size( );
      bld << ", but the formula has only " << ex. vars. size( ) << "variables";
      err. push( std::move( bld ));
      return { };
   }
   
   seq. hide( ind );
   seq. pushdecision( ind, choice );

   for( size_t v = 0; v != ex. vars. size( ); ++ v )
   {
      if( v < eigen. size( ))
         assume( eigen. at(v), ex. vars. at(v). tp );
      else 
         assume( ex. vars. at(v). pref, ex. vars. at(v). tp );
   }

   auto lab = seq. nextlabel; 
   seq. append( disjunction( { exists( std::move( ex. body )) } ));
   return lab; 
}

std::optional< calc::label >
calc::proofchecker::expand( label fm, const identifier& ident, size_t occ )
{
   auto ind = seq. find( fm );
   if( ind == seq. stack. size( ))
   {
      errorstack::builder bld;
      bld << "expand: unknown label " << ident;
      err. push( std::move( bld ));
      return { };
   }

   // The expander will check if ident has a definition
   // for the types with which it is used. We don't need
   // to do anything.

   expander def( ident, occ, blfs, err );
      // We are using unchecked identifier exp. ident( ).
      // The expander will look only at exact overloads.
      // This guarantees type safety.

   std::cout << def << "\n";

   // I see a recurring pattern here, that needs to become a template:

   if( seq. at( ind ). is_dnf( ))
   {
      auto res = seq. at( ind ). get_dnf( );
      res = lift( std::move( res ), seq. liftdist( ind ));
      res = outermost( def, std::move( res ), 0 );
      seq. hide( ind );
      auto lab = seq. nextlabel;
      seq. append( res );
      return lab;
   }

   if( seq. at( ind ). is_unf( ))
   {
      std::cout << "it is a UNF\n";
   }

}


std::optional< calc::label >
calc::proofchecker::expand( label fm, size_t var, size_t occ ) 
{

   if( !seq. ctxt. hasdefinition( var ))
   {
      errorstack::builder bld;
      auto prnt = pretty_printer( bld, blfs, seq. ctxt );
      prnt << "expandlocal: variable ";
      prnt << logic::term( logic::op_debruijn, var );
      prnt << " does not have a definition";
      err. push( std::move( bld ));
      return { };
   }

   auto def = localexpander( var, seq. ctxt. getdefinition( var ), occ );

   auto ind = seq. find( fm );
   if( ind == seq. stack. size( ))
   {
      errorstack::builder bld;
      auto prnt = pretty_printer( bld, blfs );
      prnt << "unknown formula " << fm;
      err. push( std::move( bld ));
      return { };
   }

   // Now we need to look at the type of formula at hand:

   seq. hide( ind );

   if( seq. at( ind ). is_dnf( ))
   {
      auto d = seq. at( ind ). get_dnf( );
      d = lift( std::move(d), seq. liftdist( ind ));
      std::cout << "after the lift " << d << "\n";
      auto lab = seq. nextlabel; 
      seq. append( outermost( def, std::move(d), 0 ));
      return lab; 
   }

   if( seq. at( ind ). is_unf( ))
   {
       throw std::logic_error( "unf: unfinished" );

   }

   seq. print( std::cout );
   throw std::logic_error( "should be unreachable" );
}


std::optional< calc::label > 
calc::proofchecker::flatten( label fm )
{
   // This repeated pattern needs to become a function:

   size_t ind = seq. find( fm );
   if( ind == seq. stack. size( ))
   {
      errorstack::builder bld;
      auto prnt = pretty_printer( bld, blfs, seq. ctxt );
      seq. print( prnt );
      prnt << "flatten: unknown formula label " << fm;
      err. push( std::move( bld ));
      return { };
   }

   // If it is UNF, we know that it is non-trivial.
   // Hence, we can only flatten into UNF.

   if( seq. at( ind ). is_dnf( ))
   {
      auto f1 = lift( seq. at( ind ). get_dnf( ),
                      seq. liftdist( ind ));

      auto f2 = calc::flatten(f1);

      if( f1. size( ) != f2. size( ) || !subsumes( f2, f1 ))
      {
         // Note that this is problematic. It relies on
         // weakness of subsumption. There should be some kind of
         // weight function based on offending operators.
         // Equality will probably also work.

         seq. hide( ind );
         auto lab = seq. nextlabel;
         seq. append( std::move(f2) );
         return lab; 
      }

      // If f1 is trivial, it may still be possible to transform into
      // CNF. I believe this should be put in separate functions.

      if( f1. size( ) == 1 && f1. at(0). vars. size( ) == 0 )
      {
         auto cnf1 = conjunction( { forall( f1. at(0). body ) } );
         auto cnf2 = calc::flatten( cnf1 );

         std::cout << "cnf1 = " << cnf1 << "\n";
         std::cout << "cnf2 = " << cnf2 << "\n";
         if( cnf1. size( ) != cnf2. size( ) || !subsumes( cnf2, cnf1 ))
         {
            seq. hide( ind ); 
            auto lab = seq. nextlabel; 
            seq. append( cnf2 );
            return lab;
         }
      }
   }

   if( seq. at( ind ). is_unf( ))
       throw std::logic_error( "this case is not handled" );

   throw std::logic_error( "flatten: unreachable" );
}


std::optional< calc::label > calc::proofchecker::normalize( label fm )
{
   size_t ind = seq. find( fm );
   if( ind == seq. stack. size( ))
   {        
      errorstack::builder bld;
      auto prnt = pretty_printer( bld, blfs );
      prnt << "normalize: unknown formula label " << fm;
      err. push( std::move( bld )); 
      return { };
   }

   // This is a repeating pattern that needs to be made into a function:

   if( seq. at( ind ). is_dnf( ))
   {        
      auto d = seq. at( ind ). get_dnf( );
      d = lift( std::move(d), seq. liftdist( ind ));
      seq. hide( ind );
      auto lab = seq. nextlabel;
      seq. append( ::normalize( blfs, std::move(d), 0 ));
      return lab;
   }

   throw std::logic_error( "normalize not finished" );
   return { };
}

bool 
calc::proofchecker::deflocal( std::string_view name, logic::term val )
{
   std::cout << "val = " << val << "\n";
   auto tp = checktype( val );

   if( !tp. has_value( ))
      throw std::logic_error( "def local, no type" );

   define( std::string( name ), val, tp. value( ));
   return true;
}


std::optional< calc::label > 
calc::proofchecker::instantiate( label fm,
                                 const std::vector< logic::term > & values )
{
   size_t ind = seq. find( fm );
   if( ind == seq. stack. size( ))   
   {
      errorstack::builder bld;
      bld << "instantiate: Unknown label for universal " << fm; 
      err. push( std::move( bld ));
      return { };
   }
    
   if( !seq. at( ind ). is_unf( ))
   {     
      errorstack::builder bld;
      auto prnt = pretty_printer( bld, blfs );
      bld << "instantiate, formula is not universal: " << seq. at( ind );
      err. push( std::move( bld ));
      return { };
   }

   if( seq. at( ind ). get_unf( ). vars. size( ) < values. size( ))
   {
      errorstack::builder bld;
      bld << "forallelim " << fm << " : ";
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
      std::cout << "i = " << i << "\n";
      auto inst = values. at(i);
      auto tp = checktype( inst );

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
            auto prt = pretty_printer( bld, blfs );
            prt << "true type of instance " << inst << " is wrong\n";
            prt << "It is " << tp. value( ) << ", but it must be ";
            prt << mainform. vars. at(i). tp;
            err. push( std::move( bld ));
         }
      }
      else
         std::cout << "had no value\n";
   }

   if( nrcorrecttypes != values. size( ))
   {
      auto bld = errorstack::builder( );
      bld << "unable to instantiate";
      err. push( std::move( bld ));
      return { };
   }

   // We do not remove the outermost forall, because its
   // presence is required by the data structure.
   // It is allowed that some variables remain.

   mainform. vars. erase( mainform. vars. begin( ),
                          mainform. vars. begin( ) + values. size( ));

   mainform = outermost( subst, std::move( mainform ), 0 );

   // We append mainform as CNF. The append function will
   // convert formula into a DNF is the quantification is empty.

   seq. hide( ind );
   auto lab = seq. nextlabel; 
   seq. append( conjunction( { mainform } ));
   return lab;

}


std::optional< calc::label > calc::proofchecker::simplify( )
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

   auto res = seq. nextlabel; 
   for( auto& cls : sat. checked )
   {
      // We don't add initial ones, because they are already there.

      if( !cls. seqind )
         seq. append( make_dnf( cls. disj ));
   }

   if( res != seq. nextlabel )
      return res;
   else
      return { };

}


std::optional< calc::label > calc::proofchecker::resolve( )
{  
   if( seq. decisions. size( ) == 0 )
      throw std::logic_error( "resolve: no decision" ); 

   std::cout << seq. decisions. back( ) << "\n";

   return { };
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
calc::proofchecker::checktype( logic::term& tm ) 
{
   size_t ss = seq. ctxt. size( );

   auto tp = checkandresolve( blfs, err, seq. ctxt, tm );

   if( seq. ctxt. size( ) != ss )
      throw std::logic_error( "context not restored" );

   return tp; 
}


logic::term calc::proofchecker::replacedebruijn( logic::term tm )
{
   std::cout << db. size( ) << " " << seq. ctxt. size( ) << "\n";

   if( db. size( ) != seq. ctxt. size( ))
      throw std::logic_error( "replacedebruijn: Sizes differ" );

   return logic::replace_debruijn( db, tm );
}

