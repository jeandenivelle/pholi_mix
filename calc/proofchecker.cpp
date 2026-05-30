
#include "proofchecker.h"

#include "outermost.h"
#include "localexpander.h"
#include "flatten.h"
#include "subsumption.h"

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
  
   size_t cc = seq. ctxt. size( );
   size_t ss = seq. stack. size( );

   // Assume the existentially quantified variables of alt:

   if( ex. vars. size( ) != eigen. size( ))
   {
      errorstack::builder bld;
      bld << "exists " << fm << " : ";
      bld << "number of eigenvariables is not right: ";
      bld << "it is " << eigen. size( );
      bld << ", but it must be " << ex. vars. size( );
      err. push( std::move( bld ));
      return { };
   }
   
   seq. hide( ind );
   seq. pushdecision( ind, choice );

   for( size_t v = 0; v != ex. vars. size( ); ++ v )
   {
      if( eigen. at(v). size( ) != 0 )
         seq. ctxt. assume( eigen. at(v), ex. vars[v]. tp );
      else 
         seq. ctxt. assume( "_", ex. vars[v]. tp );
   }

   auto lab = seq. nextlabel; 
   seq. append( disjunction( { std::move( ex ) } ));
   return lab; 
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
      // seq. pretty( prnt );
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
         seq. append( std::move(f2) );
         return { };  // The returns are incorrect.
      }

      // If f1 is trivial, it may still be possible to transform into
      // CNF. I believe this should be put in separate functions.

      if( f1. size( ) == 1 && f1. at(0). vars. size( ) == 0 )
      {
         auto cnf1 = conjunction( { forall( f1. at(0). body ) } );
         auto cnf2 = calc::flatten( cnf1 );

         if( cnf1. size( ) != cnf2. size( ) || !subsumes( cnf2, cnf1 ))
         {
            seq. hide( ind );
            seq. append( cnf2 );
            return { };
         }
      }
   }

   if( seq. at( ind ). is_unf( ))
       throw std::logic_error( "this case is not handled" );

   throw std::logic_error( "flatten: unreachable" );
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
   return logic::replace_debruijn( db, tm );
}

