
#include <compare>

#include "projection.h"


logic::term
calc::projection::operator( ) ( logic::term tm, size_t vardepth, bool& change )
{  
   const auto* fld = getfuncbelief( tm, logic::bel_fld );
   if( !fld )
      return tm;

   const auto& first = tm. view_apply( ). arg(0);
   const auto* constr = getfuncbelief( first, logic::bel_constr );
   if( !constr )
      return tm;

   logic::exact tp1 = fld -> view_field( ). sdef( );
   logic::exact tp2 = constr -> view_constr( ). tp( );

   if( tp1 != tp2 ) 
      return tm;
 
   size_t offset = fld -> view_field( ). offset( );

   if( offset >= first. view_apply( ). size( ))
      throw std::logic_error( "offset is too big, it cannot happen" );

   auto res = first. view_apply( ). arg( offset );
   if( tm. view_apply( ). size( ) > 1 )
   { 
      res = logic::term( logic::op_apply, 
                         res, std::initializer_list< logic::term > ( ));

      for( size_t i = 1; i < tm. view_apply( ). size( ); ++ i )
         res. view_apply( ). push_back( tm. view_apply( ). arg(i));
   }

   change = true;
   ++ counter;
   return res;
}

void calc::projection::print( std::ostream& out ) const
{
   out << "projection(" << counter << ")";
}


const logic::belief* 
calc::projection::getfuncbelief( const logic::term& tm, 
                                 logic::selector sel ) const
{
   if( tm. sel( ) != logic::op_apply )
      return nullptr;

   auto appl = tm. view_apply( );
   if( appl. size( ) < 1 )
      return nullptr; 
   
   const auto& f = appl. func( );
   if( f. sel( ) != logic::op_exact )
      return nullptr;

   auto ex = f. view_exact( ). ex( );
   const auto& bel = blfs. at( ex );
   if( bel. sel( ) != sel )
      return nullptr;

   return &bel;
}


