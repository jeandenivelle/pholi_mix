
#include "beliefstate.h"
#include "pretty.h"


void 
logic::beliefstate::remove_candidates( identifier2exact& overloads,
                const identifier& id,
                logic::exact name ) 
{
   auto p = overloads. find( id );
   if( p != overloads. end( ))
   {
      if( p -> second. size( ) && p -> second. back( ) == name )
         p -> second. pop_back( );

      if( p -> second. size( ) == 0 )
         overloads. erase(p); 
   }
}

logic::exact logic::beliefstate::append( belief&& bl )
{

   switch( bl. sel( ))
   {
   case bel_struct:
      {
         auto exstruct = exact( vect. size( ));
            // The exact name that the struct will have.

         structdefs[ bl. ident( ) ]. push_back( exstruct );

         // We temporarily insert an empty belief, because we still need
         // access to bl later when we add the field functions and
         // the constructor. If we insert bl now, it moves 
         // with every insertion, which is annoying.
         // We still have to insert something because we need
         // the exactname. 
 
         vect. push_back( belief( bel_empty, identifier( ) ));

         auto exconstr = exact( vect. size( ));
         functions[ bl. ident( ) ]. push_back( exconstr );

         vect. push_back( belief( logic::bel_constr, bl. ident( ), exstruct )); 

         // We create the field functions:

         const structdef& sdef = bl. view_struct( ). def( ); 
            // sdef is not in vect. That would be dangerous,
            // because we are adding the fields as functions to vect.

         for( size_t offset = 0; offset != sdef. size( ); ++ offset )
         {
            auto fieldfunc = belief( logic::bel_fld, 
                                     sdef. at( offset ). name, 
                                     exstruct, offset );
            auto exfld = exact( vect. size( ));
            functions[ sdef. at( offset ). name ]. push_back( exfld ); 
            vect. push_back( std::move( fieldfunc ));
         }

         at( exstruct ) = std::move( bl );
            // We replace the temporary belief by bl. 

         return exstruct;
      }      

   case bel_symbol:
   case bel_def: 
      {
         exact ex = exact( vect. size( ));
         functions[ bl. ident( ) ]. push_back( ex );
         vect. push_back( std::move( bl ));
         return ex; 
      }

   case bel_thm:
   case bel_axiom:
      {
         exact ex = exact( vect. size( ));
         formulas[ bl. ident( ) ]. push_back( ex );
         vect. push_back( std::move( bl ));
         return ex;      
      }
   }

   std::cout << "dont know how to append : " << bl << "\n";
   throw std::runtime_error( "stopping" );
}


const std::vector< logic::exact > & 
logic::beliefstate::getstructdefs( const identifier& id ) const
{
   auto p = structdefs. find( id );
   if( p != structdefs. end( ))
      return p -> second;
   else
      return empty; 
}

const std::vector< logic::exact > & 
logic::beliefstate::getfunctions( const identifier& id ) const
{
   auto p = functions. find( id );
   if( p != functions. end( ))
      return p -> second;
   else
      return empty; 
}

const std::vector< logic::exact > & 
logic::beliefstate::getformulas( const identifier& id ) const
{
   auto p = formulas. find( id );
   if( p != formulas. end( ))
      return p -> second;
   else
      return empty;
}


namespace
{
   void print( std::ostream& out, const std::vector< logic::exact > & uses )
   {
      out << '{';
      for( auto p = uses. begin( ); p != uses. end( ); ++ p )
      {
         if( p != uses. begin( ))
            out << ", ";
         else
            out << " ";
         out << *p;
      }
      out << " }";
   }
}

void logic::beliefstate::print( std::ostream& out ) const
{
   out << "Beliefstate:\n"; 
   for( size_t i = 0; i != vect. size( ); ++ i )
   {
      out << vect[i]. ident( ) << '/' << exact(i) << "   "; 
      pretty::print( out, *this, vect[i] );
   }
   out << "\n";

   out << "Functions:\n";
   for( const auto& f : functions )
   {
      out << "   " << f. first << " :   ";
      ::print( out, f. second );
      out << '\n';
   }
   out << '\n';

   out << "Structdefs:\n";
   for( const auto& sdef : structdefs )
   {
      out << "   " << sdef. first << " :   ";
      ::print( out, sdef. second ); 
      out << '\n';
   }
   out << '\n';

   out << "Formulas:\n";
   for( const auto& f : formulas )
   {
      out << "   " << f. first << " :   ";
      ::print( out, f. second ); 
      out << '\n';
   }
   out << '\n';
}


