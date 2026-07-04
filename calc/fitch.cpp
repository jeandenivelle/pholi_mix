
// This code was automatically built by TreeGen
// Written by Hans de Nivelle, see www.compiler-tools.eu

#include "tableau.h"

calc::tableau::tableau( const tableau& from )
   : _ssss( from. _ssss )
{
   // std::cout << "tableau( const tableau& " << from. _ssss << " )";
   
   switch( from. _ssss )
   {
   case tab_assume:
      repr. _fld00. heap = takeshare( from. repr. _fld00. heap );
      break;
   case tab_concl:
      repr. _fld01. heap = takeshare( from. repr. _fld01. heap );
      break;
   case tab_decide:
      repr. _fld02. heap = takeshare( from. repr. _fld02. heap );
      break;
   case tab_define:
      repr. _fld03. heap = takeshare( from. repr. _fld03. heap );
      break;
   case tab_empty:
      break;
   case tab_imp:
      repr. _fld05. heap = takeshare( from. repr. _fld05. heap );
      break;
   }
}

calc::tableau::tableau( tableau&& from ) noexcept
   : _ssss( from. _ssss )
{
   // std::cout << "tableau( tableau&& " << from. _ssss << " )";
   
   switch( from. _ssss )
   {
   case tab_assume:
      repr. _fld00. heap = from. repr. _fld00. heap;
      break;
   case tab_concl:
      repr. _fld01. heap = from. repr. _fld01. heap;
      break;
   case tab_decide:
      repr. _fld02. heap = from. repr. _fld02. heap;
      break;
   case tab_define:
      repr. _fld03. heap = from. repr. _fld03. heap;
      break;
   case tab_empty:
      break;
   case tab_imp:
      repr. _fld05. heap = from. repr. _fld05. heap;
      break;
   }

   // Leave from in trivial state:
   
   from. _ssss = tab_empty;
   new (&from. repr) options( );
}

// Note that the implementation of assignment is minimalistic.
// One should create special cases for when *this and from are 
// in the same state.

const calc::tableau & calc::tableau::operator = ( const tableau& from )
{
   if( this == &from )
      return *this;
   
   switch( from. _ssss )
   {
   case tab_assume:
      takeshare( from. repr. _fld00. heap );
      break;
   case tab_concl:
      takeshare( from. repr. _fld01. heap );
      break;
   case tab_decide:
      takeshare( from. repr. _fld02. heap );
      break;
   case tab_define:
      takeshare( from. repr. _fld03. heap );
      break;
   case tab_imp:
      takeshare( from. repr. _fld05. heap );
      break;
   }

   this -> ~tableau( );
   
   _ssss = from. _ssss;
   
   switch( _ssss )
   {
   case tab_assume:
      repr. _fld00. heap = from. repr. _fld00. heap;
      break;
   case tab_concl:
      repr. _fld01. heap = from. repr. _fld01. heap;
      break;
   case tab_decide:
      repr. _fld02. heap = from. repr. _fld02. heap;
      break;
   case tab_define:
      repr. _fld03. heap = from. repr. _fld03. heap;
      break;
   case tab_empty:
      break;
   case tab_imp:
      repr. _fld05. heap = from. repr. _fld05. heap;
      break;
   }

   return *this;
}

// We don't check self assignment in the moving case, because it is UB:

const calc::tableau & calc::tableau::operator = ( tableau&& from ) noexcept
{
   if( _ssss == from. _ssss )
   {
      switch( _ssss )
      {
      case tab_assume:
         dropshare( repr. _fld00. heap );
         repr. _fld00. heap = from. repr. _fld00. heap;
         break;
      case tab_concl:
         dropshare( repr. _fld01. heap );
         repr. _fld01. heap = from. repr. _fld01. heap;
         break;
      case tab_decide:
         dropshare( repr. _fld02. heap );
         repr. _fld02. heap = from. repr. _fld02. heap;
         break;
      case tab_define:
         dropshare( repr. _fld03. heap );
         repr. _fld03. heap = from. repr. _fld03. heap;
         break;
      case tab_empty:
         break;
      case tab_imp:
         dropshare( repr. _fld05. heap );
         repr. _fld05. heap = from. repr. _fld05. heap;
         break;
      }

      // Leave from in trivial state:

      from. _ssss = tab_empty;
      new (&from. repr) options( );
      return *this;
   }
   else
   {
      // I believe that this wll be safe, because we have
      // the only reference to other: 

      this -> ~tableau( );

      new (this) tableau( std::move( from ));
      return *this;
   }
}

calc::tableau::~tableau( ) noexcept
{
   // If there are prefix fields, they will be destroyed automatically

   switch( _ssss )
   {
   case tab_assume:
      dropshare( repr. _fld00. heap );
      break;
   case tab_concl:
      dropshare( repr. _fld01. heap );
      break;
   case tab_decide:
      dropshare( repr. _fld02. heap );
      break;
   case tab_define:
      dropshare( repr. _fld03. heap );
      break;
   case tab_empty:
      break;
   case tab_imp:
      dropshare( repr. _fld05. heap );
      break;
   }
}

bool calc::tableau::very_equal_to( const tableau & other ) const
{
   if( _ssss != other. _ssss )
      return false;

   switch( _ssss )
   {
   case tab_assume:
      if( repr. _fld00. heap != other. repr. _fld00. heap )
         return false;
      return true;
   case tab_concl:
      if( repr. _fld01. heap != other. repr. _fld01. heap )
         return false;
      return true;
   case tab_decide:
      if( repr. _fld02. heap != other. repr. _fld02. heap )
         return false;
      return true;
   case tab_define:
      if( repr. _fld03. heap != other. repr. _fld03. heap )
         return false;
      return true;
   case tab_empty:
      return true;
   case tab_imp:
      if( repr. _fld05. heap != other. repr. _fld05. heap )
         return false;
      return true;
   }
}

void calc::tableau::printstate( std::ostream& out ) const
{
   switch( _ssss )
   {
   case tab_assume:
      tvm::printstate( repr. _fld00. heap, out );
      break;
   case tab_concl:
      tvm::printstate( repr. _fld01. heap, out );
      break;
   case tab_decide:
      tvm::printstate( repr. _fld02. heap, out );
      break;
   case tab_define:
      tvm::printstate( repr. _fld03. heap, out );
      break;
   case tab_imp:
      tvm::printstate( repr. _fld05. heap, out );
      break;
   }
}

