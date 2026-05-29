
#include "proofchecker.h"

void calc::proofchecker::setgoal( logic::exact fname )
{
   std::cout << "setting goal: " << fname << "\n";

   std::cout << blfs << "\n";
   auto& blf = blfs. at( fname );

   seq = sequent( );

   switch( blf. sel( ))
   {
   case logic::bel_thm:
      {
         seq. ctxt. define( "goal", blf. view_form( ). fm( ),
                            logic::type( logic::type_form ));
         break;
      }

   default:
      throw std::logic_error( "belief not a formula" );
   }

    
   nrfakes = 0;
}


