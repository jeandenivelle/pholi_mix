
#ifndef CALC_FILESCANNER_
#define CALC_FILESCANNER_

namespace calc
{

   struct filescanner
   {
      errorstack err;
      lexing::filereader inp;

      filescanner( )
      { }

      ~filescanner( );

      bool setinput( const std::filesystem::path& file );
         // We do not put this in the constructor,
         // because it might fail. In our view, constructors
         // should never fail, unless when out of memory.

      std::optional< logic::type > parsetype( errorstack& err );
      std::optional< logic::term > parseterm( errorstack& err );

      void move_errors( errorstack& global );
         // Move our errors to global, and append a header.

      void check( );
 
   };

}

#endif

