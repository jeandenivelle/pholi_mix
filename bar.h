
#ifndef BAR_
#define BAR_

struct bar
{
   size_t len;
   explicit bar( size_t len = 70 )
      : len( len )
   { }
};

inline std::ostream& operator << ( std::ostream& out, bar br )
{
   for( size_t i = 0; i != br. len; ++ i )
      out. put( '-' );
   return out;
}

#endif

