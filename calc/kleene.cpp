
#include "kleene.h"

const char* calc::getcstring( kleene kl )
{
   switch( kl )
   {
   case kleene_and:
      return "kleene-and";
   case kleene_or:
      return "kleene-or";
   case kleene_forall:
      return "kleene-forall";
   case kleene_exists:
      return "kleene-exists";
   }
   return "???";
}

