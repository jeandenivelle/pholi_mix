
// Written by Sabina Bralina and Hans de Nivelle, Fall 2023
// Made some fixes in August 2024. (It accepted setbelow(n,n). )

#ifndef RANKINGFUNCTION_
#define RANKINGFUNCTION_   

#include <iostream>
#include <unordered_map>
#include <unordered_set>
#include <queue>

template< typename V, typename H = std::hash<V>, typename E = std::equal_to<V>>
struct rankingfunction
{
   using set = std::unordered_set<V,H,E> ; 
   using queue = std::queue<V> ; 

   // We attach to each node a level (natural number),
   // and the set of its successors.

   // The ranks must be such that
   // v2 in reachable(v1) --> rank(v2) > rank(v1).

   struct vertdata
   {
      size_t rank;      // I think that size_t is reasonable, because
                        // the data structure has to fit in memory,
                        // and all lower rannks will occur.
                        // Using long unsigned int is unsafe because of 
                        // microsoft. 
      set successors;   // Direct successors (must have higher rank). 

      vertdata( ) :
         rank(0) 
      { } 

      void print( std::ostream& out ) const
      {
         out << "rank = " << rank << ", successors = {";
         for( auto p = successors. begin( ); p != successors. end( ); ++ p )
         {
            if( p != successors. begin( ))
               out << ", ";
            else
               out << " ";
            out << *p;
         }
         out << " }";
      }
   };

   std::unordered_map< V, vertdata, H, E > vert;
   E eq; 
      
public:  
   rankingfunction( ) = default;

   // Make sure that rank(v1) < rank(v2):

   bool setbelow( const V& v1, const V& v2 )
   {
      // We wouldn't detect this, because the vertex is added
      // at the end only.

      if( eq( v1, v2 ))
         return false;

      if( vert[v1].rank >= vert[v2].rank )
      {
         vert[v2]. rank = vert[v1]. rank + 1; 
         if( !update_above( v2, v1 ))
            return false; 
      }
     
      vert[v1]. successors. insert(v2);
      return true;
   }
         
   bool update_above( const V& v, const V& forbidden )
   {
      queue notsure; 
         // These are the vertices whose rank has been increased, and which
         // now could have a child with a too low rank. 
         // If you want to state it formally. If a vertix is not in notsure, 
         // then we are sure that its children have a rank higher than 
         // the rank of node.
          
      notsure. push(v);
      while( !notsure. empty( ))
      {
         V v = std::move( notsure. front() ); 
         notsure. pop(); 

         const auto& data = vert[v];
         size_t neededrank = data. rank + 1;
            // Minimal rank that a successor of v must have.

         // We go through the children of v, and check if they
         // have the minimal rank:

         for( const V& child : data. successors )
         {
            if( vert[ child ]. rank < neededrank )
            {
               // Rank too low:

               if( eq( child, forbidden ))
               {
                  return false; 
                     // We have a cycle. Game over. 
               }

               vert[ child ]. rank = neededrank;

               notsure. push( child );
                  // Now the children of child must be checked too.
            }
         }
      }
      return true;
   }

         
   void print(std::ostream& out) const
   {
      out << "Ranking Function:\n";
      for( auto& vert : vert )
      {
         out << "   ";
         out << vert. first << "   "; 
         out << vert. second << "\n";
      }
   }

};

#endif

