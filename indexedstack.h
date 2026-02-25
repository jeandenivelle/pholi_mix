
// Written by Hans de Nivelle, Oct 2023.
// Added hash and equal_to parameters in Sept 2024.

#ifndef INDEXEDSTACK_
#define INDEXEDSTACK_

#include <iostream>
#include <vector>
#include <unordered_map>

#include "util/print.h" 

// An indexedstack is a stack with an additional index for
// quick lookup of the last value. 

template< typename K, typename V, 
          typename H = std::hash<K>, typename E = std::equal_to<K> > 
class indexedstack
{
   std::unordered_map< K, std::vector< size_t >, H, E > index;
   std::vector<std::pair<K,V>> stack; 

public:
   indexedstack( ) noexcept = default;

   using iterator = typename std::vector< std::pair<K,V>> :: iterator; 
   using const_iterator = typename std::vector<std::pair<K,V>> :: const_iterator;

   iterator begin( ) { return stack. begin( ); }
   iterator end( ) { return stack. end( ); }

   const_iterator begin( ) const { return stack. begin( ); }
   const_iterator end( ) const { return stack. end( ); }

   const_iterator cbegin( ) const { return stack. cbegin( ); }
   const_iterator cend( ) const { return stack. cend( ); }

   size_t size( ) const { return stack. size( ); }
   bool empty( ) const { return stack. empty( ); }

   void push( const K& k, const V& v )
   {
      size_t s = stack. size( );
      stack. push_back( std::pair( k, v ));
      index[k]. push_back(s);
   }

   void pop( ) 
   {
      auto p = index. find( stack. back( ). first );
      p -> second. pop_back( );
      if( p -> second. empty( ))
         index. erase(p); 
      stack. pop_back( ); 
   }

   void restore( size_t s )
   {
      while( stack. size( ) > s )
         pop( );
   }

   iterator find( const K& k )
   {
      auto p = index. find(k);
      if( p != index. end( ))
         return stack. begin( ) + ( p -> second. back( ));
      else 
         return stack. end( );
   }

   const_iterator find( const K& k ) const
   {
      auto p = index. find(k);
      if( p != index. end( ))
         return stack. begin( ) + ( p -> second. back( ));
      else
         return stack. end( );
   }

   void print( std::ostream& out ) const
   requires requires( const K k, const V v, std::ostream out ) 
      { { out << k } -> std::same_as< std::ostream& > ; 
        { out << v } -> std::same_as< std::ostream& > ; }
   {
      out << "Indexedstack:\n";
      for( const auto& p : stack )
         out << "   " << p. first << " : " << p. second << "\n";
   }

};

#endif


