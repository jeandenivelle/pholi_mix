
// Written by Hans de Nivelle, Oct 2023.
// Added hash and equal_to parameters in Sept 2024.
// Replaced iterators by indices on 2026.05.24. 
// Use of iterators was ridiculous because they are not stable. 

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
   std::vector< std::pair<K,V> > stack; 

public:
   indexedstack( ) noexcept = default;
   indexedstack( indexedstack&& ) noexcept = default;
   indexedstack& operator = ( indexedstack&& ) noexcept = default;

   size_t size( ) const { return stack. size( ); }
   bool empty( ) const { return stack. empty( ); }

   size_t push( const K& k, const V& v )
   {
      size_t s = stack. size( );
      stack. push_back( std::pair( k, v ));
      index[k]. push_back(s);
      return s;
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

   size_t find( const K& k )
   {
      auto p = index. find(k);
      if( p != index. end( ))
         return p -> second. back( );
      else 
         return stack. size( );
   }

   const std::pair<K,V> & at( size_t i ) const 
      { return stack. at(i); }

   std::pair<K,V> & at( size_t i ) 
      { return stack. at(i); }

   const std::pair<K,V> & back( ) const
      { return stack. back( ); }

   std::pair<K,V> & back( ) 
      { return stack. back( ); }

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


