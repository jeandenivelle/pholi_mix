
// This code was automatically built by TreeGen
// Written by Hans de Nivelle, see www.compiler-tools.eu

#ifndef CALC_TABLEAU_
#define CALC_TABLEAU_

#include <iostream>
#include <utility>
#include <tuple>
#include <initializer_list>
#include "selector.h"


#line 19 "calc/treedefs.rec"
#include "tvm/concepts.h"
   #include "tvm/includes.h"
   #include <vector>
   #include "logic/term.h"
   #include "label.h"


namespace calc { 




#line 27 "calc/treedefs.rec"
bool very_equal( const std::vector< logic::vartype > & v1, 
                  const std::vector< logic::vartype > & v2 );
   class tableau
   {
   private:
      selector _ssss;

      using _loc00 = tvm::unit;
      using _scal00 = std::vector<logic::vartype>;
      using _rep00 = tableau;
      using _loc01 = tvm::unit;
      using _scal01 = std::tuple<label,logic::term,std::string>;
      using _rep01 = tvm::unit;
      using _loc02 = tvm::unit;
      using _scal02 = logic::term;
      using _rep02 = tableau;
      using _loc03 = tvm::unit;
      using _scal03 = std::pair<logic::vartype,logic::term>;
      using _rep03 = tableau;
      using _loc04 = tvm::unit;
      using _scal04 = tvm::unit;
      using _rep04 = tvm::unit;
      using _loc05 = tvm::unit;
      using _scal05 = int;
      using _rep05 = tvm::unit;

      static constexpr bool check = true;

      union options
      {
         tvm::field< _loc00, _scal00, _rep00 > _fld00;
         tvm::field< _loc01, _scal01, _rep01 > _fld01;
         tvm::field< _loc02, _scal02, _rep02 > _fld02;
         tvm::field< _loc03, _scal03, _rep03 > _fld03;
         tvm::field< _loc04, _scal04, _rep04 > _fld04;
         tvm::field< _loc05, _scal05, _rep05 > _fld05;

         options( ) : _fld04( ) { }
         ~options( ) noexcept { }
      };

   private:
      options repr;

   public:
      tableau( ) = delete;
      tableau( const tableau& );
      tableau( tableau&& ) noexcept;
      const tableau& operator = ( const tableau& );
      const tableau& operator = ( tableau&& ) noexcept;
      ~tableau( ) noexcept;
      
      selector sel( ) const { return _ssss; }
      bool very_equal_to( const tableau& ) const;
      void printstate( std::ostream& out ) const;
      
      template< tvm::const_iterator< _rep00 > It >
      tableau( selector sel, const std::vector<logic::vartype> & _xx00, It begin, It end )
         : _ssss( sel )
      {
         if constexpr( check )
         {
            switch( _ssss )
            {
            case tab_assume:
               break;
            default:
               throw std::invalid_argument( "wrong selector for constructor" );
            }
         }
         repr. _fld00. heap = takeshare( tvm::constr_scalar_vector< _scal00, _rep00 > ( _xx00, begin, end ));
      }

      tableau( selector sel, const std::vector<logic::vartype> & _xx00, std::initializer_list< _rep00 > repeated )
         : tableau( sel, _xx00, repeated. begin( ), repeated. end( ) )
      { }

      tableau( selector sel, const label & _xx00, const logic::term & _xx01, const std::string & _xx02 )
         : _ssss( sel )
      {
         if constexpr( check )
         {
            switch( _ssss )
            {
            case tab_concl:
               break;
            default:
               throw std::invalid_argument( "wrong selector for constructor" );
            }
         }
         repr. _fld01. heap = takeshare( tvm::constr_scalar< _scal01 > ( std::tuple( _xx00, _xx01, _xx02 ) ));
      }

      template< tvm::const_iterator< _rep02 > It >
      tableau( selector sel, const logic::term & _xx00, It begin, It end )
         : _ssss( sel )
      {
         if constexpr( check )
         {
            switch( _ssss )
            {
            case tab_decide:
               break;
            default:
               throw std::invalid_argument( "wrong selector for constructor" );
            }
         }
         repr. _fld02. heap = takeshare( tvm::constr_scalar_vector< _scal02, _rep02 > ( _xx00, begin, end ));
      }

      tableau( selector sel, const logic::term & _xx00, std::initializer_list< _rep02 > repeated )
         : tableau( sel, _xx00, repeated. begin( ), repeated. end( ) )
      { }

      template< tvm::const_iterator< _rep03 > It >
      tableau( selector sel, const logic::vartype & _xx00, const logic::term & _xx01, It begin, It end )
         : _ssss( sel )
      {
         if constexpr( check )
         {
            switch( _ssss )
            {
            case tab_define:
               break;
            default:
               throw std::invalid_argument( "wrong selector for constructor" );
            }
         }
         repr. _fld03. heap = takeshare( tvm::constr_scalar_vector< _scal03, _rep03 > ( std::pair( _xx00, _xx01 ), begin, end ));
      }

      tableau( selector sel, const logic::vartype & _xx00, const logic::term & _xx01, std::initializer_list< _rep03 > repeated )
         : tableau( sel, _xx00, _xx01, repeated. begin( ), repeated. end( ) )
      { }

      tableau( selector sel )
         : _ssss( sel )
      {
         if constexpr( check )
         {
            switch( _ssss )
            {
            case tab_empty:
               break;
            default:
               throw std::invalid_argument( "wrong selector for constructor" );
            }
         }
      }

      tableau( selector sel, const int & _xx00 )
         : _ssss( sel )
      {
         if constexpr( check )
         {
            switch( _ssss )
            {
            case tab_imp:
               break;
            default:
               throw std::invalid_argument( "wrong selector for constructor" );
            }
         }
         repr. _fld05. heap = takeshare( tvm::constr_scalar< _scal05 > ( _xx00 ));
      }

      bool option_is_assume( ) const noexcept
      {
         switch( _ssss )
         {
         case tab_assume:
            return true;
         default:
            return false;
         }
      }

      struct const_assume
      {
         const tableau* _xxxx;
         const tableau & operator * ( ) const { return * _xxxx; }
         const_assume( const tableau* _xxxx ) : _xxxx( _xxxx ) { }

         const std::vector<logic::vartype> & aaaa( ) const { return _xxxx -> repr. _fld00. heap -> scal; }
         size_t size( ) const { return _xxxx -> repr. _fld00. heap -> size( ); }
         const tableau & sub( size_t _iiii ) const
            { return _xxxx -> repr. _fld00. heap -> begin( ) [ _iiii ]; }
      };

      const_assume view_assume( ) const
      {
         if constexpr( check )
         {
            if( !option_is_assume( ))
               throw std::invalid_argument( "wrong selector for view" );
         }
         return this;
      }

      struct mut_assume
      {
         tableau* _xxxx;
         mut_assume( tableau* _xxxx ) : _xxxx( _xxxx ) { }
         const tableau & operator * ( ) const { return * _xxxx; }

         const std::vector<logic::vartype> & aaaa( ) const { return _xxxx -> repr. _fld00. heap -> scal; }
         std::vector<logic::vartype> extr_aaaa( ) const {
            if( iswritable( _xxxx -> repr. _fld00. heap ))
               return std::move( _xxxx -> repr. _fld00. heap -> scal );
            else
               return _xxxx -> repr. _fld00. heap -> scal;
         }
         void update_aaaa( const std::vector<logic::vartype> & repl ) const
         {
            if( tvm::distinct( _xxxx -> repr. _fld00. heap -> scal, repl ))
            {
               _xxxx -> repr. _fld00. heap = takeshare( replacebywritable( _xxxx -> repr. _fld00. heap ));
               _xxxx -> repr. _fld00. heap -> scal = repl;
            }
         }

         size_t size( ) const { return _xxxx -> repr. _fld00. heap -> size( ); }
         void push_back( const tableau & xx00 ) const
         {
            _xxxx -> repr. _fld00. heap = tvm::push_back( _xxxx -> repr. _fld00. heap, xx00 );
         }
         void pop_back( ) const { _xxxx -> repr. _fld00. heap = tvm::pop_back( _xxxx -> repr. _fld00. heap ); }
         const tableau& sub( size_t _iiii ) const
            { return _xxxx -> repr. _fld00. heap -> begin( ) [ _iiii ]; }
         tableau extr_sub( size_t _iiii ) const
         {
            if( iswritable( _xxxx -> repr. _fld00. heap ))
               return std::move( _xxxx -> repr. _fld00. heap -> begin( ) [ _iiii ] );
            else
               return _xxxx -> repr. _fld00. heap -> begin( ) [ _iiii ];
         }
         void update_sub( size_t _iiii, const tableau & repl ) const
         {
            if( tvm::distinct( _xxxx -> repr. _fld00. heap -> begin( ) [ _iiii ], repl ))
            {
               _xxxx -> repr. _fld00. heap = takeshare( replacebywritable( _xxxx -> repr. _fld00. heap ));
               _xxxx -> repr. _fld00. heap -> begin( ) [ _iiii ] = repl;
            }
         }
      };

      mut_assume view_assume( )
      {
         if constexpr( check )
         {
            if( !option_is_assume( ))
               throw std::invalid_argument( "wrong selector for view" );
         }
         return this;
      }
      
      bool option_is_conclusion( ) const noexcept
      {
         switch( _ssss )
         {
         case tab_concl:
            return true;
         default:
            return false;
         }
      }

      struct const_conclusion
      {
         const tableau* _xxxx;
         const tableau & operator * ( ) const { return * _xxxx; }
         const_conclusion( const tableau* _xxxx ) : _xxxx( _xxxx ) { }

         const label & lab( ) const { return get<0> ( _xxxx -> repr. _fld01. heap -> scal ); }
         const logic::term & fm( ) const { return get<1> ( _xxxx -> repr. _fld01. heap -> scal ); }
         const std::string & comment( ) const { return get<2> ( _xxxx -> repr. _fld01. heap -> scal ); }
      };

      const_conclusion view_conclusion( ) const
      {
         if constexpr( check )
         {
            if( !option_is_conclusion( ))
               throw std::invalid_argument( "wrong selector for view" );
         }
         return this;
      }

      struct mut_conclusion
      {
         tableau* _xxxx;
         mut_conclusion( tableau* _xxxx ) : _xxxx( _xxxx ) { }
         const tableau & operator * ( ) const { return * _xxxx; }

         const label & lab( ) const { return get<0> ( _xxxx -> repr. _fld01. heap -> scal ); }
         label extr_lab( ) const {
            if( iswritable( _xxxx -> repr. _fld01. heap ))
               return std::move( get<0> ( _xxxx -> repr. _fld01. heap -> scal ) );
            else
               return get<0> ( _xxxx -> repr. _fld01. heap -> scal );
         }
         void update_lab( const label & repl ) const
         {
            if( tvm::distinct( get<0> ( _xxxx -> repr. _fld01. heap -> scal ), repl ))
            {
               _xxxx -> repr. _fld01. heap = takeshare( replacebywritable( _xxxx -> repr. _fld01. heap ));
               get<0> ( _xxxx -> repr. _fld01. heap -> scal ) = repl;
            }
         }
         const logic::term & fm( ) const { return get<1> ( _xxxx -> repr. _fld01. heap -> scal ); }
         logic::term extr_fm( ) const {
            if( iswritable( _xxxx -> repr. _fld01. heap ))
               return std::move( get<1> ( _xxxx -> repr. _fld01. heap -> scal ) );
            else
               return get<1> ( _xxxx -> repr. _fld01. heap -> scal );
         }
         void update_fm( const logic::term & repl ) const
         {
            if( tvm::distinct( get<1> ( _xxxx -> repr. _fld01. heap -> scal ), repl ))
            {
               _xxxx -> repr. _fld01. heap = takeshare( replacebywritable( _xxxx -> repr. _fld01. heap ));
               get<1> ( _xxxx -> repr. _fld01. heap -> scal ) = repl;
            }
         }
         const std::string & comment( ) const { return get<2> ( _xxxx -> repr. _fld01. heap -> scal ); }
         std::string extr_comment( ) const {
            if( iswritable( _xxxx -> repr. _fld01. heap ))
               return std::move( get<2> ( _xxxx -> repr. _fld01. heap -> scal ) );
            else
               return get<2> ( _xxxx -> repr. _fld01. heap -> scal );
         }
         void update_comment( const std::string & repl ) const
         {
            if( tvm::distinct( get<2> ( _xxxx -> repr. _fld01. heap -> scal ), repl ))
            {
               _xxxx -> repr. _fld01. heap = takeshare( replacebywritable( _xxxx -> repr. _fld01. heap ));
               get<2> ( _xxxx -> repr. _fld01. heap -> scal ) = repl;
            }
         }
      };

      mut_conclusion view_conclusion( )
      {
         if constexpr( check )
         {
            if( !option_is_conclusion( ))
               throw std::invalid_argument( "wrong selector for view" );
         }
         return this;
      }
      
      bool option_is_decide( ) const noexcept
      {
         switch( _ssss )
         {
         case tab_decide:
            return true;
         default:
            return false;
         }
      }

      struct const_decide
      {
         const tableau* _xxxx;
         const tableau & operator * ( ) const { return * _xxxx; }
         const_decide( const tableau* _xxxx ) : _xxxx( _xxxx ) { }

         const logic::term & fm( ) const { return _xxxx -> repr. _fld02. heap -> scal; }
         size_t size( ) const { return _xxxx -> repr. _fld02. heap -> size( ); }
         const tableau & sub( size_t _iiii ) const
            { return _xxxx -> repr. _fld02. heap -> begin( ) [ _iiii ]; }
      };

      const_decide view_decide( ) const
      {
         if constexpr( check )
         {
            if( !option_is_decide( ))
               throw std::invalid_argument( "wrong selector for view" );
         }
         return this;
      }

      struct mut_decide
      {
         tableau* _xxxx;
         mut_decide( tableau* _xxxx ) : _xxxx( _xxxx ) { }
         const tableau & operator * ( ) const { return * _xxxx; }

         const logic::term & fm( ) const { return _xxxx -> repr. _fld02. heap -> scal; }
         logic::term extr_fm( ) const {
            if( iswritable( _xxxx -> repr. _fld02. heap ))
               return std::move( _xxxx -> repr. _fld02. heap -> scal );
            else
               return _xxxx -> repr. _fld02. heap -> scal;
         }
         void update_fm( const logic::term & repl ) const
         {
            if( tvm::distinct( _xxxx -> repr. _fld02. heap -> scal, repl ))
            {
               _xxxx -> repr. _fld02. heap = takeshare( replacebywritable( _xxxx -> repr. _fld02. heap ));
               _xxxx -> repr. _fld02. heap -> scal = repl;
            }
         }

         size_t size( ) const { return _xxxx -> repr. _fld02. heap -> size( ); }
         void push_back( const tableau & xx00 ) const
         {
            _xxxx -> repr. _fld02. heap = tvm::push_back( _xxxx -> repr. _fld02. heap, xx00 );
         }
         void pop_back( ) const { _xxxx -> repr. _fld02. heap = tvm::pop_back( _xxxx -> repr. _fld02. heap ); }
         const tableau& sub( size_t _iiii ) const
            { return _xxxx -> repr. _fld02. heap -> begin( ) [ _iiii ]; }
         tableau extr_sub( size_t _iiii ) const
         {
            if( iswritable( _xxxx -> repr. _fld02. heap ))
               return std::move( _xxxx -> repr. _fld02. heap -> begin( ) [ _iiii ] );
            else
               return _xxxx -> repr. _fld02. heap -> begin( ) [ _iiii ];
         }
         void update_sub( size_t _iiii, const tableau & repl ) const
         {
            if( tvm::distinct( _xxxx -> repr. _fld02. heap -> begin( ) [ _iiii ], repl ))
            {
               _xxxx -> repr. _fld02. heap = takeshare( replacebywritable( _xxxx -> repr. _fld02. heap ));
               _xxxx -> repr. _fld02. heap -> begin( ) [ _iiii ] = repl;
            }
         }
      };

      mut_decide view_decide( )
      {
         if constexpr( check )
         {
            if( !option_is_decide( ))
               throw std::invalid_argument( "wrong selector for view" );
         }
         return this;
      }
      
      bool option_is_define( ) const noexcept
      {
         switch( _ssss )
         {
         case tab_define:
            return true;
         default:
            return false;
         }
      }

      struct const_define
      {
         const tableau* _xxxx;
         const tableau & operator * ( ) const { return * _xxxx; }
         const_define( const tableau* _xxxx ) : _xxxx( _xxxx ) { }

         const logic::vartype & var( ) const { return _xxxx -> repr. _fld03. heap -> scal. first; }
         const logic::term & val( ) const { return _xxxx -> repr. _fld03. heap -> scal. second; }
         size_t size( ) const { return _xxxx -> repr. _fld03. heap -> size( ); }
         const tableau & sub( size_t _iiii ) const
            { return _xxxx -> repr. _fld03. heap -> begin( ) [ _iiii ]; }
      };

      const_define view_define( ) const
      {
         if constexpr( check )
         {
            if( !option_is_define( ))
               throw std::invalid_argument( "wrong selector for view" );
         }
         return this;
      }

      struct mut_define
      {
         tableau* _xxxx;
         mut_define( tableau* _xxxx ) : _xxxx( _xxxx ) { }
         const tableau & operator * ( ) const { return * _xxxx; }

         const logic::vartype & var( ) const { return _xxxx -> repr. _fld03. heap -> scal. first; }
         logic::vartype extr_var( ) const {
            if( iswritable( _xxxx -> repr. _fld03. heap ))
               return std::move( _xxxx -> repr. _fld03. heap -> scal. first );
            else
               return _xxxx -> repr. _fld03. heap -> scal. first;
         }
         void update_var( const logic::vartype & repl ) const
         {
            if( tvm::distinct( _xxxx -> repr. _fld03. heap -> scal. first, repl ))
            {
               _xxxx -> repr. _fld03. heap = takeshare( replacebywritable( _xxxx -> repr. _fld03. heap ));
               _xxxx -> repr. _fld03. heap -> scal. first = repl;
            }
         }
         const logic::term & val( ) const { return _xxxx -> repr. _fld03. heap -> scal. second; }
         logic::term extr_val( ) const {
            if( iswritable( _xxxx -> repr. _fld03. heap ))
               return std::move( _xxxx -> repr. _fld03. heap -> scal. second );
            else
               return _xxxx -> repr. _fld03. heap -> scal. second;
         }
         void update_val( const logic::term & repl ) const
         {
            if( tvm::distinct( _xxxx -> repr. _fld03. heap -> scal. second, repl ))
            {
               _xxxx -> repr. _fld03. heap = takeshare( replacebywritable( _xxxx -> repr. _fld03. heap ));
               _xxxx -> repr. _fld03. heap -> scal. second = repl;
            }
         }

         size_t size( ) const { return _xxxx -> repr. _fld03. heap -> size( ); }
         void push_back( const tableau & xx00 ) const
         {
            _xxxx -> repr. _fld03. heap = tvm::push_back( _xxxx -> repr. _fld03. heap, xx00 );
         }
         void pop_back( ) const { _xxxx -> repr. _fld03. heap = tvm::pop_back( _xxxx -> repr. _fld03. heap ); }
         const tableau& sub( size_t _iiii ) const
            { return _xxxx -> repr. _fld03. heap -> begin( ) [ _iiii ]; }
         tableau extr_sub( size_t _iiii ) const
         {
            if( iswritable( _xxxx -> repr. _fld03. heap ))
               return std::move( _xxxx -> repr. _fld03. heap -> begin( ) [ _iiii ] );
            else
               return _xxxx -> repr. _fld03. heap -> begin( ) [ _iiii ];
         }
         void update_sub( size_t _iiii, const tableau & repl ) const
         {
            if( tvm::distinct( _xxxx -> repr. _fld03. heap -> begin( ) [ _iiii ], repl ))
            {
               _xxxx -> repr. _fld03. heap = takeshare( replacebywritable( _xxxx -> repr. _fld03. heap ));
               _xxxx -> repr. _fld03. heap -> begin( ) [ _iiii ] = repl;
            }
         }
      };

      mut_define view_define( )
      {
         if constexpr( check )
         {
            if( !option_is_define( ))
               throw std::invalid_argument( "wrong selector for view" );
         }
         return this;
      }
      
      bool option_is_empty( ) const noexcept
      {
         switch( _ssss )
         {
         case tab_empty:
            return true;
         default:
            return false;
         }
      }

      struct const_empty
      {
         const tableau* _xxxx;
         const tableau & operator * ( ) const { return * _xxxx; }
         const_empty( const tableau* _xxxx ) : _xxxx( _xxxx ) { }
      };

      const_empty view_empty( ) const
      {
         if constexpr( check )
         {
            if( !option_is_empty( ))
               throw std::invalid_argument( "wrong selector for view" );
         }
         return this;
      }

      struct mut_empty
      {
         tableau* _xxxx;
         mut_empty( tableau* _xxxx ) : _xxxx( _xxxx ) { }
         const tableau & operator * ( ) const { return * _xxxx; }
      };

      mut_empty view_empty( )
      {
         if constexpr( check )
         {
            if( !option_is_empty( ))
               throw std::invalid_argument( "wrong selector for view" );
         }
         return this;
      }
      
      bool option_is_importance( ) const noexcept
      {
         switch( _ssss )
         {
         case tab_imp:
            return true;
         default:
            return false;
         }
      }

      struct const_importance
      {
         const tableau* _xxxx;
         const tableau & operator * ( ) const { return * _xxxx; }
         const_importance( const tableau* _xxxx ) : _xxxx( _xxxx ) { }

         const int & imp( ) const { return _xxxx -> repr. _fld05. heap -> scal; }
      };

      const_importance view_importance( ) const
      {
         if constexpr( check )
         {
            if( !option_is_importance( ))
               throw std::invalid_argument( "wrong selector for view" );
         }
         return this;
      }

      struct mut_importance
      {
         tableau* _xxxx;
         mut_importance( tableau* _xxxx ) : _xxxx( _xxxx ) { }
         const tableau & operator * ( ) const { return * _xxxx; }

         const int & imp( ) const { return _xxxx -> repr. _fld05. heap -> scal; }
         int extr_imp( ) const {
            if( iswritable( _xxxx -> repr. _fld05. heap ))
               return std::move( _xxxx -> repr. _fld05. heap -> scal );
            else
               return _xxxx -> repr. _fld05. heap -> scal;
         }
         void update_imp( const int & repl ) const
         {
            if( tvm::distinct( _xxxx -> repr. _fld05. heap -> scal, repl ))
            {
               _xxxx -> repr. _fld05. heap = takeshare( replacebywritable( _xxxx -> repr. _fld05. heap ));
               _xxxx -> repr. _fld05. heap -> scal = repl;
            }
         }
      };

      mut_importance view_importance( )
      {
         if constexpr( check )
         {
            if( !option_is_importance( ))
               throw std::invalid_argument( "wrong selector for view" );
         }
         return this;
      }
      
   };
}

#endif

