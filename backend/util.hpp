#ifndef UTIL_HPP_
#define UTIL_HPP_

#include <boost/variant.hpp>
#include <boost/variant/recursive_wrapper.hpp>
#include <boost/foreach.hpp>
#include <boost/static_assert.hpp>
#include <boost/scoped_ptr.hpp>
#include <boost/shared_ptr.hpp>
#include <boost/make_shared.hpp>
#include <boost/intrusive_ptr.hpp>
#include <boost/unordered_map.hpp>

#include <algorithm>
#include <iostream>
#include <stdint.h>

/* basic data structures */

using std::pair;
using std::list;
using std::string;
using std::vector;
using boost::unordered_map;
using boost::unordered_multimap;

/* smart pointers */

using boost::scoped_ptr;
using boost::shared_ptr;
using boost::make_shared;
using boost::intrusive_ptr;

/* variants */

using boost::variant;
using boost::recursive_variant_;
using boost::make_recursive_variant;
using boost::get;
using boost::bad_get;
using boost::apply_visitor;

/* I/O */

using std::cout;
using std::cerr;
using std::endl;

/* integer aliases */

typedef unsigned int uint;
typedef long long int llint;
typedef unsigned long long int ullint;

#define unreachable() assert(false);

namespace util {

  template <typename T>
  struct with_offset {

    T base;
    llint offset;

    with_offset(const T& b, llint o)
      : base(b), offset(o) {}

    template <typename U>
    with_offset(const with_offset<U>& wo)
      : base(wo.base), offset(wo.offset) {}

    virtual ~with_offset() {}

    bool operator==(const with_offset& wo) const
    {
      return offset == wo.offset && base == wo.base;
    }
    
  };

  template <typename T>
  std::size_t hash_value(const with_offset<T>& wot)
  {

    std::size_t rval = 0;

    boost::hash_combine(rval, wot.base);
    boost::hash_combine(rval, wot.offset);

    return rval;

  }

  template <typename T>
  with_offset<T> operator+(const with_offset<T>& o, llint x)
  {
    return with_offset<T>(o.base, o.offset + x);
  }

  template <typename T>
  with_offset<T>& operator+=(with_offset<T>& o, llint x)
  {
    o.offset += x;
    return o;
  }

  // if you modify this, also update string_of_error_code in .cpp
  enum error_code {
    ec_type = 0,
    ec_syntax,
    ec_backend,
    ec_id,
    ec_case,
    ec_api,
    ec_interrupted,
    ec_logic,
    ec_type_uf,
    ec_unimplemented,
    ec_sanity
  };

  string string_of_error_code(error_code);

  template <typename T, typename U, uintptr_t mask = 0x1>
  class uintptr_variant {

  private:

    BOOST_STATIC_ASSERT(sizeof(T) == sizeof(uintptr_t));
    BOOST_STATIC_ASSERT(sizeof(U) == sizeof(uintptr_t));

    uintptr_t p;

  public:

    uintptr_variant(T t): p((uintptr_t)t | mask) {}

    uintptr_variant(U u): p((uintptr_t)u) {}

    inline bool is_left() const
    {
      return p & mask;
    }

    inline bool is_right() const
    {
      return !(p & mask);
    }

    inline operator T() const
    {
      assert(is_left());
      return (T)(p ^ mask);
    }

    inline operator U() const
    {
      assert(is_right());
      return (U)p;
    }

    operator uintptr_t() const
    {
      return p;
    }

    bool operator==(uintptr_variant v) const
    {
      return p == v.p;
    }

  };

  template<typename T, typename U, uintptr_t mask>
  std::size_t hash_value(const util::uintptr_variant<T, U, mask>& v)
  {
    return boost::hash_value(uintptr_t(v));
  }

  template <typename T, uintptr_t mask = 0x1>
  class uintptr_cons_variant {

  private:

    typedef pair<uintptr_cons_variant, uintptr_cons_variant>* ppair;

    BOOST_STATIC_ASSERT(sizeof(T) == sizeof(uintptr_t));
    BOOST_STATIC_ASSERT(sizeof(ppair) == sizeof(uintptr_t));

    uintptr_t p;

  public:

    uintptr_cons_variant(T t): p(uintptr_t(t)) {}

    uintptr_cons_variant(ppair r): p(uintptr_t(r) | mask) {}


    inline bool is_pair() const
    {
      return p & mask;
    }

    inline ppair get_pair() const
    {
      return (ppair)(p ^ mask);
    }

    inline T get_ground() const
    {
      return (T)p;
    }

    bool operator==(uintptr_cons_variant v) const
    {
      return p == v.p;
    }

    operator uintptr_t() const
    {
      return p;
    }

  };

  template <typename T>
  bool vector_exists_eq(const vector<T>& v, const T& x)
  {
    BOOST_FOREACH (const T& x2, v)
      if (x == x2) return true;
    return false;
  }

  template <typename T>
  bool vector_all_eq(const vector<T>& v, const T& x)
  {
    BOOST_FOREACH (const T& x2, v)
      if (x != x2) return false;
    return true;
  }

}

#endif
