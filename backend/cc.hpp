#ifndef CC_HPP_
#define CC_HPP_

#define DEBUG

#include "util.hpp"

#include <boost/functional/hash.hpp>

// We provide an "abstract" congruence module, i.e., no references to
// SCIP are allowed. We accomplish this via templates (surprise,
// surprise). cc_solver "drives" the abstract CC implementation, i.e.,
// notifies us when the ILP solver branches, when we have to backtrack
// and so on.

// for the data structures and algorithms, see Niewenhuis & Oliveras,
// "Fast CC & Extensions"

// #define DEBUG

namespace cc {

  using util::with_offset;

  template <typename>
  class context;

  typedef unsigned int constant;

  struct opair {

    constant c1;
    constant c2;
    llint off;

    opair(constant x1, constant x2, llint o)
      : c1(x1), c2(x2), off(o)
    {}

  };

  template <typename T>
  class callback {

  public:

    virtual void operator()(T a, T b, llint o) = 0;

  };

  template <typename T>
  class context {

  private:

    bool consistent;

    typedef with_offset<T> o_t;
    // typedef typename offset<constant>::type o_constant;
    typedef pair<constant, llint> o_constant;
    typedef pair<constant, o_constant> app;

    // log entry for a class list update
    struct update {
      constant src;
      constant dst;
      llint offset;
      unsigned int use_length;
      update(constant s, constant d, llint o,
             unsigned int l)
        : src(s),
          dst(d),
          offset(o),
          use_length(l) {}
    };

    struct equation {
      app lhs;
      o_constant rhs;
      equation(app a, o_constant c): lhs(a), rhs(c) {}
    };
    
    // a frame groups the updates for a single "decision level"
    struct frame {
      vector<update> updates;
      vector<app> l_updates;
      frame(): updates(), l_updates() {}
    };

    unsigned int nxt;

    typedef unordered_map<app, constant> app_map;
    typedef pair<app, constant> app_map_pair;
    app_map app_m;

    typedef unordered_map<constant, T> symbol_map;
    typedef pair<constant, T> symbol_map_pair;
    symbol_map symbol_m;

    typedef unordered_map<T, constant> symbol_rev_map;
    typedef pair<T, constant> symbol_rev_map_pair;
    symbol_rev_map symbol_rev_m;

    typedef unordered_map<app, equation> lookup_map;
    typedef pair<app, equation> lookup_map_pair;
    lookup_map lookup_m;

    vector<opair> pending;
    vector<o_constant> repr_v;
    vector<list<o_constant> > class_v;
    vector<vector<equation> > use_v;
    vector<frame> frames;

    callback<T>* cb;

    inline void enqueue_pending(constant a, constant b, llint o)
    {
      pending.push_back(opair(a, b, o));
    }

    inline void enqueue_pending(o_constant a, o_constant b)
    {
      pending.push_back(opair(a.first, b.first,
                              b.second - a.second));
    }

    void merge_classes_call_back(constant a, constant b,
                                 llint o, bool all)
    {

      typename symbol_map::iterator it_a, it_b;

      BOOST_FOREACH (o_constant c1, class_v[a]) {
        it_a = symbol_m.find(c1.first);
        if (it_a == symbol_m.end()) continue;
        BOOST_FOREACH(o_constant c2, class_v[b]) {
          it_b = symbol_m.find(c2.first);
          if (it_b == symbol_m.end()) continue;
          cb->operator()(it_a->second,
                         it_b->second,
                         o + c2.second - c1.second);
          if (!all) return;
        }
      }

    }

    inline void merge_classes(constant a, constant b, llint o,
                              bool top)
    {

      // a = b + o

      assert(a != b);
      assert(!frames.empty());
      assert(repr_v[a].first == a);
      assert(repr_v[b].first == b);
      assert(!repr_v[a].second);
      assert(!repr_v[b].second);

      list<o_constant>& c_a = class_v[a];
      list<o_constant>& c_b = class_v[b];
      int n = 0;

      // if (!top)
      //   merge_classes_call_back(a, b, o, true);

      frames.back().updates.push_back(update(a, b, o, 0));

      BOOST_FOREACH (o_constant c, c_a) {
        assert(repr_v[c.first].second == - c.second);
        repr_v[c.first] = o_constant(b, o - c.second);
        c_b.push_back(o_constant(c.first, c.second - o));
      }

      assert(repr_v[a].first == repr_v[b].first);
      assert(repr_v[a].second - repr_v[b].second == o);

      BOOST_FOREACH (equation& eq, use_v[a]) {
        app p = repr(eq.lhs);
        typename lookup_map::iterator it = lookup_m.find(p);
        if (it != lookup_m.end()) {
          const equation& eq2 = it->second;
          enqueue_pending(eq.rhs, eq2.rhs);
        } else {
          lookup_m.insert(lookup_map_pair(p, eq));
          frames.back().l_updates.push_back(p);
          use_v[b].push_back(eq);
          n++;
        }
      }

      BOOST_FOREACH (list<o_constant>& lo, class_v) {
        if (lo.empty()) continue;
#ifdef DEBUG
        cout << "{ ";
        BOOST_FOREACH (o_constant& o, lo)
          cout << "$" << o.first << " + " << o.second << ", ";
        cout << "}\n";
#endif
      }

      // when we backtrack, we will just have to erase the last cnt
      // elements of use_v[b]
      frames.back().updates.back().use_length = n;

      // we will not erase the contents of use_v[a] and class_v[a]: we
      // are allowed to do this because a will never again be the
      // representative of a class; when we backtrack, we will just
      // use the old contents

    }

    inline void propagate(constant a, constant b, llint o, bool top)
    {

      // { a = b + o }

      const o_constant& a_prime = repr_v[a];
      const o_constant& b_prime = repr_v[b];
      constant v_a = a_prime.first, v_b = b_prime.first;
      llint o_a = a_prime.second, o_b = b_prime.second;
      
      // { v_a + o_a = v_b + o_b + o }

      if (v_a == v_b) {
        if (o_a != o_b + o) consistent = false;
        return;
      }

      if (class_v[v_a].size() <= class_v[v_b].size())
        merge_classes(v_a, v_b, o + o_b - o_a, top);
      else
        merge_classes(v_b, v_a, o_a - o_b - o, top);

    }

    void propagate()
    {

      while (!pending.empty()) {

        opair& p = pending.back();
        constant a = p.c1;
        constant b = p.c2;
        llint o = p.off;
        pending.pop_back();
        
        propagate(a, b, o, false);

        if (!consistent) {
          pending.erase(pending.begin(), pending.end());
          return;
        }

        typename symbol_map::iterator
          it_a = symbol_m.find(a),
          it_b = symbol_m.find(b);

        if (it_a != symbol_m.end()) {
          assert(it_b != symbol_m.end());
          cb->operator()(it_a->second, it_b->second, o);
        }
        
      }

    }

    void init_constant(constant c)
    {

      assert(repr_v.size() == c);
      assert(class_v.size() == c);
      assert(use_v.size() == c);
      
      repr_v.push_back(o_constant(c, 0));
      class_v.push_back(list<o_constant>(1, o_constant(c, 0)));
      use_v.push_back(vector<equation>());

      assert(repr_v[c].first == c);
      assert(repr_v[c].second == 0);
      assert(class_v[c].front().first == c);
      assert(class_v[c].front().second == 0);

    }

    inline constant get_constant(T a)
    {

      typename symbol_rev_map::const_iterator it =
        symbol_rev_m.find(a);

      if (it != symbol_rev_m.end()) return it->second;

      assert(frames.empty());

      constant rval(nxt++);
      symbol_rev_m.emplace(symbol_rev_map_pair(a, rval));
      init_constant(rval);
      symbol_m.insert(symbol_map_pair(rval, a));

      return rval;

    }

    constant get_constant(constant a, const o_constant& oc, llint o)
    {

      assert(frames.empty());

      app p(a, oc);
      typename app_map::const_iterator it =  app_m.find(p);

      if (it != app_m.end()) {
        assert(!o);
        return it->second;
      }

      constant rval(nxt++);
      app_m.emplace(p, rval);
      init_constant(rval);

      equation eq(p, o_constant(rval, o));
      lookup_m.emplace(p, eq);
      use_v[a].push_back(eq);
      use_v[oc.first].push_back(eq);

      return rval;

    }

    o_constant get_o_constant(const o_t& x)
    {
      return o_constant(get_constant(x.base), x.offset);
    }

    o_constant repr(const o_constant& o)
    {
      o_constant r = repr_v[o.first];
      return o_constant(r.first, r.second + o.second);
    }

    app repr(const app& a) {
      assert(repr_v[a.first].second == 0);
      // assert(repr_v[a.first].first == a.first);
      o_constant r = repr(a.second);
      return app(repr_v[a.first].first, r);
    }

  public:

    context(callback<T>* cback)
      /* TODO: more fields need initialization */
      : consistent(true),
        nxt(0),
        app_m(),
        symbol_m(),
        symbol_rev_m(),
        lookup_m(),
        pending(),
        repr_v(),
        class_v(),
        use_v(),
        frames(),
        cb(cback) {}

    context(const context& ctx, callback<T>* cback)
      : consistent(true),
        nxt(ctx.nxt),
        app_m(ctx.app_m),
        symbol_m(ctx.symbol_m),
        symbol_rev_m(ctx.symbol_rev_m),
        lookup_m(),
        pending(),
        repr_v(),
        class_v(),
        use_v(),
        frames(),
        cb(cback)
    {

      unreachable();

      assert(ctx.pending.empty());

      for (unsigned int i = 0; i < nxt; i++)
        init_constant(i);

      // looks reasonable; double-check
      typename app_map::iterator it = app_m.begin();
      while (it != app_m.end()) {
        const app& a = it->first;
        constant c = it->second;
        equation eq(a, o_constant(c, 0));
        lookup_m.emplace(a, eq);
        use_v[a.first].push_back(eq);
        use_v[a.second.first].push_back(eq);
        it++;
      }

    }

    // just push an empty frame to stack
    void push_frame()
    {
      assert(consistent);
      frames.push_back(frame());
    }

    // undo the updates described by the top frame
    void pop_frame()
    {

      assert(!frames.empty());
      assert(pending.empty());

      vector<update>& updates = frames.back().updates;
      vector<app>& l_updates = frames.back().l_updates;

      typename vector<update>::reverse_iterator r_it =
        updates.rbegin();
      while (r_it < updates.rend()) {
        constant src = r_it->src;
        constant dst = r_it->dst;
        list<o_constant>& c_dst = class_v[dst];
        // elements of class_v[src] never left
        list<o_constant>& c_src = class_v[src];
        BOOST_FOREACH (o_constant c, c_src) {
          assert(repr_v[c.first].first == dst);
          repr_v[c.first] = o_constant(src, - c.second);
        }
        // ugly code begin
        typename list<o_constant>::iterator it = c_dst.begin();
        llint size_diff = c_dst.size() - c_src.size();
        for (int i = 0; i < size_diff; i++) it++;
        c_dst.erase(it, c_dst.end());
        use_v[dst].erase(use_v[dst].end() - r_it->use_length,
                         use_v[dst].end());
        r_it++;
      }

      BOOST_FOREACH (const app& a, l_updates)
        lookup_m.erase(a);

      consistent = true;

      frames.pop_back();

    }

    void merge(T a, T b, llint o)
    {

      if (!consistent) return;

      constant
        cnst_a = get_constant(a),
        cnst_b = get_constant(b);

#ifdef DEBUG
      cout << "merge: " << cnst_a << " and " << cnst_b
           << " with offset " << o << endl;
#endif

      const o_constant& repr_a = repr_v[cnst_a];
      const o_constant& repr_b = repr_v[cnst_b];
      if (repr_a.first == repr_b.first) {
        if (repr_a.second != repr_b.second + o)
          consistent = false;
        return;
      }

      assert(pending.empty());
      propagate(cnst_a, cnst_b, o, true);
      propagate();

    }

    void call(o_t r, T f, const vector<o_t>& v)
    {

      // r = r_v + r_c = f(v)

      const T& r_v = r.base;
      const llint& r_c = r.offset;

      assert (!v.empty());

      constant c =
        get_constant(get_constant(f), get_o_constant(v[0]),
                     v.size() == 1 ? r_c : 0);

      if (v.size() > 1) {
        typename vector<o_t>::const_iterator it = v.begin() + 1;
        while (it < v.end() - 1) {
          c = get_constant(c, get_o_constant(*it), 0);
          it++;
        }
        c = get_constant(c, get_o_constant(*it), r_c);
      }
        
      symbol_m.insert(symbol_map_pair(c, r_v));
      symbol_rev_m.insert(symbol_rev_map_pair(r_v, c));

    }

    bool get_consistent()
    {
      return consistent;
    }

  };

}

#undef DEBUG

#endif
