#ifndef CC_HANDLER_HPP_
#define CC_HANDLER_HPP_

#include <boost/tuple/tuple.hpp>
#include <boost/tuple/tuple_comparison.hpp>

#include "util.hpp"
#include "cc.hpp"

extern "C" {
#include <stdint.h>
}

#include "objscip/objscip.h"

// cc_handler is a SCIP constraint and event handler that talks to our
// congruence closure implementation
//
// implementing both a constraint and an event handler in the same
// class; that should be OK

using boost::tuples::tuple;

typedef util::uintptr_variant<SCIP_VAR*, const string*> symbol;
typedef cc::context<symbol> context;
// typedef context::cnst cnst;
typedef unordered_map<SCIP_VAR*, SCIP_VAR*> vv_map;
typedef pair<SCIP_VAR*, SCIP_VAR*> vpair;
typedef unordered_map<vpair, SCIP_VAR*> dvar_map;
// typedef pair<cnst, cnst> cpair;
typedef util::with_offset<SCIP_VAR*> scip_ovar;

typedef util::uintptr_variant<SCIP_NODE*, void*> pnode;

class scip_callback: public cc::callback<symbol> {

private:
  
  SCIP* scip;
  int n_called;
  bool* node_infeasible;
  bool* bound_changed;
  const dvar_map* dvar_m;

  SCIP_VAR* get_dvar(SCIP_VAR*, SCIP_VAR*);
  SCIP_VAR* maybe_get_dvar(SCIP_VAR*, SCIP_VAR*);

public:

  scip_callback(SCIP* s, dvar_map* m, bool* ni, bool* b)
    : scip(s),
      n_called(0),
      node_infeasible(ni),
      bound_changed(b),
      dvar_m(m)
  {}

  virtual void operator()(symbol, symbol, llint);

};

class scip_callback_sol: public cc::callback<symbol> {

private:

  SCIP* scip;
  SCIP_SOL* sol;
  bool consistent;

public:

  bool get_consistent() const
  {
    return consistent;
  }

  scip_callback_sol(SCIP* s, SCIP_SOL* so)
    : scip(s),
      sol(so),
      consistent(true)
  {}

  virtual void operator()(symbol, symbol, llint);
  
};

typedef pair<vector<llint>, scip_ovar> ffc_offset;

struct compare_ffc_offset {
  bool operator()(const ffc_offset&, const ffc_offset&);
};

class cc_handler:
  
  public scip::ObjConshdlr,
  public scip::ObjEventhdlr

{

private:
  
  typedef pair<const string*, unsigned int> loc;
  typedef pair<loc, llint> loc_off;
  
  llint uf_call_cnt;
  bool node_infeasible;
  bool bound_changed;
  bool seen_node;
  boost::scoped_ptr<dvar_map> dvar_m;
  boost::scoped_ptr<scip_callback> cback;
  context ctx;

  // typedef-ing maps, because we frequently have to refer to the
  // types of their iterators

  typedef unordered_map<string, const string*> fun_symbol_map;
  fun_symbol_map fun_symbol_m;

  typedef tuple<const string*, scip_ovar, vector<scip_ovar> > fcall;

  typedef unordered_map<SCIP_VAR*, SCIP_VAR*> orig_var_map;
  orig_var_map orig_var_m;

  typedef unordered_map<SCIP_VAR*, vpair> dvar_rev_map;
  dvar_rev_map dvar_rev_m;

  typedef unordered_map<SCIP_VAR*, vector<llint> > dvar_offset_map;
  dvar_offset_map dvar_offset_m;

  // dvar_offset_map::iterator dvar_offset_rr_iterator;

  typedef unordered_map<pnode, bool> node_seen_map;
  node_seen_map node_seen_m;

  typedef unordered_map<loc, vector<scip_ovar> > loc_map;
  loc_map loc_m;

  // not exactly reverse of the above, but close enough
  typedef unordered_map<SCIP_VAR*, vector<loc_off> > loc_rev_map;
  loc_rev_map loc_rev_m;

  typedef unordered_map<vector<SCIP_VAR*>,
                        vector<ffc_offset> > ffcall_slave_map;
  typedef unordered_map<const string*, ffcall_slave_map> ffcall_map;

  ffcall_map ffcall_m;

  typedef pair<const string*, vector<llint> > fcall_lookup_key;
  typedef unordered_map<fcall_lookup_key, llint> fcall_lookup_map;
  
  vector<SCIP_VAR*> vars;
  vector<SCIP_VAR*> dvars;
  vector<pnode> frames;
  vector<fcall> fcalls;

  SCIP_VAR* orig_var(SCIP_VAR*);
  void catch_variable(SCIP_VAR*, bool);
  void catch_all_variables();

  /* difference vars (dvars) and branching on them */

  SCIP_VAR* add_dvar(SCIP_VAR*, SCIP_VAR*);
  SCIP_VAR* add_dvar(const scip_ovar&, const scip_ovar&);
  SCIP_VAR* get_dvar(SCIP_VAR*, SCIP_VAR*);
  bool branch_on_diff(const scip_ovar&, const scip_ovar&);
  bool branch_on_diff();

  /* stack management */
  
  void push_frame(pnode);
  void pop_frame();
  pnode current_node();
  void rewind_to_frame(pnode);
  bool node_in_frames(pnode);

  /* register function arguments: keep track of where they appear so
     that we will branch on and query about relevant pairs */

  void register_var(SCIP_VAR*);
  void register_ret(const string*,
                    const vector<scip_ovar>&,
                    const scip_ovar&);
  void register_arg(const string*, unsigned int, const scip_ovar&);

  void add_rval_dvars(ffcall_slave_map::const_iterator,
                      ffcall_slave_map::const_iterator);

  /* event sub-handlers for specific events (scip_exec does the
     dispatching) */

  SCIP_RETCODE scip_exec_nodefocused(SCIP_EVENT*);
  SCIP_RETCODE scip_exec_relaxed(SCIP_VAR*, SCIP_Real, SCIP_Real,
                                 SCIP_Real, SCIP_Real);
  SCIP_RETCODE scip_exec_lbrelaxed(SCIP_EVENT*);
  SCIP_RETCODE scip_exec_ubrelaxed(SCIP_EVENT*);

  /* extract and print info for debugging */

  void dbg_print_assignment(SCIP_SOL*, SCIP_VAR*);
  void dbg_print_assignment(SCIP_SOL*);

  /* "implementation" versions of handler methods, which do most of
     the work; they will be called from different places */

  void scip_prop_impl_ranges
  (const vector<SCIP_VAR*>&,
   const ffc_offset&,
   const vector<ffc_offset>&);
  void scip_prop_impl_ranges();
  SCIP_RESULT scip_prop_impl(bool);
  SCIP_RESULT scip_prop_impl(context&);
  SCIP_RESULT scip_check_impl(SCIP_SOL*);

public:

  cc_handler(SCIP*);

  virtual ~cc_handler();

  /* constraint handler methods */

  // mandatory methods
  
  virtual SCIP_DECL_CONSTRANS(scip_trans);

  virtual SCIP_DECL_CONSLOCK(scip_lock);

  virtual SCIP_DECL_CONSENFOLP(scip_enfolp);

  virtual SCIP_DECL_CONSENFOPS(scip_enfops);

  virtual SCIP_DECL_CONSCHECK(scip_check);

  // optional methods

  virtual SCIP_DECL_CONSPROP(scip_prop);

  virtual SCIP_DECL_CONSPRESOL(scip_presol);

  /* event handler */
  
  // mandatory methods

  virtual SCIP_DECL_EVENTEXEC(scip_exec);

  // optional methods

  virtual SCIP_RETCODE scip_init(SCIP*, SCIP_EVENTHDLR*);

  /* extra methods */

  void call(const scip_ovar&, const string&,
            const vector<scip_ovar>&);

  void finalize();
  
};

#endif
