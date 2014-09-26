#ifndef CC_HANDLER_H_
#define CC_HANDLER_H_

#ifdef __cplusplus /* begin C++ declarations */

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
typedef unordered_map<SCIP_VAR*, SCIP_VAR*> vv_map;
typedef pair<SCIP_VAR*, SCIP_VAR*> vpair;
typedef unordered_map<vpair, SCIP_VAR*> dvar_map;
typedef util::with_offset<SCIP_VAR*> scip_ovar;

struct dp;

struct cut_gen;

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
  
  llint uf_call_cnt;
  bool node_infeasible;
  bool bound_changed;
  bool seen_node;
  boost::scoped_ptr<dvar_map> dvar_m;
  boost::scoped_ptr<scip_callback> cback;
  context ctx;
  dp* ocaml_dp;
  cut_gen* ocaml_cut_gen;

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

  dvar_offset_map ocaml_dvar_offset_m;

  // dvar_offset_map::iterator dvar_offset_rr_iterator;

  typedef unordered_map<SCIP_NODE*, bool> node_seen_map;
  node_seen_map node_seen_m;
  node_seen_map node_seen_ocg_m;

  typedef unordered_map<loc, vector<scip_ovar> > loc_map;
  loc_map loc_m;

  typedef unordered_map<vector<SCIP_VAR*>,
                        vector<ffc_offset> > ffcall_slave_map;
  typedef unordered_map<const string*, ffcall_slave_map> ffcall_map;

  ffcall_map ffcall_m;

  typedef pair<const string*, vector<llint> > fcall_lookup_key;
  typedef pair<llint, const fcall * const> fcall_lookup_data;
  typedef unordered_map<fcall_lookup_key, fcall_lookup_data>
	  fcall_lookup_map;

  const fcall* conflict_fcall1;
  const fcall* conflict_fcall2;
  
  vector<SCIP_VAR*> vars;
  vector<SCIP_VAR*> dvars;
  vector<SCIP_NODE*> frames;
  vector<SCIP_NODE*> frames_ocg;
  vector<fcall> fcalls;
  vector<SCIP_VAR*> catchq;

  SCIP_VAR* orig_var(SCIP_VAR*);
  void catch_variable(SCIP_VAR*, bool);
  void catch_all_variables();

  /* difference vars (dvars) and branching on them */

  SCIP_VAR* add_dvar(SCIP_VAR*, SCIP_VAR*);
  SCIP_VAR* add_dvar(const scip_ovar&, const scip_ovar&);
  SCIP_VAR* get_dvar(SCIP_VAR*, SCIP_VAR*);
  bool branch_on_diff(const scip_ovar&, const scip_ovar&);
  
  /* branching high-level methods */

  bool branch_on_last_cc_conflict();
  bool branch_on_cc_diff();
  bool branch_on_ocaml_diff();
  SCIP_RESULT cut_or_branch(bool);

  /* stack management */
  
  void push_frame(SCIP_NODE*);
  void pop_frame();
  SCIP_NODE* current_node();
  void rewind_to_frame(SCIP_NODE*);
  bool node_in_frames(SCIP_NODE*);

  /* cutgen stack management (ocg stands for OCaml Cut Generation) */

  void push_frame_ocg(SCIP_NODE*);
  void pop_frame_ocg();
  SCIP_NODE* current_node_ocg();
  void rewind_to_frame_ocg(SCIP_NODE*);
  bool node_in_frames_ocg(SCIP_NODE*);
  void scip_exec_nodefocused_ocg(SCIP_NODE*);
  
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

  cc_handler(SCIP*, dp*, cut_gen*);

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

  void catch_var_events_impl(SCIP_VAR*);

  void catch_var_events(SCIP_VAR*);

  void finalize();

  void include();

  SCIP_VAR* ocaml_add_dvar(SCIP_VAR*, SCIP_VAR*, llint);

  const int scip_sepafreq_;

};

#else /* end C++ declarations */

typedef struct cc_handler cc_handler;

#endif

#ifdef __cplusplus
extern "C" {
#endif

#if defined(__STDC__) || defined(__cplusplus) // ANSI C prototypes
	extern cc_handler* new_cc_handler(SCIP* s,
					  struct dp*,
					  struct cut_gen*);
	extern void delete_cc_handler(cc_handler*);
	extern void cc_handler_call(cc_handler*,
				    SCIP_VAR*, llint, char*,
				    unsigned int, SCIP_VAR**, llint*);
	extern void cc_handler_finalize(cc_handler*);
	extern void cc_handler_include(cc_handler*);
	extern SCIP_VAR* cc_handler_zero_var(cc_handler*);
	extern SCIP_VAR* cc_handler_add_dvar(cc_handler*,
					     SCIP_VAR*,
					     SCIP_VAR*,
					     llint);
	extern void cc_handler_catch_var_events(cc_handler*, SCIP_VAR*);
	extern uintptr_t uintptr_t_of_var(SCIP_VAR*);
	extern uintptr_t uintptr_t_of_node(SCIP_NODE*);
#else // K&R style prototypes
	extern cc_handler* new_cc_handler();
	extern void delete_cc_handler();
	extern void cc_handler_call();
	extern void cc_handler_finalize();
	extern void cc_handler_include();
	extern SCIP_VAR* cc_handler_zero_var();
	extern SCIP_VAR* cc_handler_add_dvar();
	extern void cc_handler_catch_var_events();
	extern uintptr_t uintptr_t_of_var();
	extern uintptr_t uintptr_t_of_node();
#endif

#ifdef __cplusplus
}
#endif

#endif
