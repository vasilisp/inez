#include "cc_handler.h"
#include "scip_utils.hpp"

#include <boost/utility.hpp>
#include <algorithm>
#include <cstdlib>
#include <stdint.h>

// #define DEBUG0
// #define DEBUG1
// #define DEBUG2

#ifdef DEBUG2
#define DEBUG1
#endif

#ifdef DEBUG1
#define DEBUG0
#endif

#define BRANCH_CONFLICT
#define PROP_RANGES

// potentially not portable stuff

typedef int HRESULT;
typedef struct { unsigned char data[16]; } IID;

struct dp {
  virtual HRESULT QueryInterface(int iid, void** p) = 0;
  virtual unsigned long AddRef() = 0;
  virtual unsigned long Release() = 0;
  virtual void push_level();
  virtual void backtrack();
  virtual SCIP_RESULT propagate();
  virtual bool check(SCIP_SOL*);
  virtual bool branch();
};

struct cut_gen {
  virtual HRESULT QueryInterface(int iid, void** p) = 0;
  virtual unsigned long AddRef() = 0;
  virtual unsigned long Release() = 0;
  virtual void push_level();
  virtual void backtrack();
  virtual SCIP_RESULT generate();
  virtual bool check(SCIP_SOL*);
};

#define ASSERT_SCIP_POINTER(s) \
  assert((s) == scip::ObjEventhdlr::scip_);

/* utilities */

inline const char* var_id(SCIP_VAR *v)
{
  static const char* null_id = "NULL";
  return (v ? SCIPvarGetName(v) : null_id);
}

bool lex_compare(const vector<llint>& v1, const vector<llint>& v2)
{
  return std::lexicographical_compare(v1.begin(), v1.end(),
                                      v2.begin(), v2.end());
}

bool compare_ffc_offset::operator()(const ffc_offset& fo1,
                                    const ffc_offset& fo2)
{

  const scip_ovar& ov1 = fo1.second;
  const scip_ovar& ov2 = fo2.second;

  if (lex_compare(fo1.first, fo2.first)) return true;
  if (lex_compare(fo2.first, fo1.first)) return false;
  if (ov1.base < ov2.base) return true;
  if (ov2.base < ov1.base) return false;

  return ov1.offset < ov2.offset;

}

/* scip_callback methods */

SCIP_VAR* scip_callback::get_dvar(SCIP_VAR* v1, SCIP_VAR* v2)
{

  assert(v1 > v2);

  if (!v2) return v1;
  
  dvar_map::const_iterator it =
    v1 > v2 ?
    dvar_m->find(vpair(v1, v2)) :
    dvar_m->find(vpair(v2, v1));

  assert(it != dvar_m->end());

  return it->second;
    
}

void scip_callback::operator()(symbol a, symbol b, llint x)
{

  bool ch = false, infeasible = false;
  SCIP_VAR* v_a = a;
  SCIP_VAR* v_b = b;
  SCIP_VAR* dv = NULL;

#ifdef DEBUG1
  cout << "[CP] " << var_id(a) << " = " << var_id(b)
       << " + " << x << endl;
#endif

  if (v_a > v_b) {
    dv = get_dvar(v_a, v_b);
    ch = scip_fix_variable(scip, dv, x, &infeasible);
  } else {
    dv = get_dvar(v_b, v_a);
    ch = scip_fix_variable(scip, dv, -x, &infeasible);
  }

#ifdef DEBUG1
  if (ch)
    cout << "[CP] bound changed\n";
  else
    cout << "[CP] bound did not change\n";
#endif
  
  if (infeasible) {
#ifdef DEBUG1
    cout << "[CP] infeasible\n";
#endif
    *node_infeasible = true;
  }

#ifdef DEBUG1
  fflush(stdout);
#endif

  *bound_changed = *bound_changed || ch;

}

/* scip_callback_sol methods */

void scip_callback_sol::operator()(symbol a, symbol b, llint x)
{

  assert(a.is_left());
  assert(b.is_left());
  SCIP_VAR* v_a = a;
  SCIP_VAR* v_b = b;
  assert(v_a != v_b);

  llint val_a =
    v_a ? my_llint(scip, SCIPgetSolVal(scip, sol, a)) : 0;
  llint val_b =
    v_b ? my_llint(scip, SCIPgetSolVal(scip, sol, b)) : 0;

#ifdef DEBUG1
  cout << "[DB] "
       << var_id(v_a) << " = " << val_a << ", "
       << var_id(v_b) << " = " << val_b << ", "
       << "diff is " << x << endl;
  fflush(stdout);
#endif
  
  if (val_a != val_b + x) consistent = false;

}

/* cc_handler methods */

cc_handler::cc_handler(SCIP* scip, dp* d, cut_gen* c)
  : scip::ObjConshdlr(scip, "cc", "congruence closure",
                      -100000, -100000, -100000,
                      0, 1, 0, -1,
                      TRUE, TRUE, TRUE, FALSE,
                      1),
    scip::ObjEventhdlr(scip, "cce", "congruence closure events"),
    uf_call_cnt(0),
    bound_changed(false),
    seen_node(false),
    node_infeasible(false),
    dvar_m(new dvar_map()),
    ocaml_dp(d),
    ocaml_cut_gen(c),
    cback(new scip_callback(scip, dvar_m.get(), &node_infeasible,
                            &bound_changed)),
    ctx(cback.get()),
    fun_symbol_m(),
    orig_var_m(),
    dvar_rev_m(),
    dvar_offset_m(),
    ocaml_dvar_offset_m(),
    node_seen_m(),
    node_seen_ocg_m(),
    loc_m(),
    ffcall_m(),
    conflict_fcall1(NULL),
    conflict_fcall2(NULL),
    vars(),
    dvars(),
    frames(),
    frames_ocg(),
    fcalls(),
    catchq()
{}

cc_handler::~cc_handler()
{
  
  SCIP*& scip = scip::ObjEventhdlr::scip_;

  BOOST_FOREACH (SCIP_VAR* dv, dvars)
    SCIPreleaseVar(scip, &dv);

  BOOST_FOREACH (SCIP_VAR* v, vars)
    if (v) SCIPreleaseVar(scip, &v);

}

SCIP_VAR* cc_handler::orig_var(SCIP_VAR* v)
{

  vv_map::const_iterator it = orig_var_m.find(v);

  assert(it != orig_var_m.end());

  return it->second;

}

void cc_handler::catch_variable(SCIP_VAR* v, bool catch_bound)
{

  SCIP*& scip = scip::ObjEventhdlr::scip_;
  SCIP_EVENTHDLR* eh = SCIPfindEventhdlr(scip, "cce");
  SCIP_VAR* v_trans;

  assert(eh);

  sa(SCIPcaptureVar(scip, v));
  
  // SCIPcatchVarEvent expects a transformed variable; create one
  sa(SCIPtransformVar(scip, v, &v_trans));
  sa(SCIPcaptureVar(scip, v_trans));
  
  orig_var_m.emplace(v_trans, v);

  if (catch_bound) {
    sa(SCIPcatchVarEvent
       (scip, v_trans, SCIP_EVENTTYPE_LBRELAXED, eh,
        NULL, NULL));
    sa(SCIPcatchVarEvent
       (scip, v_trans, SCIP_EVENTTYPE_UBRELAXED, eh,
        NULL, NULL));
 }
  sa(SCIPcatchVarEvent
     (scip, v_trans, SCIP_EVENTTYPE_VARDELETED, eh,
      NULL, NULL));

}

SCIP_VAR* cc_handler::add_dvar(SCIP_VAR* v1, SCIP_VAR* v2)
{

  assert(v1);
  assert(v1 > v2);

  SCIP*& scip = scip::ObjEventhdlr::scip_;
  vpair vp(v1, v2);
  SCIP_VAR* dv;
  dvar_map::const_iterator it = dvar_m->find(vp);

  if (it != dvar_m->end()) return it->second;
  
  if (v2) {
    dv = scip_dvar(scip, v1, v2);
#ifdef DEBUG1
    cout << "[DV] " << var_id(dv) << " = "
         << var_id(v1) << " - " << var_id(v2) << endl;
#endif

    sa(SCIPcaptureVar(scip, dv));
  } else
    dv = v1;

  dvars.push_back(dv);
  if (v2) dvar_m->emplace(vp, dv);
  dvar_rev_m.emplace(dv, vp);

  return dv;

}

SCIP_VAR* cc_handler::ocaml_add_dvar(SCIP_VAR* v1, SCIP_VAR* v2,
                                     llint o, bool reg)
{

  assert(v1 > v2);

  SCIP_VAR* rval = add_dvar(v1, v2);

  if (!reg) return rval;

  dvar_offset_map::iterator it = ocaml_dvar_offset_m.find(rval);

  if (it != ocaml_dvar_offset_m.end()) {
    vector<llint>& vlli = it->second;
    if (!util::vector_exists_eq<llint>(vlli, o)) vlli.push_back(o);
  } else
    ocaml_dvar_offset_m.emplace(rval, vector<llint>(1, o));

  return rval;
  
}

SCIP_VAR* cc_handler::add_dvar(const scip_ovar& ov1,
                               const scip_ovar& ov2)
{

  SCIP_VAR* v1 = ov1.base;
  SCIP_VAR* v2 = ov2.base;
  llint d = ov2.offset - ov1.offset;
  assert(v1 > v2);
  SCIP_VAR* rval = add_dvar(v1, v2);
  dvar_offset_map::iterator it = dvar_offset_m.find(rval);

  if (it != dvar_offset_m.end()) {
    vector<llint>& vlli = it->second;
    if (!util::vector_exists_eq<llint>(vlli, d)) vlli.push_back(d);
  } else
    dvar_offset_m.emplace(rval, vector<llint>(1, d));

  return rval;

}

inline SCIP_VAR* cc_handler::get_dvar(SCIP_VAR* v1, SCIP_VAR* v2)
{

  assert(v1 > v2);

  if (!v2) return v1;

  vpair vp(v1 > v2 ? v1 : v2, v1 > v2 ? v2 : v1);
  dvar_map::const_iterator it = dvar_m->find(vp);

  assert(it != dvar_m->end());

  return it->second;
    
}

inline bool branch_around_val(SCIP* scip, SCIP_VAR* v, llint x)
{

  SCIP_Real
    lb = SCIPvarGetLbLocal(v),
    ub = SCIPvarGetUbLocal(v);

  if ((SCIPisEQ(scip, lb, x) && SCIPisEQ(scip, ub, x)) ||
      SCIPisLT(scip, ub, x) ||
      SCIPisGT(scip, lb, x))
    return false;
  
  scip_branch_around_val(scip, v, x);
  return true;

}

bool cc_handler::branch_on_diff(const scip_ovar& ov1,
                                const scip_ovar& ov2)
{

  SCIP_VAR* const& v1 = ov1.base;
  SCIP_VAR* const& v2 = ov2.base;

  if (v1 == v2) return false;
  if (v2 > v1) return branch_on_diff(ov2, ov1);

  assert(v1 > v2);
  SCIP*& scip = scip::ObjEventhdlr::scip_;
  SCIP_VAR* dv = get_dvar(v1, v2);
  llint d = ov2.offset - ov1.offset;

  return branch_around_val(scip, dv, d);

}

bool cc_handler::branch_on_last_cc_conflict()
{

  if (!conflict_fcall1 || !conflict_fcall2) return false;

  const vector<scip_ovar> a1 = conflict_fcall1->get<2>();
  const vector<scip_ovar> a2 = conflict_fcall2->get<2>();
  vector<scip_ovar>::const_iterator it1 = a1.begin();
  vector<scip_ovar>::const_iterator it2 = a2.begin();

  while (it1 != a1.end()) {
    assert (it2 != a2.end());
    if (branch_on_diff(*it1, *it2)) {
      conflict_fcall1 = NULL;
      conflict_fcall2 = NULL;
      return true;
    }
    it1++;
    it2++;
  }

  const scip_ovar& ov1 = conflict_fcall1->get<1>();
  const scip_ovar& ov2 = conflict_fcall2->get<1>();

  if (branch_on_diff(ov1, ov2)) return true;

  return false;

}

bool cc_handler::branch_on_cc_diff()
{

  loc_map::iterator it = loc_m.begin();

  while (it != loc_m.end()) {
    vector<scip_ovar>& v = it->second;
    vector<scip_ovar>::const_iterator it1 = v.begin();
    while (it1 != v.end()) {
      const scip_ovar& ov1 = *it1;
      vector<scip_ovar>::const_iterator it2 = it1 + 1;
      while (it2 != v.end()) {
        const scip_ovar& ov2 = *it2;
        if (branch_on_diff(ov1, ov2)) return true;
        it2++;
      }
      it1++;
    }
    it++;
  }

  return false;
  
}


SCIP_NODE* cc_handler::current_node_ocg()
{
  
  assert(ocaml_cut_gen);
  assert(!seen_node || !frames_ocg.empty());
  
  return seen_node ? frames_ocg.back() : NULL;

}

void cc_handler::push_frame_ocg(SCIP_NODE* n)
{

  if (!ocaml_cut_gen) return;
  
  frames_ocg.push_back(n);
  ocaml_cut_gen->push_level();
  node_seen_ocg_m.emplace(n, true);
  
}

void cc_handler::pop_frame_ocg()
{

  assert(ocaml_cut_gen);
  SCIP_NODE* n = current_node_ocg();

  ocaml_cut_gen->backtrack();
  frames_ocg.pop_back();
  node_seen_ocg_m.erase(n);

}

void cc_handler::push_frame(SCIP_NODE* n)
{
  frames.push_back(n);
  ctx.push_frame();
  if (ocaml_dp) ocaml_dp->push_level();
  assert(ctx.get_consistent());
  node_seen_m.emplace(n, true);
}

void cc_handler::pop_frame()
{

  assert(!frames.empty());
  SCIP_NODE* cn = frames.back();
  
  node_infeasible = false;
  frames.pop_back();
  ctx.pop_frame();
  if (ocaml_dp) ocaml_dp->backtrack();
  node_seen_m.erase(cn);

}

SCIP_NODE* cc_handler::current_node()
{
  assert(!frames.empty());
  return frames.back();
}

// rewind the stack till we find the target node
void cc_handler::rewind_to_frame(SCIP_NODE* node)
{
  while (true) {
    // assert(!frames.empty());
    // CHECKME
    if (frames.empty()) return;
    SCIP_NODE* n = frames.back();
    if (node == n)
      return;
    else
      pop_frame();
  }
}

bool cc_handler::node_in_frames(SCIP_NODE* node)
{
  return (node_seen_m.find(node) != node_seen_m.end());
}

bool cc_handler::node_in_frames_ocg(SCIP_NODE* node)
{
  return (node_seen_ocg_m.find(node) != node_seen_ocg_m.end());
}

void cc_handler::dbg_print_assignment(SCIP_SOL* sol, SCIP_VAR* v)
{

  SCIP*& scip = scip::ObjEventhdlr::scip_;
  SCIP_Real val = SCIPgetSolVal(scip, sol, v),
    lb = SCIPvarGetLbLocal(v),
    ub = SCIPvarGetUbLocal(v);

  cout << "[SOL] " << var_id(v) << " = " << val;
  if (SCIPisEQ(scip, lb, val) && SCIPisEQ(scip, ub, val)) {
    assert(SCIPisEQ(scip, lb, ub));
    cout << " (fixed)\n";
  } else {
    cout << " in [" << lb << ", " << ub << ']' << endl;
  }
  
  if (SCIPisLE(scip, lb, val) && SCIPisLE(scip, val, ub)) return;
  cout << "[W!] SCIP numerical issues (?)" << endl;
  assert(sol);
  fflush(stdout);
  // unreachable();

}

void cc_handler::dbg_print_assignment(SCIP_SOL* sol)
{

  cout << "[SOL:BEGIN]\n";

  BOOST_FOREACH (SCIP_VAR* dv, dvars)
    if (dv) dbg_print_assignment(sol, dv);

  BOOST_FOREACH (SCIP_VAR* v, vars)
    if (v) dbg_print_assignment(sol, v);

  cout << "[SOL:END]\n";

}

bool cc_handler::scip_prop_impl_ranges
(const vector<SCIP_VAR*>& v,
 const ffc_offset& fo,
 const vector<ffc_offset>& vfo)
{

  SCIP*& scip = scip::ObjEventhdlr::scip_;

  const vector<llint>& vl = fo.first;
  const scip_ovar& ov = fo.second;
  SCIP_VAR* const var = ov.base;

  uint n = v.size();
  SCIP_Real lb[n], ub[n];
  bool found_not_null = false;

  uint count_within_bounds_target = 1;
  for (uint i = 0; i < n; i++) {
    SCIP_VAR* const var2 = v[i];
    if (var2) {
      found_not_null = true;
      lb[i] = SCIPvarGetLbLocal(var2);
      ub[i] = SCIPvarGetUbLocal(var2);
      if (SCIPisGT(scip, ub[i] - lb[i], 1000)) return false;
      assert(lb[i] != -SCIPinfinity(scip));
      assert(ub[i] != SCIPinfinity(scip));
      lb[i] += vl[i];
      ub[i] += vl[i];
    } else {
      lb[i] = vl[i];
      ub[i] = vl[i];
    }
    count_within_bounds_target *= (ub[i] - lb[i] + 1);
  }

  assert(found_not_null);

  uint count_within_bounds = 0;
  SCIP_Real lbn = SCIPinfinity(scip), ubn = -SCIPinfinity(scip);
  BOOST_FOREACH (const ffc_offset& fo2, vfo) {
    const vector<llint>& vl2 = fo2.first;
    const scip_ovar& ov2 = fo2.second;
    SCIP_VAR* const& var2 = ov2.base;
    const llint& o2 = ov2.offset;
    bool within_bounds = true;
    for (uint i = 0; i < n; i++) {
      const llint& l = vl2[i];
      if (l < lb[i] || l > ub[i]) {
        within_bounds = false;
        break;
      }
    }
    if (within_bounds) {
      SCIP_Real
        lb_candidate = (var2 ? SCIPvarGetLbLocal(var2) : 0) + o2,
        ub_candidate = (var2 ? SCIPvarGetUbLocal(var2) : 0) + o2;
      if (SCIPisLE(scip, lb_candidate, lbn)) lbn = lb_candidate;
      if (SCIPisGE(scip, ub_candidate, ubn)) ubn = ub_candidate;
      count_within_bounds++;
    }
  }

  assert(count_within_bounds <= count_within_bounds_target);
  if (count_within_bounds_target != count_within_bounds ||
      SCIPisLE(scip, lbn, -SCIPinfinity(scip)) ||
      SCIPisGE(scip, ubn, SCIPinfinity(scip)))
    return false;

  ubn -= ov.offset;
  lbn -= ov.offset;

  SCIP_Real
    lbo = (var ? SCIPvarGetLbLocal(var) : 0),
    ubo = (var ? SCIPvarGetUbLocal(var) : 0);

  if (var) {
    SCIP_Bool
      lb_infeasible, lb_tightened,
      ub_infeasible, ub_tightened;
    sa(SCIPinferVarUbCons(scip, var, ubn, NULL, 0, TRUE,
                          &lb_infeasible, &lb_tightened));
    sa(SCIPinferVarLbCons(scip, var, lbn, NULL, 0, TRUE,
                          &ub_infeasible, &ub_tightened));
    bound_changed |= lb_tightened;
    bound_changed |= ub_tightened;
    node_infeasible |= lb_infeasible;
    node_infeasible |= ub_infeasible;
  } else if (lbn < 0 || ubn > 0) {
    unreachable();
    node_infeasible = true;
  }
  return node_infeasible;

}

void cc_handler::scip_prop_impl_ranges()
{

  ffcall_map::const_iterator it = ffcall_m.begin();

  while (it != ffcall_m.end()) {

    const ffcall_slave_map& ffcs_m = it->second;
    ffcall_slave_map::const_iterator its = ffcs_m.begin();

    while (its != ffcs_m.end()) {

      const vector<SCIP_VAR*>& v = its->first;
      uint n = v.size();

      if (util::vector_all_eq<SCIP_VAR*>(v, NULL)) {
        its++;
        continue;
      }

      vector<SCIP_VAR*> v_nulls(n, NULL);
      ffcall_slave_map::const_iterator itc = ffcs_m.find(v_nulls);
      if(itc == ffcs_m.end()) {
        its++;
        continue;
      }

      const vector<ffc_offset>& vfo = its->second;
      BOOST_FOREACH (const ffc_offset& fo, vfo)
        if (scip_prop_impl_ranges(v, fo, itc->second)) return;

      its++;

    }

    it++;

  }

}

SCIP_RESULT cc_handler::scip_prop_impl(context& c)
{

  SCIP*& scip = scip::ObjEventhdlr::scip_;

  bound_changed = false;

#ifdef PROP_RANGES
  scip_prop_impl_ranges();

  if (node_infeasible) return SCIP_CUTOFF;

  if (!c.get_consistent()) return SCIP_CUTOFF;
#endif

  dvar_offset_map::iterator it = dvar_offset_m.begin();

  while (it != dvar_offset_m.end()) {
    SCIP_VAR* dv = it->first;
    SCIP_Real lb = SCIPvarGetLbLocal(dv),
      ub = SCIPvarGetUbLocal(dv);
    llint lb_again = my_llint(scip, lb);
    if (SCIPisEQ(scip, lb, ub) &&
        util::vector_exists_eq<llint>(it->second, lb_again)) {
      dvar_rev_map::iterator it = dvar_rev_m.find(dv);
      assert(it != dvar_rev_m.end());
      SCIP_VAR* v1 = it->second.first;
      SCIP_VAR* v2 = it->second.second;
      SCIP_Real
        lb1 = v1 ? SCIPvarGetLbLocal(v1) : 0,
        ub1 = v1 ? SCIPvarGetUbLocal(v1) : 0,
        lb2 = v2 ? SCIPvarGetLbLocal(v2) : 0,
        ub2 = v2 ? SCIPvarGetUbLocal(v2) : 0;
      // infinities shouldn't cause trouble
      assert(SCIPisLE(scip, lb1 - ub2, lb));
      assert(SCIPisLE(scip, ub, ub1 - lb2));
#ifdef DEBUG1
      cout << "[CB] prop-in " << var_id(it->second.first) << ", "
           << var_id(it->second.second) << ", "
           << lb
           << endl;
#endif
      c.merge(v1, v2, my_llint(scip, lb_again));
      if (node_infeasible) return SCIP_CUTOFF;
      if (!c.get_consistent()) return  SCIP_CUTOFF;
    }
    it++;
  }

  if (node_infeasible) return SCIP_CUTOFF;

  if (!c.get_consistent()) return SCIP_CUTOFF;

  if (bound_changed) return SCIP_REDUCEDDOM;

  if (ocaml_dp) return ocaml_dp->propagate();

  return SCIP_DIDNOTFIND;
  
}

SCIP_RESULT cc_handler::scip_prop_impl(bool stateless = true)
{

  if (node_infeasible || !ctx.get_consistent()) {
#ifdef DEBUG1
    cout << "[W!] prop called, although we are infeasible\n";
    if (node_infeasible)
      cout << "[W!] node_infeasible\n";
    if (!ctx.get_consistent())
      cout << "[W!] !ctx.get_consistent()\n";
    cout << "[W!] ... this is probably fine; double-check\n";
#endif
    // return SCIP_CUTOFF;
  }

  if (stateless) {
    context ctx_prop = context(ctx, cback.get());
    ctx_prop.push_frame();
    return scip_prop_impl(ctx_prop);
  } else {
    SCIP*& scip = scip::ObjEventhdlr::scip_;
    assert(SCIPgetStage(scip) != SCIP_STAGE_PRESOLVING);
    return scip_prop_impl(ctx);
  }

}

inline SCIP_RESULT scip_check_impl_return(SCIP_RESULT r) {

#ifdef DEBUG1
  switch (r) {
  case SCIP_INFEASIBLE:
    cout << "[CK] infeasible\n";
    break;
  case SCIP_FEASIBLE:
    cout << "[CK] feasible\n";
    break;
  }
#endif

  return r;

}

SCIP_RESULT cc_handler::scip_check_impl(SCIP_SOL* sol)
{

  SCIP*& scip = scip::ObjEventhdlr::scip_;
  fcall_lookup_map fcall_lookup_m;

#ifdef DEBUG2
  dbg_print_assignment(sol);
#endif

  BOOST_FOREACH (const fcall& fc, fcalls) {
    vector<llint> args;
    BOOST_FOREACH (const scip_ovar& ov, fc.get<2>()) {
      llint x = ov.base ?
        my_llint(scip, SCIPgetSolVal(scip, sol, ov.base)) :
        0;
      args.push_back(x + ov.offset);
    }
    SCIP_VAR* v = fc.get<1>().base;
    llint r = v ? my_llint(scip, SCIPgetSolVal(scip, sol,v)) : 0;
    r += fc.get<1>().offset;
#ifdef DEBUG1
    cout << "[CK] " << *fc.get<0>() << "(";
    BOOST_FOREACH (llint x, args) cout << x << ", ";
    cout << ") = " << r << endl;
#endif
    fcall_lookup_key k(fc.get<0>(), args);
    fcall_lookup_map::iterator it = fcall_lookup_m.find(k);
    if (it != fcall_lookup_m.end()) {
      if (r != it->second.first) {
        conflict_fcall1 = &fc;
        conflict_fcall2 = it->second.second;
        return scip_check_impl_return(SCIP_INFEASIBLE);
      }
    } else
      fcall_lookup_m.emplace(k, fcall_lookup_data(r, &fc));
  }

  if (ocaml_dp && !ocaml_dp->check(sol))
    return scip_check_impl_return(SCIP_INFEASIBLE);

  if (ocaml_cut_gen && sol && !ocaml_cut_gen->check(sol))
    return scip_check_impl_return(SCIP_INFEASIBLE);

  return scip_check_impl_return(SCIP_FEASIBLE);

}

SCIP_RETCODE cc_handler::scip_trans
(SCIP* s, SCIP_CONSHDLR* ch, SCIP_CONS* src, SCIP_CONS** tgt)
{
  
#ifdef DEBUG0
  cout << "[CB] trans\n";
#endif
  
  ASSERT_SCIP_POINTER(s);

  return SCIP_OKAY;

}

SCIP_RETCODE cc_handler::scip_lock
(SCIP* s, SCIP_CONSHDLR* ch, SCIP_CONS* c, int n_pos, int n_neg)
{

#ifdef DEBUG0
  cout << "[CB] lock\n";
#endif

  ASSERT_SCIP_POINTER(s);

  BOOST_FOREACH (SCIP_VAR* v, vars)
    if (v) SCIPaddVarLocks(s, v, n_pos + n_neg, n_pos + n_neg);

  BOOST_FOREACH (SCIP_VAR* v, catchq)
    if (v) SCIPaddVarLocks(s, v, n_pos + n_neg, n_pos + n_neg);

  BOOST_FOREACH (SCIP_VAR* v, dvars)
    SCIPaddVarLocks(s, v, n_pos + n_neg, n_pos + n_neg);

  return SCIP_OKAY;
  
}

bool cc_handler::branch_on_ocaml_diff()
{

  SCIP*& scip = scip::ObjEventhdlr::scip_;

  dvar_offset_map::iterator it = ocaml_dvar_offset_m.begin();

  while (it != ocaml_dvar_offset_m.end()) {

    SCIP_VAR* dv = it->first;

    SCIP_Real
      lb = SCIPvarGetLbLocal(dv),
      ub = SCIPvarGetUbLocal(dv);
    vector<llint> v = it->second;

    vector<llint>::const_iterator it2 = v.begin();

    while (it2 != v.end()) {
      const llint& o = *it2;
      if (branch_around_val(scip, dv, o)) return true;
      it2++;
    }

    it++;

  }

  return false;
  
}

SCIP_RESULT cc_handler::cut_or_branch(bool cc_feasible)
{

  SCIP*& scip = scip::ObjEventhdlr::scip_;

#ifdef DEBUG1
  cout << "[CB] enfolp: trying to cut or branch\n";
#endif

  if (ocaml_cut_gen) {
    SCIP_RESULT cg_result = ocaml_cut_gen->generate();
    switch (cg_result) {
    case SCIP_DIDNOTFIND:
      break;
    case SCIP_CUTOFF:
    case SCIP_SEPARATED:
    case SCIP_CONSADDED:
      return cg_result;
    case SCIP_FEASIBLE:
      if (cc_feasible) return cg_result;
      break;
    default:
      throw util::ec_case;
    }
  }

  /* trying to branch on something that makes sense for CC */

#ifdef BRANCH_CONFLICT
  if (branch_on_last_cc_conflict()) return SCIP_BRANCHED;

  assert(ocaml_dp || ocaml_cut_gen);
#endif

  if (branch_on_cc_diff()) return SCIP_BRANCHED;

  /* trying to branch on something that makes sense for ocaml_dp */

  if (ocaml_dp && ocaml_dp->branch()) return SCIP_BRANCHED;

  /* branch on behalf of theory solvers (on registered diffs) */

#ifdef DEBUG1
  dbg_print_assignment(NULL);
#endif

  if (branch_on_ocaml_diff()) return SCIP_BRANCHED;
  
  /* we are in trouble */

#ifdef DEBUG1
  dbg_print_assignment(NULL);
#endif

  unreachable();
  return SCIP_DIDNOTFIND;
  
}

SCIP_RETCODE cc_handler::scip_enfolp
(SCIP* s, SCIP_CONSHDLR* ch, SCIP_CONS** ac,
 int n, int n_useful, SCIP_Bool infeasible, SCIP_RESULT* r)
{

#ifdef DEBUG0
  cout << "[CB] enfolp" << endl;
#endif

#ifdef DEBUG2
  dbg_print_assignment(NULL);
#endif

  ASSERT_SCIP_POINTER(s);
  assert(SCIPgetStage(s) != SCIP_STAGE_PRESOLVING);

  assert(!node_infeasible);
  assert(ctx.get_consistent());

  if (scip_check_impl(NULL) == SCIP_FEASIBLE) {
    *r = ocaml_cut_gen ?
      cut_or_branch(true) :
      SCIP_FEASIBLE;
    return SCIP_OKAY;
  }
    
#ifdef DEBUG1
  cout << "[CB] enfolp: solution infeasible, trying to propagate\n";
#endif

  switch (scip_prop_impl(false)) {
  case SCIP_DIDNOTFIND: 
    break;
  case SCIP_REDUCEDDOM:
    *r = SCIP_REDUCEDDOM;
    return SCIP_OKAY;
  case SCIP_CUTOFF:
    *r = SCIP_CUTOFF;
    return SCIP_OKAY;
  default:
    throw util::ec_case;
  }

#ifdef DEBUG1
    cout << "[CB] ... failed to propagate\n";
#endif
  
  *r = cut_or_branch(false);
  assert(!node_infeasible);
  assert(ctx.get_consistent());
  assert(*r != SCIP_FEASIBLE);
  return SCIP_OKAY;
  
}

SCIP_RETCODE cc_handler::scip_enfops
(SCIP* s, SCIP_CONSHDLR* ch, SCIP_CONS** ac,
 int n, int n_useful, SCIP_Bool infeasible, SCIP_Bool obj_infeasible,
 SCIP_RESULT* result)
{

#ifdef DEBUG0
  cout << "[CB] enfops\n";
#endif

  unreachable();
  
  SCIP_RESULT r = scip_check_impl(NULL);

  *result = (r == SCIP_FEASIBLE) ? SCIP_FEASIBLE : SCIP_SOLVELP;
  
  return SCIP_OKAY;

}

SCIP_RETCODE cc_handler::scip_check
(SCIP* s, SCIP_CONSHDLR* ch, SCIP_CONS** ac,
 int n, SCIP_SOL* sol, SCIP_Bool ck_integral, SCIP_Bool ck_rows,
 SCIP_Bool print_reason, SCIP_RESULT* result)
{

#ifdef DEBUG0
  cout << "[CB] check\n";
#endif

  ASSERT_SCIP_POINTER(s);

  *result = scip_check_impl(sol);
  
  return SCIP_OKAY;

}

SCIP_RETCODE cc_handler::scip_prop
(SCIP* s, SCIP_CONSHDLR* ch, SCIP_CONS** ac,
 int n, int n_useful, int n_marked,
 SCIP_PROPTIMING pt, SCIP_RESULT* result)
{

#ifdef DEBUG0
  cout << "[CB] prop ... ";
  fflush(stdout);
#endif

  ASSERT_SCIP_POINTER(s);

  *result = scip_prop_impl(false);
  
#ifdef DEBUG1
  switch (*result) {
  case SCIP_DIDNOTFIND:
    cout << "no propagation\n";
    break;
  case SCIP_CUTOFF:
    cout << "cutoff\n";
    break;
  case SCIP_REDUCEDDOM:
    cout << "domain reduction\n";
    break;
  default:
    throw util::ec_case;
  }
#endif

  return SCIP_OKAY;

}

SCIP_RETCODE cc_handler::scip_presol
(SCIP* s, SCIP_CONSHDLR* conshdlr, SCIP_CONS** conss,
 int nconss, int nrounds, int nnewfixedvars, int nnewaggrvars,
 int nnewchgvartypes, int nnewchgbds, int nnewholes,
 int nnewdelconss, int nnewaddconss, int nnewupgdconss,
 int nnewchgcoefs, int nnewchgsides,
 int* nfixedvars, int* naggrvars, int* nchgvartypes,
 int* nchgbds, int* naddholes, int* ndelconss, int* naddconss,
 int* nupgdconss, int* nchgcoefs, int* nchgsides,
 SCIP_RESULT* result)
{

#ifdef DEBUG0
  cout << "[CB] presol\n";
#endif

  ASSERT_SCIP_POINTER(s);

  return SCIP_OKAY;

}

// rewind the stack till we find the target node
void cc_handler::rewind_to_frame_ocg(SCIP_NODE* node)
{
  while (true) {
    if (frames_ocg.empty()) return;
    if (node == frames_ocg.back()) return;
    pop_frame_ocg();
  }
}

void cc_handler::scip_exec_nodefocused_ocg(SCIP_NODE* en)
{

  assert(ocaml_cut_gen);

  SCIP_NODE* pn = SCIPnodeGetParent(en);
  SCIP_NODE* cn = current_node_ocg();

  if (pn == cn) {
    push_frame_ocg(en);
    return;
  }

#ifdef DEBUG1
  cout << "[OC] all the way to the top\n";
#endif

  rewind_to_frame_ocg(node_in_frames_ocg(pn) ? pn : NULL);
  push_frame_ocg(en);
  return;

}

SCIP_RETCODE cc_handler::scip_exec_nodefocused(SCIP_EVENT* e)
{

  SCIP*& scip = scip::ObjEventhdlr::scip_;
  SCIP_NODE* en = SCIPeventGetNode(e);
  SCIP_NODE* cn;
  SCIP_NODE* pn;

  assert(!seen_node || en);

  if (ocaml_cut_gen)
    scip_exec_nodefocused_ocg(en);

  if (frames.empty()) {
    assert(!seen_node);
    seen_node = true;
    push_frame(en);
    push_frame_ocg(en);
    return SCIP_OKAY;
  }

#ifdef DEBUG0
  cout << "[EV] node " << en << " focused ... ";
#endif

  cn = current_node();
  pn = SCIPnodeGetParent(en);
  assert(pn || SCIPgetRootNode(scip) == en);
  if (pn == cn) {
#ifdef DEBUG0
    cout << "we can go on with our stack\n";
    fflush(stdout);
#endif
    push_frame(en);
    return SCIP_OKAY;
  }

  if (node_in_frames(pn)) {
#ifdef DEBUG0
    cout << "halfway there\n";
    fflush(stdout);
#endif
    rewind_to_frame(pn);
    push_frame(en);
    return SCIP_OKAY;
  }

#ifdef DEBUG0
  cout << "all the way to the top\n";
  fflush(stdout);
#endif

  rewind_to_frame((SCIP_NODE*)NULL);
  push_frame(en);

  return SCIP_OKAY;

}

SCIP_RETCODE cc_handler::scip_exec_relaxed
(SCIP_VAR* ev,
 SCIP_Real old_lb,
 SCIP_Real new_lb,
 SCIP_Real old_ub,
 SCIP_Real new_ub)
{

  assert (new_lb <= new_ub);

  SCIP*& scip = scip::ObjEventhdlr::scip_;
  SCIP_NODE* cn = current_node();

#ifdef DEBUG1
  cout << "[EV] bound for " << var_id(ev) << " relaxed from ["
       << old_lb << ", " << old_ub << "] to ["
       << new_lb << ", " << new_ub << "]\n";
  fflush(stdout);
#endif

  // tried to be smarter in the past, leading to wrong answers. We
  // cannot dependably whether our state 

  rewind_to_frame_ocg(NULL);
  push_frame_ocg(cn);
  rewind_to_frame((SCIP_NODE*)NULL);
  push_frame(cn);
  return SCIP_OKAY;

}

SCIP_RETCODE cc_handler::scip_exec_lbrelaxed(SCIP_EVENT* e)
{

  SCIP_VAR* ev = orig_var(SCIPeventGetVar(e));
  SCIP_Real old_lb = SCIPeventGetOldbound(e);
  SCIP_Real new_lb = SCIPeventGetNewbound(e);
  SCIP_Real ub = SCIPvarGetUbLocal(ev);

  return scip_exec_relaxed(ev, old_lb, new_lb, ub, ub);

}

SCIP_RETCODE cc_handler::scip_exec_ubrelaxed(SCIP_EVENT* e)
{
  
  SCIP_VAR* ev = orig_var(SCIPeventGetVar(e));
  SCIP_Real old_ub = SCIPeventGetOldbound(e);
  SCIP_Real new_ub = SCIPeventGetNewbound(e);
  SCIP_Real lb = SCIPvarGetLbLocal(ev);

  return scip_exec_relaxed(ev, lb, lb, old_ub, new_ub);
  
}

SCIP_RETCODE cc_handler::scip_exec
(SCIP* s, SCIP_EVENTHDLR* eh, SCIP_EVENT* e, SCIP_EVENTDATA* ed)
{

  ASSERT_SCIP_POINTER(s);

  switch (SCIPeventGetType(e)) {
  case SCIP_EVENTTYPE_NODEFOCUSED:
    return scip_exec_nodefocused(e);
  case SCIP_EVENTTYPE_VARDELETED:
    unreachable();
  case SCIP_EVENTTYPE_LBRELAXED:
    return scip_exec_lbrelaxed(e);
  case SCIP_EVENTTYPE_UBRELAXED:
    return scip_exec_ubrelaxed(e);
#ifdef DEBUG2
  case SCIP_EVENTTYPE_ROWADDEDLP:
    cout << "[EV] row added\n";
    fflush(stdout);
  case SCIP_EVENTTYPE_ROWDELETEDLP:
    cout << "[EV] row deleted\n";
    fflush(stdout);
#endif
  }
  
  return SCIP_OKAY;

}

SCIP_RETCODE cc_handler::scip_init(SCIP* s, SCIP_EVENTHDLR* eh)
{

#ifdef DEBUG0
  cout << "[CB] init\n";
#endif

  ASSERT_SCIP_POINTER(s);

#ifdef DEBUG2
  sa(SCIPcatchEvent(s, SCIP_EVENTTYPE_ROWADDEDLP, eh, NULL, NULL));
  sa(SCIPcatchEvent(s, SCIP_EVENTTYPE_ROWDELETEDLP, eh, NULL, NULL));
#endif
  
  sa(SCIPcatchEvent(s, SCIP_EVENTTYPE_NODEFOCUSED, eh, NULL, NULL));

  BOOST_FOREACH (SCIP_VAR* v, vars)
    if(v) catch_variable(v, false);

  BOOST_FOREACH (SCIP_VAR* dv, dvars)
    catch_variable(dv, true); 

  BOOST_FOREACH (SCIP_VAR* v, catchq)
    if (v) catch_var_events_impl(v); 

  return SCIP_OKAY;

}

void cc_handler::register_var(SCIP_VAR* v)
{
  
  BOOST_FOREACH (SCIP_VAR* v2, vars)
    if (v == v2)
      return;

  vars.push_back(v);

}

void cc_handler::register_ret
(const string* s,
 const vector<scip_ovar>& vv,
 const scip_ovar& ov)
{

  // TODO: avoid constructing a temporary ffcall_slave_map (can't
  // figure out how to forward 0 arguments)
  const pair<ffcall_map::iterator, bool> p =
    ffcall_m.emplace(s, ffcall_slave_map());
  const ffcall_map::iterator& it = p.first;
  assert(it != ffcall_m.end());
  ffcall_slave_map& ffcs_m = it->second;

  vector<SCIP_VAR*> key;
  vector<llint> offsets;

  BOOST_FOREACH (const scip_ovar& ov2, vv) {
    key.push_back(ov2.base);
    offsets.push_back(ov2.offset);
  }

  ffc_offset fo(offsets, ov);

  const pair<ffcall_slave_map::iterator, bool> ps =
    ffcs_m.emplace(key, vector<ffc_offset>(1, fo));

  if (!ps.second) {
    vector<ffc_offset>& v = ps.first->second;
    if (!util::vector_exists_eq<ffc_offset>(v, fo))
      v.push_back(fo);
  }

}

void cc_handler::register_arg(const string* s,
                              uint n,
                              const scip_ovar& ov)
{

  loc al(s, n);
  loc_map::iterator it = loc_m.find(al);

  register_var(ov.base);

  if (it != loc_m.end()) {
    vector<scip_ovar>& v = it->second;
    if (!util::vector_exists_eq<scip_ovar>(v, ov)) v.push_back(ov);
  } else
    loc_m.emplace(al, vector<scip_ovar>(1, ov));

}

void cc_handler::call(const scip_ovar& r, const string& s,
                      const vector<scip_ovar>& v)
{

  uint i = 0;
  uf_call_cnt++;

#ifdef DEBUG1
  cout << "[CALL] " << var_id(r.base)
       << (r.offset >= 0 ? '+' : '-')
       << (r.offset >= 0 ? r.offset : -r.offset)
       << " = " << s << '(';

  vector<scip_ovar>::const_iterator it = v.begin();

  while (true) {
    cout << (it->base ? var_id(it->base) : "0")
         << (it->offset >= 0 ? '+' : '-')
         << (it->offset >= 0 ? it->offset : -it->offset);
    if (++it != v.end())
      cout << ", ";
    else
      break;
  }

  cout << ')' << endl;
#endif

  const string* sptr = NULL;
  fun_symbol_map::iterator it_m = fun_symbol_m.find(s);
  if (it_m != fun_symbol_m.end())
    sptr = it_m->second;
  else {
    sptr = new string(s);
    fun_symbol_m.emplace(s, sptr);
  }

  vector<util::with_offset<symbol> > v_prime;
  BOOST_FOREACH (const scip_ovar& ov, v) {
    register_arg(sptr, i++, ov);
    v_prime.push_back(ov);
  }
  register_ret(sptr, v, r);
  register_var(r.base);

  fcalls.push_back(fcall(sptr, r, v));

  ctx.call(r, sptr, v_prime);

}

void cc_handler::add_rval_dvars(ffcall_slave_map::const_iterator it1,
                                ffcall_slave_map::const_iterator it2)
{

  const vector<SCIP_VAR*>& vv1 = it1->first;
  const vector<ffc_offset>& vffco1 = it1->second;
  const vector<SCIP_VAR*>& vv2 = it2->first;
  const vector<ffc_offset>& vffco2 = it2->second;
  assert(vv1.size() == vv2.size());

  BOOST_FOREACH (const ffc_offset& fo1, vffco1) {

    const vector<llint>& vo1 = fo1.first;
    const scip_ovar& ov1 = fo1.second;
    SCIP_VAR* const& v1 = fo1.second.base;
    assert(vo1.size() == vv1.size());

    BOOST_FOREACH (const ffc_offset& fo2, vffco2) {

      const vector<llint>& vo2 = fo2.first;
      const scip_ovar& ov2 = fo2.second;
      SCIP_VAR* const& v2 = fo2.second.base;
      assert(vo2.size() == vv2.size());

      bool irrelevant = false;
      vector<SCIP_VAR*>::const_iterator
        it_v1 = vv1.begin(), it_v2 = vv2.begin();
      vector<llint>::const_iterator
        it_o1 = vo1.begin(), it_o2 = vo2.begin();
      while (it_v1 < vv1.end()) {
        if (*it_v1 == *it_v2 && *it_o1 != *it_o2) {
          irrelevant = true;
          break;
        }
        it_v1++;
        it_v2++;
        it_o1++;
        it_o2++;
      }

      if (!irrelevant)
        if (v1 > v2)
          add_dvar(v1, v2);
        else
          add_dvar(v2, v1);

    }

  }

}

void cc_handler::finalize()
{
  
  loc_map::iterator it = loc_m.begin();
  
  while (it != loc_m.end()) {
    vector<scip_ovar>& v = it->second;
    vector<scip_ovar>::const_iterator it1 = v.begin();
    while (it1 != v.end()) {
      const scip_ovar& ov1 = *it1;
      SCIP_VAR* v1 = ov1.base;
      vector<scip_ovar>::const_iterator it2 = it1 + 1;
      while (it2 != v.end()) {
        const scip_ovar& ov2 = *it2;
        SCIP_VAR* v2 = ov2.base;
        if (v1 > v2)
          add_dvar(ov1, ov2);
        if (v2 > v1)
          add_dvar(ov2, ov1);
        it2++;
      }
      it1++;
    }
    it++;
  }

  ffcall_map::iterator it_r = ffcall_m.begin();
  
  while (it_r != ffcall_m.end()) {

    ffcall_slave_map& ffcs_m = it_r->second;

    ffcall_slave_map::iterator it0 = ffcs_m.begin();
    while (it0 != ffcs_m.end()) {
      sort(it0->second.begin(), it0->second.end(),
           compare_ffc_offset());
      it0++;
    }

    ffcall_slave_map::const_iterator it1 = ffcs_m.begin();

    while (it1 != ffcs_m.end()) {
      ffcall_slave_map::const_iterator it2(it1);
      it2++;
      while (it2 != ffcs_m.end()) {
        add_rval_dvars(it1, it2);
        it2++;
      }
      it1++;
    }

    it_r++;

  }

#ifdef DEBUG0
  fflush(stdout);
#endif

}

void cc_handler::include()
{
  SCIP*& scip = scip::ObjEventhdlr::scip_;
  sa(SCIPincludeObjConshdlr(scip, this, false));
  sa(SCIPincludeObjEventhdlr(scip, this, false));
}

// FIXME: can it be merged with catch_variable?
void cc_handler::catch_var_events_impl(SCIP_VAR* v)
{

  SCIP*& scip = scip::ObjEventhdlr::scip_;

  SCIP_EVENTHDLR* eh = SCIPfindEventhdlr(scip, "cce");
  SCIP_VAR* v_trans;

  assert(eh);

  sa(SCIPcaptureVar(scip, v));

  // SCIPcatchVarEvent expects a transformed variable; create one
  sa(SCIPtransformVar(scip, v, &v_trans));
  sa(SCIPcaptureVar(scip, v_trans));

  orig_var_m.emplace(v_trans, v);
  
  sa(SCIPcatchVarEvent
     (scip, v_trans, SCIP_EVENTTYPE_LBRELAXED, eh,
      NULL, NULL));
  sa(SCIPcatchVarEvent
     (scip, v_trans, SCIP_EVENTTYPE_UBRELAXED, eh,
      NULL, NULL));
  sa(SCIPcatchVarEvent
     (scip, v_trans, SCIP_EVENTTYPE_VARDELETED, eh,
      NULL, NULL));

}

void cc_handler::catch_var_events(SCIP_VAR* v)
{
  catchq.push_back(v);
}

/* C wrappers */

cc_handler* new_cc_handler(SCIP* s, dp* d, cut_gen* c)
{
  return new cc_handler(s, d, c);
}

void delete_cc_handler(cc_handler* c)
{
  delete c;
}

void cc_handler_call(cc_handler* c,
                     SCIP_VAR* rv, llint roffset, char* id,
                     uint nvars, SCIP_VAR** vars, llint* coefs)
{

  scip_ovar ov(rv, roffset);
  vector<scip_ovar> ovv;

  for (uint i = 0; i < nvars; i++)
    ovv.push_back(scip_ovar(vars[i], coefs[i]));

  c->call(ov, id, ovv);

}

void cc_handler_finalize(cc_handler* c)
{
  c->finalize();
}

void cc_handler_include(cc_handler* c)
{
  c->include();
}

void cc_handler_catch_var_events(cc_handler* c, SCIP_VAR* v)
{
  c->catch_var_events(v);
}

SCIP_VAR* cc_handler_zero_var(cc_handler* c)
{
  return NULL;
}

SCIP_VAR* cc_handler_add_dvar(cc_handler* c,
                              SCIP_VAR* v1,
                              SCIP_VAR* v2,
                              llint o,
                              bool reg)
{
  return c->ocaml_add_dvar(v1, v2, o, reg);
}

uintptr_t uintptr_t_of_var(SCIP_VAR* v)
{
  return uintptr_t(v);
}

uintptr_t uintptr_t_of_node(SCIP_NODE* n)
{
  return uintptr_t(n);
}
