#include "scip_utils.hpp"

#include "scip/debug.h"

// #define DEBUG

// FIXME: copy-pasted function
inline const char* var_id(SCIP_VAR *v) {
  if (v) return SCIPvarGetName(v);
  return NULL;
}

SCIP_VAR* scip_dvar(SCIP* scip, SCIP_VAR* a, SCIP_VAR* b)
{

  assert(a != b);
  
  static unsigned int n = 0;
  SCIP_CONS* cons;
  SCIP_VAR* rval;
  char cons_id[64], rval_id[64];
  SCIP_VAR* vars[3] = {b, a, NULL};
  SCIP_Real coefs[3] = {1, -1, 1};
  SCIP_Real oo = SCIPinfinity(scip);

  sprintf(rval_id, "dvar%d", n);
  sprintf(cons_id, "deq%d", n++);
  sa(SCIPcreateVarBasic(scip, &rval, rval_id, -oo, oo, 0,
                        SCIP_VARTYPE_INTEGER));
  sa(SCIPaddVar(scip, rval));
  vars[2] = rval;
  sa(SCIPcreateConsLinear 
     (scip, &cons, cons_id, 3, vars, coefs, 0, 0,
      TRUE, TRUE, TRUE, TRUE, TRUE,
      FALSE, FALSE, FALSE, FALSE, FALSE));
  sa(SCIPaddCons(scip, cons));

  return rval;

}

bool scip_fix_variable
(SCIP* scip, SCIP_VAR* v, llint x, bool* infeasible)
{

  SCIP_Bool
    lb_infeasible, lb_tightened,
    ub_infeasible, ub_tightened;

  if (SCIPisEQ(scip, x, SCIPvarGetLbLocal(v)) &&
      SCIPisEQ(scip, x, SCIPvarGetUbLocal(v))) {
    *infeasible = false;
    return false;
  }

  sa(SCIPinferVarUbCons(scip, v, x, NULL, 0, TRUE,
                        &lb_infeasible, &lb_tightened));
  sa(SCIPinferVarLbCons(scip, v, x, NULL, 0, TRUE,
                        &ub_infeasible, &ub_tightened));

  *infeasible = *infeasible || lb_infeasible || ub_infeasible;
  return (lb_tightened || ub_tightened);

}

void scip_branch_around_val(SCIP* scip, SCIP_VAR* v, llint x)
{

#ifdef DEBUG
  cout << "[SU] branching around "
       << x << " for " << var_id(v)
       << endl;
#endif

  fflush(stdout);

  SCIP_NODE* left;
  SCIP_NODE* middle;
  SCIP_NODE* right;
  
  assert(SCIPvarGetLbLocal(v) <= x);
  assert(x <= SCIPvarGetUbLocal(v));
  sa(SCIPbranchVarVal(scip, v, x, &left, &middle, &right));

#ifdef DEBUG
  cout << "created children "
       << left << " < " << middle << " < " << right << endl;
#endif

}
