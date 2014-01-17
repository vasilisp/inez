#ifndef SCIP_UTILS_HPP_
#define SCIP_UTILS_HPP_

#include "util.hpp"

#include "scip/scip.h"
#include "scip/scipdefplugins.h"

// sa for *s*cip *a*ssert
inline void sa(SCIP_RETCODE r)
{
  // help GCC with branch prediction info
  if (__builtin_expect(r != SCIP_OKAY, 0)) {
    cerr << "SCIP error code: " << r << endl;
    throw util::ec_backend;
  }
}

inline llint my_llint(SCIP* scip, SCIP_Real r)
{
  llint rval = SCIPround(scip, r);
  assert(SCIPisEQ(scip, rval, r) ||
         SCIPisEQ(scip, r, SCIPinfinity(scip)) ||
         SCIPisEQ(scip, r, -SCIPinfinity(scip)));
  return rval;
}

SCIP_VAR* scip_dvar(SCIP*, SCIP_VAR*, SCIP_VAR*);

bool scip_fix_variable(SCIP*, SCIP_VAR*, llint, bool*);

void scip_fix_diff(SCIP*, SCIP_CONSHDLR*, SCIP_VAR*, SCIP_VAR*, llint);

void scip_branch_around_val(SCIP*, SCIP_VAR*, llint);

void scip_include_default_plugins(SCIP*);

#endif
