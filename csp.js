!function() {

var CSP = {},
    FAILURE = 'FAILURE',
    stepCounter = 0;

// ---------------- Public API ----------------

CSP.solve = function solve(csp) {
  // Normalize and validate
  csp = normalizeProblem(csp);
  validateProblem(csp);

  // Precompute n-ary adjacency index for GAC queueing
  csp._naryIndex = buildNaryIndex(csp.naryConstraints);

  // Backtrack with consistency
  const result = backtrack({}, cloneVars(csp.variables), csp);
  if (result === FAILURE) return result;

  // Unwrap singleton arrays to raw values
  for (var key in result) {
    const v = result[key];
    result[key] = Array.isArray(v) ? v[0] : v;
  }
  return result;
};

// ---------------- Core search ----------------

function backtrack(_assigned, unassigned, csp) {
  const assigned = cloneAssignment(_assigned);

  if (finished(unassigned)) return assigned;

  const nextKey = selectUnassignedVariable(unassigned);
  if (nextKey == null) return FAILURE;

  const values = orderValues(nextKey, assigned, unassigned, csp);
  // Remove nextKey domain from unassigned for this depth
  const savedDom = unassigned[nextKey];
  delete unassigned[nextKey];

  for (let i = 0; i < values.length; i++) {
    stepCounter++;
    assigned[nextKey] = [values[i]];

    const consistent = enforceConsistency(assigned, unassigned, csp);
    if (consistent === FAILURE) {
      // rollback assignment and continue
      delete assigned[nextKey];
      continue;
    }

    // Split consistent into newAssigned/newUnassigned
    const newAssigned = {};
    const newUnassigned = {};
    for (const key in consistent) {
      if (assigned[key]) newAssigned[key] = consistent[key].slice();
      else newUnassigned[key] = consistent[key].slice();
    }

    // Callback (optional)
    if (csp.cb) {
      setTimeout(((A, U) => () => csp.cb(A, U, csp))(newAssigned, newUnassigned), stepCounter * csp.timeStep);
    }

    if (anyEmpty(consistent)) {
      delete assigned[nextKey];
      continue;
    }

    const result = backtrack(newAssigned, newUnassigned, csp);
    if (result !== FAILURE) return result;

    delete assigned[nextKey];
  }

  // restore (defensive – though caller discards this frame’s unassigned anyway)
  unassigned[nextKey] = savedDom;
  return FAILURE;
}

// ---------------- Helpers: cloning and checks ----------------

function cloneVars(variables) {
  const out = {};
  for (const k in variables) out[k] = variables[k].slice();
  return out;
}
function cloneAssignment(assigned) {
  const out = {};
  for (const k in assigned) out[k] = assigned[k].slice();
  return out;
}
function finished(unassigned) {
  return Object.keys(unassigned).length === 0;
}
function anyEmpty(vars) {
  for (const k in vars) if (!vars[k] || vars[k].length === 0) return true;
  return false;
}
function partialAssignment(assigned, unassigned) {
  const partial = {};
  for (const key in unassigned) partial[key] = unassigned[key].slice();
  for (const key in assigned) partial[key] = assigned[key].slice();
  return partial;
}

// ---------------- Consistency: AC-3 + GAC ----------------

function enforceConsistency(assigned, unassigned, csp) {
  const variables = partialAssignment(assigned, unassigned);

  // Binary AC-3 (if any)
  if (csp.constraints.length) {
    const ok = runAC3(variables, csp.constraints);
    if (!ok) return FAILURE;
  }

  // N-ary GAC (if any)
  if (csp.naryConstraints.length) {
    const ok = runGAC(variables, csp);
    if (!ok) return FAILURE;
  }

  return variables;
}

// AC-3 for binary constraints represented as [head, tail, predicate(headVal, tailVal)]
function runAC3(variables, constraints) {
  function incomingConstraints(node) {
    return constraints.filter(c => c[0] === node);
  }
  function removeInconsistentValues(head, tail, predicate, vars) {
    const hv = vars[head], tv = vars[tail];
    if (!hv || !tv) return false;
    const validTailValues = tv.filter(t => hv.some(h => predicate(h, t)));
    const removed = validTailValues.length !== tv.length;
    vars[tail] = validTailValues;
    return removed;
  }

  let queue = constraints.slice();
  while (queue.length) {
    const [head, tail, predicate] = queue.shift();
    if (!variables[head] || !variables[tail]) continue;
    if (removeInconsistentValues(head, tail, predicate, variables)) {
      if (!variables[tail] || variables[tail].length === 0) return false;
      queue = queue.concat(incomingConstraints(tail));
    }
  }
  return true;
}

// Build var -> list of n-ary constraints
function buildNaryIndex(naryConstraints) {
  const index = {};
  for (let i = 0; i < naryConstraints.length; i++) {
    const C = naryConstraints[i];
    if (!C || !Array.isArray(C.vars)) continue;
    for (let j = 0; j < C.vars.length; j++) {
      const v = C.vars[j];
      (index[v] = index[v] || []).push(C);
    }
  }
  return index;
}

// Robust GAC driver
function runGAC(variables, csp) {
  // Start with all n-ary constraints in the queue
  const queue = csp.naryConstraints.slice();

  // For quick related-constraint lookup
  const index = csp._naryIndex || buildNaryIndex(csp.naryConstraints);

  while (queue.length) {
    const C = queue.shift();
    if (!C || !Array.isArray(C.vars) || typeof C.predicate !== 'function') continue;

    let changedAny = false;

    for (let vi = 0; vi < C.vars.length; vi++) {
      const varName = C.vars[vi];
      const dom = variables[varName];
      if (!Array.isArray(dom)) continue; // variable may not be in current scope

      const newDom = [];
      for (let di = 0; di < dom.length; di++) {
        const val = dom[di];
        if (hasSupport(varName, val, C, variables)) newDom.push(val);
      }
      if (newDom.length !== dom.length) {
        variables[varName] = newDom;
        if (newDom.length === 0) return false;
        changedAny = true;
      }
    }

    if (changedAny) {
      // Re-enqueue all constraints related to any var in C
      for (let vi2 = 0; vi2 < C.vars.length; vi2++) {
        const v2 = C.vars[vi2];
        const related = index[v2] || [];
        for (let r = 0; r < related.length; r++) {
          const Rc = related[r];
          if (queue.indexOf(Rc) === -1) queue.push(Rc);
        }
      }
    }
  }
  return true;
}

// Robust hasSupport: checks if focusVar=focusVal can be extended to satisfy C.predicate
function hasSupport(focusVar, focusVal, C, variables) {
  // Prepare the list of other variables that have defined, non-empty domains
  const others = [];
  for (let i = 0; i < C.vars.length; i++) {
    const v = C.vars[i];
    if (v === focusVar) continue;
    const dom = variables[v];
    if (!Array.isArray(dom)) return false;      // missing variable => no support
    if (dom.length === 0) return false;         // empty domain => no support
    others.push(v);
  }

  // Sort by domain size, but guard against undefined
  others.sort((a, b) => {
    const da = variables[a] ? variables[a].length : Infinity;
    const db = variables[b] ? variables[b].length : Infinity;
    return da - db;
  });

  // DFS over cartesian product of others' domains
  const order = [focusVar].concat(others);
  const domains = [ [focusVal] ].concat(others.map(v => variables[v]));

  const assign = {};
  function dfs(i) {
    if (i === order.length) {
      try {
        return !!C.predicate(assign);
      } catch (e) {
        return false;
      }
    }
    const vname = order[i];
    const dom = domains[i] || [];
    for (let k = 0; k < dom.length; k++) {
      assign[vname] = dom[k];
      if (dfs(i + 1)) return true;
    }
    delete assign[vname];
    return false;
  }
  return dfs(0);
}

// ---------------- Heuristics ----------------

function selectUnassignedVariable(unassigned) {
  let minKey = null, minLen = Infinity;
  for (const key in unassigned) {
    const dom = unassigned[key];
    const len = Array.isArray(dom) ? dom.length : Infinity;
    if (len < minLen) {
      minKey = key; minLen = len;
      if (len === 1) break;
    }
  }
  return minKey;
}

function orderValues(nextKey, assigned, unassigned, csp) {
  const baseValues = (unassigned[nextKey] || []).slice();
  if (baseValues.length <= 1) return baseValues;

  // Count total domain sizes after enforcing consistency with tentative assignment
  function countValues(vars) {
    let sum = 0;
    for (const k in vars) {
      const d = vars[k];
      sum += Array.isArray(d) ? d.length : 0;
    }
    return sum;
  }

  const score = Object.create(null);

  for (let i = 0; i < baseValues.length; i++) {
    const val = baseValues[i];

    // Build fresh copies to avoid mutating parent state
    const A = cloneAssignment(assigned);
    const U = cloneVars(unassigned);

    // Tentatively assign nextKey
    A[nextKey] = [val];
    delete U[nextKey];

    const res = enforceConsistency(A, U, csp);
    if (res === FAILURE || anyEmpty(res)) {
      score[val] = -Infinity; // worst score (eliminated)
    } else {
      score[val] = countValues(res); // larger remaining search => try later
    }
  }

  // Sort descending by score (fail-most-first), tie-break by value stable
  baseValues.sort((a, b) => (score[b] - score[a]));
  return baseValues;
}

// ---------------- Validation and normalization ----------------

function normalizeProblem(csp) {
  const out = {
    variables: {},
    constraints: [],
    naryConstraints: [],
    timeStep: csp.timeStep || 1,
    cb: csp.cb
  };
  // Clone variables defensively and ensure arrays
  for (const k in csp.variables || {}) {
    const dom = csp.variables[k];
    out.variables[k] = Array.isArray(dom) ? dom.slice() : [];
  }
  // Binary constraints: expect [head, tail, predicate]
  if (Array.isArray(csp.constraints)) {
    out.constraints = csp.constraints.slice().filter(c =>
      Array.isArray(c) && c.length >= 3 && typeof c[2] === 'function'
    );
  }
  // N-ary constraints: expect { vars: [...], predicate: fn }
  if (Array.isArray(csp.naryConstraints)) {
    out.naryConstraints = csp.naryConstraints.slice().filter(C =>
      C && Array.isArray(C.vars) && typeof C.predicate === 'function'
    );
  }
  return out;
}

function validateProblem(csp) {
  const varsSet = new Set(Object.keys(csp.variables));

  // Ensure all domains are arrays and non-empty
  for (const v in csp.variables) {
    if (!Array.isArray(csp.variables[v])) {
      throw new Error('Variable "' + v + '" domain is not an array');
    }
  }

  // Validate binary constraints
  for (let i = 0; i < csp.constraints.length; i++) {
    const c = csp.constraints[i];
    const head = c[0], tail = c[1], pred = c[2];
    if (!varsSet.has(head)) throw new Error('Binary constraint references unknown variable "' + head + '"');
    if (!varsSet.has(tail)) throw new Error('Binary constraint references unknown variable "' + tail + '"');
    if (typeof pred !== 'function') throw new Error('Binary constraint missing predicate function');
  }

  // Validate n-ary constraints
  for (let i = 0; i < csp.naryConstraints.length; i++) {
    const C = csp.naryConstraints[i];
    if (!Array.isArray(C.vars) || C.vars.length === 0) {
      throw new Error('N-ary constraint missing vars array');
    }
    for (let j = 0; j < C.vars.length; j++) {
      const v = C.vars[j];
      if (!varsSet.has(v)) {
        throw new Error('N-ary constraint references unknown variable "' + v + '"');
      }
    }
    if (typeof C.predicate !== 'function') {
      throw new Error('N-ary constraint missing predicate function');
    }
  }
}

// ---------------- UMD export ----------------

if (typeof define === 'function' && define.amd) {
  define(CSP);
} else if (typeof module === 'object' && module.exports) {
  module.exports = CSP;
} else {
  this.csp = CSP;
}

}();
