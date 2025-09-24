!function() {

var CSP = {},
    FAILURE = 'FAILURE',
    stepCounter = 0;

CSP.solve = function solve(csp) {
  csp.timeStep = csp.timeStep || 1;
  csp.naryConstraints = csp.naryConstraints || [];
  // Precompute index from var -> n-ary constraints containing it (for GAC queueing)
  csp._naryIndex = buildNaryIndex(csp.naryConstraints);
  var result = backtrack({}, csp.variables, csp);
  if (result == FAILURE) { return result; }
  for (var key in result) { result[key] = result[key][0]; }
  return result;
};

function backtrack(_assigned, unassigned, csp) {
  var assigned = {};
  for (var key in _assigned) { assigned[key] = _assigned[key]; }

  if (finished(unassigned)) { return assigned; }
  var nextKey = selectUnassignedVariable(unassigned),
      values = orderValues(nextKey, assigned, unassigned, csp);
  delete unassigned[nextKey];

  for (var i = 0; i < values.length; i++) {
    stepCounter++;
    assigned[nextKey] = [values[i]];
    var consistent = enforceConsistency(assigned, unassigned, csp);
    var newUnassigned = {}, newAssigned = {};
    for (var key in consistent) {
      if (assigned[key]) { newAssigned[key] = assigned[key].slice(); }
      else { newUnassigned[key] = consistent[key].slice(); }
    }
    if (csp.cb) {
      setTimeout(
        (function (newAssigned, newUnassigned) {
          return function () { csp.cb(newAssigned, newUnassigned, csp); };
        })(newAssigned, newUnassigned),
        stepCounter * csp.timeStep
      );
    }
    if (anyEmpty(consistent)) { continue; }
    var result = backtrack(newAssigned, newUnassigned, csp);
    if (result != FAILURE) { return result; }
  }

  return FAILURE;
}

function finished(unassigned) {
  return Object.keys(unassigned).length == 0;
}

function anyEmpty(vars) {
  for (var key in vars) {
    if (vars[key].length == 0) { return true; }
  }
  return false;
}

function partialAssignment(assigned, unassigned) {
  var partial = {};
  for (var key in unassigned) { partial[key] = unassigned[key].slice(); }
  for (var key in assigned) { partial[key] = assigned[key].slice(); }
  return partial;
}

function enforceConsistency(assigned, unassigned, csp) {
  // Binary AC-3
  function removeInconsistentValues(head, tail, constraint, variables) {
    var hv = variables[head], tv = variables[tail];
    var validTailValues = tv.filter(function (t) {
      return hv.some(function (h) { return constraint(h, t); });
    });
    var removed = tv.length != validTailValues.length;
    variables[tail] = validTailValues;
    return removed;
  }
  function incomingConstraints(node) {
    return csp.constraints.filter(function (c) { return c[0] == node; });
  }

  var variables = partialAssignment(assigned, unassigned);

  // Run binary arc consistency first
  var queue = csp.constraints.slice();
  while (queue.length) {
    var c = queue.shift(), head = c[0], tail = c[1], constraint = c[2];
    if (removeInconsistentValues(head, tail, constraint, variables)) {
      queue = queue.concat(incomingConstraints(tail));
    }
  }

  // Then run n-ary GAC
  if (csp.naryConstraints && csp.naryConstraints.length) {
    enforceGAC(variables, csp);
  }

  return variables;
}

// ---------- N-ary constraints (GAC) ----------

function buildNaryIndex(naryConstraints) {
  var index = {};
  for (var i = 0; i < naryConstraints.length; i++) {
    var C = naryConstraints[i];
    for (var j = 0; j < C.vars.length; j++) {
      var v = C.vars[j];
      (index[v] = index[v] || []).push(C);
    }
  }
  return index;
}

function enforceGAC(variables, csp) {
  var queue = csp.naryConstraints.slice();

  while (queue.length) {
    var C = queue.shift();
    var changedAny = false;

    for (var vi = 0; vi < C.vars.length; vi++) {
      var varName = C.vars[vi];
      var dom = variables[varName];
      // If a variable is currently unrepresented (shouldn't happen), skip
      if (!dom) continue;

      // Try to prune unsupported values
      var newDom = [];
      for (var di = 0; di < dom.length; di++) {
        var val = dom[di];
        if (hasSupport(varName, val, C, variables)) {
          newDom.push(val);
        }
      }
      if (newDom.length !== dom.length) {
        variables[varName] = newDom;
        changedAny = true;
      }
      if (newDom.length === 0) {
        // Early exit possible; but keep consistent with AC loop which lets caller detect empties
      }
    }

    if (changedAny) {
      // Re-enqueue all n-ary constraints that mention any variable that changed.
      // For simplicity, we conservatively re-enqueue all constraints that share any var in C.
      for (var vi2 = 0; vi2 < C.vars.length; vi2++) {
        var v2 = C.vars[vi2];
        var related = csp._naryIndex[v2] || [];
        for (var r = 0; r < related.length; r++) {
          var Rc = related[r];
          // Avoid adding duplicates too often; simple check
          if (queue.indexOf(Rc) === -1) { queue.push(Rc); }
        }
      }
    }
  }
}

function hasSupport(focusVar, focusVal, C, variables) {
  // Search for any assignment to the other vars in C that makes predicate true
  var others = [];
  for (var i = 0; i < C.vars.length; i++) {
    var v = C.vars[i];
    if (v !== focusVar) { others.push(v); }
  }
  // Sort by domain size (fail first)
  others.sort(function(a, b) { return variables[a].length - variables[b].length; });

  function dfs(idx, partial) {
    if (idx === others.length) {
      var tuple = {};
      for (var k in partial) { tuple[k] = partial[k]; }
      tuple[focusVar] = focusVal;
      return C.predicate(tuple);
    }
    var v = others[idx];
    var dom = variables[v];
    for (var i = 0; i < dom.length; i++) {
      partial[v] = dom[i];
      if (dfs(idx + 1, partial)) { return true; }
    }
    return false;
  }

  return dfs(0, {});
}

// ---------- Heuristics ----------

function selectUnassignedVariable(unassigned) {
  var minKey = null, minLen = Number.POSITIVE_INFINITY;
  for (var key in unassigned) {
    var len = unassigned[key].length;
    if (len < minLen) { minKey = key, minLen = len; }
  }
  return minKey;
}

function orderValues(nextKey, assigned, unassigned, csp) {
  function countValues(vars) {
    var sum = 0;
    for (var key in vars) { sum += vars[key].length; }
    return sum;
  }
  function valuesEliminated(val) {
    assigned[nextKey] = [val];
    var newLength = countValues(enforceConsistency(assigned, unassigned, csp));
    delete assigned[nextKey];
    return newLength;
  }
  var cache = {}, values = unassigned[nextKey];
  values.forEach(function(val) { cache[val] = valuesEliminated(val); });
  values.sort(function (a, b) { return cache[b] - cache[a]; });
  return values;
}

// UMD export
if (typeof define === 'function' && define.amd) {
  define(CSP);
} else if (typeof module === 'object' && module.exports) {
  module.exports = CSP;
} else {
  this.csp = CSP;
}

}();
