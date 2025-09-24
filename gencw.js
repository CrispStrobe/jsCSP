// gencw.js
// Generates and solves an N x N arithmetic square puzzle.
//
// Usage example: node gencw.js --ops='*,-,/'
// node gencw.js --size=4 --range=2-50 verbose --clues=3 --ops=-,+

const csp = require('./csp');

// ------------------- Configuration & Argument Parsing -------------------

const DEFAULT_CONFIG = {
  GRID_N: 3,
  MIN_N: 1,
  MAX_N: 20,
  OPS: ['+', '−', '×', '÷'],
  MAX_ATTEMPTS: 250,
  NUM_CLUES: 0,
  verbose: false,
};

function parseArgs() {
    const config = { ...DEFAULT_CONFIG };
    const args = process.argv.slice(2);
    for (const arg of args) {
        if (arg === 'verbose') { config.verbose = true; continue; }
        const [key, value] = arg.replace(/^--/, '').split('=');
        if (!value) continue;
        switch (key) {
            case 'size':
                const size = parseInt(value, 10);
                if (!isNaN(size) && size > 2) config.GRID_N = size;
                break;
            case 'range':
                const [min, max] = value.split('-').map(Number);
                if (!isNaN(min) && !isNaN(max) && min < max) {
                    config.MIN_N = min;
                    config.MAX_N = max;
                }
                break;
            case 'ops':
                const opMap = {
                    '-': '−', // Hyphen to Minus Sign
                    '*': '×', // Asterisk to Multiplication Sign
                    '/': '÷'  // Slash to Division Sign
                };
                const validOps = new Set(['+', '−', '×', '÷']);

                const userOps = value.split(',')
                                     .map(op => {
                                         const trimmedOp = op.trim();
                                         return opMap[trimmedOp] || trimmedOp; // Use mapped value or original
                                     })
                                     .filter(op => validOps.has(op));
                if (userOps.length > 0) {
                    config.OPS = userOps;
                }
                break;
            case 'clues':
                const clues = parseInt(value, 10);
                if (!isNaN(clues) && clues >= 0) config.NUM_CLUES = clues;
                break;
        }
    }
    // Set default clues for larger grids if not specified
    if (config.GRID_N > 3 && !args.some(a => a.startsWith('--clues'))) {
        config.NUM_CLUES = Math.floor(config.GRID_N / 2);
    }
    return config;
}

const config = parseArgs();

// ------------------- Utility -------------------

function log(message) { if (config.verbose) console.log(message); }
function randInt(a, b) { return Math.floor(Math.random() * (b - a + 1)) + a; }
function randChoice(arr) { return arr[Math.floor(Math.random() * arr.length)]; }
function id(r, c) { return `r${r}c${c}`; }
function opId(r, c, type, index = 0) {
    if (type === 'row') return `op_r${r}_i${index}`;
    if (type === 'col') return `op_c${c}_i${index}`;
}

function evaluate(operands, ops) {
    if (operands.length !== ops.length + 1) return null;
    let currentVal = operands[0];
    for (let i = 0; i < ops.length; i++) {
        const op = ops[i];
        const nextVal = operands[i + 1];
        switch(op) {
            case '+': currentVal += nextVal; break;
            case '−': currentVal -= nextVal; break;
            case '×': currentVal *= nextVal; break;
            case '÷':
                if (nextVal === 0 || currentVal % nextVal !== 0) return null;
                currentVal /= nextVal;
                break;
            default: return null;
        }
    }
    return currentVal;
}

// ------------------- Puzzle & Grid Generation -------------------

function buildPuzzleConstraints(config, ops, clues) {
    const { GRID_N, MIN_N, MAX_N } = config;
    const variables = {};
    const naryConstraints = [];
    for (let r = 0; r < GRID_N; r++) {
        for (let c = 0; c < GRID_N; c++) {
            const cellId = id(r, c);
            if (clues[cellId] !== undefined) {
                variables[cellId] = [clues[cellId]];
            } else {
                variables[cellId] = Array.from({ length: MAX_N - MIN_N + 1 }, (_, i) => i + MIN_N);
            }
        }
    }
    for (let r = 0; r < GRID_N; r++) {
        const vars = Array.from({ length: GRID_N }, (_, c) => id(r, c));
        naryConstraints.push({ vars, predicate: (assign) => {
            const values = vars.map(v => assign[v]), operands = values.slice(0, -1), result = values.slice(-1)[0];
            return evaluate(operands, ops.rows[r]) === result;
        }});
    }
    for (let c = 0; c < GRID_N; c++) {
        const vars = Array.from({ length: GRID_N }, (_, r) => id(r, c));
        naryConstraints.push({ vars, predicate: (assign) => {
            const values = vars.map(v => assign[v]), operands = values.slice(0, -1), result = values.slice(-1)[0];
            return evaluate(operands, ops.cols[c]) === result;
        }});
    }
    return { variables, constraints: [], naryConstraints };
}

function asciiGrid(solution, ops, N) {
  const out = [];
  const hLine = '+' + '-'.repeat(N * 4 + (N - 1) * 3) + '+';
  out.push(hLine);
  for (let r = 0; r < N; r++) {
    let numRow = '|';
    for (let c = 0; c < N; c++) {
      const val = solution[id(r, c)] != null ? String(solution[id(r, c)]) : '?';
      numRow += val.padStart(4, ' ');
      if (c < N - 2) numRow += ` ${ops[opId(r, null, 'row', c)]} `;
      else if (c === N - 2) numRow += ' = ';
    }
    numRow += ' |';
    out.push(numRow);
    if (r < N - 1) {
      let opRow = '|';
      const getOperator = (col) => (r < N - 2) ? ops[opId(null, col, 'col', r)] : '=';
      for (let c = 0; c < N; c++) {
        opRow += '  ' + getOperator(c) + ' ';
        if (c < N - 1) opRow += '   ';
      }
      opRow += ' |';
      out.push(opRow);
    }
  }
  out.push(hLine);
  return out.join('\n');
}

// ------------------- Main Generation Logic -------------------

function generatePuzzle(config) {
    const { GRID_N, OPS, MAX_ATTEMPTS, NUM_CLUES, MIN_N, MAX_N } = config;
    console.log(`\n--- Generating ${GRID_N}x${GRID_N} Puzzle ---`);
    console.log(`(Range: ${MIN_N}-${MAX_N}, Ops: [${OPS.join(', ')}])`);
    if (NUM_CLUES > 0) console.log(`(Seeding with up to ${NUM_CLUES} random clues)`);

    for (let attempt = 1; attempt <= MAX_ATTEMPTS; attempt++) {
        console.log(`\n--- Attempt ${attempt}/${MAX_ATTEMPTS} ---`);

        // Step 1: Generate operators
        const opLayout = { rows: [], cols: [] }, opDetails = {};
        for (let r = 0; r < GRID_N; r++) {
            const ops = Array.from({ length: GRID_N - 2 }, () => randChoice(OPS));
            opLayout.rows.push(ops);
            ops.forEach((op, i) => { opDetails[opId(r, null, 'row', i)] = op; });
        }
        for (let c = 0; c < GRID_N; c++) {
            const ops = Array.from({ length: GRID_N - 2 }, () => randChoice(OPS));
            opLayout.cols.push(ops);
            ops.forEach((op, i) => { opDetails[opId(null, c, 'col', i)] = op; });
        }
        
        // Step 2: Determine forbidden clue locations (divisors)
        const forbiddenClueCells = new Set();
        for (let r = 0; r < GRID_N; r++) { // Horizontal scan
            for (let i = 0; i < opLayout.rows[r].length; i++) {
                if (opLayout.rows[r][i] === '÷') forbiddenClueCells.add(id(r, i + 1));
            }
        }
        for (let c = 0; c < GRID_N; c++) { // Vertical scan
            for (let i = 0; i < opLayout.cols[c].length; i++) {
                if (opLayout.cols[c][i] === '÷') forbiddenClueCells.add(id(i + 1, c));
            }
        }
        log(`Forbidden clue locations: ${[...forbiddenClueCells].join(', ') || 'None'}`);

        // Step 3: Generate clues in valid locations
        const clues = {};
        const allCells = [];
        for (let r = 0; r < GRID_N; r++) for (let c = 0; c < GRID_N; c++) allCells.push(id(r,c));
        const validClueCells = allCells.filter(cellId => !forbiddenClueCells.has(cellId));
        validClueCells.sort(() => 0.5 - Math.random()); // Shuffle valid locations
        
        const numCluesToPlace = Math.min(NUM_CLUES, validClueCells.length);
        for (let i = 0; i < numCluesToPlace; i++) {
            clues[validClueCells[i]] = randInt(MIN_N, MAX_N);
        }

        // Step 4: Print the skeleton with clues
        console.log(asciiGrid(clues, opDetails, GRID_N));
        
        // Step 5: Try to solve
        console.log("Solving...");
        const prob = buildPuzzleConstraints(config, opLayout, clues);
        const solution = csp.solve(prob);

        if (solution !== 'FAILURE') {
            console.log("\n✅ SUCCESS! Found a solution for the layout above:");
            console.log(asciiGrid(solution, opDetails, GRID_N));
            return;
        } else {
            console.log("❌ Failed to solve. Generating new layout.");
        }
    }
    console.log(`\n--- FAILED to find a solvable layout in ${MAX_ATTEMPTS} attempts. ---`);
}

// ------------------- Run -------------------
generatePuzzle(config);
