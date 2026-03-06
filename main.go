package main

import (
	"fmt"
	"sort"
	"time"
)

type SIMDLogicalOP uint8

const (
	// boolean simd operations, for reducing expression to VPTERNLOG* instructions
	// sloInterior is set for non-root nodes in logical-op expression trees.
	// the operations are even-numbered.
	sloInterior SIMDLogicalOP = 1
	sloNone     SIMDLogicalOP = 2 * iota
	sloAnd
	sloOr
	sloAndNot
	sloXor
	sloNot
	sloTernlog
	sloPos // pseudo-op for positive
)

type Value struct {
	id   int
	op   SIMDLogicalOP
	args []*Value

	imm8 uint8
}

type EValue struct {
	value  *Value
	params []*EValue
	args   []*EValue
}

type RValue struct {
	evalue *EValue

	relations [2][]*EValue
	args      []*RValue
}

func simulateTERNLOG(a, b, c bool, imm8 uint8) bool {
	idx := 0
	if a {
		idx |= 4
	}
	if b {
		idx |= 2
	}
	if c {
		idx |= 1
	}
	return (imm8 & (1 << idx)) != 0
}

func GroupUnion(a, b []*EValue) []*EValue {
	result := a

	for _, vB := range b {
		found := false
		for _, vA := range a {
			if vB.value.id == vA.value.id {
				found = true
				break
			}
		}
		if !found {
			result = append(result, vB)
		}
	}
	return result
}

func computeParameterTree(v *Value) *EValue {
	ev := &EValue{
		value: v,
	}

	if v.op&sloInterior != 0 || (v.op == sloTernlog) {
		ev.params = []*EValue{ev}
		return ev
	}

	for _, arg := range v.args {
		child := computeParameterTree(arg)
		ev.args = append(ev.args, child)
		ev.params = GroupUnion(ev.params, child.params)
	}

	return ev
}

func computeTT(v *EValue) uint8 {
	var imm8 uint8 = 0
	for i := 0; i < 2; i++ {
		for j := 0; j < 2; j++ {
			for k := 0; k < 2; k++ {
				if getEValResult(v, v, []bool{i != 0, j != 0, k != 0}) {
					imm8 |= 1 << (i*4 + j*2 + k)
				}
			}
		}
	}
	return imm8
}

func getEValResult(root *EValue, ev *EValue, inputs []bool) bool {
	for idx, param := range root.params {
		if param.value.id == ev.value.id {
			return inputs[idx]
		}
	}
	Op := ev.value.op &^ sloInterior

	switch Op {
	case sloAnd:
		return getEValResult(root, ev.args[0], inputs) && getEValResult(root, ev.args[1], inputs)
	case sloOr:
		return getEValResult(root, ev.args[0], inputs) || getEValResult(root, ev.args[1], inputs)
	case sloAndNot:
		return getEValResult(root, ev.args[0], inputs) && !getEValResult(root, ev.args[1], inputs)
	case sloXor:
		return getEValResult(root, ev.args[0], inputs) != getEValResult(root, ev.args[1], inputs)
	case sloTernlog: // ASSUMES TERNLOG HAS ATLEAST 2 PARAMETERS
		a := getEValResult(root, ev.args[0], inputs)
		b := getEValResult(root, ev.args[1], inputs)
		c := len(ev.args) > 2 && getEValResult(root, ev.args[2], inputs)
		return simulateTERNLOG(a, b, c, ev.value.imm8)
	case sloNot:
		return !getEValResult(root, ev.args[0], inputs)
	case sloPos:
		return true
	default:
		panic("No such boolean function exists")
	}
}

func fullRewrite(v *Value) *Value {
	if v.op&sloInterior != 0 {
		return v
	}

	ev := computeParameterTree(v)

	rv := findRelations(ev)

	v = rewriteTern(rv)

	v = mergeTernlog(v)

	v = lowerRewrite(v)

	return v
}

func lowerRewrite(v *Value) *Value {
	// TODO: lower ternlogs to normal instructions if the ternlog is useless
	return v
}

func findRelations(ev *EValue) *RValue {
	rv := &RValue{evalue: ev}

	if ev.value.op&sloInterior != 0 {
		rv.relations = [2][]*EValue{{rv.evalue.params[0]}, {}} // A leaf node is related to itself in the first group
		return rv
	}

	arg1 := ev.args[0]
	childRV1 := findRelations(arg1)
	rv.relations[0] = GroupUnion(childRV1.relations[0], childRV1.relations[1]) // combine the relations of the child
	rv.args = append(rv.args, childRV1)

	if len(ev.args) > 1 {
		arg2 := ev.args[1]
		childRV2 := findRelations(arg2)
		rv.relations[1] = GroupUnion(childRV2.relations[0], childRV2.relations[1]) // combine the relations of the child
		rv.args = append(rv.args, childRV2)
	}

	return rv
}

func rewriteTern(rv *RValue) *Value {
	if rv.evalue.value.op&sloInterior != 0 {
		return rv.evalue.value
	}

	totalVars := GroupUnion(rv.relations[0], rv.relations[1])
	count := len(totalVars)

	if count < 4 {
		v := &Value{
			id:   rv.evalue.value.id,
			op:   sloTernlog,
			args: make([]*Value, 3),
		}

		if count == 1 {
			rv.evalue.params = []*EValue{totalVars[0], totalVars[0], totalVars[0]}
			v.args[0], v.args[1], v.args[2] = totalVars[0].value, totalVars[0].value, totalVars[0].value

		} else if count == 2 {
			rv.evalue.params = []*EValue{totalVars[0], totalVars[1], totalVars[0]}
			v.args[0], v.args[1], v.args[2] = totalVars[0].value, totalVars[1].value, totalVars[0].value

		} else if count == 3 {
			rv.evalue.params = []*EValue{totalVars[0], totalVars[1], totalVars[2]}
			v.args[0], v.args[1], v.args[2] = totalVars[0].value, totalVars[1].value, totalVars[2].value
		}

		v.imm8 = computeTT(rv.evalue)

		*rv.evalue.value = *v

		return v
	}

	if len(rv.args) > 0 {
		rv.evalue.value.args[0] = rewriteTern(rv.args[0])
	}
	if len(rv.args) > 1 {
		rv.evalue.value.args[1] = rewriteTern(rv.args[1])
	}

	recalculatedEV := computeParameterTree(rv.evalue.value)
	newCount := len(recalculatedEV.params)

	if newCount < 4 {
		v := &Value{
			id:   rv.evalue.value.id, // Steal the ID here too!
			op:   sloTernlog,
			args: make([]*Value, 3),
		}

		if newCount == 1 {
			recalculatedEV.params = []*EValue{recalculatedEV.params[0], recalculatedEV.params[0], recalculatedEV.params[0]}
			v.args[0], v.args[1], v.args[2] = recalculatedEV.params[0].value, rv.evalue.value.args[0], rv.evalue.value.args[0]
		} else if newCount == 2 {
			recalculatedEV.params = []*EValue{recalculatedEV.params[0], recalculatedEV.params[1], recalculatedEV.params[0]}
			v.args[0], v.args[1], v.args[2] = recalculatedEV.params[0].value, recalculatedEV.params[1].value, rv.evalue.value.args[0]
		} else if newCount == 3 {
			v.args[0], v.args[1], v.args[2] = recalculatedEV.params[0].value, recalculatedEV.params[1].value, recalculatedEV.params[2].value
		}

		v.imm8 = computeTT(recalculatedEV)
		*rv.evalue.value = *v

		return v
	}

	return rv.evalue.value
}

func mergeTernlog(v *Value) *Value {
	if v.op == sloTernlog {
		for i, arg := range v.args {
			v.args[i] = mergeTernlog(arg)
		}
		//rule 1
		if v.args[0].op == sloTernlog && v.args[1].op == sloTernlog {
			if v.args[0].args[2] == v.args[0].args[0] && v.args[0].args[1] != v.args[0].args[0] && v.args[1].args[2] == v.args[1].args[0] && v.args[1].args[1] != v.args[1].args[0] {
				arg1 := v.args[0]
				arg2 := v.args[1].args[0]
				arg3 := v.args[1].args[1]

				var composedImm8 uint8 = 0
				for i := 0; i < 8; i++ {
					t1_state := (i & 4) != 0
					c_state := (i & 2) != 0
					d_state := (i & 1) != 0

					t2_out := simulateTERNLOG(c_state, d_state, c_state, v.args[1].imm8)

					parent_out := simulateTERNLOG(t1_state, t2_out, t1_state, v.imm8)

					if parent_out {
						composedImm8 |= (1 << i)
					}
				}

				*v = Value{
					id:   v.id,
					op:   sloTernlog,
					args: []*Value{arg1, arg2, arg3},
					imm8: composedImm8,
				}
			}
		}
	}
	return v
}

// TESTING AND BENCHMARKING MOSTLY AI GENERATED BELOW, NOT CORE TO THE REWRITE ALGORITHM

func countNodes(v *Value) int {
	return countUniqueNodes(v, make(map[*Value]bool))
}

func countUniqueNodes(v *Value, visited map[*Value]bool) int {
	if v == nil || visited[v] {
		return 0
	}

	visited[v] = true

	count := 1
	for _, arg := range v.args {
		count += countUniqueNodes(arg, visited)
	}

	return count
}

func main() {
	// 1. Create a pool of 16 physical hardware registers
	var leafPool []*Value
	for i := 100; i < 116; i++ {
		leafPool = append(leafPool, &Value{id: i, op: sloInterior})
	}

	// 2. Build the Monster Tree
	// Depth 14 = 16,383 Operations!
	fmt.Println("==========================================")
	fmt.Println("🔨 GENERATING MONSTER TREE (Depth 14)...")
	startGen := time.Now()
	idCounter := 1000 // Start IDs high to avoid colliding with registers
	monsterTree := buildMassiveTree(10, leafPool, &idCounter)
	// fmt.Print(printAST(monsterTree, "", make(map[*Value]bool)))
	fmt.Printf("Done. Generated %d nodes in %v, Total Nodes: %d\n", idCounter-1000, time.Since(startGen), countNodes(monsterTree))

	// 3. Run the Synthesis Engine (The Rewrite)
	fmt.Println("\n🚀 COMPILING (Technology Mapping)...")
	startCompile := time.Now()
	optimizedTree := fullRewrite(monsterTree)
	compileTime := time.Since(startCompile)
	fmt.Printf("Done. Compilation took: %v, Total Nodes: %d\n", compileTime, countNodes(optimizedTree))
	// fmt.Print(printAST(optimizedTree, "", make(map[*Value]bool)))

	// 4. Formal Verification Prep
	varMap := make(map[int]bool)
	extractRegIDs(monsterTree, varMap)
	vars := make([]int, 0, len(varMap))
	for id := range varMap {
		vars = append(vars, id)
	}
	sort.Ints(vars)

	fmt.Println("\n🔬 RUNNING FORMAL VERIFICATION...")
	fmt.Printf("Variables: %d (Combinations: %d)\n", len(vars), 1<<len(vars))

	startVerify := time.Now()
	// Capture Before
	originalLogic := captureTruthTable(monsterTree, vars)
	// Capture After
	optimizedLogic := captureTruthTable(optimizedTree, vars)
	verifyTime := time.Since(startVerify)

	// 5. Check Results
	match := true
	for i := range originalLogic {
		if originalLogic[i] != optimizedLogic[i] {
			match = false
			break
		}
	}

	fmt.Println("==========================================")
	if match {
		fmt.Printf("[✓] PERFORMANCE PASSED!\n")
		fmt.Printf("    -> Compile Time: %v\n", compileTime)
		fmt.Printf("    -> Verify Time : %v\n", verifyTime)
	} else {
		fmt.Printf("[X] LOGIC CORRUPTED DURING REWRITE!\n")
	}
	fmt.Println("==========================================")
}

// buildMassiveTree recursively generates a massive, pseudo-random boolean AST
func buildMassiveTree(depth int, leafPool []*Value, idCounter *int) *Value {
	if depth == 0 {
		// Pick a "random" register from our 16-register pool based on the ID counter
		return leafPool[*idCounter%len(leafPool)]
	}

	*idCounter++
	currentID := *idCounter

	// Rotate operations to create a chaotic truth table
	op := sloXor
	if depth%3 == 1 {
		op = sloAnd
	} else if depth%3 == 2 {
		op = sloOr
	}

	return &Value{
		id: currentID,
		op: op,
		args: []*Value{
			buildMassiveTree(depth-1, leafPool, idCounter),
			buildMassiveTree(depth-1, leafPool, idCounter),
		},
	}
}

// ==========================================
// --- LOGIC EVALUATION ENGINE ---
// ==========================================

// extractRegIDs crawls the AST to find every unique physical register
func extractRegIDs(v *Value, ids map[int]bool) {
	if v == nil {
		return
	}
	if v.op&sloInterior != 0 {
		ids[v.id] = true
	}
	for _, arg := range v.args {
		extractRegIDs(arg, ids)
	}
}

// captureTruthTable evaluates the AST for every possible combination of inputs
func captureTruthTable(v *Value, vars []int) []bool {
	numVars := len(vars)
	numCombinations := 1 << numVars // 2^N combinations
	result := make([]bool, numCombinations)

	for i := 0; i < numCombinations; i++ {
		// Build the environment (1s and 0s) for this specific combination
		env := make(map[int]bool)
		for j := 0; j < numVars; j++ {
			env[vars[j]] = ((i >> j) & 1) == 1
		}
		result[i] = evalTree(v, env)
	}
	return result
}

// evalTree natively executes the boolean math of your AST, including simulating Intel's VPTERNLOGD
func evalTree(v *Value, env map[int]bool) bool {
	switch v.op {
	case sloInterior:
		return env[v.id]
	case sloAnd:
		return evalTree(v.args[0], env) && evalTree(v.args[1], env)
	case sloOr:
		return evalTree(v.args[0], env) || evalTree(v.args[1], env)
	case sloXor:
		return evalTree(v.args[0], env) != evalTree(v.args[1], env)
	case sloTernlog:
		// Simulate the physical hardware pins
		a := evalTree(v.args[0], env)
		b := evalTree(v.args[1], env)
		c := evalTree(v.args[2], env)

		// Calculate the Intel immediate byte index: (A<<2) | (B<<1) | C
		idx := 0
		if a {
			idx |= 4
		}
		if b {
			idx |= 2
		}
		if c {
			idx |= 1
		}

		// Return true if that specific bit in the imm8 hex code is a 1
		return (v.imm8 & (1 << idx)) != 0
	}
	return false
}

// ==========================================
// --- DAG PRINTER ---
// ==========================================
func printAST(v *Value, indent string, visited map[*Value]bool) string {
	if v == nil {
		return indent + "nil\n"
	}
	if visited[v] {
		return indent + fmt.Sprintf("-> [Shared Wire to Node %d]\n", v.id)
	}
	visited[v] = true

	res := indent
	switch v.op {
	case sloInterior:
		res += fmt.Sprintf("Reg[%d] len: %d\n", v.id, len(v.args))
	case sloTernlog:
		res += fmt.Sprintf("TERNLOG(imm8: 0x%02X) [ID: %d]\n", v.imm8, v.id)
	case sloAnd:
		res += "AND\n"
	case sloOr:
		res += "OR\n"
	case sloXor:
		res += "XOR\n"
	default:
		res += fmt.Sprintf("OP(%d)\n", v.op)
	}

	for _, arg := range v.args {
		res += printAST(arg, indent+"  ", visited)
	}
	return res
}
