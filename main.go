package main

import (
	"fmt"
	"sort"
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

	if v.op&sloInterior != 0 || v.op == sloTernlog {
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

	mergeTernlog(v)

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
		//rule 1
		if v.args[2] == v.args[0] && v.args[1] != v.args[0] {
			if v.args[0].op == sloTernlog && v.args[1].op == sloTernlog {
				if v.args[0].args[2] == v.args[0].args[0] && v.args[0].args[1] != v.args[0].args[0] && v.args[1].args[2] == v.args[1].args[0] && v.args[1].args[1] != v.args[1].args[0] {
					newarg1 := &Value{
						id:   v.args[0].id,
						op:   sloTernlog,
						args: []*Value{v.args[0].args[0], v.args[0].args[1], v.args[1].args[0]},                                                                                  // a,b,c
						imm8: computeTT(computeParameterTree(&Value{op: sloTernlog, id: v.args[0].id, args: []*Value{v.args[0].args[0], v.args[0].args[1], v.args[1].args[0]}})), // a,b,c
					}
					newv := &Value{
						id:   v.id,
						op:   sloTernlog,
						args: []*Value{newarg1, v.args[1].args[0], v.args[1].args[1]},                                                                          // ternlog(a,b,c),c,d
						imm8: computeTT(computeParameterTree(&Value{op: sloTernlog, id: v.id, args: []*Value{newarg1, v.args[1].args[0], v.args[1].args[1]}})), // ternlog(ternlog(a,b,c),c,d)
					}
					*v = *newv
				}
			}
		}
		for _, arg := range v.args {
			mergeTernlog(arg)
		}
	}
	return v
}

func main() {
	// --- REGISTERS ---
	regA := &Value{id: 101, op: sloInterior}
	regB := &Value{id: 102, op: sloInterior}
	regC := &Value{id: 103, op: sloInterior}
	regD := &Value{id: 104, op: sloInterior}
	regE := &Value{id: 105, op: sloInterior}
	regF := &Value{id: 106, op: sloInterior}

	// --- DEFINING THE TEST SUITE ---
	tests := []struct {
		name string
		tree *Value
	}{
		{
			name: "The Clever Person Trap (4 Vars)",
			tree: &Value{
				id: 200, op: sloXor,
				args: []*Value{
					{id: 201, op: sloXor, args: []*Value{{id: 202, op: sloAnd, args: []*Value{regA, regB}}, regB}},
					{id: 203, op: sloXor, args: []*Value{regD, {id: 204, op: sloAnd, args: []*Value{regC, regD}}}},
				},
			},
		},
		{
			name: "The 6-Var Split",
			tree: &Value{
				id: 300, op: sloXor,
				args: []*Value{
					{id: 301, op: sloXor, args: []*Value{{id: 302, op: sloAnd, args: []*Value{regA, regB}}, regC}},
					{id: 303, op: sloAnd, args: []*Value{{id: 304, op: sloOr, args: []*Value{regD, regE}}, regF}},
				},
			},
		},
		{
			name: "The Redundancy Wall (Deep tree, 2 Vars)",
			tree: &Value{
				id: 500, op: sloXor,
				args: []*Value{
					{id: 501, op: sloAnd, args: []*Value{
						{id: 502, op: sloXor, args: []*Value{regA, regB}},
						{id: 503, op: sloOr, args: []*Value{regA, regB}},
					}},
					{id: 504, op: sloAnd, args: []*Value{regA, regB}},
				},
			},
		},
	}

	// --- RUNNING THE TEST SUITE ---
	for _, tt := range tests {
		fmt.Printf("==========================================\n")
		fmt.Printf("TEST: %s\n", tt.name)
		fmt.Printf("==========================================\n")

		// 1. Identify all unique variables in this tree
		varMap := make(map[int]bool)
		extractRegIDs(tt.tree, varMap)
		vars := make([]int, 0, len(varMap))
		for id := range varMap {
			vars = append(vars, id)
		}
		sort.Ints(vars) // Sort for deterministic truth tables

		// 2. Capture the exact boolean logic BEFORE optimization
		originalLogic := captureTruthTable(tt.tree, vars)

		fmt.Println("=== BEFORE REWRITE ===")
		fmt.Print(printAST(tt.tree, "", make(map[*Value]bool)))

		// 3. Unleash the engine
		optimizedTree := fullRewrite(tt.tree)

		fmt.Println("\n=== AFTER REWRITE ===")
		fmt.Print(printAST(optimizedTree, "", make(map[*Value]bool)))

		// 4. Capture the boolean logic AFTER optimization
		optimizedLogic := captureTruthTable(optimizedTree, vars)

		// 5. Verify Logic Preservation
		match := true
		for i := range originalLogic {
			if originalLogic[i] != optimizedLogic[i] {
				match = false
				break
			}
		}

		if match {
			fmt.Printf("\n[✓] LOGIC VERIFIED: All %d combinations match perfectly.\n", len(originalLogic))
		} else {
			fmt.Printf("\n[X] LOGIC CORRUPTED: The rewrite changed the mathematical output!\n")
		}
		fmt.Println()
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
		res += fmt.Sprintf("Reg[%d]\n", v.id)
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
