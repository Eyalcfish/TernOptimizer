package main

import (
	"fmt"
	"strings"
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
	id   uint32
	op   SIMDLogicalOP
	args []*Value

	imm8 uint8
}

type EValue struct {
	value  *Value
	params []*EValue
	args   []*EValue

	totalArgs int
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

	if v.op&sloInterior != 0 {
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
	if ev.value.op&sloInterior != 0 {
		for idx, param := range root.params {
			if param.value.id == ev.value.id {
				return inputs[idx]
			}
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

func rewriteTern(ev *EValue) *EValue {
	if ev.value.op&sloInterior != 0 {
		return ev
	}

	if len(ev.params) < 4 && len(ev.params) > 1 {
		imm8 := computeTT(ev)
		ev.value.op = sloTernlog
		ev.value.imm8 = imm8
		params := make([]*Value, 3)
		params[0] = ev.params[0].value
		params[1] = ev.params[1].value
		params[2] = &Value{op: sloPos, id: ev.args[0].value.id}
		if len(ev.params) > 2 {
			params[2] = ev.params[2].value
		}
		ev.args = ev.params

		ev.value.args = params
		return ev
	} else {
		for _, arg := range ev.args {
			rewriteTern(arg)
		}
	}
	return ev
}

func printAST(v *Value, indent string) string {
	if v == nil {
		return "nil"
	}

	opNames := map[SIMDLogicalOP]string{
		sloAnd: "AND", sloOr: "OR", sloXor: "XOR", sloAndNot: "ANDNOT",
		sloNot: "NOT", sloTernlog: "TERNLOG", sloInterior: "LEAF",
	}

	name := opNames[v.op]
	if v.op&sloInterior != 0 && v.op != sloInterior {
		name = opNames[v.op&^sloInterior] + "_LEAF"
	} else if v.op == sloInterior {
		return fmt.Sprintf("Reg[%d]", v.id)
	}

	if v.op == sloTernlog {
		res := fmt.Sprintf("TERNLOG(imm8: 0x%02X)\n", v.imm8)
		for _, arg := range v.args {
			res += indent + "  ├── " + printAST(arg, indent+"  ") + "\n"
		}
		return strings.TrimRight(res, "\n")
	}

	res := fmt.Sprintf("%s\n", name)
	for _, arg := range v.args {
		res += indent + "  ├── " + printAST(arg, indent+"  ") + "\n"
	}
	return strings.TrimRight(res, "\n")
}

func main() {
	// 4 Hardware Registers
	aregA := &Value{id: 101, op: sloInterior}
	aregB := &Value{id: 102, op: sloInterior}
	aregC := &Value{id: 103, op: sloInterior}
	aregD := &Value{id: 104, op: sloInterior}

	// The "Clever Person" Equation: ((A AND B) XOR B) XOR (D XOR (C AND D))
	leftBranch := &Value{
		op: sloXor,
		args: []*Value{
			{op: sloAnd, args: []*Value{aregA, aregB}},
			aregB,
		},
	}

	rightBranch := &Value{
		op: sloXor,
		args: []*Value{
			aregD,
			{op: sloAnd, args: []*Value{aregC, aregD}},
		},
	}

	cleverTree := &Value{
		op:   sloXor,
		args: []*Value{leftBranch, rightBranch},
	}

	fmt.Println("=== BEFORE REWRITE: The 'Clever Person' Equation ===")
	fmt.Println(printAST(cleverTree, ""))

	// Build the context tree and run your optimizer
	eTree := computeParameterTree(cleverTree)
	rewriteTern(eTree)

	fmt.Println("\n=== AFTER REWRITE: Current Maximal Munch Output ===")
	fmt.Println(printAST(cleverTree, ""))
	// 5 Hardware Registers for complex testing
	regA := &Value{id: 101, op: sloInterior}
	regB := &Value{id: 102, op: sloInterior}
	regC := &Value{id: 103, op: sloInterior}
	regD := &Value{id: 104, op: sloInterior}
	regE := &Value{id: 105, op: sloInterior}

	fmt.Println()

	fmt.Println("=== SUITE 1: AST PURE LOGIC CHECKS ===")

	logicTests := []struct {
		name     string
		root     *Value
		inputs   []bool // Specific runtime states to test
		expected bool
	}{
		{
			name:     "T AND F -> False",
			root:     &Value{op: sloAnd, args: []*Value{regA, regB}},
			inputs:   []bool{true, false},
			expected: false,
		},
		{
			name:     "T OR F -> True",
			root:     &Value{op: sloOr, args: []*Value{regA, regB}},
			inputs:   []bool{true, false},
			expected: true,
		},
		{
			name: "Complex: (T AND F) OR (NOT F) -> True",
			root: &Value{
				op: sloOr,
				args: []*Value{
					{op: sloAnd, args: []*Value{regA, regB}}, // T & F = F
					{op: sloNot, args: []*Value{regC}},       // !F = T
				},
			},
			inputs:   []bool{true, false, false}, // regA=T, regB=F, regC=F
			expected: true,
		},
		{
			name: "4-Variable Overload: (T & T) | (F & T) -> True",
			root: &Value{
				op: sloOr,
				args: []*Value{
					{op: sloAnd, args: []*Value{regA, regB}},
					{op: sloAnd, args: []*Value{regC, regD}},
				},
			},
			// T & T | F & T == T | F == True
			inputs:   []bool{true, true, false, true},
			expected: true,
		},
		{
			name: "5-Variable Monster: ((T & T) | (F ^ T)) & F -> False",
			root: &Value{
				op: sloAnd,
				args: []*Value{
					{
						op: sloOr,
						args: []*Value{
							{op: sloAnd, args: []*Value{regA, regB}},
							{op: sloXor, args: []*Value{regC, regD}},
						},
					},
					regE,
				},
			},
			// ((T & T) | (F ^ T)) & F == (T | T) & F == T & F == False
			inputs:   []bool{true, true, false, true, false},
			expected: false,
		},
	}

	logicPassed := 0
	for _, tc := range logicTests {
		eTree := computeParameterTree(tc.root)

		// This is brilliant: you are mutating the AST and THEN checking its logic.
		// If simulateTERNLOG is wrong, these will fail!
		eTree = rewriteTern(eTree)

		result := getEValResult(eTree, eTree, tc.inputs)

		if result == tc.expected {
			fmt.Printf("[PASS] %-60s\n", tc.name)
			logicPassed++
		} else {
			fmt.Printf("[FAIL] %-60s -> Got: %v | Expected: %v\n", tc.name, result, tc.expected)
		}
	}

	fmt.Println("\n=== SUITE 2: TERNLOG IMM8 SYNTHESIS ===")

	ternTests := []struct {
		name     string
		root     *Value
		expected uint8
	}{
		{
			name:     "A AND B",
			root:     &Value{op: sloAnd, args: []*Value{regA, regB}},
			expected: 0xC0,
		},
		{
			name:     "A OR B",
			root:     &Value{op: sloOr, args: []*Value{regA, regB}},
			expected: 0xFC,
		},
		{
			name: "((A AND B) OR C) XOR A",
			root: &Value{
				op: sloXor,
				args: []*Value{
					{op: sloOr, args: []*Value{
						{op: sloAnd, args: []*Value{regA, regB}},
						regC,
					}},
					regA,
				},
			},
			expected: 0x1A,
		},
		{
			name:     "Aliased Redundancy (A AND A)",
			root:     &Value{op: sloAnd, args: []*Value{regA, regA}},
			expected: 0xF0,
		},
		{
			name: "Passthrough pre-compiled TERNLOG",
			root: &Value{
				op:   sloTernlog,
				imm8: 0x96,
				args: []*Value{regA, regB, regC},
			},
			expected: 0x96,
		},
		{
			name: "Nested TERNLOGs: OR(A, B, AND(A,B,C))",
			root: &Value{
				op:   sloTernlog,
				imm8: 0xFE,
				args: []*Value{
					regA,
					regB,
					{op: sloTernlog, imm8: 0x80, args: []*Value{regA, regB, regC}},
				},
			},
			expected: 0xFC,
		},
	}

	ternPassed := 0
	for _, tc := range ternTests {
		eTree := computeParameterTree(tc.root)
		imm8 := computeTT(eTree)

		if imm8 == tc.expected {
			fmt.Printf("[PASS] %-40s -> 0x%02X\n", tc.name, imm8)
			ternPassed++
		} else {
			fmt.Printf("[FAIL] %-40s -> Got: 0x%02X | Expected: 0x%02X\n", tc.name, imm8, tc.expected)
		}
	}

	// ========================================================================
	// NEW: SUITE 3
	// ========================================================================
	fmt.Println("\n=== SUITE 3: GRAPH MUTATION & MAXIMAL MUNCH ===")

	mutationTests := []struct {
		name   string
		root   *Value
		verify func(ev *EValue) bool // Programmatically check the AST shape
	}{
		{
			name: "Collapse 3-Variable Tree",
			root: &Value{
				op: sloOr,
				args: []*Value{
					{op: sloAnd, args: []*Value{regA, regB}},
					regC,
				},
			},
			verify: func(ev *EValue) bool {
				// The entire thing should collapse into a single TERNLOG
				return ev.value.op == sloTernlog && ev.value.imm8 == 0xEA
			},
		},
		{
			name: "Recursive Split 4-Variable Tree",
			root: &Value{
				op: sloOr,
				args: []*Value{
					{op: sloAnd, args: []*Value{regA, regB}}, // Branch L
					{op: sloAnd, args: []*Value{regC, regD}}, // Branch R
				},
			},
			verify: func(ev *EValue) bool {
				// Root must stay OR (4 variables is too many)
				if ev.value.op != sloOr {
					return false
				}

				// Left and Right children should be squashed into TERNLOGs
				leftChild := ev.args[0].value
				rightChild := ev.args[1].value

				return leftChild.op == sloTernlog && leftChild.imm8 == 0xC0 &&
					rightChild.op == sloTernlog && rightChild.imm8 == 0xC0
			},
		},
	}

	mutPassed := 0
	for _, tc := range mutationTests {
		eTree := computeParameterTree(tc.root)
		eTree = rewriteTern(eTree) // Run the optimizer

		if tc.verify(eTree) {
			fmt.Printf("[PASS] %-40s\n", tc.name)
			mutPassed++
		} else {
			fmt.Printf("[FAIL] %-40s -> Tree structural mismatch\n", tc.name)
		}
	}

	fmt.Printf("\n------------------------------------------------\n")
	fmt.Printf("RESULTS: Logic %d/%d | Ternlog %d/%d | Mutation %d/%d\n",
		logicPassed, len(logicTests), ternPassed, len(ternTests), mutPassed, len(mutationTests))
}
