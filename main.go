package main

import (
	"fmt"
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

	switch ev.value.op {
	case sloAnd:
		return getEValResult(root, ev.args[0], inputs) && getEValResult(root, ev.args[1], inputs)
	case sloOr:
		return getEValResult(root, ev.args[0], inputs) || getEValResult(root, ev.args[1], inputs)
	case sloAndNot:
		return getEValResult(root, ev.args[0], inputs) && !getEValResult(root, ev.args[1], inputs)
	case sloXor:
		return getEValResult(root, ev.args[0], inputs) != getEValResult(root, ev.args[1], inputs)
	case sloTernlog:
		a := getEValResult(root, ev.args[0], inputs)
		b := getEValResult(root, ev.args[1], inputs)
		c := getEValResult(root, ev.args[2], inputs)
		return simulateTERNLOG(a, b, c, ev.value.imm8)
	case sloNot:
		return !getEValResult(root, ev.args[0], inputs)
	default:
		panic("No such boolean function exists")
	}
}

func main() {
	regA := &Value{id: 101, op: sloInterior}
	regB := &Value{id: 102, op: sloInterior}
	regC := &Value{id: 103, op: sloInterior}

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
	}

	logicPassed := 0
	for _, tc := range logicTests {
		eTree := computeParameterTree(tc.root)
		result := getEValResult(eTree, eTree, tc.inputs)

		if result == tc.expected {
			fmt.Printf("[PASS] %-40s\n", tc.name)
			logicPassed++
		} else {
			fmt.Printf("[FAIL] %-40s -> Got: %v | Expected: %v\n", tc.name, result, tc.expected)
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
		// ==========================================
		// NEW TESTS: sloTernlog Integration
		// ==========================================
		{
			// Proves the engine can evaluate a pre-compiled TERNLOG node.
			// 0x96 is the truth table for (A XOR B XOR C).
			name: "Passthrough pre-compiled TERNLOG",
			root: &Value{
				op:   sloTernlog,
				imm8: 0x96,
				args: []*Value{regA, regB, regC},
			},
			expected: 0x96,
		},
		{
			// Proves we can combine a standard logical op with a TERNLOG.
			// Expression: A AND TERNLOG_XOR(A, B, C)
			// Math: 0xF0 & 0x96 = 0x90
			name: "Hybrid: A AND TERNLOG_XOR(A, B, C)",
			root: &Value{
				op: sloAnd,
				args: []*Value{
					regA,
					{op: sloTernlog, imm8: 0x96, args: []*Value{regA, regB, regC}},
				},
			},
			expected: 0x90,
		},
		{
			// The Holy Grail: Folding multiple TERNLOGs into one.
			// Inner: TERNLOG_AND(A, B, C) -> 0x80
			// Outer: TERNLOG_OR(A, B, Inner) -> 0xFE is the truth table for X | Y | Z
			// Math: A | B | (A & B & C) = 0xF0 | 0xCC | 0x80 = 0xFC
			name: "Nested TERNLOGs: OR(A, B, AND(A,B,C))",
			root: &Value{
				op:   sloTernlog,
				imm8: 0xFE, // Truth table for (arg0 | arg1 | arg2)
				args: []*Value{
					regA,
					regB,
					{op: sloTernlog, imm8: 0x80, args: []*Value{regA, regB, regC}}, // Truth table for (arg0 & arg1 & arg2)
				},
			},
			expected: 0xFC,
		},
		{
			// Testing parameter aliasing inside a TERNLOG node.
			// Expression: TERNLOG_NOT(A) OR B
			// 0x0F is the truth table for NOT A (inverts the highest nibble).
			// Math: (!A) | B = 0x0F | 0xCC = 0xCF
			name: "Aliased Hybrid: TERNLOG_NOT(A) OR B",
			root: &Value{
				op: sloOr,
				args: []*Value{
					{op: sloTernlog, imm8: 0x0F, args: []*Value{regA, regA, regA}}, // Padding args with regA
					regB,
				},
			},
			expected: 0xCF,
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

	fmt.Printf("\n------------------------------------------------\n")
	fmt.Printf("RESULTS: Logic %d/%d | Ternlog %d/%d\n", logicPassed, len(logicTests), ternPassed, len(ternTests))
}
