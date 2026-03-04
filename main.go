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
)

type Value struct {
	id   uint32
	op   SIMDLogicalOP
	args []*Value
}

type EValue struct {
	value  *Value
	params []*EValue
	args   []*EValue
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

	// 2. Table-driven AST Test Cases
	tests := []struct {
		name     string
		root     *Value
		expected uint8
	}{
		{
			name:     "Identity AND (A & B)",
			root:     &Value{op: sloAnd, args: []*Value{regA, regB}},
			expected: 0xC0, // A=0xF0 & B=0xCC = 0xC0
		},
		{
			name:     "Identity OR (A | B)",
			root:     &Value{op: sloOr, args: []*Value{regA, regB}},
			expected: 0xFC, // A=0xF0 | B=0xCC = 0xFC
		},
		{
			name:     "Identity XOR (A ^ B)",
			root:     &Value{op: sloXor, args: []*Value{regA, regB}},
			expected: 0x3C, // A=0xF0 ^ B=0xCC = 0x3C
		},
		{
			name: "Ternary Mixed ((A & B) ^ C)",
			root: &Value{
				op: sloXor,
				args: []*Value{
					{op: sloAnd, args: []*Value{regA, regB}},
					regC,
				},
			},
			expected: 0x6A, // 0xC0 ^ 0xAA = 0x6A
		},
		{
			name:     "Aliasing Reduction (A & A)",
			root:     &Value{op: sloAnd, args: []*Value{regA, regA}},
			expected: 0xF0, // Should reduce perfectly to A's mask
		},
		{
			name:     "Aliasing Nullification (A ^ A)",
			root:     &Value{op: sloXor, args: []*Value{regA, regA}},
			expected: 0x00, // Should nullify
		},
		{
			name: "Deep Nesting ((A | B) & !C)",
			root: &Value{
				op: sloAnd,
				args: []*Value{
					{op: sloOr, args: []*Value{regA, regB}},
					{op: sloNot, args: []*Value{regC}},
				},
			},
			expected: 0x54, // (0xF0 | 0xCC) & ^0xAA = 0xFC & 0x55 = 0x54
		},
	}

	// 3. Execution Engine
	fmt.Println("=== SSA TERNLOG SYNTHESIS TESTS ===")
	passed := 0

	for _, tc := range tests {
		// Build the EValue AST
		eTree := computeParameterTree(tc.root)

		// Synthesize the Immediate Byte
		imm8 := computeTT(eTree)

		// Verification
		if imm8 == tc.expected {
			fmt.Printf("[PASS] %-30s -> 0x%02X\n", tc.name, imm8)
			passed++
		} else {
			fmt.Printf("[FAIL] %-30s -> Got: 0x%02X, Expected: 0x%02X\n", tc.name, imm8, tc.expected)

			// Print Deduplication state for debug
			fmt.Printf("       Variable Count: %d\n", len(eTree.params))
		}
	}

	fmt.Printf("-----------------------------------\n")
	fmt.Printf("RESULT: %d/%d Tests Passed\n", passed, len(tests))
}
