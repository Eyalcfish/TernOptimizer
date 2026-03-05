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

	var emptyValue *Value = nil // &Value{id: 0, op: sloNone}

	if count < 4 {
		v := &Value{
			id:   rv.evalue.value.id, // Steal the ID here too!
			op:   sloTernlog,
			args: make([]*Value, 3),
		}

		if count == 1 {
			rv.evalue.params = []*EValue{totalVars[0], totalVars[0], totalVars[0]}
			v.args[0], v.args[1], v.args[2] = totalVars[0].value, emptyValue, emptyValue

		} else if count == 2 {
			rv.evalue.params = []*EValue{totalVars[0], totalVars[1], totalVars[0]}
			v.args[0], v.args[1], v.args[2] = totalVars[0].value, totalVars[1].value, emptyValue

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
			v.args[0], v.args[1], v.args[2] = recalculatedEV.params[0].value, emptyValue, emptyValue
		} else if newCount == 2 {
			recalculatedEV.params = []*EValue{recalculatedEV.params[0], recalculatedEV.params[1], recalculatedEV.params[0]}
			v.args[0], v.args[1], v.args[2] = recalculatedEV.params[0].value, recalculatedEV.params[1].value, emptyValue
		} else if newCount == 3 {
			v.args[0], v.args[1], v.args[2] = recalculatedEV.params[0].value, recalculatedEV.params[1].value, recalculatedEV.params[2].value
		}

		v.imm8 = computeTT(recalculatedEV)
		*rv.evalue.value = *v

		return v
	}

	return rv.evalue.value
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
	regA := &Value{id: 101, op: sloInterior}
	regB := &Value{id: 102, op: sloInterior}
	regC := &Value{id: 103, op: sloInterior}
	regD := &Value{id: 104, op: sloInterior}

	// The Clever Person Trap: ((A AND B) XOR B) XOR (D XOR (C AND D))
	cascadeTree := &Value{
		id: 200, op: sloXor,
		args: []*Value{
			// Left Branch: ((A AND B) XOR B)
			{
				id: 201, op: sloXor,
				args: []*Value{
					{
						id: 202, op: sloAnd,
						args: []*Value{regA, regB},
					},
					regB,
				},
			},
			// Right Branch: (D XOR (C AND D))
			{
				id: 203, op: sloXor,
				args: []*Value{
					regD,
					{
						id: 204, op: sloAnd,
						args: []*Value{regC, regD},
					},
				},
			},
		},
	}

	fmt.Println("=== BEFORE REWRITE ===")
	fmt.Print(printAST(cascadeTree, ""))

	// Run your engine!
	optimizedTree := fullRewrite(cascadeTree)

	fmt.Println("\n=== AFTER REWRITE ===")
	fmt.Print(printAST(optimizedTree, ""))
}
