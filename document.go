package document

import (
	"fmt"
	"strings"

	ft "github.com/leisure-tools/lazyfingertree"
)

///
/// types
///

type Set[T comparable] map[T]bool

type OpTree = ft.FingerTree[OpMeasurer, Operation, Measure]

type Document struct {
	Ops OpTree
}

type Replacement struct {
	Offset int
	Length int
	Text   string
}

type OpMeasurer bool

type Operation interface {
	OpString(offset int) string
	GetText() string
	Measure() Measure
	Merge(m *Merger) bool
	fmt.Stringer
}

type Measure struct {
	OldLen  int
	NewLen  int
	Markers Set[string]
}

type RetainOp struct {
	Text string
}

type DeleteOp struct {
	Text string
	// could put a pointer to a "move" operation here if text has moved
}

type InsertOp struct {
	Peer string // used for ordering
	Text string
}

type MarkerOp struct {
	Name string
}

///
/// set
///

func NewSet[T comparable](elements ...T) Set[T] {
	result := Set[T]{}
	for _, item := range elements {
		result[item] = true
	}
	return result
}

func (m Set[T]) Copy() Set[T] {
	result := Set[T]{}
	for k, v := range m {
		result[k] = v
	}
	return result
}

func (m Set[T]) Merge(m2 Set[T]) Set[T] {
	for k, v := range m2 {
		m[k] = v
	}
	return m
}

func (m Set[T]) Union(m2 Set[T]) Set[T] {
	if len(m) == 0 {
		return m
	} else if len(m2) == 0 {
		return m2
	}
	return m.Copy().Merge(m2)
}

func (m Set[T]) Add(op T) Set[T] {
	m[op] = true
	return m
}

func (m Set[T]) Has(op T) bool {
	return m[op]
}

///
/// opMeasurer
///

func (m OpMeasurer) Identity() Measure {
	return Measure{}
}

func (m OpMeasurer) Measure(op Operation) Measure {
	return op.Measure()
}

func (m OpMeasurer) Sum(a Measure, b Measure) Measure {
	return Measure{
		OldLen:  a.OldLen + b.OldLen,
		NewLen:  a.NewLen + b.NewLen,
		Markers: a.Markers.Union(b.Markers),
	}
}

///
/// operations
///

func (r *RetainOp) String() string {
	return r.Text
}

func (r *RetainOp) OpString(offset int) string {
	return fmt.Sprintf("retain[%d](%d, '%s')", len(r.Text), offset, r.Text)
}

func (r *RetainOp) GetText() string {
	return r.Text
}

func (r *RetainOp) Measure() Measure {
	return Measure{OldLen: len(r.Text), NewLen: len(r.Text)}
}

func (r *RetainOp) Merge(m *Merger) bool {
	// only called when both are retains
	opB, _ := m.Fb.(*RetainOp)
	if len(r.Text) > len(opB.Text) {
		m.swap()
		r, opB = opB, r
	}
	m.appendOps(r)
	if len(r.Text) < len(opB.Text) {
		return m.shiftA(&RetainOp{opB.Text[len(r.Text):]})
	}
	return m.shiftBoth()
}

func (d *DeleteOp) String() string {
	return ""
}

func (d *DeleteOp) OpString(offset int) string {
	return fmt.Sprintf("delete[%d](%d, %d)", len(d.Text), offset, len(d.Text))
}

func (d *DeleteOp) GetText() string {
	return d.Text
}

func (d *DeleteOp) Measure() Measure {
	return Measure{OldLen: len(d.Text)}
}

func (d *DeleteOp) Merge(m *Merger) bool {
	switch opB := m.Fb.(type) {
	case *RetainOp:
		if len(d.Text) > len(opB.Text) {
			m.addDelete(d.Text[0:len(opB.Text)])
			m.swap()
			return m.shiftA(&DeleteOp{d.Text[len(opB.Text):]})
		} else {
			m.addDelete(d.Text)
			if len(d.Text) < len(opB.Text) {
				return m.shiftA(&RetainOp{opB.Text[len(d.Text):]})
			} else {
				return m.shiftBoth()
			}
		}
	case *DeleteOp:
		if len(d.Text) > len(opB.Text) {
			m.swap()
			d, opB = opB, d
		}
		m.addDelete(d.Text)
		if len(d.Text) < len(opB.Text) {
			return m.shiftA(&DeleteOp{opB.Text[len(d.Text):]})
		} else {
			return m.shiftBoth()
		}
	default:
		m.addDelete(d.Text)
		return m.shiftA(opB)
	}
}

func (i *InsertOp) String() string {
	return i.Text
}

func (i *InsertOp) OpString(offset int) string {
	return fmt.Sprintf("insert[%s, %d](%d, '%s')", i.Peer, len(i.Text), offset, i.Text)
}

func (i *InsertOp) GetText() string {
	return i.Text
}

func (i *InsertOp) Measure() Measure {
	return Measure{NewLen: len(i.Text)}
}

func (i *InsertOp) Merge(m *Merger) bool {
	switch opB := m.Fb.(type) {
	case *RetainOp:
		m.appendOps(i)
		return m.shiftA(opB)
	case *DeleteOp:
		m.swap() // handle in the delete case above
		return true
	case *InsertOp:
		if i.Peer > opB.Peer {
			m.swap()
			i, opB = opB, i
		}
		return m.shiftBoth(i, opB)
	default:
		m.appendOps(i)
		return m.shiftA(opB)
	}
}

func (s *MarkerOp) String() string {
	return ""
}

func (s *MarkerOp) OpString(offset int) string {
	return fmt.Sprintf("marker(%s, %d)", s.Name, offset)
}

func (s *MarkerOp) GetText() string {
	return ""
}

func (s *MarkerOp) Measure() Measure {
	return Measure{Markers: NewSet(s.Name)}
}

func (opA *MarkerOp) Merge(m *Merger) bool {
	switch opB := m.Fb.(type) {
	case *RetainOp:
		m.appendOps(opA)
		return m.shiftA(opB)
	case *DeleteOp, *InsertOp:
		m.swap() // handle in the case above
		return true
	default:
		return m.shiftBoth(opA, opB)
	}
}

///
/// document
///

func newOpTree(ops ...Operation) OpTree {
	return ft.FromArray[OpMeasurer, Operation, Measure](OpMeasurer(true), ops)
}

func NewDocument(text ...string) *Document {
	sb := &strings.Builder{}
	var ops OpTree
	if len(text) > 0 {
		for _, t := range text {
			fmt.Fprint(sb, t)
		}
		ops = newOpTree(&RetainOp{sb.String()})
	} else {
		ops = newOpTree()
	}
	return &Document{
		Ops: ops,
	}
}

func (d *Document) Copy() *Document {
	d2 := *d
	return &d2
}

func (d *Document) Freeze() *Document {
	return NewDocument(d.String())
}

// string for the new document
func (d *Document) String() string {
	sb := &strings.Builder{}
	for _, item := range d.Ops.ToSlice() {
		fmt.Fprint(sb, item)
	}
	return sb.String()
}

// string for the original document
func (d *Document) OriginalString() string {
	sb := &strings.Builder{}
	for _, item := range d.Ops.ToSlice() {
		switch op := item.(type) {
		case *DeleteOp, *RetainOp:
			fmt.Fprint(sb, op.GetText())
		}
	}
	return sb.String()
}

func OpString(tree OpTree) string {
	sb := &strings.Builder{}
	pos := 0
	first := true
	for _, item := range tree.ToSlice() {
		if first {
			first = false
		} else {
			fmt.Fprint(sb, ", ")
		}
		fmt.Fprint(sb, item.OpString(pos))
		pos += item.Measure().NewLen
	}
	return sb.String()
}

func (d *Document) OpString() string {
	return OpString(d.Ops)
}

func As[T any](v any) T {
	if tv, ok := v.(T); ok {
		return tv
	}
	panic(fmt.Sprintf("Bad value: %v", v))
}

// split the tree's old text at an offset
func SplitOld(tree OpTree, offset int) (OpTree, OpTree) {
	if offset > tree.Measure().OldLen+1 {
		panic(fmt.Errorf("Split point %d is not within doc of length %d", offset, tree.Measure().OldLen))
	}
	left, right := tree.Split(func(m Measure) bool {
		return m.OldLen > offset
	})
	splitPoint := offset - left.Measure().OldLen
	if splitPoint > 0 {
		// not a clean break, if the first right element is a retain, it needs to be split
		// otherwise it is a delete and should remain on the right
		switch first := right.PeekFirst().(type) {
		case *RetainOp:
			left = left.AddLast(&RetainOp{first.Text[:splitPoint]})
			right = right.RemoveFirst().AddFirst(&RetainOp{first.Text[splitPoint:]})
		case *DeleteOp:
			// leave it on the right
		default:
			panic(fmt.Errorf("bad value at split point %d: %v", splitPoint, first))
		}
	}
	return left, right
}

// SplitNew the tree's new text at an offset
func SplitNew(tree OpTree, offset int) (OpTree, OpTree) {
	if offset > tree.Measure().NewLen+1 {
		panic(fmt.Errorf("Split point %d is not within doc of length %d", offset, tree.Measure().NewLen))
	}
	left, right := tree.Split(func(m Measure) bool {
		return m.NewLen > offset
	})
	splitPoint := offset - left.Measure().NewLen
	if splitPoint > 0 {
		// not a clean break, the first right element is a retain or insert element and needs to be split
		first := right.PeekFirst()
		right = right.RemoveFirst()
		switch first := first.(type) {
		case *RetainOp:
			left = left.AddLast(&RetainOp{first.Text[:splitPoint]})
			right = right.AddFirst(&RetainOp{first.Text[splitPoint:]})
		case *InsertOp:
			left = left.AddLast(&InsertOp{first.Peer, first.Text[:splitPoint]})
			right = right.AddFirst(&InsertOp{first.Peer, first.Text[splitPoint:]})
		default:
			panic(fmt.Errorf("bad value at split point %d: %v", splitPoint, first))
		}
	}
	return left, right
}

func Isa[T any](v any) bool {
	_, ok := v.(T)
	return ok
}

// if left ends in inserts and (optionally) markers, shift them to right
func ShiftInsertsRight(left OpTree, right OpTree) (OpTree, OpTree) {
	l, r := left, right
	found := false
	for !l.IsEmpty() {
		switch op := l.PeekLast().(type) {
		case *MarkerOp, *InsertOp:
			l = l.RemoveLast()
			r = r.AddFirst(op)
			found = found || Isa[*InsertOp](op)
			continue
		}
		break
	}
	if found {
		return l, r
	}
	return left, right
}

// if left ends in deletes and (optionally) markers, shift them to right
func ShiftDeletesRight(left OpTree, right OpTree) (OpTree, OpTree) {
	l, r := left, right
	found := false
	for !l.IsEmpty() {
		switch op := l.PeekLast().(type) {
		case *MarkerOp, *DeleteOp:
			l = l.RemoveLast()
			r = r.AddFirst(op)
			found = found || Isa[*DeleteOp](op)
			continue
		}
		break
	}
	if found {
		return l, r
	}
	return left, right
}

func RemoveMarker(tree OpTree, name string) OpTree {
	left, right := SplitOnMarker(tree, name)
	if !right.IsEmpty() {
		tree = left.Concat(right.RemoveFirst())
	}
	return tree
}

func (d *Document) Replace(peer string, start int, length int, str string) {
	// the left mid value should be a string if mid is nonempty
	left, right := SplitNew(d.Ops, start)
	if length > 0 {
		sb := &strings.Builder{}
		// gather deletes at the end of left, followed by markers
		mid := newOpTree()
		left, mid = ShiftDeletesRight(left, mid)
		if !mid.IsEmpty() {
			// there will only be one delete
			del, _ := mid.PeekFirst().(*DeleteOp)
			fmt.Fprint(sb, del.Text)
			mid = mid.RemoveFirst()
		}
		var del OpTree
		del, right = SplitNew(right, length)
		del.Each(func(v Operation) bool {
			switch o := v.(type) {
			case *RetainOp, *DeleteOp:
				// coalesce retains and deletes into a single delete
				fmt.Fprint(sb, o.GetText())
			case *InsertOp:
				// chuck inserts
			default:
				// gather markers after the delete
				mid.AddLast(o)
			}
			return true
		})
		if !right.IsEmpty() {
			switch del := right.PeekFirst().(type) {
			case *DeleteOp:
				fmt.Fprint(sb, del.Text)
				right = right.RemoveFirst()
			}
		}
		left = left.AddLast(&DeleteOp{sb.String()}).Concat(mid)
	}
	if len(str) > 0 {
		right = right.AddFirst(&InsertOp{peer, str})
	}
	d.Ops = left.Concat(right)
}

type Merger struct {
	Doc    *Document
	Ops    []Operation
	Fa, Fb Operation
	Ta, Tb ft.FingerTree[OpMeasurer, Operation, Measure]
}

func (d *Document) Merge(b *Document) {
	(&Merger{
		Doc: d,
		Ops: make([]Operation, 0, 8),
		Ta:  d.Ops,
		Tb:  b.Ops,
	}).merge(d, b)
}

func (m *Merger) swap() {
	m.Fa, m.Ta, m.Fb, m.Tb = m.Fb, m.Tb, m.Fa, m.Ta
}

func (m *Merger) shiftBoth(newOps ...Operation) bool {
	m.appendOps(newOps...)
	if m.Ta.IsEmpty() {
		m.Doc.Ops = newOpTree(m.Ops...).Concat(m.Tb)
	} else if m.Tb.IsEmpty() {
		m.Doc.Ops = newOpTree(m.Ops...).Concat(m.Ta)
	} else {
		m.Fa = m.Ta.PeekFirst()
		m.Ta = m.Ta.RemoveFirst()
		m.Fb = m.Tb.PeekFirst()
		m.Tb = m.Tb.RemoveFirst()
		return true
	}
	return false
}

func (m *Merger) shiftA(newB Operation) bool {
	if m.Ta.IsEmpty() {
		m.Doc.Ops = newOpTree(m.Ops...).Concat(m.Tb.AddFirst(newB))
		return false
	}
	m.Fb = newB
	m.Fa = m.Ta.PeekFirst()
	m.Ta = m.Ta.RemoveFirst()
	return true
}

func (m *Merger) addDelete(text string) {
	if len(m.Ops) > 0 {
		if del, ok := m.Ops[len(m.Ops)-1].(*DeleteOp); ok {
			m.Ops[len(m.Ops)-1] = &DeleteOp{del.Text + text}
			return
		}
	}
	m.appendOps(&DeleteOp{text})
}

func (m *Merger) appendOps(ops ...Operation) {
	m.Ops = append(m.Ops, ops...)
}

// Merge operations from the same ancestor document into this one
func (m *Merger) merge(a, b *Document) {
	if !m.shiftBoth() {
		return
	}
	for cont := true; cont; {
		if _, ok := m.Fa.(*RetainOp); ok {
			m.swap()
		}
		cont = m.Fa.Merge(m)
	}
}

func SplitOnMarker(tree OpTree, name string) (OpTree, OpTree) {
	return tree.Split(func(m Measure) bool {
		return m.Markers.Has(name)
	})
}

func (d *Document) SplitOnMarker(name string) (OpTree, OpTree) {
	return SplitOnMarker(d.Ops, name)
}

// append edits that restore the original document
func (d *Document) ReverseEdits() []Replacement {
	edits := make([]Replacement, 0, 8)
	var repl Replacement
	offset := d.Ops.Measure().NewLen
	d.Ops.EachReverse(func(op Operation) bool {
		switch op := op.(type) {
		case *DeleteOp:
			repl.Text = op.Text + repl.Text
		case *InsertOp:
			repl.Length += len(op.Text)
			offset -= len(op.Text)
		case *RetainOp:
			if repl.Length > 0 || len(repl.Text) > 0 {
				repl.Offset = offset
				edits = append(edits, repl)
				repl.Length = 0
				repl.Text = ""
			}
			offset -= len(op.Text)
		}
		return true
	})
	if repl.Length > 0 || len(repl.Text) > 0 {
		repl.Offset = offset
		edits = append(edits, repl)
	}
	return edits
}

// append Edits that restore the original document
func (d *Document) Edits() []Replacement {
	edits := make([]Replacement, 0, 8)
	hasRepl := false
	var repl Replacement
	offset := 0
	ensureRepl := func() {
		if !hasRepl {
			hasRepl = true
			repl.Offset = offset
			repl.Length = 0
			repl.Text = ""
		}
	}
	d.Ops.Each(func(op Operation) bool {
		switch op := op.(type) {
		case *DeleteOp:
			ensureRepl()
			repl.Length += len(op.Text)
		case *InsertOp:
			ensureRepl()
			repl.Text += op.Text
			offset += len(op.Text)
		case *RetainOp:
			if hasRepl {
				edits = append(edits, repl)
				hasRepl = false
			}
			offset += len(op.Text)
		}
		return true
	})
	if hasRepl {
		edits = append(edits, repl)
	}
	return edits
}

func (d *Document) Apply(peer string, edits []Replacement) {
	for _, repl := range edits {
		d.Replace(peer, repl.Offset, repl.Length, repl.Text)
	}
}

func Apply(peer, str string, repl []Replacement) string {
	doc := NewDocument(peer, str)
	doc.Apply(peer, repl)
	return doc.String()
}
