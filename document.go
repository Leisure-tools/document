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
	Offset int    `json:"offset"`
	Length int    `json:"length"`
	Text   string `json:"text"`
}

type OpMeasurer bool

type Operation interface {
	OpString(offset int, verbose ...bool) string
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

type SkipOp struct {
	Text string
	// could put a pointer to a "move" operation here if text has moved
}

type InsertOp struct {
	Peer string // used for ordering
	Text string
}

type MarkerOp struct {
	Names Set[string]
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

func (s Set[T]) ToSlice() []T {
	items := make([]T, 0, len(s))
	for item := range s {
		items = append(items, item)
	}
	return items
}

func (s Set[T]) Copy() Set[T] {
	result := Set[T]{}
	for k, v := range s {
		result[k] = v
	}
	return result
}

func (s Set[T]) Merge(s2 Set[T]) Set[T] {
	for k, v := range s2 {
		s[k] = v
	}
	return s
}

func (s Set[T]) Union(s2 Set[T]) Set[T] {
	if len(s) == 0 {
		return s2
	} else if len(s2) == 0 {
		return s
	}
	return s.Copy().Merge(s2)
}

func (s Set[T]) Add(op T) Set[T] {
	s[op] = true
	return s
}

func (s Set[T]) Remove(op T) Set[T] {
	delete(s, op)
	return s
}

func (s Set[T]) Has(op T) bool {
	return s[op]
}

func (s Set[T]) IsEmpty() bool {
	return len(s) == 0
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

func (r *RetainOp) OpString(offset int, verbose ...bool) string {
	return fmt.Sprintf("retain[%d](%d, '%s')", len(r.Text), offset, r.Text)
}

func (r *RetainOp) GetText() string {
	if r == nil {
		return ""
	}
	return r.Text
}

func (r *RetainOp) Measure() Measure {
	return Measure{OldLen: len(r.Text), NewLen: len(r.Text)}
}

func (r *RetainOp) Merge(m *Merger) bool {
	// only called when both are retains
	opB, _ := m.OpB.(*RetainOp)
	if len(r.Text) > len(opB.Text) {
		m.swap()
		r, opB = opB, r
	}
	m.appendOps(r)
	m.commitPending()
	if len(r.Text) < len(opB.Text) {
		return m.shiftA(&RetainOp{opB.Text[len(r.Text):]})
	}
	return m.shiftBoth()
}

func (s *SkipOp) String() string {
	return ""
}

func (s *SkipOp) OpString(offset int, verbose ...bool) string {
	verboseStr := ""
	if len(verbose) > 0 {
		verboseStr = ", " + s.Text
	}
	return fmt.Sprintf("skip[%d%s](%d, %d)", len(s.Text), verboseStr, offset, len(s.Text))
}

func (s *SkipOp) GetText() string {
	if s == nil {
		return ""
	}
	return s.Text
}

func (s *SkipOp) Measure() Measure {
	return Measure{OldLen: len(s.Text)}
}

func (s *SkipOp) Merge(m *Merger) bool {
	switch opB := m.OpB.(type) {
	case *RetainOp:
		if len(s.Text) > len(opB.Text) {
			m.addSkip(s.Text[0:len(opB.Text)])
			m.swap()
			return m.shiftA(&SkipOp{s.Text[len(opB.Text):]})
		}
		m.addSkip(s.Text)
		if len(s.Text) < len(opB.Text) {
			return m.shiftA(&RetainOp{opB.Text[len(s.Text):]})
		}
		return m.shiftBoth()
	case *SkipOp:
		if len(s.Text) > len(opB.Text) {
			m.swap()
			s, opB = opB, s
		}
		m.addSkip(s.Text)
		if len(s.Text) < len(opB.Text) {
			return m.shiftA(&SkipOp{opB.Text[len(s.Text):]})
		}
		return m.shiftBoth()
	default: // *MarkerOp, *InsertOp
		m.addSkip(s.Text)
		return m.shiftA(opB)
	}
}

func (i *InsertOp) String() string {
	return i.Text
}

func (i *InsertOp) OpString(offset int, verbose ...bool) string {
	return fmt.Sprintf("insert[%s, %d](%d, '%s')", i.Peer, len(i.Text), offset, i.Text)
}

func (i *InsertOp) GetText() string {
	if i == nil {
		return ""
	}
	return i.Text
}

func (i *InsertOp) Measure() Measure {
	return Measure{NewLen: len(i.Text)}
}

func (i *InsertOp) Merge(m *Merger) bool {
	switch opB := m.OpB.(type) {
	case *RetainOp:
		m.appendOps(i)
		return m.shiftA(opB)
	case *SkipOp:
		m.swap() // handle in the skip case above
		return true
	case *InsertOp:
		if i.Peer > opB.Peer {
			m.swap()
			i, opB = opB, i
		}
		return m.shiftBoth(i, opB)
	default: // MarkerOp
		m.appendOps(i)
		return m.shiftA(opB)
	}
}

func (s *MarkerOp) String() string {
	return ""
}

func (s *MarkerOp) OpString(offset int, verbose ...bool) string {
	return fmt.Sprintf("marker(%s, %d)", strings.Join(s.Names.ToSlice(), ", "), offset)
}

func (s *MarkerOp) GetText() string {
	return ""
}

func (s *MarkerOp) Measure() Measure {
	return Measure{Markers: s.Names}
}

func (opA *MarkerOp) Merge(m *Merger) bool {
	switch opB := m.OpB.(type) {
	case *MarkerOp:
		return m.shiftBoth(&MarkerOp{opA.Names.Union(opB.Names)})
	case *SkipOp, *InsertOp:
		m.swap() // handle in the case above
		return true
	default: //case *RetainOp:
		m.appendOps(opA)
		return m.shiftA(opB)
	}
}

///
/// merger
///

type Merger struct {
	Doc          *Document
	Merged       []Operation
	PendingOps   []Operation
	PendingSkip  *strings.Builder
	OpA, OpB     Operation
	TreeA, TreeB ft.FingerTree[OpMeasurer, Operation, Measure]
}

func (m *Merger) swap() {
	m.OpA, m.TreeA, m.OpB, m.TreeB = m.OpB, m.TreeB, m.OpA, m.TreeA
}

func (m *Merger) shiftBoth(newOps ...Operation) bool {
	m.appendOps(newOps...)
	if !m.TreeA.IsEmpty() && !m.TreeB.IsEmpty() {
		m.OpA = m.TreeA.PeekFirst()
		m.TreeA = m.TreeA.RemoveFirst()
		m.OpB = m.TreeB.PeekFirst()
		m.TreeB = m.TreeB.RemoveFirst()
		return true
	}
	m.commitPending()
	// one of the trees is empty, so just concat them both
	m.Doc.Ops = newOpTree(m.Merged...).Concat(m.TreeA.Concat(m.TreeB))
	return false
}

func (m *Merger) shiftA(newB Operation) bool {
	if !m.TreeA.IsEmpty() {
		m.OpB = newB
		m.OpA = m.TreeA.PeekFirst()
		m.TreeA = m.TreeA.RemoveFirst()
		return true
	}
	m.commitPending()
	m.Doc.Ops = newOpTree(m.Merged...).AddLast(newB).Concat(m.TreeA.Concat(m.TreeB))
	return false
}

func (m *Merger) addSkip(text string) {
	if len(m.Merged) > 0 {
		if skip, ok := m.Merged[len(m.Merged)-1].(*SkipOp); ok {
			m.Merged[len(m.Merged)-1] = &SkipOp{skip.Text + text}
			return
		}
	}
	m.appendOps(&SkipOp{text})
}

func (m *Merger) appendOps(ops ...Operation) {
	m.PendingOps = append(m.PendingOps, ops...)
}

func (m *Merger) commitPending() {
	if m.PendingSkip.Len() > 0 {
		m.Merged = append(m.Merged, &SkipOp{m.PendingSkip.String()})
		m.PendingSkip.Reset()
	}
	if len(m.PendingOps) > 0 {
		m.Merged = append(m.Merged, m.PendingOps...)
		m.PendingOps = m.PendingOps[:0]
	}
}

// Merge operations from the same ancestor document into this one
func (m *Merger) merge(a, b *Document) {
	if !m.shiftBoth() {
		return
	}
	for cont := true; cont; {
		if Isa[*RetainOp](m.OpA) {
			m.swap()
		}
		cont = m.OpA.Merge(m)
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
		case *SkipOp, *RetainOp:
			fmt.Fprint(sb, op.GetText())
		}
	}
	return sb.String()
}

func OpString(tree OpTree, verbose ...bool) string {
	sb := &strings.Builder{}
	pos := 0
	first := true
	for _, item := range tree.ToSlice() {
		if first {
			first = false
		} else {
			fmt.Fprint(sb, ", ")
		}
		fmt.Fprint(sb, item.OpString(pos, verbose...))
		pos += item.Measure().NewLen
	}
	return sb.String()
}

func (d *Document) OpString(verbose ...bool) string {
	return OpString(d.Ops, verbose...)
}

func (d *Document) Changes(prefix string) string {
	return Changes(prefix, d.Ops)
}

func Changes(prefix string, ops OpTree) string {
	sb := &strings.Builder{}
	for _, op := range ops.ToSlice() {
		switch op := op.(type) {
		case *MarkerOp:
			fmt.Fprintf(sb, "%s> %s\n", prefix, strings.Join(op.Names.ToSlice(), ", "))
		case *RetainOp:
			printOp(sb, prefix, "=", op.Text)
		case *SkipOp:
			printOp(sb, prefix, "-", op.Text)
		case *InsertOp:
			printOp(sb, prefix, "+", op.Text)
		}
	}
	return sb.String()
}

func printOp(sb *strings.Builder, lead, prefix, text string) {
	for _, line := range strings.Split(text, "\n") {
		fmt.Fprintf(sb, "%s%s%s%s\n", lead, prefix, line, prefix)
	}
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
		// otherwise it is a skip and should remain on the right
		switch first := right.PeekFirst().(type) {
		case *RetainOp:
			left = left.AddLast(&RetainOp{first.Text[:splitPoint]})
			right = right.RemoveFirst().AddFirst(&RetainOp{first.Text[splitPoint:]})
		case *SkipOp:
			// leave it on the right
		default:
			panic(fmt.Errorf("bad value at split point %d: %v", splitPoint, first))
		}
	}
	return left, right
}

// SplitNew the tree's new text at an offset
func SplitNew(tree OpTree, offset int) (OpTree, OpTree) {
	if offset > tree.Measure().NewLen {
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

// delete from the new text -- save retained text in skipText and discard inserts
func deleteText(right OpTree, length int, skipText *strings.Builder) OpTree {
	left := newOpTree()
	for length > 0 {
		if right.IsEmpty() {
			panic("Delete past end of document")
		}
		first := right.PeekFirst()
		right = right.RemoveFirst()
		switch op := first.(type) {
		case *RetainOp:
			if length >= len(op.GetText()) {
				skipText.WriteString(op.GetText())
				length -= len(op.GetText())
				continue
			}
			skipText.WriteString(op.GetText()[:length])
			first = &RetainOp{op.GetText()[length:]}
			length = 0
		case *InsertOp:
			if length >= len(op.GetText()) {
				length -= len(op.GetText())
				continue
			}
			first = &InsertOp{op.Peer, op.Text[length:]}
			length = 0
		}
		left = left.AddLast(first)
	}
	return left.Concat(right)
}

// find the first skip to the left if there is one before the first retain
func getLeftSkip(t OpTree) (OpTree, *SkipOp, OpTree) {
	empty := newOpTree()
	left := t
	right := empty
	for !left.IsEmpty() {
		last := left.PeekLast()
		left = left.RemoveLast()
		switch op := last.(type) {
		case *RetainOp:
			break
		case *SkipOp:
			return left, op, right
		}
		right = right.AddFirst(last)
	}
	return t, nil, empty
}

func RemoveMarker(tree OpTree, name string) OpTree {
	left, right := SplitOnMarker(tree, name)
	if !right.IsEmpty() {
		if m, ok := right.PeekFirst().(*MarkerOp); ok {
			if len(m.Names) == 1 {
				return left.Concat(right.RemoveFirst())
			} else {
				return left.Concat(right.RemoveFirst().AddFirst(&MarkerOp{m.Names.Copy().Remove(name)}))
			}
		} else {
			panic(fmt.Errorf("Internal document error, split on a marker but right side did not start with a marker"))
		}
	}
	return tree
}

func (d *Document) Replace(peer string, start int, length int, str string) {
	// if right is nonempty, it should start with an insert or a retain
	left, right := SplitNew(d.Ops, start)
	for length > 0 {
		if right.IsEmpty() {
			panic("Delete past end of document")
		}
		first := right.PeekFirst()
		right = right.RemoveFirst()
		switch op := first.(type) {
		case *SkipOp, *MarkerOp:
			left = left.AddLast(first)
		default:
			if ins, ok := op.(*InsertOp); ok {
				if length < len(op.GetText()) {
					right = right.AddFirst(&InsertOp{ins.Peer, op.GetText()[length:]})
				}
			} else {
				if length < len(op.GetText()) {
					right = right.AddFirst(&RetainOp{op.GetText()[length:]})
				}
				if length > len(op.GetText()) {
					left = left.AddLast(&SkipOp{op.GetText()})
				} else {
					left = left.AddLast(&SkipOp{op.GetText()[:length]})
				}
			}
			length -= len(op.GetText())
		}
	}
	if str != "" {
		left = left.AddLast(&InsertOp{peer, str})
	}
	d.Ops = left.Concat(right)
}

func SplitOnMarker(tree OpTree, name string) (OpTree, OpTree) {
	return tree.Split(func(m Measure) bool {
		return m.Markers.Has(name)
	})
}

// Merge another version of the original document into this one
func (d *Document) Merge(b *Document) {
	(&Merger{
		Doc:         d,
		Merged:      make([]Operation, 0, 8),
		PendingOps:  make([]Operation, 0, 8),
		PendingSkip: &strings.Builder{},
		TreeA:       d.Ops,
		TreeB:       b.Ops,
	}).merge(d, b)
}

func (d *Document) SplitOnMarker(name string) (OpTree, OpTree) {
	return SplitOnMarker(d.Ops, name)
}

func (d *Document) Mark(peer, name string, offset int) {
	ops := RemoveMarker(d.Ops, name)
	m := NewSet(name)
	left, right := SplitNew(ops, offset)
	if !left.IsEmpty() {
		if prevMarker, ok := left.PeekLast().(*MarkerOp); ok {
			d.Ops = left.RemoveLast().AddLast(&MarkerOp{prevMarker.Names.Union(m)}).Concat(right)
			return
		}
	}
	d.Ops = left.AddLast(&MarkerOp{m}).Concat(right)
}

// append edits that restore the original document
func (d *Document) ReverseEdits() []Replacement {
	edits := make([]Replacement, 0, 8)
	var repl Replacement
	offset := d.Ops.Measure().NewLen
	d.Ops.EachReverse(func(op Operation) bool {
		switch op := op.(type) {
		case *SkipOp:
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
		case *SkipOp:
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

func (d *Document) Simplify() {
	ops := d.Ops.ToSlice()
	if len(ops) < 2 {
		return
	}
	processed := ops[:1] // start with the first item
	next := ops[1:]
	eat := false
	for len(processed) > 1 || len(next) > 0 {
		if eat && len(next) == 0 {
			break
		} else if eat || len(processed) == 1 {
			processed = append(processed, next[0])
			next = next[1:]
			eat = false
		}
		cur := processed[len(processed)-1]
		prev := processed[len(processed)-2]
		switch op := cur.(type) {
		case *RetainOp:
			if prevRet, ok := prev.(*RetainOp); ok {
				// absorb the retain into the previous one
				processed = processed[:len(processed)-1]
				processed[len(processed)-1] = &RetainOp{prevRet.Text + op.Text}
				continue
			}
		case *InsertOp:
			if prevSkip, ok := prev.(*SkipOp); ok {
				smaller := len(op.Text)
				if len(prevSkip.Text) < smaller {
					smaller = len(prevSkip.Text)
				}
				text := op.Text[0:smaller]
				if strings.HasPrefix(prevSkip.Text, text) {
					// replace the skip with a retain
					processed[len(processed)-2] = &RetainOp{text}
					if len(prevSkip.Text) > smaller {
						processed[len(processed)-1] = &SkipOp{prevSkip.Text[smaller:]}
					} else if len(op.Text) > smaller {
						processed[len(processed)-1] = &InsertOp{op.Peer, op.Text[smaller:]}
					} else {
						processed = processed[:len(processed)-1]
					}
					continue
				}
			}
		}
		eat = true
	}
	d.Ops = newOpTree(processed...)
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
