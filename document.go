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

type opTree = ft.FingerTree[OpMeasurer, Operation, Measure]

type Document struct {
	Ops opTree
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
	Merge(doc *Document, offset int)
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

type insertOp struct {
	Peer string // used for ordering
	Text string
}

type markerOp struct {
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
	return fmt.Sprintf("retain(%d, '%s')", offset, r.Text)
}

func (r *RetainOp) GetText() string {
	return r.Text
}

func (r *RetainOp) Measure() Measure {
	return Measure{OldLen: len(r.Text), NewLen: len(r.Text)}
}

func (r *RetainOp) Merge(doc *Document, offset int) {
	// ignore this, it doesn't change the doc
}

func (d *DeleteOp) String() string {
	return ""
}

func (d *DeleteOp) OpString(offset int) string {
	return fmt.Sprintf("delete(%d, %d)", offset, len(d.Text))
}

func (d *DeleteOp) GetText() string {
	return d.Text
}

func (d *DeleteOp) Measure() Measure {
	return Measure{OldLen: len(d.Text)}
}

func (d *DeleteOp) Merge(doc *Document, offset int) {
	left, right := SplitOld(doc.Ops, offset)
	for {
		if right.IsEmpty() {
			doc.Ops = left.AddLast(d)
			return
		}
		switch first := right.PeekFirst().(type) {
		case *DeleteOp:
			if len(first.Text) >= len(d.Text) {
				// same text has already been deleted
				return
			}
			// doc has deleted the first part of this text, continue with rest of delete
			d = &DeleteOp{d.Text[len(first.Text):]}
			left = left.AddLast(first)
			right = right.RemoveFirst()
			// make another pass through the loop
		case *RetainOp:
			// remove the retain
			right = right.RemoveFirst()
			if len(first.Text) >= len(d.Text) {
				// the entire deleted text is still in the doc, add the deletion
				if len(first.Text) > len(d.Text) {
					// keep any remaining retained text
					right = right.AddFirst(&RetainOp{first.Text[len(d.Text):]})
				}
				doc.Ops = left.AddLast(d).Concat(right)
				return
			}
			// the first part of the deletion is still in the doc
			left = left.AddLast(&DeleteOp{d.Text[:len(first.Text)]})
			// continue with rest of delete
			d = &DeleteOp{d.Text[len(first.Text):]}
			// make another pass through the loop
		default:
			// an insert or marker should not be the first right operation
			panic(fmt.Errorf("Invalid operation during merge: %v", first))
		}
	}
}

func (i *insertOp) String() string {
	return i.Text
}

func (i *insertOp) OpString(offset int) string {
	return fmt.Sprintf("insert[%s](%d, '%s')", i.Peer, offset, i.Text)
}

func (i *insertOp) GetText() string {
	return i.Text
}

func (i *insertOp) Measure() Measure {
	return Measure{NewLen: len(i.Text)}
}

func (i *insertOp) Merge(doc *Document, offset int) {
	// splitOld returns the first right as a retain or delete
	// push any trailing inserts onto the right
	left, right := ShiftInsertsRight(SplitOld(doc.Ops, offset))
	for {
		if right.IsEmpty() {
			doc.Ops = left.AddLast(i)
			return
		}
		switch first := right.PeekFirst().(type) {
		case *insertOp:
			if i.Peer < first.Peer {
				doc.Ops = left.AddLast(i).Concat(right)
				return
			}
			left = left.AddLast(first)
			right = right.RemoveFirst()
			// make another pass through the loop
		case *RetainOp:
			doc.Ops = left.AddLast(i).Concat(right)
			return
		case *DeleteOp:
			left = left.AddLast(first)
			right = right.RemoveFirst()
			// make another pass through the loop
		case *markerOp:
			doc.Ops = left.AddLast(i).Concat(right)
			return
		default:
			panic(fmt.Errorf("Illegal operation: %v", first))
		}
	}
}

func (s *markerOp) String() string {
	return ""
}

func (s *markerOp) OpString(offset int) string {
	return fmt.Sprintf("marker(%s, %d)", s.Name, offset)
}

func (s *markerOp) GetText() string {
	return ""
}

func (s *markerOp) Measure() Measure {
	return Measure{Markers: NewSet(s.Name)}
}

func (s *markerOp) Merge(doc *Document, offset int) {
	left, right := SplitOld(doc.Ops, offset)
	for {
		if right.IsEmpty() {
			doc.Ops = left.AddLast(s)
			return
		}
		switch first := right.PeekFirst().(type) {
		case *insertOp, *DeleteOp:
			left = left.AddLast(first)
			right = right.RemoveFirst()
		case *RetainOp, *markerOp:
			doc.Ops = left.AddLast(s).Concat(right)
		}
	}
}

///
/// document
///

func newOpTree(ops ...Operation) opTree {
	return ft.FromArray[OpMeasurer, Operation, Measure](OpMeasurer(true), ops)
}

func NewDocument(text ...string) *Document {
	sb := &strings.Builder{}
	var ops opTree
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

func (d *Document) OpString() string {
	sb := &strings.Builder{}
	pos := 0
	first := true
	for _, item := range d.Ops.ToSlice() {
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

func As[T any](v any) T {
	if tv, ok := v.(T); ok {
		return tv
	}
	panic(fmt.Sprintf("Bad value: %v", v))
}

// split the tree's old text at an offset
func SplitOld(tree opTree, offset int) (opTree, opTree) {
	if offset > tree.Measure().OldLen {
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
func SplitNew(tree opTree, offset int) (opTree, opTree) {
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
		case *insertOp:
			left = left.AddLast(&insertOp{first.Peer, first.Text[:splitPoint]})
			right = right.AddFirst(&insertOp{first.Peer, first.Text[splitPoint:]})
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
func ShiftInsertsRight(left opTree, right opTree) (opTree, opTree) {
	l, r := left, right
	found := false
	for !l.IsEmpty() {
		switch op := l.PeekLast().(type) {
		case *markerOp, *insertOp:
			l = l.RemoveLast()
			r = r.AddFirst(op)
			found = found || Isa[*insertOp](op)
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
func ShiftDeletesRight(left opTree, right opTree) (opTree, opTree) {
	l, r := left, right
	found := false
	for !l.IsEmpty() {
		switch op := l.PeekLast().(type) {
		case *markerOp, *DeleteOp:
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

func RemoveMarker(tree opTree, name string) opTree {
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
		var del opTree
		del, right = SplitNew(right, length)
		del.Each(func(v Operation) bool {
			switch o := v.(type) {
			case *RetainOp, *DeleteOp:
				// coalesce retains and deletes into a single delete
				fmt.Fprint(sb, o.GetText())
			case *insertOp:
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
		right = right.AddFirst(&insertOp{peer, str})
	}
	d.Ops = left.Concat(right)
}

// Merge operations from the same ancestor document into this one
func (a *Document) Merge(b *Document) {
	offset := 0
	b.Ops.Each(func(op Operation) bool {
		op.Merge(a, offset)
		offset += op.Measure().OldLen
		return true
	})
}

func SplitOnMarker(tree opTree, name string) (opTree, opTree) {
	return tree.Split(func(m Measure) bool {
		return m.Markers.Has(name)
	})
}

func (d *Document) SplitOnMarker(name string) (opTree, opTree) {
	return SplitOnMarker(d.Ops, name)
}

// append edits that restore the original document
func (d *Document) ReverseEdits() []Replacement {
	edits := make([]Replacement, 0, 8)
	docLen := d.Ops.Measure().NewLen
	d.Ops.EachReverse(func(op Operation) bool {
		width := op.Measure().NewLen
		switch op := op.(type) {
		case *DeleteOp:
			edits = append(edits, Replacement{Offset: docLen, Length: 0, Text: op.Text})
		case *insertOp:
			edits = append(edits, Replacement{Offset: docLen - width, Length: len(op.Text), Text: ""})
		}
		docLen -= width
		return true
	})
	return edits
}

// append Edits that restore the original document
func (d *Document) Edits() []Replacement {
	edits := make([]Replacement, 0, 8)
	offset := 0
	d.Ops.Each(func(op Operation) bool {
		switch op := op.(type) {
		case *DeleteOp:
			edits = append(edits, Replacement{Offset: offset, Length: len(op.Text), Text: ""})
		case *insertOp:
			edits = append(edits, Replacement{Offset: offset, Length: 0, Text: op.Text})
		}
		offset += op.Measure().NewLen
		return true
	})
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
