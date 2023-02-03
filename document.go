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

type opTree = ft.FingerTree[opMeasurer, operation, measure]

type Document struct {
	ops opTree
}

type Replacement struct {
	Offset int
	Length int
	Text   string
}

type opMeasurer bool

type operation interface {
	opString(offset int) string
	text() string
	measure() measure
	merge(doc *Document, offset int)
	fmt.Stringer
}

type measure struct {
	oldLen  int
	newLen  int
	markers Set[string]
}

type retainOp struct {
	_text string
}

type deleteOp struct {
	_text string
	// could put a pointer to a "move" operation here if text has moved
}

type insertOp struct {
	peer  string // used for ordering
	_text string
}

type markerOp struct {
	name string
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

func (m Set[T]) copy() Set[T] {
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
	return m.copy().Merge(m2)
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

func (m opMeasurer) Identity() measure {
	return measure{}
}

func (m opMeasurer) Measure(op operation) measure {
	return op.measure()
}

func (m opMeasurer) Sum(a measure, b measure) measure {
	return measure{
		oldLen:  a.oldLen + b.oldLen,
		newLen:  a.newLen + b.newLen,
		markers: a.markers.Union(b.markers),
	}
}

///
/// operations
///

func (r *retainOp) String() string {
	return r._text
}

func (r *retainOp) opString(offset int) string {
	return fmt.Sprintf("retain(%d, '%s')", offset, r._text)
}

func (r *retainOp) text() string {
	return r._text
}

func (r *retainOp) measure() measure {
	return measure{oldLen: len(r._text), newLen: len(r._text)}
}

func (r *retainOp) merge(doc *Document, offset int) {
	// ignore this, it doesn't change the doc
}

func (d *deleteOp) String() string {
	return ""
}

func (d *deleteOp) opString(offset int) string {
	return fmt.Sprintf("delete(%d, %d)", offset, len(d._text))
}

func (d *deleteOp) text() string {
	return d._text
}

func (d *deleteOp) measure() measure {
	return measure{oldLen: len(d._text)}
}

func (d *deleteOp) merge(doc *Document, offset int) {
	left, right := splitOld(doc.ops, offset)
	for {
		if right.IsEmpty() {
			doc.ops = left.AddLast(d)
			return
		}
		switch first := right.PeekFirst().(type) {
		case *deleteOp:
			if len(first._text) >= len(d._text) {
				// same text has already been deleted
				return
			}
			// doc has deleted the first part of this text, continue with rest of delete
			d = &deleteOp{d._text[len(first._text):]}
			left = left.AddLast(first)
			right = right.RemoveFirst()
			// make another pass through the loop
		case *retainOp:
			// remove the retain
			right = right.RemoveFirst()
			if len(first._text) >= len(d._text) {
				// the entire deleted text is still in the doc, add the deletion
				if len(first._text) > len(d._text) {
					// keep any remaining retained text
					right = right.AddFirst(&retainOp{first._text[len(d._text):]})
				}
				doc.ops = left.AddLast(d).Concat(right)
				return
			}
			// the first part of the deletion is still in the doc
			left = left.AddLast(&deleteOp{d._text[:len(first._text)]})
			// continue with rest of delete
			d = &deleteOp{d._text[len(first._text):]}
			// make another pass through the loop
		default:
			// an insert or marker should not be the first right operation
			panic(fmt.Errorf("Invalid operation during merge: %v", first))
		}
	}
}

func (i *insertOp) String() string {
	return i._text
}

func (i *insertOp) opString(offset int) string {
	return fmt.Sprintf("insert[%s](%d, '%s')", i.peer, offset, i._text)
}

func (i *insertOp) text() string {
	return i._text
}

func (i *insertOp) measure() measure {
	return measure{newLen: len(i._text)}
}

func (i *insertOp) merge(doc *Document, offset int) {
	// splitOld returns the first right as a retain or delete
	// push any trailing inserts onto the right
	left, right := shiftInsertsRight(splitOld(doc.ops, offset))
	for {
		if right.IsEmpty() {
			doc.ops = left.AddLast(i)
			return
		}
		switch first := right.PeekFirst().(type) {
		case *insertOp:
			if i.peer < first.peer {
				doc.ops = left.AddLast(i).Concat(right)
				return
			}
			left = left.AddLast(first)
			right = right.RemoveFirst()
			// make another pass through the loop
		case *retainOp:
			doc.ops = left.AddLast(i).Concat(right)
			return
		case *deleteOp:
			left = left.AddLast(first)
			right = right.RemoveFirst()
			// make another pass through the loop
		case *markerOp:
			doc.ops = left.AddLast(i).Concat(right)
			return
		default:
			panic(fmt.Errorf("Illegal operation: %v", first))
		}
	}
}

func (s *markerOp) String() string {
	return ""
}

func (s *markerOp) opString(offset int) string {
	return fmt.Sprintf("marker(%s, %d)", s.name, offset)
}

func (s *markerOp) text() string {
	return ""
}

func (s *markerOp) measure() measure {
	return measure{markers: NewSet(s.name)}
}

func (s *markerOp) merge(doc *Document, offset int) {
	left, right := splitOld(doc.ops, offset)
	for {
		if right.IsEmpty() {
			doc.ops = left.AddLast(s)
			return
		}
		switch first := right.PeekFirst().(type) {
		case *insertOp, *deleteOp:
			left = left.AddLast(first)
			right = right.RemoveFirst()
		case *retainOp, *markerOp:
			doc.ops = left.AddLast(s).Concat(right)
		}
	}
}

///
/// document
///

func newOpTree(ops ...operation) opTree {
	return ft.FromArray[opMeasurer, operation, measure](opMeasurer(true), ops)
}

func newDocument(text ...string) *Document {
	sb := &strings.Builder{}
	var ops opTree
	if len(text) > 0 {
		for _, t := range text {
			fmt.Fprint(sb, t)
		}
		ops = newOpTree(&retainOp{sb.String()})
	} else {
		ops = newOpTree()
	}
	return &Document{
		ops: ops,
	}
}

func (d *Document) Copy() *Document {
	d2 := *d
	return &d2
}

func (d *Document) Freeze() *Document {
	return newDocument(d.String())
}

// string for the new document
func (d *Document) String() string {
	sb := &strings.Builder{}
	for _, item := range d.ops.ToSlice() {
		fmt.Fprint(sb, item)
	}
	return sb.String()
}

// string for the original document
func (d *Document) OriginalString() string {
	sb := &strings.Builder{}
	for _, item := range d.ops.ToSlice() {
		switch op := item.(type) {
		case *deleteOp, *retainOp:
			fmt.Fprint(sb, op.text())
		}
	}
	return sb.String()
}

func (d *Document) opString() string {
	sb := &strings.Builder{}
	pos := 0
	first := true
	for _, item := range d.ops.ToSlice() {
		if first {
			first = false
		} else {
			fmt.Fprint(sb, ", ")
		}
		fmt.Fprint(sb, item.opString(pos))
		pos += item.measure().newLen
	}
	return sb.String()
}

func as[T any](v any) T {
	if tv, ok := v.(T); ok {
		return tv
	}
	panic(fmt.Sprintf("Bad value: %v", v))
}

// split the tree's old text at an offset
func splitOld(tree opTree, offset int) (opTree, opTree) {
	if offset > tree.Measure().oldLen {
		panic(fmt.Errorf("Split point %d is not within doc of length %d", offset, tree.Measure().oldLen))
	}
	left, right := tree.Split(func(m measure) bool {
		return m.oldLen > offset
	})
	splitPoint := offset - left.Measure().oldLen
	if splitPoint > 0 {
		// not a clean break, if the first right element is a retain, it needs to be split
		// otherwise it is a delete and should remain on the right
		switch first := right.PeekFirst().(type) {
		case *retainOp:
			left = left.AddLast(&retainOp{first._text[:splitPoint]})
			right = right.RemoveFirst().AddFirst(&retainOp{first._text[splitPoint:]})
		case *deleteOp:
			// leave it on the right
		default:
			panic(fmt.Errorf("bad value at split point %d: %v", splitPoint, first))
		}
	}
	return left, right
}

// splitNew the tree's new text at an offset
func splitNew(tree opTree, offset int) (opTree, opTree) {
	if offset > tree.Measure().newLen {
		panic(fmt.Errorf("Split point %d is not within doc of length %d", offset, tree.Measure().newLen))
	}
	left, right := tree.Split(func(m measure) bool {
		return m.newLen > offset
	})
	splitPoint := offset - left.Measure().newLen
	if splitPoint > 0 {
		// not a clean break, the first right element is a retain or insert element and needs to be split
		first := right.PeekFirst()
		right = right.RemoveFirst()
		switch first := first.(type) {
		case *retainOp:
			left = left.AddLast(&retainOp{first._text[:splitPoint]})
			right = right.AddFirst(&retainOp{first._text[splitPoint:]})
		case *insertOp:
			left = left.AddLast(&insertOp{first.peer, first._text[:splitPoint]})
			right = right.AddFirst(&insertOp{first.peer, first._text[splitPoint:]})
		default:
			panic(fmt.Errorf("bad value at split point %d: %v", splitPoint, first))
		}
	}
	return left, right
}

func isa[T any](v any) bool {
	_, ok := v.(T)
	return ok
}

// if left ends in inserts and (optionally) markers, shift them to right
func shiftInsertsRight(left opTree, right opTree) (opTree, opTree) {
	l, r := left, right
	found := false
	for !l.IsEmpty() {
		switch op := l.PeekLast().(type) {
		case *markerOp, *insertOp:
			l = l.RemoveLast()
			r = r.AddFirst(op)
			found = found || isa[*insertOp](op)
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
func shiftDeletesRight(left opTree, right opTree) (opTree, opTree) {
	l, r := left, right
	found := false
	for !l.IsEmpty() {
		switch op := l.PeekLast().(type) {
		case *markerOp, *deleteOp:
			l = l.RemoveLast()
			r = r.AddFirst(op)
			found = found || isa[*deleteOp](op)
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
	left, right := splitNew(d.ops, start)
	if length > 0 {
		sb := &strings.Builder{}
		// gather deletes at the end of left, followed by markers
		mid := newOpTree()
		left, mid = shiftDeletesRight(left, mid)
		if !mid.IsEmpty() {
			// there will only be one delete
			del, _ := mid.PeekFirst().(*deleteOp)
			fmt.Fprint(sb, del._text)
			mid = mid.RemoveFirst()
		}
		var del opTree
		del, right = splitNew(right, length)
		del.Each(func(v operation) bool {
			switch o := v.(type) {
			case *retainOp, *deleteOp:
				// coalesce retains and deletes into a single delete
				fmt.Fprint(sb, o.text())
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
			case *deleteOp:
				fmt.Fprint(sb, del._text)
				right = right.RemoveFirst()
			}
		}
		left = left.AddLast(&deleteOp{sb.String()}).Concat(mid)
	}
	if len(str) > 0 {
		right = right.AddFirst(&insertOp{peer, str})
	}
	d.ops = left.Concat(right)
}

// Merge operations from the same ancestor document into this one
func (a *Document) Merge(b *Document) {
	offset := 0
	b.ops.Each(func(op operation) bool {
		op.merge(a, offset)
		offset += op.measure().oldLen
		return true
	})
}

func SplitOnMarker(tree opTree, name string) (opTree, opTree) {
	return tree.Split(func(m measure) bool {
		return m.markers.Has(name)
	})
}

func (d *Document) SplitOnMarker(name string) (opTree, opTree) {
	return SplitOnMarker(d.ops, name)
}

// append edits that restore the original document
func (d *Document) ReverseEdits() []Replacement {
	edits := make([]Replacement, 0, 8)
	docLen := d.ops.Measure().newLen
	d.ops.EachReverse(func(op operation) bool {
		width := op.measure().newLen
		switch op := op.(type) {
		case *deleteOp:
			edits = append(edits, Replacement{Offset: docLen, Length: 0, Text: op._text})
		case *insertOp:
			edits = append(edits, Replacement{Offset: docLen - width, Length: len(op._text), Text: ""})
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
	d.ops.Each(func(op operation) bool {
		switch op := op.(type) {
		case *deleteOp:
			edits = append(edits, Replacement{Offset: offset, Length: len(op._text), Text: ""})
		case *insertOp:
			edits = append(edits, Replacement{Offset: offset, Length: 0, Text: op._text})
		}
		offset += op.measure().newLen
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
	doc := newDocument(peer, str)
	doc.Apply(peer, repl)
	return doc.String()
}
