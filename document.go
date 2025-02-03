package document

import (
	"fmt"
	"sort"
	"strings"

	ft "github.com/leisure-tools/lazyfingertree"
)

///
/// types
///

type Set[T comparable] map[T]bool

type OpTree = ft.FingerTree[OpMeasurer, Operation, Measure]

type Document struct {
	ops       OpTree
	opStrings map[string]string
}

type Replacement struct {
	Offset int    `json:"offset"`
	Length int    `json:"length"`
	Text   string `json:"text"`
}

type OpMeasurer bool

var emptyOpTree = ft.FromArray[OpMeasurer, Operation, Measure](OpMeasurer(true), []Operation{})

// a unique id for an insert or delete
// the parentId of the block and the offset within the concatenation of the replacments
type ReplId struct {
	Owner      string
	ReplOffset int
}

type Operation interface {
	OpString(offset int, verbose bool) string
	GetId() ReplId
	GetText() string
	CopyWith(offset int, text string) Operation
	Measure() Measure
	Merge(m *Merger) bool
	fmt.Stringer
}

type Measure struct {
	Width   int
	Markers Set[string]
}

type DeleteOp struct {
	Id       ReplId // id of the original insert, "" means original text
	Text     string
	Deleters []string
}

type InsertOp struct {
	Id ReplId // ID of the peerParent block, for ordering, "" is original text
	//PrevId     string // the previous text -- could be an insert or a delete
	//PrevOffset int
	//PrevBefore bool // whether or not the previous text lies before this insert
	Text string
}

type Merger struct {
	Swapped              bool
	OpA, OpB             Operation
	Result, TreeA, TreeB ft.FingerTree[OpMeasurer, Operation, Measure]
	BaseEdits            map[string]ft.FingerTree[OpMeasurer, Operation, Measure]
	ReplMap              map[ReplId]Operation
	Shared               Set[string]
	Used                 Set[ReplId]
	Marked               Set[string]
	opStrings            map[string]string
	last                 Operation
	seenA                Operation
	seenB                Operation
}

type MarkerOp struct {
	Names Set[string]
}

///
/// set
///

func NewSet[T comparable](elements ...T) Set[T] {
	l := len(elements)
	if l == 0 {
		l = 8
	}
	result := make(Set[T], l)
	for _, item := range elements {
		result[item] = true
	}
	return result
}

func (s Set[T]) ToSlice() []T {
	items := make([]T, len(s))
	i := 0
	for item := range s {
		items[i] = item
		i += 1
	}
	return items
}

func (s Set[T]) Merge(s2 Set[T]) Set[T] {
	for k, v := range s2 {
		s[k] = v
	}
	return s
}

func (s Set[T]) Copy() Set[T] {
	return Set[T]{}.Merge(s)
}

func (s Set[T]) Union(s2 Set[T]) Set[T] {
	if len(s) == 0 {
		return s2
	} else if len(s2) == 0 {
		return s
	}
	return s.Copy().Merge(s2)
}

func (s Set[T]) Compliment(s2 Set[T]) Set[T] {
	for item := range s2 {
		delete(s, item)
	}
	return s
}

func (s Set[T]) Add(els ...T) Set[T] {
	for _, el := range els {
		s[el] = true
	}
	return s
}

func (s Set[T]) Remove(els ...T) Set[T] {
	for _, el := range els {
		delete(s, el)
	}
	return s
}

func (s Set[T]) Has(el T) bool {
	return s[el]
}

func (s Set[T]) IsEmpty() bool {
	return len(s) == 0
}

func (s Set[T]) String() string {
	sl := s.ToSlice()
	var f func(i, j int) bool
	var strs []string
	sortStrings := false

	switch x := any(sl).(type) {
	case []int:
		f = func(i, j int) bool { return x[i] < x[j] }
	case []int8:
		f = func(i, j int) bool { return x[i] < x[j] }
	case []int16:
		f = func(i, j int) bool { return x[i] < x[j] }
	case []int32:
		f = func(i, j int) bool { return x[i] < x[j] }
	case []int64:
		f = func(i, j int) bool { return x[i] < x[j] }
	case []uint:
		f = func(i, j int) bool { return x[i] < x[j] }
	case []uint8:
		f = func(i, j int) bool { return x[i] < x[j] }
	case []uint16:
		f = func(i, j int) bool { return x[i] < x[j] }
	case []uint32:
		f = func(i, j int) bool { return x[i] < x[j] }
	case []uint64:
		f = func(i, j int) bool { return x[i] < x[j] }
	case []uintptr:
		f = func(i, j int) bool { return x[i] < x[j] }
	case []float32:
		f = func(i, j int) bool { return x[i] < x[j] }
	case []float64:
		f = func(i, j int) bool { return x[i] < x[j] }
	default:
		// defer sorting until after string conversion
		sortStrings = true
	}
	if f != nil {
		sort.Slice(sl, f)
	}
	strs = make([]string, len(sl))
	for i, v := range sl {
		strs[i] = fmt.Sprint(v)
	}
	if sortStrings {
		sort.Strings(strs)
	}
	return fmt.Sprintf("Set[%s]", strings.Join(strs, ", "))
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
		Width:   a.Width + b.Width,
		Markers: a.Markers.Union(b.Markers),
	}
}

///
/// operations
///

func Owner(op Operation) string {
	return op.GetId().Owner
}

func ReplOffset(op Operation) int {
	return op.GetId().ReplOffset
}

func ReplEnd(op Operation) int {
	return op.GetId().ReplOffset + Len(op)
}

func Len(op Operation) int {
	return len(op.GetText())
}

func Overlaps(op1 Operation, op2 Operation) bool {
	return RangesOverlap(op1.GetId().ReplOffset, Len(op1), op2.GetId().ReplOffset, Len(op2))
}

func OverlapsRange(op1 Operation, offset, len int) bool {
	return RangesOverlap(op1.GetId().ReplOffset, Len(op1), offset, len)
}

func RangesOverlap(off1, len1, off2, len2 int) bool {
	return !(off1+len1 < off2 || off2+len2 < off1)
}

func isDelete(op any) bool {
	_, isDel := op.(*DeleteOp)
	return isDel
}

func (d *DeleteOp) String() string {
	return ""
}

func (d *DeleteOp) HasDeleter(del string) bool {
	for _, d := range d.Deleters {
		if d == del {
			return true
		}
	}
	return false
}

func (d *DeleteOp) OpString(offset int, verbose bool) string {
	verboseStr := ""
	if verbose {
		verboseStr = ", " + strings.ReplaceAll(d.Text, "\n", "\\n")
	}
	return fmt.Sprintf("delete[%s%s](%d, %d)", d.Id.Owner, verboseStr, offset, d.Len())
}

func (d *DeleteOp) GetText() string {
	if d == nil {
		return ""
	}
	return d.Text
}

func (d *DeleteOp) GetId() ReplId {
	return d.Id
}

func (d *DeleteOp) Overlaps(offset1, del *DeleteOp) bool {
	return d.OverlapsRange(del.Id.ReplOffset, del.Len())
}

func (d *DeleteOp) OverlapsRange(offset2, len int) bool {
	return !(ReplEnd(d) < offset2 || offset2+len < d.Id.ReplOffset)
}

func (d *DeleteOp) Len() int {
	return len(d.Text)
}

func (d *DeleteOp) Measure() Measure {
	return Measure{}
}

func (d *DeleteOp) Merge(m *Merger) bool {
	m.sliceForMerge()
	if d.Id == m.OpB.GetId() {
		m.sliceB()
		return m.shiftBoth(m.OpA) // sliceForMerged may have changed opA
	}
	return m.shiftA(m.OpA)
}

func (d *DeleteOp) CopyWith(offset int, text string) Operation {
	return &DeleteOp{ReplId{d.Id.Owner, offset}, text, d.Deleters}
}

func (i *InsertOp) String() string {
	return i.Text
}

func (i *InsertOp) GetId() ReplId {
	return i.Id
}

func (i *InsertOp) OpString(offset int, verbose bool) string {
	return fmt.Sprintf("insert[%s, %d](%d, '%s')", i.Id.Owner, i.Id.ReplOffset, offset, i.Text)
}

func (i *InsertOp) GetText() string {
	if i == nil {
		return ""
	}
	return i.Text
}

func (i *InsertOp) Measure() Measure {
	return Measure{Width: len(i.Text)}
}

func (i *InsertOp) Merge(m *Merger) bool {
	if !m.sliceForMerge() {
		if i.Id == m.OpB.GetId() {
			// this should be impossible because of priority
			//panic("Wha?")
			return m.swap()
		}
		return m.shiftA()
	} else if i.Id == m.OpB.GetId() {
		m.sliceB()
		return m.shiftBoth(m.OpB)
	} else if _, bIsIns := m.OpB.(*InsertOp); bIsIns {
		return m.shiftA(m.OpA)
	} else if d, dIsDel := m.OpB.(*DeleteOp); dIsDel && Owner(i) != Owner(d) {
		return m.shiftA(m.OpA)
	}
	return m.swap()
}

func (i *InsertOp) CopyWith(offset int, text string) Operation {
	return &InsertOp{ReplId{i.Id.Owner, offset}, text}
}

func (m *MarkerOp) String() string {
	return ""
}

func (m *MarkerOp) OpString(offset int, verbose bool) string {
	return fmt.Sprintf("marker(%s, %d)", strings.Join(m.Names.ToSlice(), ", "), offset)
}

func (m *MarkerOp) GetText() string {
	return ""
}

func (m *MarkerOp) GetId() ReplId {
	return ReplId{"", 0}
}

func (m *MarkerOp) CopyWith(offset int, text string) Operation {
	return m
}

func (m *MarkerOp) Measure() Measure {
	return Measure{Markers: m.Names}
}

func (opA *MarkerOp) Merge(m *Merger) bool {
	n := opA.Names.Copy()
	mar, isBMarker := m.OpB.(*MarkerOp)
	if isBMarker {
		n.Union(mar.Names)
	}
	n.Compliment(m.Marked)
	if !n.IsEmpty() {
		m.appendOps(&MarkerOp{n})
	}
	m.Marked.Merge(n)
	if isBMarker {
		return m.shiftBoth()
	}
	return m.shiftA()
}

///
/// merger
///

type TextRange struct {
	Offset int
	Length int
}

func RangeFor(op Operation) TextRange {
	return TextRange{op.GetId().ReplOffset, Len(op)}
}

func (r TextRange) Overlaps(op Operation) bool {
	return RangesOverlap(r.Offset, r.Length, op.GetId().ReplOffset, Len(op))
}

func (r TextRange) End() int {
	return r.Offset + r.Length
}

type rangeTree = ft.FingerTree[RangeMeasurer, TextRange, TextRange]

func newRangeTree(offset int, op Operation) rangeTree {
	if op != nil {
		return ft.FromArray[RangeMeasurer, TextRange, TextRange](RangeMeasurer(true), []TextRange{
			RangeFor(op),
		})
	}
	return ft.FromArray[RangeMeasurer, TextRange, TextRange](RangeMeasurer(true), []TextRange{})
}

var emptyRangeTree = newRangeTree(0, nil)

type RangeMeasurer bool

func (m RangeMeasurer) Identity() TextRange {
	return TextRange{0, 0}
}

func (m RangeMeasurer) Measure(r TextRange) TextRange {
	return r
}

func (m RangeMeasurer) Sum(m1, m2 TextRange) TextRange {
	start := m1.Offset
	end := m1.End()
	if m2.Offset < m1.Offset {
		start = m2.Offset
	}
	if m2.End() > m1.End() {
		end = m2.End()
	}
	return TextRange{start, end - start}
}

//// merge all adjacent deletes that have common ids
//func (m *Merger) simplifyDeletes() {
//	for id, dels := range m.Deleted {
//		newDels := emptyDelTree
//		offset := -1
//		text := strings.Builder{}
//		pushDel := func() {
//			if offset != -1 {
//				newDels = newDels.AddLast(&DeleteOp{
//					Id:     id,
//					Offset: offset,
//					Text:   text.String(),
//				})
//				text.Reset()
//			}
//		}
//		dels.Each(func(del Operation) bool {
//			if offset != -1 && offset+text.Len() == del.GetOffset() {
//				text.WriteString(del.GetText())
//				return true
//			}
//			pushDel()
//			offset = del.GetOffset()
//			text.WriteString(del.GetText())
//			return true
//		})
//		pushDel()
//		m.Deleted[id] = newDels
//	}
//}

func isEdit(op Operation) bool {
	_, isMarker := op.(*MarkerOp)
	return !isMarker
}

func getEdits(ops OpTree) map[string]OpTree {
	editMap := make(map[string]OpTree, 8)
	maxLen := make(map[string]int, 8)
	ops.Each(func(op Operation) bool {
		if isEdit(op) {
			owner := Owner(op)
			if maxLen[owner] < ReplEnd(op) {
				maxLen[owner] = ReplEnd(op)
			}
			edits := editMap[owner]
			if edits.IsZero() {
				edits = emptyOpTree
			}
			editMap[owner] = edits.AddLast(op)
		}
		return true
	})
	return editMap
}

type ReplMergeState struct {
	op   Operation
	tree OpTree
}

func (s *ReplMergeState) shift() {
	if s.tree.IsEmpty() {
		s.op = nil
	} else {
		s.op = s.tree.PeekFirst()
		s.tree = s.tree.RemoveFirst()
	}
}

func (s *ReplMergeState) shiftMarks() {
	for !isEdit(s.op) {
		s.shift()
	}
}

func SplitOp(op Operation, split int) (Operation, Operation) {
	splitPoint := split - ReplOffset(op)
	a := op.CopyWith(ReplOffset(op), op.GetText()[:splitPoint])
	b := op.CopyWith(split, op.GetText()[splitPoint:])
	return a, b
}

func replMerge(a, b *ReplMergeState) Operation {
	a.shiftMarks()
	b.shiftMarks()
	if a.op != nil && b.op != nil && ReplEnd(b.op) < ReplEnd(a.op) {
		a, b = b, a
	}
	aOp := a.op
	bOp := b.op
	if a.op != nil {
		a.shift()
	} else {
		b.shift()
		return bOp
	}
	if b.op == nil {
		return aOp
	} else if ReplEnd(aOp) == ReplEnd(bOp) {
		b.shift()
	} else {
		first, second := SplitOp(bOp, ReplEnd(aOp))
		bOp = first
		b.op = second
	}
	if _, aIsDel := aOp.(*DeleteOp); aIsDel {
		return aOp
	}
	return bOp
}

// compute merged edits for an owner
func mergeEdits(current, incoming OpTree) OpTree {
	if current.IsEmpty() {
		return current
	}
	result := emptyOpTree
	sCur := &ReplMergeState{tree: current}
	sCur.shift()
	sInc := &ReplMergeState{tree: incoming}
	sInc.shift()
	for sCur.op != nil {
		result = result.AddLast(replMerge(sCur, sInc))
	}
	return result
}

func (m *Merger) isShared(op Operation) bool {
	return m.Shared[Owner(op)]
}

func (m *Merger) findOverlap(deleted map[string]rangeTree, op Operation) (string, rangeTree, rangeTree) {
	id := op.GetId().Owner
	dels := deleted[id]
	if dels.IsZero() {
		dels = emptyRangeTree
	}
	left, right := dels.Split(func(rng TextRange) bool {
		// find first range overlapping or after this operation
		return rng.Overlaps(op) || ReplEnd(op) < rng.Offset
	})
	return id, left, right
}

func (m *Merger) swap() bool {
	m.OpA, m.TreeA, m.OpB, m.TreeB = m.OpB, m.TreeB, m.OpA, m.TreeA
	m.Swapped = !m.Swapped
	return true
}

func (m *Merger) shiftBoth(newOps ...Operation) bool {
	m.appendOps(newOps...)
	if !m.TreeA.IsEmpty() && !m.TreeB.IsEmpty() {
		m.OpA = m.TreeA.PeekFirst()
		m.TreeA = m.TreeA.RemoveFirst()
		m.OpB = m.TreeB.PeekFirst()
		m.TreeB = m.TreeB.RemoveFirst()
		if Owner(m.OpA) == Owner(m.OpB) {
			if dA, isDelA := m.OpA.(*DeleteOp); isDelA {
				if dB, isDelB := m.OpB.(*DeleteOp); isDelB && dA.Text == dB.Text {
					if len(dA.Deleters) == 0 {
						dA.Deleters = dB.Deleters
					} else if len(dB.Deleters) == 0 {
						dB.Deleters = dA.Deleters
					} else {
						newdels := make([]string, len(dA.Deleters), len(dA.Deleters)+len(dB.Deleters))
						copy(newdels, dA.Deleters)
					outer:
						for _, del := range dB.Deleters {
							for _, cur := range newdels {
								if del == cur {
									continue outer
								}
							}
							newdels = append(newdels, del)
						}
						dA.Deleters = newdels
						dB.Deleters = newdels
					}
				}
			}
		}
		return true
	}
	// one of the trees is empty, so just concat them both
	m.Result = m.Result.Concat(m.TreeA.Concat(m.TreeB))
	return false
}

func (m *Merger) shiftAndSwap() bool {
	result := m.shiftA()
	if result {
		m.swap()
	}
	return result
}

func (m *Merger) shiftA(appends ...Operation) bool {
	m.appendOps(appends...)
	if !m.TreeA.IsEmpty() {
		m.OpA = m.TreeA.PeekFirst()
		m.TreeA = m.TreeA.RemoveFirst()
		return true
	}
	m.appendOps(m.OpB)
	m.Result = m.Result.Concat(m.TreeA.Concat(m.TreeB))
	return false
}

func (m *Merger) sliceB() {
	m.swap()
	m.sliceForMerge()
	m.swap()
}

// returns true if merged is an insert
func (m *Merger) sliceForMerge() bool {
	merged := m.ReplMap[m.OpA.GetId()]
	if merged != nil && Len(merged) < Len(m.OpA) {
		first, second := SplitOp(m.OpA, ReplEnd(merged))
		m.TreeA = m.TreeA.AddFirst(second)
		m.OpA = first
		_, isIns := merged.(*InsertOp)
		return isIns
	}
	return true
}

func contiguous(firstOp, secondOp Operation) bool {
	switch first := firstOp.(type) {
	case *InsertOp:
		if second, isIns := secondOp.(*InsertOp); isIns {
			return Owner(first) == Owner(second) && ReplEnd(first) == ReplOffset(second)
		}
	case *DeleteOp:
		if second, isDel := secondOp.(*DeleteOp); isDel {
			return Owner(first) == Owner(second) && ReplEnd(first) == ReplOffset(second)
		}
	}
	return false
}

// TODO verify ops can never be in used, then remove check below
func (m *Merger) appendOps(ops ...Operation) {
	for _, op := range ops {
		if !m.Used.Has(op.GetId()) {
			if !m.Result.IsEmpty() && contiguous(m.Result.PeekLast(), op) {
				// merge contiguous changes
				prev := m.Result.PeekLast()
				//text := m.opStrings[Owner(prev)][ReplOffset(prev):ReplEnd(op)]
				//text := prev.GetText()[:ReplEnd(op)-ReplOffset(prev)]
				text := prev.GetText() + op.GetText()
				m.Result = m.Result.RemoveLast().AddLast(prev.CopyWith(ReplOffset(prev), text))
			} else {
				m.Result = m.Result.AddLast(op)
			}
			if isEdit(op) {
				m.Used.Add(op.GetId())
			}
		}
	}
}

func (m *Merger) shiftUsed() bool {
	m.swap()
	for m.Used.Has(m.OpA.GetId()) {
		if !m.shiftA() {
			return false
		}
	}
	return true
}

// Merge operations from the same ancestor document into this one
func (m *Merger) merge(b *Document) {
	m.TreeB = b.ops
	for owner, str := range b.opStrings {
		m.opStrings[owner] = str
	}
	incomingEdits := getEdits(b.ops)
	for owner, incoming := range incomingEdits {
		edits := incoming
		if !m.BaseEdits[owner].IsZero() {
			edits = mergeEdits(m.BaseEdits[owner], incoming)
			delete(m.BaseEdits, owner)
			m.Shared.Add(owner)
		}
		edits.Each(func(op Operation) bool {
			m.ReplMap[op.GetId()] = op
			return true
		})
	}
	for _, base := range m.BaseEdits {
		base.Each(func(op Operation) bool {
			m.ReplMap[op.GetId()] = op
			return true
		})
	}
	cont := m.shiftBoth()
	for cont {
		cont = false
		if m.shiftUsed() {
			if m.shiftUsed() {
				if m.hasPriority(m.OpA, m.OpB) || !m.hasPriority(m.OpB, m.OpA) {
					cont = m.OpA.Merge(m)
				} else {
					cont = m.swap()
				}
				m.checkInfinite()
			}
		}
	}
}

func (m *Merger) checkInfinite() {
	if (m.Result.IsEmpty() || m.last == m.Result.PeekLast()) &&
		(m.seenA == m.OpA || m.seenB == m.OpA) {
		panic("Internal error, cannot complete merge!")
	}
	if !m.Result.IsEmpty() {
		m.last = m.Result.PeekLast()
	}
	m.seenA, m.seenB = m.OpA, m.seenA
}

func (m *Merger) hasPriority(a, b Operation) bool {
	_, bIsIns := b.(*InsertOp)
	return !isEdit(a) ||
		!m.isShared(a) && m.isShared(b) ||
		!m.isShared(a) && !m.isShared(b) && Owner(a) < Owner(b) ||
		Owner(a) == Owner(b) && ReplOffset(a) < ReplOffset(b) ||
		bIsIns && m.isDeleted(b)
}

func (m *Merger) isDeleted(op Operation) bool {
	_, isDel := m.ReplMap[op.GetId()].(*DeleteOp)
	return isDel
}

///
/// document
///

func newOpTree(ops ...Operation) OpTree {
	return ft.FromArray[OpMeasurer, Operation, Measure](OpMeasurer(true), ops)
}

func NewDocument(text ...string) *Document {
	if len(text) > 0 {
		sb := &strings.Builder{}
		for _, t := range text {
			sb.WriteString(t)
		}
		return &Document{newOpTree(&InsertOp{Text: sb.String()}), make(map[string]string, 8)}
	}
	return &Document{newOpTree(), make(map[string]string, 8)}
}

func (d *Document) GetOps() OpTree {
	return d.ops
}

func (d *Document) SetOps(newOps OpTree) {
	ops := newOps.ToSlice()
	maxLen := make(map[string]int, 8)
	for _, op := range ops {
		maxLen[Owner(op)] += Len(op)
	}
	stringBytes := make(map[string][]byte, 8)
	for owner, len := range maxLen {
		// don't recompute existing op strings
		if d.opStrings[owner] == "" {
			stringBytes[owner] = make([]byte, 0, len)
		}
	}
	for _, op := range ops {
		owner := Owner(op)
		if Len(op) > 0 && stringBytes[owner] != nil {
			l := len(stringBytes[owner])
			stringBytes[owner] = stringBytes[owner][:l+Len(op)]
			copy(stringBytes[owner][l:], []byte(op.GetText()))
		}
	}
	for owner, bytes := range stringBytes {
		if len(stringBytes[owner]) > 0 {
			d.opStrings[owner] = string(bytes)
		}
	}
	offs := make(map[string]int, 8)
	newOps = emptyOpTree
	for _, op := range ops {
		owner := Owner(op)
		offset := offs[owner]
		switch op.(type) {
		case *InsertOp, *DeleteOp:
			if len(stringBytes[owner]) > 0 {
				newText := d.opStrings[owner][offset : offset+Len(op)]
				newOps = newOps.AddLast(op.CopyWith(offset, newText))
			} else {
				newOps = newOps.AddLast(op)
			}
		default:
			newOps = newOps.AddLast(op)
		}
		offs[Owner(op)] += Len(op)
	}
	d.ops = newOps
}

// Makes a top-level copy of a document since the internals are persistent
func (d *Document) Copy() *Document {
	d2 := *d
	return &d2
}

// A new document based on a document's string with only one insert
func (d *Document) Freeze() *Document {
	return NewDocument(d.String())
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
		case *DeleteOp, *InsertOp:
			if op.GetId().Owner == "" {
				fmt.Fprint(sb, op.GetText())
			}
		}
	}
	return sb.String()
}

func OpString(tree OpTree, verbose bool) string {
	sb := &strings.Builder{}
	pos := 0
	first := true
	for _, item := range tree.ToSlice() {
		if first {
			first = false
		} else {
			fmt.Fprint(sb, ", ")
		}
		fmt.Fprint(sb, item.OpString(pos, verbose))
		pos += item.Measure().Width
	}
	return sb.String()
}

func (d *Document) OpString(verbose bool) string {
	return OpString(d.ops, verbose)
}

func (d *Document) Changes(prefix string) string {
	return Changes(prefix, d.ops)
}

func Changes(prefix string, ops OpTree) string {
	sb := &strings.Builder{}
	for _, op := range ops.ToSlice() {
		switch op := op.(type) {
		case *MarkerOp:
			fmt.Fprintf(sb, "%s> %s\n", prefix, strings.Join(op.Names.ToSlice(), ", "))
		case *DeleteOp:
			printOp(sb, prefix, "-", op.Text, op.Id.Owner, op.Deleters)
		case *InsertOp:
			if op.Id.Owner == "" {
				printOp(sb, prefix, "=", op.Text, op.Id.Owner, nil)
			} else {
				printOp(sb, prefix, "+", op.Text, op.Id.Owner, nil)
			}
		}
	}
	return sb.String()
}

func printOp(sb *strings.Builder, lead, prefix, text, id string, deleters []string) {
	for _, line := range strings.Split(text, "\n") {
		if deleters == nil {
			fmt.Fprintf(sb, "%s%s%s%s [%s]\n", lead, prefix, line, prefix, id)
		} else {
			fmt.Fprintf(sb, "%s%s%s%s [%s]%v\n", lead, prefix, line, prefix, id, deleters)
		}
	}
}

func As[T any](v any) T {
	if tv, ok := v.(T); ok {
		return tv
	}
	panic(fmt.Sprintf("Bad value: %v", v))
}

// SplitNew the tree's new text at an offset
func SplitNew(tree OpTree, offset int) (OpTree, OpTree) {
	if offset > tree.Measure().Width {
		panic(fmt.Errorf("Split point %d is not within doc of length %d", offset, tree.Measure().Width))
	}
	left, right := tree.Split(func(m Measure) bool {
		return m.Width > offset
	})
	splitPoint := offset - left.Measure().Width
	if splitPoint > 0 {
		// not a clean break, the first right element is an insert element and needs to be split
		first := right.PeekFirst()
		right = right.RemoveFirst()
		switch first := first.(type) {
		case *InsertOp:
			firstIns := *first
			firstIns.Text = first.Text[:splitPoint]
			left = left.AddLast(&firstIns)
			secondIns := *first
			secondIns.Id.ReplOffset += splitPoint
			secondIns.Text = first.Text[splitPoint:]
			right = right.AddFirst(&secondIns)
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

//func deleteText(right OpTree, length int, skipText *strings.Builder) OpTree {
//	left := newOpTree()
//	for length > 0 {
//		if right.IsEmpty() {
//			panic("Delete past end of document")
//		}
//		first := right.PeekFirst()
//		right = right.RemoveFirst()
//		switch op := first.(type) {
//		case *InsertOp:
//			l := len(op.Text)
//			if length < l {
//				l = length
//			}
//			length -= l
//			first = &DeleteOp{
//				Id:         op.Id,
//				ReplOffset: op.ReplOffset,
//				Text:       op.Text[:l],
//			}
//			if l < len(op.Text) {
//				left = left.AddLast(first)
//				new := *op
//				new.Text = op.Text[l:]
//				new.ReplOffset += l
//				first = &new
//			}
//		}
//		left = left.AddLast(first)
//	}
//	return left.Concat(right)
//}

//// find the first skip to the left if there is one before the first original text
//func getLeftSkip(t OpTree) (OpTree, *DeleteOp, OpTree) {
//	empty := newOpTree()
//	left := t
//	right := empty
//loop:
//	for !left.IsEmpty() {
//		last := left.PeekLast()
//		left = left.RemoveLast()
//		switch op := last.(type) {
//		case *InsertOp:
//			if op.Id == "" {
//				break loop
//			}
//		case *DeleteOp:
//			return left, op, right
//		}
//		right = right.AddFirst(last)
//	}
//	return t, nil, empty
//}

func RemoveMarker(tree OpTree, name string) OpTree {
	left, right := SplitOnMarker(tree, name)
	if !right.IsEmpty() {
		if m, ok := right.PeekFirst().(*MarkerOp); ok {
			if len(m.Names) == 1 {
				return left.Concat(right.RemoveFirst())
			}
			return left.Concat(right.RemoveFirst().AddFirst(&MarkerOp{m.Names.Copy().Remove(name)}))
		} else {
			panic(fmt.Errorf("Internal document error, split on a marker but right side did not start with a marker"))
		}
	}
	return tree
}

func (d *Document) Replace(peerParent string, replOffset, start, length int, str string) {
	if length == 0 && len(str) == 0 {
		return
	}
	left, right := SplitNew(d.ops, start)
	for length > 0 {
		if right.IsEmpty() {
			panic("Delete past end of document")
		}
		first := right.PeekFirst()
		right = right.RemoveFirst()
		switch op := first.(type) {
		case *DeleteOp, *MarkerOp:
			left = left.AddLast(first)
		case *InsertOp:
			deleters := make([]string, 1, 4)
			deleters[0] = peerParent
			if length > len(op.Text) {
				left = left.AddLast(&DeleteOp{op.Id, op.Text, deleters})
			} else {
				left = left.AddLast(&DeleteOp{op.Id, op.Text[:length], deleters})
			}
			if length < len(op.Text) {
				right = right.AddFirst(&InsertOp{
					ReplId{op.Id.Owner, op.Id.ReplOffset + length},
					op.Text[length:],
				})
			}
			length -= len(op.Text)
		}
	}
	if str != "" {
		left = left.AddLast(&InsertOp{
			ReplId{peerParent, replOffset},
			str,
		})
	}
	d.SetOps(left.Concat(right))
}

func SplitOnMarker(tree OpTree, name string) (OpTree, OpTree) {
	return tree.Split(func(m Measure) bool {
		return m.Markers.Has(name)
	})
}

func (d *Document) NewMerger() *Merger {
	m := &Merger{
		Result:    emptyOpTree,
		TreeA:     d.ops,
		BaseEdits: getEdits(d.ops),
		ReplMap:   make(map[ReplId]Operation, 8),
		Used:      NewSet[ReplId](),
		Shared:    NewSet[string](),
		opStrings: make(map[string]string, len(d.opStrings)),
		Marked:    NewSet[string](),
	}
	for _, ops := range m.BaseEdits {
		ops.Each(func(op Operation) bool {
			m.ReplMap[op.GetId()] = op
			return true
		})
	}
	for owner, str := range d.opStrings {
		m.opStrings[owner] = str
	}
	return m
}

// Merge another version of the original document into this one
func (d *Document) Merge(b *Document) {
	m := d.NewMerger()
	m.merge(b)
	d.SetOps(m.Result)
}

func (d *Document) SplitOnMarker(name string) (OpTree, OpTree) {
	return SplitOnMarker(d.ops, name)
}

func (d *Document) Mark(name string, offset int) {
	ops := RemoveMarker(d.ops, name)
	m := NewSet(name)
	left, right := SplitNew(ops, offset)
	if !left.IsEmpty() {
		if prevMarker, ok := left.PeekLast().(*MarkerOp); ok {
			d.SetOps(left.RemoveLast().AddLast(&MarkerOp{prevMarker.Names.Union(m)}).Concat(right))
			return
		}
	}
	d.SetOps(left.AddLast(&MarkerOp{m}).Concat(right))
}

// append edits that restore the original document
func (d *Document) ReverseEdits() []Replacement {
	edits := make([]Replacement, 0, 8)
	var repl Replacement
	offset := d.ops.Measure().Width
	d.ops.EachReverse(func(op Operation) bool {
		switch op := op.(type) {
		case *DeleteOp:
			if Owner(op) == "" {
				repl.Text = op.Text + repl.Text
			}
		case *InsertOp:
			if op.Id.Owner == "" {
				if repl.Length > 0 || len(repl.Text) > 0 {
					repl.Offset = offset
					edits = append(edits, repl)
					repl.Length = 0
					repl.Text = ""
				}
			} else {
				repl.Length += len(op.Text)
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

// insert <--> delete
// newBase ops are transformed to ""
// "" ops are transformed to oldBase
func (d *Document) Reversed(oldBase, newBase string) *Document {
	tree := emptyOpTree
	d.ops.Each(func(oldOp Operation) bool {
		owner := Owner(oldOp)
		if owner == "" {
			owner = oldBase
		} else if owner == newBase {
			owner = ""
		}
		id := ReplId{owner, ReplOffset(oldOp)}
		switch op := oldOp.(type) {
		case *InsertOp:
			tree = tree.AddLast(&DeleteOp{id, op.Text, nil})
		case *DeleteOp:
			tree = tree.AddLast(&InsertOp{id, op.Text})
		case *MarkerOp:
			tree = tree.AddLast(op)
		}
		return true
	})
	ret := &Document{emptyOpTree, make(map[string]string, 8)}
	ret.SetOps(tree)
	return ret
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
	d.ops.Each(func(op Operation) bool {
		switch op := op.(type) {
		case *DeleteOp:
			if Owner(op) == "" {
				ensureRepl()
				repl.Length += len(op.Text)
			}
		case *InsertOp:
			if op.Id.Owner == "" {
				if hasRepl {
					edits = append(edits, repl)
					hasRepl = false
				}
			} else {
				ensureRepl()
				repl.Text += op.Text
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

// return edits the owner made in this document
func (d *Document) EditsFor(owner string, markers ...string) ([]Replacement, map[string]int) {
	markerSet := NewSet(markers...)
	edits := make([]Replacement, 0, 8)
	hasRepl := false
	var repl Replacement
	offset := 0
	markerPositions := make(map[string]int, len(markers))
	ensureRepl := func() {
		if !hasRepl {
			hasRepl = true
			repl.Offset = offset
			repl.Length = 0
			repl.Text = ""
		}
	}
	addRepl := func() {
		if hasRepl {
			edits = append(edits, repl)
			hasRepl = false
		}
	}
	d.ops.Each(func(op Operation) bool {
		switch op := op.(type) {
		case *DeleteOp:
			//if Owner(op) == owner {
			if op.HasDeleter(owner) {
				ensureRepl()
				repl.Length += len(op.Text)
			}
		case *InsertOp:
			if op.Id.Owner == owner {
				ensureRepl()
				repl.Text += op.Text
			} else {
				addRepl()
			}
			offset += len(op.Text)
		case *MarkerOp:
			for k := range op.Names {
				if markerSet.Has(k) {
					markerPositions[k] = offset
				}
			}
		}
		return true
	})
	if hasRepl {
		edits = append(edits, repl)
	}
	return edits, markerPositions
}

func prevRetain(ops []Operation) *InsertOp {
	for i := len(ops) - 2; i >= 0; i-- {
		if op, isIns := ops[i].(*InsertOp); isIns && Owner(op) == "" {
			return op
		} else if op, isDel := ops[i].(*DeleteOp); isDel && Owner(op) == "" {
			return nil
		}
	}
	return nil
}

func previousSkip(ins *InsertOp, ops []Operation) (int, *DeleteOp) {
	for i := len(ops) - 2; i >= 0; i-- {
		if op, isIns := ops[i].(*InsertOp); isIns && Owner(op) == Owner(ins) {
			return -1, nil
		} else if op, isDel := ops[i].(*DeleteOp); isDel && op.Text == ins.Text {
			return i, op
		}
	}
	return -1, nil
}

// remove non-source deletes
func (d *Document) Simplify() {
	ops := d.ops.ToSlice()
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
		case *InsertOp:
			if Owner(op) == "" {
				if prevRet, ok := prev.(*InsertOp); ok && Owner(prevRet) == "" {
					// absorb retain into the previous one
					processed = processed[:len(processed)-1]
					processed[len(processed)-1] = &InsertOp{Text: prevRet.Text + op.Text}
					continue
				}
				break
			}
			iDel, prevSkip := previousSkip(op, processed)
			if prevSkip != nil {
				smaller := len(op.Text)
				if len(prevSkip.Text) < smaller {
					smaller = len(prevSkip.Text)
				}
				text := op.Text[0:smaller]
				if strings.HasPrefix(prevSkip.Text, text) {
					// replace the skip with a retain
					processed[iDel] = &InsertOp{Text: text}
					if len(prevSkip.Text) > smaller {
						processed[len(processed)-1] = &DeleteOp{Text: prevSkip.Text[smaller:], Deleters: prevSkip.Deleters}
					} else if len(op.Text) > smaller {
						processed[len(processed)-1] = &InsertOp{op.Id, op.Text[smaller:]}
					} else {
						processed = processed[:len(processed)-1]
					}
					continue
				}
			}
		}
		eat = true
	}
	d.SetOps(removeTrivialDeletes(newOpTree(processed...)))
	//d.SetOps(newOpTree(processed...))
}

func removeTrivialDeletes(ops OpTree) OpTree {
	replMap := getEdits(ops)
	allDeletes := NewSet[string]()
	for owner, ops := range replMap {
		if owner != "" && ops.Measure().Width == 0 {
			allDeletes.Add(owner)
		}
	}
	newOps := emptyOpTree
	ops.Each(func(op Operation) bool {
		if !isEdit(op) || !allDeletes.Has(Owner(op)) {
			newOps = newOps.AddLast(op)
		}
		return true
	})
	return newOps
}

func (d *Document) Apply(id string, offset int, edits []Replacement) {
	for _, repl := range edits {
		d.Replace(id, offset, repl.Offset, repl.Length, repl.Text)
		offset += repl.Length
	}
	delete(d.opStrings, id)
	d.SetOps(d.ops)
}

func Apply(id, str string, offset int, repl []Replacement) string {
	doc := NewDocument(id, str)
	doc.Apply(id, offset, repl)
	return doc.String()
}

func Width(repl []Replacement) int {
	width := 0
	for _, r := range repl {
		width += len(r.Text)
	}
	return width
}

///
/// diag
///

func LenTree(tree OpTree) int {
	l := 0
	tree.Each(func(op Operation) bool {
		l++
		return true
	})
	return l
}
