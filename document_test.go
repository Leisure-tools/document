package document

import (
	"fmt"
	"os"
	"runtime/debug"
	"strings"
	"testing"
)

func replace(t *testing.T, tree *Document, id string, offset, start, length int, text string) {
	str := tree.String()
	tree.Replace(id, offset, start, length, text)
	expect := fmt.Sprintf("%s%s%s", str[0:start], text, str[start+length:])
	if tree.String() != expect {
		failWith(t, fmt.Sprintf("Bad tree '%s', expected '%s'\n", tree.String(), expect))
	}
}

func testEqual(t *testing.T, actual any, expected any, msg string) {
	failIfNot(t, actual == expected, fmt.Sprintf("%s: expected <%v> but got <%v>", msg, expected, actual))
}

func failIfNot(t *testing.T, cond bool, msg string) {
	if !cond {
		failWith(t, msg)
	}
}

func failIfErrNow(t *testing.T, err any) {
	if err != nil {
		failWith(t, err)
	}
}

func failWith(t *testing.T, msg any) {
	t.Log(msg)
	fmt.Fprintln(os.Stderr, msg)
	debug.PrintStack()
	t.FailNow()
}

func TestConcat(t *testing.T) {
	d1 := NewDocument("aaa")
	d1.Replace("peer", 0, 2, 1, "")
	d2 := NewDocument("aa")
	d2.Replace("peer", 0, 1, 1, "")
	d1.Ops.Concat(d2.Ops).ToSlice()
}

func TestDoc(t *testing.T) {
	doc := NewDocument("aaaaa")
	replace(t, doc, "peer", 0, 0, 0, "hello")
	replace(t, doc, "peer", 5, 1, 2, "d")
	doc = NewDocument("aaaaa")
	replace(t, doc, "peer", 0, 3, 1, "hello")
	replace(t, doc, "peer", 5, 2, 2, "")
	replace(t, doc, "peer", 5, 0, 0, "bbb")
}

const doc1 = `line one
line two
line three`

const docMerged = `line ONE
line TWO
line three
line four
line five`

func index(str string, line, col int) int {
	i := 0
	for line > 0 {
		index := strings.IndexByte(str, '\n') + 1
		i += index
		str = str[index:]
		line--
	}
	return i + col
}

func docONE(t *testing.T, peer string) *Document {
	doc := NewDocument(doc1)
	replace(t, doc, peer, 0, index(doc1, 0, 5), 3, "ONE")
	replace(t, doc, peer, 3, index(doc1, 2, 10), 0, "\nline four")
	return doc
}

func docTWO(t *testing.T, peer string) *Document {
	doc := NewDocument(doc1)
	replace(t, doc, peer, 0, index(doc1, 1, 5), 3, "TWO")
	replace(t, doc, peer, 3, index(doc1, 2, 10), 0, "\nline five")
	return doc
}

func docs(t *testing.T) (*Document, *Document) {
	return docONE(t, "peer1"), docTWO(t, "peer2")
}

func replaceAll(t *testing.T, doc *Document, id string, edits []Replacement, expected string) {
	offset := 0
	for _, r := range edits {
		replace(t, doc, id, offset, r.Offset, r.Length, r.Text)
		offset += r.Length
	}
	testEqual(t, doc.String(), expected, "unsuccessful reversal")
}

var bools = []bool{}

func changes(d *Document) {
	fmt.Println(d.Changes(""))
}

func ops(d *Document) {
	fmt.Println(d.OpString(true))
}

func toSlice(d *Document) []Operation {
	return d.Ops.ToSlice()
}

func TestMerge(t *testing.T) {
	a, b := docs(t)
	a.Merge(b)
	testEqual(t, a.String(), docMerged, "unsuccessful merge")
	replaceAll(t, a.Freeze(), "peer1", a.ReverseEdits(), doc1)
	backForward := a.Freeze()
	edits := a.ReverseEdits()
	backForward.Apply("peer1", 0, edits)
	backForward.Apply("peer1", Width(edits), a.Edits())
	testEqual(t, backForward.String(), a.String(), "backForward is wrong")
	backForward.Simplify()
	testEqual(t, len(backForward.Edits()), 0, "extra edits in backForward document")
	a, b = docs(t)
	b.Merge(a)
	testEqual(t, b.String(), docMerged, "unsuccessful merge")
	replaceAll(t, b.Freeze(), "peer1", b.ReverseEdits(), doc1)
	// uncomment these to make the functions availble while debugging
	//changes(a)
	//ops(a)
	//fmt.Println(toSlice(a))
}
