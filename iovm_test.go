package iovm

import (
	"fmt"
	"strings"
	"sync"
	"testing"
	"time"

	"zappem.net/pub/io/gpio"
)

type datum struct {
	mu     sync.Mutex
	value  uint64
	setter <-chan bool
}

func TestEdgeCases(t *testing.T) {
	var ex *Executable
	if lab := ex.Label(1); lab != "<bad[1]: nil executable for index=1>" {
		t.Fatalf("empty executable label is bad: %q", lab)
	}
	if max, _, _ := ex.Latency(); max != 0 {
		t.Fatalf("empty executable latency non zero: %v", max)
	}
	ex = &Executable{}
	if lab := ex.Label(2); lab != "<BIT[2]>" {
		t.Fatalf("unexpected label for bad index: %q", lab)
	}
	if lab := ex.Label(192); lab != "<bad[192]: getting index=192 outside range [0,64)>" {
		t.Fatalf("unexpected label for bad index: %q", lab)
	}
	if on, err := ex.Get(192); err == nil {
		t.Fatalf("got invalid executable index flag 192=%v", on)
	}
	if err := ex.Set(192, true); err == nil {
		t.Fatal("set invalid executable index flag 192")
	}
	var s *State
	if got := s.String(); got != "<nil>" {
		t.Fatalf("empty state non <nil>: %q", got)
	}
	s = &State{}
	if s.String() != "?0" {
		t.Fatalf("bad state not \"?0\": got=%s", s)
	}
	if err := confirmNumber(false, s); err == nil {
		t.Fatalf("non-number confirmed number?")
	}
	s.Number = &self{}
	if err := confirmNumber(true, s); err == nil {
		t.Fatalf("const-number confirmed valid lvalue?")
	}
	var me self
	if _, err := me.SetHold(1); err == nil {
		t.Fatal("SetHold of self constant worked?")
	}
	c := Code{}
	if c.String() != "Invalid(0)" {
		t.Fatalf("bad code is not \"Invalid(0)\": %v", c)
	}
	defer func() {
		if res := recover(); res == nil {
			t.Errorf("bad code should panic but didn't")
		}
	}()
	Build("ladder")
}

func TestBits(t *testing.T) {
	ex := &Executable{Name: "bit"}
	ex.Ops = Build(
		Raise(Bit(ex, 0)),
		JumpFalse(Bit(ex, 0), 1),
		Or(Bit(ex, 2), Bit(ex, 0), Bit(ex, 1)),
		JumpTrue(Bit(ex, 2), 1),
		Jump(2),
		[]Code{
			And(Bit(ex, 3), Bit(ex, 0), Bit(ex, 2)),
			Xor(Bit(ex, 4), Bit(ex, 0), Bit(ex, 1)),
		},
		Copy(Bit(ex, 5), Bit(ex, 4)),
	)

	// Validate that this disassembles as expected.
	{
		want := []string{
			"<bit[0]> = true",
			"if !<bit[0]> { jump +1 }",
			"<bit[2]> = <bit[0]> || <bit[1]>",
			"if <bit[2]> { jump +1 }",
			"jump +2",
			"<bit[3]> = <bit[0]> && <bit[2]>",
			"<bit[4]> = <bit[0]> ^^ <bit[1]>",
			"<bit[5]> = <bit[4]>",
		}
		for i := 0; i < len(ex.Ops); i++ {
			line := ex.Ops[i].String()
			if i >= len(want) || line != want[i] {
				t.Errorf("unexpected [%2d]: %s", i, line)
			}
		}
	}

	if on, err := ex.Get(3); err != nil {
		t.Errorf("un-run value of <bit[3]> is an error: %v", err)
	} else if on {
		t.Error("un-run value of <bit[3]> is true, want=false")
	}
	if err := ex.Run(time.Now()); err != nil {
		t.Fatalf("failed to run %v: %v", ex, err)
	}
	if on, err := ex.Get(3); err != nil {
		t.Errorf("run value of <bit[3]> is an error: %v", err)
	} else if !on {
		t.Error("run value of <bit[3]> is false, want=true")
	}
	if on, err := ex.Get(5); err != nil {
		t.Errorf("run value of <bit[5]> is an error: %v", err)
	} else if !on {
		t.Error("run value of <bit[5]> is false, want=true")
	}
}

func TestMilestone1(t *testing.T) {
	ex := &Executable{}
	ex.Ops = Build(
		Xor(Bit(ex, 27), Bit(ex, 27), Bit(ex, 17)),
		Not(Bit(ex, 17), Bit(ex, 17)),
	)

	max, ave, sigma := ex.Latency()
	if max != ave || ave != sigma {
		t.Fatalf("bad latencies for never run executable: %v %v %v", max, ave, sigma)
	}

	if err := ex.Run(time.Now()); err != nil {
		t.Fatalf("first run of milestone 1 code failed: %v", err)
	}
	if want := uint64(1 << 17); ex.value != want {
		t.Fatalf("got:%016x want:%016x", ex.value, want)
	}
	if err := ex.Run(time.Now()); err != nil {
		t.Fatalf("second run of milestone 1 code failed: %v", err)
	}
	if want := uint64(1 << 27); ex.value != want {
		t.Fatalf("got:%016x want:%016x", ex.value, want)
	}
	if err := ex.Run(time.Now()); err != nil {
		t.Fatalf("third run of milestone 1 code failed: %v", err)
	}
	if want := uint64(1<<27) | uint64(1<<17); ex.value != want {
		t.Fatalf("got:%016x want:%016x", ex.value, want)
	}
	max, ave, sigma = ex.Latency()
	t.Logf("stats for milestone 1: latency = %v +/- %v (max = %v)", ave, sigma, max)
	if max < ave {
		t.Fatalf("max=%v < ave=%v is invalid", max, ave)
	}
}

func TestMilestone2(t *testing.T) {
	ex := &Executable{}
	ex.Ops = Build(
		Xor(Bit(ex, 27), Bit(ex, 27), Bit(ex, 17)),
		Not(Bit(ex, 17), Bit(ex, 17)),
		JumpTrue(Bit(ex, 17), 2),
		Lower(Bit(ex, 10)),
		Jump(1),
		Raise(Bit(ex, 10)),
	)
	max, ave, sigma := ex.Latency()
	if max != ave || ave != sigma {
		t.Fatalf("bad latencies for never run executable: %v %v %v", max, ave, sigma)
	}

	if err := ex.Run(time.Now()); err != nil {
		t.Fatalf("first run of milestone 1 code failed: %v", err)
	}
	if want := uint64(1<<17) | uint64(1<<10); ex.value != want {
		t.Fatalf("got:%016x want:%016x", ex.value, want)
	}
	if err := ex.Run(time.Now()); err != nil {
		t.Fatalf("second run of milestone 1 code failed: %v", err)
	}
	if want := uint64(1 << 27); ex.value != want {
		t.Fatalf("got:%016x want:%016x", ex.value, want)
	}
	if err := ex.Run(time.Now()); err != nil {
		t.Fatalf("third run of milestone 1 code failed: %v", err)
	}
	if want := uint64(1<<27) | uint64(1<<17) | uint64(1<<10); ex.value != want {
		t.Fatalf("got:%016x want:%016x", ex.value, want)
	}
	max, ave, sigma = ex.Latency()
	t.Logf("stats for milestone 1: latency = %v +/- %v (max = %v)", ave, sigma, max)
	if max < ave {
		t.Fatalf("max=%v < ave=%v is invalid", max, ave)
	}
}

type Ins struct {
	Time   time.Time
	Exec   string
	Line   int
	Before bool
}

type foo struct {
	mu            sync.Mutex
	masks, values []uint64
	nows          []time.Time
	tr            []Ins
	t             *testing.T
}

func (f *foo) Sample(mask, value uint64) {
	f.mu.Lock()
	defer f.mu.Unlock()
	if n := len(f.masks) - 1; n >= 0 && value == f.values[n] && mask == f.masks[n] {
		return
	}
	f.nows = append(f.nows, time.Now())
	f.masks = append(f.masks, mask)
	f.values = append(f.values, value)
}

func (f *foo) Edge(ex *Executable, line int, before bool) {
	now := time.Now()
	f.mu.Lock()
	defer f.mu.Unlock()
	f.tr = append(f.tr, Ins{Time: now, Exec: ex.Name, Line: line, Before: before})
}

// Milestone3 is IO tracing with concurrency.
func TestMilestone3(t *testing.T) {
	ex1 := &Executable{Name: "ex1"}
	ex2 := &Executable{Name: "     ex2"}

	builder := func(ex *Executable) []Code {
		return Build(
			Unless(Bit(ex, 1), []Code{ // jump if ex[1] is true, otherwise set it to true
				Not(Bit(ex, 0), Bit(ex, 1)), // should set ex[0] to false.
				Raise(Bit(ex, 2)),           // this should only be raised while ex[1] is true
				Lower(Bit(ex, 2)),           // this should only be lowered while ex[1] is true
				Not(Bit(ex, 1), Bit(ex, 1)), // should set ex[1] to false.
			}),
			Not(Bit(ex, 0), Bit(ex, 1)), // can set ex[0] to true or false.
		)
	}

	tr := &foo{t: t}
	ex1.SetTracer(tr)
	ex1.SetProfiler(tr)
	ex2.SetProfiler(tr)

	ex1.Ops = builder(ex1)
	ex2.Ops = builder(ex1)

	// Validate that this disassembles as expected.
	{
		want := []string{
			"if <ex1[1]> { jump +4 } else { <ex1[1]> = true }",
			"<ex1[0]> = !<ex1[1]>",
			"<ex1[2]> = true",
			"<ex1[2]> = false",
			"<ex1[1]> = !<ex1[1]>",
			"<ex1[0]> = !<ex1[1]>",
		}
		for i := 0; i < len(ex1.Ops); i++ {
			line := ex1.Ops[i].String()
			if i >= len(want) || line != want[i] {
				t.Errorf("unexpected [%2d]: %s", i, line)
			}
		}
	}

	ch := make(chan bool, 10)
	var wg sync.WaitGroup
	wg.Add(2)
	go func() {
		defer wg.Done()
		n := 0
		for <-ch {
			n++
			if err := ex1.Run(time.Now()); err != nil {
				t.Fatalf("ex1 failed: %v", err)
			}
		}
		t.Logf("ex1 ran %d times", n)
	}()
	go func() {
		defer wg.Done()
		n := 0
		for <-ch {
			n++
			if err := ex2.Run(time.Now()); err != nil {
				t.Fatalf("ex1 failed: %v", err)
			}
		}
		t.Logf("ex2 ran %d times", n)
	}()
	for i := 0; i < 100; i++ {
		ch <- true
	}
	close(ch)
	wg.Wait()

	// Test the constraint on ex[2] vs ex[1] and confirm all bits
	// are changed.
	var bit0set, bit1set, bit2set, bit0unset, bit1unset, bit2unset bool
	for i := 0; i < len(tr.values); i++ {
		x := tr.values[i]
		if x&4 != 0 && x&2 == 0 {
			for j := 0; j < len(tr.tr); j++ {
				in := tr.tr[j]
				if in.Time.After(tr.nows[i]) {
					break
				}
				t.Logf("%-60v %q:%d %v", in.Time, in.Exec, in.Line, in.Before)
			}
			for j := i - 10; j < len(tr.values) && j <= i+2; j++ {
				if j < 0 {
					continue
				}
				t.Logf("%-60v %08b", tr.nows[i], tr.values[j])
			}
			t.Fatalf("illegal state found @ %v", tr.nows[i])
		}
		bit0set = bit0set || x&1 != 0
		bit0unset = bit0unset || x&1 == 0
		bit1set = bit1set || x&2 != 0
		bit1unset = bit1unset || x&2 == 0
		bit2set = bit2set || x&4 != 0
		bit2unset = bit2unset || x&4 == 0
	}
	if !(bit0set && bit0unset && bit1set && bit1unset && bit2set && bit2unset) {
		t.Errorf("set/unset of bit0=%v/%v bit1=%v/%v bit2=%v/%v", bit0set, bit0unset, bit1set, bit1unset, bit2set, bit2unset)
	}

	max1, av1, er1 := ex1.Latency()
	if max1 < av1 || max1 < er1 {
		t.Errorf("ex1 %v+/-%v (max %v)", av1, er1, max1)
	}
	max2, av2, er2 := ex2.Latency()
	if max2 < av2 || max2 < er2 {
		t.Errorf("ex2 %v+/-%v (max %v)", av2, er2, max2)
	}
}

func TestMath1(t *testing.T) {
	ex1 := &Executable{Name: "ex1"}
	n := gpio.NewVector(5)
	ex1.Ops = Build(
		Copy(Value(n, 1), Int(4)),
		JumpGEq(Int(4), Value(n, 1), 2),
		Add(Value(n, 1), Value(n, 1), Value(n, 1)),
		Copy(Value(n, 0), Int(2)),
		Sub(Value(n, 2), Value(n, 1), Value(n, 0)),
		JumpGT(Value(n, 2), Value(n, 0), 1),
		Copy(Value(n, 3), Value(n, 0)),
		JumpNEq(Value(n, 3), Value(n, 0), 1),
		Copy(Value(n, 4), Value(n, 0)),
		JumpEq(Value(n, 3), Value(n, 4), 1),
		Copy(Value(n, 1), Value(n, 3)),
	)

	// Validate that this disassembles as expected.
	{
		want := []string{
			"<VECTOR[1]> = 4",
			"if <VECTOR[1]> < 4 { jump +2 }",
			"<VECTOR[1]> = <VECTOR[1]> + <VECTOR[1]>",
			"<VECTOR[0]> = 2",
			"<VECTOR[2]> = <VECTOR[1]> - <VECTOR[0]>",
			"if <VECTOR[0]> <= <VECTOR[2]> { jump +1 }",
			"<VECTOR[3]> = <VECTOR[0]>",
			"if <VECTOR[3]> != <VECTOR[0]> { jump +1 }",
			"<VECTOR[4]> = <VECTOR[0]>",
			"if <VECTOR[3]> == <VECTOR[4]> { jump +1 }",
			"<VECTOR[1]> = <VECTOR[3]>",
		}
		for i := 0; i < len(ex1.Ops); i++ {
			line := ex1.Ops[i].String()
			if i >= len(want) || line != want[i] {
				t.Errorf("unexpected [%2d]: %s", i, line)
			}
		}
	}

	if err := ex1.Run(time.Now()); err != nil {
		t.Fatalf("failed to run ex1: %v", err)
	}
	for i, x := range []int64{2, 8, 6, 0, 0} {
		if y, err := n.Get(i); err != nil {
			t.Errorf("vector[%d]: %v", i, err)
		} else if x != y {
			t.Errorf("vector[%d]: got=%d want=%d", i, y, x)
		}
	}
	max1, av1, er1 := ex1.Latency()
	if max1 < av1 || max1 < er1 {
		t.Errorf("ex1 %v+/-%v (max %v)", av1, er1, max1)
	}
	t.Logf("stats for Math 1: latency = %v +/- %v (max = %v)", av1, er1, max1)
}

// keep and keep.Edge offer an example of how to trace an
// executable. The tracing isn't that sophisticated, but it should be
// usable for debugging test cases.

type keep struct {
	seen     []string
	lastLine int
}

func (k *keep) Edge(ex *Executable, line int, before bool) {
	lastLine := k.lastLine
	k.lastLine = line
	if !before && line != lastLine+1 {
		if line == len(ex.Ops) {
			k.seen = append(k.seen, "        jump taken to END")
			return
		}
		k.seen = append(k.seen, fmt.Sprintf("      jump taken to %d", line))
		return
	}

	snapshot := func(s *State) string {
		if s.Bank != nil {
			on, _ := s.Bank.Get(s.Index)
			return fmt.Sprintf("%v=%v", s, on)
		}
		if s.Number != nil {
			val, _ := s.Number.Get(s.Index)
			return fmt.Sprintf("%v=%d", s, val)
		}
		return "<?>"
	}

	if before {
		c := ex.Ops[line]
		k.seen = append(k.seen, fmt.Sprintf(">>> %04d: %v", line, c))
		var state []string
		if c.Dest != nil {
			state = append(state, snapshot(c.Dest))
		}
		for _, s := range c.Src {
			state = append(state, snapshot(s))
		}
		if len(state) != 0 {
			k.seen = append(k.seen, fmt.Sprintf("        BEFORE: %s", strings.Join(state, ", ")))
		}
	} else {
		c := ex.Ops[lastLine]
		if c.Dest != nil {
			k.seen = append(k.seen, fmt.Sprintf("        AFTER:  %s", snapshot(c.Dest)))
		}
	}
	if line == len(ex.Ops) {
		k.seen = append(k.seen, "        END")
	}
}

func TestMath2(t *testing.T) {
	ex1 := &Executable{Name: "F"}
	n := gpio.NewVector(3)
	if err := n.Set(0, 100); err != nil {
		t.Fatalf("unable to set n[0] to 100: %v", err)
	}
	ex1.Ops = Build(
		Add(Value(n, 1), Value(n, 1), Int(1)),
		JumpLT(Value(n, 1), Value(n, 0), 1),
		Raise(Bit(ex1, 0)),
	)
	n.SetAlias("R")

	// Validate that this disassembles as expected.
	{
		want := []string{
			"<R[1]> = <R[1]> + 1",
			"if <R[1]> < <R[0]> { jump +1 }",
			"<F[0]> = true",
		}
		for i := 0; i < len(ex1.Ops); i++ {
			line := ex1.Ops[i].String()
			if i >= len(want) || line != want[i] {
				t.Errorf("unexpected [%2d]: %s", i, line)
			}
		}
	}
	for i := 0; i < 102; i++ {
		if err := ex1.Run(time.Now()); err != nil {
			t.Fatalf("failed to run ex1: %v", err)
		}
		if bit, err := ex1.Get(0); err != nil {
			t.Fatalf("iteration %d error: %v", i, err)
		} else if want := i >= 99; bit != want {
			t.Errorf("bad value on iteration %d: got=%v want=%v", i, bit, want)
		}
	}
	max1, av1, er1 := ex1.Latency()
	if max1 < av1 || max1 < er1 {
		t.Errorf("ex1 %v+/-%v (max %v)", av1, er1, max1)
	}
	t.Logf("stats for Math 1: latency = %v +/- %v (max = %v)", av1, er1, max1)

	// Now execute it with profiling enabled.
	n.Set(0, 3)
	n.Set(1, 0)
	ex1.Set(0, false)

	eye := &keep{}
	ex1.SetProfiler(eye)

	for i := 0; i < 5; i++ {
		ex1.Run(time.Now())
	}

	// Validate that this traces as expected.
	{
		want := strings.Split(`>>> 0000: <R[1]> = <R[1]> + 1
        BEFORE: <R[1]>=0, <R[1]>=0, 1=1
        AFTER:  <R[1]>=1
>>> 0001: if <R[1]> < <R[0]> { jump +1 }
        BEFORE: <R[1]>=1, <R[0]>=3
        jump taken to END
>>> 0000: <R[1]> = <R[1]> + 1
        BEFORE: <R[1]>=1, <R[1]>=1, 1=1
        AFTER:  <R[1]>=2
>>> 0001: if <R[1]> < <R[0]> { jump +1 }
        BEFORE: <R[1]>=2, <R[0]>=3
        jump taken to END
>>> 0000: <R[1]> = <R[1]> + 1
        BEFORE: <R[1]>=2, <R[1]>=2, 1=1
        AFTER:  <R[1]>=3
>>> 0001: if <R[1]> < <R[0]> { jump +1 }
        BEFORE: <R[1]>=3, <R[0]>=3
>>> 0002: <F[0]> = true
        BEFORE: <F[0]>=false
        AFTER:  <F[0]>=true
        END
>>> 0000: <R[1]> = <R[1]> + 1
        BEFORE: <R[1]>=3, <R[1]>=3, 1=1
        AFTER:  <R[1]>=4
>>> 0001: if <R[1]> < <R[0]> { jump +1 }
        BEFORE: <R[1]>=4, <R[0]>=3
>>> 0002: <F[0]> = true
        BEFORE: <F[0]>=true
        AFTER:  <F[0]>=true
        END
>>> 0000: <R[1]> = <R[1]> + 1
        BEFORE: <R[1]>=4, <R[1]>=4, 1=1
        AFTER:  <R[1]>=5
>>> 0001: if <R[1]> < <R[0]> { jump +1 }
        BEFORE: <R[1]>=5, <R[0]>=3
>>> 0002: <F[0]> = true
        BEFORE: <F[0]>=true
        AFTER:  <F[0]>=true
        END
`, "\n")
		for i := 0; i < len(eye.seen); i++ {
			line := eye.seen[i]
			if i >= len(want) || line != want[i] {
				t.Errorf("unexpected [%2d]: %s", i, line)
			}
		}
	}
}

func TestIfElseIfNot(t *testing.T) {
	ex := &Executable{Name: "F"}

	ex.Ops = Build(
		IfElse(Bit(ex, 0), []Code{
			Raise(Bit(ex, 1)),
		}, IfNot(Bit(ex, 1), []Code{
			Raise(Bit(ex, 0)),
		})),
	)

	// Validate that this disassembles as expected.
	{
		want := []string{
			"if !<F[0]> { jump +2 }",
			"<F[1]> = true",
			"jump +2",
			"if <F[1]> { jump +1 }",
			"<F[0]> = true",
		}
		for i := 0; i < len(ex.Ops); i++ {
			line := ex.Ops[i].String()
			if i >= len(want) || line != want[i] {
				t.Errorf("unexpected [%2d]: %s", i, line)
			}
		}
	}

	tr := &foo{t: t}
	ex.SetTracer(tr)

	for i := 0; i < 2; i++ {
		if err := ex.Run(time.Now()); err != nil {
			t.Fatalf("run %d failed: %v", i, err)
		}
	}

	masks := []uint64{
		0, // start
		1, // read F[0]
		3, // read F[1]
		3,
		3,
	}
	values := []uint64{
		0,
		0,
		0,
		1, // raise F[0]
		3, // raise F[1]
	}
	for i, v := range tr.values {
		if m := tr.masks[i]; masks[i] != m {
			t.Errorf("%d: bad mask got=%03x want=%03x", i, m, masks[i])
		}
		if values[i] != v {
			t.Errorf("%d: bad mask got=%03x want=%03x", i, v, values[i])
		}
	}
}
