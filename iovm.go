// Package iovm is a small virtual machine implementation for IO
// operations. This is an attempt to explore close to realtime IO
// execution.
//
// Go offers no realtime guarantees, so it is not realistic to think
// we might be able to achieve this, but we include continuously
// measured execution latency to surface characteristic timing of VM
// executed code sequences so that can be evaluated against the use
// case needs.
//
// The package provides hooks for IO and instruction tracing.
package iovm

import (
	"fmt"
	"math"
	"runtime"
	"sync"
	"time"
)

// Command is the instruction type.
type Command byte

const (
	CmdInvalid Command = iota
	CmdRaise
	CmdLower
	CmdCopy
	CmdNot
	CmdAnd
	CmdOr
	CmdXor
	CmdAdd
	CmdSub
	CmdJump
	CmdJumpTrue
	CmdJumpFalse
	CmdJumpOrRaise
	CmdJumpEq
	CmdJumpNEq
	CmdJumpLT
	CmdJumpLEq
)

// Tracer indicates the API iovm supports for IO tracing. Use
// (*Executable).SetTracer() to enable tracing of the executable's
// internal state.
type Tracer interface {
	// Sample records a sample of masked data.
	Sample(mask, value uint64)
}

// Profiler is used to trace executable instruction completion.
// Combined with the Tracer all Code execution and state changes can
// be monitored. If used, Edge() is called before and after each
// instruction Code is executed.
type Profiler interface {
	Edge(ex *Executable, line int, before bool)
}

// Bank defines a Get/SetHold interface for the executable's internal
// state flags.
type Bank interface {
	// Get reads the value of an indexed signal.
	Get(index int) (bool, error)

	// SetHold sets the indexed signal atomically via the returned
	// channel. One (this index) or many indices may be blocked
	// for setting while the returned channel is open. Canceled
	// writes occur when the channel is closed without being
	// written to.
	SetHold(index int) (chan<- bool, error)

	// Label returns a string label for the specified index.
	Label(index int) string
}

// Number defines a Get/SetHold interface for the executable's numeric
// vector state.
type Number interface {
	// Get reads the value of an indexed value.
	Get(index int) (int64, error)

	// SetHold sets the indexed value atomically via the returned
	// channel. One (this index) or many indices may be blocked
	// for setting while the returned channel is open. Canceled
	// writes occur when the channel is closed without being
	// written to.
	SetHold(index int) (chan<- int64, error)

	// Label returns a string label for the specified index.
	Label(index int) string
}

// State defines a reference to some signal. Typically these are
// internal (such as the Executable's flag values) or external, such
// as GPIO space.
type State struct {
	// Bank holds an indicator of which bank a state item refers
	// to.
	Bank   Bank
	Number Number // if neither Bank or Number are set, index is an absolute value.
	Index  int
}

// String returns the label associated with a State.
func (s *State) String() string {
	if s == nil {
		return "<nil>"
	}
	if s.Bank != nil {
		return s.Bank.Label(s.Index)
	}
	if s.Number != nil {
		return s.Number.Label(s.Index)
	}
	return fmt.Sprintf("?%d", s.Index)
}

// Bit generates a source and/or destination state reference.
func Bit(b Bank, index int) *State {
	return &State{
		Bank:  b,
		Index: index,
	}
}

// Value generates a source and/or destination numeric state reference.
func Value(n Number, index int) *State {
	return &State{
		Number: n,
		Index:  index,
	}
}

// self is a simple read only array where the returned value is the
// index value.
type self struct{}

func (s self) Get(index int) (int64, error) {
	return int64(index), nil
}

func (s self) SetHold(index int) (chan<- int64, error) {
	return nil, fmt.Errorf("number %d is read-only", index)
}

func (s self) Label(index int) string {
	return fmt.Sprint(index)
}

// Int generates a source numeric absolute value reference.
func Int(value int) *State {
	return &State{
		Number: self{},
		Index:  value,
	}
}

// confirmNumber confirms that a State holds a number.
func confirmNumber(asLvalue bool, nums ...*State) error {
	for _, x := range nums {
		if x.Number == nil {
			return fmt.Errorf("state %v non-numeric", x)
		}
		if !asLvalue {
			continue
		}
		switch x.Number.(type) {
		case *self:
			return fmt.Errorf("number %v is not a valid lvalue", x)
		}
	}
	return nil
}

// Code is an atom of programmed code.
type Code struct {
	Cmd  Command
	Src  []*State
	Dest *State
	Step int
}

// Executable holds a compiled executable
type Executable struct {
	mu          sync.Mutex
	setter      chan bool
	mask, value uint64
	tracer      Tracer
	profiler    Profiler
	Name        string
	Ops         []Code
	Line        int
	// MaxTime, SumTime etc allow computation of the latency properties.
	MaxTime           time.Duration
	SumTime, SumTime2 time.Duration
	SumTries          uint
}

// Raise generates code to set a State value to true.
func Raise(res *State) Code {
	return Code{
		Cmd:  CmdRaise,
		Dest: res,
	}
}

// Lower generates code to reset a State value to false.
func Lower(res *State) Code {
	return Code{
		Cmd:  CmdLower,
		Dest: res,
	}
}

// Copy copies the current state of src to res.
func Copy(res, src *State) Code {
	return Code{
		Cmd:  CmdCopy,
		Src:  []*State{src},
		Dest: res,
	}
}

// Not inverts the src and copies that value to res.
func Not(res, src *State) Code {
	return Code{
		Cmd:  CmdNot,
		Src:  []*State{src},
		Dest: res,
	}
}

// And performs a logical AND of two src states into res.
func And(res, src1, src2 *State) Code {
	return Code{
		Cmd:  CmdAnd,
		Dest: res,
		Src:  []*State{src1, src2},
	}
}

// Or performs a logical OR of two src states into res.
func Or(res, src1, src2 *State) Code {
	return Code{
		Cmd:  CmdOr,
		Dest: res,
		Src:  []*State{src1, src2},
	}
}

// Xor performs a logical XOR of two src states into res.
func Xor(res, src1, src2 *State) Code {
	return Code{
		Cmd:  CmdXor,
		Dest: res,
		Src:  []*State{src1, src2},
	}
}

// Add performs a numerical addition of two src states into res.
func Add(res, src1, src2 *State) Code {
	return Code{
		Cmd:  CmdAdd,
		Dest: res,
		Src:  []*State{src1, src2},
	}
}

// Sub performs a numerical subtraction of two src[0]-src[1] states
// into res.
func Sub(res, src1, src2 *State) Code {
	return Code{
		Cmd:  CmdSub,
		Dest: res,
		Src:  []*State{src1, src2},
	}
}

// Jump performs an unconditional jump. The iovm execution model only
// supports relative jumping forwards. Providing a negative value will
// cause a runtime error.
func Jump(step int) Code {
	return Code{
		Cmd:  CmdJump,
		Step: step,
	}
}

// JumpTrue performs a jump if the src State is true. The iovm execution
// model only supports relative jumping forwards. Providing a negative
// value will cause a runtime error.
func JumpTrue(src *State, step int) Code {
	return Code{
		Cmd:  CmdJumpTrue,
		Src:  []*State{src},
		Step: step,
	}
}

// JumpFalse performs a jump if the src State is false. The iovm
// execution model only supports relative jumping forwards. Providing
// a negative value will cause a runtime error.
func JumpFalse(src *State, step int) Code {
	return Code{
		Cmd:  CmdJumpFalse,
		Src:  []*State{src},
		Step: step,
	}
}

// JumpOrRaise performs a jump if the reg State is true. The iovm
// execution model only supports relative jumping forwards. Providing
// a negative value will cause a runtime error. If the res State is
// false, the state is set to true and the jump is not taken. This
// instruction is atomic and can be used to implement mutex
// functionality.
func JumpOrRaise(res *State, step int) Code {
	return Code{
		Cmd:  CmdJumpOrRaise,
		Dest: res,
		Step: step,
	}
}

// JumpEq performs a jump if the a State equals the b State. The iovm
// execution model only supports relative jumping forwards. Providing
// a negative value will cause a runtime error.
func JumpEq(a, b *State, step int) Code {
	return Code{
		Cmd:  CmdJumpEq,
		Src:  []*State{a, b},
		Step: step,
	}
}

// JumpNEq performs a jump if the a State does not equal the b State.
// The iovm execution model only supports relative jumping
// forwards. Providing a negative value will cause a runtime error.
func JumpNEq(a, b *State, step int) Code {
	return Code{
		Cmd:  CmdJumpNEq,
		Src:  []*State{a, b},
		Step: step,
	}
}

// JumpLT performs a jump if the a State is less than the b State.
// The iovm execution model only supports relative jumping
// forwards. Providing a negative value will cause a runtime error.
func JumpLT(a, b *State, step int) Code {
	return Code{
		Cmd:  CmdJumpLT,
		Src:  []*State{a, b},
		Step: step,
	}
}

// JumpLEq performs a jump if the a State is less than or equal to the
// b State.  The iovm execution model only supports relative jumping
// forwards. Providing a negative value will cause a runtime error.
func JumpLEq(a, b *State, step int) Code {
	return Code{
		Cmd:  CmdJumpLEq,
		Src:  []*State{a, b},
		Step: step,
	}
}

// JumpGT performs a jump if the a State is greater than to the b
// State.  The iovm execution model only supports relative jumping
// forwards. Providing a negative value will cause a runtime error.
func JumpGT(a, b *State, step int) Code {
	return JumpLEq(b, a, step)
}

// JumpGEq performs a jump if the a State is greater than or equal to
// the b State.  The iovm execution model only supports relative
// jumping forwards. Providing a negative value will cause a runtime
// error.
func JumpGEq(a, b *State, step int) Code {
	return JumpLT(b, a, step)
}

// Build is used to concatenate code segments. The code values can be
// individual or sequences of []Code. Once built, scratch registers
// are assigned.
func Build(code ...interface{}) []Code {
	var ops []Code
	for i, c := range code {
		switch t := c.(type) {
		default:
			panic(fmt.Sprintf("invalid input[%d]: %v of type (%T)", i, c, t))
		case Code:
			ops = append(ops, c.(Code))
		case []Code:
			ops = append(ops, c.([]Code)...)
		}
	}
	return ops
}

// If executes a block if a is true.
func If(a *State, block []Code) []Code {
	n := len(block)
	return Build(JumpFalse(a, n), block)
}

// IfNot executes a block if a is true.
func IfNot(a *State, block []Code) []Code {
	n := len(block)
	return Build(JumpTrue(a, n), block)
}

// IfElse executes block if a is true, otherwise it executes alt.
func IfElse(a *State, block, alt []Code) []Code {
	n := len(block)
	m := len(alt)
	return Build(
		JumpFalse(a, n+1),
		block,
		Jump(m),
		alt,
	)
}

func (ex *Executable) valid(index int) error {
	if ex == nil {
		return fmt.Errorf("nil executable for index=%d", index)
	}
	if index < 0 || index >= 64 {
		return fmt.Errorf("getting index=%d outside range [0,64)", index)
	}
	return nil
}

// Get loads the indexed state flag of the Executable. Each executable
// has their own Value (64 bits of flags initialized to 0 before first
// Run). Note, this may expand the lazily defined active mask and
// cause the tracer to be invoked with an extended mask sample.
func (ex *Executable) Get(index int) (bool, error) {
	if err := ex.valid(index); err != nil {
		return false, err
	}
	bit := uint64(1) << index
	ex.mu.Lock()
	defer ex.mu.Unlock()
	if ex.mask&bit == 0 {
		ex.mask |= bit
		if ex.tracer != nil {
			ex.tracer.Sample(ex.mask, ex.value)
		}
	}
	return ex.value&bit != 0, nil
}

// SetHold sets the content of a state flag of the Executable. Each
// Executable has their own value (64 bits of flags initialized to 0
// before first Run). SetHold() returns a channel over which the
// caller can actually set the state. The channel should be closed
// quickly to unlock the state again.
func (ex *Executable) SetHold(index int) (chan<- bool, error) {
	if err := ex.valid(index); err != nil {
		return nil, err
	}
	ch := make(chan bool)
	ex.mu.Lock()
	// Before returning we need to be blocking all changes to
	// index state.  This guarantees that any reads of the indexed
	// state are not going to change while the caller knows the
	// state is held.
	for {
		if ex.setter == nil {
			ex.setter = ch
			break
		}
		ex.mu.Unlock()
		runtime.Gosched()
		ex.mu.Lock()
	}
	go func() {
		defer ex.mu.Unlock()
		bit := uint64(1) << index
		for {
			select {
			case on, ok := <-ch:
				if ok {
					oldMask := ex.mask
					ex.mask |= bit
					old := ex.value
					if on != (old&bit != 0) {
						ex.value ^= bit
					}
					if ex.tracer != nil && (old != ex.value || oldMask != ex.mask) {
						ex.tracer.Sample(ex.mask, ex.value)
					}
					// Block until channel closed.
					for ok {
						_, ok = <-ch
					}
				}
				ex.setter = nil
				return
			default:
				ex.mu.Unlock()
				runtime.Gosched()
				ex.mu.Lock()
			}
		}
	}()
	return ch, nil
}

// Set is a serialized version of SetHold(). Once it returns, the
// value has been set to on.
func (ex *Executable) Set(index int, on bool) error {
	ch, err := ex.SetHold(index)
	if err != nil {
		return err
	}
	ch <- on
	close(ch)
	return nil
}

// Label labels an internal flag index reference.
func (ex *Executable) Label(index int) string {
	if err := ex.valid(index); err != nil {
		return fmt.Sprintf("<bad[%d]: %v>", index, err)
	}
	if ex.Name != "" {
		return fmt.Sprintf("<%s[%d]>", ex.Name, index)
	}
	return fmt.Sprintf("<BIT[%d]>", index)
}

// Run executes an executable, the start of execution is the specified
// start time.
func (ex *Executable) Run(start time.Time) error {
	for i := 0; i < len(ex.Ops); {
		ex.mu.Lock()
		pr := ex.profiler
		ex.mu.Unlock()
		if pr != nil {
			pr.Edge(ex, i, true)
		}
		var err error
		var bit bool
		var val int64
		c := ex.Ops[i]
		var setbit chan<- bool
		var setval chan<- int64
		if c.Dest != nil {
			if c.Dest.Bank != nil {
				setbit, err = c.Dest.Bank.SetHold(c.Dest.Index)
				if err != nil {
					return fmt.Errorf("failed to hold %v", c.Dest)
				}
			} else if c.Dest.Number != nil {
				setval, err = c.Dest.Number.SetHold(c.Dest.Index)
				if err != nil {
					return fmt.Errorf("failed to hold %v", c.Dest)
				}
			}
		}
		switch c.Cmd {
		default:
			err = fmt.Errorf("exec failed for [%d] bad command: %v", i, c)
		case CmdRaise:
			bit = true
		case CmdLower:
			bit = false
		case CmdCopy:
			if b := c.Src[0].Bank; b != nil {
				if c.Dest.Bank == nil {
					err = fmt.Errorf("[%d] bad Copy: %v", i, c)
				}
				bit, err = b.Get(c.Src[0].Index)
			} else if n := c.Src[0].Number; n != nil {
				if c.Dest.Number == nil {
					err = fmt.Errorf("[%d] bad Copy: %v", i, c)
				}
				val, err = n.Get(c.Src[0].Index)
			} else {
				err = fmt.Errorf("[%d] unknown Copy: %v", i, c)
			}
		case CmdNot:
			if c.Src[0].Bank == nil {
				err = fmt.Errorf("exec failed for [%d] bad command: %v", i, c)
				break
			}
			bit, err = c.Src[0].Bank.Get(c.Src[0].Index)
			if err != nil {
				break
			}
			bit = !bit
		case CmdAnd, CmdOr, CmdXor:
			var bit2 bool
			// Loop until we get a consistent read on both sources.
			for retry := true; retry; {
				bit, err = c.Src[0].Bank.Get(c.Src[0].Index)
				if err != nil {
					break
				}
				bit2, err = c.Src[1].Bank.Get(c.Src[1].Index)
				if err != nil {
					break
				}
				var check bool
				check, err = c.Src[0].Bank.Get(c.Src[0].Index)
				if err != nil {
					break
				}
				if check == bit {
					retry = false
				}
			}
			if c.Cmd == CmdAnd {
				bit = bit && bit2
			} else if c.Cmd == CmdOr {
				bit = bit || bit2
			} else {
				bit = bit != bit2
			}
		case CmdAdd, CmdSub:
			if err = confirmNumber(false, c.Src...); err != nil {
				err = fmt.Errorf("require [%d] all numeric sources: %v", i, err)
				break
			}
			if err = confirmNumber(true, c.Dest); err != nil {
				err = fmt.Errorf("require [%d] all numeric result: %v", i, err)
				break
			}
			var a, b int64
			a, err = c.Src[0].Number.Get(c.Src[0].Index)
			if err != nil {
				break
			}
			b, err = c.Src[1].Number.Get(c.Src[1].Index)
			if err != nil {
				break
			}
			switch c.Cmd {
			case CmdAdd:
				val = a + b
			case CmdSub:
				val = a - b
			default:
				err = fmt.Errorf("expecting [%d] numeric operation: %v", i, c)
			}
		case CmdJumpEq, CmdJumpNEq, CmdJumpLT, CmdJumpLEq:
			if c.Step < 0 {
				err = fmt.Errorf("illegal [%d] negative jump target: %d", i, c.Step)
				break
			}
			if err = confirmNumber(false, c.Src...); err != nil {
				err = fmt.Errorf("require [%d] numerical comparison for jump: %v", i, c)
				break
			}
			var a, b int64
			a, err = c.Src[0].Number.Get(c.Src[0].Index)
			if err != nil {
				break
			}
			b, err = c.Src[1].Number.Get(c.Src[1].Index)
			if err != nil {
				break
			}
			var on bool
			switch c.Cmd {
			case CmdJumpEq:
				on = a == b
			case CmdJumpNEq:
				on = a != b
			case CmdJumpLT:
				on = a < b
			case CmdJumpLEq:
				on = a <= b
			default:
				err = fmt.Errorf("jump [%d] type unsupported: %v", i, c)
			}
			if err != nil || !on || c.Step == 0 {
				break
			}
			if i+c.Step >= len(ex.Ops) {
				err = fmt.Errorf("jump @%d:+%d beyond end (%d)", i, c.Step, len(ex.Ops))
				break
			}
			i += c.Step
		case CmdJump, CmdJumpTrue, CmdJumpFalse, CmdJumpOrRaise:
			if c.Step < 0 {
				err = fmt.Errorf("illegal [%d] negative jump target: %d", i, c.Step)
				break
			}
			on := true
			if c.Cmd == CmdJumpOrRaise {
				if on, err = c.Dest.Bank.Get(c.Dest.Index); err != nil {
					break
				}
				if !on {
					bit = true
					break
				} else {
					close(setbit)
					setbit = nil
				}
			} else if c.Cmd != CmdJump {
				on, err = c.Src[0].Bank.Get(c.Src[0].Index)
				if err != nil {
					break
				}
				if c.Cmd == CmdJumpFalse {
					on = !on
				}
			}
			if !on || c.Step == 0 {
				break
			}
			if i+c.Step >= len(ex.Ops) {
				err = fmt.Errorf("jump @%d:+%d beyond end (%d)", i, c.Step, len(ex.Ops))
				break
			}
			i += c.Step
		}
		if err != nil {
			if setbit != nil {
				close(setbit)
			}
			return fmt.Errorf("exec failed for [%d]: %v", i, err)
		}
		if setbit != nil {
			setbit <- bit
			close(setbit)
		}
		if setval != nil {
			setval <- val
			close(setval)
		}
		i++
		if pr != nil {
			pr.Edge(ex, i, false)
		}
	}
	latency := time.Now().Sub(start)
	ex.mu.Lock()
	defer ex.mu.Unlock()
	if latency > ex.MaxTime {
		ex.MaxTime = latency
	}
	ex.SumTime += latency
	ex.SumTime2 += latency * latency
	ex.SumTries++
	return nil
}

// Disassemble outputs a human readable version of the code.
func (c Code) String() string {
	switch c.Cmd {
	case CmdRaise:
		return fmt.Sprintf("%v = true", c.Dest)
	case CmdLower:
		return fmt.Sprintf("%v = false", c.Dest)
	case CmdNot:
		return fmt.Sprintf("%v = !%v", c.Dest, c.Src[0])
	case CmdCopy:
		return fmt.Sprintf("%v = %v", c.Dest, c.Src[0])
	case CmdAnd:
		return fmt.Sprintf("%v = %v && %v", c.Dest, c.Src[0], c.Src[1])
	case CmdOr:
		return fmt.Sprintf("%v = %v || %v", c.Dest, c.Src[0], c.Src[1])
	case CmdXor:
		return fmt.Sprintf("%v = %v ^^ %v", c.Dest, c.Src[0], c.Src[1])
	case CmdAdd:
		return fmt.Sprintf("%v = %v + %v", c.Dest, c.Src[0], c.Src[1])
	case CmdSub:
		return fmt.Sprintf("%v = %v - %v", c.Dest, c.Src[0], c.Src[1])
	case CmdJump:
		return fmt.Sprintf("jump +%d", c.Step)
	case CmdJumpTrue:
		return fmt.Sprintf("if %v { jump +%d }", c.Src[0], c.Step)
	case CmdJumpFalse:
		return fmt.Sprintf("if !%v { jump +%d }", c.Src[0], c.Step)
	case CmdJumpOrRaise:
		return fmt.Sprintf("if %v { jump +%d } else { %v = true }", c.Dest, c.Step, c.Dest)
	case CmdJumpEq:
		return fmt.Sprintf("if %v == %v { jump +%d }", c.Src[0], c.Src[1], c.Step)
	case CmdJumpNEq:
		return fmt.Sprintf("if %v != %v { jump +%d }", c.Src[0], c.Src[1], c.Step)
	case CmdJumpLT:
		return fmt.Sprintf("if %v < %v { jump +%d }", c.Src[0], c.Src[1], c.Step)
	case CmdJumpLEq:
		return fmt.Sprintf("if %v <= %v { jump +%d }", c.Src[0], c.Src[1], c.Step)
	default:
		return fmt.Sprintf("Invalid(%v)", c.Cmd)
	}
}

// Latency returns the current summary of how latent the executable
// completion is.
func (ex *Executable) Latency() (max, ave, sigma time.Duration) {
	if ex == nil {
		return
	}
	ex.mu.Lock()
	defer ex.mu.Unlock()
	if ex.SumTries == 0 {
		return
	}
	max = ex.MaxTime
	ave = ex.SumTime / time.Duration(ex.SumTries)
	v := ex.SumTime2/time.Duration(ex.SumTries) - ave*ave
	sigma = time.Duration(math.Sqrt(float64(v)))
	return
}

// SetTracer turns internal state tracing on and off (tracer = nil).
func (ex *Executable) SetTracer(tracer Tracer) {
	ex.mu.Lock()
	defer ex.mu.Unlock()
	ex.tracer = tracer
	tracer.Sample(ex.mask, ex.value)
}

// SetProfiler enables instruction profiling. The profile function is
// called before and after each instruction is executed.
func (ex *Executable) SetProfiler(profile Profiler) {
	ex.mu.Lock()
	defer ex.mu.Unlock()
	ex.profiler = profile
}
