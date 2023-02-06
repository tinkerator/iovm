# iovm - a package for algorithmically setting IO signals.

## Overview

The package `iovm` is inspired by the
[x/net/bpf](https://pkg.go.dev/golang.org/x/net/bpf) package. However,
this present VM operates on signal bit IO banks and int64 numerical
vectors with a more restrictive instruction set that include both
reading and writing those values.

Automated package documentation for this Go package should be
available from [![Go
Reference](https://pkg.go.dev/badge/zappem.net/pub/io/iovm.svg)](https://pkg.go.dev/zappem.net/pub/io/iovm).

## Status

This project is intended to use such an execution model to build logic
systems with something approximating realtime behavior. Since Go does
not guarantee realtime execution, we can only measure how reliable the
timing appears to be and offer this visibility as an easy to determine
metric for performance.

The current status of the project is that we can execute sequences of
`iovm.Code` and permit instruction tracing. The code includes one
primitave for concurrency management: the `JumpOrRaise()` operation.

The only examples of _code_ at present are in the `iovm_test.go` file.

## TODOs

- Run a sequence with GPIOs once every 100ms on an RPi and measure
  its completion latency.
- Use the `iotracer` and `gpio` packages to export its wave trace as a
  VCD file.

In the distant future, we might consider compilation to binary form
for running on actual realtime devices. However, right now we are
focused on interpreted timing on Linux devices.

## License info

The `iovm` package is distributed with the same BSD 3-clause license
as that used by [golang](https://golang.org/LICENSE) itself.

## Reporting bugs and feature requests

The package `iovm` has been developed purely out of self-interest and
a curiosity for debugging physical IO projects, primarily on the
Raspberry Pi. Should you find a bug or want to suggest a feature
addition, please use the [bug
tracker](https://github.com/tinkerator/iovm/issues).
