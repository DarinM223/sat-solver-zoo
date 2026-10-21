SAT Solver Zoo
==============

Learning how to write SAT solvers.
Currently only a basic CDCL SAT solver is included.

Benchmarking
------------

```
sudo sysctl -w kernel.perf_event_paranoid=0
cargo +nightly flamegraph --bench large_cnf \
  -c "record -e cycles:u --call-graph dwarf" \
  -- --bench
perf report -i perf.data &> output.txt
```