# URM: Unlimited Register Machines

A Lean 4 formalization of Unlimited Register Machines (URMs), a model of computation equivalent to Turing machines and partial recursive functions.

This standalone project formalizes URMs for eventual contribution to [CSLib](https://github.com/leanprover/cslib).

## References

- N.J. Cutland, *Computability: An Introduction to Recursive Function Theory* (1980)
- J.C. Shepherdson & H.E. Sturgis, *Computability of Recursive Functions* (1963)

## Structure

- `Urm/Basic.lean` - Core definitions: instructions, programs, state, configuration
- `Urm/Execution.lean` - Step semantics, halting, divergence, evaluation
- `Urm/Computable.lean` - URMComputable definition, basic function theorems

## Build

```bash
lake build
```

## Dependencies

- [CSLib](https://github.com/leanprover/cslib)
- Mathlib
