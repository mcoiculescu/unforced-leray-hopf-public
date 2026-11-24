# Lean formalization of the two-solution theorem

`UnforcedLeray.main_theorem` proves `UnforcedLeray.MainClaim`, the two-solution
Theorem A in the [73-page reference manuscript](../reference/73-page-reference.pdf).
The theorem uses exactly `propext`, `Classical.choice`, and `Quot.sound`.

## Build and check

Install [Lean with elan](https://lean-lang.org/install/). The toolchain and
Mathlib revision are pinned in this directory. From the repository root,
run the following commands.

```sh
cd lean
lake exe cache get
lake build UnforcedLeray NonUniqueEuler NavierStokes
lake env lean verification/MainTheorem.lean
```

The last command checks the theorem's type and its transitive axiom set.

The clean audit on November 24, 2026 compiled 10,134 modules with Lean
`v4.34.0-rc2` and checked 103,479 project theorems. The release removes
internal paths and workflow notes from comments. The audited Lean statements
and proof code are preserved.

[Third-party notices](THIRD_PARTY_NOTICES.md)
