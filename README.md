# Non-Uniqueness of Leray–Hopf Solutions to the Unforced Three-Dimensional Navier–Stokes Equations

Tristan Buckmaster, Matei P. Coiculescu, and Chen Li.

- [Read the manuscript (PDF)](unforced-leray-hopf-shorter-proof.pdf)
- [LaTeX source](manuscript/main.tex)

## Lean formalization

The [audited Lean sources](lean/) prove the two-solution Theorem A in the
[73-page reference manuscript](reference/73-page-reference.pdf).
A Lean formalization in one-to-one correspondence with the proof in that
reference manuscript is forthcoming.

## Build the manuscript

With a TeX installation providing `latexmk` and the packages used in the source:

```sh
cd manuscript
build_dir=$(mktemp -d)
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir="$build_dir" main.tex
```

The compiled PDF is written to `$build_dir/main.pdf`.
