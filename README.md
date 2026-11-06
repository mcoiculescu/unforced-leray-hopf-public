# Non-Uniqueness of Leray–Hopf Solutions to the Unforced Three-Dimensional Navier–Stokes Equations

Tristan Buckmaster, Matei P. Coiculescu, and Chen Li.

- [Read the manuscript (PDF)](unforced-leray-hopf-shorter-proof.pdf)
- [LaTeX source](manuscript/main.tex)

A Lean formalization is forthcoming in this repository.

## Build the manuscript

With a TeX installation providing `latexmk` and the packages used in the source:

```sh
cd manuscript
build_dir=$(mktemp -d)
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir="$build_dir" main.tex
```

The compiled PDF is written to `$build_dir/main.pdf`.
