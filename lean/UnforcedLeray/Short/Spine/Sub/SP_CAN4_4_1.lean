import UnforcedLeray.Short.Spine.Sub.SP_CAN4_4

/-!
# Spine: `OscSmoothRep` cut into its leaf statements (task `Spine:SP-CAN/4/4/1`)

Target (`Short/Spine/Sub/SP_CAN4_4.lean`): `OscSmoothRep`, the Hermite level estimate. There are
smooth representatives `φ n` of `oscBasis n` on `(0, ∞)` with `sup_{[a,b]} |∂_r^m φ n| ≤ C (1+n)^q`.

Source of record: `the November 2 reference manuscript`, line 1086 and lines
1134-1140 (Hermite decomposition of `D`; `X_{G,j}` is the Gaussian-weighted Sobolev space); old
manuscript `paper/main.tex` 1856-1865, 1879-1888 (read only).

## The cut

`φ n := profFun (q n)` with `oscBasis n = prof (q n)`, `lag (q n) = -n q n` (`B0094.oscBasis_eigen`).

* Group A (profiles, polynomial calculus): `OscProfContDiff` (`profFun p` is `C^∞`),
  `OscProfOde` (`oscillatorD (profFun p) = profFun (lag p)` on `(0, ∞)`), `OscProfLocalNorm`
  (`∫_a^b |profFun q|² w ≤ ‖prof q‖²`, `w = 4π e^{r²/4} r`).
* Group B (radial ODE analysis, no polynomials). `OscOde n φ` says `φ` is `C^∞` on `(0, ∞)` with
  `oscillatorD φ = -n φ`, equivalently `φ'' = c₁ φ' + c₀ φ`, `c₁ = -(1/r + r/2)`,
  `c₀ = 4/r² - 2 - n` (`OscOde.deriv2`). With `w = 4π e^{r²/4} r` one has
  `(w φ')' = w c₀ φ`. The local energy estimate with a cutoff `χ` (`OscCutoff`, `OscEnergyDeriv`,
  `OscCaccioppoli`, `OscEnergyBound`) bounds `∫_a^b |φ'|² ≤ K (1+n)` from the `L²(w)` bound on a
  larger interval; the 1D Sobolev inequality (`OscSobolev1D`) turns the `L²` bounds on `φ, φ', φ''`
  into sup bounds (`OscSupBound`); the ODE differentiated `m` times bounds every derivative
  (`OscDerivRep`, `OscCoeffBounds`, `OscBootstrap`).

`oscSmoothRep_of` is the assembly (compiled here).

Status: nothing of the Hermite estimate is proved here except the assembly and `OscOde.deriv2`.
No `sorry`, `admit`, `axiom` or `native_decide`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Polynomial
open scoped ContDiff Topology InnerProductSpace

namespace UnforcedLeray.Short.Spine

open UnforcedLeray.B0010 Blueprint.Planar ComplexODEC UnforcedLeray.Cons.C01
open UnforcedLeray.Cons.G3b

/-- The `X_G` weight `w(r) = 4π e^{r²/4} r` (`B0010.xGDensity`, `B0094.weight_eq`). -/
def oscWeight (r : ℝ) : ℝ := 4 * Real.pi * Real.exp (r ^ 2 / 4) * r

/-- `φ` is a `C^∞` solution on `(0, ∞)` of the radial oscillator equation
`oscillatorD φ = -n φ` (the eigenvalue equation `D e_n = -n e_n`). -/
def OscOde (n : ℕ) (φ : ℝ → ℂ) : Prop :=
  ContDiffOn ℝ ∞ φ (Ioi 0) ∧ ∀ r : ℝ, 0 < r → oscillatorD φ r = -(n : ℂ) * φ r

/-- The coefficient `c₁(r) = -(1/r + r/2)` of `φ'` in `φ'' = c₁ φ' + c₀ φ` (complex valued). -/
def oscC1 (r : ℝ) : ℂ := ((-(1 / r + r / 2) : ℝ) : ℂ)

/-- The coefficient `c₀(r) = 4/r² - 2 - n` of `φ` in `φ'' = c₁ φ' + c₀ φ` (complex valued). -/
def oscC0 (n : ℕ) (r : ℝ) : ℂ := ((4 / r ^ 2 - 2 - (n : ℝ) : ℝ) : ℂ)

/-- **The second-order form of the eigenvalue equation**:
`φ'' = c₁ φ' + c₀ φ` on `(0, ∞)`. -/
theorem OscOde.deriv2 {n : ℕ} {φ : ℝ → ℂ} (h : OscOde n φ) {r : ℝ} (hr : 0 < r) :
    deriv (deriv φ) r = oscC1 r * deriv φ r + oscC0 n r * φ r := by
  have h1 := h.2 r hr
  unfold oscillatorD at h1
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  unfold oscC1 oscC0
  push_cast
  field_simp
  field_simp at h1
  linear_combination h1

/-! ## Group A: Gaussian-polynomial profiles -/

/-- **Leaf A1** (`profFun p` is smooth). `profFun p r = r² p(r²) e^{-r²/4}` is a polynomial in `r`
times `e^{-r²/4}`, hence `C^∞` on all of `ℝ`. -/
def OscProfContDiff : Prop :=
  ∀ p : ℂ[X], ContDiff ℝ ∞ (B0094.profFun p)

/-- **Leaf A2** (the radial oscillator on a profile). For every polynomial `p` and `r > 0`,
`oscillatorD (profFun p) r = profFun (lag p) r`: the radial form (`f'' + f'/r - 4f/r² + (r/2) f' +
2f`) of `D (r² p(r²) e^{-r²/4} e^{2iθ}) = r² (lag p)(r²) e^{-r²/4} e^{2iθ}`
(`B0094.gaussianOperator_angularTwoField_profFun`, `Units/B0094/Planar.lean:233`). -/
def OscProfOde : Prop :=
  ∀ (p : ℂ[X]) (r : ℝ), 0 < r →
    oscillatorD (B0094.profFun p) r = B0094.profFun (B0094.lag p) r

/-- **Leaf A3** (local `L²` bound from the `X_G` norm). For `0 < a ≤ b`,
`∫_a^b |profFun q|² w ≤ ‖prof q‖²_{X_G}`, since `‖prof q‖² = ∫_{(0,∞)} |profFun q|² w`
(`B0094.inner_prof`, `B0094.weight_eq`, `B0094.memLp_profFun`) and the integrand is nonnegative. -/
def OscProfLocalNorm : Prop :=
  ∀ (q : ℂ[X]) (a b : ℝ), 0 < a → a ≤ b →
    ∫ r in a..b, ‖B0094.profFun q r‖ ^ 2 * oscWeight r ≤ ‖B0094.prof q‖ ^ 2

/-! ## Group B: the radial ODE `oscillatorD φ = -n φ` -/

/-- **Leaf B1** (smooth cutoff). Between `a' < a ≤ b < b'` there is a `C^∞` function `χ` with
values in `[0, 1]`, equal to `1` on `[a, b]` and to `0` outside `(a', b')`. (Mathlib:
`ContDiffBump` centred at `(a+b)/2` with `rIn = (b-a)/2 + δ/2`, `rOut = (b-a)/2 + δ`,
`δ = min (a - a') (b' - b)`.) -/
def OscCutoff : Prop :=
  ∀ a b a' b' : ℝ, a' < a → a ≤ b → b < b' →
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ (∀ r ∈ Icc a b, χ r = 1) ∧ (∀ r, r ≤ a' → χ r = 0) ∧
      (∀ r, b' ≤ r → χ r = 0) ∧ ∀ r, 0 ≤ χ r ∧ χ r ≤ 1

/-- **Leaf B2** (the pointwise derivative of the energy flux). For a solution `φ` of
`oscillatorD φ = -n φ` and a smooth real `χ`, the function
`F = w χ² Re(conj φ · φ')` has, at every `r > 0`, the derivative
`χ² w |φ'|² + χ² w (4/r² - 2 - n) |φ|² + 2 w χ χ' Re(conj φ · φ')`.
Proof: product rule; `Re(conj φ' φ') = |φ'|²`; `w' = w (1/r + r/2)` and the ODE
`φ'' + (1/r + r/2) φ' = (4/r² - 2 - n) φ` (`OscOde.deriv2`) make
`Re(conj φ (w' φ' + w φ'')) = w (4/r² - 2 - n) |φ|²`. -/
def OscEnergyDeriv : Prop :=
  ∀ (n : ℕ) (φ : ℝ → ℂ) (χ : ℝ → ℝ), OscOde n φ → ContDiff ℝ ∞ χ →
    ∀ r : ℝ, 0 < r →
      HasDerivAt (fun s : ℝ => oscWeight s * χ s ^ 2 * (starRingEnd ℂ (φ s) * deriv φ s).re)
        (χ r ^ 2 * oscWeight r * ‖deriv φ r‖ ^ 2 +
          χ r ^ 2 * oscWeight r * (4 / r ^ 2 - 2 - (n : ℝ)) * ‖φ r‖ ^ 2 +
          2 * oscWeight r * χ r * deriv χ r * (starRingEnd ℂ (φ r) * deriv φ r).re) r

/-- **Leaf B3** (Caccioppoli inequality). For a solution `φ` of `oscillatorD φ = -n φ` and a
smooth `χ` vanishing at the endpoints `0 < a' ≤ b'`,
`∫ χ² w |φ'|² ≤ 2 (n + 2) ∫ χ² w |φ|² + 4 ∫ χ'² w |φ|²` over `[a', b']`.
Proof: integrate `OscEnergyDeriv` over `[a', b']` (fundamental theorem of calculus; the flux
vanishes at both ends), so `∫ χ² w |φ'|² = ∫ χ² w (n + 2 - 4/r²) |φ|² - 2 ∫ w χ χ' Re(conj φ φ')`;
drop `-4/r² ≤ 0` and use `2 |χ χ' φ φ'| ≤ ½ χ² |φ'|² + 2 χ'² |φ|²`; absorb the `½` term (all
integrands are continuous on `[a', b'] ⊂ (0, ∞)`). -/
def OscCaccioppoli : Prop :=
  ∀ (n : ℕ) (φ : ℝ → ℂ) (χ : ℝ → ℝ) (a' b' : ℝ), 0 < a' → a' ≤ b' → OscOde n φ →
    ContDiff ℝ ∞ χ → χ a' = 0 → χ b' = 0 →
    ∫ r in a'..b', χ r ^ 2 * oscWeight r * ‖deriv φ r‖ ^ 2 ≤
      (2 * ((n : ℝ) + 2) * ∫ r in a'..b', χ r ^ 2 * oscWeight r * ‖φ r‖ ^ 2) +
        4 * ∫ r in a'..b', (deriv χ r) ^ 2 * oscWeight r * ‖φ r‖ ^ 2

/-- **Leaf B4** (local `H¹` energy bound, linear in `n`). For `0 < a < b` there is `K` such that
every solution `φ` of `oscillatorD φ = -n φ` with `∫_{a/2}^{b+1} |φ|² w ≤ 1` has
`∫_a^b |φ|² ≤ K` and `∫_a^b |φ'|² ≤ K (1 + n)`.
Proof: `OscCutoff` with `a' = a/2`, `b' = b + 1`; `OscCaccioppoli`; `w ≥ 4π a > 0` on `[a, b]`;
`χ = 1` on `[a, b]`, `0 ≤ χ ≤ 1`, and `χ'` is bounded on `[a', b']` (continuous on a compact
set). -/
def OscEnergyBound : Prop :=
  ∀ a b : ℝ, 0 < a → a < b → ∃ K : ℝ, ∀ (n : ℕ) (φ : ℝ → ℂ), OscOde n φ →
    ∫ r in (a / 2)..(b + 1), ‖φ r‖ ^ 2 * oscWeight r ≤ 1 →
      (∫ r in a..b, ‖φ r‖ ^ 2 ≤ K) ∧ (∫ r in a..b, ‖deriv φ r‖ ^ 2 ≤ K * (1 + (n : ℝ)))

/-- **Leaf B5** (1D Sobolev inequality). For `g` smooth on `(0, ∞)`, `0 < a < b`, `x ∈ [a, b]`:
`|g x|² ≤ (1/(b-a) + 1) ∫_a^b |g|² + ∫_a^b |g'|²`.
Proof: for `x, y ∈ [a, b]`, `|g x|² - |g y|² = ∫_y^x 2 Re(conj g g')` (`HasDerivAt` of `‖g‖²`,
FTC) and `2 |g||g'| ≤ |g|² + |g'|²`, so `|g x|² ≤ |g y|² + ∫_a^b (|g|² + |g'|²)`; integrate in
`y ∈ [a, b]` and divide by `b - a`. -/
def OscSobolev1D : Prop :=
  ∀ (g : ℝ → ℂ) (a b : ℝ), 0 < a → a < b → ContDiffOn ℝ ∞ g (Ioi 0) →
    ∀ x ∈ Icc a b, ‖g x‖ ^ 2 ≤
      (1 / (b - a) + 1) * (∫ r in a..b, ‖g r‖ ^ 2) + ∫ r in a..b, ‖deriv g r‖ ^ 2

/-- **Leaf B6** (sup bounds for `φ` and `φ'`, linear in `n`). For `0 < a < b` there is `C` such
that every solution `φ` of `oscillatorD φ = -n φ` with `∫_{a/2}^{b+1} |φ|² w ≤ 1` has
`|φ r|, |φ' r| ≤ C (1 + n)` on `[a, b]`.
Proof: `OscEnergyBound` and `OscSobolev1D` for `g = φ` (bound `K (1+n)` for `|φ|²`) and for
`g = φ'` where `φ'' = c₁ φ' + c₀ φ` (`OscOde.deriv2`) gives `∫_a^b |φ''|² ≤ C (1+n)²`, so
`|φ'|² ≤ C (1+n)²` on `[a, b]`. -/
def OscSupBound : Prop :=
  ∀ a b : ℝ, 0 < a → a < b → ∃ C : ℝ, ∀ (n : ℕ) (φ : ℝ → ℂ), OscOde n φ →
    ∫ r in (a / 2)..(b + 1), ‖φ r‖ ^ 2 * oscWeight r ≤ 1 →
      ∀ r ∈ Icc a b, ‖φ r‖ ≤ C * (1 + (n : ℝ)) ∧ ‖deriv φ r‖ ≤ C * (1 + (n : ℝ))

/-- **Leaf B7** (Leibniz form of the differentiated ODE). For a solution `φ` of
`oscillatorD φ = -n φ`, every `m` and `r > 0`:
`φ^{(m+2)}(r) = ∑_{i ≤ m} C(m,i) (c₁^{(i)}(r) φ^{(m-i+1)}(r) + c₀^{(i)}(r) φ^{(m-i)}(r))`.
Proof: `iteratedDeriv_succ'` twice; `deriv (deriv φ) = oscC1 * deriv φ + oscC0 n * φ` on the
open set `Ioi 0` (`OscOde.deriv2`, `Filter.EventuallyEq.iteratedDeriv_eq`); `iteratedDeriv_add`,
`iteratedDeriv_mul` (Mathlib, `Analysis/Calculus/IteratedDeriv/Lemmas.lean`); `ContDiffAt` of
`oscC1`, `oscC0 n`, `φ` at `r > 0`; `iteratedDeriv_succ'` for `iteratedDeriv j (deriv φ)`. -/
def OscDerivRep : Prop :=
  ∀ (n : ℕ) (φ : ℝ → ℂ), OscOde n φ → ∀ (m : ℕ) (r : ℝ), 0 < r →
    iteratedDeriv (m + 2) φ r =
      ∑ i ∈ Finset.range (m + 1), (m.choose i : ℂ) *
        (iteratedDeriv i oscC1 r * iteratedDeriv (m - i + 1) φ r +
          iteratedDeriv i (oscC0 n) r * iteratedDeriv (m - i) φ r)

/-- **Leaf B8** (bounds for the coefficient derivatives on `[a, b]`). For `0 < a < b` and each
order `i`, `|c₁^{(i)}| ≤ C` and `|c₀^{(i)}| ≤ C (1 + n)` on `[a, b]`, uniformly in `n`.
Proof: `oscC1` and `oscC0 0` are `C^∞` on `(0, ∞)` (quotients of polynomials), so their iterated
derivatives are continuous on the compact `[a, b]` hence bounded; `oscC0 n = oscC0 0 - n` and
`iteratedDeriv i (oscC0 n) = iteratedDeriv i (oscC0 0)` for `i ≥ 1`, while for `i = 0` the value
is `oscC0 0 r - n`. -/
def OscCoeffBounds : Prop :=
  ∀ a b : ℝ, 0 < a → a < b → ∀ i : ℕ, ∃ C : ℝ, ∀ n : ℕ, ∀ r ∈ Icc a b,
    ‖iteratedDeriv i oscC1 r‖ ≤ C ∧ ‖iteratedDeriv i (oscC0 n) r‖ ≤ C * (1 + (n : ℝ))

/-- **Leaf B9** (bounds for all derivatives from those of `φ, φ'`). For `0 < a < b` and `m`
there is `C` such that if `|φ|, |φ'| ≤ M (1 + n)` on `[a, b]` (`M ≥ 0`), then
`|φ^{(m)}| ≤ C M (1 + n)^{m+1}` on `[a, b]`.
Proof: `m = 0, 1` are the hypotheses; for `m + 2` use `OscDerivRep` and `OscCoeffBounds`: each term
is at most `C' (1+n) M (1+n)^{m-i+1}` or `C' M (1+n)^{m-i+2}`, both at most
`C' M (1+n)^{m+2}`. Induct on `m` proving the bounds for `m` and `m + 1` with one common `C`
(monotone in the constant), so no recursion on constants is needed. -/
def OscBootstrap : Prop :=
  ∀ a b : ℝ, 0 < a → a < b → ∀ m : ℕ, ∃ C : ℝ, ∀ (n : ℕ) (φ : ℝ → ℂ) (M : ℝ), 0 ≤ M →
    OscOde n φ →
    (∀ r ∈ Icc a b, ‖φ r‖ ≤ M * (1 + (n : ℝ)) ∧ ‖deriv φ r‖ ≤ M * (1 + (n : ℝ))) →
      ∀ r ∈ Icc a b, ‖iteratedDeriv m φ r‖ ≤ C * M * (1 + (n : ℝ)) ^ (m + 1)

/-- **`OscSmoothRep` from the leaf statements** `OscProfContDiff`, `OscProfOde`,
`OscProfLocalNorm`, `OscSupBound`, `OscBootstrap`. Take `φ n = profFun (q n)` with
`oscBasis n = prof (q n)`, `lag (q n) = -n q n` (`B0094.oscBasis_eigen`). -/
theorem oscSmoothRep_of (h1 : OscProfContDiff) (h2 : OscProfOde) (h3 : OscProfLocalNorm)
    (h4 : OscSupBound) (h5 : OscBootstrap) : OscSmoothRep := by
  choose q hq1 hq2 using B0094.oscBasis_eigen
  have hode : ∀ n : ℕ, OscOde n (B0094.profFun (q n)) := by
    intro n
    refine ⟨(h1 (q n)).contDiffOn, fun r hr => ?_⟩
    rw [h2 (q n) r hr, hq2 n, B0094.profFun_smul]
    rfl
  have hnorm : ∀ n : ℕ, ‖B0094.prof (q n)‖ = 1 := by
    intro n
    rw [← hq1 n]
    exact B0094.oscBasis.orthonormal.1 n
  refine ⟨fun n => B0094.profFun (q n), ?_, ?_, ?_⟩
  · intro n
    have h := B0094.coeFn_prof (q n)
    rw [← hq1 n] at h
    exact h.symm
  · intro n
    exact (h1 (q n)).contDiffOn
  · intro m a b ha hab
    obtain ⟨C1, hC1⟩ := h4 a b ha hab
    obtain ⟨C2, hC2⟩ := h5 a b ha hab m
    refine ⟨C2 * |C1|, m + 1, fun n r hr => ?_⟩
    have hint : ∫ s in (a / 2)..(b + 1), ‖B0094.profFun (q n) s‖ ^ 2 * oscWeight s ≤ 1 := by
      have := h3 (q n) (a / 2) (b + 1) (by linarith) (by linarith)
      rw [hnorm n] at this
      simpa using this
    have hs0 : ∀ s ∈ Icc a b, ‖B0094.profFun (q n) s‖ ≤ |C1| * (1 + (n : ℝ)) ∧
        ‖deriv (B0094.profFun (q n)) s‖ ≤ |C1| * (1 + (n : ℝ)) := by
      intro s hs
      obtain ⟨e0, e1⟩ := hC1 n (B0094.profFun (q n)) (hode n) hint s hs
      have hn : (0 : ℝ) ≤ 1 + (n : ℝ) := by positivity
      exact ⟨e0.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hn),
        e1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hn)⟩
    exact hC2 n (B0094.profFun (q n)) |C1| (abs_nonneg _) (hode n) hs0 r hr

end UnforcedLeray.Short.Spine
