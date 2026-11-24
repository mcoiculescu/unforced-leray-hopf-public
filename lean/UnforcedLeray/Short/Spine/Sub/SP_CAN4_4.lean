import UnforcedLeray.Short.Spine.Sub.SP_CAN4

/-!
# Spine: `SobolevJointSmooth` cut into its leaf statements (task `Spine:SP-CAN/4/4`)

Target (`Short/Spine/Sub/SP_CAN4.lean`): `SobolevJointSmooth`. A curve `V` that is `C^∞` into every
`X_{G,j}` on `(0, ∞)` (`IsSmoothAllXGj V`) has a jointly `C^∞` representative on `(0, ∞)²`.

Source of record: `the November 2 reference manuscript`, line 1086 ("smooth for
positive `θ`") and lines 1134-1140 (the Hermite decomposition of `D` identifies `X_{G,j}` with the
Gaussian-weighted Sobolev space of order `j`; "Cartesian derivatives may leave angular sector two");
old manuscript `paper/main.tex` 1856-1865 and 1879-1888 (read only).

## The cut (Hermite route)

Write `c_n(θ) = ⟪e_n, V θ⟫` for the coefficients in the eigenbasis `e_n = oscBasis n` of `D`
(`D e_n = -n e_n`; each `e_n` is a Gaussian-polynomial profile, `B0094.oscBasis_eigen`) and
`W(θ, r) = ∑ₙ c_n(θ) φ_n(r)`, where `φ_n` is a smooth representative of `e_n`.

* `OscSmoothRep`: smooth representatives `φ_n` of `e_n` on `(0, ∞)` with derivative bounds on
  compact subintervals polynomial in `n` (the Hermite level estimate; NOT in the library).
* `CoefficientBounds`: `c_n` is `C^∞` on `(0, ∞)` and `∑ₙ (1+n)^j |c_n^{(k)}(θ)|²` is locally
  bounded, for all `k, j` (from `IsSmoothAllXGj`, `B0123.inner_IDpow`, Parseval).
* `SeriesJointSmooth`: the two previous facts make `∑ₙ c_n(θ) φ_n(r)` jointly `C^∞` on `(0, ∞)²`
  (Weierstrass M-test on all mixed derivatives with Cauchy-Schwarz).
* `SeriesIdentify`: for `f ∈ ⋂ⱼ X_{G,j}` the series `∑ₙ ⟪e_n, f⟫ φ_n(r)` converges absolutely for
  `r > 0` and equals `f` `xGMeasure`-a.e. (Hilbert basis expansion plus an a.e. subsequence).

`sobolevJointSmooth_of` is the assembly.

Status: the Hermite sup-bound (`OscSmoothRep`) is the real analytic gap; nothing here is proved
except the assembly. No `sorry`, `admit`, `axiom` or `native_decide`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology InnerProductSpace

namespace UnforcedLeray.Short.Spine

open UnforcedLeray.B0010 Blueprint.Planar ComplexODEC UnforcedLeray.Cons.C01
open UnforcedLeray.Cons.G3b

/-- **Leaf 1, the Hermite level estimate** (shorter proof lines 1134-1140). There are smooth
representatives `φ n` of the eigenvectors `oscBasis n` of `D` on `(0, ∞)`, with
`sup_{[a,b]} |∂_r^m φ_n| ≤ C_{m,a,b} (1+n)^q` for some `q = q(m)`.

Route (sketch): `oscBasis n = prof q_n` is a Gaussian-polynomial profile with `D e_n = -n e_n`
(`B0094.oscBasis_eigen`), so the smooth representative satisfies the radial ODE
`oscillatorD φ_n = -n φ_n`, i.e. `φ'' = -(1/r + r/2) φ' + (4/r² - 2 - n) φ`; hence every
`φ_n^{(m)}` is a combination of `φ_n, φ_n'` with coefficients polynomial in `(r, 1/r, n)`. The two
sup bounds for `φ_n, φ_n'` on `[a, b]` come from `‖φ_n‖_{L²(xGMeasure)} = 1`, the energy identity
`∫ |φ_n'|² w ≤ n + 2` (`w = r e^{r²/4}`, integration by parts for the self-adjoint `D`) and the
1D Sobolev inequality on `[a, b]`. Expect a further cut when drafted. -/
def OscSmoothRep : Prop :=
  ∃ φ : ℕ → ℝ → ℂ,
    (∀ n : ℕ, φ n =ᵐ[xGMeasure] ((B0094.oscBasis n : XG) : ℝ → ℂ)) ∧
    (∀ n : ℕ, ContDiffOn ℝ ∞ (φ n) (Ioi 0)) ∧
    ∀ (m : ℕ) (a b : ℝ), 0 < a → a < b →
      ∃ C : ℝ, ∃ q : ℕ, ∀ n : ℕ, ∀ r ∈ Icc a b,
        ‖iteratedDeriv m (φ n) r‖ ≤ C * (1 + (n : ℝ)) ^ q

/-- **Leaf 2, joint smoothness of the series** (Mathlib-level). Smooth `φ n` with polynomially
bounded derivatives and smooth coefficients `c n` with locally bounded weighted `ℓ²` norms of all
`θ`-derivatives give a jointly `C^∞` sum on `(0, ∞)²`.

Sketch: for `θ ∈ [a, b]`, each term `(1+n)^j ‖c_n^{(k)}(θ)‖² ≤ C`, so
`‖c_n^{(k)}(θ)‖ ≤ C^{1/2} (1+n)^{-j/2}`; with `j = 2q + 4` the mixed derivatives
`c_n^{(k)}(θ) φ_n^{(m)}(r)` of the terms are bounded by `C' (1+n)^{-2}`, which is summable. Apply
`contDiff_tsum` (Mathlib, `Analysis/Calculus/SmoothSeries.lean`) to the terms multiplied by a smooth
cutoff equal to `1` on a box in `(0, ∞)²`, or prove the `ContDiffOn` version directly;
`ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear` bounds the iterated derivative of
`(θ, r) ↦ c_n(θ) φ_n(r)`. -/
def SeriesJointSmooth : Prop :=
  ∀ (φ : ℕ → ℝ → ℂ) (c : ℕ → ℝ → ℂ),
    (∀ n : ℕ, ContDiffOn ℝ ∞ (φ n) (Ioi 0)) →
    (∀ (m : ℕ) (a b : ℝ), 0 < a → a < b →
      ∃ C : ℝ, ∃ q : ℕ, ∀ n : ℕ, ∀ r ∈ Icc a b,
        ‖iteratedDeriv m (φ n) r‖ ≤ C * (1 + (n : ℝ)) ^ q) →
    (∀ n : ℕ, ContDiffOn ℝ ∞ (c n) (Ioi 0)) →
    (∀ (k j : ℕ) (a b : ℝ), 0 < a → a < b →
      ∃ C : ℝ, ∀ θ ∈ Icc a b,
        Summable (fun n : ℕ => (1 + (n : ℝ)) ^ j * ‖iteratedDeriv k (c n) θ‖ ^ 2) ∧
        ∑' n : ℕ, (1 + (n : ℝ)) ^ j * ‖iteratedDeriv k (c n) θ‖ ^ 2 ≤ C) →
    ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => ∑' n : ℕ, c n z.1 * φ n z.2) (Ioi 0 ×ˢ Ioi 0)

/-- **Leaf 3, the Hermite coefficients of a smooth curve** (provable from the library). For `V`
with `IsSmoothAllXGj V`, the coefficients `θ ↦ ⟪e_n, V θ⟫` are `C^∞` on `(0, ∞)` and satisfy the
weighted `ℓ²` bounds needed by `SeriesJointSmooth`.

Route: with `U_j` the `C^∞` witness of `IsSmoothAllXGj V j`, `⟪e_n, U_j θ⟫ = (1+n)^{j/2} ⟪e_n, V θ⟫`
(`B0123.inner_IDpow`, `B0123.idMult`), so `⟪e_n, V θ⟫ = (1+n)^{-j/2} ⟪e_n, U_j θ⟫` is a continuous
linear functional of a `C^∞` curve; `iteratedDeriv k` of it is `(1+n)^{-j/2} ⟪e_n, U_j^{(k)} θ⟫`
on `(0, ∞)` (locality of `iteratedDeriv` on the open set), and
`∑ₙ (1+n)^j |⟪e_n, ...⟫|² = ∑ₙ |⟪e_n, U_j^{(k)} θ⟫|² ≤ ‖U_j^{(k)} θ‖²` (Bessel/Parseval,
`hasSum_norm_inner_sq`), bounded on `[a, b]` since `U_j^{(k)}` is continuous on `(0, ∞)`. -/
def CoefficientBounds : Prop :=
  ∀ V : ℝ → XG, IsSmoothAllXGj V →
    (∀ n : ℕ, ContDiffOn ℝ ∞ (fun θ : ℝ => inner ℂ (B0094.oscBasis n) (V θ)) (Ioi 0)) ∧
    (∀ (k j : ℕ) (a b : ℝ), 0 < a → a < b →
      ∃ C : ℝ, ∀ θ ∈ Icc a b,
        Summable (fun n : ℕ => (1 + (n : ℝ)) ^ j *
          ‖iteratedDeriv k (fun θ' : ℝ => inner ℂ (B0094.oscBasis n) (V θ')) θ‖ ^ 2) ∧
        ∑' n : ℕ, (1 + (n : ℝ)) ^ j *
          ‖iteratedDeriv k (fun θ' : ℝ => inner ℂ (B0094.oscBasis n) (V θ')) θ‖ ^ 2 ≤ C)

/-- **Leaf 4, the expansion identifies the representative** (Hilbert-basis level). If `φ n` are
representatives of the eigenbasis with locally polynomially bounded values, and `f` lies in every
`X_{G,j}`, then `∑ₙ ⟪e_n, f⟫ φ_n(r)` converges absolutely for every `r > 0` and equals `f`
`xGMeasure`-a.e.

Proof: pointwise absolute convergence for `r ∈ [a, b]` by Cauchy-Schwarz,
`∑ |⟪e_n, f⟫| C(1+n)^q ≤ (∑ (1+n)^{2q+2} |⟪e_n, f⟫|²)^{1/2} (C² ∑ (1+n)^{-2})^{1/2}` with
`j = 2q + 2` (`B0123.mem_XGj_iff`); the partial sums converge to `f` in `L²(xGMeasure)`
(`HilbertBasis.hasSum_repr`, `B0094.oscBasis`), hence a subsequence a.e. (`tendstoInMeasure`,
`exists_seq_tendsto_ae`), and `ae_xG_pos` (`B0012.ae_xG_pos`) restricts to `r > 0`. -/
def SeriesIdentify : Prop :=
  ∀ (φ : ℕ → ℝ → ℂ) (f : XG),
    (∀ n : ℕ, φ n =ᵐ[xGMeasure] ((B0094.oscBasis n : XG) : ℝ → ℂ)) →
    (∀ a b : ℝ, 0 < a → a < b → ∃ C : ℝ, ∃ q : ℕ, ∀ n : ℕ, ∀ r ∈ Icc a b,
      ‖φ n r‖ ≤ C * (1 + (n : ℝ)) ^ q) →
    (∀ j : ℕ, f ∈ B0123.XGj j) →
    (fun r : ℝ => ∑' n : ℕ, inner ℂ (B0094.oscBasis n) f * φ n r) =ᵐ[xGMeasure]
      ((f : XG) : ℝ → ℂ)

/-- **`SobolevJointSmooth` from the four leaf statements.** Take `φ` from `OscSmoothRep`,
`c n θ = ⟪e_n, V θ⟫`, and `W θ r = ∑ₙ c n θ * φ n r`. -/
theorem sobolevJointSmooth_of (h1 : OscSmoothRep) (h2 : SeriesJointSmooth)
    (h3 : CoefficientBounds) (h4 : SeriesIdentify) : SobolevJointSmooth := by
  intro V hV
  obtain ⟨φ, hφae, hφsm, hφbd⟩ := h1
  obtain ⟨hcsm, hcbd⟩ := h3 V hV
  refine ⟨fun θ r => ∑' n : ℕ, inner ℂ (B0094.oscBasis n) (V θ) * φ n r, ?_, ?_⟩
  · intro θ hθ
    have hmem : ∀ j : ℕ, V θ ∈ B0123.XGj j := by
      intro j
      obtain ⟨U, hU, -⟩ := hV j
      obtain ⟨h, -⟩ := hU θ hθ
      exact h
    exact h4 φ (V θ) hφae
      (fun a b ha hab => by simpa only [iteratedDeriv_zero] using hφbd 0 a b ha hab) hmem
  · exact h2 φ (fun n θ => inner ℂ (B0094.oscBasis n) (V θ)) hφsm hφbd hcsm hcbd

end UnforcedLeray.Short.Spine
