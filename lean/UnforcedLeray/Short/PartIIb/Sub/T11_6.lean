import UnforcedLeray.Short.PartIIb.Sub.T11
import UnforcedLeray.Short.PartIIb.Sub.T12
import UnforcedLeray.Short.PartIIb.Org.QPeriodicHalfSpace.Basic

/-!
# Part II-b, leaf `PartII-b:T11/6` (`NiceFieldsSeparate`): cylinder Liouville in `L^r` (conditional)

Source of record: `the November 2 reference manuscript`, SP 2618 ("Free uniqueness
identifies ..."), with the flat equation of lines 1684-1690 and 1923-1938. The source never writes
the separation argument; it is the classical Liouville theorem for periodic `L^r` fields with
`div = curl = 0` on the planar cross-section `(q, η)`, proved here through mollification.

## Mathematical proof (all leaves below are classical, none is a source claim)

Let `b ∈ H_r`, `1 < r < 3`, be weakly solenoidal and orthogonal to the product tests
`θ(s) ∇^⊥ζ` (`ζ` a nice stream). Write `a = r/2 - 5/2 < 0`, so the density `s^a` of `H_r` is
bounded below on every bounded `s`-window: `b` is `L^r` on bounded windows `s ∈ (0, T)`.

1. (*Cut-off.*) For `δ > 0` let `b_δ = b · 1_{s > δ}`. It is locally integrable on `Coord`
   (`CutLocInt`, from `HrBoxIntegrable`, `T11/1/4`).
2. (*Tensor mollification.*) For kernels `ρ₁(t) ρ₂(w)` supported in `|t| ≤ δ`, `|w| ≤ δ`, put
   `M(p) = ∫ ρ₁(p₁ - x₁) ρ₂(p₂ - x₂) b_δ(x) dx`. Then `M` is `C^∞` with the usual derivative
   formula (`MollRegular`).
3. (*Equations.*) For `p₁ > 2δ` the test `x ↦ ρ₁(p₁ - x₁) ρ₂(p₂ - x₂)` is a coordinate test
   supported in `s > δ`, so the solenoidal clause gives `div M = 0` (`MollDiv`). The orthogonality
   to nice streams is first unfolded to compactly supported planar streams on all of `ℝ²`
   (`OrthUnfold`: periodize the planar part, use `c`-periodicity of `b`); with `θ(t) = ρ₁(p₁ - t)`,
   `ψ(w) = ρ₂(p₂ - w)` it gives `curl M = 0` (`MollCurl`).
4. (*Periodicity and `L^r` bound.*) `M` is `c`-periodic in `q` (`MollPeriodic`) and `M(s, ·)` is in
   `L^r(cell × ℝ)` (`MollLp`: Hölder in `t`, Young for the periodic planar convolution).
5. (*Liouville.*) `f = M₀ - i M₁` is entire (Cauchy-Riemann), `c`-periodic, in `L^r(cell × ℝ)`; the
   disc mean value property and Hölder make `f` bounded, Liouville makes it constant, and `L^r` over
   the infinite strip makes it `0` (`PeriodicEntireVanish`). Applying this to `M₀ - i M₁` and to
   `(M₀ + i M₁)(conj ·)` gives `M₀ = M₁ = 0` (`DivCurlFreeVanish`).
6. (*Approximate identity.*) `∫ ρ₁ρ₂ b_δ = 0` for all admissible product kernels at all `p₁ > 2δ`
   gives `b_δ = 0` a.e. on `s > 2δ` (`MollTranspose`, `TensorMollApprox`).
7. (*Transfer.*) `δ = 1/(n+1) → 0` gives `b = 0` a.e. on `s > 0`; `hMeas c r` is carried by
   `s > 0` and is absolutely continuous with respect to Lebesgue measure (`HMeasAe`).

Proved here: `niceFieldsSeparate_of`, the glue (step 5's component bookkeeping, steps 6-7).
Statements, not proofs, of the eighteen leaves `PartII-b:T11/6/1` ... `T11/6/18` are given below
with exact Lean types.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-! ## Definitions -/

/-- The cut-off `g · 1_{s > δ}` of a scalar function on the chart `Coord = ℝ_s × ℝ_q × ℝ_η`. -/
def cutC (δ : ℝ) (g : Coord → ℂ) : Coord → ℂ := Set.indicator {x : Coord | δ < x.1} g

/-- The tensor mollification of a function `h`: `(ρ₁ ⊗ ρ₂) ⋆ h` at the point `p = (s, (q, η))`,
`∫ ρ₁(s - t) ρ₂((q, η) - w) h(t, w) dt dw`. -/
def mollG (ρ₁ : ℝ → ℝ) (ρ₂ : ℝ × ℝ → ℝ) (h : Coord → ℂ) (p : Coord) : ℂ :=
  ∫ x : Coord, ((ρ₁ (p.1 - x.1) * ρ₂ (p.2 - x.2) : ℝ) : ℂ) * h x

/-- The mollification of the cut-off `g · 1_{s > δ}`. -/
def mollC (δ : ℝ) (ρ₁ : ℝ → ℝ) (ρ₂ : ℝ × ℝ → ℝ) (g : Coord → ℂ) (p : Coord) : ℂ :=
  mollG ρ₁ ρ₂ (cutC δ g) p

/-- The `s`-slice `z ↦ mollC δ ρ₁ ρ₂ g (s, z)` of the mollification, a function on the plane
`(q, η)`. -/
def mollSlice (δ : ℝ) (ρ₁ : ℝ → ℝ) (ρ₂ : ℝ × ℝ → ℝ) (g : Coord → ℂ) (s : ℝ) : ℝ × ℝ → ℂ :=
  fun z => mollC δ ρ₁ ρ₂ g (s, z)

/-- The tensor kernel `(t, w) ↦ ρ₁(t) ρ₂(w)` on the chart. -/
def tensorK (ρ₁ : ℝ → ℝ) (ρ₂ : ℝ × ℝ → ℝ) (y : Coord) : ℝ := ρ₁ y.1 * ρ₂ y.2

/-- An admissible mollifier pair of radius `δ`: smooth and vanishing for `|t| > δ`,
respectively for `max |w₁| |w₂| > δ`. -/
structure IsMollKer (δ : ℝ) (ρ₁ : ℝ → ℝ) (ρ₂ : ℝ × ℝ → ℝ) : Prop where
  smooth₁ : ContDiff ℝ ∞ ρ₁
  smooth₂ : ContDiff ℝ ∞ ρ₂
  supp₁ : ∀ t : ℝ, δ < |t| → ρ₁ t = 0
  supp₂ : ∀ w : ℝ × ℝ, (δ < |w.1| ∨ δ < |w.2|) → ρ₂ w = 0

/-- Orthogonality to the product tests `θ(s) ∇^⊥ζ(q, η)`, `ζ` a nice stream, on the cell. -/
def NiceOrth (c : ℝ) (b : CProf) : Prop :=
  ∀ (θ : ℝ → ℝ) (ζ : ℝ × ℝ → ℝ), TimeTest θ → NiceStream c ζ →
    ∫ x, streamPair b θ ζ x ∂(Axi.ageμ c 0) = 0

/-- Orthogonality to the product tests `θ(s) ∇^⊥ψ(q, η)`, `ψ` smooth with compact support in the
plane, over all of `Coord`. -/
def FullOrth (b : CProf) : Prop :=
  ∀ (θ : ℝ → ℝ) (ψ : ℝ × ℝ → ℝ), TimeTest θ → ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
    ∫ x : Coord, streamPair b θ ψ x = 0

/-! ## The leaves

Numbering `PartII-b:T11/6/k`. The ten leaves used by the glue `niceFieldsSeparate_of` are
`DivCurlFreeVanish` (5), `CutLocInt` (6), `MollRegular` (7), `MollDiv` (9), `OrthUnfold` (11),
`MollCurl` (12), `MollPeriodic` (13), `MollLp` (15), `TensorMollApprox` (17), `HMeasAe` (18); the
others are ingredients of those. -/

/-- **Leaf `PartII-b:T11/6/1`** (an entire periodic function in `L^r` of the strip is bounded).
Let `f : ℂ → ℂ` be entire, `c`-periodic in `Re z`, with `∫_{-c/2 ≤ Re z < c/2} |f|^r < ∞`
(`c > 0`, `r ≥ 1`). Then `f` is bounded.
Proof: (i) mean value: `∫_{B(z₀,1)} f = π f(z₀)` for entire `f`
(`Tasks/FlatUnique/Separate/DiscMean.lean`, `SeparateDisc.integral_ball_eq_of_differentiable`), so
`π ‖f z₀‖ ≤ ∫⁻_{B(z₀,1)} ‖f‖ₑ`; Hölder (or Jensen) on the ball, whose measure is `π`:
`∫⁻_B ‖f‖ₑ ≤ (∫⁻_B ‖f‖ₑ^r)^{1/r} π^{1-1/r}`; (ii) covering by period cells:
`∫⁻_{B(z₀,1)} ‖f‖ₑ^r ≤ (2/c + 2) ∫⁻_{cell} ‖f‖ₑ^r` for the periodic measurable `G = ‖f‖ₑ^r`
(`Tasks/FlatUnique/Separate/CoverBall.lean`, `SeparateCover.lintegral_ball_le_cellC_mul`, whose
`cellC c` is exactly the set `{z | z.re ∈ Ico (-(c/2)) (c/2)}` below). So
`‖f z₀‖ ≤ C` with `C` independent of `z₀`. -/
def PeriodicEntireBounded : Prop :=
  ∀ (c r : ℝ) (f : ℂ → ℂ), 0 < c → 1 ≤ r → Differentiable ℂ f →
    (∀ z : ℂ, f (z + (c : ℂ)) = f z) →
    (∫⁻ z in {z : ℂ | z.re ∈ Ico (-(c / 2)) (c / 2)}, ‖f z‖ₑ ^ r) ≠ ⊤ → ∃ C : ℝ, ∀ z : ℂ, ‖f z‖ ≤ C

/-- **Leaf `PartII-b:T11/6/2`** (periodic entire functions in `L^r` of the strip vanish; the
Liouville core; uses `T11/6/1`). An entire `f : ℂ → ℂ` that is `c`-periodic in `Re z` and satisfies
`∫_{-c/2 ≤ Re z < c/2} |f|^r < ∞` (`c > 0`, `r ≥ 1`) is `0`.
Proof: by `T11/6/1` `f` is bounded; Liouville (`Differentiable.apply_eq_apply_of_bounded`) makes
`f` constant `= k`; if `k ≠ 0` then `∫⁻_{cell} ‖k‖ₑ^r = ‖k‖ₑ^r · volume(cell) = ∞` (the cell has
infinite Lebesgue measure: it is `Ico ×ˢ univ` under `Complex.volume_preserving_equiv_real_prod`,
or contains the discs `B(i n, 1/2)`, `n ∈ ℕ`), contradiction. -/
def PeriodicEntireVanish : Prop :=
  ∀ (c r : ℝ) (f : ℂ → ℂ), 0 < c → 1 ≤ r → Differentiable ℂ f →
    (∀ z : ℂ, f (z + (c : ℂ)) = f z) →
    (∫⁻ z in {z : ℂ | z.re ∈ Ico (-(c / 2)) (c / 2)}, ‖f z‖ₑ ^ r) ≠ ⊤ → f = 0

/-- **Leaf `PartII-b:T11/6/3`** (Cauchy-Riemann). A real-`C¹` function `f : ℂ → ℂ` whose real
derivative `L = fderiv ℝ f z` satisfies `L 1 + i L i = 0` is complex differentiable.
Proof: `L i = i L 1` (multiply `i L i = -L 1` by `-i`), so `L h = L(h.re • 1 + h.im • i) =
h.re • L 1 + h.im • i L 1 = h • L 1`, i.e. `L` is `ℂ`-linear: `fderiv ℝ f z = (L 1) • 1` as maps
`ℂ →L[ℝ] ℂ`; use `differentiableAt_iff_restrictScalars` (or `HasFDerivAt.of_restrictScalars`-type
lemma) in `Mathlib/Analysis/Calculus/FDeriv/RestrictScalars.lean`. -/
def CRDifferentiable : Prop :=
  ∀ f : ℂ → ℂ, ContDiff ℝ 1 f →
    (∀ z : ℂ, fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I = 0) → Differentiable ℂ f

/-- **Leaf `PartII-b:T11/6/4`** (the strip of the plane as a cell of `ℝ × ℝ`). For measurable
`G : ℝ × ℝ → ℝ≥0∞`, `∫⁻_{-c/2 ≤ Re z < c/2} G(Re z, Im z) = ∫⁻_{Cyl.cell c} G`.
Proof: `Complex.volume_preserving_equiv_real_prod` (`Complex.measurableEquivRealProd`) maps
`z ↦ (z.re, z.im)` measure preservingly, and the image of the strip is
`Ico (-(c/2)) (c/2) ×ˢ univ = Cyl.cell c` (`neg_div`); use `MeasurePreserving.setLIntegral_comp_preimage_emb`
or `MeasurableEquiv.lintegral_map_equiv`. -/
def CellLintegralComplex : Prop :=
  ∀ (c : ℝ) (G : ℝ × ℝ → ℝ≥0∞), Measurable G →
    ∫⁻ z in {z : ℂ | z.re ∈ Ico (-(c / 2)) (c / 2)}, G (z.re, z.im) = ∫⁻ p in Cyl.cell c, G p

/-- **Leaf `PartII-b:T11/6/5`** (periodic `L^r` fields with `div = curl = 0` vanish; uses
`T11/6/2`, `T11/6/3`, `T11/6/4`). Let `B₀, B₁ : ℝ² → ℂ` be `C¹`, `c`-periodic in `q`, with
`∂_q B₀ + ∂_η B₁ = 0` and `∂_η B₀ - ∂_q B₁ = 0` everywhere and
`∫_{cell} |B_i|^r < ∞` for `i = 0, 1` (`Cyl.cell c = [-c/2, c/2) × ℝ`). Then `B₀ = B₁ = 0`.
Proof: `f(z) = B₀(Re z, Im z) - i B₁(Re z, Im z)` is real-`C¹` with
`f_q + i f_η = div + i curl = 0` (here `f_q = fderiv ℝ f z 1`, `f_η = fderiv ℝ f z I`), so `f` is
entire by `T11/6/3`; it is `c`-periodic (`f (z + c) = f z`), and by `T11/6/4` and
`‖f‖ₑ ≤ ‖B₀‖ₑ + ‖B₁‖ₑ`, `(x + y)^r ≤ 2^{r-1}(x^r + y^r)` (`ENNReal.rpow_add_le_mul_rpow_add_rpow`)
the strip integral is finite. By `T11/6/2`, `f = 0`. Next `g(z) = B₀(Re z, -Im z) + i B₁(Re z, -Im z)`
satisfies `g_q + i g_η = 0` (the sign of `η` flips both the `curl` sign and the `i`), is periodic with
the same strip integral (`η ↦ -η` preserves Lebesgue measure), hence `g = 0`. Then `B₀(q, η) =
(f + g(conj))/2 = 0` and `B₁ = 0` (evaluate `f` at `q + iη` and `g` at `q - iη`). -/
def DivCurlFreeVanish : Prop :=
  ∀ (c r : ℝ) (B₀ B₁ : ℝ × ℝ → ℂ), 0 < c → 1 ≤ r → ContDiff ℝ 1 B₀ → ContDiff ℝ 1 B₁ →
    (∀ z : ℝ × ℝ, B₀ (z.1 + c, z.2) = B₀ z) → (∀ z : ℝ × ℝ, B₁ (z.1 + c, z.2) = B₁ z) →
    (∀ z : ℝ × ℝ, fderiv ℝ B₀ z (1, 0) + fderiv ℝ B₁ z (0, 1) = 0) →
    (∀ z : ℝ × ℝ, fderiv ℝ B₀ z (0, 1) - fderiv ℝ B₁ z (1, 0) = 0) →
    (∫⁻ z in Cyl.cell c, ‖B₀ z‖ₑ ^ r) ≠ ⊤ → (∫⁻ z in Cyl.cell c, ‖B₁ z‖ₑ ^ r) ≠ ⊤ →
      B₀ = 0 ∧ B₁ = 0

/-- **Leaf `PartII-b:T11/6/6`** (the cut-off components are locally integrable; uses
`hrBoxIntegrable`, `T11/1/4`, file `Tasks/FlatUnique/CellStream/HrBox.lean`). For `b ∈ H_r`,
`r > 1`, `δ > 0` and `i = 0, 1`, the function `x ↦ b x i · 1_{x.1 > δ}` is locally integrable on
`Coord` (Lebesgue measure).
Proof: `locallyIntegrable_iff` on compacts: a compact `K` lies in a box `[-T, T] × [-R, R]²`; on
`K ∩ {s > δ} ⊆ [δ, T] × [-R, R] × [-R, R]` the function equals `b · i`, integrable by
`HrBoxIntegrable` (`σ := δ`), and the indicator of the measurable set `{δ < s}` preserves
integrability (`IntegrableOn.indicator`); it vanishes on the rest of `K`. -/
def CutLocInt : Prop :=
  ∀ (c r δ : ℝ) (b : CProf), 0 < c → 1 < r → 0 < δ → InHr c r b → ∀ i : Fin 2,
    LocallyIntegrable (cutC δ (fun x => b x i)) volume

/-- **Leaf `PartII-b:T11/6/7`** (regularity of the tensor mollification of a locally integrable
function; Mathlib `HasCompactSupport.contDiff_convolution_left` /
`HasCompactSupport.hasFDerivAt_convolution_left` or the `_right` versions,
`Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`).
For `g` with `cutC δ g` locally integrable and an admissible pair `(ρ₁, ρ₂)` of radius `δ`,
`mollC δ ρ₁ ρ₂ g` is `C^∞` on `Coord` and its derivative in the direction `v` at `p` is
`∫ (∂_v tensorK)(p - x) · cutC δ g x dx`.
Proof: `mollC δ ρ₁ ρ₂ g p = (tensorK ⋆[lsmul ℝ ℝ] cutC δ g) p` up to the change of variables
`x ↦ p - x` (`convolution_def`, `integral_sub_left_eq_self`, or `convolution_flip`); `tensorK ρ₁ ρ₂`
is smooth with compact support (`tsupport ⊆ [-δ, δ] × [-δ, δ]²`), and `cutC δ g` is locally
integrable. The derivative formula is the second Mathlib lemma. -/
def MollRegular : Prop :=
  ∀ (g : Coord → ℂ) (δ : ℝ) (ρ₁ : ℝ → ℝ) (ρ₂ : ℝ × ℝ → ℝ), 0 < δ → IsMollKer δ ρ₁ ρ₂ →
    LocallyIntegrable (cutC δ g) volume →
      ContDiff ℝ ∞ (mollC δ ρ₁ ρ₂ g) ∧
      ∀ p v : Coord, fderiv ℝ (mollC δ ρ₁ ρ₂ g) p v =
        ∫ x : Coord, ((fderiv ℝ (tensorK ρ₁ ρ₂) (p - x) v : ℝ) : ℂ) * cutC δ g x

/-- **Leaf `PartII-b:T11/6/8`** (derivative of an `s`-slice; uses `T11/6/7`). Under the same
hypotheses, for every `s`, `z` and planar direction `u`,
`fderiv ℝ (mollSlice δ ρ₁ ρ₂ g s) z u = ∫ ρ₁(s - x₁) (fderiv ρ₂ (z - x₂) u) · cutC δ g x dx`.
Proof: `mollSlice δ ρ₁ ρ₂ g s = mollC δ ρ₁ ρ₂ g ∘ (fun z => (s, z))` with
`HasFDerivAt (fun z => (s, z)) (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) z`, so the slice derivative
in direction `u` is `fderiv ℝ (mollC ...) (s, z) (0, u)` (`T11/6/7` gives differentiability);
and `fderiv ℝ (tensorK ρ₁ ρ₂) y (0, u) = ρ₁ y.1 * fderiv ℝ ρ₂ y.2 u` (product rule for
`y ↦ ρ₁ y.1 * ρ₂ y.2`; the first factor is constant in the direction `(0, u)`). -/
def MollSliceDeriv : Prop :=
  ∀ (g : Coord → ℂ) (δ : ℝ) (ρ₁ : ℝ → ℝ) (ρ₂ : ℝ × ℝ → ℝ), 0 < δ → IsMollKer δ ρ₁ ρ₂ →
    LocallyIntegrable (cutC δ g) volume → ∀ (s : ℝ) (z u : ℝ × ℝ),
      fderiv ℝ (mollSlice δ ρ₁ ρ₂ g s) z u =
        ∫ x : Coord, ((ρ₁ (s - x.1) * fderiv ℝ ρ₂ (z - x.2) u : ℝ) : ℂ) * cutC δ g x

/-- **Leaf `PartII-b:T11/6/9`** (the mollification is divergence free; uses `T11/6/6`, `T11/6/8`).
For `b ∈ H_r` weakly solenoidal, an admissible pair `(ρ₁, ρ₂)` of radius `δ` and `s > 2δ`, the
`s`-slices `M_i(z) = mollC δ ρ₁ ρ₂ (b · i) (s, z)` satisfy
`∂_q M₀(z) + ∂_η M₁(z) = 0` for all `z = (q, η)`.
Proof: by `MollSliceDeriv` the sum is `∫ ρ₁(s - x₁) [(fderiv ρ₂ (z - x₂) (1,0)) b₀ + (fderiv ρ₂ (z - x₂) (0,1)) b₁] dx`
(using `cutC δ (b · i) = b · i` on `x.1 > δ`, which contains the support since `x.1 ≥ s - δ > δ`).
The function `φ(x) = ρ₁(s - x₁) ρ₂(z - x₂)` is an `IsCoordTest` (smooth, compact support,
`tsupport φ ⊆ {s - δ ≤ x.1} ⊆ Ioi 0 ×ˢ univ`) with
`cpd 1 φ x = -ρ₁(s - x₁) fderiv ρ₂ (z - x₂) (1,0)` and `cpd 2 φ x = -ρ₁(s - x₁) fderiv ρ₂ (z - x₂) (0,1)`
(chain rule for `x ↦ z - x₂`), so the sum is `-∫ (b₀ cpd 1 φ + b₁ cpd 2 φ) = 0` by `WeakSolenoidal`.
Integrability of the two summands separately: `T11/6/6` times a bounded compactly supported
coefficient. -/
def MollDiv : Prop :=
  ∀ (c r : ℝ) (b : CProf), 0 < c → 1 < r → InHr c r b → WeakSolenoidal b →
    ∀ (δ : ℝ) (ρ₁ : ℝ → ℝ) (ρ₂ : ℝ × ℝ → ℝ), 0 < δ → IsMollKer δ ρ₁ ρ₂ →
      ∀ s : ℝ, 2 * δ < s → ∀ z : ℝ × ℝ,
        fderiv ℝ (mollSlice δ ρ₁ ρ₂ (fun x => b x 0) s) z (1, 0) +
          fderiv ℝ (mollSlice δ ρ₁ ρ₂ (fun x => b x 1) s) z (0, 1) = 0

/-- **Leaf `PartII-b:T11/6/10`** (periodization of a compactly supported planar stream is a nice
stream). For `c > 0` and `ψ` smooth with compact support there is a nice stream `ζ` (smooth,
`c`-periodic in `q`, vanishing for `|η|` large) with
`perpGrad ζ p i = Σ_{n ∈ ℤ} perpGrad ψ (p.1 + n c, p.2) i`.
Proof: `ζ p := Σ'_{n ∈ ℤ} ψ (p.1 + n c, p.2)`. Since `tsupport ψ ⊆ [-A, A] × [-L, L]`, for `q` in a
bounded set only finitely many `n` give a nonzero term (cf. `CellPart.per` and
`CellPart.mem_window`, `term_zero_of_not_mem` in `Tasks/FlatUnique/CellStream/Partition.lean`), so
on a neighbourhood of every point `ζ` is a finite sum of smooth functions (`contDiff_finsum`-type
lemma, or `ContDiffAt` via eventual equality to `Finset.sum`), the derivative of a locally finite
sum is the sum of the derivatives, `ζ (q + c, η) = ζ (q, η)` by reindexing `n ↦ n + 1`
(`Equiv.tsum_eq` / `tsum_eq_tsum_of_ne_zero_bij`), and `ζ = 0` for `|η| ≥ L`. -/
def PerNice : Prop :=
  ∀ (c : ℝ) (ψ : ℝ × ℝ → ℝ), 0 < c → ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
    ∃ ζ : ℝ × ℝ → ℝ, NiceStream c ζ ∧
      ∀ (p : ℝ × ℝ) (i : Fin 2), perpGrad ζ p i = ∑' n : ℤ, perpGrad ψ (p.1 + n * c, p.2) i

/-- **Leaf `PartII-b:T11/6/11`** (unfolding the orthogonality; uses `T11/6/10`).
If `b ∈ H_r` (`r > 1`, `c > 0`) is orthogonal to `θ(s) ∇^⊥ζ(q, η)` over the cell
(`ageμ c 0 = ds ⊗ dq/c dη|_{cell}`) for every time test `θ` and nice stream `ζ`, then
`∫_{Coord} streamPair b θ ψ = 0` for every time test `θ` and every smooth compactly supported
`ψ : ℝ² → ℝ`.
Proof: let `ζ` be the nice stream of `PerNice` for `ψ`. Put `A x = streamPair b θ ψ x`. It is
integrable on `Coord` (`hrBoxIntegrable`, `T11/1/4`, times a bounded coefficient supported in
`s ∈ tsupport θ`, `|q| ≤ A'`, `|η| ≤ L`). Strips `pucStrip c n` partition `Coord`
(`puc_iUnion_strip`, `puc_pairwise_disjoint`; `integral_iUnion`), and
`∫_{pucStrip c n} A = ∫_{univ ×ˢ cell} A (qShift (n c) y) dy` (`puc_setIntegral_strip`); by
a.e. `c`-periodicity of `b` (`InHr.periodic`, `puc_ae_shift_int`), `A (qShift (n c) y) = b y · θ · perpGrad ψ (y.2.1 + n c, y.2.2)`
a.e. Sum over `n` (finitely many nonzero terms on the compact `s, η`-support; `integral_tsum` or a
`Finset` window as in `coordPeriodicUnfold`) and use `PerNice`:
`∫_{Coord} A = ∫_{univ ×ˢ cell} streamPair b θ ζ`. Finally, `θ = 0` for `s ≤ 0`, so this equals
`∫_{Ioi 0 ×ˢ cell} streamPair b θ ζ = c ∫ streamPair b θ ζ ∂ageμ c 0` (`CellPart.ageμ_zero_eq`,
`Tasks/FlatUnique/CellStream/AgeCell.lean`), which is `0` by hypothesis. -/
def OrthUnfold : Prop :=
  ∀ (c r : ℝ) (b : CProf), 0 < c → 1 < r → InHr c r b → NiceOrth c b → FullOrth b

/-- **Leaf `PartII-b:T11/6/12`** (the mollification is curl free; uses `T11/6/6`, `T11/6/8`).
For `b ∈ H_r` with `FullOrth b`, an admissible pair of radius `δ` and `s > 2δ`, the slices satisfy
`∂_η M₀(z) - ∂_q M₁(z) = 0` for all `z`.
Proof: by `MollSliceDeriv` the left side is
`∫ ρ₁(s - x₁) [(fderiv ρ₂ (z - x₂) (0,1)) b₀ - (fderiv ρ₂ (z - x₂) (1,0)) b₁] dx`. Take
`θ(t) = ρ₁(s - t)` (a `TimeTest`: smooth, compact support, `tsupport θ ⊆ [s - δ, s + δ] ⊆ Ioi 0`
because `s > 2δ`) and `ψ(w) = ρ₂(z - w)` (smooth, compact support). Then
`perpGrad ψ w = ![-(fderiv ρ₂ (z - w) (0,1)), fderiv ρ₂ (z - w) (1,0)]` and
`streamPair b θ ψ x = -ρ₁(s - x₁)[b₀ (fderiv ρ₂ (z - x₂) (0,1)) - b₁ (fderiv ρ₂ (z - x₂) (1,0))]`,
whose integral is `0` by `FullOrth`. (`cutC δ (b · i) = b · i` on the support, as in `MollDiv`.) -/
def MollCurl : Prop :=
  ∀ (c r : ℝ) (b : CProf), 0 < c → 1 < r → InHr c r b → FullOrth b →
    ∀ (δ : ℝ) (ρ₁ : ℝ → ℝ) (ρ₂ : ℝ × ℝ → ℝ), 0 < δ → IsMollKer δ ρ₁ ρ₂ →
      ∀ s : ℝ, 2 * δ < s → ∀ z : ℝ × ℝ,
        fderiv ℝ (mollSlice δ ρ₁ ρ₂ (fun x => b x 0) s) z (0, 1) -
          fderiv ℝ (mollSlice δ ρ₁ ρ₂ (fun x => b x 1) s) z (1, 0) = 0

/-- **Leaf `PartII-b:T11/6/13`** (periodicity of the mollification). If `g` is a.e. `c`-periodic
in `q`, then `mollC δ ρ₁ ρ₂ g` is `c`-periodic in `q` everywhere: `mollC (qShift c p) = mollC p`.
Proof: `cutC δ g` depends on `g` and on `s` only, so it is a.e. `c`-periodic; the substitution
`x = qShift c y` (measure preserving embedding, `puc_measurePreserving_qShift`,
`puc_qShift_measurableEmbedding` in `Tasks/FlatUnique/CellStream/PeriodicUnfold.lean`,
`MeasurePreserving.integral_comp`) turns `∫ k(qShift c p - x) cutC g x dx` into
`∫ k(p - y) cutC g (qShift c y) dy`, since `qShift c p - qShift c y = p - y`; then
`integral_congr_ae`. A compiled proof is in `Sub/T11_6/ScratchMollPeriodic.lean`
(`scratchMollPeriodic`); copy it. -/
def MollPeriodic : Prop :=
  ∀ (c : ℝ) (g : Coord → ℂ) (δ : ℝ) (ρ₁ : ℝ → ℝ) (ρ₂ : ℝ × ℝ → ℝ), 0 < c →
    (∀ᵐ x : Coord, g (qShift c x) = g x) → ∀ p : Coord,
      mollC δ ρ₁ ρ₂ g (qShift c p) = mollC δ ρ₁ ρ₂ g p

/-- **Leaf `PartII-b:T11/6/14`** (`H_r` is `L^r` on strip boxes). For `b ∈ H_r`, `r > 1`,
`0 < σ`, and any `H, R`, `∫⁻_{[σ,H] × [-R,R] × ℝ} ‖b‖ₑ^r d(volume) < ∞`.
Proof: same device as `hrBoxIntegrable` (`Tasks/FlatUnique/CellStream/HrBox.lean`, whose
`hrBox_lintegral_G_bound` is the case of one cell `[σ,H] × cell`): on `[σ,H]` the density
`s^{r/2-5/2}` of `hMeas c r` is bounded below by a positive constant (`hrBox_density_lower`), so
`∫⁻_{[σ,H] × cell} ‖b'‖ₑ^r < ∞` for a measurable representative `b'`; the strip
`[-R, R] × ℝ` is covered by finitely many `q`-translates `qShift (n c)` of the cell, which are
measure preserving, and `‖b‖ₑ^r ∘ qShift (n c) = ‖b‖ₑ^r` a.e. (`QPeriodic`, `hrBox_shiftPer_all`). -/
def HrStripLp : Prop :=
  ∀ (c r : ℝ) (b : CProf), 0 < c → 1 < r → InHr c r b → ∀ σ H R : ℝ, 0 < σ →
    (∫⁻ x in Icc σ H ×ˢ (Icc (-R) R ×ˢ (univ : Set ℝ)), ‖b x‖ₑ ^ r) ≠ ⊤

/-- **Leaf `PartII-b:T11/6/15`** (the `s`-slices of the mollification are in `L^r(cell)`; uses
`T11/6/14`). For `b ∈ H_r`, `r > 1`, an admissible pair of radius `δ`, every `s` and `i = 0, 1`,
`∫_{cell} |mollC δ ρ₁ ρ₂ (b · i) (s, z)|^r dz < ∞`.
Proof: with `K(t, w) = |ρ₁(s - t)| |ρ₂(z - w)|`, `m = ∫ K = ‖ρ₁‖₁ ‖ρ₂‖₁ < ∞`, Hölder/Jensen
(`ENNReal.lintegral_mul_le_Lp_mul_Lq`, or `eLpNorm`-version for the probability measure
`K dt dw / m`) gives `‖M(s, z)‖ₑ^r ≤ m^{r-1} ∫⁻ K(t, w) ‖b̃_i(t, w)‖ₑ^r d(t, w)`, `b̃ = cutC δ (b · i)`.
Integrate over `z ∈ cell`, Tonelli (`lintegral_lintegral_swap`): for fixed `(t, w)` the `z`-integral
of `|ρ₂(z - w)|` is `≤ ‖ρ₂‖₁` and vanishes unless `w ∈ [-c/2 - δ, c/2 + δ] × ℝ`; also `K = 0`
unless `t ∈ [s - δ, s + δ]`, and `b̃ = 0` unless `t > δ`. So the integral is at most
`m^{r-1} ‖ρ₂‖₁ ‖ρ₁‖_∞ ∫⁻_{[δ, s+δ] × [-c/2-δ, c/2+δ] × ℝ} ‖b‖ₑ^r`, finite by `HrStripLp` with
`σ = δ`, `H = s + δ`, `R = c/2 + δ` (and `‖b x i‖ₑ ≤ ‖b x‖ₑ`). If `s + δ ≤ δ` the integrand is `0`. -/
def MollLp : Prop :=
  ∀ (c r : ℝ) (b : CProf), 0 < c → 1 < r → InHr c r b →
    ∀ (δ : ℝ) (ρ₁ : ℝ → ℝ) (ρ₂ : ℝ × ℝ → ℝ), 0 < δ → IsMollKer δ ρ₁ ρ₂ →
      ∀ (s : ℝ) (i : Fin 2),
        (∫⁻ z in Cyl.cell c, ‖mollSlice δ ρ₁ ρ₂ (fun x => b x i) s z‖ₑ ^ r) ≠ ⊤

/-- **Leaf `PartII-b:T11/6/16`** (transposition of a tensor mollification; Fubini). For `h` locally
integrable, continuous compactly supported kernels `ρ₁, ρ₂` and `χ : Coord → ℝ` continuous with
compact support,
`∫ χ(x) (ρ₁ ⊗ ρ₂ ⋆ h)(x) dx = ∫ (∫ χ(x) ρ₁(x₁ - y₁) ρ₂(x₂ - y₂) dx) h(y) dy`.
Proof: the function `(x, y) ↦ χ(x) ρ₁(x₁ - y₁) ρ₂(x₂ - y₂) h(y)` is integrable on `Coord × Coord`
(for `x ∈ supp χ` the `y`-support lies in the compact `supp χ - supp(ρ₁ ⊗ ρ₂)`, on which `h` is
integrable; the kernel and `χ` are bounded), so `integral_integral_swap` applies. -/
def MollTranspose : Prop :=
  ∀ (h : Coord → ℂ) (ρ₁ : ℝ → ℝ) (ρ₂ : ℝ × ℝ → ℝ) (χ : Coord → ℝ),
    LocallyIntegrable h volume → Continuous ρ₁ → HasCompactSupport ρ₁ →
    Continuous ρ₂ → HasCompactSupport ρ₂ → Continuous χ → HasCompactSupport χ →
    ∫ x : Coord, (χ x : ℂ) * mollG ρ₁ ρ₂ h x =
      ∫ y : Coord, ((∫ x : Coord, χ x * (ρ₁ (x.1 - y.1) * ρ₂ (x.2 - y.2)) : ℝ) : ℂ) * h y

/-- **Leaf `PartII-b:T11/6/17`** (a locally integrable function whose small tensor mollifications
vanish is zero; uses `T11/6/16`). Let `h` be locally integrable on `Coord` and `δ > 0`. If
`mollG ρ₁ ρ₂ h p = 0` for every admissible pair of radius `δ` and every `p` with `p.1 > 2δ`, then
`h = 0` a.e. on `{x.1 > 2δ}`.
Proof: let `U = {x.1 > 2δ}` (open). By `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`
(`Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`) it suffices that `∫ χ h = 0` for
smooth `χ` with compact `tsupport χ ⊆ U`. Take
`ρ₁ⁿ = (ContDiffBump (0:ℝ)).normed`, `ρ₂ⁿ = (ContDiffBump (0:ℝ×ℝ)).normed` with outer radius
`ε_n = δ/(n+1)` (nonnegative, integral `1`, `support = ball 0 ε_n`; Mathlib
`ContDiffBump.normed`, `integral_normed`, `nonneg_normed`, `support_normed_eq`,
`Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`); they are admissible of radius `δ` (note the
sup norm on `ℝ × ℝ`). By `MollTranspose`, `0 = ∫ χ (ρⁿ ⋆ h) = ∫ χⁿ h`,
`χⁿ(y) = ∫ χ(x) ρⁿ(x - y) dx`. As `n → ∞`, `χⁿ → χ` uniformly (uniform continuity of `χ`,
`ρⁿ ≥ 0`, `∫ ρⁿ = 1`, support shrinking; or `convolution_tendsto_right_of_continuous`), all
supported in a fixed compact set on which `h` is integrable, so `∫ χⁿ h → ∫ χ h` (dominated
convergence, `tendsto_integral_of_dominated_convergence`). Hence `∫ χ h = 0`. -/
def TensorMollApprox : Prop :=
  ∀ (h : Coord → ℂ) (δ : ℝ), 0 < δ → LocallyIntegrable h volume →
    (∀ (ρ₁ : ℝ → ℝ) (ρ₂ : ℝ × ℝ → ℝ) (p : Coord), IsMollKer δ ρ₁ ρ₂ → 2 * δ < p.1 →
      mollG ρ₁ ρ₂ h p = 0) →
    ∀ᵐ x : Coord, 2 * δ < x.1 → h x = 0

/-- **Leaf `PartII-b:T11/6/18`** (`hMeas` is carried by `s > 0` and is absolutely continuous).
If a property `P` holds Lebesgue-a.e. on `{x.1 > 0}`, it holds `hMeas c r`-a.e.
Proof: `hMeas c r = ageμ c (r/2 - 5/2) = ((vol|_{Ioi 0}).withDensity w).prod (Cyl.avgμ c)` with
`Cyl.avgμ c = ofReal c⁻¹ • vol|_{cell c}`. Hence `hMeas c r ≪ vol|_{Ioi 0} ⊗ vol = vol|_{Ioi 0 ×ˢ univ}`
(`Measure.AbsolutelyContinuous.prod`, `withDensity_absolutelyContinuous`,
`Measure.prod_restrict`), and a property holding a.e. on `Ioi 0 ×ˢ univ` holds `hMeas`-a.e.
(`ae_restrict_iff'`, `AbsolutelyContinuous.ae_le`). A compiled proof is in
`Sub/T11_6/ScratchHMeas.lean` (`scratchHMeasAe`); copy it. -/
def HMeasAe : Prop :=
  ∀ (c r : ℝ) (P : Coord → Prop), 0 < c → (∀ᵐ x : Coord, 0 < x.1 → P x) →
    ∀ᵐ x ∂(hMeas c r), P x

/-! ## The conditional theorem -/

theorem niceFieldsSeparate_of
    (hB : DivCurlFreeVanish) (hCL : CutLocInt)
    (hReg : MollRegular) (hDiv : MollDiv) (hUn : OrthUnfold) (hCurl : MollCurl)
    (hPer : MollPeriodic) (hLp : MollLp) (hAp : TensorMollApprox) (hAC : HMeasAe) : NiceFieldsSeparate := by
  intro c r b hc hr hr3 hb hsol horth
  have hfull : FullOrth b := hUn c r b hc hr hb horth
  have key : ∀ n : ℕ, ∀ᵐ x : Coord, 2 * (1 / ((n : ℝ) + 1)) < x.1 → b x = 0 := by
    intro n
    set δ : ℝ := 1 / ((n : ℝ) + 1) with hδ
    have hδpos : 0 < δ := by positivity
    have hcut : ∀ i : Fin 2, LocallyIntegrable (cutC δ (fun x => b x i)) volume :=
      hCL c r δ b hc hr hδpos hb
    -- `b` is periodic only on `s > 0` (`QPeriodic`), so the periodic function is the cut-off
    have hperi : ∀ i : Fin 2, ∀ᵐ x : Coord,
        cutC δ (fun y => b y i) (qShift c x) = cutC δ (fun y => b y i) x := by
      intro i
      refine QPerHalf.indicator_ae hδpos.le ?_
      filter_upwards [QPerHalf.ae_imp hb.periodic] with x hx hx0
      simp only [hx hx0]
    have hcc : ∀ (ρ₁ : ℝ → ℝ) (ρ₂ : ℝ × ℝ → ℝ) (g : Coord → ℂ),
        mollC δ ρ₁ ρ₂ (cutC δ g) = mollC δ ρ₁ ρ₂ g := by
      intro ρ₁ ρ₂ g
      funext p
      simp only [mollC, cutC, Set.indicator_indicator, Set.inter_self]
    -- vanishing of the mollifications
    have hvan : ∀ (ρ₁ : ℝ → ℝ) (ρ₂ : ℝ × ℝ → ℝ) (p : Coord), IsMollKer δ ρ₁ ρ₂ → 2 * δ < p.1 →
        mollC δ ρ₁ ρ₂ (fun x => b x 0) p = 0 ∧ mollC δ ρ₁ ρ₂ (fun x => b x 1) p = 0 := by
      intro ρ₁ ρ₂ p hk hp
      have hsm : ∀ i : Fin 2, ContDiff ℝ 1 (mollSlice δ ρ₁ ρ₂ (fun x => b x i) p.1) := by
        intro i
        have h1 : ContDiff ℝ ∞ (mollC δ ρ₁ ρ₂ (fun x => b x i)) :=
          (hReg (fun x => b x i) δ ρ₁ ρ₂ hδpos hk (hcut i)).1
        have h2 : ContDiff ℝ ∞ (fun z : ℝ × ℝ => ((p.1, z) : Coord)) :=
          contDiff_const.prodMk contDiff_id
        exact (h1.comp h2).of_le (by exact_mod_cast le_top)
      have hper : ∀ i : Fin 2, ∀ z : ℝ × ℝ,
          mollSlice δ ρ₁ ρ₂ (fun x => b x i) p.1 (z.1 + c, z.2) =
            mollSlice δ ρ₁ ρ₂ (fun x => b x i) p.1 z := by
        intro i z
        have h := hPer c (cutC δ (fun x => b x i)) δ ρ₁ ρ₂ hc (hperi i) (p.1, z)
        rw [hcc] at h
        exact h
      have hres := hB c r (mollSlice δ ρ₁ ρ₂ (fun x => b x 0) p.1)
        (mollSlice δ ρ₁ ρ₂ (fun x => b x 1) p.1) hc hr.le (hsm 0) (hsm 1) (hper 0) (hper 1)
        (hDiv c r b hc hr hb hsol δ ρ₁ ρ₂ hδpos hk p.1 hp)
        (hCurl c r b hc hr hb hfull δ ρ₁ ρ₂ hδpos hk p.1 hp)
        (hLp c r b hc hr hb δ ρ₁ ρ₂ hδpos hk p.1 0) (hLp c r b hc hr hb δ ρ₁ ρ₂ hδpos hk p.1 1)
      have h0 := congrFun hres.1 p.2
      have h1 := congrFun hres.2 p.2
      exact ⟨h0, h1⟩
    have comp : ∀ i : Fin 2, ∀ᵐ x : Coord, 2 * δ < x.1 → b x i = 0 := by
      intro i
      have h := hAp (cutC δ (fun x => b x i)) δ hδpos (hcut i)
        (fun ρ₁ ρ₂ p hk hp => by
          fin_cases i
          · exact (hvan ρ₁ ρ₂ p hk hp).1
          · exact (hvan ρ₁ ρ₂ p hk hp).2)
      filter_upwards [h] with x hx h2
      have hx' := hx h2
      have hmem : x ∈ {x : Coord | δ < x.1} := by
        show δ < x.1
        linarith
      simpa [cutC, Set.indicator_of_mem hmem] using hx'
    have hall := (ae_all_iff.2 comp)
    filter_upwards [hall] with x hx h2
    ext i
    simpa using hx i h2
  have hall : ∀ᵐ x : Coord, ∀ n : ℕ, 2 * (1 / ((n : ℝ) + 1)) < x.1 → b x = 0 := ae_all_iff.2 key
  refine hAC c r (fun x => b x = 0) hc ?_
  filter_upwards [hall] with x hx hxpos
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < x.1 / 2 by linarith)
  exact hx n (by linarith)

end UnforcedLeray.Short.IIb
