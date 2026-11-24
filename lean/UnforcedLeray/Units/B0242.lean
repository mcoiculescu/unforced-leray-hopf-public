import UnforcedLeray.Units.B0242.Seam

/-!
# B0242: the weighted cell space `X_c` and the seam inequality

Blueprint unit **B0242** (`unlabeled:4173`, old ledger `C17`), `paper/main.tex` lines 4171–4184:

> Fix `m` sufficiently large, for example `m > 8`, and use
> `X_c = L²(C_c, (1+q²+η²)^m dq dη)`. The weight is defined on the centered cell and
> periodically continued. It is continuous across the seam. Its normal derivative has a
> negative jump there, so distributionally `Δ(weight) ≤ C_m weight`. Smooth approximations,
> or integration by parts separately on the two sides, give the usual weighted diffusion
> energy with this favorable seam term. All Sobolev norms below can equivalently use a smooth
> uniformly comparable periodic weight.

## Representation

The cylinder `C_c = (ℝ/cℤ) × ℝ` (line 4127, centered cell `q ∈ [-c/2, c/2)`) is represented in
lifted coordinates `(q, η) ∈ ℝ × ℝ`; fields on `C_c` are functions on `ℝ × ℝ` that are
`c`-periodic in `q`, and `dq dη` on `C_c` is Lebesgue measure on the open centered cell
`B0656.cell c = (-c/2, c/2) × ℝ` (`B0656.cellMeasure c`; the seam is a null set).
Derivatives are the library's classical partials `GaussianVortex.partialX` (`∂_q`) and
`GaussianVortex.partialY` (`∂_η`); `∂_q²φ + ∂_η²φ` is `CylinderNS.spatialLaplacian φ`

that draft is not compiled).

## Contents (helper files in `Units/B0242/`)

* `Weight.lean`: the periodically continued weight `cellWeight m c` (`(1+q²+η²)^m` on the
  centered cell, `cellWeight_eq_polyWeight`), its periodicity, its continuity across the seam
  (`continuous_cellWeight`), the one-sided normal derivatives at the seam and their negative
  jump (`seam_jump_neg`), the space `Xc m c = L²(C_c, (1+q²+η²)^m dq dη)`, and the uniform
  comparison with the smooth periodic weight `ρ_c^m` of B0656 (`rho_rpow_comparable`,
  `eLpNorm_rho_le`, `eLpNorm_le_rho`, `memLp_iff_rho`).
* `Profile.lean`: the one-variable profile `(a + x²)^m` and Green's identities.
* `Seam.lean`: the core seam inequality `weak_seam_core` (integration by parts on the two
  sides of the seam).
* this file: the distributional inequality `Δ(weight) ≤ C_m weight` against nonnegative test
  functions on `C_c` (`distributional_laplacian_cellWeight_le`), the weighted diffusion energy
  with the favorable seam term (`weighted_diffusion_energy`, and on `X_c`,
  `weighted_diffusion_energy_Xc`), and the uniformity of `C_m` in `c`
  (`exists_seam_const_uniform`).

The constant is `C_m = seamConst m = 2(4m² − 2m)`, which depends only on `m`. The results hold
for every `m ≥ 1`, in particular for the manuscript's `m > 8` (`main`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ENNReal ContDiff

namespace UnforcedLeray.B0242

open UnforcedLeray.GaussianVortex (partialX partialY)
open UnforcedLeray.B0656 (cell cellMeasure measurableSet_cell rho)

/-! ### Test functions on the cylinder -/

/-- A test function on the cylinder `C_c = (ℝ/cℤ) × ℝ` in lifted coordinates: smooth,
`c`-periodic in `q`, and vanishing for `|η| ≥ R` for some `R` (compact support on `C_c`). -/
structure IsCylinderTest (c : ℝ) (φ : ℝ × ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ φ
  periodic : ∀ q η, φ (q + c, η) = φ (q, η)
  support : ∃ R : ℝ, ∀ z : ℝ × ℝ, R ≤ |z.2| → φ z = 0

/-- If `F` vanishes on `{R < |η|}`, so does `∂_q F`. -/
theorem partialX_eq_zero_of_band {R : ℝ} {F : ℝ × ℝ → ℝ}
    (hF : ∀ z : ℝ × ℝ, R < |z.2| → F z = 0) {z : ℝ × ℝ} (hz : R < |z.2|) :
    partialX F z = 0 := by
  change deriv (fun x => F (x, z.2)) z.1 = 0
  have : (fun x => F (x, z.2)) = fun _ => (0 : ℝ) := funext fun x => hF (x, z.2) hz
  rw [this, deriv_const]

/-- If `F` vanishes on `{R < |η|}`, so does `∂_η F`. -/
theorem partialY_eq_zero_of_band {R : ℝ} {F : ℝ × ℝ → ℝ}
    (hF : ∀ z : ℝ × ℝ, R < |z.2| → F z = 0) {z : ℝ × ℝ} (hz : R < |z.2|) :
    partialY F z = 0 := by
  change deriv (fun y => F (z.1, y)) z.2 = 0
  have hopen : IsOpen {y : ℝ | R < |y|} := isOpen_lt continuous_const continuous_abs
  have hev : (fun y => F (z.1, y)) =ᶠ[𝓝 z.2] fun _ => (0 : ℝ) := by
    filter_upwards [hopen.mem_nhds hz] with y hy
    exact hF (z.1, y) hy
  rw [hev.deriv_eq, deriv_const]

/-- A continuous function vanishing on `{R < |η|}`, times the weight, is integrable on the
centered cell. -/
theorem integrable_weight_mul_of_band {m c R : ℝ} {G : ℝ × ℝ → ℝ} (hG : Continuous G)
    (hR : ∀ z : ℝ × ℝ, R < |z.2| → G z = 0) :
    Integrable (fun z => polyWeight m z * G z) (cellMeasure c) :=
  integrable_cell_of_bounded (R := R + 1) ((continuous_polyWeight m).mul hG)
    fun z hz => by rw [hR z (by linarith), mul_zero]

/-- On the centered cell, integrals against the periodically continued weight are integrals
against `(1+q²+η²)^m`. -/
theorem integral_cellWeight_mul {m c : ℝ} (hc : 0 < c) (g : ℝ × ℝ → ℝ) :
    ∫ z, cellWeight m c z * g z ∂cellMeasure c = ∫ z, polyWeight m z * g z ∂cellMeasure c :=
  integral_congr_ae (ae_restrict_of_forall_mem (measurableSet_cell c) fun z hz => by
    simp only [cellWeight_eq_polyWeight_of_mem hc hz])

/-! ### Distributionally `Δ(weight) ≤ C_m weight` -/

/-- **Distributionally `Δ(weight) ≤ C_m weight`** (`paper/main.tex` lines 4178–4180, unit
B0242). For `m ≥ 1`, `c > 0` and every nonnegative test function `φ` on the cylinder `C_c`,
`∫_{C_c} W Δφ dq dη ≤ C_m ∫_{C_c} W φ dq dη`, where `W` is the periodically continued weight
`(1+q²+η²)^m` and `C_m = seamConst m` does not depend on `c`. The negative jump of the normal
derivative of `W` at the seam contributes the nonpositive term `−2 ∂_q W(c/2⁻, η) φ(c/2, η)`. -/
theorem distributional_laplacian_cellWeight_le {m c : ℝ} (hm : 1 ≤ m) (hc : 0 < c)
    {φ : ℝ × ℝ → ℝ} (hφ : IsCylinderTest c φ) (hnn : ∀ z, 0 ≤ φ z) :
    ∫ z, cellWeight m c z * (partialX (partialX φ) z + partialY (partialY φ) z)
        ∂cellMeasure c ≤
      seamConst m * ∫ z, cellWeight m c z * φ z ∂cellMeasure c := by
  obtain ⟨R, hR⟩ := hφ.support
  have hR' : ∀ z : ℝ × ℝ, R < |z.2| → φ z = 0 := fun z hz => hR z hz.le
  have hD := C2Data.of_contDiff (contDiff_infty.1 hφ.smooth 2)
  have hY : ∀ z : ℝ × ℝ, R < |z.2| → partialY φ z = 0 := fun z hz =>
    partialY_eq_zero_of_band hR' hz
  have hXX : ∀ z : ℝ × ℝ, R < |z.2| → partialX (partialX φ) z = 0 := fun z hz =>
    partialX_eq_zero_of_band (fun z' hz' => partialX_eq_zero_of_band hR' hz') hz
  have hYY : ∀ z : ℝ × ℝ, R < |z.2| → partialY (partialY φ) z = 0 := fun z hz =>
    partialY_eq_zero_of_band hY hz
  have key := weak_seam_core hm hc hD hφ.periodic hnn
    (integrable_weight_mul_of_band hD.cont hR') (integrable_weight_mul_of_band hD.contY hY)
    (integrable_weight_mul_of_band hD.contXX hXX) (integrable_weight_mul_of_band hD.contYY hYY)
  rw [integral_cellWeight_mul hc, integral_cellWeight_mul hc]
  exact key

/-! ### Product rules for the classical partials -/

theorem partialX_eq_of_hasDerivAt {F : ℝ × ℝ → ℝ} {q η d : ℝ}
    (h : HasDerivAt (fun x => F (x, η)) d q) : partialX F (q, η) = d := h.deriv

theorem partialY_eq_of_hasDerivAt {F : ℝ × ℝ → ℝ} {q η d : ℝ}
    (h : HasDerivAt (fun y => F (q, y)) d η) : partialY F (q, η) = d := h.deriv

theorem partialX_mul {f g : ℝ × ℝ → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (z : ℝ × ℝ) :
    partialX (fun z => f z * g z) z = partialX f z * g z + f z * partialX g z :=
  partialX_eq_of_hasDerivAt (F := fun z => f z * g z)
    ((hasDerivAt_sliceX hf z.1 z.2).mul (hasDerivAt_sliceX hg z.1 z.2))

theorem partialY_mul {f g : ℝ × ℝ → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (z : ℝ × ℝ) :
    partialY (fun z => f z * g z) z = partialY f z * g z + f z * partialY g z :=
  partialY_eq_of_hasDerivAt (F := fun z => f z * g z)
    ((hasDerivAt_sliceY hf z.1 z.2).mul (hasDerivAt_sliceY hg z.1 z.2))

theorem partialX_add {f g : ℝ × ℝ → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (z : ℝ × ℝ) : partialX (fun z => f z + g z) z = partialX f z + partialX g z :=
  partialX_eq_of_hasDerivAt (F := fun z => f z + g z)
    ((hasDerivAt_sliceX hf z.1 z.2).add (hasDerivAt_sliceX hg z.1 z.2))

theorem partialY_add {f g : ℝ × ℝ → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (z : ℝ × ℝ) : partialY (fun z => f z + g z) z = partialY f z + partialY g z :=
  partialY_eq_of_hasDerivAt (F := fun z => f z + g z)
    ((hasDerivAt_sliceY hf z.1 z.2).add (hasDerivAt_sliceY hg z.1 z.2))

/-- `∂_q²(w²) = 2((∂_q w)² + w ∂_q² w)`. -/
theorem partialX_partialX_sq {w : ℝ × ℝ → ℝ} (hw : C2Data w) :
    partialX (partialX (fun z => w z * w z)) =
      fun z => 2 * (partialX w z * partialX w z + partialX (partialX w) z * w z) := by
  have e : partialX (fun z => w z * w z) = fun z => partialX w z * w z + w z * partialX w z :=
    funext (partialX_mul hw.diff hw.diff)
  rw [e]
  funext z
  rw [partialX_add (f := fun z => partialX w z * w z) (g := fun z => w z * partialX w z)
      (hw.diffX.mul hw.diff) (hw.diff.mul hw.diffX),
    partialX_mul hw.diffX hw.diff, partialX_mul hw.diff hw.diffX]
  ring

/-- `∂_η²(w²) = 2((∂_η w)² + w ∂_η² w)`. -/
theorem partialY_partialY_sq {w : ℝ × ℝ → ℝ} (hw : C2Data w) :
    partialY (partialY (fun z => w z * w z)) =
      fun z => 2 * (partialY w z * partialY w z + partialY (partialY w) z * w z) := by
  have e : partialY (fun z => w z * w z) = fun z => partialY w z * w z + w z * partialY w z :=
    funext (partialY_mul hw.diff hw.diff)
  rw [e]
  funext z
  rw [partialY_add (f := fun z => partialY w z * w z) (g := fun z => w z * partialY w z)
      (hw.diffY.mul hw.diff) (hw.diff.mul hw.diffY),
    partialY_mul hw.diffY hw.diff, partialY_mul hw.diff hw.diffY]
  ring

/-- `∂_η(w²) = 2 w ∂_η w`. -/
theorem partialY_sq {w : ℝ × ℝ → ℝ} (hw : C2Data w) :
    partialY (fun z => w z * w z) = fun z => 2 * (partialY w z * w z) := by
  funext z
  rw [partialY_mul hw.diff hw.diff]
  ring

/-! ### The weighted diffusion energy with the favorable seam term -/

/-- **The weighted diffusion energy with the favorable seam term** (`paper/main.tex` lines
4180–4182, unit B0242). Let `m ≥ 1`, `c > 0`, `ν ≥ 0`, and let `w` be `C²` and `c`-periodic in
`q` (a `C²` field on the cylinder `C_c`) with `w, ∂_q w, ∂_η w ∈ X_c` and with the two pieces
`(∂_q² w) w`, `(∂_η² w) w` of `(Δw) w` integrable for the `X_c` measure. Then
`2 ⟨ν Δw, w⟩_{X_c} ≤ −2ν ∫ |∇w|² W + C_m ν ‖w‖²_{X_c}`, with `C_m = seamConst m`
independent of `c`. All integrals are against `(1+q²+η²)^m dq dη` on the centered cell. -/
theorem weighted_diffusion_energy {m c ν : ℝ} (hm : 1 ≤ m) (hc : 0 < c) (hν : 0 ≤ ν)
    {w : ℝ × ℝ → ℝ} (hw : ContDiff ℝ 2 w) (hper : ∀ q η, w (q + c, η) = w (q, η))
    (h0 : MemLp w 2 (weightMeasure m c))
    (h1 : MemLp (partialX w) 2 (weightMeasure m c))
    (h2 : MemLp (partialY w) 2 (weightMeasure m c))
    (h11 : Integrable (fun z => partialX (partialX w) z * w z) (weightMeasure m c))
    (h22 : Integrable (fun z => partialY (partialY w) z * w z) (weightMeasure m c)) :
    2 * ν * ∫ z, (partialX (partialX w) z + partialY (partialY w) z) * w z ∂weightMeasure m c ≤
      -2 * ν * ∫ z, (partialX w z ^ 2 + partialY w z ^ 2) ∂weightMeasure m c +
        seamConst m * ν * ∫ z, w z ^ 2 ∂weightMeasure m c := by
  have hD := C2Data.of_contDiff hw
  have hφ : C2Data (fun z => w z * w z) := C2Data.of_contDiff (hw.mul hw)
  have hperφ : ∀ q η, (fun z => w z * w z) (q + c, η) = (fun z => w z * w z) (q, η) :=
    fun q η => by simp only [hper]
  have j0 : Integrable (fun z => w z * w z) (weightMeasure m c) := h0.integrable_mul h0
  have jY : Integrable (fun z => partialY w z * w z) (weightMeasure m c) := h2.integrable_mul h0
  have jX2 : Integrable (fun z => partialX w z * partialX w z) (weightMeasure m c) :=
    h1.integrable_mul h1
  have jY2 : Integrable (fun z => partialY w z * partialY w z) (weightMeasure m c) :=
    h2.integrable_mul h2
  have jXX : Integrable (fun z => 2 * (partialX w z * partialX w z +
      partialX (partialX w) z * w z)) (weightMeasure m c) := (jX2.add h11).const_mul 2
  have jYY : Integrable (fun z => 2 * (partialY w z * partialY w z +
      partialY (partialY w) z * w z)) (weightMeasure m c) := (jY2.add h22).const_mul 2
  have key := weak_seam_core hm hc hφ hperφ (fun z => mul_self_nonneg (w z))
    ((integrable_weightMeasure_iff hc).1 j0)
    (by rw [partialY_sq hD]; exact (integrable_weightMeasure_iff hc).1 (jY.const_mul 2))
    (by rw [partialX_partialX_sq hD]; exact (integrable_weightMeasure_iff hc).1 jXX)
    (by rw [partialY_partialY_sq hD]; exact (integrable_weightMeasure_iff hc).1 jYY)
  simp only [partialX_partialX_sq hD, partialY_partialY_sq hD] at key
  have key2 : ∫ z, (2 * (partialX w z * partialX w z + partialX (partialX w) z * w z) +
      2 * (partialY w z * partialY w z + partialY (partialY w) z * w z)) ∂weightMeasure m c ≤
      seamConst m * ∫ z, w z * w z ∂weightMeasure m c := by
    rw [integral_weightMeasure hc, integral_weightMeasure hc]
    exact key
  have iA : Integrable (fun z => partialX w z ^ 2 + partialY w z ^ 2) (weightMeasure m c) :=
    (jX2.add jY2).congr (ae_of_all _ fun z => by simp only [Pi.add_apply, pow_two])
  have iB : Integrable (fun z => (partialX (partialX w) z + partialY (partialY w) z) * w z)
      (weightMeasure m c) :=
    (h11.add h22).congr (ae_of_all _ fun z => by simp only [Pi.add_apply]; ring)
  have hl : ∫ z, (2 * (partialX w z * partialX w z + partialX (partialX w) z * w z) +
      2 * (partialY w z * partialY w z + partialY (partialY w) z * w z)) ∂weightMeasure m c =
      2 * ∫ z, (partialX w z ^ 2 + partialY w z ^ 2) ∂weightMeasure m c +
        2 * ∫ z, (partialX (partialX w) z + partialY (partialY w) z) * w z
          ∂weightMeasure m c := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (iA.const_mul 2) (iB.const_mul 2)]
    congr 1
    funext z
    ring
  have hr : ∫ z, w z * w z ∂weightMeasure m c = ∫ z, w z ^ 2 ∂weightMeasure m c := by
    congr 1
    funext z
    ring
  rw [hl, hr] at key2
  have := mul_le_mul_of_nonneg_left key2 hν
  linarith

/-! ### The same inequality on `X_c` -/

theorem inner_toLp_eq_integral {μ : Measure (ℝ × ℝ)} {f g : ℝ × ℝ → ℝ} (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) : inner ℝ (hf.toLp f) (hg.toLp g) = ∫ z, f z * g z ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with z e1 e2
  rw [Real.inner_apply, e1, e2]

theorem norm_toLp_sq_eq_integral {μ : Measure (ℝ × ℝ)} {f : ℝ × ℝ → ℝ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ z, f z ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, inner_toLp_eq_integral]
  congr 1
  funext z
  ring

/-- **The weighted diffusion energy on `X_c`** (`paper/main.tex` lines 4180–4182, unit B0242).
For `m ≥ 1`, `c > 0`, `ν ≥ 0`, and a `C²`, `c`-periodic `w` with `w`, `∂_q w`, `∂_η w`,
`∂_q² w`, `∂_η² w ∈ X_c`:
`2ν ⟨Δw, w⟩_{X_c} ≤ −2ν (‖∂_q w‖²_{X_c} + ‖∂_η w‖²_{X_c}) + C_m ν ‖w‖²_{X_c}`. -/
theorem weighted_diffusion_energy_Xc {m c ν : ℝ} (hm : 1 ≤ m) (hc : 0 < c) (hν : 0 ≤ ν)
    {w : ℝ × ℝ → ℝ} (hw : ContDiff ℝ 2 w) (hper : ∀ q η, w (q + c, η) = w (q, η))
    (h0 : MemLp w 2 (weightMeasure m c))
    (h1 : MemLp (partialX w) 2 (weightMeasure m c))
    (h2 : MemLp (partialY w) 2 (weightMeasure m c))
    (h11 : MemLp (partialX (partialX w)) 2 (weightMeasure m c))
    (h22 : MemLp (partialY (partialY w)) 2 (weightMeasure m c)) :
    2 * ν * inner ℝ ((h11.add h22).toLp (partialX (partialX w) + partialY (partialY w)) : Xc m c)
        (h0.toLp w) ≤
      -2 * ν * (‖(h1.toLp (partialX w) : Xc m c)‖ ^ 2 + ‖(h2.toLp (partialY w) : Xc m c)‖ ^ 2) +
        seamConst m * ν * ‖(h0.toLp w : Xc m c)‖ ^ 2 := by
  have E := weighted_diffusion_energy hm hc hν hw hper h0 h1 h2 (h11.integrable_mul h0)
    (h22.integrable_mul h0)
  rw [inner_toLp_eq_integral, norm_toLp_sq_eq_integral, norm_toLp_sq_eq_integral,
    norm_toLp_sq_eq_integral]
  have hs : ∫ z, (partialX w z ^ 2 + partialY w z ^ 2) ∂weightMeasure m c =
      (∫ z, partialX w z ^ 2 ∂weightMeasure m c) + ∫ z, partialY w z ^ 2 ∂weightMeasure m c := by
    refine integral_add ?_ ?_
    · exact (h1.integrable_mul h1).congr (ae_of_all _ fun z => by simp only [Pi.mul_apply, pow_two])
    · exact (h2.integrable_mul h2).congr (ae_of_all _ fun z => by simp only [Pi.mul_apply, pow_two])
  rw [hs] at E
  simpa only [Pi.add_apply] using E

/-! ### Uniformity of the constant and the summary for `m > 8` -/

/-- **`C_m` is independent of `c`** (line 4180): one constant serves every period `c > 0`, both
for the distributional inequality `Δ(weight) ≤ C_m weight` and for the weighted diffusion
energy. -/
theorem exists_seam_const_uniform {m : ℝ} (hm : 1 ≤ m) :
    ∃ C : ℝ,
      (∀ c : ℝ, 0 < c → ∀ φ : ℝ × ℝ → ℝ, IsCylinderTest c φ → (∀ z, 0 ≤ φ z) →
        ∫ z, cellWeight m c z * (partialX (partialX φ) z + partialY (partialY φ) z)
            ∂cellMeasure c ≤
          C * ∫ z, cellWeight m c z * φ z ∂cellMeasure c) ∧
      (∀ c ν : ℝ, 0 < c → 0 ≤ ν → ∀ w : ℝ × ℝ → ℝ, ContDiff ℝ 2 w →
        (∀ q η, w (q + c, η) = w (q, η)) →
        MemLp w 2 (weightMeasure m c) → MemLp (partialX w) 2 (weightMeasure m c) →
        MemLp (partialY w) 2 (weightMeasure m c) →
        Integrable (fun z => partialX (partialX w) z * w z) (weightMeasure m c) →
        Integrable (fun z => partialY (partialY w) z * w z) (weightMeasure m c) →
        2 * ν * ∫ z, (partialX (partialX w) z + partialY (partialY w) z) * w z
            ∂weightMeasure m c ≤
          -2 * ν * ∫ z, (partialX w z ^ 2 + partialY w z ^ 2) ∂weightMeasure m c +
            C * ν * ∫ z, w z ^ 2 ∂weightMeasure m c) :=
  ⟨seamConst m, fun _ hc _ hφ hnn => distributional_laplacian_cellWeight_le hm hc hφ hnn,
    fun _ _ hc hν _ hw hper h0 h1 h2 h11 h22 =>
      weighted_diffusion_energy hm hc hν hw hper h0 h1 h2 h11 h22⟩

/-- **B0242, summary** (`paper/main.tex` lines 4171–4184) for the manuscript's `m > 8` and
every period `c > 0`: the periodically continued weight `W = cellWeight m c` equals
`(1+q²+η²)^m` on the centered cell, is `c`-periodic and continuous (across the seam); its
`q`-derivative at the seam `q = c/2` has one-sided values whose jump (outside minus inside) is
negative; `Δ W ≤ C_m W` holds distributionally on `C_c`; and the smooth periodic weight
`ρ_c^m` of B0656 is comparable to `W` with constants depending only on `m`. The weighted
diffusion energy is `weighted_diffusion_energy` / `weighted_diffusion_energy_Xc`. -/
theorem main {m c : ℝ} (hm : 8 < m) (hc : 0 < c) :
    (∀ z ∈ cell c, cellWeight m c z = polyWeight m z) ∧
    (∀ q η, cellWeight m c (q + c, η) = cellWeight m c (q, η)) ∧
    Continuous (cellWeight m c) ∧
    (∀ η : ℝ, HasDerivWithinAt (fun q => cellWeight m c (q, η)) (profileD m (1 + η ^ 2) (c / 2))
        (Iic (c / 2)) (c / 2) ∧
      HasDerivWithinAt (fun q => cellWeight m c (q, η)) (profileD m (1 + η ^ 2) (-(c / 2)))
        (Ici (c / 2)) (c / 2) ∧
      profileD m (1 + η ^ 2) (-(c / 2)) - profileD m (1 + η ^ 2) (c / 2) < 0) ∧
    (∀ φ : ℝ × ℝ → ℝ, IsCylinderTest c φ → (∀ z, 0 ≤ φ z) →
      ∫ z, cellWeight m c z * (partialX (partialX φ) z + partialY (partialY φ) z)
          ∂cellMeasure c ≤
        seamConst m * ∫ z, cellWeight m c z * φ z ∂cellMeasure c) ∧
    (ContDiff ℝ ∞ (rho c) ∧ (∀ q η, rho c (q + c, η) = rho c (q, η)) ∧
      ∀ z, (4 / Real.pi ^ 2) ^ m * cellWeight m c z ≤ rho c z ^ m ∧
        rho c z ^ m ≤ cellWeight m c z) := by
  have hm1 : 1 ≤ m := by linarith
  have hm0 : 0 < m := by linarith
  exact ⟨fun z hz => cellWeight_eq_polyWeight_of_mem hc hz, cellWeight_add_period m c,
    continuous_cellWeight m c,
    fun η => ⟨hasDerivWithinAt_cellWeight_seam_left hc η,
      hasDerivWithinAt_cellWeight_seam_right hc η, seam_jump_neg hm0 hc η⟩,
    fun _ hφ hnn => distributional_laplacian_cellWeight_le hm1 hc hφ hnn,
    B0656.contDiff_rho c, B0656.rho_periodic hc.ne',
    rho_rpow_comparable hm0.le hc⟩

end UnforcedLeray.B0242
