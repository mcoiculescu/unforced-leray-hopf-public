import UnforcedLeray.Short.PartI.Sub.T02_3_11
import UnforcedLeray.Lib.Cylinder.IBP

/-!
# Part I, task `PartI:T02/3/11` (leaf): `CcViscousEstimate`

Source of record: `the November 2 reference manuscript`, lines 276-288 (the viscous
cross term of the energy method for the difference of two classical solutions).
Target: `ccViscousEstimate : CcViscousEstimate` (`Short/PartI/Sub/T02_3_11.lean`, line 223), from the
hypotheses `EtaCutoffFacts`, `CellIntegrableOfSupport`, `CcSliceSmooth` and `CcDiffEnergyBound`.

Route. Let `w = ccDiffV v v' s`, `φ = etaCutoff R`, `D = ∫_cell φ |∇w|²`, `C₀` from `EtaCutoffFacts`
(`|φ'| ≤ (C₀/R)√φ`).

1. Pointwise Young inequality (`ccVE_young`): with `k = C₀/R`, `t = √φ`,
   `-2ν φ' ⟨w, ∂_η w⟩ ≤ (ν/2) φ |∂_η w|² + 2ν k² |w|²` and `|∂_η w|² ≤ |∇w|²`.
2. Integrate over the cell (`integral_mono`, `integral_add`, `integral_const_mul`); the
   integrability and continuity come from `CcSliceSmooth` and `CellIntegrableOfSupport`, and
   `CcDiffEnergyBound` gives `∫_cell |w|² ≤ 4M`.  Hence
   `-2ν ∫ φ'⟨w, ∂_η w⟩ ≤ (ν/2) D + 8ν C₀² M / R²`.
3. `ccViscousRhs = -2νD - 2ν ∫ φ'⟨w, ∂_η w⟩ ≤ -(3/2)νD + K/R²` with `K = 8νC₀²M ≥ 0` (`M ≥ 0`
   from `‖v(0, 0)‖ ≤ M`), and `K/R² ≤ K/√R` since `√R ≤ R²` for `R ≥ 1`.

Helpers are prefixed `ccVE_`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-! ### Elementary inequalities -/

/-- Pointwise Young inequality for the viscous cross term: with `|p| ≤ k t` (where `t = √φ`,
`t² = φ`), `|I| ≤ y x`, `x² ≤ G`, `-2ν p I ≤ (ν/2) φ G + 2ν k² y²`. -/
theorem ccVE_young (ν k t p I x y G φv : ℝ) (hν : 0 ≤ ν) (hk : 0 ≤ k) (ht : 0 ≤ t)
    (ht2 : t ^ 2 = φv) (hφ0 : 0 ≤ φv) (hp : |p| ≤ k * t) (hI : |I| ≤ y * x)
    (hx : x ^ 2 ≤ G) :
    -2 * ν * (p * I) ≤ ν / 2 * (φv * G) + 2 * ν * k ^ 2 * y ^ 2 := by
  have h1 : -(p * I) ≤ k * t * (y * x) := by
    have hpI : -(p * I) ≤ |p * I| := neg_le_abs _
    rw [abs_mul] at hpI
    have hmul : |p| * |I| ≤ k * t * (y * x) :=
      mul_le_mul hp hI (abs_nonneg _) (mul_nonneg hk ht)
    linarith
  have h2 : -2 * ν * (p * I) ≤ 2 * ν * (k * t * (y * x)) := by
    have hν2 : 0 ≤ 2 * ν := by linarith
    have h' := mul_le_mul_of_nonneg_left h1 hν2
    nlinarith
  have h3 : 2 * ν * (k * t * (y * x)) ≤ ν / 2 * (t ^ 2 * x ^ 2) + 2 * ν * k ^ 2 * y ^ 2 := by
    nlinarith [mul_nonneg hν (sq_nonneg (t * x - 2 * k * y))]
  have h4 : ν / 2 * (φv * x ^ 2) ≤ ν / 2 * (φv * G) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx hφ0) (by linarith)
  rw [ht2] at h3
  linarith [h2, h3, h4]

/-! ### Partial derivatives of vector fields and their components -/

/-- The `η`-derivative of a component is the component of the `η`-derivative. -/
theorem ccVE_partialEta_comp {u : Plane → Vec} (hu : Differentiable ℝ u) (i : Fin 2)
    (z : Plane) :
    Cyl.partialEta (fun w => u w i) z = Cyl.partialEta u z i := by
  have hslice : HasDerivAt (fun η : ℝ => u (z.1, η)) (Cyl.partialEta u z) z.2 :=
    Cyl.hasDerivAt_sliceEta hu z.1 z.2
  have hcomp := (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt z.2 hslice
  exact hcomp.deriv

/-- `‖∂_η u‖² ≤ |∇u|²` (the squared Euclidean norm of the `η`-derivative is the sum of the squares
of its two components, which are the `η`-derivatives of the components). -/
theorem ccVE_norm_sq_le {u : Plane → Vec} (hu : Differentiable ℝ u) (z : Plane) :
    ‖Cyl.partialEta u z‖ ^ 2 ≤ gradNormSq u z := by
  have hpe : ‖Cyl.partialEta u z‖ ^ 2 =
      Cyl.partialEta u z 0 ^ 2 + Cyl.partialEta u z 1 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  rw [hpe, ← ccVE_partialEta_comp hu 0 z, ← ccVE_partialEta_comp hu 1 z]
  unfold gradNormSq
  nlinarith [sq_nonneg (Cyl.partialQ (fun w => u w 0) z),
    sq_nonneg (Cyl.partialQ (fun w => u w 1) z)]

/-- Continuity of `|∇u|²` for a `C¹` vector field `u`. -/
theorem ccVE_gradNormSq_cont {u : Plane → Vec} (hu : ContDiff ℝ 1 u) :
    Continuous (gradNormSq u) := by
  have hc0 : ContDiff ℝ 1 (fun z => u z 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hu
  have hc1 : ContDiff ℝ 1 (fun z => u z 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hu
  have h0 := Cyl.C1_partial_of_contDiff hc0
  have h1 := Cyl.C1_partial_of_contDiff hc1
  unfold gradNormSq
  exact (((h0.1.pow 2).add (h0.2.pow 2)).add (h1.1.pow 2)).add (h1.2.pow 2)

/-! ### The target -/

/-- **`PartI:T02/3/11` leaf, target `CcViscousEstimate`.** -/
theorem ccViscousEstimate (hη : EtaCutoffFacts) (hI : CellIntegrableOfSupport)
    (hS : CcSliceSmooth) (hE : CcDiffEnergyBound) : CcViscousEstimate := by
  unfold CcViscousEstimate
  intro ν c T M v v' p p' h
  unfold EtaCutoffFacts at hη
  obtain ⟨C₀, hC₀, hcut⟩ := hη
  have hν : 0 < ν := h.nu_pos
  have hc : 0 < c := by linarith [h.c_ge]
  -- `M ≥ 0`, from `‖v(0, 0)‖ ≤ M`
  have hM : 0 ≤ M := le_trans (norm_nonneg _) ((h.bb 0 ⟨le_refl 0, h.T_pos.le⟩).1 0)
  have hK0 : 0 ≤ 8 * ν * C₀ ^ 2 * M :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hν.le) (sq_nonneg _)) hM
  refine ⟨8 * ν * C₀ ^ 2 * M, hK0, ?_⟩
  intro R hR s hs
  have hR0 : 0 < R := by linarith
  -- smoothness of the difference `w = ccDiffV v v' s` at age `s`
  have hw1 : ContDiff ℝ ∞ (ccDiffV v v' s) :=
    (hS ν c T v p h.cl s hs).1.sub (hS ν c T v' p' h.cl' s hs).1
  have hw1' : ContDiff ℝ 1 (ccDiffV v v' s) := hw1.of_le (by simp)
  have hwc : Continuous (ccDiffV v v' s) := hw1'.continuous
  have hwd : Differentiable ℝ (ccDiffV v v' s) := hw1'.differentiable (by simp)
  have hpe : Continuous (Cyl.partialEta (ccDiffV v v' s)) :=
    (Cyl.C1_partial_of_contDiff hw1').2
  -- the cutoff facts at radius `R`
  obtain ⟨hsm, -, -, hφz, hφd⟩ := hcut R hR
  have hsm1 : ContDiff ℝ 1 (etaCutoff R) := hsm.of_le (by simp)
  have hφc : Continuous (fun z : Plane => etaCutoff R z.2) :=
    hsm1.continuous.comp continuous_snd
  have hdc : Continuous (fun z : Plane => deriv (etaCutoff R) z.2) :=
    hsm1.continuous_deriv_one.comp continuous_snd
  have hφ0 : ∀ η : ℝ, 0 ≤ etaCutoff R η := etaCutoff_nonneg R
  -- the derivative of the cutoff vanishes for `2R ≤ |η|` (a nonnegative function that is `0`
  -- there attains its minimum, so its derivative vanishes there)
  have hdz : ∀ η : ℝ, 2 * R ≤ |η| → deriv (etaCutoff R) η = 0 := by
    intro η hη
    apply IsLocalMin.deriv_eq_zero
    show ∀ᶠ y in nhds η, etaCutoff R η ≤ etaCutoff R y
    refine Filter.Eventually.of_forall (fun y => ?_)
    rw [hφz η hη]
    exact hφ0 y
  have hf_zero : ∀ z : Plane, 2 * R ≤ |z.2| →
      deriv (etaCutoff R) z.2 *
        inner ℝ (ccDiffV v v' s z) (Cyl.partialEta (ccDiffV v v' s) z) = 0 := by
    intro z hz
    rw [hdz z.2 hz, zero_mul]
  have hD_zero : ∀ z : Plane, 2 * R ≤ |z.2| →
      etaCutoff R z.2 * gradNormSq (ccDiffV v v' s) z = 0 := by
    intro z hz
    rw [hφz z.2 hz, zero_mul]
  -- continuity and support, hence integrability on the cell
  have hG_cont : Continuous (gradNormSq (ccDiffV v v' s)) :=
    ccVE_gradNormSq_cont hw1'
  have hfcont : Continuous (fun z : Plane =>
      deriv (etaCutoff R) z.2 * inner ℝ (ccDiffV v v' s z) (Cyl.partialEta (ccDiffV v v' s) z)) :=
    hdc.mul (hwc.inner hpe)
  have hDcont : Continuous (fun z : Plane =>
      etaCutoff R z.2 * gradNormSq (ccDiffV v v' s) z) :=
    hφc.mul hG_cont
  have hfI : IntegrableOn (fun z : Plane =>
      deriv (etaCutoff R) z.2 * inner ℝ (ccDiffV v v' s z) (Cyl.partialEta (ccDiffV v v' s) z))
      (Cyl.cell c) :=
    hI c R hc hR0 _ hfcont hf_zero
  have hDI : IntegrableOn (fun z : Plane => etaCutoff R z.2 * gradNormSq (ccDiffV v v' s) z)
      (Cyl.cell c) :=
    hI c R hc hR0 _ hDcont hD_zero
  -- the energy of the difference: integrability and `∫_cell |w|² ≤ 4M`
  obtain ⟨hWI, hWle⟩ := hE ν c T M v v' p p' h s hs
  -- pointwise Young inequality
  have hpt : ∀ z : Plane,
      -2 * ν * (deriv (etaCutoff R) z.2 *
        inner ℝ (ccDiffV v v' s z) (Cyl.partialEta (ccDiffV v v' s) z)) ≤
        ν / 2 * (etaCutoff R z.2 * gradNormSq (ccDiffV v v' s) z) +
          2 * ν * (C₀ / R) ^ 2 * ‖ccDiffV v v' s z‖ ^ 2 := by
    intro z
    exact ccVE_young ν (C₀ / R) (Real.sqrt (etaCutoff R z.2)) (deriv (etaCutoff R) z.2)
      (inner ℝ (ccDiffV v v' s z) (Cyl.partialEta (ccDiffV v v' s) z))
      ‖Cyl.partialEta (ccDiffV v v' s) z‖ ‖ccDiffV v v' s z‖
      (gradNormSq (ccDiffV v v' s) z) (etaCutoff R z.2)
      hν.le (div_nonneg hC₀ hR0.le) (Real.sqrt_nonneg _) (Real.sq_sqrt (hφ0 z.2)) (hφ0 z.2)
      (hφd z.2) (abs_real_inner_le_norm _ _)
      (ccVE_norm_sq_le hwd z)
  -- integrate the pointwise bound over the cell
  have hmono : ∫ z in Cyl.cell c, -2 * ν * (deriv (etaCutoff R) z.2 *
        inner ℝ (ccDiffV v v' s z) (Cyl.partialEta (ccDiffV v v' s) z)) ≤
      ∫ z in Cyl.cell c, (ν / 2 * (etaCutoff R z.2 * gradNormSq (ccDiffV v v' s) z) +
        2 * ν * (C₀ / R) ^ 2 * ‖ccDiffV v v' s z‖ ^ 2) :=
    integral_mono (hfI.const_mul (-2 * ν))
      ((hDI.const_mul (ν / 2)).add (hWI.const_mul (2 * ν * (C₀ / R) ^ 2)))
      (fun z => hpt z)
  have hlhs : ∫ z in Cyl.cell c, -2 * ν * (deriv (etaCutoff R) z.2 *
        inner ℝ (ccDiffV v v' s z) (Cyl.partialEta (ccDiffV v v' s) z)) =
      -2 * ν * ∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 *
        inner ℝ (ccDiffV v v' s z) (Cyl.partialEta (ccDiffV v v' s) z) := by
    rw [integral_const_mul]
  have hsplit : ∫ z in Cyl.cell c, (ν / 2 * (etaCutoff R z.2 * gradNormSq (ccDiffV v v' s) z) +
        2 * ν * (C₀ / R) ^ 2 * ‖ccDiffV v v' s z‖ ^ 2) =
      ν / 2 * (∫ z in Cyl.cell c, etaCutoff R z.2 * gradNormSq (ccDiffV v v' s) z) +
        2 * ν * (C₀ / R) ^ 2 * (∫ z in Cyl.cell c, ‖ccDiffV v v' s z‖ ^ 2) := by
    rw [integral_add (hDI.const_mul (ν / 2)) (hWI.const_mul (2 * ν * (C₀ / R) ^ 2)),
      integral_const_mul, integral_const_mul]
  -- the constant: `2ν (C₀/R)² · 4M = 8ν C₀² M / R²`, and `K/R² ≤ K/√R` for `R ≥ 1`
  have hW2 : 2 * ν * (C₀ / R) ^ 2 * ∫ z in Cyl.cell c, ‖ccDiffV v v' s z‖ ^ 2 ≤
      2 * ν * (C₀ / R) ^ 2 * (4 * M) :=
    mul_le_mul_of_nonneg_left (hWle) (mul_nonneg (mul_nonneg (by norm_num) hν.le) (sq_nonneg _))
  have hK2 : 2 * ν * (C₀ / R) ^ 2 * (4 * M) = 8 * ν * C₀ ^ 2 * M / R ^ 2 := by
    rw [div_pow]
    ring
  have hsqrt_pos : 0 < Real.sqrt R := Real.sqrt_pos.2 hR0
  have hsqrt_R : Real.sqrt R ≤ R := by
    nlinarith [Real.sq_sqrt hR0.le, Real.sqrt_nonneg R, hR]
  have hsqrt_le : Real.sqrt R ≤ R ^ 2 := by
    nlinarith [mul_nonneg hR0.le (sub_nonneg.2 hR)]
  have hKR : 8 * ν * C₀ ^ 2 * M / R ^ 2 ≤ 8 * ν * C₀ ^ 2 * M / Real.sqrt R :=
    div_le_div_of_nonneg_left hK0 hsqrt_pos hsqrt_le
  -- assemble: `ccViscousRhs = -2νD - 2ν ∫ φ'⟨w, ∂_η w⟩`
  unfold ccViscousRhs ccDissipation
  linarith [hmono, hlhs, hsplit, hW2, hK2, hKR]

end UnforcedLeray.Short.PartI
