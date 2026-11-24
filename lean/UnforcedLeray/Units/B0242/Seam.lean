import UnforcedLeray.Units.B0242.Weight
import UnforcedLeray.Analysis.GaussianVortex.PlanarDefs

/-!
# B0242, part 3: the seam inequality on the centered cell

Blueprint unit **B0242** (`unlabeled:4173`), `paper/main.tex` lines 4177–4183: "Its normal
derivative has a negative jump there, so distributionally `Δ(weight) ≤ C_m weight`. Smooth
approximations, or integration by parts separately on the two sides, give the usual weighted
diffusion energy with this favorable seam term."

This file proves the core inequality by integration by parts on the centered cell:
for a nonnegative `C²` function `φ`, `c`-periodic in `q`, with enough weighted integrability,
`∫_cell W Δφ ≤ C_m ∫_cell W φ` with `C_m = 2(4m² − 2m)` (`weak_seam_core`). Along `q` the
integration by parts is on `[-c/2, c/2]` and the two boundary terms combine into the seam term
`−2 ∂_q W(c/2⁻) φ(c/2) ≤ 0`; along `η` it is on the whole line (`integral_green_line`).

Derivatives are the library's classical partial derivatives `GaussianVortex.partialX` (`∂_q`)
and `GaussianVortex.partialY` (`∂_η`). The slice lemmas below are adapted from

compiled).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ENNReal ContDiff

namespace UnforcedLeray.B0242

open UnforcedLeray.GaussianVortex (partialX partialY)
open UnforcedLeray.B0656 (cell cellMeasure measurableSet_cell)

/-! ### Classical partial derivatives along lines (adapted from B0151/Cell.lean) -/

theorem hasDerivAt_sliceX {h : ℝ × ℝ → ℝ} (hd : Differentiable ℝ h) (x y : ℝ) :
    HasDerivAt (fun x' => h (x', y)) (partialX h (x, y)) x := by
  have : DifferentiableAt ℝ (fun x' : ℝ => h (x', y)) x :=
    (hd (x, y)).comp x (differentiableAt_id.prodMk (differentiableAt_const y))
  exact this.hasDerivAt

theorem hasDerivAt_sliceY {h : ℝ × ℝ → ℝ} (hd : Differentiable ℝ h) (x y : ℝ) :
    HasDerivAt (fun y' => h (x, y')) (partialY h (x, y)) y := by
  have : DifferentiableAt ℝ (fun y' : ℝ => h (x, y')) y :=
    (hd (x, y)).comp y ((differentiableAt_const x).prodMk differentiableAt_id)
  exact this.hasDerivAt

theorem partialX_eq_fderiv {h : ℝ × ℝ → ℝ} (hd : Differentiable ℝ h) (z : ℝ × ℝ) :
    partialX h z = fderiv ℝ h z (1, 0) := by
  have h1 : HasDerivAt (fun x' : ℝ => h (x', z.2)) (fderiv ℝ h (z.1, z.2) (1, 0)) z.1 := by
    have h0 : HasDerivAt (fun x : ℝ => (x, z.2)) ((1 : ℝ), (0 : ℝ)) z.1 :=
      (hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2)
    exact (hd (z.1, z.2)).hasFDerivAt.comp_hasDerivAt z.1 h0
  exact h1.deriv

theorem partialY_eq_fderiv {h : ℝ × ℝ → ℝ} (hd : Differentiable ℝ h) (z : ℝ × ℝ) :
    partialY h z = fderiv ℝ h z (0, 1) := by
  have h1 : HasDerivAt (fun y' : ℝ => h (z.1, y')) (fderiv ℝ h (z.1, z.2) (0, 1)) z.2 := by
    have h0 : HasDerivAt (fun y : ℝ => (z.1, y)) ((0 : ℝ), (1 : ℝ)) z.2 :=
      (hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2)
    exact (hd (z.1, z.2)).hasFDerivAt.comp_hasDerivAt z.2 h0
  exact h1.deriv

theorem contDiff_partialX {n : WithTop ℕ∞} {h : ℝ × ℝ → ℝ} (hh : ContDiff ℝ (n + 1) h) :
    ContDiff ℝ n (partialX h) := by
  have hd : Differentiable ℝ h := hh.differentiable (by simp)
  rw [show partialX h = fun z => fderiv ℝ h z (1, 0) from funext (partialX_eq_fderiv hd)]
  exact (hh.fderiv_right le_rfl).clm_apply contDiff_const

theorem contDiff_partialY {n : WithTop ℕ∞} {h : ℝ × ℝ → ℝ} (hh : ContDiff ℝ (n + 1) h) :
    ContDiff ℝ n (partialY h) := by
  have hd : Differentiable ℝ h := hh.differentiable (by simp)
  rw [show partialY h = fun z => fderiv ℝ h z (0, 1) from funext (partialY_eq_fderiv hd)]
  exact (hh.fderiv_right le_rfl).clm_apply contDiff_const

theorem partialX_add_period {c : ℝ} {h : ℝ × ℝ → ℝ} (hp : ∀ q η, h (q + c, η) = h (q, η))
    (q η : ℝ) : partialX h (q + c, η) = partialX h (q, η) := by
  change deriv (fun x => h (x, η)) (q + c) = deriv (fun x => h (x, η)) q
  have e : (fun x => h (x + c, η)) = fun x => h (x, η) := funext fun x => hp x η
  rw [← deriv_comp_add_const, e]

/-- The regularity package of a `C²` function used below. -/
structure C2Data (φ : ℝ × ℝ → ℝ) : Prop where
  cont : Continuous φ
  diff : Differentiable ℝ φ
  diffX : Differentiable ℝ (partialX φ)
  diffY : Differentiable ℝ (partialY φ)
  contX : Continuous (partialX φ)
  contY : Continuous (partialY φ)
  contXX : Continuous (partialX (partialX φ))
  contYY : Continuous (partialY (partialY φ))

theorem C2Data.of_contDiff {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) : C2Data φ := by
  have h11 : ContDiff ℝ (1 + 1) φ := by rwa [one_add_one_eq_two]
  have hX1 : ContDiff ℝ 1 (partialX φ) := contDiff_partialX h11
  have hY1 : ContDiff ℝ 1 (partialY φ) := contDiff_partialY h11
  have hX1' : ContDiff ℝ (0 + 1) (partialX φ) := by simpa using hX1
  have hY1' : ContDiff ℝ (0 + 1) (partialY φ) := by simpa using hY1
  exact ⟨hφ.continuous, hφ.differentiable (by norm_num), hX1.differentiable (by norm_num),
    hY1.differentiable (by norm_num), hX1.continuous, hY1.continuous,
    (contDiff_partialX hX1').continuous, (contDiff_partialY hY1').continuous⟩

/-! ### The classical second derivatives of the centered-cell weight -/

/-- `∂_q² (1+q²+η²)^m`. -/
def weightQQ (m : ℝ) (z : ℝ × ℝ) : ℝ := profileDD m (1 + z.2 ^ 2) z.1

/-- `∂_η² (1+q²+η²)^m`. -/
def weightHH (m : ℝ) (z : ℝ × ℝ) : ℝ := profileDD m (1 + z.1 ^ 2) z.2

/-- The seam constant `C_m = 2(4m² − 2m)`; it depends only on `m`, not on the period `c`. -/
def seamConst (m : ℝ) : ℝ := 2 * (4 * m ^ 2 - 2 * m)

theorem partialX_polyWeight (m : ℝ) (z : ℝ × ℝ) :
    partialX (polyWeight m) z = profileD m (1 + z.2 ^ 2) z.1 := by
  have e : (fun x => polyWeight m (x, z.2)) = profile m (1 + z.2 ^ 2) :=
    funext fun x => polyWeight_eq_profile_fst m x z.2
  change deriv (fun x => polyWeight m (x, z.2)) z.1 = _
  rw [e]
  exact (hasDerivAt_profile m (by positivity) z.1).deriv

theorem partialY_polyWeight (m : ℝ) (z : ℝ × ℝ) :
    partialY (polyWeight m) z = profileD m (1 + z.1 ^ 2) z.2 := by
  change deriv (fun y => profile m (1 + z.1 ^ 2) y) z.2 = _
  exact (hasDerivAt_profile m (by positivity) z.2).deriv

/-- `weightQQ` is the classical `∂_q²` of `(1+q²+η²)^m`. -/
theorem partialX_partialX_polyWeight (m : ℝ) (z : ℝ × ℝ) :
    partialX (partialX (polyWeight m)) z = weightQQ m z := by
  change deriv (fun x => partialX (polyWeight m) (x, z.2)) z.1 = _
  simp only [partialX_polyWeight]
  exact (hasDerivAt_profileD m (by positivity) z.1).deriv

/-- `weightHH` is the classical `∂_η²` of `(1+q²+η²)^m`. -/
theorem partialY_partialY_polyWeight (m : ℝ) (z : ℝ × ℝ) :
    partialY (partialY (polyWeight m)) z = weightHH m z := by
  change deriv (fun y => partialY (polyWeight m) (z.1, y)) z.2 = _
  simp only [partialY_polyWeight]
  exact (hasDerivAt_profileD m (by positivity) z.2).deriv

theorem continuous_weightQQ (m : ℝ) : Continuous (weightQQ m) :=
  continuous_profileDD_comp m (continuous_const.add (continuous_snd.pow 2)) continuous_fst
    fun _ => by positivity

theorem continuous_weightHH (m : ℝ) : Continuous (weightHH m) :=
  continuous_profileDD_comp m (continuous_const.add (continuous_fst.pow 2)) continuous_snd
    fun _ => by positivity

theorem abs_weightQQ_le {m : ℝ} (hm : 1 ≤ m) (z : ℝ × ℝ) :
    |weightQQ m z| ≤ (4 * m ^ 2 - 2 * m) * polyWeight m z := by
  rw [show z = (z.1, z.2) from rfl, polyWeight_eq_profile_fst]
  exact abs_profileDD_le hm (by nlinarith [sq_nonneg z.2]) z.1

theorem abs_weightHH_le {m : ℝ} (hm : 1 ≤ m) (z : ℝ × ℝ) :
    |weightHH m z| ≤ (4 * m ^ 2 - 2 * m) * polyWeight m z := by
  rw [show z = (z.1, z.2) from rfl, polyWeight_eq_profile_snd]
  exact abs_profileDD_le hm (by nlinarith [sq_nonneg z.1]) z.2

/-- **Classical Laplacian bound inside the cell**: `Δ(1+q²+η²)^m ≤ C_m (1+q²+η²)^m`,
with `C_m` independent of `c`. -/
theorem laplacian_polyWeight_le {m : ℝ} (hm : 1 ≤ m) (z : ℝ × ℝ) :
    weightQQ m z + weightHH m z ≤ seamConst m * polyWeight m z := by
  have h1 := (abs_weightQQ_le hm z)
  have h2 := (abs_weightHH_le hm z)
  have := le_abs_self (weightQQ m z)
  have := le_abs_self (weightHH m z)
  simp only [seamConst]
  linarith

/-! ### Fubini on the cell -/

theorem cellMeasure_eq_prod (c : ℝ) :
    cellMeasure c = (volume.restrict (Ioo (-(c / 2)) (c / 2))).prod (volume : Measure ℝ) := by
  rw [cellMeasure, B0656.cell, Measure.volume_eq_prod, ← Measure.prod_restrict,
    Measure.restrict_univ]

/-- Integrand domination by the weighted function. -/
theorem integrable_of_abs_le {μ : Measure (ℝ × ℝ)} {F G : ℝ × ℝ → ℝ} (K : ℝ)
    (hG : Integrable G μ) (hF : Continuous F) (hle : ∀ z, |F z| ≤ K * |G z|) :
    Integrable F μ :=
  Integrable.mono' (hG.norm.const_mul K) hF.aestronglyMeasurable
    (ae_of_all _ fun z => by simpa [Real.norm_eq_abs] using hle z)

/-- **The core seam inequality.** Let `m ≥ 1`, `c > 0`, and let `φ ≥ 0` be `C²` and
`c`-periodic in `q`, with `W φ`, `W ∂_η φ`, `W ∂_q²φ`, `W ∂_η²φ` integrable on the centered
cell, `W = (1+q²+η²)^m`. Then `∫_cell W Δφ ≤ C_m ∫_cell W φ`. -/
theorem weak_seam_core {m c : ℝ} (hm : 1 ≤ m) (hc : 0 < c) {φ : ℝ × ℝ → ℝ}
    (hφ : C2Data φ) (hper : ∀ q η, φ (q + c, η) = φ (q, η)) (hnn : ∀ z, 0 ≤ φ z)
    (i0 : Integrable (fun z => polyWeight m z * φ z) (cellMeasure c))
    (i1 : Integrable (fun z => polyWeight m z * partialY φ z) (cellMeasure c))
    (i2 : Integrable (fun z => polyWeight m z * partialX (partialX φ) z) (cellMeasure c))
    (i3 : Integrable (fun z => polyWeight m z * partialY (partialY φ) z) (cellMeasure c)) :
    ∫ z, polyWeight m z * (partialX (partialX φ) z + partialY (partialY φ) z) ∂cellMeasure c ≤
      seamConst m * ∫ z, polyWeight m z * φ z ∂cellMeasure c := by
  have hm0 : 0 ≤ m := by linarith
  have hC : 0 ≤ 4 * m ^ 2 - 2 * m := by nlinarith
  have iQ : Integrable (fun z => weightQQ m z * φ z) (cellMeasure c) := by
    refine integrable_of_abs_le (4 * m ^ 2 - 2 * m) i0 ((continuous_weightQQ m).mul hφ.cont)
      fun z => ?_
    rw [abs_mul, abs_mul, abs_of_pos (polyWeight_pos m z), ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (abs_weightQQ_le hm z) (abs_nonneg _)
  have iH : Integrable (fun z => weightHH m z * φ z) (cellMeasure c) := by
    refine integrable_of_abs_le (4 * m ^ 2 - 2 * m) i0 ((continuous_weightHH m).mul hφ.cont)
      fun z => ?_
    rw [abs_mul, abs_mul, abs_of_pos (polyWeight_pos m z), ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (abs_weightHH_le hm z) (abs_nonneg _)
  -- the `q`-direction: integration by parts on `[-c/2, c/2]` with the seam term
  have hQ : ∫ z, polyWeight m z * partialX (partialX φ) z ∂cellMeasure c ≤
      ∫ z, weightQQ m z * φ z ∂cellMeasure c := by
    rw [cellMeasure_eq_prod] at i2 iQ ⊢
    rw [integral_prod_symm _ i2, integral_prod_symm _ iQ]
    refine integral_mono i2.integral_prod_right iQ.integral_prod_right fun η => ?_
    dsimp only
    have hle : -(c / 2) ≤ c / 2 := by linarith
    rw [← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hle, ← intervalIntegral.integral_of_le hle]
    simp only [polyWeight_eq_profile_fst, weightQQ]
    have hhalf : -(c / 2) + c = c / 2 := by ring
    refine seam_interval (g := fun x => φ (x, η)) (g' := fun x => partialX φ (x, η))
      (g'' := fun x => partialX (partialX φ) (x, η)) hm0 (by positivity) (by linarith)
      (fun x => hasDerivAt_sliceX hφ.diff x η) (fun x => hasDerivAt_sliceX hφ.diffX x η)
      (hφ.contXX.comp (continuous_id.prodMk continuous_const)) ?_ ?_ (hnn _)
    · have := hper (-(c / 2)) η
      rw [hhalf] at this
      exact this.symm
    · have := partialX_add_period hper (-(c / 2)) η
      rw [hhalf] at this
      exact this.symm
  -- the `η`-direction: integration by parts on the whole line
  have hH : ∫ z, polyWeight m z * partialY (partialY φ) z ∂cellMeasure c =
      ∫ z, weightHH m z * φ z ∂cellMeasure c := by
    rw [cellMeasure_eq_prod] at i0 i1 i3 iH ⊢
    rw [integral_prod _ i3, integral_prod _ iH]
    refine integral_congr_ae ?_
    filter_upwards [i0.prod_right_ae, i1.prod_right_ae, i3.prod_right_ae, iH.prod_right_ae]
      with q h0 h1 h3 h4
    have ha : (0 : ℝ) < 1 + q ^ 2 := by positivity
    have ha1 : (1 : ℝ) ≤ 1 + q ^ 2 := by nlinarith [sq_nonneg q]
    have hsl : Continuous fun η : ℝ => φ (q, η) :=
      hφ.cont.comp (continuous_const.prodMk continuous_id)
    have hD : Integrable fun η => profileD m (1 + q ^ 2) η * φ (q, η) := by
      refine Integrable.mono' (h0.norm.const_mul (2 * m))
        ((continuous_profileD m ha).mul hsl).aestronglyMeasurable (ae_of_all _ fun η => ?_)
      simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (polyWeight_pos m (q, η))]
      rw [← mul_assoc, polyWeight_eq_profile_snd]
      exact mul_le_mul_of_nonneg_right (abs_profileD_le hm0 ha1 η) (abs_nonneg _)
    have hG := integral_green_line (f := profile m (1 + q ^ 2)) (f' := profileD m (1 + q ^ 2))
      (f'' := profileDD m (1 + q ^ 2)) (g := fun η => φ (q, η))
      (g' := fun η => partialY φ (q, η)) (g'' := fun η => partialY (partialY φ) (q, η))
      (hasDerivAt_profile m ha) (hasDerivAt_profileD m ha)
      (fun η => hasDerivAt_sliceY hφ.diff q η) (fun η => hasDerivAt_sliceY hφ.diffY q η)
      (h1.sub hD) (h3.sub h4)
    have h0' : ∫ η, (polyWeight m (q, η) * partialY (partialY φ) (q, η) -
        weightHH m (q, η) * φ (q, η)) = 0 := hG
    rw [integral_sub h3 h4] at h0'
    linarith
  have hsplit : ∫ z, polyWeight m z * (partialX (partialX φ) z + partialY (partialY φ) z)
      ∂cellMeasure c = (∫ z, polyWeight m z * partialX (partialX φ) z ∂cellMeasure c) +
        ∫ z, polyWeight m z * partialY (partialY φ) z ∂cellMeasure c := by
    rw [← integral_add i2 i3]
    congr 1
    funext z
    ring
  have hfin : (∫ z, weightQQ m z * φ z ∂cellMeasure c) + ∫ z, weightHH m z * φ z ∂cellMeasure c ≤
      seamConst m * ∫ z, polyWeight m z * φ z ∂cellMeasure c := by
    rw [← integral_add iQ iH, ← integral_const_mul]
    refine integral_mono (iQ.add iH) (i0.const_mul _) fun z => ?_
    have h1 := mul_le_mul_of_nonneg_right (laplacian_polyWeight_le hm z) (hnn z)
    calc weightQQ m z * φ z + weightHH m z * φ z = (weightQQ m z + weightHH m z) * φ z := by
          ring
      _ ≤ seamConst m * polyWeight m z * φ z := h1
      _ = seamConst m * (polyWeight m z * φ z) := by ring
  rw [hsplit]
  linarith

/-! ### Test functions on the cylinder -/

/-- A continuous function vanishing for `|η| ≥ R` is integrable on the centered cell. -/
theorem integrable_cell_of_bounded {c R : ℝ} {F : ℝ × ℝ → ℝ} (hF : Continuous F)
    (hR : ∀ z : ℝ × ℝ, R ≤ |z.2| → F z = 0) : Integrable F (cellMeasure c) := by
  have hK : IsCompact (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R) := isCompact_Icc.prod isCompact_Icc
  have h1 : IntegrableOn F (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R) :=
    hF.continuousOn.integrableOn_compact hK
  have h2 : IntegrableOn F (cell c) := by
    refine h1.of_forall_sdiff_eq_zero (measurableSet_cell c) fun z hz => hR z ?_
    obtain ⟨hzc, hzK⟩ := hz
    have hz1 : z.1 ∈ Icc (-(c / 2)) (c / 2) := Ioo_subset_Icc_self hzc.1
    have hz2 : z.2 ∉ Icc (-R) R := fun h => hzK ⟨hz1, h⟩
    by_contra hlt
    exact hz2 (abs_le.1 (not_le.1 hlt).le)
  exact h2

end UnforcedLeray.B0242
