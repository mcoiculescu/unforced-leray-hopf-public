import UnforcedLeray.Short.PartIIIa.Sub.T21_c2

/-!
# Part III-a, task `PartIII-a:T21/c2/1` (`fmeScale`): the change of variables `x = √a y`

Source of record: `the November 2 reference manuscript`, lines 2937-2958.
Plane scaling `y ↦ r y` maps `cell (c/r)` onto `cell c` with Jacobian `r²`; no measurability of `g`
is needed (measurable embedding + `lintegral_withDensity_eq_lintegral_mul_non_measurable`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- Change of variables on the plane for the scaling `y ↦ r y`, on the cells. -/
theorem fmeScale_lintegral (r c : ℝ) (hr : 0 < r) (G : ℝ × ℝ → ℝ≥0∞) :
    ∫⁻ y in B0579.cell (c / r), G (r * y.1, r * y.2) =
      ENNReal.ofReal ((r ^ 2)⁻¹) * ∫⁻ x in B0579.cell c, G x := by
  have hemb : MeasurableEmbedding (fun y : ℝ × ℝ => r • y) :=
    (Homeomorph.smulOfNeZero r hr.ne').measurableEmbedding
  have h1 : ∫⁻ y in B0579.cell c, G y ∂(Measure.map (fun y : ℝ × ℝ => r • y) volume) =
      ∫⁻ x in (fun y : ℝ × ℝ => r • y) ⁻¹' B0579.cell c, G (r • x) := by
    rw [hemb.restrict_map, hemb.lintegral_map]
  have hpre : (fun y : ℝ × ℝ => r • y) ⁻¹' B0579.cell c = B0579.cell (c / r) := by
    ext y
    simp only [B0579.cell, mem_preimage, mem_prod, mem_Ico, mem_univ, and_true, Prod.smul_fst,
      smul_eq_mul]
    have e1 : -(c / 2) ≤ r * y.1 ↔ -(c / r / 2) ≤ y.1 := by
      rw [show c / r / 2 = (c / 2) / r by ring, show -(c / 2 / r) = -(c / 2) / r from (neg_div _ _).symm,
        div_le_iff₀ hr, mul_comm]
    have e2 : r * y.1 < c / 2 ↔ y.1 < c / r / 2 := by
      rw [show c / r / 2 = (c / 2) / r by ring, lt_div_iff₀ hr, mul_comm]
    exact and_congr e1 e2
  rw [hpre, Measure.map_addHaar_smul (μ := (volume : Measure (ℝ × ℝ))) hr.ne'] at h1
  rw [Measure.restrict_smul, lintegral_smul_measure] at h1
  have hfr : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
  rw [hfr] at h1
  have h2 : ENNReal.ofReal |(r ^ 2)⁻¹| = ENNReal.ofReal ((r ^ 2)⁻¹) := by
    rw [abs_of_nonneg (by positivity)]
  rw [h2] at h1
  exact h1.symm

theorem fmeScale_enorm_sq (x : ℝ) : ‖((x : ℝ) : ℂ)‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (x ^ 2) := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
    ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num), Real.rpow_two, sq_abs]

theorem fmeScale : FmeScale := by
  intro c m a hc ha g hg
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hss : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  set s := Real.sqrt a with hs_def
  unfold xNorm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by simp)]
  unfold B0579.cellMeasure
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _
    (B0579.measurable_density m).coe_nnreal_ennreal
    (Filter.Eventually.of_forall fun x => ENNReal.coe_lt_top)]
  have hpt : (fun y : ℝ × ℝ => ((fun x => (B0579.density m x : ℝ≥0∞)) *
        fun y => ‖JscaleInv a (fun x => ((g x : ℝ) : ℂ)) y‖ₑ ^ (2 : ENNReal).toReal) y) =
      fun y : ℝ × ℝ => (fun x : ℝ × ℝ => ENNReal.ofReal (B0579.jb (x.1 / s, x.2 / s) ^ m) *
        ENNReal.ofReal ((a ^ 2 * g x) ^ 2)) (s * y.1, s * y.2) := by
    funext y
    have h3 : JscaleInv a (fun x => ((g x : ℝ) : ℂ)) y = ((a ^ 2 * g (s * y.1, s * y.2) : ℝ) : ℂ) := by
      unfold JscaleInv; push_cast; rfl
    simp only [Pi.mul_apply, h3, ENNReal.toReal_ofNat, fmeScale_enorm_sq]
    rw [mul_div_cancel_left₀ _ hs.ne', mul_div_cancel_left₀ _ hs.ne']
    rfl
  rw [hpt]
  unfold cellLen
  rw [← hs_def]
  rw [fmeScale_lintegral s c hs (fun x : ℝ × ℝ => ENNReal.ofReal (B0579.jb (x.1 / s, x.2 / s) ^ m) *
    ENNReal.ofReal ((a ^ 2 * g x) ^ 2))]
  set w : ℝ × ℝ → ℝ := fun x => (1 + (x.1 ^ 2 + x.2 ^ 2) / a) ^ m with hw
  have hG : ∀ x : ℝ × ℝ, ENNReal.ofReal (B0579.jb (x.1 / s, x.2 / s) ^ m) *
      ENNReal.ofReal ((a ^ 2 * g x) ^ 2) = ENNReal.ofReal (a ^ 4 * (g x ^ 2 * w x)) := by
    intro x
    have hj : B0579.jb (x.1 / s, x.2 / s) = 1 + (x.1 ^ 2 + x.2 ^ 2) / a := by
      unfold B0579.jb
      simp only [div_pow, hss]
      ring
    have hwn : 0 ≤ w x := Real.rpow_nonneg (by rw [← hj]; exact (B0579.jb_pos _).le) _
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (B0579.jb_pos _).le _), hj]
    congr 1
    simp only [hw]
    ring
  simp only [hG]
  have hint : Integrable (fun x => a ^ 4 * (g x ^ 2 * w x)) (volume.restrict (B0579.cell c)) :=
    hg.const_mul _
  have hnn : 0 ≤ᵐ[volume.restrict (B0579.cell c)] fun x => a ^ 4 * (g x ^ 2 * w x) :=
    Filter.Eventually.of_forall fun x => by
      have : 0 ≤ w x := Real.rpow_nonneg (by positivity) _
      positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, ← ENNReal.ofReal_mul (by positivity)]
  have hI : ∫ x in B0579.cell c, a ^ 4 * (g x ^ 2 * w x) = a ^ 4 * movEnergy c m a g := by
    rw [integral_const_mul]; rfl
  have hE : 0 ≤ movEnergy c m a g :=
    integral_nonneg fun x => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by positivity) _)
  rw [hss, hI, ENNReal.toReal_ofNat, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
    Real.sqrt_eq_rpow]
  congr 2
  field_simp

end UnforcedLeray.Short.IIIa
