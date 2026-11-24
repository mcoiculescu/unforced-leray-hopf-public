import UnforcedLeray.Short.PartI.Sub.PartI_S18_2_1

/-!
# `PartI:S18/2/1/1`: the Hilbert adjoint of `Planar.dilW` is the weighted reflection

Source `the November 2 reference manuscript`
lines 946-953.  With `ρ(z) = (1+|z|²)^M` and `s = √a`, `(J_a)^* g (z) = a⁻¹ (ρ(s z)/ρ(z)) g(s z)`.
The proof checks `⟪J_a f, g⟫ = ⟪f, T g⟫` by the change of variables `y = s z`
(`Measure.integral_comp_smul`), then identifies the adjoint by `ext_inner_left`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ComplexConjugate ENNReal NNReal

namespace UnforcedLeray.Short.PartI

/-- The ratio `ρ(√a z)/ρ(z)` with `ρ(z) = (1+|z|²)^M`. -/
def ratioR (M a : ℝ) (z : ℂ) : ℝ := (1 + ‖(√a : ℝ) • z‖ ^ 2) ^ M / (1 + ‖z‖ ^ 2) ^ M

/-- The candidate adjoint `z ↦ a⁻¹ (ρ(√a z)/ρ(z)) g(√a z)`. -/
def cand (M a : ℝ) (g : ℂ → ℂ) (z : ℂ) : ℂ :=
  (((a⁻¹ * ratioR M a z : ℝ)) : ℂ) * g ((√a : ℝ) • z)

theorem rpow_one_add_pos (M : ℝ) (z : ℂ) : 0 < (1 + ‖z‖ ^ 2) ^ M :=
  Real.rpow_pos_of_pos (by positivity) M

theorem ratioR_nonneg (M a : ℝ) (z : ℂ) : 0 ≤ ratioR M a z := by
  unfold ratioR
  exact div_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _)

theorem ratioR_le (M : ℝ) (hM : 0 ≤ M) {a : ℝ} (ha : 0 < a) (z : ℂ) :
    ratioR M a z ≤ max 1 a ^ M := by
  unfold ratioR
  have hn : ‖(√a : ℝ) • z‖ ^ 2 = a * ‖z‖ ^ 2 := by
    rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg a), mul_pow, Real.sq_sqrt ha.le]
  rw [hn, div_le_iff₀ (rpow_one_add_pos M z)]
  exact Planar.one_add_mul_sq_rpow_le hM ha.le ‖z‖

theorem ratioR_mul (M a : ℝ) (z : ℂ) :
    (1 + ‖z‖ ^ 2) ^ M * ratioR M a z = (1 + ‖(√a : ℝ) • z‖ ^ 2) ^ M := by
  have h := (rpow_one_add_pos M z).ne'
  unfold ratioR
  field_simp

theorem density_cand (M : ℝ) {a : ℝ} (ha : 0 < a) (g : ℂ → ℂ) (z : ℂ) :
    (B0008.density M z : ℝ) * ‖cand M a g z‖ ^ 2 =
      (a⁻¹ ^ 2 * ratioR M a z) *
        ((B0008.density M ((√a : ℝ) • z) : ℝ) * ‖g ((√a : ℝ) • z)‖ ^ 2) := by
  have hr := ratioR_nonneg M a z
  unfold cand
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (inv_nonneg.2 ha.le) hr)]
  rw [B0008.coe_density, B0008.coe_density, ← ratioR_mul]
  ring

theorem memLp_cand {M : ℝ} (hM : 1 < M) {a : ℝ} (ha : 0 < a) (g : Planar.L2w M) :
    MemLp (cand M a g) 2 (Planar.wMeasure M) := by
  have hs : 0 < √a := Real.sqrt_pos.2 ha
  have hsne : (√a : ℝ) ≠ 0 := hs.ne'
  have hgm : AEStronglyMeasurable (fun z : ℂ => g ((√a : ℝ) • z)) (Planar.wMeasure M) :=
    (Lp.memLp g).1.comp_quasiMeasurePreserving (Planar.qmp_smul_wMeasure (M := M) hsne)
  have hrm : Measurable (fun z : ℂ => ((a⁻¹ * ratioR M a z : ℝ) : ℂ)) := by
    unfold ratioR
    fun_prop
  have hmeas : AEStronglyMeasurable (cand M a g) (Planar.wMeasure M) :=
    hrm.aestronglyMeasurable.mul hgm
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  show Integrable (fun x => ‖cand M a g x‖ ^ 2)
    (volume.withDensity fun y => (B0008.density M y : ℝ≥0∞))
  rw [integrable_withDensity_iff_integrable_smul (B0008.measurable_density M)]
  simp only [NNReal.smul_def, smul_eq_mul]
  have hΦ : Integrable (fun z : ℂ => (B0008.density M ((√a : ℝ) • z) : ℝ) * ‖g ((√a : ℝ) • z)‖ ^ 2)
      volume :=
    (integrable_comp_smul_iff volume
      (fun y => (B0008.density M y : ℝ) * ‖g y‖ ^ 2) hsne).2 (Planar.integrable_density_sq (Lp.memLp g))
  have hfm : AEStronglyMeasurable (fun x => (B0008.density M x : ℝ) * ‖cand M a g x‖ ^ 2) volume := by
    have h1 : AEStronglyMeasurable (fun x : ℂ => (B0008.density M x : ℝ)) volume :=
      (B0008.continuous_coe_density M).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun x => ‖cand M a g x‖ ^ 2) volume :=
      ((hmeas.mono_ac (Planar.volume_ac M)).norm).pow 2
    exact h1.mul h2
  refine Integrable.mono' (hΦ.const_mul (a⁻¹ ^ 2 * max 1 a ^ M)) hfm ?_
  refine Eventually.of_forall fun z => ?_
  have hΦz : 0 ≤ (B0008.density M ((√a : ℝ) • z) : ℝ) * ‖g ((√a : ℝ) • z)‖ ^ 2 :=
    mul_nonneg (NNReal.coe_nonneg _) (sq_nonneg _)
  rw [density_cand M ha g z, Real.norm_of_nonneg
    (mul_nonneg (mul_nonneg (sq_nonneg _) (ratioR_nonneg M a z)) hΦz)]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (ratioR_le M (by linarith) ha z) (sq_nonneg _)) hΦz

/-- The `L²_M` inner product as a weighted volume integral. -/
theorem inner_L2w_eq {M : ℝ} (u v : Planar.L2w M) :
    inner ℂ u v = ∫ z, (((1 + ‖z‖ ^ 2) ^ M : ℝ) : ℂ) * inner ℂ (u z) (v z) := by
  have h : ∫ z, inner ℂ (u z) (v z) ∂(Planar.wMeasure M) =
      ∫ z, B0008.density M z • inner ℂ (u z) (v z) :=
    B0008.integral_wMeasure M (fun z => inner ℂ (u z) (v z))
  rw [MeasureTheory.L2.inner_def, h]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  dsimp only
  rw [NNReal.smul_def, Complex.real_smul, B0008.coe_density]

theorem dilWAdjFormula : DilWAdjFormula := by
  intro M hM a ha g
  have hmem := memLp_cand hM ha g
  have hs : 0 < √a := Real.sqrt_pos.2 ha
  have hsne : (√a : ℝ) ≠ 0 := hs.ne'
  have hsq : (√a : ℝ) ^ 2 = a := Real.sq_sqrt ha.le
  have hc0 : ((a⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (inv_pos.2 ha).ne'
  have hinner : ∀ f : Planar.L2w M,
      inner ℂ (Planar.dilW hM ha f) g = inner ℂ f (hmem.toLp (cand M a g)) := by
    intro f
    rw [inner_L2w_eq, inner_L2w_eq]
    have step1 : ∫ z, (((1 + ‖z‖ ^ 2) ^ M : ℝ) : ℂ) * inner ℂ (Planar.dilW hM ha f z) (g z) =
        ∫ y, (((1 + ‖y‖ ^ 2) ^ M : ℝ) : ℂ) *
          inner ℂ ((((a ^ 2)⁻¹ : ℝ) : ℂ) * f ((√a : ℝ)⁻¹ • y)) (g y) := by
      refine integral_congr_ae ((Planar.volume_ac M).ae_le
        ((Planar.coeFn_dilW hM ha f).mono fun y hy => ?_))
      simp only [hy]
    have hcv := MeasureTheory.Measure.integral_comp_smul (μ := volume)
      (fun y : ℂ => (((1 + ‖y‖ ^ 2) ^ M : ℝ) : ℂ) *
          inner ℂ ((((a ^ 2)⁻¹ : ℝ) : ℂ) * f ((√a : ℝ)⁻¹ • y)) (g y)) (√a)
    rw [Complex.finrank_real_complex, hsq, abs_of_pos (inv_pos.2 ha), Complex.real_smul] at hcv
    have hpt : ∀ z : ℂ,
        (((1 + ‖(√a : ℝ) • z‖ ^ 2) ^ M : ℝ) : ℂ) *
            inner ℂ ((((a ^ 2)⁻¹ : ℝ) : ℂ) * f ((√a : ℝ)⁻¹ • (√a : ℝ) • z)) (g ((√a : ℝ) • z)) =
          ((a⁻¹ : ℝ) : ℂ) * ((((1 + ‖z‖ ^ 2) ^ M : ℝ) : ℂ) * inner ℂ (f z) (cand M a g z)) := by
      intro z
      have hc : (((1 + ‖z‖ ^ 2) ^ M : ℝ) : ℂ) * ((ratioR M a z : ℝ) : ℂ) =
          (((1 + ‖(√a : ℝ) • z‖ ^ 2) ^ M : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul, ratioR_mul]
      rw [inv_smul_smul₀ hsne]
      unfold cand
      simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
      have hcc : (((a ^ 2)⁻¹ : ℝ) : ℂ) = ((a⁻¹ : ℝ) : ℂ) ^ 2 := by push_cast; ring
      rw [hcc]
      linear_combination (-(((a⁻¹ : ℝ) : ℂ) * ((a⁻¹ : ℝ) : ℂ)) * g ((√a : ℝ) • z) *
        (starRingEnd ℂ) (f z)) * hc
    have hA : ∫ z : ℂ, (((1 + ‖(√a : ℝ) • z‖ ^ 2) ^ M : ℝ) : ℂ) *
            inner ℂ ((((a ^ 2)⁻¹ : ℝ) : ℂ) * f ((√a : ℝ)⁻¹ • (√a : ℝ) • z)) (g ((√a : ℝ) • z)) =
        ∫ z : ℂ, ((a⁻¹ : ℝ) : ℂ) * ((((1 + ‖z‖ ^ 2) ^ M : ℝ) : ℂ) * inner ℂ (f z) (cand M a g z)) :=
      integral_congr_ae (Eventually.of_forall hpt)
    rw [integral_const_mul] at hA
    have hmain : ∫ y : ℂ, (((1 + ‖y‖ ^ 2) ^ M : ℝ) : ℂ) *
          inner ℂ ((((a ^ 2)⁻¹ : ℝ) : ℂ) * f ((√a : ℝ)⁻¹ • y)) (g y) =
        ∫ z : ℂ, (((1 + ‖z‖ ^ 2) ^ M : ℝ) : ℂ) * inner ℂ (f z) (cand M a g z) := by
      apply mul_left_cancel₀ hc0
      rw [← hcv, hA]
    rw [step1, hmain]
    refine integral_congr_ae ((Planar.volume_ac M).ae_le
      ((hmem.coeFn_toLp).mono fun z hz => ?_))
    simp only [hz]
  have hadj : ContinuousLinearMap.adjoint (Planar.dilW hM ha) g =
      hmem.toLp (cand M a g) := by
    refine ext_inner_left ℂ ?_
    intro v
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact hinner v
  rw [hadj]
  exact hmem.coeFn_toLp

end UnforcedLeray.Short.PartI
