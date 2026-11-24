import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_2

/-!
# `NvPd0`: the first Cartesian derivative of the ring lift (`PartIII-b:C/rep/8/2/1/2`, (N0))

Source `the November 2 reference manuscript`,
lines 5466-5476 (`radial_chain`), 2073-2077 (ring lift `N_v`).

At `y` with `y 1 = 0`, `y 0 > 0` we have `eR y = e₀`, `ϱ y = y 0`, and `∂_{y₁} N_v` is the
derivative of the scalar factors `√age · b_k ∘ chart` along `eR y` (the frame `eR` has zero
derivative along itself, `eRD_eR_zero`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Axi

/-- Derivative of the `k`-th component of a meridional profile. -/
theorem fderiv_apply_comp_local {F : ℝ × (ℝ × ℝ) → Merid} {p : ℝ × (ℝ × ℝ)} (k : Fin 2)
    (hF : DifferentiableAt ℝ F p) (v : ℝ × (ℝ × ℝ)) :
    fderiv ℝ (fun x => F x k) p v = fderiv ℝ F p v k := by
  have h := (EuclideanSpace.proj k : Merid →L[ℝ] ℝ).hasFDerivAt.comp p hF.hasFDerivAt
  have h2 : fderiv ℝ (fun x => F x k) p = (EuclideanSpace.proj k : Merid →L[ℝ] ℝ).comp (fderiv ℝ F p) :=
    h.fderiv
  rw [h2]
  rfl

theorem dQ_comp_local {F : ℝ × (ℝ × ℝ) → Merid} {p : ℝ × (ℝ × ℝ)} (k : Fin 2)
    (hF : DifferentiableAt ℝ F p) : UnforcedLeray.Axi.dQ (fun x => F x k) p = UnforcedLeray.Axi.dQ F p k := by
  unfold UnforcedLeray.Axi.dQ
  exact fderiv_apply_comp_local k hF _

theorem dS_comp_local {F : ℝ × (ℝ × ℝ) → Merid} {p : ℝ × (ℝ × ℝ)} (k : Fin 2)
    (hF : DifferentiableAt ℝ F p) : UnforcedLeray.Axi.dS (fun x => F x k) p = UnforcedLeray.Axi.dS F p k := by
  unfold UnforcedLeray.Axi.dS
  exact fderiv_apply_comp_local k hF _

theorem dEta_comp_local {F : ℝ × (ℝ × ℝ) → Merid} {p : ℝ × (ℝ × ℝ)} (k : Fin 2)
    (hF : DifferentiableAt ℝ F p) : UnforcedLeray.Axi.dEta (fun x => F x k) p = UnforcedLeray.Axi.dEta F p k := by
  unfold UnforcedLeray.Axi.dEta
  exact fderiv_apply_comp_local k hF _

/-- `eRD y (eR y) = 0` (the frame `eR` is constant along rays). -/
theorem eRD_eR_zero_local {y : Space} (hy : y ∉ axis) : eRD y (eR y) = 0 := by
  have hρ := ϱ_ne_zero hy
  have h1 : hor (eR y) = (ϱ y)⁻¹ • hor y := by
    ext i
    fin_cases i <;> simp [eR, hor_apply_zero, hor_apply_one, hor_apply_two]
  rw [eRD_apply, ϱD_eR hy, h1, one_smul]
  have h2 : eR y = (ϱ y)⁻¹ • hor y := rfl
  rw [← h2, sub_self, smul_zero]

/-- The scalar factor `√s · F(chart)` has a derivative whose value on `eR y` is `s` times the
radial combination (`radial_chain`, with `∂_ρ √s = -R⁻¹ s`). -/
theorem sqrt_mul_chart_hasFDerivAt_local (F : ℝ × (ℝ × ℝ) → ℝ) {R τ : ℝ} (hR : 0 < R)
    {y : Space} (hy : y ∉ axis) (hF : DifferentiableAt ℝ F (chart R τ y)) :
    ∃ L : Space →L[ℝ] ℝ, HasFDerivAt (fun z => √(age R z) * F (chart R τ z)) L y ∧
      L (eR y) = age R y * (UnforcedLeray.Axi.dQ F (chart R τ y) - R⁻¹ * (F (chart R τ y) +
        2 * age R y * UnforcedLeray.Axi.dS F (chart R τ y) + trans R y * UnforcedLeray.Axi.dEta F (chart R τ y))) := by
  have hR0 : R ≠ 0 := hR.ne'
  have hage0 : age R y ≠ 0 := (age_pos hR0 hy).ne'
  have hC : HasFDerivAt (fun z => F (chart R τ z)) ((fderiv ℝ F (chart R τ y)).comp (chartD R y)) y :=
    hF.hasFDerivAt.comp y (hasFDerivAt_chart hR0 τ hy)
  have hS : HasFDerivAt (fun z => √(age R z)) ((1 / (2 * √(age R y))) • ageD R y) y :=
    (hasFDerivAt_age R hy).sqrt hage0
  refine ⟨_, hS.mul hC, ?_⟩
  have hrad := radial_chain hR hy hF
  rw [fderiv_comp_chart_apply hR0 hy hF] at hrad
  have hageD : ageD R y (eR y) = -(2 * R ^ 2 / ϱ y ^ 3) := by
    simp [ageD, ϱD_eR hy]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul]
  rw [hrad, hageD, sqrt_age hR hy]
  simp only [age, smul_eq_mul]
  have hϱ0 : ϱ y ≠ 0 := ϱ_ne_zero hy
  generalize ϱ y = r at hϱ0 ⊢
  field_simp
  ring

/-- `merSp` in the basis `e₀ = e_r`, `e₂ = e_z` at azimuth zero. -/
theorem merSp_eq_local (D : Merid) : merSp D = D 0 • coordinateVector 0 + D 1 • e3 := by
  ext j
  fin_cases j <;> simp [merSp, vecSp, coordinateVector, e3, EuclideanSpace.single_apply]

/-- **`NvPd0`.** -/
theorem nvPd0 : NvPd0 := by
  intro R τ b y hR hy0 hy1 hb
  have hy : y ∉ axis := fun h => hy0.ne' h.1
  have hϱ : ϱ y = y 0 := by
    unfold ϱ
    rw [hy1, show y 0 ^ 2 + (0 : ℝ) ^ 2 = y 0 ^ 2 by ring]
    exact Real.sqrt_sq hy0.le
  have hEr : eR y = coordinateVector 0 := by
    ext j
    fin_cases j <;> simp [eR_apply_zero, eR_apply_one, eR_apply_two, hϱ, hy1, hy0.ne',
      coordinateVector]
  have hF0 : DifferentiableAt ℝ (fun x => b x 0) (chart R τ y) :=
    (EuclideanSpace.proj (0 : Fin 2) : Merid →L[ℝ] ℝ).differentiableAt.comp (chart R τ y) hb
  have hF1 : DifferentiableAt ℝ (fun x => b x 1) (chart R τ y) :=
    (EuclideanSpace.proj (1 : Fin 2) : Merid →L[ℝ] ℝ).differentiableAt.comp (chart R τ y) hb
  obtain ⟨L0, hL0, hL0v⟩ := sqrt_mul_chart_hasFDerivAt_local (fun x => b x 0) hR hy hF0
  obtain ⟨L1, hL1, hL1v⟩ := sqrt_mul_chart_hasFDerivAt_local (fun x => b x 1) hR hy hF1
  have hNv : Nv R b τ = fun z => (√(age R z) * b (chart R τ z) 0) • eR z +
      (√(age R z) * b (chart R τ z) 1) • e3 := by
    funext z
    simp only [Nv, frameL_apply, smul_add, smul_smul]
  have hTot : HasFDerivAt (fun z => (√(age R z) * b (chart R τ z) 0) • eR z +
      (√(age R z) * b (chart R τ z) 1) • e3)
      (((√(age R y) * b (chart R τ y) 0) • eRD y + L0.smulRight (eR y)) +
        L1.smulRight e3) y :=
    (hL0.smul (hasFDerivAt_eR hy)).add (hL1.smul_const e3)
  beta_reduce at hL0v hL1v
  unfold physPd
  rw [hNv, ← hEr, hTot.fderiv]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply,
    smul_apply, eRD_eR_zero_local hy, smul_zero, zero_add, smul_eq_mul]
  rw [hL0v, hL1v, dQ_comp_local 0 hb, dQ_comp_local 1 hb, dS_comp_local 0 hb, dS_comp_local 1 hb,
    dEta_comp_local 0 hb, dEta_comp_local 1 hb, hEr, merSp_eq_local]
  simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  module

end UnforcedLeray.Short.PartIIIb.Concrete
