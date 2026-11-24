import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Sub.PartIIIb_C_near_pins_3_2_2

/-!
# `VelPhysDict` (task `PartIII-b:C/near/pins/3/2/2/1`)

Source `the November 2 reference manuscript` 2666-2668, 2683, 3309-3311.

Pointwise dictionary: with `R = ε⁻¹` and the dilated point `ε⁻¹ x`, the Axisymmetric lift `Nv`
agrees with the `B0220` meridional lift `fieldU` of the periodised profile (`Axi.chart` and
`B0220.chart` agree after dilation, `Axi.eR` and `B0220.unitR` agree and are dilation invariant,
`√(age)` is `liftA`). The a.e. transfer from `b` to `wk ∘ cellPt` on `measureH` goes through the
weighted composition `jComp.compFun_congr`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)

theorem cellRep_periodic_int {c : ℝ} (hc : 0 < c) (ξ : ℝ) (m : ℤ) :
    cellRep c (ξ + c * m) = cellRep c ξ := by
  unfold cellRep
  have h : (ξ + c * m + c / 2) / c = (ξ + c / 2) / c + m := by
    field_simp
    ring
  rw [h, Int.floor_add_intCast]
  push_cast
  ring

theorem reduceIoc_cellPt (c ξ : ℝ) (hc : 0 < c) :
    (if UnforcedLeray.B0220.reduceIoc c ξ < c / 2 then UnforcedLeray.B0220.reduceIoc c ξ
      else UnforcedLeray.B0220.reduceIoc c ξ - c) = cellRep c ξ := by
  have hr_eq : UnforcedLeray.B0220.reduceIoc c ξ = ξ + c * ((1 - ⌈ξ / c⌉ : ℤ) : ℝ) := by
    unfold UnforcedLeray.B0220.reduceIoc
    push_cast
    ring
  have hk1 : ξ / c ≤ (⌈ξ / c⌉ : ℝ) := Int.le_ceil _
  have hk2 : (⌈ξ / c⌉ : ℝ) < ξ / c + 1 := Int.ceil_lt_add_one _
  have hk1' : ξ ≤ (⌈ξ / c⌉ : ℝ) * c := by
    have := mul_le_mul_of_nonneg_right hk1 hc.le
    rwa [div_mul_cancel₀ _ hc.ne'] at this
  have hk2' : (⌈ξ / c⌉ : ℝ) * c < ξ + c := by
    have := mul_lt_mul_of_pos_right hk2 hc
    rwa [add_mul, div_mul_cancel₀ _ hc.ne', one_mul] at this
  have hr_pos : 0 < UnforcedLeray.B0220.reduceIoc c ξ := by
    rw [hr_eq]; push_cast; nlinarith
  have hr_le : UnforcedLeray.B0220.reduceIoc c ξ ≤ c := by
    rw [hr_eq]; push_cast; nlinarith
  rw [← cellRep_periodic_int hc ξ (1 - ⌈ξ / c⌉), ← hr_eq]
  by_cases h : UnforcedLeray.B0220.reduceIoc c ξ < c / 2
  · rw [if_pos h, cellRep_of_mem hc ⟨by linarith, h⟩]
  · rw [if_neg h]
    unfold cellRep
    have hf : ⌊(UnforcedLeray.B0220.reduceIoc c ξ + c / 2) / c⌋ = 1 := by
      rw [Int.floor_eq_iff]
      push_neg at h
      constructor
      · push_cast
        rw [le_div_iff₀ hc]
        linarith
      · push_cast
        rw [div_lt_iff₀ hc]
        linarith
    rw [hf]
    push_cast
    ring

theorem radius_eq_varrho (x : Space) : UnforcedLeray.B0220.radius x = Axi.ϱ x := rfl

theorem age_scale (x : Space) {ε : ℝ} (hε : 0 < ε) :
    Axi.age ε⁻¹ (ε⁻¹ • x) = UnforcedLeray.B0220.ageS x := by
  unfold Axi.age UnforcedLeray.B0220.ageS
  rw [Axi.ϱ_smul, abs_of_pos (inv_pos.2 hε), radius_eq_varrho]
  by_cases h : Axi.ϱ x = 0
  · simp [h]
  · field_simp

theorem liftA_eq_sqrt_age (x : Space) {ε : ℝ} (hε : 0 < ε) :
    √(Axi.age ε⁻¹ (ε⁻¹ • x)) = UnforcedLeray.B0220.liftA x := by
  rw [age_scale x hε]
  unfold UnforcedLeray.B0220.ageS UnforcedLeray.B0220.liftA
  rw [Real.sqrt_inv, Real.sqrt_sq (show (0 : ℝ) ≤ UnforcedLeray.B0220.radius x from Real.sqrt_nonneg _)]

theorem unitR_eq_eR (x : Space) : UnforcedLeray.B0220.unitR x = Axi.eR x := by
  ext i
  fin_cases i <;> simp [UnforcedLeray.B0220.unitR, UnforcedLeray.B0220.radius, Axi.eR, Axi.hor,
    Axi.ϱ, div_eq_inv_mul]

theorem frame_eq_frameL (x : Space) {ε : ℝ} (hε : 0 < ε) (v : Merid) :
    UnforcedLeray.B0220.frame x v = Axi.frameL (ε⁻¹ • x) v := by
  rw [UnforcedLeray.B0220.frame_apply, Axi.frameL_apply, Axi.eR_smul (inv_pos.2 hε) x,
    unitR_eq_eR]
  rfl

theorem chart_scale (x : Space) (τ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Axi.chart ε⁻¹ τ (ε⁻¹ • x) = UnforcedLeray.B0220.chart ε (x, τ) := by
  unfold Axi.chart UnforcedLeray.B0220.chart
  refine Prod.ext (age_scale x hε) (Prod.ext ?_ ?_)
  · unfold Axi.phase UnforcedLeray.B0220.cellQ
    rw [age_scale x hε]
    unfold UnforcedLeray.B0220.ageS
    rw [Real.log_inv, Real.log_pow, radius_eq_varrho]
    push_cast
    field_simp
    ring
  · unfold Axi.trans UnforcedLeray.B0220.etaCoord
    simp only [PiLp.smul_apply, smul_eq_mul, Axi.ϱ_smul, abs_of_pos (inv_pos.2 hε),
      radius_eq_varrho]
    by_cases h : Axi.ϱ x = 0
    · simp [h]
    · field_simp


theorem compFun_jComp_form {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) (f : Profile → Merid)
    (y : Space × ℝ) :
    (UnforcedLeray.B0220.jComp hε hc).compFun f y =
      UnforcedLeray.B0220.jConst ε • UnforcedLeray.B0220.fieldU ε
        (UnforcedLeray.B0220.periodize c f) y := by
  simp only [UnforcedLeray.B0220.WeightedComp.compFun, UnforcedLeray.B0220.jComp,
    LinearMap.smul_apply, UnforcedLeray.B0220.fieldU, mul_smul]
  rfl

theorem nv_eq_fieldU {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) (wk : Chart → Merid) (x : Space)
    (τ : ℝ) :
    Nv ε⁻¹ (perExt c wk) τ (ε⁻¹ • x) =
      UnforcedLeray.B0220.fieldU ε (UnforcedLeray.B0220.periodize c (fun q => wk (cellPt c q)))
        (x, τ) := by
  rcases eq_or_ne (Axi.ϱ x) 0 with h0 | h0
  · have hage : Axi.age ε⁻¹ (ε⁻¹ • x) = 0 := by simp [Axi.age, Axi.ϱ_smul, h0]
    have hl : UnforcedLeray.B0220.liftA x = 0 := by
      unfold UnforcedLeray.B0220.liftA
      have : UnforcedLeray.B0220.radius x = 0 := h0
      rw [this, inv_zero]
    unfold Axi.Nv UnforcedLeray.B0220.fieldU
    dsimp only
    rw [hage, Real.sqrt_zero, hl, zero_smul, zero_smul]
  · have key : Axi.perExt c wk (UnforcedLeray.B0220.chart ε (x, τ)) =
        UnforcedLeray.B0220.periodize c (fun q => wk (cellPt c q)) (UnforcedLeray.B0220.chart ε (x, τ)) := by
      have hif := reduceIoc_cellPt c (UnforcedLeray.B0220.cellQ ε x τ) hc
      simp only [Axi.perExt, UnforcedLeray.B0220.periodize, cellPt, UnforcedLeray.B0220.chart]
      exact congrArg wk (Prod.ext rfl (Prod.ext hif.symm rfl))
    unfold Axi.Nv UnforcedLeray.B0220.fieldU
    dsimp only
    rw [liftA_eq_sqrt_age x hε, chart_scale x τ hε, frame_eq_frameL x hε, key]

theorem velPhysDict : VelPhysDict := by
  intro p wk b hb
  have hε := p.ε_pos
  have hc := p.c_pos
  have hJ : ∀ᵐ y ∂UnforcedLeray.B0220.physMeasure p.ε p.c,
      UnforcedLeray.B0220.J hε hc b y =
        UnforcedLeray.B0220.jConst p.ε • UnforcedLeray.B0220.fieldU p.ε
          (UnforcedLeray.B0220.periodize p.c (fun q => wk (cellPt p.c q))) y := by
    filter_upwards [(UnforcedLeray.B0220.jComp hε hc).coeFn_toLI b,
      (UnforcedLeray.B0220.jComp hε hc).compFun_congr hb] with y hy1 hy2
    rw [UnforcedLeray.B0220.J, hy1, hy2, compFun_jComp_form hε hc]
  have hconst : √(2 * Real.pi) * p.ε * UnforcedLeray.B0220.jConst p.ε = 1 := by
    unfold UnforcedLeray.B0220.jConst
    exact mul_inv_cancel₀ (by positivity)
  filter_upwards [hJ] with y hy
  rw [nv_eq_fieldU hε hc wk y.1 y.2, hy, smul_smul, hconst, one_smul]

end UnforcedLeray.Short.PartIIIb.NearInst
