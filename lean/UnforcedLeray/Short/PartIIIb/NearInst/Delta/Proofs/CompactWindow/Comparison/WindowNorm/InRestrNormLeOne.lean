import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Sub.PartIIIb_C_near_delta_8_2_4

/-!
# `inRestr` has norm at most one (item `PartIII-b:C/near/delta/8/2/4/1`)

Source of record `the November 2 reference manuscript` 3956-3967.
`inRestr` multiplies both components of `Z = WithLp 1 (Z₁ × ρ_b^{-1/2} H_T)` by `1_A`, and the
norm of `Z` is the sum of the component norms; each component multiplication has norm at most one.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.Blueprint.Planar

/-- Multiplication by `1_A` on `Lp` does not increase the norm. -/
theorem restrLp_norm_le_self_aux {μ : Measure Chart} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {A : Set Chart} (hA : MeasurableSet A) (f : Lp E 2 μ) :
    ‖restrLp μ E A f‖ ≤ ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  have h1 : eLpNorm ((restrLp μ E A f : Lp E 2 μ) : Chart → E) 2 μ
      = eLpNorm (A.indicator (f : Chart → E)) 2 μ := by
    apply eLpNorm_congr_ae
    filter_upwards [restrLp_ae hA f] with x hx
    rw [hx]
    by_cases h : x ∈ A <;> simp [ind, Set.indicator_apply, Pi.smul_apply, h]
  rw [h1]
  exact ENNReal.toReal_mono (Lp.memLp f).2.ne (eLpNorm_indicator_le _)

/-- The norm of `Z` is the sum of the norms of its two components. -/
theorem zsp_norm_eq_sum_aux (c mZ ρb : ℝ) (x : Zsp c mZ ρb) :
    ‖x‖ = ‖(zEquiv c mZ ρb x).1‖ + ‖(zEquiv c mZ ρb x).2‖ := by
  rw [WithLp.prod_norm_eq_of_L1]
  rfl

theorem inRestrNormLeOne_proof : InRestrNormLeOne := by
  intro c mZ ρb A hA
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun F => ?_)
  rw [one_mul, zsp_norm_eq_sum_aux c mZ ρb (inRestr c mZ ρb A F),
    zsp_norm_eq_sum_aux c mZ ρb F]
  have h1 : ‖(zEquiv c mZ ρb (inRestr c mZ ρb A F)).1‖ ≤ ‖(zEquiv c mZ ρb F).1‖ := by
    rw [zEquiv_inRestr]
    exact restrLp_norm_le_self_aux hA _
  have h2 : ‖(zEquiv c mZ ρb (inRestr c mZ ρb A F)).2‖ ≤ ‖(zEquiv c mZ ρb F).2‖ := by
    rw [zEquiv_inRestr]
    exact restrLp_norm_le_self_aux hA _
  linarith

theorem inRestrNormLeOne : InRestrNormLeOne := inRestrNormLeOne_proof

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
