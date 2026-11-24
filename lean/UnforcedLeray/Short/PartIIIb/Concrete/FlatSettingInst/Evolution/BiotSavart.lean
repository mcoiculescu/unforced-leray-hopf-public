import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Evolution.Leaves

/-!
# Biot-Savart velocities of reflected vorticities (source 3236-3240, 287-288)

Source of record: `the November 2 reference manuscript` (73 pages).

`K_c = ∇^⊥Δ⁻¹` commutes with `x ↦ -x` up to the sign of a vector field:

* `isCylTest_comp_neg`, `pd_comp_neg`: reflected cylinder tests;
* `biotSavartReflect : BiotSavartReflect`;
* `stripVelRefl_of`: `StripVelRefl` from the Biot-Savart field of the state space
  (`Exist.BiotSavartFieldAll`, accepted `PartIII-a:T21/3/4`) and uniqueness of the velocity
  (`IIIa.CTE.BiotSavartUnique`, proved as `IIIa.CTE.isBiotSavart_unique`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Evol

open UnforcedLeray.Short.IIIa.Exist (vortFn cplx stripVel BiotSavartFieldAll)

/-- A reflected cylinder test is a cylinder test. -/
theorem isCylTest_comp_neg {c : ℝ} {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest c ψ) :
    B0579.IsCylTest c (fun y => ψ (-y)) where
  smooth := hψ.smooth.comp contDiff_neg
  periodic x := by
    have h := hψ.periodic (-x.1 - c, -x.2)
    show ψ (-(x.1 + c, x.2)) = ψ (-x)
    have e1 : (-(x.1 + c, x.2) : ℝ × ℝ) = (-x.1 - c, -x.2) := by
      ext
      · simp only [Prod.fst_neg]
        ring
      · simp only [Prod.snd_neg]
    have e2 : (-x : ℝ × ℝ) = ((-x.1 - c, -x.2).1 + c, (-x.1 - c, -x.2).2) := by
      ext
      · simp only [Prod.fst_neg]
        ring
      · simp only [Prod.snd_neg]
    rw [e1, e2, h]
  band := by
    obtain ⟨R, hR⟩ := hψ.band
    refine ⟨R, fun x hx => hR (-x) ?_⟩
    simpa [Prod.snd_neg, abs_neg] using hx

/-- `∂_j(ψ(-·))(x) = -(∂_jψ)(-x)`. -/
theorem pd_comp_neg {ψ : ℝ × ℝ → ℝ} (hψ : Differentiable ℝ ψ) (j : Fin 2) (x : ℝ × ℝ) :
    B0579.pd j (fun y => ψ (-y)) x = -B0579.pd j ψ (-x) := by
  have h : HasFDerivAt (fun y => ψ (-y))
      ((fderiv ℝ ψ (-x)).comp (-ContinuousLinearMap.id ℝ (ℝ × ℝ))) x :=
    (hψ (-x)).hasFDerivAt.comp x (hasFDerivAt_id x).neg
  simp only [B0579.pd, h.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.id_apply, map_neg]

/-- **`BiotSavartReflect`**: `x ↦ -u(-x)` is a Biot-Savart velocity of `x ↦ ω(-x)`. -/
theorem biotSavartReflect : BiotSavartReflect := by
  intro c ω u hu
  obtain ⟨h1, h2, h3⟩ := hu
  refine ⟨fun j => ?_, fun ψ hψ => ?_, fun ψ hψ => ?_⟩
  · exact ((h1 j).comp_measurePreserving (mp_neg_cell c)).neg
  · have key := h2 _ (isCylTest_comp_neg hψ)
    have e := integral_cell_comp_neg (c := c) (fun x =>
      u x 0 * (B0579.pd 0 (fun y => ψ (-y)) x : ℂ) + u x 1 * (B0579.pd 1 (fun y => ψ (-y)) x : ℂ))
    rw [← e] at key
    simp only [pd_comp_neg hψ.differentiable, neg_neg] at key
    rw [← key]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    push_cast
    ring
  · have key := h3 _ (isCylTest_comp_neg hψ)
    have e1 := integral_cell_comp_neg (c := c) (fun x => ω x * (ψ (-x) : ℂ))
    have e2 := integral_cell_comp_neg (c := c) (fun x =>
      u x 0 * (B0579.pd 1 (fun y => ψ (-y)) x : ℂ) - u x 1 * (B0579.pd 0 (fun y => ψ (-y)) x : ℂ))
    rw [← e1, ← e2] at key
    simp only [pd_comp_neg hψ.differentiable, neg_neg] at key
    rw [key]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    push_cast
    ring

/-- **`StripVelRefl`** from the Biot-Savart field of the state space and uniqueness of the
Biot-Savart velocity. -/
theorem stripVelRefl_of (hBS : BiotSavartFieldAll) (hU : IIIa.CTE.BiotSavartUnique) :
    StripVelRefl := by
  intro c m _ hm w
  have hc : 0 < c := Fact.out
  have h1 := hBS c m hm (reflV hm w)
  obtain ⟨a, b, d⟩ := biotSavartReflect c _ _ (hBS c m hm w)
  have h2 : IIIa.IsBiotSavart c (cplx (vortFn hm (reflV hm w)))
      (fun x j => -stripVel hm w (-x) j) := by
    refine ⟨a, b, fun ψ hψ => ?_⟩
    rw [← d ψ hψ]
    refine integral_congr_ae ?_
    filter_upwards [vortFn_reflV hm w] with x hx
    simp only [cplx, hx]
  filter_upwards [hU c hc _ _ _ h1 h2] with x hx j
  exact congrFun hx j

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Evol
