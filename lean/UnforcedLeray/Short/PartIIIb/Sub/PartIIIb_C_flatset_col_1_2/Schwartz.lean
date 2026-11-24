import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_1_2.Reduce
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_1_2.Gauss
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.TemperateGrowth

/-!
# `FlatTermSchwartz` from a Gaussian Schwartz function (decomposition of `PartIII-b:C/flatset/col/1/2`)

Source of record `the November 2 reference manuscript`: 4976, 4988.

`ftF1 a B`, `ftF2 a B` are `ftPh a u v` times polynomials in `(u, v)`, and
`ftPh a u v = (a^2)⁻¹ * exp (-(u^2+v^2)/(4a))`.  Mathlib has no Gaussian element of the Schwartz
space on `ℝ × ℝ`; this file reduces `FlatTermSchwartz` to that single fact (the hypothesis `hG`
below), by multiplying the Gaussian Schwartz function by polynomials of temperate growth.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

namespace FlatTermAux

theorem flatTermSchwartz_of_gauss
    (hG : ∀ b : ℝ, 0 < b → ∃ g : SchwartzMap (ℝ × ℝ) ℝ,
      ∀ y : ℝ × ℝ, g y = Real.exp (-(b * (y.1 ^ 2 + y.2 ^ 2)))) :
    FlatTermSchwartz := by
  intro a B ha
  obtain ⟨g, hg⟩ := hG (1 / (4 * a)) (by positivity)
  have hX : (fun y : ℝ × ℝ => y.1).HasTemperateGrowth :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasTemperateGrowth
  have hY : (fun y : ℝ × ℝ => y.2).HasTemperateGrowth :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasTemperateGrowth
  have hC : ∀ c : ℝ, (fun _ : ℝ × ℝ => c).HasTemperateGrowth :=
    fun c => Function.HasTemperateGrowth.const c
  -- the quadratic form `Q = y · B_mer y`, a polynomial of temperate growth
  have hQ : (fun y : ℝ × ℝ => B 0 0 * y.1 ^ 2 + (B 0 2 + B 2 0) * (y.1 * y.2) + B 2 2 * y.2 ^ 2)
      |>.HasTemperateGrowth :=
    (((hC (B 0 0)).mul (hX.pow 2)).add (((hC (B 0 2 + B 2 0)).mul (hX.mul hY)))).add
      ((hC (B 2 2)).mul (hY.pow 2))
  obtain ⟨P1, hP1e⟩ : ∃ P1 : ℝ × ℝ → ℝ, P1 = fun y : ℝ × ℝ =>
      (a ^ 2)⁻¹ * ((B 0 0 * y.1 ^ 2 + (B 0 2 + B 2 0) * (y.1 * y.2) + B 2 2 * y.2 ^ 2)
        * (1 / (2 * a)) * y.2
        + (-(B 2 0) * y.1 - B 2 2 * y.2 - B 0 0 * y.2 + B 0 2 * y.1)) := ⟨_, rfl⟩
  obtain ⟨P2, hP2e⟩ : ∃ P2 : ℝ × ℝ → ℝ, P2 = fun y : ℝ × ℝ =>
      (a ^ 2)⁻¹ * (-(B 0 0 * y.1 ^ 2 + (B 0 2 + B 2 0) * (y.1 * y.2) + B 2 2 * y.2 ^ 2)
          * (1 / (2 * a)) * y.1
        + (B 0 0 * y.1 + B 0 2 * y.2) + (-(B 2 0) * y.2 + B 2 2 * y.1)) := ⟨_, rfl⟩
  have hP1 : Function.HasTemperateGrowth P1 := by
    rw [hP1e]
    exact (hC _).mul
      (((hQ.mul (hC (1 / (2 * a)))).mul hY).add
        ((((hC (-(B 2 0))).mul hX).sub ((hC (B 2 2)).mul hY)).sub ((hC (B 0 0)).mul hY) |>.add
          ((hC (B 0 2)).mul hX)))
  have hP2 : Function.HasTemperateGrowth P2 := by
    rw [hP2e]
    exact (hC _).mul
      ((((hQ.neg.mul (hC (1 / (2 * a)))).mul hX).add
          (((hC (B 0 0)).mul hX).add ((hC (B 0 2)).mul hY))).add
        (((hC (-(B 2 0))).mul hY).add ((hC (B 2 2)).mul hX)))
  refine ⟨SchwartzMap.smulLeftCLM ℝ P1 g, SchwartzMap.smulLeftCLM ℝ P2 g, fun y => ?_, fun y => ?_⟩
  · rw [SchwartzMap.smulLeftCLM_apply_apply hP1 g y, hg y, hP1e]
    simp only [smul_eq_mul, ftF1, ftPh, ftKap, ftQf]
    have e : Real.exp (-((1 / (4 * a)) * (y.1 ^ 2 + y.2 ^ 2)))
        = Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / (4 * a)) := congrArg Real.exp (by ring)
    rw [e]
    ring
  · rw [SchwartzMap.smulLeftCLM_apply_apply hP2 g y, hg y, hP2e]
    simp only [smul_eq_mul, ftF2, ftPh, ftKap, ftQf]
    have e : Real.exp (-((1 / (4 * a)) * (y.1 ^ 2 + y.2 ^ 2)))
        = Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / (4 * a)) := congrArg Real.exp (by ring)
    rw [e]
    ring

end FlatTermAux

/-- Source 4976, 4988: the flat curl terms are Schwartz. -/
theorem flatTermSchwartz : FlatTermSchwartz :=
  FlatTermAux.flatTermSchwartz_of_gauss FlatTermAux.gauss_schwartz

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
