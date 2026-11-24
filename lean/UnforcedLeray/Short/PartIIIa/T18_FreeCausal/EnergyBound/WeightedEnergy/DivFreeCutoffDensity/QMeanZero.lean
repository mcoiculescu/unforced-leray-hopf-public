import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_1
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.DivFreeCutoffDensity.QPrimDeriv
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.DivFreeCutoffDensity.QPeriodic
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.DivFreeCutoffDensity.QL2

/-!
# Part III-a, task `PartIII-a:T18/3/1/1/5`: the `q`-mean of `φ₁` vanishes

Target (`Sub/T18_3_1_1.lean`): `DfcQMeanZero`. Source of record:
`the November 2 reference manuscript`, lines 3541-3552.

`M(η) = ∫_{-c/2}^{c/2} φ₁(t, η) dt` is differentiable with `M' = ∫ ∂_η φ₁ = -∫ ∂_q φ₀ = 0`
(`DfcQPrimDeriv`, divergence freeness, `DfcQPeriodic`), hence constant. `M ∈ L²(ℝ)` by `DfcQL2`,
so the constant is `0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem dfcQMeanZero : UnforcedLeray.Short.IIIa.DfcQMeanZero := by
  unfold DfcQMeanZero
  intro c hc φ hφ
  have hf : ContDiff ℝ ∞ (fun x : ℝ × ℝ => φ x 1) := hφ.smooth 1
  have hfc : Continuous (fun x : ℝ × ℝ => φ x 1) := hf.continuous
  have hL2 : MemLp (fun x : ℝ × ℝ => φ x 1) 2 (volume.restrict (B0579.cell c)) := hφ.l2 1
  have hMd : Differentiable ℝ (dfcQInt c (fun x : ℝ × ℝ => φ x 1)) :=
    ((dfcQPrimSmooth c hc _ hf).2).differentiable (by simp)
  have hMder : ∀ η : ℝ, deriv (dfcQInt c (fun x : ℝ × ℝ => φ x 1)) η = 0 := by
    intro η
    rw [(dfcQPrimDeriv c hc _ hf).2.2 η]
    have hfun : B0579.pd 1 (fun x : ℝ × ℝ => φ x 1) =
        fun x => -(B0579.pd 0 (fun y : ℝ × ℝ => φ y 0) x) := by
      funext x
      have := hφ.divFree x
      linarith
    have hneg : dfcQInt c (fun x => -(B0579.pd 0 (fun y : ℝ × ℝ => φ y 0) x)) η =
        -(dfcQInt c (B0579.pd 0 (fun y : ℝ × ℝ => φ y 0)) η) := by
      unfold dfcQInt
      exact intervalIntegral.integral_neg
    have hz : dfcQInt c (B0579.pd 0 (fun y : ℝ × ℝ => φ y 0)) η = 0 :=
      (dfcQPeriodic c hc _ (hφ.smooth 0) (fun x => hφ.periodic x 0)).1 η
    rw [hfun, hneg, hz, neg_zero]
  have hconst := is_const_of_deriv_eq_zero hMd hMder
  have hLp := (dfcQL2 c hc _ hfc hL2).1
  have hLp' : MemLp (fun _ : ℝ => dfcQInt c (fun x : ℝ × ℝ => φ x 1) 0) 2 volume := by
    convert hLp using 1
    exact funext fun η => (hconst η 0).symm
  have hz0 : dfcQInt c (fun x : ℝ × ℝ => φ x 1) 0 = 0 := by
    rcases (memLp_const_iff (p := 2) (by norm_num) (by norm_num)).1 hLp' with h | h
    · exact h
    · exfalso
      simp at h
  intro η
  rw [hconst η 0, hz0]

end UnforcedLeray.Short.IIIa
