import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_4_1_1_2_org
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Normed.Operator.Prod

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

/-- The weight coordinate `x ↦ x.2.1` as a continuous linear map. -/
def wProj : ℝ × (ℝ × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

theorem wProj_apply (x : ℝ × (ℝ × ℝ)) : wProj x = x.2.1 := rfl

theorem norm_wProj_le : ‖wProj‖ ≤ 1 := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have h1 : ‖ContinuousLinearMap.fst ℝ ℝ ℝ‖ ≤ 1 := ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ
  have h2 : ‖ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)‖ ≤ 1 := ContinuousLinearMap.norm_snd_le ℝ ℝ (ℝ × ℝ)
  exact mul_le_one₀ h1 (norm_nonneg _) h2

theorem isOpen_parPos : IsOpen parPos :=
  isOpen_lt continuous_const (continuous_fst.comp continuous_snd)

/-- Derivatives of `G ∘ w` on the half space are those of `G` at `w` (up to `‖wProj‖ ≤ 1`). -/
theorem norm_iteratedFDeriv_comp_w_le (G G' : ℝ → ℝ) (hG : ContDiffOn ℝ ∞ G (Ioi 0))
    (hEq : EqOn G G' (Ioi 0)) (i : ℕ) (x : ℝ × (ℝ × ℝ)) (hx : 0 < x.2.1) :
    ‖iteratedFDeriv ℝ i (fun y : ℝ × (ℝ × ℝ) => G y.2.1) x‖ ≤
      ‖iteratedFDeriv ℝ i G' x.2.1‖ := by
  have hxp : x ∈ parPos := hx
  have hmem : wProj x ∈ Ioi 0 := hx
  have hpre : wProj ⁻¹' Ioi 0 = parPos := rfl
  have hi : (i : WithTop ℕ∞) ≤ ∞ := by
    exact_mod_cast le_top
  have h1 : iteratedFDeriv ℝ i (fun y : ℝ × (ℝ × ℝ) => G y.2.1) x =
      iteratedFDerivWithin ℝ i (G ∘ wProj) parPos x :=
    (iteratedFDerivWithin_of_isOpen i isOpen_parPos hxp).symm
  have h2 := ContinuousLinearMap.iteratedFDerivWithin_comp_right wProj hG
    (uniqueDiffOn_Ioi 0) (by rw [hpre]; exact isOpen_parPos.uniqueDiffOn) hmem hi
  rw [hpre] at h2
  have h3 : iteratedFDerivWithin ℝ i G (Ioi 0) (wProj x) =
      iteratedFDeriv ℝ i G' x.2.1 := by
    rw [iteratedFDerivWithin_congr hEq hmem i,
      iteratedFDerivWithin_of_isOpen i isOpen_Ioi hmem]
    rfl
  rw [h1]
  have h4 : iteratedFDerivWithin ℝ i (G ∘ wProj) parPos x =
      (iteratedFDeriv ℝ i G' x.2.1).compContinuousLinearMap fun _ => wProj := by
    rw [h2, h3]
  rw [h4]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hp : ∏ _ : Fin i, ‖wProj‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => norm_wProj_le)
  exact mul_le_of_le_one_right (norm_nonneg _) hp

/-- The one-variable power law: `‖∂^i (c s^r)(t)‖ = |c| |P_i(r)| t^(r - i)` on `t > 0`. -/
theorem norm_iteratedFDeriv_const_mul_rpow (c r : ℝ) (i : ℕ) (t : ℝ) (ht : 0 < t) :
    ‖iteratedFDeriv ℝ i (fun s : ℝ => c * s ^ r) t‖ =
      |c| * |(descPochhammer ℝ i).eval r| * t ^ (r - (i : ℝ)) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have hd : ContDiffAt ℝ i (fun s : ℝ => s ^ r) t :=
    Real.contDiffAt_rpow_const_of_ne (n := i) ht.ne'
  rw [iteratedDeriv_const_mul c hd, iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const]
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos ht _)]
  ring

/-- **Jets of the weights** `R/w` and `R/√w` on `0 < w ≤ 1` (SP 1897-2663, parity chart). -/
theorem parWeightJet : UnforcedLeray.Short.IIb.ParWeightJet := by
  intro R
  have hG1 : ContDiffOn ℝ ∞ (fun t : ℝ => R / t) (Ioi 0) :=
    contDiffOn_const.div contDiffOn_id (fun t ht => ne_of_gt ht)
  have hG2 : ContDiffOn ℝ ∞ (fun t : ℝ => R / Real.sqrt t) (Ioi 0) :=
    contDiffOn_const.div
      (fun t ht => (Real.contDiffAt_sqrt (n := ∞) (ne_of_gt ht)).contDiffWithinAt)
      (fun t ht => (Real.sqrt_pos.2 ht).ne')
  have hE1 : EqOn (fun t : ℝ => R / t) (fun t : ℝ => R * t ^ (-1 : ℝ)) (Ioi 0) := by
    intro t _
    show R / t = R * t ^ (-1 : ℝ)
    rw [Real.rpow_neg_one, div_eq_mul_inv]
  have hE2 : EqOn (fun t : ℝ => R / Real.sqrt t) (fun t : ℝ => R * t ^ (-(1 / 2) : ℝ)) (Ioi 0) := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    show R / Real.sqrt t = R * t ^ (-(1 / 2) : ℝ)
    rw [Real.sqrt_eq_rpow, Real.rpow_neg ht'.le, div_eq_mul_inv]
  refine ⟨?_, ?_, ?_⟩
  · exact hG1.comp wProj.contDiff.contDiffOn (fun x hx => hx)
  · exact hG2.comp wProj.contDiff.contDiffOn (fun x hx => hx)
  intro n
  refine ⟨(∑ i ∈ Finset.range (n + 1), |R| * |(descPochhammer ℝ i).eval (-1)|) +
    ∑ i ∈ Finset.range (n + 1), |R| * |(descPochhammer ℝ i).eval (-(1 / 2))|, ?_⟩
  intro x hx hx1 i hi
  have hxpos : 0 < x.2.1 := hx
  have hi' : i ∈ Finset.range (n + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le hi)
  have hA : |R| * |(descPochhammer ℝ i).eval (-1)| ≤
      ∑ j ∈ Finset.range (n + 1), |R| * |(descPochhammer ℝ j).eval (-1)| :=
    Finset.single_le_sum (f := fun j => |R| * |(descPochhammer ℝ j).eval (-1)|)
      (fun j _ => by positivity) hi'
  have hB : |R| * |(descPochhammer ℝ i).eval (-(1 / 2))| ≤
      ∑ j ∈ Finset.range (n + 1), |R| * |(descPochhammer ℝ j).eval (-(1 / 2))| :=
    Finset.single_le_sum (f := fun j => |R| * |(descPochhammer ℝ j).eval (-(1 / 2))|)
      (fun j _ => by positivity) hi'
  have hA0 : 0 ≤ ∑ j ∈ Finset.range (n + 1), |R| * |(descPochhammer ℝ j).eval (-1)| :=
    Finset.sum_nonneg (fun j _ => by positivity)
  have hB0 : 0 ≤ ∑ j ∈ Finset.range (n + 1), |R| * |(descPochhammer ℝ j).eval (-(1 / 2))| :=
    Finset.sum_nonneg (fun j _ => by positivity)
  constructor
  · have e1 := norm_iteratedFDeriv_comp_w_le (fun t : ℝ => R / t)
      (fun t : ℝ => R * t ^ (-1 : ℝ)) hG1 hE1 i x hxpos
    have e2 := norm_iteratedFDeriv_const_mul_rpow R (-1) i x.2.1 hxpos
    have hp : 0 ≤ x.2.1 ^ (-(1 : ℝ) - (i : ℝ)) := Real.rpow_nonneg hxpos.le _
    calc ‖iteratedFDeriv ℝ i (fun y : ℝ × (ℝ × ℝ) => R / y.2.1) x‖
        ≤ ‖iteratedFDeriv ℝ i (fun t : ℝ => R * t ^ (-1 : ℝ)) x.2.1‖ := e1
      _ = |R| * |(descPochhammer ℝ i).eval (-1)| * x.2.1 ^ (-(1 : ℝ) - (i : ℝ)) := e2
      _ ≤ (∑ j ∈ Finset.range (n + 1), |R| * |(descPochhammer ℝ j).eval (-1)| +
            ∑ j ∈ Finset.range (n + 1), |R| * |(descPochhammer ℝ j).eval (-(1 / 2))|) *
          x.2.1 ^ (-(1 : ℝ) - (i : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ hp
        linarith
  · have e1 := norm_iteratedFDeriv_comp_w_le (fun t : ℝ => R / Real.sqrt t)
      (fun t : ℝ => R * t ^ (-(1 / 2) : ℝ)) hG2 hE2 i x hxpos
    have e2 := norm_iteratedFDeriv_const_mul_rpow R (-(1 / 2)) i x.2.1 hxpos
    have hp : 0 ≤ x.2.1 ^ (-(1 / 2 : ℝ) - (i : ℝ)) := Real.rpow_nonneg hxpos.le _
    calc ‖iteratedFDeriv ℝ i (fun y : ℝ × (ℝ × ℝ) => R / Real.sqrt y.2.1) x‖
        ≤ ‖iteratedFDeriv ℝ i (fun t : ℝ => R * t ^ (-(1 / 2) : ℝ)) x.2.1‖ := e1
      _ = |R| * |(descPochhammer ℝ i).eval (-(1 / 2))| * x.2.1 ^ (-(1 / 2 : ℝ) - (i : ℝ)) := e2
      _ ≤ (∑ j ∈ Finset.range (n + 1), |R| * |(descPochhammer ℝ j).eval (-1)| +
            ∑ j ∈ Finset.range (n + 1), |R| * |(descPochhammer ℝ j).eval (-(1 / 2))|) *
          x.2.1 ^ (-(1 / 2 : ℝ) - (i : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ hp
        linarith

end UnforcedLeray.Short.IIb
