import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.PairDeriv.Cont
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Sub_T12_7_5

/-!
# Part II-b, task `PartII-b:T12/7/5/2` (`dfe_deqPdCont`): continuity of the smoothed pairing

Source of record: `the November 2 reference manuscript`, lines 1923-1927.
For `s > t` both `z ↦ deqSmooth ν Ψ i t s z` and `z ↦ deqSmoothD ν Ψ i t s z` are continuous:
each is a convolution of the heat kernel (age `ν(s-t) > 0`) with a bounded continuous function of
the planar variable (`Ψ_i(s, ·)`, resp. the combination `∂_sΨ_i + νΔΨ_i` at time `s`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem dfe_deqPdCont : UnforcedLeray.Short.IIb.dfe_DeqPdCont := by
  intro ν t hν ht Ψ hΨ i s hs
  have hθ : 0 < ν * (s - t) := mul_pos hν (by linarith)
  have hF : ContDiff ℝ ∞ (fun x : Coord => Ψ x i) := (hΨ.smooth i).smooth
  have hFc : HasCompactSupport (fun x : Coord => Ψ x i) := (hΨ.smooth i).compact
  constructor
  · -- the smoothed test `deqSmooth`
    have hc : Continuous (fun y : ℝ × ℝ => Ψ (s, y) i) :=
      hF.continuous.comp (continuous_const.prodMk continuous_id)
    obtain ⟨M, hM⟩ := hF.continuous.bounded_above_of_compact_support hFc
    refine Continuous.congr
      (deqpc_conv_cont hθ (fun y : ℝ × ℝ => Ψ (s, y) i) hc M (fun y => hM (s, y))) (fun z => ?_)
    simp only [deqSmooth, flatHeat_kernel_eq hθ]
  · -- the derivative-side test `deqSmoothD`
    have c0 : HasCompactSupport (fun x : Coord => cpd 0 (fun y => Ψ y i) x) :=
      HasCompactSupport.fderiv_apply ℝ hFc (cdir 0)
    have c1 : HasCompactSupport (fun y : Coord => cpd 1 (fun x => Ψ x i) y) :=
      HasCompactSupport.fderiv_apply ℝ hFc (cdir 1)
    have c2 : HasCompactSupport (fun y : Coord => cpd 2 (fun x => Ψ x i) y) :=
      HasCompactSupport.fderiv_apply ℝ hFc (cdir 2)
    have c11 : HasCompactSupport (fun x : Coord => cpd 1 (fun y => cpd 1 (fun x => Ψ x i) y) x) :=
      HasCompactSupport.fderiv_apply ℝ c1 (cdir 1)
    have c22 : HasCompactSupport (fun x : Coord => cpd 2 (fun y => cpd 2 (fun x => Ψ x i) y) x) :=
      HasCompactSupport.fderiv_apply ℝ c2 (cdir 2)
    have hgcs : HasCompactSupport (fun x : Coord =>
        cpd 0 (fun y => Ψ y i) x +
          ν * (cpd 1 (fun y => cpd 1 (fun x => Ψ x i) y) x +
            cpd 2 (fun y => cpd 2 (fun x => Ψ x i) y) x)) :=
      c0.add ((c11.add c22).mul_left)
    have hc0 : Continuous (fun x : Coord => cpd 0 (fun y => Ψ y i) x) :=
      (deqT_cpd_contDiff hF 0).continuous
    have hc11 : Continuous (fun x : Coord => cpd 1 (fun y => cpd 1 (fun x => Ψ x i) y) x) :=
      (deqT_cpd_contDiff (deqT_cpd_contDiff hF 1) 1).continuous
    have hc22 : Continuous (fun x : Coord => cpd 2 (fun y => cpd 2 (fun x => Ψ x i) y) x) :=
      (deqT_cpd_contDiff (deqT_cpd_contDiff hF 2) 2).continuous
    have hgc : Continuous (fun x : Coord =>
        cpd 0 (fun y => Ψ y i) x +
          ν * (cpd 1 (fun y => cpd 1 (fun x => Ψ x i) y) x +
            cpd 2 (fun y => cpd 2 (fun x => Ψ x i) y) x)) :=
      hc0.add (continuous_const.mul (hc11.add hc22))
    obtain ⟨M, hM⟩ := hgc.bounded_above_of_compact_support hgcs
    have hc' : Continuous (fun y : ℝ × ℝ =>
        cpd 0 (fun y => Ψ y i) (s, y) +
          ν * (cpd 1 (fun y => cpd 1 (fun x => Ψ x i) y) (s, y) +
            cpd 2 (fun y => cpd 2 (fun x => Ψ x i) y) (s, y))) :=
      hgc.comp (continuous_const.prodMk continuous_id)
    refine Continuous.congr
      (deqpc_conv_cont hθ _ hc' M (fun y => hM (s, y))) (fun z => ?_)
    simp only [deqSmoothD, flatHeat_kernel_eq hθ]

end UnforcedLeray.Short.IIb
