import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.LerayVelocityToClassical.ClosedParamIntegral
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1_5

/-!
# Helper: the scaling integral `T_k f (z) = ∫₀¹ ½ c(t)^k f(c(t) z) dt`, `c(t) = (1+t)/2`

Used for the radial potential `u = T₀ V` (source lines 1351-1362, 1470-1480): `u(z) = ∫_{1/2}^1 V(r z) dr`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The scaling parameter `c(t) = (1+t)/2`, ranging over `[1/2, 1]`. -/
def cc (t : ℝ) : ℝ := (1 + t) / 2

/-- `T_k f (z) = ∫₀¹ ½ c(t)^k f(c(t) z) dt`. -/
def Tk (k : ℕ) (f : Space → ℝ) (z : Space) : ℝ :=
  ∫ t in (0 : ℝ)..1, (1 / 2) * cc t ^ k * f (cc t • z)

theorem contDiff_cc : ContDiff ℝ ∞ cc := by unfold cc; fun_prop

theorem contDiff_Tk (k : ℕ) {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (Tk k f) := by
  have hG : ContDiff ℝ ∞ (fun p : Space × ℝ => (1 / 2) * cc p.2 ^ k * f (cc p.2 • p.1)) := by
    have := contDiff_cc
    fun_prop
  rw [← contDiffOn_univ]
  refine contDiffOn_infty.mpr fun n => ?_
  have := UnforcedLeray.Short.PartI.ClosedParamIntegral.contDiffOn_integral_closed
    (S := (univ : Set Space)) isClosed_univ convex_univ uniqueDiffOn_univ n ℝ
    (fun z t => (1 / 2) * cc t ^ k * f (cc t • z))
    (hG.of_le (by exact_mod_cast le_top)).contDiffOn
  exact this

theorem hasFDerivAt_Tk (k : ℕ) {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (z : Space) :
    HasFDerivAt (Tk k f)
      (∫ t in (0 : ℝ)..1, ((1 / 2) * cc t ^ (k + 1)) • fderiv ℝ f (cc t • z)) z := by
  have hG : ContDiff ℝ ∞ (fun p : Space × ℝ => (1 / 2) * cc p.2 ^ k * f (cc p.2 • p.1)) := by
    have := contDiff_cc
    fun_prop
  have h := UnforcedLeray.Short.PartI.ClosedParamIntegral.hasFDerivWithinAt_integral
    (S := (univ : Set Space)) isClosed_univ convex_univ uniqueDiffOn_univ
    (G := fun z t => (1 / 2) * cc t ^ k * f (cc t • z))
    (hG.of_le (by exact_mod_cast le_top)).contDiffOn (mem_univ z)
  rw [hasFDerivWithinAt_univ] at h
  have e : ∀ t, fderivWithin ℝ (fun w => (1 / 2) * cc t ^ k * f (cc t • w)) univ z =
      ((1 / 2) * cc t ^ (k + 1)) • fderiv ℝ f (cc t • z) := by
    intro t
    rw [fderivWithin_univ]
    have h1 : HasFDerivAt (fun w : Space => f (cc t • w))
        ((fderiv ℝ f (cc t • z)).comp (cc t • ContinuousLinearMap.id ℝ Space)) z :=
      (hf.differentiable (by simp) (cc t • z)).hasFDerivAt.comp z
        ((hasFDerivAt_id z).const_smul (cc t))
    have h2 := h1.const_mul ((1 / 2) * cc t ^ k)
    rw [h2.fderiv]
    ext v
    simp [pow_succ]
    ring
  simp only [e] at h
  exact h

theorem fderiv_Tk (k : ℕ) {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (z w : Space) :
    fderiv ℝ (Tk k f) z w = Tk (k + 1) (fun y => fderiv ℝ f y w) z := by
  rw [(hasFDerivAt_Tk k hf z).fderiv]
  have hc : Continuous (fun t : ℝ => ((1 / 2) * cc t ^ (k + 1)) • fderiv ℝ f (cc t • z)) := by
    have h1 : Continuous (fun y => fderiv ℝ f y) := hf.continuous_fderiv (by simp)
    have := contDiff_cc.continuous
    fun_prop
  have := (ContinuousLinearMap.apply ℝ ℝ w).intervalIntegral_comp_comm
    (hc.intervalIntegrable (μ := volume) 0 1)
  simp only [ContinuousLinearMap.apply_apply] at this
  rw [← this]
  unfold Tk
  congr 1

end UnforcedLeray.Short.PartIIIb.Concrete
