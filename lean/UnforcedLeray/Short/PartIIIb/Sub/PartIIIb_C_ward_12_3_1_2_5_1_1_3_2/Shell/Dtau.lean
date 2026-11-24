import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_2.Shell.Smooth

/-!
# `ShellDτ`: the phase-time derivative of the ring lift

Source `the November 2 reference manuscript`
lines 1206-1222: the phase coordinate is affine in the phase time with slope `R/2`, so
`∂_τ (b ∘ chart) = (R/2) ∂_ξ b ∘ chart` (`phase_chain`).  Off the axis the map
`(τ, x) ↦ realC (Nv R b τ x)` is differentiable, so its `dτ` is the slice derivative.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.Shell

open UnforcedLeray.Axi

theorem realC_eq_cplxV (v : UnforcedLeray.Space) : UnforcedLeray.B0412.realC v = Axi.cplxV v := by
  ext i
  simp [UnforcedLeray.B0412.realC_apply, Axi.cplxV_apply]

/-- **`ShellDτ`** (source 1206-1222). -/
theorem shellDτ : ShellDτ := by
  intro R b hR hb τ x hx
  have hnhds : axisᶜ ∈ nhds x := isOpen_compl_axis.mem_nhds hx
  have hbd : Differentiable ℝ b := hb.differentiable (by simp)
  have hage : DifferentiableAt ℝ (age R) x :=
    ((contDiffOn_age R).contDiffAt hnhds).differentiableAt (by simp)
  have hlog : DifferentiableAt ℝ (fun y => Real.log (age R y)) x :=
    ((contDiffOn_log_age hR.ne').contDiffAt hnhds).differentiableAt (by simp)
  have htr : DifferentiableAt ℝ (Axi.trans R) x :=
    ((contDiffOn_trans R).contDiffAt hnhds).differentiableAt (by simp)
  have hfr : DifferentiableAt ℝ (frameFac R) x :=
    ((contDiffOn_frameFac hR.ne').contDiffAt hnhds).differentiableAt (by simp)
  have h2 : DifferentiableAt ℝ (fun q : ℝ × UnforcedLeray.Space => q.2) (τ, x) :=
    differentiableAt_snd
  have hph : DifferentiableAt ℝ
      (fun q : ℝ × UnforcedLeray.Space => R * q.1 / 2 - (R / 2) * Real.log (age R q.2))
      (τ, x) :=
    ((by fun_prop : Differentiable ℝ (fun q : ℝ × UnforcedLeray.Space => R * q.1 / 2))
      (τ, x)).sub ((hlog.comp (τ, x) h2).const_mul _)
  have hchartJ : DifferentiableAt ℝ
      (fun q : ℝ × UnforcedLeray.Space => chart R q.1 q.2) (τ, x) :=
    (hage.comp (τ, x) h2).prodMk (hph.prodMk (htr.comp (τ, x) h2))
  have hNvJ : DifferentiableAt ℝ
      (fun q : ℝ × UnforcedLeray.Space => frameFac R q.2 (b (chart R q.1 q.2))) (τ, x) :=
    (hfr.comp (τ, x) h2).clm_apply ((hbd _).comp (τ, x) hchartJ)
  have hΦeq : (fun q : ℝ × UnforcedLeray.Space => UnforcedLeray.B0412.realC (Nv R b q.1 q.2)) =
      fun q => Axi.cplxV (frameFac R q.2 (b (chart R q.1 q.2))) := by
    funext q
    rw [realC_eq_cplxV, Nv_eq_frameFac]
  have hΦ : DifferentiableAt ℝ
      (fun q : ℝ × UnforcedLeray.Space => UnforcedLeray.B0412.realC (Nv R b q.1 q.2)) (τ, x) := by
    rw [hΦeq]
    exact Axi.cplxV.differentiableAt.comp (τ, x) hNvJ
  have hγ : HasDerivAt (fun t : ℝ => ((t, x) : ℝ × UnforcedLeray.Space))
      ((1 : ℝ), (0 : UnforcedLeray.Space)) τ :=
    (hasDerivAt_id τ).prodMk (hasDerivAt_const τ x)
  have hd1 := hΦ.hasFDerivAt.comp_hasDerivAt τ hγ
  have hpc := phase_chain (F := b) (R := R) (τ := τ) x (hbd _)
  have hd2 := ((Axi.cplxV.comp (frameFac R x)).hasFDerivAt).comp_hasDerivAt τ hpc
  have hfun : ((fun q : ℝ × UnforcedLeray.Space => UnforcedLeray.B0412.realC (Nv R b q.1 q.2)) ∘
      fun t : ℝ => ((t, x) : ℝ × UnforcedLeray.Space)) =
      (Axi.cplxV.comp (frameFac R x)) ∘ fun t => b (chart R t x) := by
    funext t
    simp only [Function.comp_apply, realC_eq_cplxV, Nv_eq_frameFac,
      ContinuousLinearMap.coe_comp']
  rw [hfun] at hd1
  show fderiv ℝ (fun q : ℝ × UnforcedLeray.Space => UnforcedLeray.B0412.realC (Nv R b q.1 q.2))
    (τ, x) (1, 0) = _
  rw [hd1.unique hd2, realC_eq_cplxV, Nv_eq_frameFac]
  rfl

end UnforcedLeray.Short.PartIIIb.Concrete.Shell
