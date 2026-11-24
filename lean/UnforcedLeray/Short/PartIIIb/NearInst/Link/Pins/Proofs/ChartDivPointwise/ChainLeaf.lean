import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_4_1

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst

open MeasureTheory UnforcedLeray.Axi UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem chainLeaf : ChainLeaf := by
  intro R τ y hR hy F hF p hp
  subst hp
  have hR0 : R ≠ 0 := hR.ne'
  -- joint differentiability of the chart in `(τ, y)` off the axis
  have hΦd : DifferentiableAt ℝ (fun x : ℝ × Space => Axi.chart R x.1 x.2) (τ, y) := by
    have hage : DifferentiableAt ℝ (fun x : ℝ × Space => Axi.age R x.2) (τ, y) :=
      DifferentiableAt.comp (f := fun x : ℝ × Space => x.2) (g := Axi.age R) (τ, y)
        (Axi.hasFDerivAt_age R hy).differentiableAt differentiableAt_snd
    have hpos : Axi.age R y ≠ 0 := (Axi.age_pos hR0 hy).ne'
    have hphase : DifferentiableAt ℝ (fun x : ℝ × Space => Axi.phase R x.1 x.2) (τ, y) := by
      unfold Axi.phase
      have h2 : DifferentiableAt ℝ (fun x : ℝ × Space => R * x.1 / 2) (τ, y) := by
        fun_prop
      exact h2.sub ((differentiableAt_const (R / 2)).mul (hage.log hpos))
    have htrans : DifferentiableAt ℝ (fun x : ℝ × Space => Axi.trans R x.2) (τ, y) :=
      DifferentiableAt.comp (f := fun x : ℝ × Space => x.2) (g := Axi.trans R) (τ, y)
        (Axi.hasFDerivAt_trans R hy).differentiableAt differentiableAt_snd
    unfold Axi.chart
    exact hage.prodMk (hphase.prodMk htrans)
  -- the derivative in the `y`-direction at a fixed phase time is `chartD`
  have hcomp := hΦd.hasFDerivAt.comp y ((hasFDerivAt_const τ y).prodMk (hasFDerivAt_id y))
  have hslice0 : HasFDerivAt (fun y' : Space => Axi.chart R τ y') (chartD R y) y :=
    hasFDerivAt_chart hR0 τ hy
  have hL := hcomp.unique hslice0
  have hv : ∀ v : Space, fderiv ℝ (fun x : ℝ × Space => Axi.chart R x.1 x.2) (τ, y) (0, v) =
      chartD R y v := by
    intro v
    have h := congrArg (fun T : Space →L[ℝ] ℝ × (ℝ × ℝ) => T v) hL
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      zero_apply, ContinuousLinearMap.id_apply] at h
    exact h
  have hG : DifferentiableAt ℝ (fun x : ℝ × Space => F (Axi.chart R x.1 x.2)) (τ, y) :=
    hF.comp (τ, y) hΦd
  refine ⟨hG, fun v => ?_⟩
  have hGd : HasFDerivAt (fun x : ℝ × Space => F (Axi.chart R x.1 x.2))
      ((fderiv ℝ F (Axi.chart R τ y)).comp
        (fderiv ℝ (fun x : ℝ × Space => Axi.chart R x.1 x.2) (τ, y))) (τ, y) :=
    hF.hasFDerivAt.comp (τ, y) hΦd.hasFDerivAt
  rw [hGd.fderiv, ContinuousLinearMap.comp_apply, hv v, chartD_apply, Axi.sqrt_age hR hy]
  rw [Axi.clm_triple]
  simp only [Axi.dS, Axi.dQ, Axi.dEta, Axi.age, Axi.trans, smul_eq_mul]
  have hρ := Axi.ϱ_ne_zero hy
  field_simp
  ring

end UnforcedLeray.Short.PartIIIb.NearInst
