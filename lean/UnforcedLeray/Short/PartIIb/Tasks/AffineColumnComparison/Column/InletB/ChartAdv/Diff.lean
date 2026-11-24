import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_4

/-!
# Part II-b, task `PartII-b:G4/3/4/1/B` (`chartAdv_diffAt`)

Source of record: `the November 2 reference manuscript`, SP 1919-1921, 2007-2012.
Off the axis the ring lift `(τ,y) ↦ Nv R d τ y = √s (d_r e_r(y) + d_z e₃)` at the chart point
is differentiable jointly in `(τ, y)` whenever the profile `d` is differentiable at the chart
point; the second conjunct is the restriction to the slice `τ` fixed.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- Joint differentiability of the similarity chart `(τ,y) ↦ chart R τ y` off the axis. -/
theorem chartAdv_chart_diffAt {R : ℝ} (hR : R ≠ 0) {q : ℝ × UnforcedLeray.Space}
    (hq : q.2 ∉ UnforcedLeray.Axi.axis) :
    DifferentiableAt ℝ (fun x : ℝ × UnforcedLeray.Space => UnforcedLeray.Axi.chart R x.1 x.2) q := by
  have hage : DifferentiableAt ℝ
      (fun x : ℝ × UnforcedLeray.Space => UnforcedLeray.Axi.age R x.2) q :=
    ((UnforcedLeray.Axi.hasFDerivAt_age R hq).differentiableAt).comp q differentiableAt_snd
  have hpos : UnforcedLeray.Axi.age R q.2 ≠ 0 := (UnforcedLeray.Axi.age_pos hR hq).ne'
  have hphase : DifferentiableAt ℝ
      (fun x : ℝ × UnforcedLeray.Space => UnforcedLeray.Axi.phase R x.1 x.2) q := by
    unfold UnforcedLeray.Axi.phase
    have h2 : DifferentiableAt ℝ (fun x : ℝ × UnforcedLeray.Space => R * x.1 / 2) q := by
      fun_prop
    exact h2.sub ((differentiableAt_const (R / 2)).mul (hage.log hpos))
  have htrans : DifferentiableAt ℝ
      (fun x : ℝ × UnforcedLeray.Space => UnforcedLeray.Axi.trans R x.2) q :=
    ((UnforcedLeray.Axi.hasFDerivAt_trans R hq).differentiableAt).comp q differentiableAt_snd
  unfold UnforcedLeray.Axi.chart
  exact hage.prodMk (hphase.prodMk htrans)

/-- **`PartII-b:G4/3/4/1/B`**: joint differentiability of the ring lift off the axis, and its
slice at a fixed phase time. -/
theorem chartAdv_diffAt (R : ℝ) (hR : 0 < R) (d : Coord → Axi.Merid) (τ : ℝ) (y : Space)
    (hy : y ∉ Axi.axis) (hd : DifferentiableAt ℝ d (Axi.chart R τ y)) :
    DifferentiableAt ℝ (fun x : ℝ × Space => Axi.Nv R d x.1 x.2) (τ, y) ∧
      DifferentiableAt ℝ (Axi.Nv R d τ) y := by
  have hc : DifferentiableAt ℝ (fun x : ℝ × Space => Axi.chart R x.1 x.2) (τ, y) :=
    chartAdv_chart_diffAt hR.ne' hy
  have hd' : DifferentiableAt ℝ (fun x : ℝ × Space => d (Axi.chart R x.1 x.2)) (τ, y) :=
    hd.comp (τ, y) hc
  have hage_y : DifferentiableAt ℝ (Axi.age R) y :=
    (Axi.hasFDerivAt_age R hy).differentiableAt
  have hage0 : DifferentiableAt ℝ (fun x : ℝ × Space => Axi.age R x.2) (τ, y) :=
    DifferentiableAt.comp (τ, y) (g := Axi.age R) (f := fun x : ℝ × Space => x.2) hage_y
      differentiableAt_snd
  have hage : DifferentiableAt ℝ (fun x : ℝ × Space => √(Axi.age R x.2)) (τ, y) :=
    hage0.sqrt (Axi.age_pos hR.ne' hy).ne'
  have hE_y : DifferentiableAt ℝ Axi.eR y := (Axi.hasFDerivAt_eR hy).differentiableAt
  have hE : DifferentiableAt ℝ (fun x : ℝ × Space => Axi.eR x.2) (τ, y) :=
    DifferentiableAt.comp (τ, y) (g := Axi.eR) (f := fun x : ℝ × Space => x.2) hE_y
      differentiableAt_snd
  have hp0 : DifferentiableAt ℝ (fun x : ℝ × Space => d (Axi.chart R x.1 x.2) 0) (τ, y) :=
    (EuclideanSpace.proj (0 : Fin 2) : Axi.Merid →L[ℝ] ℝ).differentiableAt.comp (τ, y) hd'
  have hp1 : DifferentiableAt ℝ (fun x : ℝ × Space => d (Axi.chart R x.1 x.2) 1) (τ, y) :=
    (EuclideanSpace.proj (1 : Fin 2) : Axi.Merid →L[ℝ] ℝ).differentiableAt.comp (τ, y) hd'
  have hfun : (fun x : ℝ × Space => Axi.Nv R d x.1 x.2) = fun x : ℝ × Space =>
      √(Axi.age R x.2) • (d (Axi.chart R x.1 x.2) 0 • Axi.eR x.2 +
        d (Axi.chart R x.1 x.2) 1 • Axi.e3) := by
    funext x
    simp only [Axi.Nv, Axi.frameL_apply]
  have h1 : DifferentiableAt ℝ (fun x : ℝ × Space => Axi.Nv R d x.1 x.2) (τ, y) := by
    rw [hfun]
    exact hage.smul ((hp0.smul hE).add (hp1.smul (differentiableAt_const _)))
  refine ⟨h1, ?_⟩
  exact h1.comp y ((differentiableAt_const τ).prodMk differentiableAt_id)

end UnforcedLeray.Short.IIb
