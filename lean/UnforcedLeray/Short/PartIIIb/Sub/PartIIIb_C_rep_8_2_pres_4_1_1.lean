import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_1

/-!
# Smoothness of the ring lift off the axis (task `PartIII-b:C/rep/8/2/pres/4/1/1`)

Source `the November 2 reference manuscript`
2666-2688 (ring lift `N_v b(τ, y) = √s (b_r e_r + b_z e_z)` at the chart point
`(s, ξ, η) = (R²/ϱ², Rτ/2 − (R/2) log s, R y₃/ϱ)`).

Off the axis `ϱ > 0`, so the age `s = R²/ϱ²` is positive and the chart maps `offAxis` into
`Ioi 0 ×ˢ univ`, where `b` is `C²`. The age, phase, transverse coordinate, `√s` and the frame
`eR` are `C²` off the axis, and the lift is a composition and product of these with `b`.
-/

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem mapsTo_snd_offAxis : MapsTo (fun x : ℝ × Space => x.2) offAxis axisᶜ :=
  fun _ hx => hx

theorem contDiffOn_age_offAxis (R : ℝ) :
    ContDiffOn ℝ 2 (fun x : ℝ × Space => UnforcedLeray.Axi.age R x.2) offAxis := by
  have h : ContDiffOn ℝ 2 (fun y : Space => R ^ 2 / UnforcedLeray.Axi.ϱ y ^ 2) axisᶜ :=
    (contDiffOn_const (c := R ^ 2)).div ((UnforcedLeray.Axi.contDiffOn_ϱ (k := 2)).pow 2)
      (fun y hy => pow_ne_zero 2 (UnforcedLeray.Axi.ϱ_ne_zero hy))
  exact h.comp contDiffOn_snd mapsTo_snd_offAxis

theorem age_ne_zero_offAxis {R : ℝ} (hR : 0 < R) {x : ℝ × Space} (hx : x ∈ offAxis) :
    UnforcedLeray.Axi.age R x.2 ≠ 0 :=
  (UnforcedLeray.Axi.age_pos hR.ne' hx).ne'

namespace PresChart411

theorem contDiffOn_chart_offAxis {R : ℝ} (hR : 0 < R) :
    ContDiffOn ℝ 2 (fun x : ℝ × Space => UnforcedLeray.Axi.chart R x.1 x.2) offAxis := by
  have hAge := contDiffOn_age_offAxis R
  have hLog : ContDiffOn ℝ 2 (fun x : ℝ × Space => Real.log (UnforcedLeray.Axi.age R x.2))
      offAxis :=
    hAge.log fun x hx => age_ne_zero_offAxis hR hx
  have hPhase : ContDiffOn ℝ 2 (fun x : ℝ × Space => UnforcedLeray.Axi.phase R x.1 x.2) offAxis := by
    have h := ((contDiffOn_const (c := R)).mul contDiffOn_fst).div_const (2 : ℝ) |>.sub
      ((contDiffOn_const (c := R / 2)).mul hLog)
    simpa only [UnforcedLeray.Axi.phase] using h
  have hcoord2 : ContDiffOn ℝ 2 (fun x : ℝ × Space => x.2 2) offAxis := by
    have h : ContDiff ℝ 2 (fun y : Space => y 2) := by fun_prop
    exact (h.comp contDiff_snd).contDiffOn
  have hϱ : ContDiffOn ℝ 2 (fun x : ℝ × Space => UnforcedLeray.Axi.ϱ x.2) offAxis :=
    (UnforcedLeray.Axi.contDiffOn_ϱ (k := 2)).comp contDiffOn_snd mapsTo_snd_offAxis
  have hTrans : ContDiffOn ℝ 2 (fun x : ℝ × Space => UnforcedLeray.Axi.trans R x.2) offAxis := by
    have h := ((contDiffOn_const (c := R)).mul hcoord2).div hϱ
      (fun _ hx => UnforcedLeray.Axi.ϱ_ne_zero (show _ ∉ UnforcedLeray.Axi.axis from hx))
    exact h
  exact hAge.prodMk (hPhase.prodMk hTrans)

end PresChart411

theorem mapsTo_chart_offAxis {R : ℝ} (hR : 0 < R) :
    MapsTo (fun x : ℝ × Space => UnforcedLeray.Axi.chart R x.1 x.2) offAxis
      (Ioi 0 ×ˢ univ) :=
  fun x hx => ⟨UnforcedLeray.Axi.age_pos hR.ne' hx, trivial⟩

/-- **Task `PartIII-b:C/rep/8/2/pres/4/1/1`.** The ring lift `Nv` of a `C²` profile `b` is
`C²` off the axis, jointly in `(τ, y)`. -/
theorem nv_contDiffOn_offAxis {R : ℝ} (hR : 0 < R) {b : ℝ × (ℝ × ℝ) → Merid} (hb : ContDiffOn ℝ 2 b (Ioi 0 ×ˢ univ)) : ContDiffOn ℝ 2 (fun x : ℝ × Space => Axi.Nv R b x.1 x.2) offAxis := by
  have hc := PresChart411.contDiffOn_chart_offAxis hR
  have hbc : ContDiffOn ℝ 2 (fun x : ℝ × Space => b (UnforcedLeray.Axi.chart R x.1 x.2)) offAxis :=
    hb.comp hc (mapsTo_chart_offAxis hR)
  have hb0 : ContDiffOn ℝ 2 (fun x : ℝ × Space => (b (UnforcedLeray.Axi.chart R x.1 x.2)) 0)
      offAxis :=
    (EuclideanSpace.proj (0 : Fin 2) : Merid →L[ℝ] ℝ).contDiff.comp_contDiffOn hbc
  have hb1 : ContDiffOn ℝ 2 (fun x : ℝ × Space => (b (UnforcedLeray.Axi.chart R x.1 x.2)) 1)
      offAxis :=
    (EuclideanSpace.proj (1 : Fin 2) : Merid →L[ℝ] ℝ).contDiff.comp_contDiffOn hbc
  have hS : ContDiffOn ℝ 2 (fun x : ℝ × Space => √(UnforcedLeray.Axi.age R x.2)) offAxis :=
    (contDiffOn_age_offAxis R).sqrt fun x hx => age_ne_zero_offAxis hR hx
  have hE : ContDiffOn ℝ 2 (fun x : ℝ × Space => UnforcedLeray.Axi.eR x.2) offAxis :=
    (UnforcedLeray.Axi.contDiffOn_eR (k := 2)).comp contDiffOn_snd mapsTo_snd_offAxis
  have hN : (fun x : ℝ × Space => Axi.Nv R b x.1 x.2) =
      fun x : ℝ × Space =>
        (√(UnforcedLeray.Axi.age R x.2) * (b (UnforcedLeray.Axi.chart R x.1 x.2)) 0) •
            UnforcedLeray.Axi.eR x.2 +
          (√(UnforcedLeray.Axi.age R x.2) * (b (UnforcedLeray.Axi.chart R x.1 x.2)) 1) •
            UnforcedLeray.Axi.e3 := by
    funext x
    simp only [Axi.Nv, UnforcedLeray.Axi.frameL_apply, smul_add, smul_smul]
  rw [hN]
  have hE3 : ContDiffOn ℝ 2 (fun _ : ℝ × Space => UnforcedLeray.Axi.e3) offAxis :=
    contDiffOn_const
  exact ((hS.mul hb0).smul hE).add ((hS.mul hb1).smul hE3)

end UnforcedLeray.Short.PartIIIb.Concrete
