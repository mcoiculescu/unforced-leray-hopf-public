import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_lp_org
import UnforcedLeray.Cons.L2.BackgroundConcrete.Fields

/-!
# Smoothness of the raw lift off the axis, self-contained copy
(helper of `PartIII-b:C/rep/8/2/pres/4/2/lp/6`)

Source `the November 2 reference manuscript`
2076-2077, 5200-5201.  This is the content of `Sub/PartIII-b_C_rep_8_2_pres_4_1_1`, `_4_1_2`,
`_4_1_3`, reproduced in the private namespace `PwSplitRaw` so that it does not depend on the
module `Sub/PartIII-b_C_rep_8_2_pres_4_1` (which currently fails to compile).
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace PwSplitRaw

/-- The (open) set of `(τ, y)` off the axis. -/
def offAxis : Set (ℝ × Space) := {x | x.2 ∉ axis}

theorem isOpen_offAxis : IsOpen offAxis := by
  have h : IsClosed {x : ℝ × Space | x.2 ∈ axis} := by
    have : {x : ℝ × Space | x.2 ∈ axis} = {x | x.2 0 = 0} ∩ {x | x.2 1 = 0} := by
      ext x; simp [axis]
    rw [this]
    refine IsClosed.inter (isClosed_eq ?_ continuous_const) (isClosed_eq ?_ continuous_const)
    · exact (EuclideanSpace.proj (0 : Fin 3)).continuous.comp continuous_snd
    · exact (EuclideanSpace.proj (1 : Fin 3)).continuous.comp continuous_snd
  exact h.isOpen_compl

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

theorem mapsTo_chart_offAxis {R : ℝ} (hR : 0 < R) :
    MapsTo (fun x : ℝ × Space => UnforcedLeray.Axi.chart R x.1 x.2) offAxis
      (Ioi 0 ×ˢ univ) :=
  fun x hx => ⟨UnforcedLeray.Axi.age_pos hR.ne' hx, trivial⟩

/-- **Task `PartIII-b:C/rep/8/2/pres/4/1/1`.** The ring lift `Nv` of a `C²` profile `b` is
`C²` off the axis, jointly in `(τ, y)`. -/
theorem nv_contDiffOn_offAxis {R : ℝ} (hR : 0 < R) {b : ℝ × (ℝ × ℝ) → Merid} (hb : ContDiffOn ℝ 2 b (Ioi 0 ×ˢ univ)) : ContDiffOn ℝ 2 (fun x : ℝ × Space => Axi.Nv R b x.1 x.2) offAxis := by
  have hc := contDiffOn_chart_offAxis hR
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


section S2
open UnforcedLeray.Cons.C03
open UnforcedLeray.Cyl

/-- The one-variable `η`-derivative of a slice is a joint partial derivative. -/
theorem rp_deriv_eta {ψ : ℝ → ℝ × ℝ → ℝ} {s ξ η : ℝ}
    (hd : DifferentiableAt ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) (s, (ξ, η))) :
    deriv (fun t => ψ s (ξ, t)) η =
      fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) (s, (ξ, η)) (0, (0, 1)) := by
  have hγ : HasDerivAt (fun t : ℝ => ((s, (ξ, t)) : ℝ × (ℝ × ℝ)))
      ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) η :=
    (hasDerivAt_const η s).prodMk ((hasDerivAt_const η ξ).prodMk (hasDerivAt_id η))
  exact (HasFDerivAt.comp_hasDerivAt η hd.hasFDerivAt hγ).deriv

/-- The one-variable `s`-derivative of a slice is a joint partial derivative. -/
theorem rp_deriv_s {ψ : ℝ → ℝ × ℝ → ℝ} {s ξ η : ℝ}
    (hd : DifferentiableAt ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) (s, (ξ, η))) :
    deriv (fun t => ψ t (ξ, η)) s =
      fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) (s, (ξ, η)) (1, (0, 0)) := by
  have hγ : HasDerivAt (fun t : ℝ => ((t, (ξ, η)) : ℝ × (ℝ × ℝ)))
      ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) s :=
    (hasDerivAt_id s).prodMk ((hasDerivAt_const s ξ).prodMk (hasDerivAt_const s η))
  exact (HasFDerivAt.comp_hasDerivAt s hd.hasFDerivAt hγ).deriv

/-- Pointwise formula for `raisedStream` through joint partial derivatives of `ψ`. -/
theorem rp_raised_eq {ψ : ℝ → ℝ × ℝ → ℝ} {O : Set (ℝ × (ℝ × ℝ))} (hO : IsOpen O)
    (hG : ContDiffOn ℝ 3 (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) O) {p : ℝ × (ℝ × ℝ)} (hp : p ∈ O) :
    raisedStream ψ p.1 p.2.1 p.2.2 =
      ψ p.1 p.2 - (p.2.2 * fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) p (0, (0, 1)) +
        2 * p.1 * fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) p (1, (0, 0))) := by
  have hd : DifferentiableAt ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) (p.1, (p.2.1, p.2.2)) :=
    (hG.differentiableOn (by norm_num)).differentiableAt (hO.mem_nhds hp)
  unfold raisedStream
  rw [rp_deriv_eta hd, rp_deriv_s hd]

/-- `raisedStream` is `C²` on an open set where `ψ` is `C³` jointly. -/
theorem rp_raised_contDiffOn {ψ : ℝ → ℝ × ℝ → ℝ} {O : Set (ℝ × (ℝ × ℝ))} (hO : IsOpen O)
    (hG : ContDiffOn ℝ 3 (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) O) :
    ContDiffOn ℝ 2 (fun p : ℝ × (ℝ × ℝ) => raisedStream ψ p.1 p.2.1 p.2.2) O := by
  have hG2 : ContDiffOn ℝ 2 (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) O := hG.of_le (by norm_num)
  have hFd : ContDiffOn ℝ 2
      (fun x : ℝ × (ℝ × ℝ) => fderiv ℝ (fun y : ℝ × (ℝ × ℝ) => ψ y.1 y.2) x) O :=
    hG.fderiv_of_isOpen hO (by norm_num)
  have hD1 : ContDiffOn ℝ 2
      (fun x : ℝ × (ℝ × ℝ) => fderiv ℝ (fun y : ℝ × (ℝ × ℝ) => ψ y.1 y.2) x (0, (0, 1))) O :=
    hFd.clm_apply (contDiffOn_const (c := ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))))
  have hD2 : ContDiffOn ℝ 2
      (fun x : ℝ × (ℝ × ℝ) => fderiv ℝ (fun y : ℝ × (ℝ × ℝ) => ψ y.1 y.2) x (1, (0, 0))) O :=
    hFd.clm_apply (contDiffOn_const (c := ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))))
  have hη : ContDiffOn ℝ 2 (fun p : ℝ × (ℝ × ℝ) => p.2.2) O :=
    (contDiff_snd.comp contDiff_snd).contDiffOn
  have hp1 : ContDiffOn ℝ 2 (fun p : ℝ × (ℝ × ℝ) => p.1) O := contDiffOn_fst
  have hH : ContDiffOn ℝ 2
      (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2 - (p.2.2 *
        fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) p (0, (0, 1)) +
          2 * p.1 * fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) p (1, (0, 0)))) O :=
    hG2.sub ((hη.mul hD1).add (((contDiffOn_const (c := (2 : ℝ))).mul hp1).mul hD2))
  exact hH.congr fun p hp => rp_raised_eq hO hG hp

/-- **Task `PartIII-b:C/rep/8/2/pres/4/1/2`.** The raw lift profile of a train is `C²` on
`Ioi 0 ×ˢ univ`. -/
theorem rawProfile_contDiffOn {ν c ε : ℝ} {v : ℝ → Plane → UnforcedLeray.Train.Vec} {p ψ : ℝ → Plane → ℝ} (h : UnforcedLeray.B0140.IsTrain ν c v p ψ) (hψ : ContDiffOn ℝ 3 (fun x : ℝ × Plane => ψ x.1 x.2) (Ioi 0 ×ˢ univ)) : ContDiffOn ℝ 2 (UnforcedLeray.Cons.C03.rawProfile ε v ψ) (Ioi 0 ×ˢ univ) := by
  have hO : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hv : ContDiffOn ℝ 2 (fun x : ℝ × Plane => v x.1 x.2) (Ioi 0 ×ˢ univ) :=
    (h.smooth_v.mono (Set.prod_mono Set.Ioi_subset_Ici_self Set.Subset.rfl)).of_le (by norm_num)
  have hH := rp_raised_contDiffOn hO hψ
  have hstep : ContDiffOn ℝ 2
      (fun p : ℝ × (ℝ × ℝ) => (ε * raisedStream ψ p.1 p.2.1 p.2.2) •
        EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) (Ioi 0 ×ˢ univ) :=
    ((contDiffOn_const (c := ε)).mul hH).smul contDiffOn_const
  unfold UnforcedLeray.Cons.C03.rawProfile
  exact hv.add hstep


end S2

section S3
open UnforcedLeray.Cons.C03.Concrete
open UnforcedLeray.Cyl

/-- **Task `PartIII-b:C/rep/8/2/pres/4/1/3`.** The raw lift `U_raw` of the actual train is `C²`
jointly in `(τ, y)` off the axis, given that the stream is `C³` on `Ioi 0 ×ˢ univ`. -/
theorem rawU_contDiffOn_offAxis_of (p : Params) (hε : 0 < p.ε) (hψ : ContDiffOn ℝ 3 (fun x : ℝ × Plane => p.train.ψ x.1 x.2) (Ioi 0 ×ˢ univ)) : ContDiffOn ℝ 2 (fun x : ℝ × Space => p.raw x.1 x.2) offAxis := by
  have hR : 0 < p.ε⁻¹ := inv_pos.2 hε
  have hb : ContDiffOn ℝ 2 (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ)
      (Ioi 0 ×ˢ univ) :=
    rawProfile_contDiffOn p.train.isTrain hψ
  have hN := nv_contDiffOn_offAxis hR hb
  exact hN.congr fun x hx => p.raw_eq_off_axis x.1 x.2 hx


end S3

end PwSplitRaw

end UnforcedLeray.Short.PartIIIb.Concrete
