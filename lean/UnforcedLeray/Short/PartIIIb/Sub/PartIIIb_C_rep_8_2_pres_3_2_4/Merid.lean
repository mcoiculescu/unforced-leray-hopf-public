import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_4.Meas
import UnforcedLeray.Short.PartIIb.Sub.R1_7
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.RingCartesianNS.LiftMeridSmooth
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.RingCartesianNS.TrainPressureSmooth
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.RingResidualAxisymmetric

/-!
# Continuity of the ring residual off the axis (`pres/3/2/4`)

Source `the November 2 reference manuscript`,
1203-1250 (the lifted profiles are `C²` jointly in `(r, z, t)` for `r, t > 0`), 1263
(`F_R = s^{3/2} r`).  The cylindrical residual only uses first and second partial derivatives of
`C²` profiles, hence is continuous on `{r > 0, t > 0}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi UnforcedLeray.B0187 UnforcedLeray.B0185
open UnforcedLeray.B0184
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.IIb (meridDomain MeridSmooth)

theorem pf4_isOpen_merid : IsOpen meridDomain :=
  (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_const continuous_snd.snd)

section Partials

variable {G : ℝ × ℝ × ℝ → ℝ} {D : Set (ℝ × ℝ × ℝ)}

theorem pf4_physR_eq (hD : IsOpen D) (hG : DifferentiableOn ℝ G D) {r z t : ℝ}
    (h : (r, z, t) ∈ D) :
    physR (fun a b c => G (a, b, c)) r z t = fderiv ℝ G (r, z, t) (1, 0, 0) := by
  have hm : HasDerivAt (fun x : ℝ => ((x, z, t) : ℝ × ℝ × ℝ)) ((1, 0, 0) : ℝ × ℝ × ℝ) r :=
    (hasDerivAt_id r).prodMk ((hasDerivAt_const r z).prodMk (hasDerivAt_const r t))
  have := (hG.differentiableAt (hD.mem_nhds h)).hasFDerivAt.comp_hasDerivAt r hm
  exact this.deriv

theorem pf4_physZ_eq (hD : IsOpen D) (hG : DifferentiableOn ℝ G D) {r z t : ℝ}
    (h : (r, z, t) ∈ D) :
    physZ (fun a b c => G (a, b, c)) r z t = fderiv ℝ G (r, z, t) (0, 1, 0) := by
  have hm : HasDerivAt (fun x : ℝ => ((r, x, t) : ℝ × ℝ × ℝ)) ((0, 1, 0) : ℝ × ℝ × ℝ) z :=
    (hasDerivAt_const z r).prodMk ((hasDerivAt_id z).prodMk (hasDerivAt_const z t))
  have := (hG.differentiableAt (hD.mem_nhds h)).hasFDerivAt.comp_hasDerivAt z hm
  exact this.deriv

theorem pf4_physT_eq (hD : IsOpen D) (hG : DifferentiableOn ℝ G D) {r z t : ℝ}
    (h : (r, z, t) ∈ D) :
    physT (fun a b c => G (a, b, c)) r z t = fderiv ℝ G (r, z, t) (0, 0, 1) := by
  have hm : HasDerivAt (fun x : ℝ => ((r, z, x) : ℝ × ℝ × ℝ)) ((0, 0, 1) : ℝ × ℝ × ℝ) t :=
    (hasDerivAt_const t r).prodMk ((hasDerivAt_const t z).prodMk (hasDerivAt_id t))
  have := (hG.differentiableAt (hD.mem_nhds h)).hasFDerivAt.comp_hasDerivAt t hm
  exact this.deriv

end Partials

section Cont

variable {G : ℝ × ℝ × ℝ → ℝ}

theorem pf4_D1 (hG : ContDiffOn ℝ 2 G meridDomain) (v : ℝ × ℝ × ℝ) :
    ContDiffOn ℝ 1 (fun q => fderiv ℝ G q v) meridDomain :=
  (hG.fderiv_of_isOpen pf4_isOpen_merid (m := 1) (by norm_num)).clm_apply contDiffOn_const

theorem pf4_cont_first (hG : ContDiffOn ℝ 2 G meridDomain) (v : ℝ × ℝ × ℝ) :
    ContinuousOn (fun q => fderiv ℝ G q v) meridDomain :=
  (pf4_D1 hG v).continuousOn

theorem pf4_cont_second (hG : ContDiffOn ℝ 2 G meridDomain) (v w : ℝ × ℝ × ℝ) :
    ContinuousOn (fun q => fderiv ℝ (fun q' => fderiv ℝ G q' v) q w) meridDomain := by
  have h := (pf4_D1 hG v).continuousOn_fderiv_of_isOpen pf4_isOpen_merid (by norm_num)
  exact h.clm_apply continuousOn_const

/-- Second radial/axial partial. -/
theorem pf4_physR_physR (hG : ContDiffOn ℝ 2 G meridDomain) {r z t : ℝ}
    (h : (r, z, t) ∈ meridDomain) :
    physR (physR fun a b c => G (a, b, c)) r z t =
      fderiv ℝ (fun q' => fderiv ℝ G q' (1, 0, 0)) (r, z, t) (1, 0, 0) := by
  have hD1 := pf4_D1 hG (1, 0, 0)
  have hev : (fun x => physR (fun a b c => G (a, b, c)) x z t) =ᶠ[𝓝 r]
      fun x => (fun q' => fderiv ℝ G q' (1, 0, 0)) (x, z, t) := by
    have hcont : Continuous fun x : ℝ => ((x, z, t) : ℝ × ℝ × ℝ) := by fun_prop
    have hn : {x : ℝ | (x, z, t) ∈ meridDomain} ∈ 𝓝 r :=
      hcont.continuousAt.preimage_mem_nhds (pf4_isOpen_merid.mem_nhds h)
    filter_upwards [hn] with x hx
    exact pf4_physR_eq pf4_isOpen_merid (hG.differentiableOn (by norm_num)) hx
  calc physR (physR fun a b c => G (a, b, c)) r z t
      = deriv (fun x => physR (fun a b c => G (a, b, c)) x z t) r := rfl
    _ = deriv (fun x => (fun q' => fderiv ℝ G q' (1, 0, 0)) (x, z, t)) r := hev.deriv_eq
    _ = physR (fun a b c => (fun q' => fderiv ℝ G q' (1, 0, 0)) (a, b, c)) r z t := rfl
    _ = _ := pf4_physR_eq (G := fun q' => fderiv ℝ G q' (1, 0, 0)) pf4_isOpen_merid
      (hD1.differentiableOn (by norm_num)) h

theorem pf4_physZ_physZ (hG : ContDiffOn ℝ 2 G meridDomain) {r z t : ℝ}
    (h : (r, z, t) ∈ meridDomain) :
    physZ (physZ fun a b c => G (a, b, c)) r z t =
      fderiv ℝ (fun q' => fderiv ℝ G q' (0, 1, 0)) (r, z, t) (0, 1, 0) := by
  have hD1 := pf4_D1 hG (0, 1, 0)
  have hev : (fun x => physZ (fun a b c => G (a, b, c)) r x t) =ᶠ[𝓝 z]
      fun x => (fun q' => fderiv ℝ G q' (0, 1, 0)) (r, x, t) := by
    have hcont : Continuous fun x : ℝ => ((r, x, t) : ℝ × ℝ × ℝ) := by fun_prop
    have hn : {x : ℝ | (r, x, t) ∈ meridDomain} ∈ 𝓝 z :=
      hcont.continuousAt.preimage_mem_nhds (pf4_isOpen_merid.mem_nhds h)
    filter_upwards [hn] with x hx
    exact pf4_physZ_eq pf4_isOpen_merid (hG.differentiableOn (by norm_num)) hx
  calc physZ (physZ fun a b c => G (a, b, c)) r z t
      = deriv (fun x => physZ (fun a b c => G (a, b, c)) r x t) z := rfl
    _ = deriv (fun x => (fun q' => fderiv ℝ G q' (0, 1, 0)) (r, x, t)) z := hev.deriv_eq
    _ = physZ (fun a b c => (fun q' => fderiv ℝ G q' (0, 1, 0)) (a, b, c)) r z t := rfl
    _ = _ := pf4_physZ_eq (G := fun q' => fderiv ℝ G q' (0, 1, 0)) pf4_isOpen_merid
      (hD1.differentiableOn (by norm_num)) h

end Cont

section Residual

variable {f : ℝ → ℝ → ℝ → ℝ}

theorem pf4_contOn_physR (hf : MeridSmooth 2 f) :
    ContinuousOn (fun q : ℝ × ℝ × ℝ => physR f q.1 q.2.1 q.2.2) meridDomain := by
  refine (pf4_cont_first hf (1, 0, 0)).congr fun q hq => ?_
  exact pf4_physR_eq (G := fun q : ℝ × ℝ × ℝ => f q.1 q.2.1 q.2.2) pf4_isOpen_merid
    (hf.differentiableOn (by norm_num)) hq

theorem pf4_contOn_physZ (hf : MeridSmooth 2 f) :
    ContinuousOn (fun q : ℝ × ℝ × ℝ => physZ f q.1 q.2.1 q.2.2) meridDomain := by
  refine (pf4_cont_first hf (0, 1, 0)).congr fun q hq => ?_
  exact pf4_physZ_eq (G := fun q : ℝ × ℝ × ℝ => f q.1 q.2.1 q.2.2) pf4_isOpen_merid
    (hf.differentiableOn (by norm_num)) hq

theorem pf4_contOn_physT (hf : MeridSmooth 2 f) :
    ContinuousOn (fun q : ℝ × ℝ × ℝ => physT f q.1 q.2.1 q.2.2) meridDomain := by
  refine (pf4_cont_first hf (0, 0, 1)).congr fun q hq => ?_
  exact pf4_physT_eq (G := fun q : ℝ × ℝ × ℝ => f q.1 q.2.1 q.2.2) pf4_isOpen_merid
    (hf.differentiableOn (by norm_num)) hq

theorem pf4_contOn_physRR (hf : MeridSmooth 2 f) :
    ContinuousOn (fun q : ℝ × ℝ × ℝ => physR (physR f) q.1 q.2.1 q.2.2) meridDomain := by
  refine (pf4_cont_second hf (1, 0, 0) (1, 0, 0)).congr fun q hq => ?_
  exact pf4_physR_physR (G := fun q : ℝ × ℝ × ℝ => f q.1 q.2.1 q.2.2) hf hq

theorem pf4_contOn_physZZ (hf : MeridSmooth 2 f) :
    ContinuousOn (fun q : ℝ × ℝ × ℝ => physZ (physZ f) q.1 q.2.1 q.2.2) meridDomain := by
  refine (pf4_cont_second hf (0, 1, 0) (0, 1, 0)).congr fun q hq => ?_
  exact pf4_physZ_physZ (G := fun q : ℝ × ℝ × ℝ => f q.1 q.2.1 q.2.2) hf hq

theorem pf4_contOn_val (hf : MeridSmooth 2 f) :
    ContinuousOn (fun q : ℝ × ℝ × ℝ => f q.1 q.2.1 q.2.2) meridDomain := hf.continuousOn

end Residual

section Combine

variable {ur uz p : ℝ → ℝ → ℝ → ℝ} {ν : ℝ}

theorem pf4_contOn_radial (hu : MeridSmooth 2 ur) (hv : MeridSmooth 2 uz) (hp : MeridSmooth 2 p) :
    ContinuousOn (fun q : ℝ × ℝ × ℝ => cylRadialResidual ν ur uz p q.1 q.2.1 q.2.2)
      meridDomain := by
  have hr : ∀ q ∈ meridDomain, q.1 ≠ 0 := fun q hq => hq.1.ne'
  unfold cylRadialResidual radialVectorLaplacian
  have h1 := pf4_contOn_physT hu
  have h2 := pf4_contOn_val hu
  have h3 := pf4_contOn_physR hu
  have h4 := pf4_contOn_val hv
  have h5 := pf4_contOn_physZ hu
  have h6 := pf4_contOn_physRR hu
  have h7 := pf4_contOn_physZZ hu
  have h8 := pf4_contOn_physR hp
  have hq1 : ContinuousOn (fun q : ℝ × ℝ × ℝ => q.1) meridDomain := continuous_fst.continuousOn
  refine ((((h1.add (h2.mul h3)).add (h4.mul h5)).sub ?_).add h8)
  refine continuousOn_const.mul ?_
  refine (((h6.add (h3.div hq1 hr)).sub (h2.div (hq1.pow 2) fun q hq => pow_ne_zero 2 (hr q hq))).add h7)

theorem pf4_contOn_axial (hu : MeridSmooth 2 ur) (hv : MeridSmooth 2 uz) (hp : MeridSmooth 2 p) :
    ContinuousOn (fun q : ℝ × ℝ × ℝ => cylAxialResidual ν ur uz p q.1 q.2.1 q.2.2)
      meridDomain := by
  have hr : ∀ q ∈ meridDomain, q.1 ≠ 0 := fun q hq => hq.1.ne'
  unfold cylAxialResidual axialVectorLaplacian
  have h1 := pf4_contOn_physT hv
  have h2 := pf4_contOn_val hu
  have h3 := pf4_contOn_physR hv
  have h4 := pf4_contOn_val hv
  have h5 := pf4_contOn_physZ hv
  have h6 := pf4_contOn_physRR hv
  have h7 := pf4_contOn_physZZ hv
  have h8 := pf4_contOn_physZ hp
  have hq1 : ContinuousOn (fun q : ℝ × ℝ × ℝ => q.1) meridDomain := continuous_fst.continuousOn
  refine ((((h1.add (h2.mul h3)).add (h4.mul h5)).sub ?_).add h8)
  refine continuousOn_const.mul ?_
  exact ((h6.add (h3.div hq1 hr)).add h7)

end Combine

end UnforcedLeray.Short.PartIIIb.Concrete
