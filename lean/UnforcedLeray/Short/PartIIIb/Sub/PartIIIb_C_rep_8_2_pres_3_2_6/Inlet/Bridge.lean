import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_6.Phys
import UnforcedLeray.Lib.AxisymmetricB.Bridge
import UnforcedLeray.Cons.L2.BackgroundConcrete.Operators

/-!
# Real physical source versus the complexified phase-space operators
(helper of `PartIII-b:C/rep/8/2/pres/3/2/6/1`)

Source `the November 2 reference manuscript`
2370-2374 (the complete unprojected source column), 4139-4141 (`D₀ = ∂_τ - ½y·∇ - νΔ - ½`).

For a jointly `C²` field `G` on `ℝ × ℝ³` and a field `U` differentiable at `(τ, y)`,
the complexification `realC` of the real source `D₀G + G·∇U + U·∇G` (`physDmu`, `fderiv`) is
`L₀(realC G) + (realC U·∇)(realC G) + (realC G·∇)(realC U)` (`B0411.L0`, `advT`), the form in
which the Part II-b chart identities `InletL0Ptw`, `InletBPtw` are stated.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open UnforcedLeray.PhaseSpace UnforcedLeray.B0412

namespace UnforcedLeray.Short.PartIIIb.Concrete.ES326Inlet

theorem realC_eq_cplxV : (realC : Space → PhaseSpace.CVec3) = Axi.cplxV := by
  funext v
  ext i
  simp [realC_apply, Axi.cplxV_apply]

theorem rc_add (a b : Space) : realC (a + b) = realC a + realC b := by
  rw [realC_eq_cplxV, map_add]

theorem rc_sub (a b : Space) : realC (a - b) = realC a - realC b := by
  rw [realC_eq_cplxV, map_sub]

theorem rc_smul (c : ℝ) (a : Space) : realC (c • a) = c • realC a := by
  rw [realC_eq_cplxV, map_smul]

theorem rc_csmul (c : ℝ) (a : Space) : realC (c • a) = (c : ℂ) • realC a := by
  rw [rc_smul, Complex.coe_smul]

theorem rc_sum {ι : Type*} (s : Finset ι) (f : ι → Space) :
    realC (∑ i ∈ s, f i) = ∑ i ∈ s, realC (f i) := by
  rw [realC_eq_cplxV, map_sum]

theorem rc_norm (a : Space) : ‖realC a‖ = ‖a‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [realC_apply, Complex.norm_real]

/-- `y = Σⱼ yⱼ eⱼ`. -/
theorem sum_coord (y : Space) : ∑ j : Fin 3, y j • coordinateVector j = y := by
  ext i
  simp [coordinateVector, Pi.single_apply, mul_ite]

/-- `Lv = Σⱼ vⱼ L eⱼ`. -/
theorem clm_sum_coord {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : Space →L[ℝ] F)
    (v : Space) :
    L v = ∑ j : Fin 3, v j • L (coordinateVector j) := by
  conv_lhs => rw [← sum_coord v]
  rw [map_sum]
  simp only [map_smul]

/-- The derivative of `realC ∘ G`. -/
theorem fderiv_realC_comp {G : ℝ × Space → Space} {x : ℝ × Space}
    (hG : DifferentiableAt ℝ G x) (w : ℝ × Space) :
    fderiv ℝ (fun x => realC (G x)) x w = realC (fderiv ℝ G x w) := by
  have h : HasFDerivAt (fun x => Axi.cplxV (G x)) (Axi.cplxV.comp (fderiv ℝ G x)) x :=
    Axi.cplxV.hasFDerivAt.comp x hG.hasFDerivAt
  rw [realC_eq_cplxV, h.fderiv]
  rfl

/-- The spatial slice derivative. -/
theorem fderiv_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {G : ℝ × Space → E}
    {τ : ℝ} {y : Space} (hG : DifferentiableAt ℝ G (τ, y)) (v : Space) :
    fderiv ℝ (fun y' => G (τ, y')) y v = fderiv ℝ G (τ, y) (0, v) := by
  have h : HasFDerivAt (fun y' => G (τ, y'))
      ((fderiv ℝ G (τ, y)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) y :=
    hG.hasFDerivAt.comp y (hasFDerivAt_prodMk_right τ y)
  rw [h.fderiv]
  rfl

/-- The phase slice derivative. -/
theorem deriv_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {G : ℝ × Space → E}
    {τ : ℝ} {y : Space} (hG : DifferentiableAt ℝ G (τ, y)) :
    deriv (fun t => G (t, y)) τ = fderiv ℝ G (τ, y) (1, 0) := by
  have h : HasFDerivAt (fun t => G (t, y))
      ((fderiv ℝ G (τ, y)).comp (ContinuousLinearMap.inl ℝ ℝ Space)) τ :=
    hG.hasFDerivAt.comp τ (hasFDerivAt_prodMk_left τ y)
  rw [h.hasDerivAt.deriv]
  rfl

theorem dτ_realC {G : ℝ × Space → Space} {τ : ℝ} {y : Space} (hG : DifferentiableAt ℝ G (τ, y)) :
    dτ (fun x => realC (G x)) (τ, y) = realC (deriv (fun t => G (t, y)) τ) := by
  rw [deriv_slice hG]
  exact fderiv_realC_comp hG _

theorem dy_realC {G : ℝ × Space → Space} {x : ℝ × Space} (hG : DifferentiableAt ℝ G x)
    (j : Fin 3) : dy j (fun x => realC (G x)) x = realC (fderiv ℝ G x (0, coordinateVector j)) :=
  fderiv_realC_comp hG _

theorem radialT_realC {G : ℝ × Space → Space} {τ : ℝ} {y : Space}
    (hG : DifferentiableAt ℝ G (τ, y)) :
    radialT (fun x => realC (G x)) (τ, y) = realC (fderiv ℝ (fun y' => G (τ, y')) y y) := by
  unfold radialT
  rw [clm_sum_coord (fderiv ℝ (fun y' => G (τ, y')) y) y, rc_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dy_realC hG, rc_smul, fderiv_slice hG]

theorem lapT_realC {G : ℝ × Space → Space} (hG : ContDiff ℝ 2 G) (τ : ℝ) (y : Space) :
    lapT (fun x => realC (G x)) (τ, y) = realC (physLap (fun y' => G (τ, y')) y) := by
  have hd : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hG1 : ContDiff ℝ 1 (fderiv ℝ G) := hG.fderiv_right (m := 1) (by norm_num)
  unfold lapT physLap
  rw [rc_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  set Gj : ℝ × Space → Space := fun x => fderiv ℝ G x (0, coordinateVector j) with hGj
  have hGjd : Differentiable ℝ Gj :=
    (hG1.differentiable (by norm_num)).clm_apply (differentiable_const _)
  have e1 : dy j (fun x => realC (G x)) = fun x => realC (Gj x) := by
    funext x
    exact dy_realC (hd x) j
  rw [e1, dy_realC (hGjd (τ, y)) j]
  congr 1
  unfold physPd2 physPd
  have e2 : (fun y' => fderiv ℝ (fun y'' => G (τ, y'')) y' (coordinateVector j)) =
      fun y' => Gj (τ, y') := by
    funext y'
    exact fderiv_slice (hd (τ, y')) _
  rw [e2, fderiv_slice (hGjd (τ, y))]

theorem advT_realC_left {G U : ℝ × Space → Space} {τ : ℝ} {y : Space}
    (hG : DifferentiableAt ℝ G (τ, y)) :
    UnforcedLeray.Cons.C03.Concrete.advT (fun x => realC (U x)) (fun x => realC (G x)) (τ, y) =
      realC (fderiv ℝ (fun y' => G (τ, y')) y (U (τ, y))) := by
  unfold UnforcedLeray.Cons.C03.Concrete.advT
  rw [clm_sum_coord (fderiv ℝ (fun y' => G (τ, y')) y) (U (τ, y)), rc_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [dy_realC hG, rc_csmul, realC_apply, fderiv_slice hG]

theorem advT_realC_right {G U : ℝ × Space → Space} {τ : ℝ} {y : Space}
    (hU : DifferentiableAt ℝ U (τ, y)) :
    UnforcedLeray.Cons.C03.Concrete.advT (fun x => realC (G x)) (fun x => realC (U x)) (τ, y) =
      realC (fderiv ℝ (fun y' => U (τ, y')) y (G (τ, y))) :=
  advT_realC_left hU

/-- **The bridge** (source 2370-2374, 4139-4141). -/
theorem realC_physSrc (ν : ℝ) {G U : ℝ × Space → Space} (hG : ContDiff ℝ 2 G) (τ : ℝ) (y : Space)
    (hU : DifferentiableAt ℝ U (τ, y)) :
    realC (physDmu ν 0 (fun t y' => G (t, y')) τ y +
        (fderiv ℝ (fun y' => G (τ, y')) y (U (τ, y)) +
          fderiv ℝ (fun y' => U (τ, y')) y (G (τ, y)))) =
      UnforcedLeray.B0411.L0 ν (fun x => realC (G x)) (τ, y) +
        UnforcedLeray.Cons.C03.Concrete.advT (fun x => realC (U x)) (fun x => realC (G x)) (τ, y) +
        UnforcedLeray.Cons.C03.Concrete.advT (fun x => realC (G x)) (fun x => realC (U x)) (τ, y) := by
  have hd : DifferentiableAt ℝ G (τ, y) := (hG.differentiable (by norm_num)) _
  rw [advT_realC_left hd, advT_realC_right hU]
  unfold UnforcedLeray.B0411.L0 UnforcedLeray.B0411.T0 physDmu
  rw [dτ_realC hd, radialT_realC hd, lapT_realC hG]
  simp only [rc_add, rc_sub, rc_smul]
  rw [zero_sub, neg_smul, ← sub_eq_add_neg]
  abel

end UnforcedLeray.Short.PartIIIb.Concrete.ES326Inlet
