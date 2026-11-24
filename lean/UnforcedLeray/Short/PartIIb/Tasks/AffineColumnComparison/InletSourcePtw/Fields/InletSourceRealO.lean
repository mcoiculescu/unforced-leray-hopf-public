import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_4_1_Fields
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.InletJointSmooth
import UnforcedLeray.Lib.AxisymmetricB.Average
import UnforcedLeray.Lib.AxisymmetricB.Bridge

/-!
# Part II-b, task `PartII-b:G4/4/1/1/4` (`InletSourceRealO`)

Source of record: `the November 2 reference manuscript`, lines 2355-2383.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint UnforcedLeray.PhaseSpace
  UnforcedLeray.B0411 UnforcedLeray.B0412 UnforcedLeray.Axi

private theorem ro_realC_eq_cplxV : (realC : Space → PhaseSpace.CVec3) = Axi.cplxV := by
  funext v
  ext i
  simp [realC_apply, Axi.cplxV_apply]

private theorem ro_rc_add (a b : Space) : realC (a + b) = realC a + realC b := by
  rw [ro_realC_eq_cplxV, map_add]

private theorem ro_rc_sub (a b : Space) : realC (a - b) = realC a - realC b := by
  rw [ro_realC_eq_cplxV, map_sub]

private theorem ro_rc_smul (c : ℝ) (a : Space) : realC (c • a) = c • realC a := by
  rw [ro_realC_eq_cplxV, map_smul]

private theorem ro_rc_csmul (c : ℝ) (a : Space) : realC (c • a) = (c : ℂ) • realC a := by
  rw [ro_rc_smul, Complex.coe_smul]

private theorem ro_rc_sum {ι : Type*} (s : Finset ι) (f : ι → Space) :
    realC (∑ i ∈ s, f i) = ∑ i ∈ s, realC (f i) := by
  rw [ro_realC_eq_cplxV, map_sum]

private theorem ro_sum_coord (y : Space) : ∑ j : Fin 3, y j • coordinateVector j = y := by
  ext i
  simp [coordinateVector, Pi.single_apply, mul_ite]

private theorem ro_clm_sum_coord {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : Space →L[ℝ] F) (v : Space) :
    L v = ∑ j : Fin 3, v j • L (coordinateVector j) := by
  conv_lhs => rw [← ro_sum_coord v]
  rw [map_sum]
  simp only [map_smul]

private theorem ro_fderiv_realC_comp {G : ℝ × Space → Space} {x : ℝ × Space}
    (hG : DifferentiableAt ℝ G x) (w : ℝ × Space) :
    fderiv ℝ (fun x => realC (G x)) x w = realC (fderiv ℝ G x w) := by
  have h : HasFDerivAt (fun x => Axi.cplxV (G x)) (Axi.cplxV.comp (fderiv ℝ G x)) x :=
    Axi.cplxV.hasFDerivAt.comp x hG.hasFDerivAt
  rw [ro_realC_eq_cplxV, h.fderiv]
  rfl

private theorem ro_fderiv_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : ℝ × Space → E} {τ : ℝ} {y : Space} (hG : DifferentiableAt ℝ G (τ, y)) (v : Space) :
    fderiv ℝ (fun y' => G (τ, y')) y v = fderiv ℝ G (τ, y) (0, v) := by
  have h : HasFDerivAt (fun y' => G (τ, y'))
      ((fderiv ℝ G (τ, y)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) y :=
    hG.hasFDerivAt.comp y (hasFDerivAt_prodMk_right τ y)
  rw [h.fderiv]
  rfl

private theorem ro_deriv_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : ℝ × Space → E} {τ : ℝ} {y : Space} (hG : DifferentiableAt ℝ G (τ, y)) :
    deriv (fun t => G (t, y)) τ = fderiv ℝ G (τ, y) (1, 0) := by
  have h : HasFDerivAt (fun t => G (t, y))
      ((fderiv ℝ G (τ, y)).comp (ContinuousLinearMap.inl ℝ ℝ Space)) τ :=
    hG.hasFDerivAt.comp τ (hasFDerivAt_prodMk_left τ y)
  rw [h.hasDerivAt.deriv]
  rfl

private theorem ro_dτ_realC {G : ℝ × Space → Space} {τ : ℝ} {y : Space}
    (hG : DifferentiableAt ℝ G (τ, y)) :
    dτ (fun x => realC (G x)) (τ, y) = realC (deriv (fun t => G (t, y)) τ) := by
  rw [ro_deriv_slice hG]
  exact ro_fderiv_realC_comp hG _

private theorem ro_dy_realC {G : ℝ × Space → Space} {x : ℝ × Space}
    (hG : DifferentiableAt ℝ G x) (j : Fin 3) :
    dy j (fun x => realC (G x)) x = realC (fderiv ℝ G x (0, coordinateVector j)) :=
  ro_fderiv_realC_comp hG _

private theorem ro_radialT_realC {G : ℝ × Space → Space} {τ : ℝ} {y : Space}
    (hG : DifferentiableAt ℝ G (τ, y)) :
    radialT (fun x => realC (G x)) (τ, y) = realC (fderiv ℝ (fun y' => G (τ, y')) y y) := by
  unfold radialT
  rw [ro_clm_sum_coord (fderiv ℝ (fun y' => G (τ, y')) y) y, ro_rc_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ro_dy_realC hG, ro_rc_smul, ro_fderiv_slice hG]

private def roLap (f : Space → Space) (y : Space) : Space :=
  ∑ j : Fin 3, fderiv ℝ (fun y' => fderiv ℝ f y' (coordinateVector j)) y (coordinateVector j)

private theorem ro_lapT_realC {G : ℝ × Space → Space} (hG : ContDiff ℝ ∞ G) (τ : ℝ) (y : Space) :
    lapT (fun x => realC (G x)) (τ, y) = realC (roLap (fun y' => G (τ, y')) y) := by
  have hd : Differentiable ℝ G := hG.differentiable (by simp)
  have hG1 : ContDiff ℝ ∞ (fderiv ℝ G) := hG.fderiv_right (m := ∞) (by simp)
  unfold lapT roLap
  rw [ro_rc_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  set Gj : ℝ × Space → Space := fun x => fderiv ℝ G x (0, coordinateVector j)
  have hGjd : Differentiable ℝ Gj :=
    (hG1.differentiable (by simp)).clm_apply (differentiable_const _)
  have e1 : dy j (fun x => realC (G x)) = fun x => realC (Gj x) := by
    funext x
    exact ro_dy_realC (hd x) j
  rw [e1, ro_dy_realC (hGjd (τ, y)) j]
  congr 1
  have e2 : (fun y' => fderiv ℝ (fun y'' => G (τ, y'')) y' (coordinateVector j)) =
      fun y' => Gj (τ, y') := by
    funext y'
    exact ro_fderiv_slice (hd (τ, y')) _
  rw [e2, ro_fderiv_slice (hGjd (τ, y))]

private theorem ro_advT_realC_left {G U : ℝ × Space → Space} {τ : ℝ} {y : Space}
    (hG : DifferentiableAt ℝ G (τ, y)) :
    advT (fun x => realC (U x)) (fun x => realC (G x)) (τ, y) =
      realC (fderiv ℝ (fun y' => G (τ, y')) y (U (τ, y))) := by
  unfold advT
  rw [ro_clm_sum_coord (fderiv ℝ (fun y' => G (τ, y')) y) (U (τ, y)), ro_rc_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ro_dy_realC hG, ro_rc_csmul, realC_apply, ro_fderiv_slice hG]

private def inletSourceR (p : Params) (i : Fin 2) (τ : ℝ) (y : Space) : Space :=
  deriv (fun t => p.inlet i t y) τ
    - (1 / 2 : ℝ) • fderiv ℝ (p.inlet i τ) y y
    - p.ν • roLap (p.inlet i τ) y
    - (1 / 2 : ℝ) • p.inlet i τ y
    + fderiv ℝ (p.inlet i τ) y (p.raw τ y)
    + fderiv ℝ (p.raw τ) y (p.inlet i τ y)

private theorem inletSourceF_eq_realC {p : Params} {i : Fin 2}
    (hInl : ContDiff ℝ ∞ (fun x : ℝ × Space => p.inlet i x.1 x.2)) (τ : ℝ) (y : Space) :
    inletSourceF p i (τ, y) = realC (inletSourceR p i τ y) := by
  have hd : DifferentiableAt ℝ (fun x : ℝ × Space => p.inlet i x.1 x.2) (τ, y) :=
    (hInl.differentiable (by simp)) (τ, y)
  unfold inletSourceF inletSourceR Params.Efun Params.Ufun
  rw [ro_dτ_realC hd, ro_radialT_realC hd, ro_lapT_realC hInl, ro_advT_realC_left hd]
  simp only [ro_rc_add, ro_rc_sub, ro_rc_smul]

private theorem ro_nv_equivar {g : Space ≃ₗᵢ[ℝ] Space} (hg : FixesAxis g) (R τ : ℝ)
    (b : ℝ × (ℝ × ℝ) → Axi.Merid) (y : Space) :
    Axi.Nv R b τ (g y) = g (Axi.Nv R b τ y) := by
  have he3 : g Axi.e3 = Axi.e3 := hg
  have hage : Axi.age R (g y) = Axi.age R y := by
    simp only [Axi.age, Axi.ϱ_map hg]
  have hchart : Axi.chart R τ (g y) = Axi.chart R τ y := by
    simp only [Axi.chart, Axi.phase, Axi.trans, hage, Axi.ϱ_map hg, Axi.apply_two_map hg]
  have hframe : ∀ v : Axi.Merid, Axi.frameL (g y) v = g (Axi.frameL y v) := by
    intro v
    rw [Axi.frameL_apply, Axi.frameL_apply, Axi.eR_map hg y, map_add, map_smul, map_smul, he3]
  simp only [Axi.Nv, hage, hchart]
  rw [hframe, map_smul]

private theorem ro_inlet_equivar (p : Params) (i : Fin 2) {g : Space ≃ₗᵢ[ℝ] Space}
    (hg : FixesAxis g) (τ : ℝ) (y : Space) :
    p.inlet i τ (g y) = g (p.inlet i τ y) :=
  ro_nv_equivar hg p.R τ (p.inletProfile i) y

private theorem ro_ext_equivar {V : Space → Space} {R : ℝ} {b : ℝ × (ℝ × ℝ) → Axi.Merid} {τ : ℝ}
    (hc : Continuous V) (hoff : ∀ z, z ∉ Axi.axis → V z = Axi.Nv R b τ z)
    {g : Space ≃ₗᵢ[ℝ] Space} (hg : FixesAxis g) (y : Space) :
    V (g y) = g (V y) := by
  have hae : (fun z : Space => V (g z)) =ᵐ[volume] fun z : Space => g (V z) := by
    filter_upwards [Axi.ae_not_mem_axis] with z hz
    have hgz : g z ∉ Axi.axis := by
      rw [Axi.mem_axis_iff, Axi.ϱ_map hg, ← Axi.mem_axis_iff]
      exact hz
    rw [hoff (g z) hgz, hoff z hz]
    exact ro_nv_equivar hg R τ b z
  exact congrFun ((Continuous.ae_eq_iff_eq volume
    (hc.comp g.continuous) (g.continuous.comp hc)).mp hae) y

private theorem ro_contDiff_slice_right {F : ℝ → Space → Space}
    (hF : ContDiff ℝ ∞ (fun x : ℝ × Space => F x.1 x.2)) (τ : ℝ) :
    ContDiff ℝ ∞ (F τ) :=
  hF.comp (contDiff_const.prodMk contDiff_id)

private theorem ro_contDiff_slice_left {F : ℝ → Space → Space}
    (hF : ContDiff ℝ ∞ (fun x : ℝ × Space => F x.1 x.2)) (y : Space) :
    ContDiff ℝ ∞ (fun t => F t y) :=
  hF.comp (contDiff_id.prodMk contDiff_const)

private theorem ro_raw_equivar (p : Params)
    (hRaw : ContDiff ℝ ∞ (fun x : ℝ × Space => p.raw x.1 x.2)) {g : Space ≃ₗᵢ[ℝ] Space}
    (hg : FixesAxis g) (τ : ℝ) (y : Space) :
    p.raw τ (g y) = g (p.raw τ y) :=
  ro_ext_equivar (ro_contDiff_slice_right hRaw τ).continuous (p.raw_eq_off_axis τ) hg y

private theorem ro_g_hasFDerivAt (g : Space ≃ₗᵢ[ℝ] Space) (y : Space) :
    HasFDerivAt (fun z : Space => g z) (g.toContinuousLinearEquiv : Space →L[ℝ] Space) y :=
  (g.toContinuousLinearEquiv).hasFDerivAt

private theorem ro_fderiv_equiv (g : Space ≃ₗᵢ[ℝ] Space) (f : Space → Space)
    (hf : Differentiable ℝ f) (hfg : ∀ z, f (g z) = g (f z)) (y v : Space) :
    fderiv ℝ f (g y) (g v) = g (fderiv ℝ f y v) := by
  have h1 : HasFDerivAt (fun z => f (g z))
      ((fderiv ℝ f (g y)).comp (g.toContinuousLinearEquiv : Space →L[ℝ] Space)) y :=
    (hf (g y)).hasFDerivAt.comp y (ro_g_hasFDerivAt g y)
  have h2 : HasFDerivAt (fun z => g (f z))
      ((g.toContinuousLinearEquiv : Space →L[ℝ] Space).comp (fderiv ℝ f y)) y :=
    (ro_g_hasFDerivAt g (f y)).comp y (hf y).hasFDerivAt
  have h3 : (fun z => f (g z)) = fun z => g (f z) := funext hfg
  rw [h3] at h1
  have h4 := h1.unique h2
  have h5 := congrArg (fun L : Space →L[ℝ] Space => L v) h4
  simpa using h5

private theorem ro_fderiv2_equiv (g : Space ≃ₗᵢ[ℝ] Space) (f : Space → Space)
    (hf : ContDiff ℝ ∞ f) (hfg : ∀ z, f (g z) = g (f z)) (y u v : Space) :
    fderiv ℝ (fderiv ℝ f) (g y) (g u) (g v) = g (fderiv ℝ (fderiv ℝ f) y u v) := by
  have hK : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have hK1 : ∀ z w, fderiv ℝ f (g z) (g w) = g (fderiv ℝ f z w) := fun z w =>
    ro_fderiv_equiv g f (hf.differentiable (by simp)) hfg z w
  have hA : HasFDerivAt (fun z => fderiv ℝ f (g z) (g v))
      ((ContinuousLinearMap.apply ℝ Space (g v)).comp
        ((fderiv ℝ (fderiv ℝ f) (g y)).comp (g.toContinuousLinearEquiv : Space →L[ℝ] Space))) y :=
    (ContinuousLinearMap.apply ℝ Space (g v)).hasFDerivAt.comp y
      ((hK (g y)).hasFDerivAt.comp y (ro_g_hasFDerivAt g y))
  have hB : HasFDerivAt (fun z => g (fderiv ℝ f z v))
      ((g.toContinuousLinearEquiv : Space →L[ℝ] Space).comp
        ((ContinuousLinearMap.apply ℝ Space v).comp (fderiv ℝ (fderiv ℝ f) y))) y :=
    (g.toContinuousLinearEquiv : Space →L[ℝ] Space).hasFDerivAt.comp y
      ((ContinuousLinearMap.apply ℝ Space v).hasFDerivAt.comp y (hK y).hasFDerivAt)
  have hB2 : HasFDerivAt (fun z => fderiv ℝ f (g z) (g v))
      ((g.toContinuousLinearEquiv : Space →L[ℝ] Space).comp
        ((ContinuousLinearMap.apply ℝ Space v).comp (fderiv ℝ (fderiv ℝ f) y))) y := by
    have hfun : (fun z => fderiv ℝ f (g z) (g v)) = fun z => g (fderiv ℝ f z v) :=
      funext fun z => hK1 z v
    rw [hfun]
    exact hB
  have key := hA.unique hB2
  have key2 := congrArg (fun L : Space →L[ℝ] Space => L u) key
  simpa using key2

private theorem ro_pd2_eq (f : Space → Space) (hf : ContDiff ℝ ∞ f) (j l : Fin 3) (y : Space) :
    fderiv ℝ (fun y' => fderiv ℝ f y' (coordinateVector l)) y (coordinateVector j) =
      fderiv ℝ (fderiv ℝ f) y (coordinateVector j) (coordinateVector l) := by
  have hK : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) y) y :=
    ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) y).hasFDerivAt
  have h2 : HasFDerivAt (fun y' => fderiv ℝ f y' (coordinateVector l))
      ((fderiv ℝ (fderiv ℝ f) y).flip (coordinateVector l)) y := by
    simpa using hK.clm_apply (hasFDerivAt_const (coordinateVector l) y)
  rw [h2.fderiv]
  simp

private theorem ro_trace (B : Space →L[ℝ] Space →L[ℝ] Space) (h : Space ≃ₗᵢ[ℝ] Space) :
    ∑ j : Fin 3, B (h (coordinateVector j)) (h (coordinateVector j)) =
      ∑ j : Fin 3, B (coordinateVector j) (coordinateVector j) := by
  have hexp : ∀ u : Space, u = ∑ k : Fin 3, inner ℝ (coordinateVector k) u • coordinateVector k := by
    intro u
    ext i
    fin_cases i <;> simp [Fin.sum_univ_three, coordinateVector,
      EuclideanSpace.inner_single_left]
  have hpars : ∀ x y : Space,
      ∑ j : Fin 3, inner ℝ x (coordinateVector j) * inner ℝ (coordinateVector j) y =
        inner ℝ x y := by
    intro x y
    conv_rhs => rw [hexp y]
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_right]
    ring
  have hdelta : ∀ k l : Fin 3,
      inner ℝ (coordinateVector k) (coordinateVector l) = if k = l then 1 else 0 := by
    intro k l
    simp [coordinateVector, EuclideanSpace.inner_single_left]
  have gen : ∀ m j : Fin 3,
      inner ℝ (coordinateVector m) (h (coordinateVector j)) =
        inner ℝ (h.symm (coordinateVector m)) (coordinateVector j) := by
    intro m j
    conv_lhs => rw [← h.apply_symm_apply (coordinateVector m)]
    exact h.inner_map_map _ _
  have hcoef : ∀ k l : Fin 3,
      ∑ j : Fin 3, inner ℝ (coordinateVector k) (h (coordinateVector j)) *
        inner ℝ (coordinateVector l) (h (coordinateVector j)) =
        inner ℝ (coordinateVector k) (coordinateVector l) := by
    intro k l
    have e2 : ∀ j : Fin 3, inner ℝ (coordinateVector l) (h (coordinateVector j)) =
        inner ℝ (coordinateVector j) (h.symm (coordinateVector l)) := by
      intro j
      rw [gen l j, real_inner_comm]
    have hk : ∀ j : Fin 3, inner ℝ (coordinateVector k) (h (coordinateVector j)) =
        inner ℝ (h.symm (coordinateVector k)) (coordinateVector j) := fun j => gen k j
    rw [Finset.sum_congr rfl fun j _ => by rw [hk j, e2 j]]
    rw [hpars (h.symm (coordinateVector k)) (h.symm (coordinateVector l))]
    exact h.symm.inner_map_map _ _
  have hexp2 : ∀ u v : Space, B u v = ∑ k : Fin 3, ∑ l : Fin 3,
      (inner ℝ (coordinateVector k) u * inner ℝ (coordinateVector l) v) •
        B (coordinateVector k) (coordinateVector l) := by
    intro u v
    conv_lhs => rw [hexp u, hexp v]
    simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [mul_comm]
  calc ∑ j : Fin 3, B (h (coordinateVector j)) (h (coordinateVector j))
      = ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
          (inner ℝ (coordinateVector k) (h (coordinateVector j)) *
            inner ℝ (coordinateVector l) (h (coordinateVector j))) •
              B (coordinateVector k) (coordinateVector l) :=
        Finset.sum_congr rfl fun j _ => hexp2 _ _
    _ = ∑ k : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3,
          (inner ℝ (coordinateVector k) (h (coordinateVector j)) *
            inner ℝ (coordinateVector l) (h (coordinateVector j))) •
              B (coordinateVector k) (coordinateVector l) := Finset.sum_comm
    _ = ∑ k : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3,
          (inner ℝ (coordinateVector k) (h (coordinateVector j)) *
            inner ℝ (coordinateVector l) (h (coordinateVector j))) •
              B (coordinateVector k) (coordinateVector l) :=
        Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k : Fin 3, ∑ l : Fin 3, inner ℝ (coordinateVector k) (coordinateVector l) •
          B (coordinateVector k) (coordinateVector l) :=
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by
          rw [← Finset.sum_smul, hcoef k l]
    _ = ∑ k : Fin 3, B (coordinateVector k) (coordinateVector k) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        simp [hdelta]

private theorem roLap_equiv (g : Space ≃ₗᵢ[ℝ] Space) (f : Space → Space) (hf : ContDiff ℝ ∞ f)
    (hfg : ∀ z, f (g z) = g (f z)) (y : Space) :
    roLap f (g y) = g (roLap f y) := by
  unfold roLap
  simp only [ro_pd2_eq f hf]
  have hw : ∀ j : Fin 3, fderiv ℝ (fderiv ℝ f) (g y) (coordinateVector j) (coordinateVector j) =
      g (fderiv ℝ (fderiv ℝ f) y (g.symm (coordinateVector j)) (g.symm (coordinateVector j))) := by
    intro j
    have := ro_fderiv2_equiv g f hf hfg y (g.symm (coordinateVector j)) (g.symm (coordinateVector j))
    rw [LinearIsometryEquiv.apply_symm_apply] at this
    exact this
  rw [Finset.sum_congr rfl (fun j _ => hw j), ← map_sum, ro_trace (fderiv ℝ (fderiv ℝ f) y) g.symm]

private theorem inletSourceR_equiv {p : Params} {i : Fin 2}
    (hInl : ContDiff ℝ ∞ (fun x : ℝ × Space => p.inlet i x.1 x.2))
    (hRaw : ContDiff ℝ ∞ (fun x : ℝ × Space => p.raw x.1 x.2))
    {g : Space ≃ₗᵢ[ℝ] Space} (hg : FixesAxis g) (τ : ℝ) (y : Space) :
    inletSourceR p i τ (g y) = g (inletSourceR p i τ y) := by
  have hEτ : ContDiff ℝ ∞ (p.inlet i τ) := ro_contDiff_slice_right hInl τ
  have hEd : Differentiable ℝ (p.inlet i τ) := hEτ.differentiable (by simp)
  have hEt : Differentiable ℝ (fun t => p.inlet i t y) :=
    (ro_contDiff_slice_left hInl y).differentiable (by simp)
  have hVd : Differentiable ℝ (p.raw τ) :=
    (ro_contDiff_slice_right hRaw τ).differentiable (by simp)
  have hEg : ∀ z, p.inlet i τ (g z) = g (p.inlet i τ z) := ro_inlet_equivar p i hg τ
  have hVg : ∀ z, p.raw τ (g z) = g (p.raw τ z) := ro_raw_equivar p hRaw hg τ
  have hT : deriv (fun t => p.inlet i t (g y)) τ = g (deriv (fun t => p.inlet i t y) τ) := by
    have e : (fun t => p.inlet i t (g y)) = fun t => g (p.inlet i t y) :=
      funext fun t => ro_inlet_equivar p i hg t y
    rw [e]
    exact ((g.toContinuousLinearEquiv : Space →L[ℝ] Space).hasFDerivAt.comp_hasDerivAt τ
      (hEt τ).hasDerivAt).deriv
  have hR1 : fderiv ℝ (p.inlet i τ) (g y) (g y) = g (fderiv ℝ (p.inlet i τ) y y) :=
    ro_fderiv_equiv g (p.inlet i τ) hEd hEg y y
  have hL : roLap (p.inlet i τ) (g y) = g (roLap (p.inlet i τ) y) :=
    roLap_equiv g (p.inlet i τ) hEτ hEg y
  have hA1 : fderiv ℝ (p.inlet i τ) (g y) (p.raw τ (g y)) =
      g (fderiv ℝ (p.inlet i τ) y (p.raw τ y)) := by
    rw [hVg y]
    exact ro_fderiv_equiv g (p.inlet i τ) hEd hEg y (p.raw τ y)
  have hA2 : fderiv ℝ (p.raw τ) (g y) (p.inlet i τ (g y)) =
      g (fderiv ℝ (p.raw τ) y (p.inlet i τ y)) := by
    rw [hEg y]
    exact ro_fderiv_equiv g (p.raw τ) hVd hVg y (p.inlet i τ y)
  unfold inletSourceR
  rw [hT, hR1, hL, hA1, hA2, hEg y]
  simp only [map_add, map_sub, map_smul]

/-- **Reality and `𝒪`-symmetry of the source** (SP 2355-2383). -/
theorem inletSourceRealO_of (hRaw : UnforcedLeray.Short.IIb.RawJointSmooth) :
    UnforcedLeray.Short.IIb.InletSourceRealO := by
  intro Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₁, h1, H1⟩ := inletJointSmooth Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₂, h2, H2⟩ := hRaw Sig lam q hSig hq dm dp hdm
  refine ⟨min ν₁ ν₂, lt_min h1 h2, ?_⟩
  intro p d hreg hν hSig' hmode i
  have e1 : p.ν ≤ ν₁ := hν.trans (min_le_left _ _)
  have e2 : p.ν ≤ ν₂ := hν.trans (min_le_right _ _)
  have hInl : ContDiff ℝ ∞ (fun x : ℝ × Space => p.inlet i x.1 x.2) :=
    H1 p d hreg e1 hSig' hmode i
  have hRaw' : ContDiff ℝ ∞ (fun x : ℝ × Space => p.raw x.1 x.2) :=
    H2 p d hreg e2 hSig' hmode i
  refine ⟨?_, ?_⟩
  · intro x
    exact ⟨inletSourceR p i x.1 x.2, inletSourceF_eq_realC hInl x.1 x.2⟩
  · intro g hg τ y
    rw [inletSourceF_eq_realC hInl τ (g.symm y), gC_realC,
      inletSourceF_eq_realC hInl τ y]
    congr 1
    have h := inletSourceR_equiv hInl hRaw' hg τ (g.symm y)
    rw [g.apply_symm_apply] at h
    exact h.symm

end UnforcedLeray.Short.IIb
