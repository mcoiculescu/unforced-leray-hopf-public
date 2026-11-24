import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import UnforcedLeray.Short.PartIIIa.Defs

/-!
# Helper for `PartIII-a:T21/c3/2/1/1/org/3/a/1/1`: integration by parts on the plane

Source: SP 2950-2954 (the integrations by parts of the free moving energy, here against a
compactly supported comparison function, so that no seam terms appear).

`pairing_identity`: for `g ∈ C²`, `h ∈ C²` with compact support, a divergence-free `C¹` field
`(v₀, v₁)` and a continuous compactly supported `h_t`,
`∫ ((νΔg - v·∇g) h + g h_t) = ∫ g (h_t + νΔh + v·∇h)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa.RelFreeTestSub.D1Aux

theorem pd_eq (j : Fin 2) (f : ℝ × ℝ → ℝ) :
    B0579.pd j f = fun x => fderiv ℝ f x (B0579.dir j) := rfl

theorem contDiff_pd_one {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f) (j : Fin 2) :
    ContDiff ℝ 1 (B0579.pd j f) := by
  rw [pd_eq]
  exact (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

theorem continuous_pd {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f) (j : Fin 2) :
    Continuous (B0579.pd j f) := by
  rw [pd_eq]
  exact (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem hasCompactSupport_pd {f : ℝ × ℝ → ℝ} (hf : HasCompactSupport f) (j : Fin 2) :
    HasCompactSupport (B0579.pd j f) := by
  rw [pd_eq]
  exact hf.fderiv_apply (𝕜 := ℝ) (B0579.dir j)

theorem integrable_of_cont_cs {f : ℝ × ℝ → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    Integrable f := hf.integrable_of_hasCompactSupport hc

/-- Integration by parts in the direction `j` against a compactly supported `g`. -/
theorem ibp_pd {f g : ℝ × ℝ → ℝ} (j : Fin 2) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) :
    ∫ x, B0579.pd j f x * g x = -∫ x, f x * B0579.pd j g x := by
  have h1 : Integrable (fun x => fderiv ℝ f x (B0579.dir j) * g x) := by
    refine integrable_of_cont_cs ((continuous_pd hf j).mul hg.continuous) ?_
    exact hgc.mul_left
  have h2 : Integrable (fun x => f x * fderiv ℝ g x (B0579.dir j)) := by
    refine integrable_of_cont_cs (hf.continuous.mul (continuous_pd hg j)) ?_
    exact (hasCompactSupport_pd hgc j).mul_left
  have h3 : Integrable (fun x => f x * g x) :=
    integrable_of_cont_cs (hf.continuous.mul hg.continuous) hgc.mul_left
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (v := B0579.dir j) h1 h2 h3 (fun x _ => (hf.differentiable (by norm_num)) x)
    (fun x _ => (hg.differentiable (by norm_num)) x)
  simp only [B0579.pd]
  rw [key, neg_neg]

/-- Two integrations by parts for the second derivative in the direction `j`. -/
theorem ibp_lap {f g : ℝ × ℝ → ℝ} (j : Fin 2) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) :
    ∫ x, B0579.pd j (B0579.pd j f) x * g x = ∫ x, f x * B0579.pd j (B0579.pd j g) x := by
  have e1 := ibp_pd j (contDiff_pd_one hf j) (hg.of_le (by norm_num)) hgc
  have e2 := ibp_pd j (hf.of_le (by norm_num)) (contDiff_pd_one hg j)
    (hasCompactSupport_pd hgc j)
  rw [e1, e2, neg_neg]

theorem pd_mul {w g : ℝ × ℝ → ℝ} (hw : Differentiable ℝ w) (hg : Differentiable ℝ g)
    (j : Fin 2) (x : ℝ × ℝ) :
    B0579.pd j (fun x => w x * g x) x = B0579.pd j w x * g x + w x * B0579.pd j g x := by
  simp only [B0579.pd]
  change (fderiv ℝ (w * g) x) (B0579.dir j) = _
  rw [((hw x).hasFDerivAt.mul (hg x).hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- Integration by parts for the transport term `w ∂_j f` against `g`. -/
theorem ibp_transport {f g w : ℝ × ℝ → ℝ} (j : Fin 2) (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 1 g) (hw : ContDiff ℝ 1 w) (hgc : HasCompactSupport g) :
    ∫ x, w x * B0579.pd j f x * g x =
      -∫ x, f x * (B0579.pd j w x * g x + w x * B0579.pd j g x) := by
  have hwg : ContDiff ℝ 1 (fun x => w x * g x) := hw.mul hg
  have hwgc : HasCompactSupport (fun x => w x * g x) := hgc.mul_left
  have e := ibp_pd j hf hwg hwgc
  have e2 : (fun x => w x * B0579.pd j f x * g x) = fun x => B0579.pd j f x * (w x * g x) := by
    funext x; ring
  rw [e2, e]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only []
  rw [pd_mul (hw.differentiable (by norm_num)) (hg.differentiable (by norm_num))]

/-- **The pairing identity** (after the integrations by parts): with `div v = 0`,
`∫ ((νΔg - v·∇g) h + g h_t) = ∫ g (h_t + νΔh + v·∇h)`. -/
theorem pairing_identity {g h ht v0 v1 : ℝ × ℝ → ℝ} (ν : ℝ) (hg : ContDiff ℝ 2 g)
    (hh : ContDiff ℝ 2 h) (hhc : HasCompactSupport h) (hv0 : ContDiff ℝ 1 v0)
    (hv1 : ContDiff ℝ 1 v1) (hdiv : ∀ x, B0579.pd 0 v0 x + B0579.pd 1 v1 x = 0)
    (htc : Continuous ht) (htcs : HasCompactSupport ht) :
    ∫ x, ((ν * lapP g x - (v0 x * B0579.pd 0 g x + v1 x * B0579.pd 1 g x)) * h x + g x * ht x) =
      ∫ x, g x * (ht x + ν * lapP h x + (v0 x * B0579.pd 0 h x + v1 x * B0579.pd 1 h x)) := by
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have hh1 : ContDiff ℝ 1 h := hh.of_le (by norm_num)
  have cg := hg.continuous
  have ch := hh.continuous
  have cpg0 := continuous_pd hg1 0
  have cpg1 := continuous_pd hg1 1
  have cpph0 := continuous_pd (contDiff_pd_one hg 0) 0
  have cpph1 := continuous_pd (contDiff_pd_one hg 1) 1
  have cph0 := continuous_pd hh1 0
  have cph1 := continuous_pd hh1 1
  have cpphh0 := continuous_pd (contDiff_pd_one hh 0) 0
  have cpphh1 := continuous_pd (contDiff_pd_one hh 1) 1
  have cv0 := hv0.continuous
  have cv1 := hv1.continuous
  have cpv0 := continuous_pd hv0 0
  have cpv1 := continuous_pd hv1 1
  -- integrability of every term (all carry a compactly supported factor)
  have ihs : ∀ {k : ℝ × ℝ → ℝ}, Continuous k → Integrable (fun x => k x * h x) := fun hk =>
    integrable_of_cont_cs (hk.mul ch) hhc.mul_left
  have i1 : Integrable (fun x => B0579.pd 0 (B0579.pd 0 g) x * h x) := ihs cpph0
  have i2 : Integrable (fun x => B0579.pd 1 (B0579.pd 1 g) x * h x) := ihs cpph1
  have i3 : Integrable (fun x => v0 x * B0579.pd 0 g x * h x) := ihs (cv0.mul cpg0)
  have i4 : Integrable (fun x => v1 x * B0579.pd 1 g x * h x) := ihs (cv1.mul cpg1)
  have i5 : Integrable (fun x => g x * ht x) :=
    integrable_of_cont_cs (cg.mul htc) htcs.mul_left
  have ics : ∀ {k : ℝ × ℝ → ℝ}, Continuous k → HasCompactSupport k →
      Integrable (fun x => g x * k x) := fun hk hkc =>
    integrable_of_cont_cs (cg.mul hk) hkc.mul_left
  have j1 : Integrable (fun x => g x * B0579.pd 0 (B0579.pd 0 h) x) :=
    ics cpphh0 (hasCompactSupport_pd (hasCompactSupport_pd hhc 0) 0)
  have j2 : Integrable (fun x => g x * B0579.pd 1 (B0579.pd 1 h) x) :=
    ics cpphh1 (hasCompactSupport_pd (hasCompactSupport_pd hhc 1) 1)
  have j3 : Integrable (fun x => g x * (B0579.pd 0 v0 x * h x + v0 x * B0579.pd 0 h x)) :=
    ics ((cpv0.mul ch).add (cv0.mul cph0))
      ((hhc.mul_left).add ((hasCompactSupport_pd hhc 0).mul_left))
  have j4 : Integrable (fun x => g x * (B0579.pd 1 v1 x * h x + v1 x * B0579.pd 1 h x)) :=
    ics ((cpv1.mul ch).add (cv1.mul cph1))
      ((hhc.mul_left).add ((hasCompactSupport_pd hhc 1).mul_left))
  have L1 := ibp_lap 0 hg hh hhc
  have L2 := ibp_lap 1 hg hh hhc
  have T1 := ibp_transport 0 hg1 hh1 hv0 hhc
  have T2 := ibp_transport 1 hg1 hh1 hv1 hhc
  -- expand the left side
  have eL : (fun x => (ν * lapP g x - (v0 x * B0579.pd 0 g x + v1 x * B0579.pd 1 g x)) * h x +
      g x * ht x) = fun x => ν * (B0579.pd 0 (B0579.pd 0 g) x * h x) +
        ν * (B0579.pd 1 (B0579.pd 1 g) x * h x) - v0 x * B0579.pd 0 g x * h x -
          v1 x * B0579.pd 1 g x * h x + g x * ht x := by
    funext x; simp only [lapP]; ring
  have eR : (fun x => g x * (ht x + ν * lapP h x +
      (v0 x * B0579.pd 0 h x + v1 x * B0579.pd 1 h x))) = fun x =>
        ν * (g x * B0579.pd 0 (B0579.pd 0 h) x) + ν * (g x * B0579.pd 1 (B0579.pd 1 h) x) +
          g x * (B0579.pd 0 v0 x * h x + v0 x * B0579.pd 0 h x) +
          g x * (B0579.pd 1 v1 x * h x + v1 x * B0579.pd 1 h x) + g x * ht x := by
    funext x
    simp only [lapP]
    have hd := hdiv x
    linear_combination (-(g x * h x)) * hd
  rw [eL, eR]
  have iA : Integrable (fun x => ν * (B0579.pd 0 (B0579.pd 0 g) x * h x)) := i1.const_mul ν
  have iB : Integrable (fun x => ν * (B0579.pd 1 (B0579.pd 1 g) x * h x)) := i2.const_mul ν
  have iAB : Integrable (fun x => ν * (B0579.pd 0 (B0579.pd 0 g) x * h x) +
      ν * (B0579.pd 1 (B0579.pd 1 g) x * h x)) := iA.add iB
  have iABC : Integrable (fun x => ν * (B0579.pd 0 (B0579.pd 0 g) x * h x) +
      ν * (B0579.pd 1 (B0579.pd 1 g) x * h x) - v0 x * B0579.pd 0 g x * h x) := iAB.sub i3
  have iABCD : Integrable (fun x => ν * (B0579.pd 0 (B0579.pd 0 g) x * h x) +
      ν * (B0579.pd 1 (B0579.pd 1 g) x * h x) - v0 x * B0579.pd 0 g x * h x -
        v1 x * B0579.pd 1 g x * h x) := iABC.sub i4
  rw [integral_add iABCD i5, integral_sub iABC i4, integral_sub iAB i3, integral_add iA iB,
    integral_const_mul, integral_const_mul]
  have jA : Integrable (fun x => ν * (g x * B0579.pd 0 (B0579.pd 0 h) x)) := j1.const_mul ν
  have jB : Integrable (fun x => ν * (g x * B0579.pd 1 (B0579.pd 1 h) x)) := j2.const_mul ν
  have jAB : Integrable (fun x => ν * (g x * B0579.pd 0 (B0579.pd 0 h) x) +
      ν * (g x * B0579.pd 1 (B0579.pd 1 h) x)) := jA.add jB
  have jABC : Integrable (fun x => ν * (g x * B0579.pd 0 (B0579.pd 0 h) x) +
      ν * (g x * B0579.pd 1 (B0579.pd 1 h) x) +
        g x * (B0579.pd 0 v0 x * h x + v0 x * B0579.pd 0 h x)) := jAB.add j3
  have jABCD : Integrable (fun x => ν * (g x * B0579.pd 0 (B0579.pd 0 h) x) +
      ν * (g x * B0579.pd 1 (B0579.pd 1 h) x) +
        g x * (B0579.pd 0 v0 x * h x + v0 x * B0579.pd 0 h x) +
        g x * (B0579.pd 1 v1 x * h x + v1 x * B0579.pd 1 h x)) := jABC.add j4
  rw [integral_add jABCD i5, integral_add jABC j4, integral_add jAB j3, integral_add jA jB,
    integral_const_mul, integral_const_mul]
  rw [L1, L2, T1, T2]
  ring

end UnforcedLeray.Short.IIIa.RelFreeTestSub.D1Aux
