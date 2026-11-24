import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_7_2.InletWeak.Calc
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.GEQIbp.Lemmas

/-!
# `PartIII-b:C/ward/12/3/1/2/5/1/2/7`: `inletYIBP_of`

Source `the November 2 reference manuscript`
lines 2385-2387.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.PhaseSpace MeasureTheory Set
open scoped ContDiff
open UnforcedLeray.Cons.C03.Concrete (Params IsSolTest pairF convT advT rep phaseInt)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Slice-by-slice integration by parts in `y_j` for a scalar smooth function against a scalar
phase test on `ℝ³`. -/
private theorem slice_ibp_dy_smooth' {P : ℝ} (j : Fin 3) {φ f : ℝ × UnforcedLeray.Space → ℂ}
    (hφ : IsPhaseTest P φ) (hf : ContDiff ℝ ∞ f) (t : ℝ) :
    ∫ y, dy j φ (t, y) * f (t, y) = -∫ y, φ (t, y) * dy j f (t, y) := by
  obtain ⟨R, hR⟩ := hφ.bounded_support
  obtain ⟨R', hR'⟩ := (hφ.dy j).bounded_support
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  have hdf := contDiff_dy' hf j
  have hφd : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
  have hdφ := contDiff_dy' hφ.smooth j
  have hc : ∀ {g : ℝ × UnforcedLeray.Space → ℂ},
      Continuous g → Continuous fun y : UnforcedLeray.Space => g (t, y) :=
    fun hg => hg.comp (continuous_const.prodMk continuous_id)
  have hfs : Differentiable ℝ (fun y : UnforcedLeray.Space => f (t, y)) :=
    hfd.comp ((differentiable_const t).prodMk differentiable_id)
  have hφs : Differentiable ℝ (fun y : UnforcedLeray.Space => φ (t, y)) :=
    hφd.comp ((differentiable_const t).prodMk differentiable_id)
  have e1 : ∀ y, fderiv ℝ (fun y' => f (t, y')) y (UnforcedLeray.coordinateVector j) =
      dy j f (t, y) := fun y => slice_fderiv hfd t y _
  have e2 : ∀ y, fderiv ℝ (fun y' => φ (t, y')) y (UnforcedLeray.coordinateVector j) =
      dy j φ (t, y) := fun y => slice_fderiv hφd t y _
  have I1 := integrable_mul_of_vanish (hc hdf.continuous) (hc hφ.smooth.continuous) R
    (fun y hy => hR t y hy)
  have I2 := integrable_mul_of_vanish (hc hf.continuous) (hc hdφ.continuous) R'
    (fun y hy => hR' t y hy)
  have I3 := integrable_mul_of_vanish (hc hf.continuous) (hc hφ.smooth.continuous) R
    (fun y hy => hR t y hy)
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun y : UnforcedLeray.Space => f (t, y))
    (g := fun y : UnforcedLeray.Space => φ (t, y))
    (v := UnforcedLeray.coordinateVector j)
    (by simpa only [e1] using I1.1) (by simpa only [e2] using I2.1) I3.1
    (fun x _ => hfs x) (fun x _ => hφs x)
  simp only [e1, e2] at key
  have a1 : (fun y => dy j φ (t, y) * f (t, y)) = fun y => f (t, y) * dy j φ (t, y) := by
    funext y; ring
  have a2 : (fun y => φ (t, y) * dy j f (t, y)) = fun y => dy j f (t, y) * φ (t, y) := by
    funext y; ring
  rw [a1, a2]
  exact key

/-- Integration by parts in `y_j` for `pairF` against any smooth field `G` (source 2385-2387):
for any phase test `Φ` and smooth vector field `G`, `pairF P (dy j Φ) G = pairF P Φ (-(dy j G))`. -/
private theorem pairF_dy_of_smooth' (P : ℝ) (j : Fin 3)
    {Φ G : ℝ × UnforcedLeray.Space → CVec3} (hΦ : IsPhaseTest P Φ) (hG : ContDiff ℝ ∞ G) :
    pairF P (dy j Φ) G = pairF P Φ (-(dy j G)) := by
  unfold pairF phaseInt
  congr 1
  congr 1
  funext t
  have hφk : ∀ k : Fin 3, IsPhaseTest P (fun x => Φ x k) :=
    fun k => isPhaseTest_comp_coord hΦ k
  have hGk : ∀ k : Fin 3, ContDiff ℝ ∞ (fun x => G x k) :=
    fun k => (contDiff_piLp_apply (p := 2) (i := k)).comp hG
  obtain ⟨R, hR⟩ := hΦ.bounded_support
  obtain ⟨R', hR'⟩ := (hΦ.dy j).bounded_support
  have hintL : ∀ k : Fin 3, Integrable (fun y : UnforcedLeray.Space =>
      dy j Φ (t, y) k * G (t, y) k) volume := by
    intro k
    have hcG : Continuous (fun y : UnforcedLeray.Space => G (t, y) k) :=
      (hGk k).continuous.comp (continuous_const.prodMk continuous_id)
    have hcΦ : Continuous (fun y : UnforcedLeray.Space => dy j Φ (t, y) k) :=
      ((contDiff_piLp_apply (p := 2) (i := k)).comp (hΦ.dy j).smooth).continuous.comp
        (continuous_const.prodMk continuous_id)
    exact (integrable_mul_of_vanish hcG hcΦ R' (fun y hy => by
      rw [hR' t y hy]; simp)).2
  have hintR : ∀ k : Fin 3, Integrable (fun y : UnforcedLeray.Space =>
      Φ (t, y) k * (-dy j G (t, y) k)) volume := by
    intro k
    have hcG : Continuous (fun y : UnforcedLeray.Space => -dy j G (t, y) k) :=
      (((contDiff_piLp_apply (p := 2) (i := k)).comp (contDiff_dy' hG j)).continuous.comp
        (continuous_const.prodMk continuous_id)).neg
    have hcΦ : Continuous (fun y : UnforcedLeray.Space => Φ (t, y) k) :=
      (hφk k).smooth.continuous.comp (continuous_const.prodMk continuous_id)
    exact (integrable_mul_of_vanish hcG hcΦ R (fun y hy => by
      rw [hR t y hy]; simp)).2
  simp only [dotL_apply, Pi.neg_apply, PiLp.neg_apply]
  rw [integral_finset_sum _ (fun k _ => hintL k),
    integral_finset_sum _ (fun k _ => hintR k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 := slice_ibp_dy_smooth' j (hφk k) (hGk k) t
  have eΦ : ∀ y, dy j (fun x => Φ x k) (t, y) = dy j Φ (t, y) k :=
    fun y => dy_comp_coord hΦ.smooth j k (t, y)
  have eG : ∀ y, dy j (fun x => G x k) (t, y) = dy j G (t, y) k :=
    fun y => dy_comp_coord hG j k (t, y)
  simp only [eΦ, eG] at h1
  have hneg : (fun y : UnforcedLeray.Space => Φ (t, y) k * (-dy j G (t, y) k)) =
      fun y => -(Φ (t, y) k * dy j G (t, y) k) := by
    funext y; ring
  rw [hneg, integral_neg, h1]

private theorem contDiff_raw_of_realC {p : Params}
    (hRC : ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space =>
      UnforcedLeray.B0412.realC (p.raw x.1 x.2))) :
    ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => p.raw x.1 x.2) := by
  apply (contDiff_piLp 2).2
  intro k
  have hcoord : (fun x : ℝ × UnforcedLeray.Space => (p.raw x.1 x.2).ofLp k) =
      fun x : ℝ × UnforcedLeray.Space => (UnforcedLeray.B0412.realC (p.raw x.1 x.2) k).re := by
    funext x
    simp [UnforcedLeray.B0412.realC_apply]
  rw [hcoord]
  exact Complex.reCLM.contDiff.comp ((contDiff_piLp_apply (p := 2) (i := k)).comp hRC)

theorem inletYIBP_of (hReg : InletFieldRegular) : InletYIBP := by
  intro lam q hq dm dp hdm
  obtain ⟨ν₀, hν₀, H0⟩ := hReg lam q hq dm dp hdm
  refine ⟨ν₀, hν₀, fun p d hreg hν hm z g hg i j Φ hΦ => ?_⟩
  obtain ⟨hRC, _, hE⟩ := H0 p d hreg hν hm z g hg
  have hR := contDiff_raw_of_realC hRC
  exact pairF_dy_of_smooth' p.period j hΦ (inletSrc_contDiff (hE i).1 hR)

end UnforcedLeray.Short.PartIIIb.Concrete
