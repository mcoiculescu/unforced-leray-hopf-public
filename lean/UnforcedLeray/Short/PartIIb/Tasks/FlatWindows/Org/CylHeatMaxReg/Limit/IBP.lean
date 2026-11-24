import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_4_4
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Complex.Basic

/-!
# Part II-b, task `PartII-b:T13/1/4/4/5` (`ChmIBP`): integration by parts on `Coord`

Source of record: `the November 2 reference manuscript` (SP) lines 1933-1935.
Integration by parts against a space-time test (Mathlib `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`)
in each direction, and symmetry of second derivatives of smooth functions.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

lemma chmIBP_ofReal_fderiv (φ : Coord → ℝ) (hφ : IsSTTestCoord φ) (x v : Coord) :
    fderiv ℝ (fun y => (φ y : ℂ)) x v = ((fderiv ℝ φ x v : ℝ) : ℂ) := by
  have hd : DifferentiableAt ℝ φ x := (hφ.smooth.differentiable (by simp)) x
  have h : fderiv ℝ (fun y => (φ y : ℂ)) x = Complex.ofRealCLM.comp (fderiv ℝ φ x) :=
    (Complex.ofRealCLM.hasFDerivAt.comp x hd.hasFDerivAt).fderiv
  rw [h]
  simp

lemma chmIBP_ofReal_contDiff (φ : Coord → ℝ) (hφ : IsSTTestCoord φ) :
    ContDiff ℝ ∞ (fun y => (φ y : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp hφ.smooth

lemma chmIBP_ofReal_cs (φ : Coord → ℝ) (hφ : IsSTTestCoord φ) :
    HasCompactSupport (fun y => (φ y : ℂ)) :=
  hφ.compact.comp_left Complex.ofReal_zero

lemma chmIBP_cdv_contDiff (w : Coord → ℂ) (hw : ContDiff ℝ ∞ w) (j : Fin 3) :
    ContDiff ℝ ∞ (cdv j w) := by
  unfold cdv
  exact (hw.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

/-- Integration by parts in one direction `j`. -/
lemma chmIBP_dir (w : Coord → ℂ) (hw : ContDiff ℝ ∞ w) (φ : Coord → ℝ) (hφ : IsSTTestCoord φ)
    (j : Fin 3) :
    ∫ x, w x * (cpd j φ x : ℂ) = -∫ x, cdv j w x * (φ x : ℂ) := by
  have hwc : Continuous w := hw.continuous
  have hψs := chmIBP_ofReal_contDiff φ hφ
  have hψc : Continuous (fun y => (φ y : ℂ)) := hψs.continuous
  have hψcs := chmIBP_ofReal_cs φ hφ
  have hD : Continuous (fun x => fderiv ℝ w x (cdir j)) :=
    (hw.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDψ : Continuous (fun x => fderiv ℝ (fun y => (φ y : ℂ)) x (cdir j)) :=
    (hψs.continuous_fderiv (by simp)).clm_apply continuous_const
  have hψD_cs : HasCompactSupport (fun x => fderiv ℝ (fun y => (φ y : ℂ)) x (cdir j)) :=
    hψcs.fderiv_apply ℝ (cdir j)
  have i1 : Integrable (fun x => fderiv ℝ w x (cdir j) * (φ x : ℂ)) :=
    (hD.mul hψc).integrable_of_hasCompactSupport hψcs.mul_left
  have i2 : Integrable (fun x => w x * fderiv ℝ (fun y => (φ y : ℂ)) x (cdir j)) :=
    (hwc.mul hDψ).integrable_of_hasCompactSupport hψD_cs.mul_left
  have i3 : Integrable (fun x => w x * (φ x : ℂ)) :=
    (hwc.mul hψc).integrable_of_hasCompactSupport hψcs.mul_left
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure Coord))
    (f := w) (g := fun y => (φ y : ℂ)) (v := cdir j) i1 i2 i3
    (fun x _ => (hw.differentiable (by simp)) x)
    (fun x _ => (hψs.differentiable (by simp)) x)
  have e1 : ∀ x, fderiv ℝ (fun y => (φ y : ℂ)) x (cdir j) = (cpd j φ x : ℂ) :=
    fun x => chmIBP_ofReal_fderiv φ hφ x (cdir j)
  simp only [e1] at key
  simpa only [cdv] using key

/-- Symmetry of the second derivatives of a smooth function, in the form used here. -/
lemma chmIBP_cdv_comm (w : Coord → ℂ) (hw : ContDiff ℝ ∞ w) (i j : Fin 3) (x : Coord) :
    cdv j (cdv i w) x = cdv i (cdv j w) x := by
  have hsymm : IsSymmSndFDerivAt ℝ w x := hw.contDiffAt.isSymmSndFDerivAt (by simp)
  have hdw : DifferentiableAt ℝ (fderiv ℝ w) x :=
    ((hw.fderiv_right (m := ∞) le_rfl).differentiable (by simp)) x
  have e : ∀ k l : Fin 3, cdv k (cdv l w) x = fderiv ℝ (fderiv ℝ w) x (cdir k) (cdir l) := by
    intro k l
    have hf := fderiv_clm_apply (𝕜 := ℝ) (c := fderiv ℝ w) (u := fun _ => cdir l) (x := x)
      hdw (differentiableAt_const _)
    have hf2 : fderiv ℝ (fun y => cdv l w y) x = (fderiv ℝ (fderiv ℝ w) x).flip (cdir l) := by
      have hfun : (fun y => cdv l w y) = fun y => (fderiv ℝ w y) ((fun _ => cdir l) y) := rfl
      rw [hfun, hf]
      simp
    unfold cdv
    rw [show fderiv ℝ (fun x_1 => fderiv ℝ w x_1 (cdir l)) x = fderiv ℝ (fun y => cdv l w y) x
      from rfl, hf2]
    simp
  rw [e j i, e i j]
  exact hsymm (cdir j) (cdir i)

theorem chmIBP : UnforcedLeray.Short.IIb.ChmIBP := by
  intro w hw φ hφ
  refine ⟨chmIBP_dir w hw φ hφ 0, fun i j => ?_⟩
  have hφ' := chmTestDeriv φ j.succ hφ
  have h1 := chmIBP_dir w hw (fun y => cpd j.succ φ y) hφ' i.succ
  have h2 := chmIBP_dir (cdv i.succ w) (chmIBP_cdv_contDiff w hw i.succ) φ hφ j.succ
  rw [h1, h2, neg_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [chmIBP_cdv_comm w hw i.succ j.succ x]

end UnforcedLeray.Short.IIb
