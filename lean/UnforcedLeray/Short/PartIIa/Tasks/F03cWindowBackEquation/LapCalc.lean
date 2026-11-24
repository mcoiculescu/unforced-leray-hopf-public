import UnforcedLeray.Short.PartIIa.Tasks.F03cWindowBackEquation.Transfer

/-!
# Part II-a, task `PartII-a:F03/3` helper: the spatial Laplacian `lapT` on vector and complex tests

Calculus used by `WindowBackEquation` (`Sub/F03.lean`) to pass from the phase Laplacian `lapT` of a
`ℂ³`-valued test to the scalar Laplacians `sLap` of real and imaginary parts:

* `lapT_add_gen`, `lapT_smul_gen`: additivity and real scalar multiples with a fixed vector;
* `lapT_clm`, `lapT_apply_comp`: `lapT` commutes with a continuous linear form `ℂ³ → ℂ`
  (so `(lapT Φ) c = lapT (Φ · c)`);
* `lapT_complex`: for a smooth `ℂ`-valued `ψ`, `lapT ψ = sLap (re ψ) + i · sLap (im ψ)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa.WinBack

open UnforcedLeray.PhaseSpace UnforcedLeray.Parabolic

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiff_dy_gen {f : ℝ × Space → F} (hf : ContDiff ℝ ∞ f) (j : Fin 3) :
    ContDiff ℝ ∞ (dy j f) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem dy_add_gen {f g : ℝ × Space → F} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (j : Fin 3) : dy j (fun p => f p + g p) = fun p => dy j f p + dy j g p := by
  funext p
  simp only [dy]
  rw [fderiv_fun_add (hf p) (hg p)]
  rfl

theorem lapT_add_gen {f g : ℝ × Space → F} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    lapT (fun p => f p + g p) = fun p => lapT f p + lapT g p := by
  funext p
  simp only [lapT]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : dy j (fun p => f p + g p) = fun p => dy j f p + dy j g p :=
    dy_add_gen (hf.differentiable (by simp)) (hg.differentiable (by simp)) j
  have hdf : Differentiable ℝ (dy j f) := (contDiff_dy_gen hf j).differentiable (by simp)
  have hdg : Differentiable ℝ (dy j g) := (contDiff_dy_gen hg j).differentiable (by simp)
  simp only [h1, dy_add_gen hdf hdg j]

theorem dy_smul_gen {s : ℝ × Space → ℝ} (hs : ContDiff ℝ ∞ s) (e : F) (j : Fin 3) :
    dy j (fun p => s p • e) = fun p => sD j (s : PS 3 → ℝ) p • e := by
  funext p
  simp only [dy]
  rw [fderiv_smul_const ((hs.differentiable (by simp)) p) e, ContinuousLinearMap.smulRight_apply]
  rfl

theorem contDiff_sD_gen {s : ℝ × Space → ℝ} (hs : ContDiff ℝ ∞ s) (j : Fin 3) :
    ContDiff ℝ ∞ (sD j (s : PS 3 → ℝ)) :=
  (hs.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem lapT_smul_gen {s : ℝ × Space → ℝ} (hs : ContDiff ℝ ∞ s) (e : F) (p : ℝ × Space) :
    lapT (fun p => s p • e) p = sLap (s : PS 3 → ℝ) p • e := by
  simp only [lapT]
  simp_rw [dy_smul_gen hs]
  simp_rw [dy_smul_gen (contDiff_sD_gen hs _)]
  rw [sLap, Finset.sum_smul]

/-- A continuous `ℂ`-linear form on `ℂ³` commutes with `dy`. -/
theorem dy_clm {L : CVec3 →L[ℂ] ℂ} {Φ : ℝ × Space → CVec3} (hΦ : Differentiable ℝ Φ)
    (j : Fin 3) : dy j (fun p => L (Φ p)) = fun p => L (dy j Φ p) := by
  funext p
  have h : fderiv ℝ (fun p => L (Φ p)) p = (L.restrictScalars ℝ).comp (fderiv ℝ Φ p) :=
    ((L.restrictScalars ℝ).hasFDerivAt.comp p (hΦ p).hasFDerivAt).fderiv
  simp only [dy]
  rw [h]
  rfl

theorem lapT_clm {L : CVec3 →L[ℂ] ℂ} {Φ : ℝ × Space → CVec3} (hΦ : ContDiff ℝ ∞ Φ)
    (p : ℝ × Space) : lapT (fun q => L (Φ q)) p = L (lapT Φ p) := by
  simp only [lapT]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hdy : Differentiable ℝ (dy j Φ) := (contDiff_dy_gen hΦ j).differentiable (by simp)
  rw [dy_clm (hΦ.differentiable (by simp)) j, dy_clm hdy j]

/-- The component `c` of `lapT Φ` is the Laplacian of the component `Φ · c`. -/
theorem lapT_apply_comp {Φ : ℝ × Space → CVec3} (hΦ : ContDiff ℝ ∞ Φ) (c : Fin 3)
    (p : ℝ × Space) : lapT (fun q => Φ q c) p = lapT Φ p c :=
  lapT_clm (L := EuclideanSpace.proj c) hΦ p

/-- Real and imaginary parts of a smooth complex test. -/
theorem lapT_complex {ψ : ℝ × Space → ℂ} (hψ : ContDiff ℝ ∞ ψ) (p : ℝ × Space) :
    lapT ψ p = ((sLap (fun q => (ψ q).re) p : ℝ) : ℂ) +
      ((sLap (fun q => (ψ q).im) p : ℝ) : ℂ) * Complex.I := by
  have hre : ContDiff ℝ ∞ (fun q => (ψ q).re) := Complex.reCLM.contDiff.comp hψ
  have him : ContDiff ℝ ∞ (fun q => (ψ q).im) := Complex.imCLM.contDiff.comp hψ
  have hdec : ψ = fun q => (ψ q).re • (1 : ℂ) + (ψ q).im • Complex.I := by
    funext q
    simp only [Complex.real_smul, mul_one]
    exact (Complex.re_add_im (ψ q)).symm
  have key : lapT ψ = lapT (fun q => (ψ q).re • (1 : ℂ) + (ψ q).im • Complex.I) :=
    congrArg lapT hdec
  rw [key, lapT_add_gen (f := fun q => (ψ q).re • (1 : ℂ)) (g := fun q => (ψ q).im • Complex.I)
    (hre.smul contDiff_const) (him.smul contDiff_const)]
  dsimp only
  rw [lapT_smul_gen (s := fun q => (ψ q).re) hre (1 : ℂ) p,
    lapT_smul_gen (s := fun q => (ψ q).im) him Complex.I p]
  simp only [Complex.real_smul, mul_one]

end UnforcedLeray.Short.PartIIa.WinBack
