import UnforcedLeray.Short.PartI.Sub.PartI_T04_8

/-!
# Part I, task `PartI:T04/8/4`, target `apEllipticD`: integrability of the curl jets

`curl f = lam ∘ Df` for a fixed continuous linear functional `lam`, so
`‖D^j (curl f) z‖ ≤ ‖lam‖ ‖D^{j+1} f z‖` (`ContinuousLinearMap.norm_iteratedFDeriv_comp_left`),
and `‖D^{j+1} f‖²` is integrable on the cell by hypothesis (`APEllipticData`, clause 6).
Measurability comes from continuity of `D^j (curl f)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

namespace APEllipticDaux

/-- The scalar curl evaluated at a derivative `A = Df`: `A (1,0) 1 - A (0,1) 0`. -/
def lam : (Plane →L[ℝ] Vec) →L[ℝ] ℝ :=
  (EuclideanSpace.proj (1 : Fin 2)).comp (ContinuousLinearMap.apply ℝ Vec ((1 : ℝ), (0 : ℝ)))
    - (EuclideanSpace.proj (0 : Fin 2)).comp (ContinuousLinearMap.apply ℝ Vec ((0 : ℝ), (1 : ℝ)))

theorem lam_apply (A : Plane →L[ℝ] Vec) : lam A = A (1, 0) 1 - A (0, 1) 0 := by
  simp [lam]

theorem partialQ_comp_eq {f : Plane → Vec} (hf : Differentiable ℝ f) (i : Fin 2) (z : Plane) :
    Cyl.partialQ (fun w => f w i) z = fderiv ℝ f z (1, 0) i := by
  have hd : Differentiable ℝ (fun w => f w i) :=
    ((EuclideanSpace.proj i : Vec →L[ℝ] ℝ).differentiable).comp hf
  rw [Cyl.partialQ_eq_fderiv hd z]
  have hD : fderiv ℝ (fun w => f w i) z =
      (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).comp (fderiv ℝ f z) :=
    ((EuclideanSpace.proj i : Vec →L[ℝ] ℝ).hasFDerivAt.comp z (hf z).hasFDerivAt).fderiv
  rw [hD]
  simp

theorem partialEta_comp_eq {f : Plane → Vec} (hf : Differentiable ℝ f) (i : Fin 2) (z : Plane) :
    Cyl.partialEta (fun w => f w i) z = fderiv ℝ f z (0, 1) i := by
  have hd : Differentiable ℝ (fun w => f w i) :=
    ((EuclideanSpace.proj i : Vec →L[ℝ] ℝ).differentiable).comp hf
  rw [Cyl.partialEta_eq_fderiv hd z]
  have hD : fderiv ℝ (fun w => f w i) z =
      (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).comp (fderiv ℝ f z) :=
    ((EuclideanSpace.proj i : Vec →L[ℝ] ℝ).hasFDerivAt.comp z (hf z).hasFDerivAt).fderiv
  rw [hD]
  simp

theorem curl_eq_lam {f : Plane → Vec} (hf : Differentiable ℝ f) (z : Plane) :
    Cyl.curl f z = lam (fderiv ℝ f z) := by
  rw [lam_apply, Cyl.curl, partialQ_comp_eq hf 1 z, partialEta_comp_eq hf 0 z]

theorem curl_fun_eq {f : Plane → Vec} (hf : ContDiff ℝ ∞ f) :
    Cyl.curl f = fun z => lam (fderiv ℝ f z) :=
  funext fun z => curl_eq_lam (hf.differentiable (by simp)) z

theorem curl_contDiff {f : Plane → Vec} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (Cyl.curl f) := by
  rw [curl_fun_eq hf]
  exact lam.contDiff.comp (hf.fderiv_right (m := ∞) (by simp))

theorem iteratedFDeriv_curl_le {f : Plane → Vec} (hf : ContDiff ℝ ∞ f) (j : ℕ) (z : Plane) :
    ‖iteratedFDeriv ℝ j (Cyl.curl f) z‖ ≤ ‖lam‖ * ‖iteratedFDeriv ℝ (j + 1) f z‖ := by
  rw [curl_fun_eq hf, ← norm_iteratedFDeriv_fderiv (𝕜 := ℝ)]
  exact lam.norm_iteratedFDeriv_comp_left
    ((hf.fderiv_right (m := ∞) (by simp)).contDiffAt) (by simp)

end APEllipticDaux

open APEllipticDaux in
/-- Target `apEllipticD`: `‖D^j (curl f)‖² ∈ L¹(cell)`. -/
theorem apEllipticD : APEllipticD := by
  intro j c f hdata
  obtain ⟨-, hf, -, -, -, hi⟩ := hdata
  have hcs : ContDiff ℝ ∞ (Cyl.curl f) := curl_contDiff hf
  have hint := (hi (j + 1)).const_mul (‖lam‖ ^ 2)
  have hcont : Continuous (fun z => ‖iteratedFDeriv ℝ j (Cyl.curl f) z‖ ^ 2) :=
    (hcs.continuous_iteratedFDeriv (m := j) (by simp)).norm.pow 2
  refine Integrable.mono' hint hcont.aestronglyMeasurable ?_
  refine ae_of_all _ fun z => ?_
  have h := iteratedFDeriv_curl_le hf j z
  have hn : 0 ≤ ‖iteratedFDeriv ℝ j (Cyl.curl f) z‖ := norm_nonneg _
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  calc ‖iteratedFDeriv ℝ j (Cyl.curl f) z‖ ^ 2
      ≤ (‖lam‖ * ‖iteratedFDeriv ℝ (j + 1) f z‖) ^ 2 := pow_le_pow_left₀ hn h 2
    _ = ‖lam‖ ^ 2 * ‖iteratedFDeriv ℝ (j + 1) f z‖ ^ 2 := mul_pow _ _ _

end UnforcedLeray.Short.PartI
