import UnforcedLeray.Short.PartI.Sub.PartI_T04_8
import UnforcedLeray.Short.PartI.Tasks.CylinderInterpolation.JetWord

/-!
# Part I, task `PartI:T04/8/3`, target `apEllipticC`: word bound for the curl

`wordCurlSq j f z ≤ 2^j * ‖D^j (curl f) z‖²`.  Route: `curl f = lam ∘ Df` for the continuous
linear functional `lam`, so `curl f` is smooth; each coordinate word of `curl f` is bounded by the
jet norm (`cylJetWord_proof`, first part), and there are at most `2^j` words.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

namespace APEllipticCaux

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
  have hD : fderiv ℝ (fun w => f w i) z = (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).comp (fderiv ℝ f z) :=
    ((EuclideanSpace.proj i : Vec →L[ℝ] ℝ).hasFDerivAt.comp z (hf z).hasFDerivAt).fderiv
  rw [hD]
  simp

theorem partialEta_comp_eq {f : Plane → Vec} (hf : Differentiable ℝ f) (i : Fin 2) (z : Plane) :
    Cyl.partialEta (fun w => f w i) z = fderiv ℝ f z (0, 1) i := by
  have hd : Differentiable ℝ (fun w => f w i) :=
    ((EuclideanSpace.proj i : Vec →L[ℝ] ℝ).differentiable).comp hf
  rw [Cyl.partialEta_eq_fderiv hd z]
  have hD : fderiv ℝ (fun w => f w i) z = (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).comp (fderiv ℝ f z) :=
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

theorem card_wordsOfLength_le (j : ℕ) : (wordsOfLength j).card ≤ 2 ^ j := by
  unfold wordsOfLength
  calc _ ≤ (Finset.univ : Finset (Fin j → Bool)).card := Finset.card_image_le
    _ = 2 ^ j := by simp

theorem length_of_mem_wordsOfLength {j : ℕ} {w : List Bool} (h : w ∈ wordsOfLength j) :
    w.length = j := by
  unfold wordsOfLength at h
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp h
  exact List.length_ofFn

end APEllipticCaux

open APEllipticCaux in
/-- Target `apEllipticC`: `wordCurlSq j f z ≤ 2^j * ‖D^j (curl f) z‖²`. -/
theorem apEllipticC : APEllipticC := by
  intro j c f hdata z
  obtain ⟨-, hf, -, -, -, -⟩ := hdata
  have hcs : ContDiff ℝ ∞ (Cyl.curl f) := curl_contDiff hf
  have hw : ∀ w ∈ wordsOfLength j,
      B0151.derivWord w (Cyl.curl f) z ^ 2 ≤ ‖iteratedFDeriv ℝ j (Cyl.curl f) z‖ ^ 2 := by
    intro w hwm
    have hlen : w.length = j := length_of_mem_wordsOfLength hwm
    have h1 := (cylJetWord_proof (Cyl.curl f) hcs j z).1 w hlen
    have h2 : ‖Train.jet j (Cyl.curl f) z‖ = ‖iteratedFDeriv ℝ j (Cyl.curl f) z‖ := rfl
    rw [← h2, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  unfold wordCurlSq
  calc ∑ w ∈ wordsOfLength j, B0151.derivWord w (Cyl.curl f) z ^ 2
      ≤ ∑ _w ∈ wordsOfLength j, ‖iteratedFDeriv ℝ j (Cyl.curl f) z‖ ^ 2 :=
        Finset.sum_le_sum hw
    _ = ((wordsOfLength j).card : ℝ) * ‖iteratedFDeriv ℝ j (Cyl.curl f) z‖ ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 ^ j * ‖iteratedFDeriv ℝ j (Cyl.curl f) z‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact_mod_cast card_wordsOfLength_le j

end UnforcedLeray.Short.PartI
