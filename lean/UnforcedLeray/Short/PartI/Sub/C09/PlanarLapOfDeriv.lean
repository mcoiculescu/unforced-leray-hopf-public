import UnforcedLeray.Short.PartI.Sub.C09

/-!
# Part I, task `PartI:C09`, step 4b: the Laplacian commutes with weak derivatives

Source of record: `the November 2 reference manuscript`, lines 1141-1142
("differentiated and iterated"). Proves `planarLapOfDeriv : PlanarLapOfDeriv` (the definition
is in `Short/PartI/Sub/C09.lean`).

Proof idea. Let `Lφ = ∂₁²φ + ∂₂²φ`, `P = pdListR γ`, `ψ = ∂^γ φ`.
* `HasWeakDerivOn u P v` applied to the test function `Lφ` gives `∫ u ∂^γ(Lφ) = (-1)^|P| ∫ v Lφ`.
* For smooth `φ`, `∂^γ(Lφ) = L(∂^γ φ)` pointwise. Both sides are iterated directional
  derivatives over the lists `P ++ A` and `A ++ P` (`A = [e₀, e₀]` or `[e₁, e₁]`), which agree
  up to permutation (`B0121.iterDirDeriv_perm`).
* `WeakLapOn u F` applied to `ψ` gives `∫ u L(ψ) = ∫ F ψ`.
* `HasWeakDerivOn F P g` applied to `φ` gives `∫ F ∂^γ φ = (-1)^|P| ∫ g φ`.
Combining and cancelling the nonzero factor `(-1)^|P|` gives `∫ v Lφ = ∫ g φ`.
Only equalities of the given integrals are used, so no integrability hypotheses are needed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray UnforcedLeray.B0121 UnforcedLeray.PlanarBS.Sob

/-- The directional derivative is additive on smooth functions. -/
theorem pLap_dirDeriv_add {F G : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (v : ℝ × ℝ) :
    dirDeriv v (fun z => F z + G z) = fun z => dirDeriv v F z + dirDeriv v G z := by
  funext x
  have hF' : DifferentiableAt ℝ F x := (hF.differentiable (by simp)) x
  have hG' : DifferentiableAt ℝ G x := (hG.differentiable (by simp)) x
  have hd : fderiv ℝ (fun z => F z + G z) x = fderiv ℝ F x + fderiv ℝ G x :=
    (hF'.hasFDerivAt.add hG'.hasFDerivAt).fderiv
  show fderiv ℝ (fun z => F z + G z) x v = fderiv ℝ F x v + fderiv ℝ G x v
  rw [hd, add_apply]

/-- The iterated directional derivative is additive on smooth functions. -/
theorem pLap_iterDirDeriv_add (vs : List (ℝ × ℝ)) :
    ∀ f g : ℝ × ℝ → ℂ, ContDiff ℝ ∞ f → ContDiff ℝ ∞ g →
      iterDirDeriv vs (fun z => f z + g z) = fun z => iterDirDeriv vs f z + iterDirDeriv vs g z := by
  induction vs with
  | nil => intro f g _ _; rfl
  | cons v vs ih =>
    intro f g hf hg
    simp only [iterDirDeriv_cons]
    rw [ih f g hf hg]
    exact pLap_dirDeriv_add (contDiff_iterDirDeriv hf vs) (contDiff_iterDirDeriv hg vs) v

/-- For smooth `φ`, the order of two iterated directional derivatives can be exchanged. -/
theorem pLap_iterDirDeriv_comm {φ : ℝ × ℝ → ℂ} (h : ContDiff ℝ ∞ φ) (vs ws : List (ℝ × ℝ)) :
    iterDirDeriv vs (iterDirDeriv ws φ) = iterDirDeriv ws (iterDirDeriv vs φ) := by
  rw [← iterDirDeriv_append, ← iterDirDeriv_append]
  exact UnforcedLeray.B0121.iterDirDeriv_perm List.perm_append_comm h

/-- **Step 4b** (source lines 1141-1142): the Laplacian commutes with weak derivatives. -/
theorem planarLapOfDeriv : PlanarLapOfDeriv := by
  intro γ u F v g hu hv hF φ hφ
  have hs : ContDiff ℝ ∞ φ := hφ.smooth
  -- the test function `Lφ = ∂₁²φ + ∂₂²φ`
  have hA : IsTestFn univ
      (fun z => iterDirDeriv [ev 0, ev 0] φ z + iterDirDeriv [ev 1, ev 1] φ z) := by
    refine ⟨(contDiff_iterDirDeriv hs [ev 0, ev 0]).add
      (contDiff_iterDirDeriv hs [ev 1, ev 1]), ?_, subset_univ _⟩
    exact (hφ.iterDirDeriv [ev 0, ev 0]).compact.add (hφ.iterDirDeriv [ev 1, ev 1]).compact
  -- the test function `∂^γ φ`
  have hψ : IsTestFn univ (iterDirDeriv (pdListR γ) φ) := hφ.iterDirDeriv (pdListR γ)
  -- `∂^γ (Lφ) = L (∂^γ φ)` pointwise
  have E1 : iterDirDeriv (pdListR γ)
        (fun z => iterDirDeriv [ev 0, ev 0] φ z + iterDirDeriv [ev 1, ev 1] φ z)
      = fun z => iterDirDeriv [ev 0, ev 0] (iterDirDeriv (pdListR γ) φ) z
          + iterDirDeriv [ev 1, ev 1] (iterDirDeriv (pdListR γ) φ) z := by
    rw [pLap_iterDirDeriv_add (pdListR γ) _ _ (contDiff_iterDirDeriv hs [ev 0, ev 0])
        (contDiff_iterDirDeriv hs [ev 1, ev 1]),
      pLap_iterDirDeriv_comm hs (pdListR γ) [ev 0, ev 0],
      pLap_iterDirDeriv_comm hs (pdListR γ) [ev 1, ev 1]]
  have e : ∀ x : ℝ × ℝ,
      iterDirDeriv (pdListR γ)
        (fun z => iterDirDeriv [ev 0, ev 0] φ z + iterDirDeriv [ev 1, ev 1] φ z) x
      = iterDirDeriv [ev 0, ev 0] (iterDirDeriv (pdListR γ) φ) x
          + iterDirDeriv [ev 1, ev 1] (iterDirDeriv (pdListR γ) φ) x :=
    fun x => congrFun E1 x
  have h1 := hv _ hA
  have h2 := hu _ hψ
  have h3 := hF φ hφ
  simp only [e] at h1
  have key : (-1 : ℂ) ^ (pdListR γ).length *
        ∫ z, v z * (iterDirDeriv [ev 0, ev 0] φ z + iterDirDeriv [ev 1, ev 1] φ z)
      = (-1 : ℂ) ^ (pdListR γ).length * ∫ z, g z * φ z := by
    linear_combination -h1 + h2 + h3
  have hne : (-1 : ℂ) ^ (pdListR γ).length ≠ 0 := pow_ne_zero _ (by norm_num)
  exact mul_left_cancel₀ hne key

end UnforcedLeray.Short.PartI
