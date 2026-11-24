import UnforcedLeray.Lib.Sobolev.Jacobian
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# The weak chain rule under a smooth diffeomorphism (helper for INF11 target S6)

Scoping note `INF11-INF14-Sobolev.md` §5.1 (S6). Manuscript use: "the chain rule for weak
derivatives under smooth diffeomorphisms" (tex 1228–1237, B0062), dilations (tex 1569–1580,
B0102).

For `Φ : ℝⁿ ≃ₜ ℝⁿ` smooth with smooth inverse `Ψ = Φ⁻¹`, write `A i j x = (DΨ(x) eⱼ)ᵢ`
(`dsymm`). If `Gᵢ = ∂ᵢ f` weakly (locally integrable), then
`∂ⱼ (f ∘ Ψ) = ∑ᵢ A i j · (Gᵢ ∘ Ψ)` weakly (`hasWeakDeriv_comp_symm`).

The proof changes variables `x = Φ y` and uses the **Piola identity**
`∑ᵢ ∂ᵢ (jac Φ · A i j ∘ Φ) = 0` (`piola`). The Piola identity is not computed with cofactors:
both sides are continuous, and their pairings with every test `u` agree because
`∫ ∂ⱼ (u ∘ Ψ) = 0` after the same change of variables (fundamental lemma, then continuity).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Sob

variable {n : ℕ} (Φ : Eucl n ≃ₜ Eucl n) (hΦ : ContDiff ℝ ∞ Φ) (hΨ : ContDiff ℝ ∞ Φ.symm)

/-- `A i j x = (DΦ⁻¹(x) eⱼ)ᵢ`. -/
def dsymm (i j : Fin n) (x : Eucl n) : ℝ := fderiv ℝ Φ.symm x (e j) i

/-- The Piola coefficients `cᵢⱼ(y) = jac Φ y · A i j (Φ y)`. -/
def piolaCoeff (i j : Fin n) (y : Eucl n) : ℝ := jac Φ y * dsymm Φ i j (Φ y)

include hΨ in
theorem contDiff_dsymm (i j : Fin n) : ContDiff ℝ ∞ (dsymm Φ i j) :=
  (contDiff_coord i).comp ((hΨ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)

include hΦ hΨ in
theorem contDiff_piolaCoeff (i j : Fin n) : ContDiff ℝ ∞ (piolaCoeff Φ i j) :=
  (contDiff_jac Φ hΦ hΨ).mul ((contDiff_dsymm Φ hΨ i j).comp hΦ)

theorem contDiff_dir {φ : Eucl n → ℝ} (hφ : ContDiff ℝ ∞ φ) (v : Eucl n) :
    ContDiff ℝ ∞ (fun x => fderiv ℝ φ x v) := contDiff_dirDeriv hφ v

theorem integrable_of_cc {g : Eucl n → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    Integrable g volume := hg.continuous.integrable_of_hasCompactSupport hc

/-- `∑ᵢ (DΨ x eⱼ)ᵢ · L eᵢ = L (DΨ x eⱼ)`. -/
theorem sum_dsymm_smul {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : Eucl n →L[ℝ] G) (j : Fin n) (x : Eucl n) :
    ∑ i, dsymm Φ i j x • L (e i) = L (fderiv ℝ Φ.symm x (e j)) :=
  (clm_apply_eq_sum L _).symm

include hΦ hΨ in
/-- The integral of a directional derivative of a test function vanishes. -/
theorem integral_dir_eq_zero {g : Eucl n → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (v : Eucl n) : ∫ x, fderiv ℝ g x v = 0 := by
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun _ : Eucl n => (1 : ℝ)) (g := g) (v := v)
    (by simp) (by simpa using integrable_of_cc (contDiff_dir hg v) (hc.fderiv_apply ℝ v))
    (by simpa using integrable_of_cc hg hc) (fun x _ => differentiableAt_const _)
    (fun x _ => (hg.differentiable (by simp)) x)
  simpa using h

include hΦ hΨ in
/-- **Piola identity**: `∑ᵢ ∂ᵢ (jac Φ · A i j ∘ Φ) = 0`. -/
theorem piola (j : Fin n) (y : Eucl n) :
    ∑ i, fderiv ℝ (piolaCoeff Φ i j) y (e i) = 0 := by
  set P : Eucl n → ℝ := fun y => ∑ i, fderiv ℝ (piolaCoeff Φ i j) y (e i) with hP
  have hc : ∀ i, ContDiff ℝ ∞ (piolaCoeff Φ i j) := fun i => contDiff_piolaCoeff Φ hΦ hΨ i j
  have hPc : Continuous P :=
    continuous_finset_sum _ fun i _ => (contDiff_dir (hc i) (e i)).continuous
  suffices hae : P =ᵐ[volume] 0 by
    have := (hPc.ae_eq_iff_eq volume continuous_const).mp hae
    exact congrFun this y
  refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hPc.locallyIntegrable
    fun u hu huc => ?_
  simp only [smul_eq_mul]
  have hu' : ContDiff ℝ ∞ (fun x => u (Φ.symm x)) := hu.comp hΨ
  have huc' : HasCompactSupport (fun x => u (Φ.symm x)) := huc.comp_homeomorph Φ.symm
  -- `∫ u ∂ᵢ cᵢ = - ∫ ∂ᵢ u · cᵢ`
  have hibp : ∀ i, ∫ x, u x * fderiv ℝ (piolaCoeff Φ i j) x (e i) =
      -∫ x, fderiv ℝ u x (e i) * piolaCoeff Φ i j x := fun i =>
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (integrable_of_cc ((contDiff_dir hu (e i)).mul (hc i)) (huc.fderiv_apply ℝ (e i)).mul_right)
      (integrable_of_cc (hu.mul (contDiff_dir (hc i) (e i))) huc.mul_right)
      (integrable_of_cc (hu.mul (hc i)) huc.mul_right)
      (fun x _ => (hu.differentiable (by simp)) x)
      (fun x _ => ((hc i).differentiable (by simp)) x)
  -- `∑ᵢ ∂ᵢ u · cᵢ = jac Φ · (∂ⱼ (u ∘ Ψ)) ∘ Φ`
  have hpt : ∀ y, ∑ i, fderiv ℝ u y (e i) * piolaCoeff Φ i j y =
      jac Φ y * fderiv ℝ (fun x => u (Φ.symm x)) (Φ y) (e j) := by
    intro y
    have hch : fderiv ℝ (fun x => u (Φ.symm x)) (Φ y) =
        (fderiv ℝ u (Φ.symm (Φ y))).comp (fderiv ℝ Φ.symm (Φ y)) :=
      fderiv_comp (Φ y) ((hu.differentiable (by simp)) _) ((hΨ.differentiable (by simp)) _)
    rw [hch, Homeomorph.symm_apply_apply, ContinuousLinearMap.comp_apply,
      ← sum_dsymm_smul Φ (fderiv ℝ u y) j (Φ y), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [piolaCoeff, smul_eq_mul]
    ring
  calc ∫ x, u x * P x
      = ∑ i, ∫ x, u x * fderiv ℝ (piolaCoeff Φ i j) x (e i) := by
        rw [← integral_finsetSum]
        · congr 1 with x
          simp only [hP, Finset.mul_sum]
        · exact fun i _ => integrable_of_cc (hu.mul (contDiff_dir (hc i) (e i))) huc.mul_right
    _ = -∫ x, ∑ i, fderiv ℝ u x (e i) * piolaCoeff Φ i j x := by
        simp only [hibp]
        rw [integral_finsetSum, Finset.sum_neg_distrib]
        exact fun i _ => integrable_of_cc ((contDiff_dir hu (e i)).mul (hc i))
          (huc.fderiv_apply ℝ (e i)).mul_right
    _ = -∫ y, jac Φ y * fderiv ℝ (fun x => u (Φ.symm x)) (Φ y) (e j) := by
        simp only [hpt]
    _ = -∫ x, fderiv ℝ (fun x => u (Φ.symm x)) x (e j) := by
        rw [integral_comp_diffeo Φ hΦ (fun x => fderiv ℝ (fun x => u (Φ.symm x)) x (e j))]
        simp only [smul_eq_mul]
    _ = 0 := by rw [integral_dir_eq_zero Φ hΦ hΨ hu' huc', neg_zero]

include hΦ hΨ in
/-- The pointwise identity behind the chain rule: for a smooth `φ`,
`jac Φ y · ∂ⱼ φ (Φ y) = ∑ᵢ ∂ᵢ (cᵢⱼ · φ ∘ Φ) (y)`. -/
theorem jac_mul_dir_eq (φ : Eucl n → ℝ) (hφ : ContDiff ℝ ∞ φ) (j : Fin n) (y : Eucl n) :
    jac Φ y * fderiv ℝ φ (Φ y) (e j) =
      ∑ i, fderiv ℝ (fun z => piolaCoeff Φ i j z * φ (Φ z)) y (e i) := by
  have hc : ∀ i, ContDiff ℝ ∞ (piolaCoeff Φ i j) := fun i => contDiff_piolaCoeff Φ hΦ hΨ i j
  have hφΦ : ContDiff ℝ ∞ (fun z => φ (Φ z)) := hφ.comp hΦ
  have hprod : ∀ i, fderiv ℝ (fun z => piolaCoeff Φ i j z * φ (Φ z)) y (e i) =
      piolaCoeff Φ i j y * fderiv ℝ (fun z => φ (Φ z)) y (e i) +
        φ (Φ y) * fderiv ℝ (piolaCoeff Φ i j) y (e i) := by
    intro i
    have : fderiv ℝ (fun z => piolaCoeff Φ i j z * φ (Φ z)) y =
        piolaCoeff Φ i j y • fderiv ℝ (fun z => φ (Φ z)) y +
          φ (Φ y) • fderiv ℝ (piolaCoeff Φ i j) y :=
      fderiv_mul (((hc i).differentiable (by simp)) y) ((hφΦ.differentiable (by simp)) y)
    rw [this]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hch : fderiv ℝ (fun z => φ (Φ z)) y = (fderiv ℝ φ (Φ y)).comp (fderiv ℝ Φ y) :=
    fderiv_comp y ((hφ.differentiable (by simp)) _) ((hΦ.differentiable (by simp)) _)
  simp only [hprod, Finset.sum_add_distrib, ← Finset.mul_sum, piola Φ hΦ hΨ j y, mul_zero,
    add_zero, hch, ContinuousLinearMap.comp_apply]
  -- `∑ᵢ jac · Aᵢⱼ(Φ y) · Dφ(Φ y)(DΦ(y) eᵢ) = jac · Dφ(Φ y)(DΦ(y)(DΨ(Φ y) eⱼ))`
  have hL := sum_dsymm_smul Φ ((fderiv ℝ φ (Φ y)).comp (fderiv ℝ Φ y)) j (Φ y)
  have hid : (fderiv ℝ Φ y) (fderiv ℝ Φ.symm (Φ y) (e j)) = e j := by
    have := congrArg (fun L : Eucl n →L[ℝ] Eucl n => L (e j))
      (fderiv_comp_symm Φ hΦ hΨ (Φ y))
    simpa [Homeomorph.symm_apply_apply] using this
  rw [ContinuousLinearMap.comp_apply, hid] at hL
  rw [← hL, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [piolaCoeff, smul_eq_mul, ContinuousLinearMap.comp_apply]
  ring

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

include hΦ hΨ in
/-- **Weak chain rule** (S6, first order): if `Gᵢ = ∂ᵢ f` weakly, then
`∂ⱼ (f ∘ Φ⁻¹) = ∑ᵢ (DΦ⁻¹ eⱼ)ᵢ · Gᵢ ∘ Φ⁻¹` weakly. -/
theorem hasWeakDeriv_comp_symm {f : Eucl n → F} {G : Fin n → Eucl n → F}
    (hf : LocallyIntegrable f volume) (hG : ∀ i, LocallyIntegrable (G i) volume)
    (hw : ∀ i, HasWeakDeriv (wholeSpace n) [e i] f (G i)) (j : Fin n) :
    HasWeakDeriv (wholeSpace n) [e j] (fun x => f (Φ.symm x))
      (fun x => ∑ i, dsymm Φ i j x • G i (Φ.symm x)) := by
  have hloc : ∀ i, LocallyIntegrable (fun x => dsymm Φ i j x • G i (Φ.symm x)) volume :=
    fun i => (locallyIntegrable_comp_symm Φ hΦ hΨ (hG i)).continuous_smul
      (contDiff_dsymm Φ hΨ i j).continuous
  refine HasWeakDeriv.of_locallyIntegrable (locallyIntegrable_comp_symm Φ hΦ hΨ hf)
    (locallyIntegrable_finsetSum _ fun i _ => hloc i) fun φ hφ hφc => ?_
  simp only [iterDirDeriv_singleton, List.length_singleton, pow_one, neg_smul, one_smul]
  set θ : Fin n → Eucl n → ℝ := fun i z => piolaCoeff Φ i j z * φ (Φ z) with hθ
  have hθA : ∀ i, (wholeSpace n).Adm (θ i) := fun i =>
    ⟨(contDiff_piolaCoeff Φ hΦ hΨ i j).mul (hφ.comp hΦ), (hφc.comp_homeomorph Φ).mul_left⟩
  have hint : ∀ i, Integrable (fun y => fderiv ℝ (θ i) y (e i) • f y) volume := fun i =>
    integrable_smul_of_adm ((wholeSpace n).deriv_mem (hθA i) (e i)) hf
  have hint' : ∀ i, Integrable (fun y => θ i y • G i y) volume := fun i =>
    integrable_smul_of_adm (hθA i) (hG i)
  calc ∫ x, fderiv ℝ φ x (e j) • f (Φ.symm x)
      = ∫ y, jac Φ y • (fderiv ℝ φ (Φ y) (e j) • f (Φ.symm (Φ y))) :=
        integral_comp_diffeo Φ hΦ _
    _ = ∫ y, ∑ i, fderiv ℝ (θ i) y (e i) • f y := by
        congr 1 with y
        rw [Homeomorph.symm_apply_apply, smul_smul, jac_mul_dir_eq Φ hΦ hΨ φ hφ j y,
          Finset.sum_smul]
    _ = ∑ i, ∫ y, fderiv ℝ (θ i) y (e i) • f y := integral_finsetSum _ fun i _ => hint i
    _ = ∑ i, -∫ y, θ i y • G i y := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have := (hw i).identity (θ i) (hθA i)
        simpa only [iterDirDeriv_singleton, wholeSpace_μ, List.length_singleton, pow_one,
          neg_smul, one_smul] using this
    _ = -∫ y, jac Φ y • (φ (Φ y) • ∑ i, dsymm Φ i j (Φ y) • G i (Φ.symm (Φ y))) := by
        rw [Finset.sum_neg_distrib, ← integral_finsetSum _ fun i _ => hint' i]
        congr 2 with y
        simp only [Homeomorph.symm_apply_apply, Finset.smul_sum, smul_smul, hθ, piolaCoeff]
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        ring
    _ = -∫ x, φ x • ∑ i, dsymm Φ i j x • G i (Φ.symm x) := by
        rw [integral_comp_diffeo Φ hΦ (fun x => φ x • ∑ i, dsymm Φ i j x • G i (Φ.symm x))]

end UnforcedLeray.Sob
