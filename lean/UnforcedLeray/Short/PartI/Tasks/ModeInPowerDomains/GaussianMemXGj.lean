import UnforcedLeray.Short.PartI.Sub.PartI_S10a
import UnforcedLeray.Units.B0121.Planar
import UnforcedLeray.Units.B0121.WeakDeriv
import UnforcedLeray.Units.B0059.NUE.P.Infra.Sobolev.Smooth
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Part I, task `PartI:S10a/2`: Gaussian-class smooth planar functions lie in every `X_{G,j}`
(source lines 913-929).

Proves `gaussianSmoothMemXGj : GaussianSmoothMemXGj`: if the planar function of `q ∈ X_G` agrees
a.e. with a smooth `F ∘ equivRealProd.symm` whose derivatives are bounded by polynomial times
`e^{-|y|²/4}`, then `q ∈ X_{G,j}` for every `j`.  The weak derivatives are the classical ones
(`hasWeakDerivOn_of_contDiffOn`), and `L²(ℝ², G⁻¹ dy)` integrability is by domination with
`e^{-|z|²/8}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.PlanarBS.Sob UnforcedLeray.B0121

/-- The real-linear coordinate map `(x, y) ↦ x + i y`. -/
def eL : ℝ × ℝ →L[ℝ] ℂ := Complex.equivRealProdCLM.symm.toContinuousLinearMap

theorem eL_apply (z : ℝ × ℝ) : eL z = Complex.equivRealProd.symm z := by
  simp [eL, Complex.equivRealProdCLM_symm_apply, Complex.equivRealProd_symm_apply]

theorem norm_eL_apply (z : ℝ × ℝ) : ‖eL z‖ = √(z.1 ^ 2 + z.2 ^ 2) := by
  rw [eL_apply, Complex.norm_eq_sqrt_sq_add_sq]
  simp

theorem sq_norm_eL_apply (z : ℝ × ℝ) : ‖eL z‖ ^ 2 = z.1 ^ 2 + z.2 ^ 2 := by
  rw [norm_eL_apply, Real.sq_sqrt (by positivity)]

/-- Directions appearing in `pdListR` have norm at most one. -/
theorem norm_pdListR_le (α : ℕ × ℕ) : ∀ v ∈ pdListR α, ‖v‖ ≤ 1 := by
  intro v hv
  simp only [pdListR, List.mem_append, List.mem_replicate] at hv
  rcases hv with ⟨_, rfl⟩ | ⟨_, rfl⟩
  · simp [ev, UnforcedLeray.B0094.e1]
  · simp [ev, UnforcedLeray.B0094.e2]

/-- Bound on the iterated directional derivatives of `F ∘ eL`. -/
theorem norm_iterDirDeriv_le {F : ℂ → ℂ} (hF : ContDiff ℝ ∞ F) {n : ℕ} {C : ℝ} {N : ℕ}
    (hb : ∀ y : ℂ, ‖iteratedFDeriv ℝ n F y‖ ≤ C * (1 + ‖y‖) ^ N * Real.exp (-(‖y‖ ^ 2) / 4))
    (vs : List (ℝ × ℝ)) (hn : vs.length = n) (hv : ∀ v ∈ vs, ‖v‖ ≤ 1) (z : ℝ × ℝ) :
    ‖iterDirDeriv vs (fun w => F (Complex.equivRealProd.symm w)) z‖ ≤
      (‖eL‖ ^ n * C) * ((1 + √(z.1 ^ 2 + z.2 ^ 2)) ^ N *
        Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 4)) := by
  have hfun : (fun w : ℝ × ℝ => F (Complex.equivRealProd.symm w)) = F ∘ eL := by
    funext w
    simp [eL_apply]
  have hFn : ContDiff ℝ n F := hF.of_le (by simp)
  have hG : ContDiff ℝ ∞ (F ∘ eL) := hF.comp eL.contDiff
  have hGn : ContDiffAt ℝ n (F ∘ eL) z := (hG.of_le (by simp)).contDiffAt
  rw [hfun, UnforcedLeray.B0059.NUE.Sob.iterDirDeriv_eq_iteratedFDeriv vs hn hGn,
    ContinuousLinearMap.iteratedFDeriv_comp_right eL hFn z le_rfl]
  have hprod : ∏ i : Fin n, ‖vs.get (Fin.cast hn.symm i)‖ ≤ 1 :=
    Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => hv _ (List.get_mem _ _))
  have hA := hb (eL z)
  rw [sq_norm_eL_apply, norm_eL_apply] at hA
  have hp : (0 : ℝ) ≤ ‖eL‖ ^ n := by positivity
  calc ‖((iteratedFDeriv ℝ n F (eL z)).compContinuousLinearMap fun _ => eL)
          (fun i => vs.get (Fin.cast hn.symm i))‖
      ≤ ‖(iteratedFDeriv ℝ n F (eL z)).compContinuousLinearMap fun _ => eL‖ *
          ∏ i : Fin n, ‖vs.get (Fin.cast hn.symm i)‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ ≤ (‖iteratedFDeriv ℝ n F (eL z)‖ * ∏ i : Fin n, ‖eL‖) * 1 := by
        refine mul_le_mul ?_ hprod (by positivity) (by positivity)
        exact ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖iteratedFDeriv ℝ n F (eL z)‖ * ‖eL‖ ^ n := by
        simp [Finset.prod_const]
    _ ≤ (C * (1 + √(z.1 ^ 2 + z.2 ^ 2)) ^ N * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 4)) * ‖eL‖ ^ n :=
        mul_le_mul_of_nonneg_right hA hp
    _ = (‖eL‖ ^ n * C) * ((1 + √(z.1 ^ 2 + z.2 ^ 2)) ^ N *
        Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 4)) := by ring

/-- A polynomial bound against the Gaussian: `(1+r)^{2k} ≤ D e^{r²/8}` for `r ≥ 0`. -/
theorem poly_le_exp_sq_div_eight (k : ℕ) :
    ∃ D : ℝ, ∀ r : ℝ, 0 ≤ r → (1 + r) ^ (2 * k) ≤ D * Real.exp (r ^ 2 / 8) := by
  refine ⟨2 ^ (2 * k - 1) * (1 + 8 ^ k * (k.factorial : ℝ)), fun r hr => ?_⟩
  have h1 := add_pow_le (zero_le_one) hr (2 * k)
  have hfac : (0 : ℝ) < (k.factorial : ℝ) := by positivity
  have h8 : (0 : ℝ) < 8 ^ k := by positivity
  have h2 : (r ^ 2 / 8) ^ k / (k.factorial : ℝ) ≤ Real.exp (r ^ 2 / 8) :=
    Real.pow_div_factorial_le_exp (r ^ 2 / 8) (by positivity) k
  have h2' : (r ^ 2) ^ k / 8 ^ k / (k.factorial : ℝ) ≤ Real.exp (r ^ 2 / 8) := by
    rw [← div_pow]
    exact h2
  have h2'' : (r ^ 2) ^ k / 8 ^ k ≤ Real.exp (r ^ 2 / 8) * (k.factorial : ℝ) :=
    (div_le_iff₀ hfac).1 h2'
  have h2''' : (r ^ 2) ^ k ≤ Real.exp (r ^ 2 / 8) * (k.factorial : ℝ) * 8 ^ k :=
    (div_le_iff₀ h8).1 h2''
  have h3 : r ^ (2 * k) ≤ 8 ^ k * (k.factorial : ℝ) * Real.exp (r ^ 2 / 8) := by
    rw [pow_mul]
    linarith
  have h4 : 1 ≤ Real.exp (r ^ 2 / 8) := Real.one_le_exp (by positivity)
  have hpos : (0 : ℝ) ≤ 2 ^ (2 * k - 1) := by positivity
  calc (1 + r) ^ (2 * k) ≤ 2 ^ (2 * k - 1) * (1 ^ (2 * k) + r ^ (2 * k)) := h1
    _ ≤ 2 ^ (2 * k - 1) * ((1 + 8 ^ k * (k.factorial : ℝ)) * Real.exp (r ^ 2 / 8)) := by
        refine mul_le_mul_of_nonneg_left ?_ hpos
        rw [one_pow]
        nlinarith
    _ = 2 ^ (2 * k - 1) * (1 + 8 ^ k * (k.factorial : ℝ)) * Real.exp (r ^ 2 / 8) := by ring

/-- `L²(ℝ², G⁻¹ dy)` membership from a continuous bound of polynomial-Gaussian type. -/
theorem memGaussL2_of_bound {φ : ℝ × ℝ → ℂ} (hφ : Continuous φ) {M : ℝ} {N : ℕ}
    (hb : ∀ z : ℝ × ℝ, ‖φ z‖ ≤
      M * ((1 + √(z.1 ^ 2 + z.2 ^ 2)) ^ N * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 4))) :
    MemGaussL2 φ := by
  have hc : Continuous (B0093.conjG φ) := by
    have e : B0093.conjG φ = fun z => (((sqG z)⁻¹ : ℝ) : ℂ) * φ z := funext (conjG_apply φ)
    rw [e]
    exact (Complex.continuous_ofReal.comp
      (contDiff_sqG.continuous.inv₀ fun z => (sqG_pos z).ne')).mul hφ
  obtain ⟨D, hD⟩ := poly_le_exp_sq_div_eight N
  have hI : Integrable (fun z : ℝ × ℝ => Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * 2))) := by
    have hb0 : 0 < 1 / (4 * 2 : ℝ) := by norm_num
    have h := (integrable_exp_neg_mul_sq hb0).mul_prod (integrable_exp_neg_mul_sq hb0)
    refine h.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only
    rw [← Real.exp_add]
    congr 1
    ring
  refine (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2 ?_
  refine Integrable.mono' (hI.const_mul (4 * Real.pi * M ^ 2 * D))
    (hc.norm.pow 2).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun z => ?_
  rw [Real.norm_of_nonneg (by positivity), norm_conjG_sq]
  have hgw : B0093.gaussianWeight z = (4 * Real.pi)⁻¹ * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 4) := by
    simp only [B0093.gaussianWeight, GaussianVortex.planarGaussian, GaussianVortex.radiusSq,
      neg_div]
  have hEpos : 0 < Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 4) := Real.exp_pos _
  have hinv : (B0093.gaussianWeight z)⁻¹ =
      4 * Real.pi * (Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 4))⁻¹ := by
    rw [hgw, mul_inv, inv_inv]
  have hr2 : (√(z.1 ^ 2 + z.2 ^ 2)) ^ 2 = z.1 ^ 2 + z.2 ^ 2 := Real.sq_sqrt (by positivity)
  have hr0 : 0 ≤ √(z.1 ^ 2 + z.2 ^ 2) := Real.sqrt_nonneg _
  have hpolyD := hD _ hr0
  rw [hr2] at hpolyD
  have hsq : ‖φ z‖ ^ 2 ≤
      (M * ((1 + √(z.1 ^ 2 + z.2 ^ 2)) ^ N * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 4))) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hb z) 2
  have hEE : Real.exp ((z.1 ^ 2 + z.2 ^ 2) / 8) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 4) =
      Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc ‖φ z‖ ^ 2 * (B0093.gaussianWeight z)⁻¹
      ≤ (M * ((1 + √(z.1 ^ 2 + z.2 ^ 2)) ^ N * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 4))) ^ 2 *
          (4 * Real.pi * (Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 4))⁻¹) := by
        rw [hinv]
        exact mul_le_mul_of_nonneg_right hsq (by positivity)
    _ = (4 * Real.pi * M ^ 2) * ((1 + √(z.1 ^ 2 + z.2 ^ 2)) ^ (2 * N) *
          Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 4)) := by
        field_simp
        ring
    _ ≤ (4 * Real.pi * M ^ 2) * ((D * Real.exp ((z.1 ^ 2 + z.2 ^ 2) / 8)) *
          Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 4)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right hpolyD hEpos.le
    _ = (4 * Real.pi * M ^ 2 * D) * (Real.exp ((z.1 ^ 2 + z.2 ^ 2) / 8) *
          Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 4)) := by ring
    _ = (4 * Real.pi * M ^ 2 * D) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * 2)) := by
        rw [hEE]

/-- **`PartI:S10a/2`: smooth Gaussian-class planar functions lie in every `X_{G,j}`**
(source lines 913-929). -/
theorem gaussianSmoothMemXGj : GaussianSmoothMemXGj := by
  intro q F hF hb hpl j
  choose C N hCN using hb
  refine (mem_XGj_iff_weakDerivs j q).2
    ⟨fun α => iterDirDeriv (pdListR α) (fun w => F (Complex.equivRealProd.symm w)),
      fun α _ => ?_⟩
  have hG : ContDiff ℝ ∞ (fun w : ℝ × ℝ => F (Complex.equivRealProd.symm w)) := by
    have e : (fun w : ℝ × ℝ => F (Complex.equivRealProd.symm w)) = F ∘ eL := by
      funext w
      simp [eL_apply]
    rw [e]
    exact hF.comp eL.contDiff
  have hcont : Continuous
      (iterDirDeriv (pdListR α) (fun w : ℝ × ℝ => F (Complex.equivRealProd.symm w))) :=
    (contDiff_iterDirDeriv hG (pdListR α)).continuous
  refine ⟨?_, ?_⟩
  · refine memGaussL2_of_bound hcont (M := ‖eL‖ ^ (pdListR α).length * C (pdListR α).length)
      (N := N (pdListR α).length) (fun z => ?_)
    exact norm_iterDirDeriv_le hF (hCN _) (pdListR α) rfl (norm_pdListR_le α) z
  · have hGn : ContDiff ℝ (pdListR α).length (fun w : ℝ × ℝ => F (Complex.equivRealProd.symm w)) :=
      hG.of_le (by simp)
    have hw := hasWeakDerivOn_of_contDiffOn isOpen_univ (vs := pdListR α)
      (n := (pdListR α).length) le_rfl hGn.contDiffOn
    intro φ hφ
    have e : (∫ x, planar q x * iterDirDeriv (pdListR α) φ x) =
        ∫ x, (fun w : ℝ × ℝ => F (Complex.equivRealProd.symm w)) x *
          iterDirDeriv (pdListR α) φ x :=
      integral_congr_ae (by
        filter_upwards [hpl] with x hx
        rw [hx])
    rw [e]
    exact hw φ hφ

end UnforcedLeray.Short.PartI
