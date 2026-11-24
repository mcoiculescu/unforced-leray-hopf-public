import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_1.MovingCalc
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_1.AgeRange

/-!
# `PartIII-a:T21/2/2/2/1/2`: the moving substitution `Φ(ζ,y) = a⁻¹ φ(r(ζ), √a y)`

Source: `the November 2 reference manuscript` lines 2854-2865, 2919-2921, 3060.
Chain rule with `dr/dζ = -a²`, `a = 1 + ν r`, `d√a/dζ = (ν(-a²))/(2√a)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa.E0

open UnforcedLeray.Short.IIIa

theorem nu_movingZ_lt_one' {ν s : ℝ} (hν : 0 < ν) (hs : 0 ≤ s) : ν * movingZ ν s < 1 := by
  have hA : 0 < 1 + ν * s := by nlinarith [mul_nonneg hν.le hs]
  have e : ν * movingZ ν s = ν * s / (1 + ν * s) := by
    unfold movingZ clockA
    ring
  rw [e, div_lt_one hA]
  linarith

/-- The reverse age has derivative `-a²` (`a = clockA ν (revAge ν s ζ)`). -/
theorem revAge_hasDerivAt' {ν s ζ : ℝ} (hν : 0 < ν) (h : ν * (movingZ ν s - ζ) < 1) :
    HasDerivAt (fun ζ' => revAge ν s ζ') (-(clockA ν (revAge ν s ζ)) ^ 2) ζ := by
  have hn : HasDerivAt (fun ζ' => movingZ ν s - ζ') (-1) ζ := by
    simpa using (hasDerivAt_id ζ).const_sub (movingZ ν s)
  have hd : HasDerivAt (fun ζ' => 1 - ν * (movingZ ν s - ζ')) ν ζ := by
    have := (hn.const_mul ν).const_sub 1
    simpa using this
  have hne : 1 - ν * (movingZ ν s - ζ) ≠ 0 := by
    intro h0
    linarith
  have hq := hn.div hd hne
  have hfun : (fun ζ' => revAge ν s ζ') =
      (fun ζ' => (movingZ ν s - ζ') / (1 - ν * (movingZ ν s - ζ'))) := by
    funext ζ'
    unfold revAge ageOfZ
    rfl
  rw [hfun]
  refine HasDerivAt.congr_deriv (f' := (-1 * (1 - ν * (movingZ ν s - ζ)) -
      (movingZ ν s - ζ) * ν) / (1 - ν * (movingZ ν s - ζ)) ^ 2) hq ?_
  have hA : clockA ν (revAge ν s ζ) = 1 / (1 - ν * (movingZ ν s - ζ)) := by
    unfold revAge ageOfZ clockA
    field_simp
    ring
  rw [hA]
  field_simp
  ring

theorem joint_hasFDerivAt' {φ : ℝ → ℝ × ℝ → ℂ} {t s r : ℝ}
    (hJ : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ))
    (hr : r ∈ Ioo t s) (x : ℝ × ℝ) :
    HasFDerivAt (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2)
      (fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (r, x)) (r, x) := by
  have hnhds : Ico t s ×ˢ (univ : Set (ℝ × ℝ)) ∈ 𝓝 (r, x) := by
    apply Filter.mem_of_superset ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hr, mem_univ _⟩)
    exact Set.prod_mono Ioo_subset_Ico_self subset_rfl
  have hca := hJ.contDiffAt hnhds
  exact (hca.differentiableAt (by simp)).hasFDerivAt

theorem partial_r_hasDerivAt' (φ : ℝ → ℝ × ℝ → ℂ) (L : ℝ × (ℝ × ℝ) →L[ℝ] ℂ) (r0 : ℝ)
    (X : ℝ × ℝ) (hF : HasFDerivAt (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) L (r0, X)) :
    HasDerivAt (fun r' => φ r' X) (L (1, 0)) r0 := by
  have hc : HasDerivAt (fun r' : ℝ => (r', X)) ((1 : ℝ), (0 : ℝ × ℝ)) r0 :=
    (hasDerivAt_id r0).prodMk (hasDerivAt_const r0 X)
  exact hF.comp_hasDerivAt r0 hc

theorem spatial_fderiv' (φ : ℝ → ℝ × ℝ → ℂ) (L : ℝ × (ℝ × ℝ) →L[ℝ] ℂ) (r0 : ℝ)
    (X : ℝ × ℝ) (hF : HasFDerivAt (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) L (r0, X))
    (v : ℝ × ℝ) : fderiv ℝ (φ r0) X v = L (0, v) := by
  have hc : HasFDerivAt (fun x : ℝ × ℝ => (r0, x))
      ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) X :=
    (hasFDerivAt_const r0 X).prodMk (hasFDerivAt_id X)
  have h2 : HasFDerivAt (φ r0) (L.comp ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod
      (ContinuousLinearMap.id ℝ (ℝ × ℝ)))) X := hF.comp X hc
  rw [h2.fderiv]
  simp


theorem fderiv_decomp' (φ : ℝ → ℝ × ℝ → ℂ) (r0 : ℝ) (X : ℝ × ℝ)
    (L : ℝ × (ℝ × ℝ) →L[ℝ] ℂ)
    (hF : HasFDerivAt (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) L (r0, X)) (c a b : ℝ) :
    L (c, (a, b)) = (c : ℂ) * L (1, 0) + (a : ℂ) * fderiv ℝ (φ r0) X (B0579.dir 0) +
      (b : ℂ) * fderiv ℝ (φ r0) X (B0579.dir 1) := by
  have h0 : fderiv ℝ (φ r0) X (B0579.dir 0) = L (0, (1, 0)) := by
    rw [spatial_fderiv' φ L r0 X hF]
    simp [B0579.dir]
  have h1 : fderiv ℝ (φ r0) X (B0579.dir 1) = L (0, (0, 1)) := by
    rw [spatial_fderiv' φ L r0 X hF]
    simp [B0579.dir]
  rw [h0, h1]
  have e : ((c, (a, b)) : ℝ × (ℝ × ℝ)) = c • ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) +
      (a • ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) + b • ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))) := by
    ext <;> simp
  have e2 : L (c, (a, b)) = c • L (1, 0) + (a • L (0, (1, 0)) + b • L (0, (0, 1))) := by
    rw [e]
    simp only [map_add, map_smul]
    rfl
  rw [e2, Complex.real_smul, Complex.real_smul, Complex.real_smul]
  ring

theorem movingSubstitution (m : ℝ) : UnforcedLeray.Short.IIIa.E0.MovingSubstitution m := by
  intro ν hν tr t s ht hts g φ hφ ζ hζ y
  have hζ' := Set.mem_Ioo.mp hζ
  have hz : ν * (movingZ ν s - ζ) < 1 := by
    have hzs := nu_movingZ_lt_one' hν (ht.trans hts.le)
    nlinarith [mul_pos hν hζ'.1]
  have hR0 : revAge ν s ζ ∈ Ioo t s := adjRangeAge ν hν t s ht hts ζ hζ
  have hRpos : 0 < revAge ν s ζ := lt_of_le_of_lt ht hR0.1
  have hA0 : 0 < clockA ν (revAge ν s ζ) := by
    unfold clockA
    nlinarith [mul_pos hν hRpos]
  have hφR : ContDiff ℝ ∞ (φ (revAge ν s ζ)) := hφ.smooth _ (Ioo_subset_Ico_self hR0)
  have hF := joint_hasFDerivAt' hφ.jointSmooth hR0
    (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1, Real.sqrt (clockA ν (revAge ν s ζ)) * y.2)
  have hA' : HasDerivAt (fun ζ' => clockA ν (revAge ν s ζ'))
      (ν * -(clockA ν (revAge ν s ζ)) ^ 2) ζ :=
    ((revAge_hasDerivAt' hν hz).const_mul ν).const_add 1
  have hS' := hA'.sqrt hA0.ne'
  have hγ := (revAge_hasDerivAt' hν hz).prodMk ((hS'.mul_const y.1).prodMk (hS'.mul_const y.2))
  have hFγ := hF.comp_hasDerivAt ζ hγ
  have hInv := (hA'.inv hA0.ne').ofReal_comp
  have hprod := hInv.mul hFγ
  apply HasDerivAt.congr_deriv hprod
  -- atomic facts, all before abstracting
  have hAt : clockA ν (revAge ν s ζ) ^ (3 / 2 : ℝ) =
      clockA ν (revAge ν s ζ) * Real.sqrt (clockA ν (revAge ν s ζ)) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hA0, Real.rpow_one,
      Real.sqrt_eq_rpow]
  have hσsq : Real.sqrt (clockA ν (revAge ν s ζ)) ^ 2 = clockA ν (revAge ν s ζ) :=
    Real.sq_sqrt hA0.le
  have hσ0 : 0 < Real.sqrt (clockA ν (revAge ν s ζ)) := Real.sqrt_pos.2 hA0
  have hLv := fderiv_decomp' φ (revAge ν s ζ)
    (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1, Real.sqrt (clockA ν (revAge ν s ζ)) * y.2)
    _ hF
  have hLr := partial_r_hasDerivAt' φ _ (revAge ν s ζ)
    (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1, Real.sqrt (clockA ν (revAge ν s ζ)) * y.2) hF
  have hPhiFun : revPhi ν φ s ζ = fun y' => (((clockA ν (revAge ν s ζ))⁻¹ : ℝ) : ℂ) *
      φ (revAge ν s ζ) (Real.sqrt (clockA ν (revAge ν s ζ)) * y'.1,
        Real.sqrt (clockA ν (revAge ν s ζ)) * y'.2) := rfl
  have hK : ((clockA ν (revAge ν s ζ))⁻¹ : ℝ) = ((clockA ν (revAge ν s ζ))⁻¹ : ℝ) := rfl
  have hdPhi : ∀ k : Fin 2, pdCx k (revPhi ν φ s ζ) y =
      (((clockA ν (revAge ν s ζ))⁻¹ : ℝ) : ℂ) * ((Real.sqrt (clockA ν (revAge ν s ζ)) : ℂ) *
        pdCx k (φ (revAge ν s ζ)) (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1,
          Real.sqrt (clockA ν (revAge ν s ζ)) * y.2)) := by
    intro k
    have hg : Differentiable ℝ (fun y' : ℝ × ℝ => φ (revAge ν s ζ) (Real.sqrt (clockA ν (revAge ν s ζ)) * y'.1,
        Real.sqrt (clockA ν (revAge ν s ζ)) * y'.2)) := by
      intro z
      have hl : DifferentiableAt ℝ (fun y' : ℝ × ℝ => (Real.sqrt (clockA ν (revAge ν s ζ)) * y'.1,
          Real.sqrt (clockA ν (revAge ν s ζ)) * y'.2)) z := by fun_prop
      exact ((hφR.differentiable (by simp)) _).comp z hl
    rw [hPhiFun]
    have h1 := pdCx_const_mul _ hg (((clockA ν (revAge ν s ζ))⁻¹ : ℝ) : ℂ) k y
    rw [h1, pdCx_scale _ (hφR.differentiable (by simp)) _ k y]
  have hlapPhi : lapCx (revPhi ν φ s ζ) y =
      (((clockA ν (revAge ν s ζ))⁻¹ : ℝ) : ℂ) * (Real.sqrt (clockA ν (revAge ν s ζ)) : ℂ) ^ 2 *
        lapCx (φ (revAge ν s ζ)) (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1,
          Real.sqrt (clockA ν (revAge ν s ζ)) * y.2) := by
    rw [hPhiFun]
    exact lapCx_scale (φ (revAge ν s ζ)) hφR _ _ y
  have hσC0 : ((Real.sqrt (clockA ν (revAge ν s ζ)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hσ0.ne'
  have hθ : ((revTheta ν s ζ)⁻¹ : ℝ) = ν * clockA ν (revAge ν s ζ) := by
    unfold revTheta clockTheta
    rw [inv_inv]
  have hV : ∀ j : Fin 2, movingTrainV tr (revAge ν s ζ) y j =
      clockA ν (revAge ν s ζ) * Real.sqrt (clockA ν (revAge ν s ζ)) *
        tr.v (revAge ν s ζ) (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1,
          Real.sqrt (clockA ν (revAge ν s ζ)) * y.2) j := by
    intro j
    simp only [movingTrainV]
    rw [hAt]
  have hPy : revPhi ν φ s ζ y = (((clockA ν (revAge ν s ζ))⁻¹ : ℝ) : ℂ) *
      φ (revAge ν s ζ) (Real.sqrt (clockA ν (revAge ν s ζ)) * y.1,
        Real.sqrt (clockA ν (revAge ν s ζ)) * y.2) := rfl
  simp only [Function.comp_apply, Pi.inv_apply]
  rw [hLv]
  unfold dSharp dilCx transCx physKappa
  rw [hθ, hlapPhi, hdPhi 0, hdPhi 1, hPy, hV 0, hV 1, hLr.deriv]
  simp only [pdCx]
  generalize clockA ν (revAge ν s ζ) = A at *
  generalize Real.sqrt A = σ at *
  subst hσsq
  push_cast
  field_simp
  ring
