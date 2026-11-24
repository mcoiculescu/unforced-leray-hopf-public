import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_1_2_3

/-!


Source: `the November 2 reference manuscript`
(SP 2074-2105).

For a separated sum `φ r x = Σ_k χ_k r * ψ_k x` (`CylSepSum`), the inner integral
`cylTdInner tr ω φ r` equals, for `r ∈ (t₀,t₁)`,
`Σ_k (χ_k'(r) * G_k(r) + χ_k(r) * H_k(r))`, where
`G_k(r) = ∫_cell ω r * ψ_k` (continuous on `[t₀,t₁]` by the weak identity and
`timeIntegrable`) and `H_k(r) = ∫_cell cylFreeIntegrand tr (ω r) r ψ_k` (interval integrable
by `timeIntegrable`). The derivative `deriv (χ_k)` is measurable everywhere.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal Interval
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

/-- Linearity of the first derivative for finite linear combinations of test functions. -/
theorem cylMeas_pd_sum {n : ℕ} (a : Fin n → ℝ) (ψ : Fin n → B0579.Plane → ℝ)
    (hψ : ∀ k, Differentiable ℝ (ψ k)) (j : Fin 2) :
    B0579.pd j (fun y => ∑ k, a k * ψ k y) = fun y => ∑ k, a k * B0579.pd j (ψ k) y := by
  funext x
  simp only [B0579.pd]
  rw [fderiv_fun_sum (A := fun k y => a k * ψ k y) (fun k _ => (hψ k x).const_mul (a k))]
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [fderiv_const_mul (hψ k x), ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- Linearity of the Laplacian for finite linear combinations of test functions. -/
theorem cylMeas_lapP_sum {c : ℝ} {n : ℕ} (a : Fin n → ℝ) (ψ : Fin n → B0579.Plane → ℝ)
    (hψ : ∀ k, B0579.IsCylTest c (ψ k)) (x : B0579.Plane) :
    lapP (fun y => ∑ k, a k * ψ k y) x = ∑ k, a k * lapP (ψ k) x := by
  have D : ∀ k, Differentiable ℝ (ψ k) := fun k => (hψ k).differentiable
  have D0 : ∀ k, Differentiable ℝ (B0579.pd 0 (ψ k)) := fun k => ((hψ k).pd 0).differentiable
  have D1 : ∀ k, Differentiable ℝ (B0579.pd 1 (ψ k)) := fun k => ((hψ k).pd 1).differentiable
  have e0 : B0579.pd 0 (fun y => ∑ k, a k * ψ k y) = fun y => ∑ k, a k * B0579.pd 0 (ψ k) y :=
    cylMeas_pd_sum a ψ D 0
  have e1 : B0579.pd 1 (fun y => ∑ k, a k * ψ k y) = fun y => ∑ k, a k * B0579.pd 1 (ψ k) y :=
    cylMeas_pd_sum a ψ D 1
  have f00 : B0579.pd 0 (fun y => ∑ k, a k * B0579.pd 0 (ψ k) y)
      = fun y => ∑ k, a k * B0579.pd 0 (B0579.pd 0 (ψ k)) y :=
    cylMeas_pd_sum a (fun k => B0579.pd 0 (ψ k)) D0 0
  have f11 : B0579.pd 1 (fun y => ∑ k, a k * B0579.pd 1 (ψ k) y)
      = fun y => ∑ k, a k * B0579.pd 1 (B0579.pd 1 (ψ k)) y :=
    cylMeas_pd_sum a (fun k => B0579.pd 1 (ψ k)) D1 1
  simp only [lapP]
  rw [e0, e1, f00, f11]
  dsimp only
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- The derivative in age of a separated sum at an interior age. -/
theorem cylMeas_deriv_sum {n : ℕ} (χ : Fin n → ℝ → ℝ) (ψ : Fin n → B0579.Plane → ℝ) (r : ℝ)
    (x : B0579.Plane) (hd : ∀ k, DifferentiableAt ℝ (χ k) r) (g : ℝ → B0579.Plane → ℝ)
    (hg : ∀ r' y, g r' y = ∑ k, χ k r' * ψ k y) :
    deriv (fun r' => g r' x) r = ∑ k, deriv (χ k) r * ψ k x := by
  have hfun : (fun r' => g r' x) = fun r' => ∑ k, χ k r' * ψ k x :=
    funext fun r' => hg r' x
  rw [hfun]
  apply HasDerivAt.deriv
  apply HasDerivAt.fun_sum (A := fun k r' => χ k r' * ψ k x)
    (A' := fun k => deriv (χ k) r * ψ k x)
  intro k _
  exact (hd k).hasDerivAt.mul_const (ψ k x)

/-- A weighted test sum in the cell: `ω * ψ` is integrable on the cell when `ω ∈ X_m`. -/
theorem cylMeas_integrableOn_test {m c : ℝ} {g ψ : B0579.Plane → ℝ}
    (hg : MemLp g 2 (B0579.cellMeasure c m)) (hψ : B0579.IsCylTest c ψ) :
    IntegrableOn (fun x => g x * ψ x) (B0579.cell c) := by
  have h := B0579.integrableOn_mul_neg c m (hg.toLp g) (B0579.testLp c (-m) hψ)
  refine Integrable.congr h ?_
  filter_upwards [(B0579.ac_cellMeasure c m).ae_le (MemLp.coeFn_toLp hg),
    B0579.coeFn_testLp c (-m) hψ] with x h1 h2
  simp only [h1, h2]

end UnforcedLeray.Short.IIb

open UnforcedLeray UnforcedLeray.Short.IIb in
theorem cylTdRhsMeas : UnforcedLeray.Short.IIb.CylTdRhsMeas := by
  intro m ν c tr t₀ f ω t₁ φ φs M H n
  obtain ⟨hm, hc, hfl, ht, -, hsep, -, -⟩ := H
  obtain ⟨N, χ, ψ, hχ, hψ, hsum⟩ := hsep n
  -- `G_k` is continuous on `[t₀, t₁]` by the weak identity for the test `ψ_k`.
  have hG : ∀ k, ContinuousOn (fun r => ∫ x in B0579.cell c, ω r x * ψ k x) (Icc t₀ t₁) := by
    intro k
    have hI : IntervalIntegrable
        (fun r => ∫ x in B0579.cell c, cylFreeIntegrand tr (ω r) r (ψ k) x) volume t₀ t₁ :=
      hfl.timeIntegrable (ψ k) (hψ k) t₁ ht
    have hP : ContinuousOn
        (fun b => ∫ r in t₀..b, ∫ x in B0579.cell c, cylFreeIntegrand tr (ω r) r (ψ k) x)
        (Icc t₀ t₁) := by
      have := intervalIntegral.continuousOn_primitive_interval' hI left_mem_uIcc
      rwa [Set.uIcc_of_le ht] at this
    have hC : ContinuousOn
        (fun r => (∫ x in B0579.cell c, f x * ψ k x) +
          ∫ r' in t₀..r, ∫ x in B0579.cell c, cylFreeIntegrand tr (ω r') r' (ψ k) x)
        (Icc t₀ t₁) :=
      continuousOn_const.add hP
    refine hC.congr fun r hr => ?_
    exact hfl.weak (ψ k) (hψ k) r hr.1
  have hGm : ∀ k, AEStronglyMeasurable (fun r => ∫ x in B0579.cell c, ω r x * ψ k x)
      (volume.restrict (Ioc t₀ t₁)) :=
    fun k => ((hG k).aestronglyMeasurable measurableSet_Icc).mono_set Ioc_subset_Icc_self
  have hχm : ∀ k, AEStronglyMeasurable (χ k) (volume.restrict (Ioc t₀ t₁)) :=
    fun k => (((hχ k).continuousOn).aestronglyMeasurable measurableSet_Icc).mono_set
      Ioc_subset_Icc_self
  have hHm : ∀ k, AEStronglyMeasurable
      (fun r => ∫ x in B0579.cell c, cylFreeIntegrand tr (ω r) r (ψ k) x)
      (volume.restrict (Ioc t₀ t₁)) :=
    fun k => (hfl.timeIntegrable (ψ k) (hψ k) t₁ ht).1.aestronglyMeasurable
  have hDm : ∀ k, AEStronglyMeasurable (deriv (χ k)) (volume.restrict (Ioc t₀ t₁)) :=
    fun k => (measurable_deriv (χ k)).aestronglyMeasurable
  have hFm : AEStronglyMeasurable
      (fun r => ∑ k, (deriv (χ k) r * (∫ x in B0579.cell c, ω r x * ψ k x) +
        χ k r * ∫ x in B0579.cell c, cylFreeIntegrand tr (ω r) r (ψ k) x))
      (volume.restrict (Ioc t₀ t₁)) :=
    Finset.aestronglyMeasurable_fun_sum _ fun k _ =>
      ((hDm k).mul (hGm k)).add ((hχm k).mul (hHm k))
  -- pointwise identity for interior ages
  have hpt : ∀ r ∈ Ioo t₀ t₁, cylTdInner tr ω (φs n) r =
      ∑ k, (deriv (χ k) r * (∫ x in B0579.cell c, ω r x * ψ k x) +
        χ k r * ∫ x in B0579.cell c, cylFreeIntegrand tr (ω r) r (ψ k) x) := by
    intro r hr
    have hdiff : ∀ k, DifferentiableAt ℝ (χ k) r := fun k =>
      ((hχ k).differentiableOn (by norm_num)).differentiableAt (Icc_mem_nhds hr.1 hr.2)
    have hlap : ∀ x, lapP (φs n r) x = ∑ k, χ k r * lapP (ψ k) x := fun x => by
      have hfun : φs n r = fun y => ∑ k, χ k r * ψ k y := funext fun y => hsum r y
      rw [hfun]
      exact cylMeas_lapP_sum (fun k => χ k r) ψ hψ x
    have hpd : ∀ j x, B0579.pd j (φs n r) x = ∑ k, χ k r * B0579.pd j (ψ k) x := fun j x => by
      have hfun : φs n r = fun y => ∑ k, χ k r * ψ k y := funext fun y => hsum r y
      rw [hfun, cylMeas_pd_sum (fun k => χ k r) ψ (fun k => (hψ k).differentiable) j]
    have hint : ∀ x, ω r x * (deriv (fun r' => φs n r' x) r + ν * lapP (φs n r) x +
        (tr.v r x 0 * B0579.pd 0 (φs n r) x + tr.v r x 1 * B0579.pd 1 (φs n r) x))
        = ∑ k, (deriv (χ k) r * (ω r x * ψ k x) + χ k r * (ω r x *
            (ν * lapP (ψ k) x + (tr.v r x 0 * B0579.pd 0 (ψ k) x +
              tr.v r x 1 * B0579.pd 1 (ψ k) x)))) := by
      intro x
      rw [cylMeas_deriv_sum χ ψ r x hdiff (φs n) hsum, hlap x, hpd 0 x, hpd 1 x]
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    have hwψ : ∀ k, IntegrableOn (fun x => ω r x * ψ k x) (B0579.cell c) := fun k =>
      cylMeas_integrableOn_test (hfl.memX r hr.1.le) (hψ k)
    have hIA : ∀ k, Integrable (fun x => deriv (χ k) r * (ω r x * ψ k x))
        (volume.restrict (B0579.cell c)) := fun k => (hwψ k).const_mul _
    have hIB : ∀ k, Integrable (fun x => χ k r * (ω r x *
        (ν * lapP (ψ k) x + (tr.v r x 0 * B0579.pd 0 (ψ k) x +
          tr.v r x 1 * B0579.pd 1 (ψ k) x))))
        (volume.restrict (B0579.cell c)) := fun k =>
      (hfl.integrable (ψ k) (hψ k) r hr.1.le).const_mul _
    unfold cylTdInner
    rw [integral_congr_ae (Eventually.of_forall hint)]
    rw [integral_finsetSum Finset.univ (f := fun k x => deriv (χ k) r * (ω r x * ψ k x) +
      χ k r * (ω r x * (ν * lapP (ψ k) x + (tr.v r x 0 * B0579.pd 0 (ψ k) x +
        tr.v r x 1 * B0579.pd 1 (ψ k) x)))) (fun k _ => (hIA k).add (hIB k))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_add (hIA k) (hIB k), integral_const_mul, integral_const_mul]
    rfl
  -- almost everywhere on `(t₀, t₁]` the inner integral is the finite sum
  have hae : cylTdInner tr ω (φs n) =ᵐ[volume.restrict (Ioc t₀ t₁)] fun r =>
      ∑ k, (deriv (χ k) r * (∫ x in B0579.cell c, ω r x * ψ k x) +
        χ k r * ∫ x in B0579.cell c, cylFreeIntegrand tr (ω r) r (ψ k) x) := by
    rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
    have hne : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ t₁ := by
      have : (volume : Measure ℝ) {t₁} = 0 := Real.volume_singleton
      simpa [ae_iff] using this
    filter_upwards [hne] with r hr hrI
    exact hpt r ⟨hrI.1, lt_of_le_of_ne hrI.2 hr⟩
  exact hFm.congr hae.symm
