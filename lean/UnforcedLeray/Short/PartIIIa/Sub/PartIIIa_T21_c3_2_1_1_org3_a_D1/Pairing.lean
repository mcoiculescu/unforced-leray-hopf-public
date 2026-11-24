import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_a_D1.Support
import UnforcedLeray.Short.PartIIIa.Clock.FreeMoving.Rate.FmrDeriv.Generic
import UnforcedLeray.Short.PartIIb.Sub.T22

/-!
# Helper for `PartIII-a:T21/c3/2/1/1/org/3/a/1/1`: the age derivative of the pairing

Source: SP 2962-2964 ("compact smooth tests and Duhamel"), SP 2861-2863.

For a regular free cylinder flow `ω` (`IIb.IsRegularCylFlow`) and the comparison function
`cmp Φ ν s σ` of a compactly supported profile, the pairing `I(σ) = ∫ ω(σ) cmp(σ)` is continuous
and has right derivative `∫ ω(σ) cmpRes(σ)` (`pairing_hasDeriv`): differentiation under the
integral sign (`fd_generic`) and the integrations by parts of `pairing_identity`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa.RelFreeTestSub.D1Aux

theorem pairing_hasDeriv {Φ : ℝ × (ℝ × ℝ) → ℝ} (hΦ : ContDiff ℝ 2 Φ) {R : ℝ} (hR : 0 ≤ R)
    (hsupp : SuppIn R Φ) {c ν s t T : ℝ} (hν : 0 < ν) (hs : 0 ≤ s) (hst : s ≤ t)
    (htT : t ≤ T) {v : ℝ → ℝ × ℝ → UnforcedLeray.Train.Vec}
    (hv : ∀ σ ∈ Icc s t, ∀ j : Fin 2, ContDiff ℝ 1 (fun x => v σ x j))
    (hdiv : ∀ σ ∈ Icc s t, ∀ x,
      B0579.pd 0 (fun x => v σ x 0) x + B0579.pd 1 (fun x => v σ x 1) x = 0)
    {M : ℝ} (hM : ∀ σ ∈ Icc s t, ∀ x, |v σ x 0| + |v σ x 1| ≤ M)
    {om : ℝ → ℝ × ℝ → ℝ} (hom : UnforcedLeray.Short.IIb.IsRegularCylFlow c ν v s T om) :
    ContinuousOn (fun σ => ∫ x, om σ x * cmp Φ ν s σ x) (Icc s t) ∧
      ∀ τ ∈ Ico s t, HasDerivWithinAt (fun σ => ∫ x, om σ x * cmp Φ ν s σ x)
        (∫ x, om τ x * cmpRes Φ v ν s τ x) (Ici τ) τ := by
  have hν0 : 0 ≤ ν := hν.le
  have hΦ1 : ContDiff ℝ 1 Φ := hΦ.of_le (by norm_num)
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by norm_num)
  set Z := movingZ ν t - movingZ ν s with hZ
  have hDc : Continuous (fun p => fderiv ℝ Φ p) := hΦ.continuous_fderiv (by norm_num)
  obtain ⟨CΦ, hCΦ0, hCΦ⟩ := exists_bound_slab hΦ.continuous hR hsupp Z
  obtain ⟨CZ, hCZ0, hCZ⟩ := exists_bound_slab (f := dZ Φ)
    (by unfold dZ; exact hDc.clm_apply continuous_const) hR (suppIn_dZ hsupp) Z
  obtain ⟨C3, hC30, hC3⟩ := exists_bound_slab (f := fun p => fderiv ℝ Φ p (0, p.2))
    (hDc.clm_apply (continuous_const.prodMk continuous_snd)) hR
    (suppIn_fderiv_apply hsupp (fun p => (0, p.2))) Z
  obtain ⟨Com, hCom⟩ := hom.decay 0
  have hCom' : ∀ σ ∈ Icc s T, ∀ x, |om σ x| + |B0579.pd 0 (om σ) x| + |B0579.pd 1 (om σ) x| +
      |UnforcedLeray.Short.IIb.lapP (om σ) x| ≤ Com := by
    intro σ hσ x
    have := hCom σ hσ x
    rwa [Real.rpow_zero, mul_one] at this
  have hCom0 : 0 ≤ Com := by
    have := hCom' s ⟨le_rfl, hst.trans htT⟩ 0
    linarith [abs_nonneg (om s 0), abs_nonneg (B0579.pd 0 (om s) 0),
      abs_nonneg (B0579.pd 1 (om s) 0), abs_nonneg (UnforcedLeray.Short.IIb.lapP (om s) 0)]
  have hM0 : 0 ≤ M := by
    have := hM s ⟨le_rfl, hst⟩ 0
    linarith [abs_nonneg (v s 0 0), abs_nonneg (v s 0 1)]
  set At := clockA ν t with hAt
  have hAt1 : 1 ≤ At := one_le_clockA' hν0 (hs.trans hst)
  set K := Metric.closedBall (0 : ℝ × ℝ) (R * Real.sqrt At) with hK
  set Gc := Com * At * CΦ + (ν * Com + M * Com) * At * CΦ + Com * (ν * CΦ + CZ + ν * C3) with hGc
  have hGc0 : 0 ≤ Gc := by positivity
  set G : ℝ × ℝ → ℝ := K.indicator (fun _ => Gc) with hG
  have hGi : IntegrableOn G univ volume := by
    rw [integrableOn_univ]
    exact (integrableOn_const (isCompact_closedBall _ _).measure_lt_top.ne).integrable_indicator
      measurableSet_closedBall
  -- pointwise facts on `[s, t]`
  have hslab : ∀ σ ∈ Icc s t, ∀ x, 0 ≤ (cpt ν s σ x).1 ∧ (cpt ν s σ x).1 ≤ Z := by
    intro σ hσ x
    simp only [cpt, hZ]
    constructor
    · linarith [movingZ_mono hν0 hs hσ.1]
    · linarith [movingZ_mono hν0 (hs.trans hσ.1) hσ.2]
  have hcmp_b : ∀ σ ∈ Icc s t, ∀ x, |cmp Φ ν s σ x| ≤ At * CΦ := by
    intro σ hσ x
    have h1 := hCΦ _ (hslab σ hσ x).1 (hslab σ hσ x).2
    have ha := clockA_pos hν0 (hs.trans hσ.1)
    unfold cmp
    rw [abs_mul, abs_of_pos ha]
    exact mul_le_mul (clockA_mono hν0 hσ.2) h1 (abs_nonneg _) (by linarith)
  have hcmpDt_b : ∀ σ ∈ Icc s t, ∀ x, |cmpDt Φ ν s σ x| ≤ ν * CΦ + CZ + ν * C3 := by
    intro σ hσ x
    have h1 := hCΦ _ (hslab σ hσ x).1 (hslab σ hσ x).2
    have h2 := hCZ _ (hslab σ hσ x).1 (hslab σ hσ x).2
    have h3 := hC3 _ (hslab σ hσ x).1 (hslab σ hσ x).2
    have ha1 := one_le_clockA' hν0 (hs.trans hσ.1)
    have hinv : (clockA ν σ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ha1
    have hinv0 : 0 ≤ (clockA ν σ)⁻¹ := by positivity
    unfold cmpDt
    calc |ν * Φ (cpt ν s σ x) + (clockA ν σ)⁻¹ * dZ Φ (cpt ν s σ x) -
          ν / 2 * fderiv ℝ Φ (cpt ν s σ x) (0, (cpt ν s σ x).2)|
        ≤ |ν * Φ (cpt ν s σ x)| + |(clockA ν σ)⁻¹ * dZ Φ (cpt ν s σ x)| +
          |ν / 2 * fderiv ℝ Φ (cpt ν s σ x) (0, (cpt ν s σ x).2)| := by
          refine (abs_sub _ _).trans ?_
          exact add_le_add (abs_add_le _ _) le_rfl
      _ ≤ ν * CΦ + 1 * CZ + ν * C3 := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hν0, abs_of_nonneg hinv0,
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ ν / 2)]
          refine add_le_add (add_le_add (mul_le_mul_of_nonneg_left h1 hν0)
            (mul_le_mul hinv h2 (abs_nonneg _) zero_le_one)) ?_
          have : ν / 2 ≤ ν := by linarith
          exact mul_le_mul this h3 (abs_nonneg _) hν0
      _ = ν * CΦ + CZ + ν * C3 := by ring
  set F : ℝ → ℝ × ℝ → ℝ := fun σ x => om σ x * cmp Φ ν s σ x with hF
  set F' : ℝ → ℝ × ℝ → ℝ := fun σ x =>
    (ν * UnforcedLeray.Short.IIb.lapP (om σ) x -
      (v σ x 0 * B0579.pd 0 (om σ) x + v σ x 1 * B0579.pd 1 (om σ) x)) * cmp Φ ν s σ x +
      om σ x * cmpDt Φ ν s σ x with hF'
  have hσT : ∀ σ ∈ Icc s t, σ ∈ Icc s T := fun σ hσ => ⟨hσ.1, hσ.2.trans htT⟩
  have hFm : ∀ σ ∈ Icc s t, AEStronglyMeasurable (F σ) (volume.restrict univ) := by
    intro σ hσ
    have h1 : Continuous (om σ) := ((hom.slice σ (hσT σ hσ)).smooth).continuous
    have h2 : Continuous (cmp Φ ν s σ) := (contDiff_cmp hΦ ν s σ).continuous
    exact (h1.mul h2).aestronglyMeasurable
  have hFb : ∀ σ ∈ Icc s t, ∀ x ∈ (univ : Set (ℝ × ℝ)), |F σ x| ≤ G x := by
    intro σ hσ x _
    by_cases hx : x ∈ K
    · rw [hG, indicator_of_mem hx]
      have hw := hCom' σ (hσT σ hσ) x
      have hom1 : |om σ x| ≤ Com := by
        linarith [abs_nonneg (B0579.pd 0 (om σ) x), abs_nonneg (B0579.pd 1 (om σ) x),
          abs_nonneg (UnforcedLeray.Short.IIb.lapP (om σ) x)]
      simp only [hF, abs_mul]
      have : |om σ x| * |cmp Φ ν s σ x| ≤ Com * (At * CΦ) :=
        mul_le_mul hom1 (hcmp_b σ hσ x) (abs_nonneg _) hCom0
      have h3 : 0 ≤ (ν * Com + M * Com) * At * CΦ + Com * (ν * CΦ + CZ + ν * C3) := by positivity
      rw [hGc]
      nlinarith
    · rw [hG, indicator_of_notMem hx]
      simp only [hF, cmp_outside hsupp hν0 (hs.trans hσ.1) hσ.2 hR hx, mul_zero, abs_zero,
        le_refl]
  have hF'b : ∀ σ ∈ Icc s t, ∀ x ∈ (univ : Set (ℝ × ℝ)), |F' σ x| ≤ G x := by
    intro σ hσ x _
    by_cases hx : x ∈ K
    · rw [hG, indicator_of_mem hx]
      have hw := hCom' σ (hσT σ hσ) x
      have hom1 : |om σ x| ≤ Com := by
        linarith [abs_nonneg (B0579.pd 0 (om σ) x), abs_nonneg (B0579.pd 1 (om σ) x),
          abs_nonneg (UnforcedLeray.Short.IIb.lapP (om σ) x)]
      have hvM := hM σ hσ x
      have hA : |ν * UnforcedLeray.Short.IIb.lapP (om σ) x -
          (v σ x 0 * B0579.pd 0 (om σ) x + v σ x 1 * B0579.pd 1 (om σ) x)| ≤ ν * Com + M * Com := by
        have e1 : |B0579.pd 0 (om σ) x| ≤ Com := by
          linarith [abs_nonneg (om σ x), abs_nonneg (B0579.pd 1 (om σ) x),
            abs_nonneg (UnforcedLeray.Short.IIb.lapP (om σ) x)]
        have e2 : |B0579.pd 1 (om σ) x| ≤ Com := by
          linarith [abs_nonneg (om σ x), abs_nonneg (B0579.pd 0 (om σ) x),
            abs_nonneg (UnforcedLeray.Short.IIb.lapP (om σ) x)]
        have e3 : |UnforcedLeray.Short.IIb.lapP (om σ) x| ≤ Com := by
          linarith [abs_nonneg (om σ x), abs_nonneg (B0579.pd 0 (om σ) x),
            abs_nonneg (B0579.pd 1 (om σ) x)]
        calc _ ≤ |ν * UnforcedLeray.Short.IIb.lapP (om σ) x| +
              (|v σ x 0 * B0579.pd 0 (om σ) x| + |v σ x 1 * B0579.pd 1 (om σ) x|) :=
              (abs_sub _ _).trans (add_le_add le_rfl (abs_add_le _ _))
          _ ≤ ν * Com + (|v σ x 0| * Com + |v σ x 1| * Com) := by
              rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hν0]
              exact add_le_add (mul_le_mul_of_nonneg_left e3 hν0)
                (add_le_add (mul_le_mul_of_nonneg_left e1 (abs_nonneg _))
                  (mul_le_mul_of_nonneg_left e2 (abs_nonneg _)))
          _ ≤ ν * Com + M * Com := by nlinarith
      have hB := hcmp_b σ hσ x
      have hD := hcmpDt_b σ hσ x
      simp only [hF']
      calc _ ≤ |(ν * UnforcedLeray.Short.IIb.lapP (om σ) x -
              (v σ x 0 * B0579.pd 0 (om σ) x + v σ x 1 * B0579.pd 1 (om σ) x)) *
              cmp Φ ν s σ x| + |om σ x * cmpDt Φ ν s σ x| := abs_add_le _ _
        _ ≤ (ν * Com + M * Com) * (At * CΦ) + Com * (ν * CΦ + CZ + ν * C3) := by
            rw [abs_mul, abs_mul]
            exact add_le_add (mul_le_mul hA hB (abs_nonneg _) (by positivity))
              (mul_le_mul hom1 hD (abs_nonneg _) hCom0)
        _ ≤ Gc := by
            rw [hGc]
            have : 0 ≤ Com * At * CΦ := by positivity
            nlinarith
    · rw [hG, indicator_of_notMem hx]
      simp only [hF', cmp_outside hsupp hν0 (hs.trans hσ.1) hσ.2 hR hx,
        cmpDt_outside hsupp hν0 (hs.trans hσ.1) hσ.2 hR hx, mul_zero, add_zero, abs_zero,
        le_refl]
  have hder : ∀ x ∈ (univ : Set (ℝ × ℝ)), ∀ σ ∈ Icc s t,
      HasDerivWithinAt (fun r => F r x) (F' σ x) (Icc s t) σ := by
    intro x _ σ hσ
    have h1 := (hom.pde σ (hσT σ hσ) x).mono (Icc_subset_Icc le_rfl htT)
    have h2 := (hasDerivAt_cmp (s := s) hΦd hν0 (hs.trans hσ.1) x).hasDerivWithinAt
      (s := Icc s t)
    exact h1.mul h2
  obtain ⟨-, hcont, hd⟩ := fd_generic (μ := volume) s t univ MeasurableSet.univ F F' G hGi
    hFm hFb hF'b hder
  simp only [Measure.restrict_univ] at hcont hd
  refine ⟨hcont, fun τ hτ => ?_⟩
  obtain ⟨-, hτd⟩ := hd τ hτ
  have hτI : τ ∈ Icc s t := Ico_subset_Icc_self hτ
  have hτ0 : 0 ≤ τ := hs.trans hτ.1
  have hid : ∫ x, F' τ x = ∫ x, om τ x * cmpRes Φ v ν s τ x := by
    have hcs : HasCompactSupport (cmp Φ ν s τ) :=
      HasCompactSupport.intro (isCompact_closedBall _ _)
        (fun x hx => cmp_outside hsupp hν0 hτ0 hτI.2 hR hx)
    have hdcs : HasCompactSupport (cmpDt Φ ν s τ) :=
      HasCompactSupport.intro (isCompact_closedBall _ _)
        (fun x hx => cmpDt_outside hsupp hν0 hτ0 hτI.2 hR hx)
    exact pairing_identity ν ((hom.slice τ (hσT τ hτI)).smooth) (contDiff_cmp hΦ ν s τ) hcs
      (hv τ hτI 0) (hv τ hτI 1) (hdiv τ hτI) (continuous_cmpDt hΦ1 ν s τ) hdcs
  rw [← hid]
  exact hτd

end UnforcedLeray.Short.IIIa.RelFreeTestSub.D1Aux
