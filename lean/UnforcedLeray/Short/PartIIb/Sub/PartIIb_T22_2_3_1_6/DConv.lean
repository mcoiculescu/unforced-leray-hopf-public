import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_1_6
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.CRCont

/-!


Source: `the November 2 reference manuscript`, lines 2100-2105.  Abstract calculus of
`dConv ν A σ x = ∫₀^σ A(ν(σ - r), r, x) dr` for an integrand `A(a, r, x)` which is jointly continuous
for `a > 0` and of size `C (1 + a^{-1/2}) b(r)` (`DAdm`): integrability and the Volterra bound
(`dConv_int`, `dConv_le`), joint continuity (`dConv_cont`, substitution `r = σ - t` and dominated
convergence as in `CC.gen_cont`), differentiation in `x` under the integral (`dConv_deriv`).  The
leaves `GainZero` and `CommGain` are applications.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb.BwdRoute

namespace LS

open CylPDE

variable {T : ℝ}

/-- The Duhamel integral of a parametrized operator. -/
def dConv (ν : ℝ) (A : ℝ → ℝ → Pl → ℝ) (σ : ℝ) (x : Pl) : ℝ :=
  ∫ r in (0 : ℝ)..σ, A (ν * (σ - r)) r x

/-- An admissible integrand: jointly continuous for `a > 0`, of size `C (1 + a^{-1/2}) b(r)`. -/
structure DAdm (T C : ℝ) (b : ℝ → ℝ) (A : ℝ → ℝ → Pl → ℝ) : Prop where
  cont : ContinuousOn (fun p : ℝ × ℝ × Pl => A p.1 p.2.1 p.2.2) (Ioi 0 ×ˢ (Icc 0 T ×ˢ univ))
  bound : ∀ a : ℝ, 0 < a → ∀ r ∈ Icc 0 T, ∀ x : Pl, |A a r x| ≤ C * (1 + a ^ (-(1 / 2 : ℝ))) * b r

/-- The kernel bound `1 + (ν t)^{-1/2} ≤ (1 + ν^{-1/2}) (1 + t^{-1/2})`. -/
theorem kernel_le {ν t : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) :
    1 + (ν * t) ^ (-(1 / 2 : ℝ)) ≤ (1 + ν ^ (-(1 / 2 : ℝ))) * (1 + t ^ (-(1 / 2 : ℝ))) := by
  rw [Real.mul_rpow hν.le ht]
  have h1 : 0 ≤ ν ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hν.le _
  have h2 : 0 ≤ t ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg ht _
  nlinarith

theorem kInt_mul {b : ℝ → ℝ} (hb : ContinuousOn b (Icc 0 T)) {σ : ℝ} (hσ : σ ∈ Icc 0 T) :
    IntervalIntegrable (fun r : ℝ => (1 + (σ - r) ^ (-(1 / 2 : ℝ))) * b r) volume 0 σ := by
  have hbc : ContinuousOn b (uIcc 0 σ) := by
    rw [uIcc_of_le hσ.1]
    exact hb.mono (Icc_subset_Icc le_rfl hσ.2)
  have h1 := hbc.intervalIntegrable (μ := volume)
  have h2 := UnforcedLeray.Gronwall.intervalIntegrable_kernel_mul hbc σ
  refine (h1.add h2).congr fun r _ => ?_
  ring

/-- The pointwise majorant of the integrand. -/
theorem dAdm_pt {ν C : ℝ} {b : ℝ → ℝ} {A : ℝ → ℝ → Pl → ℝ} (hν : 0 < ν) (hC : 0 ≤ C)
    (hb0 : ∀ r ∈ Icc 0 T, 0 ≤ b r) (hA : DAdm T C b A) {σ r : ℝ} (hσ : σ ∈ Icc 0 T)
    (hr : r ∈ Ico 0 σ) (x : Pl) :
    |A (ν * (σ - r)) r x| ≤
      C * (1 + ν ^ (-(1 / 2 : ℝ))) * ((1 + (σ - r) ^ (-(1 / 2 : ℝ))) * b r) := by
  have hrI : r ∈ Icc 0 T := ⟨hr.1, hr.2.le.trans hσ.2⟩
  have ht : 0 < σ - r := by linarith [hr.2]
  refine (hA.bound _ (mul_pos hν ht) r hrI x).trans ?_
  have hk := kernel_le hν ht.le
  have hb := hb0 r hrI
  calc C * (1 + (ν * (σ - r)) ^ (-(1 / 2 : ℝ))) * b r
      ≤ C * ((1 + ν ^ (-(1 / 2 : ℝ))) * (1 + (σ - r) ^ (-(1 / 2 : ℝ)))) * b r := by gcongr
    _ = _ := by ring

theorem ae_ne_pt (σ : ℝ) : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ σ := by simp [ae_iff]

/-- Slices of the integrand are continuous on `[0, σ)`. -/
theorem dAdm_slice {ν C : ℝ} {b : ℝ → ℝ} {A : ℝ → ℝ → Pl → ℝ} (hν : 0 < ν) (hA : DAdm T C b A)
    {σ : ℝ} (hσ : σ ∈ Icc 0 T) (x : Pl) :
    ContinuousOn (fun r => A (ν * (σ - r)) r x) (Ico 0 σ) := by
  have hmap : ContinuousOn (fun r : ℝ => ((ν * (σ - r), r, x) : ℝ × ℝ × Pl)) (Ico 0 σ) := by
    apply Continuous.continuousOn
    fun_prop
  exact hA.cont.comp hmap fun r hr =>
    ⟨mul_pos hν (by linarith [hr.2]), ⟨hr.1, hr.2.le.trans hσ.2⟩, mem_univ _⟩

theorem dAdm_meas {ν C : ℝ} {b : ℝ → ℝ} {A : ℝ → ℝ → Pl → ℝ} (hν : 0 < ν) (hA : DAdm T C b A)
    {σ : ℝ} (hσ : σ ∈ Icc 0 T) (x : Pl) :
    AEStronglyMeasurable (fun r => A (ν * (σ - r)) r x) (volume.restrict (Ioc 0 σ)) :=
  DiffC.aesm_Ioc_of_contOn (dAdm_slice hν hA hσ x)

/-- Integrability of the integrand. -/
theorem dConv_int {ν C : ℝ} {b : ℝ → ℝ} {A : ℝ → ℝ → Pl → ℝ} (hν : 0 < ν) (hC : 0 ≤ C)
    (hb : ContinuousOn b (Icc 0 T)) (hb0 : ∀ r ∈ Icc 0 T, 0 ≤ b r) (hA : DAdm T C b A) {σ : ℝ}
    (hσ : σ ∈ Icc 0 T) (x : Pl) :
    IntervalIntegrable (fun r => A (ν * (σ - r)) r x) volume 0 σ := by
  refine IntervalIntegrable.mono_fun' ((kInt_mul hb hσ).const_mul
    (C * (1 + ν ^ (-(1 / 2 : ℝ))))) ?_ ?_
  · rw [uIoc_of_le hσ.1]
    exact dAdm_meas hν hA hσ x
  · rw [uIoc_of_le hσ.1]
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    filter_upwards [ae_ne_pt σ] with r hne hr
    rw [Real.norm_eq_abs]
    exact dAdm_pt hν hC hb0 hA hσ ⟨hr.1.le, lt_of_le_of_ne hr.2 hne⟩ x

/-- The Volterra bound. -/
theorem dConv_le {ν C : ℝ} {b : ℝ → ℝ} {A : ℝ → ℝ → Pl → ℝ} (hν : 0 < ν) (hC : 0 ≤ C)
    (hb : ContinuousOn b (Icc 0 T)) (hb0 : ∀ r ∈ Icc 0 T, 0 ≤ b r) (hA : DAdm T C b A) {σ : ℝ}
    (hσ : σ ∈ Icc 0 T) (x : Pl) :
    |dConv ν A σ x| ≤ Kconv (C * (1 + ν ^ (-(1 / 2 : ℝ)))) b σ := by
  have h := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hσ.1
    (f := fun r => A (ν * (σ - r)) r x)
    (g := fun r => C * (1 + ν ^ (-(1 / 2 : ℝ))) * ((1 + (σ - r) ^ (-(1 / 2 : ℝ))) * b r)) ?_
    ((kInt_mul hb hσ).const_mul _)
  · rw [intervalIntegral.integral_const_mul, Real.norm_eq_abs] at h
    exact h
  · filter_upwards [ae_ne_pt σ] with r hne hr
    rw [Real.norm_eq_abs]
    exact dAdm_pt hν hC hb0 hA hσ ⟨hr.1.le, lt_of_le_of_ne hr.2 hne⟩ x

/-- **Joint continuity** of the Duhamel integral. -/
theorem dConv_cont {ν C : ℝ} {b : ℝ → ℝ} {A : ℝ → ℝ → Pl → ℝ} (hν : 0 < ν) (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hb : ContinuousOn b (Icc 0 T)) (hb0 : ∀ r ∈ Icc 0 T, 0 ≤ b r) (hA : DAdm T C b A) :
    ContinuousOn (fun z : ℝ × Pl => dConv ν A z.1 z.2) (Icc 0 T ×ˢ univ) := by
  obtain ⟨M0, hM0⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn hb
  have hbM : ∀ r ∈ Icc 0 T, b r ≤ M0 := fun r hr =>
    (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hM0 r hr)
  have hM00 : 0 ≤ M0 := (hb0 0 ⟨le_rfl, hT⟩).trans (hbM 0 ⟨le_rfl, hT⟩)
  -- the integrand in the variable `t = σ - r`
  let Ψ : ℝ × Pl → ℝ → ℝ := fun z t => A (ν * t) (CC.clampT 0 T (z.1 - t)) z.2
  let φ : (ℝ × Pl) × ℝ → ℝ × ℝ × Pl :=
    fun p => (ν * p.2, CC.clampT 0 T (p.1.1 - p.2), p.1.2)
  have hcl : Continuous (fun σ : ℝ => CC.clampT 0 T σ) := by
    unfold CC.clampT
    exact continuous_const.min (continuous_const.max continuous_id)
  have hφ : Continuous φ :=
    (continuous_const.mul continuous_snd).prodMk
      ((hcl.comp ((continuous_fst.comp continuous_fst).sub continuous_snd)).prodMk
        (continuous_snd.comp continuous_fst))
  have hΨat : ∀ (z0 : ℝ × Pl) (t0 : ℝ), 0 < t0 →
      ContinuousAt (fun p : (ℝ × Pl) × ℝ => Ψ p.1 p.2) (z0, t0) := by
    intro z0 t0 ht0
    have hmem : φ (z0, t0) ∈ (Ioi 0 ×ˢ (Icc 0 T ×ˢ univ) : Set (ℝ × ℝ × Pl)) :=
      ⟨mul_pos hν ht0, CC.clampT_mem hT _, mem_univ _⟩
    have htend : Tendsto φ (𝓝 (z0, t0)) (𝓝[Ioi 0 ×ˢ (Icc 0 T ×ˢ univ)] φ (z0, t0)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨hφ.tendsto _, ?_⟩
      have hopen : IsOpen {p : (ℝ × Pl) × ℝ | 0 < p.2} := isOpen_lt continuous_const continuous_snd
      filter_upwards [hopen.mem_nhds ht0] with p hp
      exact ⟨mul_pos hν hp, CC.clampT_mem hT _, mem_univ _⟩
    exact (hA.cont _ hmem).tendsto.comp htend
  have hΨT : ∀ t0 : ℝ, 0 < t0 → ∀ z0 : ℝ × Pl, ContinuousAt (fun z => Ψ z t0) z0 := by
    intro t0 ht0 z0
    exact ContinuousAt.comp (f := fun z : ℝ × Pl => (z, t0)) (hΨat z0 t0 ht0)
      (Continuous.continuousAt (f := fun z : ℝ × Pl => (z, t0))
        (continuous_id.prodMk continuous_const))
  have hΨZ : ∀ z : ℝ × Pl, ContinuousOn (fun t => Ψ z t) (Ioi 0) := by
    intro z t0 ht0
    exact (ContinuousAt.comp (f := fun t : ℝ => (z, t)) (hΨat z t0 ht0)
      (Continuous.continuousAt (f := fun t : ℝ => (z, t))
        (continuous_const.prodMk continuous_id))).continuousWithinAt
  let indF : ℝ × Pl → ℝ → ℝ := fun z t => Set.indicator (Iic z.1) (fun t' => Ψ z t') t
  have hΨeq : ∀ z ∈ Icc 0 T ×ˢ (univ : Set Pl), ∀ t : ℝ, 0 < t → t ≤ z.1 →
      Ψ z t = A (ν * t) (z.1 - t) z.2 := by
    intro z hz t ht htz
    simp only [Ψ]
    rw [CC.clampT_of_mem ⟨by linarith, by linarith [hz.1.2]⟩]
  have hIdent : ∀ z ∈ Icc 0 T ×ˢ (univ : Set Pl),
      dConv ν A z.1 z.2 = ∫ t in (0 : ℝ)..T, indF z t := by
    rintro ⟨τ, x⟩ hz
    have hτ : τ ∈ Icc 0 T := hz.1
    have hsub : dConv ν A τ x = ∫ t in (0 : ℝ)..τ, A (ν * t) (τ - t) x := by
      have := intervalIntegral.integral_comp_sub_left
        (f := fun t => A (ν * t) (τ - t) x) (a := 0) (b := τ) (d := τ)
      unfold dConv
      simpa only [sub_sub_cancel, sub_self, sub_zero] using this
    simp only
    rw [hsub, intervalIntegral.integral_of_le hτ.1, intervalIntegral.integral_of_le hT]
    have hEq : ∫ t in Ioc (0 : ℝ) τ, A (ν * t) (τ - t) x = ∫ t in Ioc (0 : ℝ) τ, Ψ (τ, x) t := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      exact (hΨeq (τ, x) hz t ht.1 ht.2).symm
    have hRHS : ∫ t in Ioc (0 : ℝ) T, indF (τ, x) t = ∫ t in Ioc (0 : ℝ) τ, Ψ (τ, x) t := by
      simp only [indF]
      rw [setIntegral_indicator measurableSet_Iic, Ioc_inter_Iic, min_eq_right hτ.2]
    rw [hEq, hRHS]
  -- the majorant
  let B : ℝ → ℝ := fun t => C * M0 * (1 + ν ^ (-(1 / 2 : ℝ)) * t ^ (-(1 / 2 : ℝ)))
  have hB0 : ∀ t : ℝ, 0 < t → 0 ≤ B t := fun t ht => by
    have h1 := Real.rpow_nonneg hν.le (-(1 / 2 : ℝ))
    have h2 := Real.rpow_nonneg ht.le (-(1 / 2 : ℝ))
    simp only [B]
    positivity
  have hBint : IntervalIntegrable B volume 0 T :=
    (intervalIntegrable_const.add ((intervalIntegral.intervalIntegrable_rpow'
      (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ))).const_mul _)).const_mul _
  have hdom : ∀ z ∈ Icc 0 T ×ˢ (univ : Set Pl), ∀ t : ℝ, 0 < t → t ≤ z.1 →
      |A (ν * t) (z.1 - t) z.2| ≤ B t := by
    intro z hz t ht htz
    have hmem : z.1 - t ∈ Icc 0 T := ⟨by linarith, by linarith [hz.1.2]⟩
    refine (hA.bound _ (mul_pos hν ht) _ hmem _).trans ?_
    rw [Real.mul_rpow hν.le ht.le]
    have h1 := Real.rpow_nonneg hν.le (-(1 / 2 : ℝ))
    have h2 := Real.rpow_nonneg ht.le (-(1 / 2 : ℝ))
    have h3 : 0 ≤ 1 + ν ^ (-(1 / 2 : ℝ)) * t ^ (-(1 / 2 : ℝ)) := by positivity
    calc C * (1 + ν ^ (-(1 / 2 : ℝ)) * t ^ (-(1 / 2 : ℝ))) * b (z.1 - t)
        ≤ C * (1 + ν ^ (-(1 / 2 : ℝ)) * t ^ (-(1 / 2 : ℝ))) * M0 :=
          mul_le_mul_of_nonneg_left (hbM _ hmem) (mul_nonneg hC h3)
      _ = B t := by simp only [B]; ring
  have hCont : ∀ z0 ∈ Icc 0 T ×ˢ (univ : Set Pl),
      ContinuousWithinAt (fun z => ∫ t in (0 : ℝ)..T, indF z t) (Icc 0 T ×ˢ univ) z0 := by
    intro z0 hz0
    refine intervalIntegral.continuousWithinAt_of_dominated_interval (bound := B) ?_ ?_ hBint ?_
    · refine Filter.Eventually.of_forall (fun z => ?_)
      rw [uIoc_of_le hT]
      exact (((hΨZ z).mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc).indicator
        measurableSet_Iic
    · refine eventually_nhdsWithin_of_forall (fun z hz => ?_)
      refine ae_of_all _ (fun t ht => ?_)
      rw [uIoc_of_le hT] at ht
      by_cases h : t ≤ z.1
      · simp only [indF]
        rw [Set.indicator_of_mem (show t ∈ Iic z.1 from h), hΨeq z hz t ht.1 h, Real.norm_eq_abs]
        exact hdom z hz t ht.1 h
      · simp only [indF]
        rw [Set.indicator_of_notMem (show t ∉ Iic z.1 from h), norm_zero]
        exact hB0 t ht.1
    · filter_upwards [ae_ne_pt z0.1] with t hne ht
      rw [uIoc_of_le hT] at ht
      have ht0 : 0 < t := ht.1
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hev : ∀ᶠ z in 𝓝 z0, t < z.1 :=
          Filter.Tendsto.eventually continuous_fst.continuousAt (lt_mem_nhds hlt)
        have h1 : ∀ᶠ z in 𝓝[Icc 0 T ×ˢ univ] z0, indF z t = Ψ z t :=
          eventually_nhdsWithin_of_eventually_nhds (hev.mono fun z hz =>
            Set.indicator_of_mem (show t ∈ Iic z.1 from le_of_lt hz) _)
        have hx : indF z0 t = Ψ z0 t :=
          Set.indicator_of_mem (show t ∈ Iic z0.1 from le_of_lt hlt) _
        exact ((hΨT t ht0 z0).continuousWithinAt).congr_of_eventuallyEq h1 hx
      · have hev : ∀ᶠ z in 𝓝 z0, z.1 < t :=
          Filter.Tendsto.eventually continuous_fst.continuousAt (Iio_mem_nhds hgt)
        have h1 : ∀ᶠ z in 𝓝[Icc 0 T ×ˢ univ] z0, indF z t = 0 :=
          eventually_nhdsWithin_of_eventually_nhds (hev.mono fun z hz =>
            Set.indicator_of_notMem (show t ∉ Iic z.1 from not_le.2 hz) _)
        have hx : indF z0 t = 0 :=
          Set.indicator_of_notMem (show t ∉ Iic z0.1 from not_le.2 hgt) _
        exact (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq h1 hx
  have hQ : ContinuousOn (fun z : ℝ × Pl => ∫ t in (0 : ℝ)..T, indF z t) (Icc 0 T ×ˢ univ) :=
    fun z hz => hCont z hz
  exact hQ.congr fun z hz => hIdent z hz

/-- **Differentiation in `x`** under the Duhamel integral. -/
theorem dConv_deriv {ν C : ℝ} {b : ℝ → ℝ} {A A0 A1 : ℝ → ℝ → Pl → ℝ} (hν : 0 < ν) (hC : 0 ≤ C)
    (hb : ContinuousOn b (Icc 0 T)) (hb0 : ∀ r ∈ Icc 0 T, 0 ≤ b r) (hA : DAdm T C b A)
    (hA0 : DAdm T C b A0) (hA1 : DAdm T C b A1)
    (hd : ∀ a : ℝ, 0 < a → ∀ r ∈ Icc 0 T, ∀ x : Pl, HasFDerivAt (A a r)
      (A0 a r x • ContinuousLinearMap.fst ℝ ℝ ℝ + A1 a r x • ContinuousLinearMap.snd ℝ ℝ ℝ) x)
    {σ : ℝ} (hσ : σ ∈ Icc 0 T) (x : Pl) :
    HasFDerivAt (dConv ν A σ)
      (dConv ν A0 σ x • ContinuousLinearMap.fst ℝ ℝ ℝ +
        dConv ν A1 σ x • ContinuousLinearMap.snd ℝ ℝ ℝ) x := by
  let F' : Pl → ℝ → (Pl →L[ℝ] ℝ) := fun y r =>
    A0 (ν * (σ - r)) r y • ContinuousLinearMap.fst ℝ ℝ ℝ +
      A1 (ν * (σ - r)) r y • ContinuousLinearMap.snd ℝ ℝ ℝ
  let bnd : ℝ → ℝ := fun r =>
    C * (1 + ν ^ (-(1 / 2 : ℝ))) * ((1 + (σ - r) ^ (-(1 / 2 : ℝ))) * b r) +
      C * (1 + ν ^ (-(1 / 2 : ℝ))) * ((1 + (σ - r) ^ (-(1 / 2 : ℝ))) * b r)
  have hbnd : IntervalIntegrable bnd volume 0 σ :=
    ((kInt_mul hb hσ).const_mul _).add ((kInt_mul hb hσ).const_mul _)
  have hint0 := dConv_int hν hC hb hb0 hA0 hσ x
  have hint1 := dConv_int hν hC hb hb0 hA1 hσ x
  have hmain : HasFDerivAt (fun y : Pl => ∫ r in (0 : ℝ)..σ, A (ν * (σ - r)) r y)
      (∫ r in (0 : ℝ)..σ, F' x r) x := by
    refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F := fun y r => A (ν * (σ - r)) r y) (F' := F') (bound := bnd) univ_mem ?_ ?_ ?_ ?_ hbnd ?_
    · refine Filter.Eventually.of_forall fun y => ?_
      rw [uIoc_of_le hσ.1]
      exact dAdm_meas hν hA hσ y
    · exact dConv_int hν hC hb hb0 hA hσ x
    · rw [uIoc_of_le hσ.1]
      exact DiffC.aesm_clm (dAdm_meas hν hA0 hσ x) (dAdm_meas hν hA1 hσ x)
    · filter_upwards [ae_ne_pt σ] with r hne hr y _
      rw [uIoc_of_le hσ.1] at hr
      have hr' : r ∈ Ico 0 σ := ⟨hr.1.le, lt_of_le_of_ne hr.2 hne⟩
      refine (DiffC.norm_clm_le _ _).trans (add_le_add ?_ ?_)
      · exact dAdm_pt hν hC hb0 hA0 hσ hr' y
      · exact dAdm_pt hν hC hb0 hA1 hσ hr' y
    · filter_upwards [ae_ne_pt σ] with r hne hr y _
      rw [uIoc_of_le hσ.1] at hr
      have hr' : r ∈ Ico 0 σ := ⟨hr.1.le, lt_of_le_of_ne hr.2 hne⟩
      exact hd _ (mul_pos hν (by linarith [hr'.2])) r ⟨hr'.1, hr'.2.le.trans hσ.2⟩ y
  have hval : (∫ r in (0 : ℝ)..σ, F' x r) =
      dConv ν A0 σ x • ContinuousLinearMap.fst ℝ ℝ ℝ +
        dConv ν A1 σ x • ContinuousLinearMap.snd ℝ ℝ ℝ := by
    simp only [F', dConv]
    have hi0 : IntervalIntegrable (fun r => A0 (ν * (σ - r)) r x • ContinuousLinearMap.fst ℝ ℝ ℝ)
        volume 0 σ := ⟨hint0.1.smul_const _, hint0.2.smul_const _⟩
    have hi1 : IntervalIntegrable (fun r => A1 (ν * (σ - r)) r x • ContinuousLinearMap.snd ℝ ℝ ℝ)
        volume 0 σ := ⟨hint1.1.smul_const _, hint1.2.smul_const _⟩
    rw [intervalIntegral.integral_add hi0 hi1,
      intervalIntegral.integral_smul_const, intervalIntegral.integral_smul_const]
  rw [hval] at hmain
  exact hmain

/-- The partials of `dConv`, from `dConv_deriv`. -/
theorem dConv_pd {ν C : ℝ} {b : ℝ → ℝ} {A A0 A1 : ℝ → ℝ → Pl → ℝ} (hν : 0 < ν) (hC : 0 ≤ C)
    (hb : ContinuousOn b (Icc 0 T)) (hb0 : ∀ r ∈ Icc 0 T, 0 ≤ b r) (hA : DAdm T C b A)
    (hA0 : DAdm T C b A0) (hA1 : DAdm T C b A1)
    (hd : ∀ a : ℝ, 0 < a → ∀ r ∈ Icc 0 T, ∀ x : Pl, HasFDerivAt (A a r)
      (A0 a r x • ContinuousLinearMap.fst ℝ ℝ ℝ + A1 a r x • ContinuousLinearMap.snd ℝ ℝ ℝ) x)
    {σ : ℝ} (hσ : σ ∈ Icc 0 T) (x : Pl) :
    B0579.pd 0 (dConv ν A σ) x = dConv ν A0 σ x ∧ B0579.pd 1 (dConv ν A σ) x = dConv ν A1 σ x := by
  have h := dConv_deriv hν hC hb hb0 hA hA0 hA1 hd hσ x
  unfold B0579.pd
  rw [h.fderiv]
  simp [B0579.dir]

end LS

end UnforcedLeray.Short.IIb.BwdRoute
