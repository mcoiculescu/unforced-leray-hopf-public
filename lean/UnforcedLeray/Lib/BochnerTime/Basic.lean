import UnforcedLeray.Lib.BochnerTime.Prelim

/-!
# Weak derivatives in time of Banach-valued functions (INF14 target T1)


("Time: time regularity uses Bochner `Lp X p (volume.restrict I)` with the predicate
`HasWeakDerivTime`") and §5.2 target T1; decision D15 of `scoping/README.md` §3 (the
Banach-valued FTC in time is built once, here).

The manuscript uses Banach-valued Sobolev functions of one time variable in several places:
`u ∈ W^{1,p}(I; L^p)` for the frozen-kernel row function (tex 3904–3921, blueprint unit B0445),
the one-dimensional trace estimate for the continuous `W^{1,p}(I)` representative (tex 4059–4065,
B0236), and the comoving FTC behind the phase sup bound (bypass B6 of the scoping note, units
B0434, B0435, B0451).

## Definition

`HasWeakDerivTime a b u u'` says that `u, u' : ℝ → X` are Bochner integrable on `Ioo a b` and
`∫ φ' • u = -∫ φ • u'` for every smooth `φ` compactly supported in `Ioo a b`. Integrability on
the bounded interval is implied by the manuscript's `u, u' ∈ L^p(I; X)`, `p ≥ 1`, so the
predicate is no stronger than the manuscript's hypothesis. All integrals are over `ℝ`; since
`φ` vanishes off `Ioo a b` and `u, u'` are integrable there, they are genuine Bochner integrals
(no junk value): see `integrable_deriv_smul`, `integrable_smul`.

## Main results

* `HasWeakDerivTime.exists_rep`: the FTC (continuous representative on `Icc a b`, a.e. equal to
  `u` on `Ioo a b`, increments given by `∫ u'`);
* `HasWeakDerivTime.rep`, `continuousOn_rep`, `ae_eq_rep`, `rep_sub_rep`, `eqOn_rep`
  (uniqueness of the continuous representative);
* `hasWeakDerivTime_of_primitive`: the converse;
* `HasWeakDerivTime.hasDerivAt_rep`, `HasWeakDerivTime.contDiffOn_rep`: the C¹ upgrade when
  `u'` is continuous;
* `HasWeakDerivTime.map`: composition with a bounded linear map (B0445: pairing with a fixed
  kernel commutes with the time derivative);
* `HasWeakDerivTime.congr_ae`, `add`, `const_smul`.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology intervalIntegral
open scoped ContDiff

namespace UnforcedLeray.BochnerTime

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- **Weak derivative in time** (scoping note §5.2, T1). `u'` is the weak derivative of `u` on
`Ioo a b`: both are Bochner integrable on `Ioo a b`, and `∫ φ' • u = -∫ φ • u'` for every smooth
scalar `φ` with compact support in `Ioo a b`. -/
structure HasWeakDerivTime (a b : ℝ) (u u' : ℝ → X) : Prop where
  int : IntegrableOn u (Ioo a b)
  int' : IntegrableOn u' (Ioo a b)
  identity : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo a b →
    ∫ t, deriv φ t • u t = -∫ t, φ t • u' t

omit [CompleteSpace X] in
/-- For a test function `φ` on `Ioo a b` and `u` integrable on `Ioo a b`, `φ' • u` is
integrable on `ℝ`. -/
theorem integrable_deriv_smul {a b : ℝ} {φ : ℝ → ℝ} {u : ℝ → X} (hφ : ContDiff ℝ ∞ φ)
    (hφs : HasCompactSupport φ) (hφt : tsupport φ ⊆ Ioo a b) (hu : IntegrableOn u (Ioo a b)) :
    Integrable (fun t => deriv φ t • u t) :=
  integrable_smul_of_tsupport_subset (hφ.continuous_deriv (by simp)) hφs.deriv
    (tsupport_deriv_subset_Ioo hφt) hu

omit [CompleteSpace X] in
/-- For a test function `φ` on `Ioo a b` and `u` integrable on `Ioo a b`, `φ • u` is integrable
on `ℝ`. -/
theorem integrable_smul {a b : ℝ} {φ : ℝ → ℝ} {u : ℝ → X} (hφ : ContDiff ℝ ∞ φ)
    (hφs : HasCompactSupport φ) (hφt : tsupport φ ⊆ Ioo a b) (hu : IntegrableOn u (Ioo a b)) :
    Integrable (fun t => φ t • u t) :=
  integrable_smul_of_tsupport_subset hφ.continuous hφs hφt hu

/-- The integral of the derivative of a smooth function supported in `Ioo a b` vanishes. -/
theorem integral_deriv_eq_zero_of_tsupport_subset {a b : ℝ} {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφt : tsupport φ ⊆ Ioo a b) : ∫ t, deriv φ t = 0 := by
  have h1 : ∫ t, deriv φ t = ∫ t in a..b, deriv φ t := by
    symm
    apply intervalIntegral.integral_eq_integral_of_support_subset
    exact (support_deriv_subset.trans hφt).trans Ioo_subset_Ioc_self
  rw [h1, integral_deriv_eq_sub (fun x _ => (hφ.differentiable (by simp)) x)
    ((hφ.continuous_deriv (by simp)).intervalIntegrable _ _),
    eq_zero_of_tsupport_subset hφt (by simp), eq_zero_of_tsupport_subset hφt (by simp), sub_zero]

omit [CompleteSpace X] in
/-- The primitive `t ↦ ∫ r in a..t, g r` of a function integrable on `Ioo a b` is continuous on
`Icc a b`. -/
theorem continuousOn_primitive_Icc {a b : ℝ} {g : ℝ → X} (hg : IntegrableOn g (Ioo a b)) :
    ContinuousOn (fun t => ∫ r in a..t, g r) (Icc a b) := by
  rcases le_or_gt a b with hab | hab
  · have : IntegrableOn g (uIcc a b) := by
      rw [uIcc_of_le hab, integrableOn_Icc_iff_integrableOn_Ioo]; exact hg
    simpa [uIcc_of_le hab] using intervalIntegral.continuousOn_primitive_interval this
  · rw [Icc_eq_empty_of_lt hab]; exact continuousOn_empty _

omit [CompleteSpace X] in
/-- The primitive of a function integrable on `Ioo a b` is integrable on `Ioo a b`. -/
theorem integrableOn_primitive {a b : ℝ} {g : ℝ → X} (hg : IntegrableOn g (Ioo a b)) :
    IntegrableOn (fun t => ∫ r in a..t, g r) (Ioo a b) := by
  rcases le_or_gt a b with hab | hab
  · exact ((continuousOn_primitive_Icc hg).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  · rw [Ioo_eq_empty_of_le hab.le]; exact integrableOn_empty

/-- **Banach-valued FTC** (T1). A function with a weak time derivative on `Ioo a b` has a
representative continuous on `Icc a b` whose increments are the integrals of the derivative. -/
theorem HasWeakDerivTime.exists_rep {a b : ℝ} {u u' : ℝ → X} (h : HasWeakDerivTime a b u u') :
    ∃ ũ : ℝ → X, ContinuousOn ũ (Icc a b) ∧ u =ᵐ[volume.restrict (Ioo a b)] ũ ∧
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ũ t - ũ s = ∫ r in s..t, u' r := by
  rcases le_or_gt b a with hba | hab
  · refine ⟨fun _ => 0, continuousOn_const, ?_, ?_⟩
    · rw [Ioo_eq_empty_of_le hba, Measure.restrict_empty, Filter.EventuallyEq, ae_zero]
      exact Filter.eventually_bot
    · intro s hs t ht
      have hs' : s = a := le_antisymm (hs.2.trans hba) hs.1
      have ht' : t = a := le_antisymm (ht.2.trans hba) ht.1
      simp [hs', ht']
  set v : ℝ → X := fun t => ∫ r in a..t, u' r with hv_def
  have hvI : IntegrableOn v (Ioo a b) := integrableOn_primitive h.int'
  have hw : IntegrableOn (fun t => u t - v t) (Ioo a b) := h.int.sub hvI
  have hw0 : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo a b →
      ∫ t, deriv φ t • (u t - v t) = 0 := by
    intro φ hφ hφs hφt
    simp only [smul_sub]
    rw [integral_sub (integrable_deriv_smul hφ hφs hφt h.int)
      (integrable_deriv_smul hφ hφs hφt hvI), h.identity φ hφ hφs hφt,
      integral_deriv_smul_primitive hφ hφt h.int', sub_self]
  obtain ⟨c, hc⟩ := ae_eq_const_of_integral_deriv_smul_eq_zero hab hw hw0
  refine ⟨fun t => c + v t, continuousOn_const.add (continuousOn_primitive_Icc h.int'), ?_, ?_⟩
  · filter_upwards [hc] with t ht
    rw [← ht]; abel
  · intro s hs t ht
    have hI : IntervalIntegrable u' volume a b :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 h.int'
    have hs' : IntervalIntegrable u' volume a s := hI.mono_set (by
      rw [uIcc_of_le hab.le, uIcc_of_le hs.1]; exact Icc_subset_Icc le_rfl hs.2)
    have ht' : IntervalIntegrable u' volume a t := hI.mono_set (by
      rw [uIcc_of_le hab.le, uIcc_of_le ht.1]; exact Icc_subset_Icc le_rfl ht.2)
    simp only [hv_def, add_sub_add_left_eq_sub]
    exact integral_interval_sub_left ht' hs'

/-- The continuous representative of a function with a weak time derivative (any choice from
`HasWeakDerivTime.exists_rep`; it is unique on `Icc a b` when `a < b`, see `eqOn_rep`). -/
noncomputable def HasWeakDerivTime.rep {a b : ℝ} {u u' : ℝ → X} (h : HasWeakDerivTime a b u u') :
    ℝ → X :=
  Classical.choose h.exists_rep

theorem HasWeakDerivTime.continuousOn_rep {a b : ℝ} {u u' : ℝ → X}
    (h : HasWeakDerivTime a b u u') : ContinuousOn h.rep (Icc a b) :=
  (Classical.choose_spec h.exists_rep).1

theorem HasWeakDerivTime.ae_eq_rep {a b : ℝ} {u u' : ℝ → X} (h : HasWeakDerivTime a b u u') :
    u =ᵐ[volume.restrict (Ioo a b)] h.rep :=
  (Classical.choose_spec h.exists_rep).2.1

/-- **FTC for the representative.** `ũ t - ũ s = ∫_s^t u'` for `s, t ∈ Icc a b`. -/
theorem HasWeakDerivTime.rep_sub_rep {a b : ℝ} {u u' : ℝ → X} (h : HasWeakDerivTime a b u u')
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) : h.rep t - h.rep s = ∫ r in s..t, u' r :=
  (Classical.choose_spec h.exists_rep).2.2 s hs t ht

/-- **Uniqueness of the continuous representative.** Any function continuous on `Icc a b` and
a.e. equal to `u` on `Ioo a b` coincides with `rep` on `Icc a b` (for `a < b`). -/
theorem HasWeakDerivTime.eqOn_rep {a b : ℝ} (hab : a < b) {u u' : ℝ → X}
    (h : HasWeakDerivTime a b u u') {ũ : ℝ → X} (hc : ContinuousOn ũ (Icc a b))
    (hae : u =ᵐ[volume.restrict (Ioo a b)] ũ) : EqOn ũ h.rep (Icc a b) := by
  have h1 : ũ =ᵐ[volume.restrict (Icc a b)] h.rep := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
    exact hae.symm.trans h.ae_eq_rep
  refine Measure.eqOn_of_ae_eq h1 hc h.continuousOn_rep ?_
  rw [interior_Icc, closure_Ioo hab.ne]

/-- Every value of the representative is given by the FTC from the left endpoint. -/
theorem HasWeakDerivTime.rep_eq {a b : ℝ} {u u' : ℝ → X} (h : HasWeakDerivTime a b u u')
    (hab : a ≤ b) {t : ℝ} (ht : t ∈ Icc a b) : h.rep t = h.rep a + ∫ r in a..t, u' r := by
  rw [← h.rep_sub_rep ⟨le_rfl, hab⟩ ht]; abel

/-- **Converse of the FTC** (T1). A primitive `x₀ + ∫_a^t u'` has weak derivative `u'`. -/
theorem hasWeakDerivTime_of_primitive {a b : ℝ} {u' : ℝ → X} (hu' : IntegrableOn u' (Ioo a b))
    (x₀ : X) : HasWeakDerivTime a b (fun t => x₀ + ∫ r in a..t, u' r) u' := by
  refine ⟨(integrableOn_const ?_).add (integrableOn_primitive hu'), hu', ?_⟩
  · simp
  intro φ hφ hφs hφt
  have hc : Integrable (fun t => deriv φ t • x₀) :=
    ((hφ.continuous_deriv (by simp)).integrable_of_hasCompactSupport hφs.deriv).smul_const x₀
  simp only [smul_add]
  rw [integral_add hc (integrable_deriv_smul hφ hφs hφt (integrableOn_primitive hu')),
    _root_.integral_smul_const, integral_deriv_eq_zero_of_tsupport_subset hφ hφt, zero_smul,
    zero_add, integral_deriv_smul_primitive hφ hφt hu']

/-- **C¹ upgrade, pointwise form** (T1). If `u'` is continuous on `Ioo a b`, the representative
has derivative `u' t` at every `t ∈ Ioo a b`. -/
theorem HasWeakDerivTime.hasDerivAt_rep {a b : ℝ} {u u' : ℝ → X} (h : HasWeakDerivTime a b u u')
    (hc : ContinuousOn u' (Ioo a b)) {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt h.rep (u' t) t := by
  have hab : a ≤ b := (ht.1.trans ht.2).le
  have hI : IntervalIntegrable u' volume a t :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1.le).2
      (h.int'.mono_set (Ioo_subset_Ioo_right ht.2.le))
  have hd : HasDerivAt (fun s => h.rep a + ∫ r in a..s, u' r) (u' t) t :=
    (integral_hasDerivAt_right hI
      (hc.stronglyMeasurableAtFilter isOpen_Ioo t ht)
      (hc.continuousAt (isOpen_Ioo.mem_nhds ht))).const_add _
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  exact h.rep_eq hab (Ioo_subset_Icc_self hs)

/-- **C¹ upgrade** (T1). If `u'` is continuous on `Ioo a b`, the representative is `C¹` on
`Ioo a b` with derivative `u'`. -/
theorem HasWeakDerivTime.contDiffOn_rep {a b : ℝ} {u u' : ℝ → X} (h : HasWeakDerivTime a b u u')
    (hc : ContinuousOn u' (Ioo a b)) :
    ContDiffOn ℝ 1 h.rep (Ioo a b) ∧ ∀ t ∈ Ioo a b, HasDerivAt h.rep (u' t) t := by
  have hd := fun t (ht : t ∈ Ioo a b) => h.hasDerivAt_rep hc ht
  refine ⟨?_, hd⟩
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨fun t ht => (hd t ht).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  rw [contDiffOn_zero]
  exact hc.congr fun t ht => (hd t ht).deriv

/-- **Bounded linear images** (T1; B0445). If `u'` is the weak time derivative of `u`, then
`L ∘ u'` is the weak time derivative of `L ∘ u` for every bounded linear `L`. -/
theorem HasWeakDerivTime.map {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {a b : ℝ} {u u' : ℝ → X} (h : HasWeakDerivTime a b u u') (L : X →L[ℝ] Y) :
    HasWeakDerivTime a b (fun t => L (u t)) (fun t => L (u' t)) := by
  refine ⟨L.integrable_comp h.int, L.integrable_comp h.int', fun φ hφ hφs hφt => ?_⟩
  simp only [← L.map_smul]
  rw [L.integral_comp_comm (integrable_deriv_smul hφ hφs hφt h.int),
    L.integral_comp_comm (integrable_smul hφ hφs hφt h.int'), h.identity φ hφ hφs hφt, L.map_neg]

omit [CompleteSpace X] in
/-- Changing `u` and `u'` on null subsets of `Ioo a b` preserves the weak derivative. -/
theorem HasWeakDerivTime.congr_ae {a b : ℝ} {u u' v v' : ℝ → X} (h : HasWeakDerivTime a b u u')
    (hv : u =ᵐ[volume.restrict (Ioo a b)] v) (hv' : u' =ᵐ[volume.restrict (Ioo a b)] v') :
    HasWeakDerivTime a b v v' := by
  refine ⟨h.int.congr_fun_ae hv, h.int'.congr_fun_ae hv', fun φ hφ hφs hφt => ?_⟩
  have e1 : ∫ t, deriv φ t • v t = ∫ t, deriv φ t • u t := by
    refine integral_congr_ae ?_
    have := (ae_restrict_iff' measurableSet_Ioo).1 hv
    filter_upwards [this] with t ht
    by_cases hmem : t ∈ Ioo a b
    · rw [ht hmem]
    · rw [eq_zero_of_tsupport_subset (tsupport_deriv_subset_Ioo hφt) hmem, zero_smul, zero_smul]
  have e2 : ∫ t, φ t • v' t = ∫ t, φ t • u' t := by
    refine integral_congr_ae ?_
    have := (ae_restrict_iff' measurableSet_Ioo).1 hv'
    filter_upwards [this] with t ht
    by_cases hmem : t ∈ Ioo a b
    · rw [ht hmem]
    · rw [eq_zero_of_tsupport_subset hφt hmem, zero_smul, zero_smul]
  rw [e1, e2, h.identity φ hφ hφs hφt]

omit [CompleteSpace X] in
/-- Weak time derivatives add. -/
theorem HasWeakDerivTime.add {a b : ℝ} {u u' v v' : ℝ → X} (hu : HasWeakDerivTime a b u u')
    (hv : HasWeakDerivTime a b v v') :
    HasWeakDerivTime a b (fun t => u t + v t) (fun t => u' t + v' t) := by
  refine ⟨hu.int.add hv.int, hu.int'.add hv.int', fun φ hφ hφs hφt => ?_⟩
  simp only [smul_add]
  rw [integral_add (integrable_deriv_smul hφ hφs hφt hu.int)
      (integrable_deriv_smul hφ hφs hφt hv.int),
    integral_add (integrable_smul hφ hφs hφt hu.int') (integrable_smul hφ hφs hφt hv.int'),
    hu.identity φ hφ hφs hφt, hv.identity φ hφ hφs hφt, neg_add]

/-- Weak time derivatives commute with scalar multiplication. -/
theorem HasWeakDerivTime.const_smul {a b : ℝ} {u u' : ℝ → X} (hu : HasWeakDerivTime a b u u')
    (c : ℝ) : HasWeakDerivTime a b (fun t => c • u t) (fun t => c • u' t) :=
  hu.map (c • ContinuousLinearMap.id ℝ X)

end UnforcedLeray.BochnerTime
