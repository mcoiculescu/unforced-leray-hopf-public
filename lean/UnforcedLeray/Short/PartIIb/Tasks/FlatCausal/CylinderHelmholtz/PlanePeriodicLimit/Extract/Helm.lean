import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T12_1_4_2
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlanePeriodicLimit.Extract.Avg

/-!
# Part II-b, task `PartII-b:T12/1/4/2/6` (`pplHelm`): planar Helmholtz identities pass to the weak limit

Source of record: `the November 2 reference manuscript` lines 1933-1935.

A compactly supported continuous test lies in `L²(W_M)` for `M` large; the pairings of `H (φ N)`
with it converge to those of `G` (`PPLWeak`) and equal the plane integrals; `divFree`, `orth`
tend to `0` along `φ`; `F ∈ L²_loc` from `CylLp c 2 F`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

namespace HelmAux

/-- Strongly measurable on `n` consecutive strips for a periodic function that is a.e. strongly
measurable on the cell. -/
theorem aesm_strips {c : ℝ} (hc : 0 < c) {F : ℝ × ℝ → CMerid}
    (hper : UnforcedLeray.Cyl.IsPeriodic c F)
    (hm : AEStronglyMeasurable F (volume.restrict (UnforcedLeray.Cyl.cell c))) (n : ℕ) (a : ℝ) :
    AEStronglyMeasurable F (volume.restrict (Ico a (a + (n : ℝ) * c) ×ˢ (univ : Set ℝ))) := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    have hnc : (0 : ℝ) ≤ (n : ℝ) * c := mul_nonneg (Nat.cast_nonneg n) hc.le
    have h1 : a ≤ a + (n : ℝ) * c := by linarith
    have h2 : a + (n : ℝ) * c ≤ a + (n : ℝ) * c + c := by linarith
    have e : a + ((n + 1 : ℕ) : ℝ) * c = a + (n : ℝ) * c + c := by push_cast; ring
    have hdisj : Disjoint (Ico a (a + (n : ℝ) * c) ×ˢ (univ : Set ℝ))
        (Ico (a + (n : ℝ) * c) (a + (n : ℝ) * c + c) ×ˢ (univ : Set ℝ)) := by
      rw [Set.disjoint_left]
      intro z hz1 hz2
      simp only [Set.mem_prod, Set.mem_Ico, Set.mem_univ, and_true] at hz1 hz2
      linarith [hz1.2, hz2.1]
    have hstrip : AEStronglyMeasurable F
        (volume.restrict (Ico (a + (n : ℝ) * c) (a + (n : ℝ) * c + c) ×ˢ (univ : Set ℝ))) :=
      ((UnforcedLeray.Cyl.isAddFundamentalDomain_strip hc _).aestronglyMeasurable_on_iff
        (UnforcedLeray.Cyl.isAddFundamentalDomain_cell hc)
        (fun g x => hper.vadd_zmultiples g x)).2 hm
    rw [e, ← Set.Ico_union_Ico_eq_Ico h1 h2, Set.union_prod,
      Measure.restrict_union hdisj (measurableSet_Ico.prod MeasurableSet.univ)]
    exact (ih a).add_measure hstrip

theorem ppWindow_eq (c : ℝ) (M : ℕ) :
    ppWindow c M = Ico (-((M : ℝ) * c)) (-((M : ℝ) * c) + ((2 * M : ℕ) : ℝ) * c) ×ˢ
      (univ : Set ℝ) := by
  ext z
  simp only [ppWindow, Set.mem_setOf_eq, Set.mem_prod, Set.mem_Ico, Set.mem_univ, and_true]
  push_cast
  constructor
  · intro h
    constructor <;> linarith [h.1, h.2]
  · intro h
    constructor <;> linarith [h.1, h.2]

/-- A `c`-periodic `L²` field is in `L²(W_M)`. -/
theorem memLp_window {c : ℝ} (hc : 0 < c) {F : ℝ × ℝ → CMerid} (hF : CylLp c 2 F) (M : ℕ) :
    MemLp F 2 (volume.restrict (ppWindow c M)) := by
  obtain ⟨hper, hmem⟩ := hF
  have hr0 : (0 : ℝ) < 2 := by norm_num
  have hpr : (ENNReal.ofReal 2).toReal = 2 := ENNReal.toReal_ofReal hr0.le
  have hp0 : ENNReal.ofReal 2 ≠ 0 := (ENNReal.ofReal_pos.2 hr0).ne'
  have hpt : ENNReal.ofReal 2 ≠ ⊤ := ENNReal.ofReal_ne_top
  have h2 : ENNReal.ofReal 2 = 2 := by simp
  rw [h2] at hmem hp0 hpt
  have hpr : ((2 : ℝ≥0∞)).toReal = 2 := by simp
  have hmeasA : AEStronglyMeasurable F (UnforcedLeray.Cyl.avgμ c) := hmem.1
  have hmeasC : AEStronglyMeasurable F (volume.restrict (UnforcedLeray.Cyl.cell c)) := by
    have : volume.restrict (UnforcedLeray.Cyl.cell c) ≪ UnforcedLeray.Cyl.avgμ c := by
      rw [UnforcedLeray.Cyl.avgμ, UnforcedLeray.Cyl.cellμ]
      have hne : ENNReal.ofReal c⁻¹ ≠ 0 := by
        simpa using inv_pos.2 hc
      exact (Measure.absolutelyContinuous_smul hne)
    exact hmeasA.mono_ac this
  have hperF : UnforcedLeray.Cyl.IsPeriodic c (fun z : ℝ × ℝ => ‖F z‖ₑ ^ (2 : ℝ)) := fun z => by
    show ‖F (z.1 + c, z.2)‖ₑ ^ (2 : ℝ) = ‖F z‖ₑ ^ (2 : ℝ)
    rw [hper z]
  have hcellfin : ∫⁻ z in UnforcedLeray.Cyl.cell c, ‖F z‖ₑ ^ (2 : ℝ) < ⊤ := by
    have hA : ∫⁻ z, ‖F z‖ₑ ^ (2 : ℝ) ∂(UnforcedLeray.Cyl.avgμ c) =
        ENNReal.ofReal c⁻¹ * ∫⁻ z in UnforcedLeray.Cyl.cell c, ‖F z‖ₑ ^ (2 : ℝ) :=
      UnforcedLeray.Cyl.lintegral_avgμ _
    have hlt := hmem.2
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt, hpr] at hlt
    have hlt' : (∫⁻ z, ‖F z‖ₑ ^ (2 : ℝ) ∂(UnforcedLeray.Cyl.avgμ c)) < ⊤ := by
      have := (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).1 hlt
      simpa using this
    rw [hA] at hlt'
    by_contra hcon
    rw [not_lt, top_le_iff] at hcon
    rw [hcon, ENNReal.mul_top (by simpa using inv_pos.2 hc)] at hlt'
    exact lt_irrefl _ hlt'
  have hWin : ∫⁻ z in ppWindow c M, ‖F z‖ₑ ^ (2 : ℝ) =
      ((2 * M : ℕ) : ℝ≥0∞) * ∫⁻ z in UnforcedLeray.Cyl.cell c, ‖F z‖ₑ ^ (2 : ℝ) := by
    rw [ppWindow_eq, lintegral_strips_eq hc hperF]
  refine ⟨?_, ?_⟩
  · rw [ppWindow_eq]
    exact aesm_strips hc hper hmeasC _ _
  · rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt, hpr, hWin]
    refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
    exact (ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) hcellfin).ne

/-- Pairing of an `L²(W_M)` field with a continuous compactly supported test. -/
theorem test_pair {c : ℝ} (hc : 0 < c) (T : ℝ × ℝ → CMerid) (hTc : Continuous T)
    (hTs : HasCompactSupport T) :
    ∃ M : ℕ, MemLp T 2 (volume.restrict (ppWindow c M)) ∧
      ∀ K : ℝ × ℝ → CMerid, MemLp K 2 (volume.restrict (ppWindow c M)) →
        Integrable (fun z => ∑ i : Fin 2, K z i * T z i) ∧
          ∫ z, ∑ i : Fin 2, K z i * T z i = ∫ z in ppWindow c M, ∑ i : Fin 2, K z i * T z i := by
  obtain ⟨C, hC⟩ := hTs.isCompact.exists_bound_of_continuousOn
    (f := fun z : ℝ × ℝ => z.1) (continuous_fst.continuousOn)
  obtain ⟨M, hM⟩ := exists_nat_gt (C / c)
  have hCM : C < (M : ℝ) * c := (div_lt_iff₀ hc).1 hM
  have hsub : tsupport T ⊆ ppWindow c M := by
    intro x hx
    have h := hC x hx
    rw [Real.norm_eq_abs] at h
    have h2 := abs_le.mp h
    constructor
    · simp only [neg_mul]; linarith [h2.1]
    · linarith [h2.2]
  have hTzero : ∀ z, z ∉ ppWindow c M → T z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport (fun h => hz (hsub h))
  have hTm : MemLp T 2 (volume.restrict (ppWindow c M)) := hTc.memLp_of_hasCompactSupport hTs
  refine ⟨M, hTm, fun K hK => ?_⟩
  have hsupp : ∀ z, z ∉ ppWindow c M → ∑ i : Fin 2, K z i * T z i = 0 := by
    intro z hz
    simp [hTzero z hz]
  have hint : Integrable (fun z => ∑ i : Fin 2, K z i * T z i)
      (volume.restrict (ppWindow c M)) := by
    have hprod : Integrable (fun z => ‖K z‖ * ‖T z‖) (volume.restrict (ppWindow c M)) :=
      MemLp.integrable_mul (f := fun z => ‖K z‖) (g := fun z => ‖T z‖) hK.norm hTm.norm
    have hmeas : AEStronglyMeasurable (fun z => ∑ i : Fin 2, K z i * T z i)
        (volume.restrict (ppWindow c M)) := by
      have hsm : ∀ i : Fin 2, AEStronglyMeasurable (fun z => K z i * T z i)
          (volume.restrict (ppWindow c M)) := fun i => by
        have h1 : AEStronglyMeasurable (fun z => K z i) (volume.restrict (ppWindow c M)) :=
          (EuclideanSpace.proj i).continuous.comp_aestronglyMeasurable hK.1
        have h2 : AEStronglyMeasurable (fun z => T z i) (volume.restrict (ppWindow c M)) :=
          ((EuclideanSpace.proj i).continuous.comp hTc).aestronglyMeasurable
        exact h1.mul h2
      have e : (fun z => ∑ i : Fin 2, K z i * T z i) =
          fun z => K z 0 * T z 0 + K z 1 * T z 1 := by
        funext z
        simp [Fin.sum_univ_two]
      rw [e]
      exact (hsm 0).add (hsm 1)
    refine Integrable.mono' (hprod.const_mul 2) hmeas (Filter.Eventually.of_forall fun z => ?_)
    calc ‖∑ i : Fin 2, K z i * T z i‖ ≤ ∑ i : Fin 2, ‖K z i * T z i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin 2, ‖K z‖ * ‖T z‖ := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_mul]
          exact mul_le_mul (PiLp.norm_apply_le _ _) (PiLp.norm_apply_le _ _) (norm_nonneg _)
            (norm_nonneg _)
      _ = 2 * (‖K z‖ * ‖T z‖) := by simp
  have hsuppset : Function.support (fun z => ∑ i : Fin 2, K z i * T z i) ⊆ ppWindow c M := by
    intro z hz
    by_contra h
    exact hz (hsupp z h)
  refine ⟨(integrableOn_iff_integrable_of_support_subset hsuppset).1 hint, ?_⟩
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero hsupp).symm

end HelmAux

theorem pplHelm : UnforcedLeray.Short.IIb.PPLHelm := by
  intro r C c F H hctx φ G hφ hweak
  obtain ⟨hr, hC, hc, hF, hF2, hP⟩ := hctx
  obtain ⟨hGmem, hconv⟩ := hweak
  have hFmem := HelmAux.memLp_window hc hF2
  -- the limit identity for a test
  have key : ∀ T : ℝ × ℝ → CMerid, Continuous T → HasCompactSupport T →
      ∃ M : ℕ, MemLp T 2 (volume.restrict (ppWindow c M)) ∧
        (∀ K : ℝ × ℝ → CMerid, MemLp K 2 (volume.restrict (ppWindow c M)) →
          Integrable (fun z => ∑ i : Fin 2, K z i * T z i) ∧
            ∫ z, ∑ i : Fin 2, K z i * T z i =
              ∫ z in ppWindow c M, ∑ i : Fin 2, K z i * T z i) ∧
        Tendsto (fun N => ∫ z, ∑ i : Fin 2, H (φ N) z i * T z i) atTop
          (𝓝 (∫ z, ∑ i : Fin 2, G z i * T z i)) := by
    intro T hTc hTs
    obtain ⟨M, hTm, hpair⟩ := HelmAux.test_pair hc T hTc hTs
    refine ⟨M, hTm, hpair, ?_⟩
    have h1 := hconv M T hTm
    have e1 : (fun N => ∫ z, ∑ i : Fin 2, H (φ N) z i * T z i) =
        fun N => ∫ z in ppWindow c M, ∑ i : Fin 2, H (φ N) z i * T z i :=
      funext fun N => (hpair _ (hP.memLp (φ N) M).1).2
    rw [e1, (hpair _ (hGmem M)).2]
    exact h1
  constructor
  · intro φ0 hφ0
    have hcont : ∀ v : ℝ × ℝ, Continuous fun z => fderiv ℝ φ0 z v := fun v =>
      (hφ0.smooth.continuous_fderiv (by simp)).clm_apply continuous_const
    set T : ℝ × ℝ → CMerid := fun z => WithLp.toLp 2
      (fun i : Fin 2 => ((![fderiv ℝ φ0 z (1, 0), fderiv ℝ φ0 z (0, 1)] i : ℝ) : ℂ)) with hT
    have hTc : Continuous T := by
      refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
      fin_cases i
      · exact Complex.continuous_ofReal.comp (hcont (1, 0))
      · exact Complex.continuous_ofReal.comp (hcont (0, 1))
    have hTs : HasCompactSupport T := by
      refine HasCompactSupport.intro hφ0.compact.isCompact fun x hx => ?_
      have : fderiv ℝ φ0 x = 0 := by
        by_contra h
        exact hx (support_fderiv_subset ℝ (Function.mem_support.2 h))
      ext i
      fin_cases i <;> simp [hT, this]
    obtain ⟨M, hTm, hpair, hlim⟩ := key T hTc hTs
    have eT : ∀ K : ℝ × ℝ → CMerid, (fun z => ∑ i : Fin 2, K z i * T z i) =
        fun z => K z 0 * (fderiv ℝ φ0 z (1, 0) : ℂ) + K z 1 * (fderiv ℝ φ0 z (0, 1) : ℂ) := by
      intro K
      funext z
      simp [hT, Fin.sum_univ_two]
    have hdiv := hP.divFree φ0 hφ0
    have hdiv' : Tendsto (fun N => ∫ z, (H (φ N) z 0 * (fderiv ℝ φ0 z (1, 0) : ℂ) +
        H (φ N) z 1 * (fderiv ℝ φ0 z (0, 1) : ℂ))) atTop (𝓝 0) :=
      hdiv.comp hφ.tendsto_atTop
    have hlim' := hlim
    simp only [eT] at hlim'
    refine ⟨?_, tendsto_nhds_unique hlim' hdiv'⟩
    have := (hpair G (hGmem M)).1
    simpa only [eT] using this
  · intro Ψ hΨ
    set T : ℝ × ℝ → CMerid := fun z => WithLp.toLp 2 (fun i : Fin 2 => ((Ψ z i : ℝ) : ℂ))
      with hT
    have hTc : Continuous T := by
      refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
      exact Complex.continuous_ofReal.comp (hΨ.comp i).smooth.continuous
    have hTs : HasCompactSupport T := by
      refine HasCompactSupport.intro
        ((hΨ.comp 0).compact.isCompact.union (hΨ.comp 1).compact.isCompact) fun x hx => ?_
      rw [Set.mem_union, not_or] at hx
      ext i
      fin_cases i
      · simp [hT, image_eq_zero_of_notMem_tsupport hx.1]
      · simp [hT, image_eq_zero_of_notMem_tsupport hx.2]
    obtain ⟨M, hTm, hpair, hlim⟩ := key T hTc hTs
    have eT : ∀ K : ℝ × ℝ → CMerid, (fun z => ∑ i : Fin 2, K z i * T z i) =
        fun z => ∑ i : Fin 2, K z i * (Ψ z i : ℂ) := by
      intro K
      funext z
      simp [hT]
    have eS : (fun z => ∑ i : Fin 2, (F z i - G z i) * (Ψ z i : ℂ)) =
        fun z => (∑ i : Fin 2, F z i * T z i) - ∑ i : Fin 2, G z i * T z i := by
      funext z
      simp only [hT, PiLp.toLp_apply, ← Finset.sum_sub_distrib, sub_mul]
    have iF := (hpair F (hFmem M)).1
    have iG := (hpair G (hGmem M)).1
    have iH : ∀ N, Integrable (fun z => ∑ i : Fin 2, H (φ N) z i * T z i) :=
      fun N => (hpair _ (hP.memLp (φ N) M).1).1
    have hlim2 : Tendsto (fun N => ∫ z, ∑ i : Fin 2, (F z i - H (φ N) z i) * (Ψ z i : ℂ))
        atTop (𝓝 ((∫ z, ∑ i : Fin 2, F z i * T z i) - ∫ z, ∑ i : Fin 2, G z i * T z i)) := by
      have e : (fun N => ∫ z, ∑ i : Fin 2, (F z i - H (φ N) z i) * (Ψ z i : ℂ)) =
          fun N => (∫ z, ∑ i : Fin 2, F z i * T z i) -
            ∫ z, ∑ i : Fin 2, H (φ N) z i * T z i := by
        funext N
        have : (fun z => ∑ i : Fin 2, (F z i - H (φ N) z i) * (Ψ z i : ℂ)) =
            fun z => (∑ i : Fin 2, F z i * T z i) - ∑ i : Fin 2, H (φ N) z i * T z i := by
          funext z
          simp only [hT, PiLp.toLp_apply, ← Finset.sum_sub_distrib, sub_mul]
        rw [this, integral_sub iF (iH N)]
      rw [e]
      exact tendsto_const_nhds.sub hlim
    have hor := (hP.orth Ψ hΨ).comp hφ.tendsto_atTop
    have hu := tendsto_nhds_unique hlim2 hor
    rw [eS]
    refine ⟨iF.sub iG, ?_⟩
    rw [integral_sub iF iG]
    exact hu

end UnforcedLeray.Short.IIb
