import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Fundamental lemma on a period (helper for `PartII-a:N01/3/3/A`)

An integrable `F` on `(0, P]` annihilated by all smooth `P`-periodic `χ` vanishes a.e.
Route: a test `g ∈ C_c^∞((0,P))` is periodised by `χ = g ∘ toIcoMod`, which is smooth, periodic
and equals `g` on `(0,P]`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.N01

/-- Periodisation of a test function supported in `(0,P)` is smooth. -/
theorem periodise_contDiff {P : ℝ} (hP : 0 < P) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hsupp : tsupport g ⊆ Ioo 0 P) : ContDiff ℝ ∞ (fun t => g (toIcoMod hP 0 t)) := by
  rw [contDiff_iff_contDiffAt]
  intro t0
  have hmem := toIcoMod_mem_Ico hP 0 t0
  rw [zero_add] at hmem
  have hdec := toIcoMod_add_toIcoDiv_zsmul hP 0 t0
  set a := toIcoMod hP 0 t0 with ha
  set n := toIcoDiv hP 0 t0 with hn
  by_cases h0 : a = 0
  · -- g vanishes near 0 and near P
    have h0' : (0 : ℝ) ∉ tsupport g := fun h => by simpa using hsupp h
    have hP' : P ∉ tsupport g := fun h => by simpa using hsupp h
    obtain ⟨δ1, hδ1, hg1⟩ := Metric.eventually_nhds_iff.1 ((notMem_tsupport_iff_eventuallyEq.1 h0'))
    obtain ⟨δ2, hδ2, hg2⟩ := Metric.eventually_nhds_iff.1 ((notMem_tsupport_iff_eventuallyEq.1 hP'))
    have hev : (fun t => g (toIcoMod hP 0 t)) =ᶠ[𝓝 t0] fun _ => (0 : ℝ) := by
      refine Metric.eventually_nhds_iff.2 ⟨min (min δ1 δ2) P, by positivity, fun t ht => ?_⟩
      have hd : |t - t0| < min (min δ1 δ2) P := by simpa [Real.dist_eq] using ht
      have h1 : |t - t0| < δ1 := lt_of_lt_of_le hd ((min_le_left _ _).trans (min_le_left _ _))
      have h2 : |t - t0| < δ2 := lt_of_lt_of_le hd ((min_le_left _ _).trans (min_le_right _ _))
      have h3 : |t - t0| < P := lt_of_lt_of_le hd (min_le_right _ _)
      have ht0 : t0 = n • P := by rw [h0] at hdec; simpa using hdec.symm
      rcases le_or_gt 0 (t - t0) with hs | hs
      · have : toIcoMod hP 0 t = t - t0 := by
          rw [toIcoMod_eq_iff]
          refine ⟨⟨hs, by rw [abs_of_nonneg hs] at h3; linarith⟩, n, ?_⟩
          rw [← ht0]; ring
        simp only [this]
        have := hg1 (y := t - t0) (by rw [Real.dist_eq, sub_zero]; exact h1)
        simpa using this
      · have : toIcoMod hP 0 t = t - t0 + P := by
          rw [toIcoMod_eq_iff]
          refine ⟨⟨by rw [abs_of_neg hs] at h3; linarith, by linarith⟩, n - 1, ?_⟩
          rw [sub_one_zsmul, ← ht0]; ring
        simp only [this]
        have := hg2 (y := t - t0 + P) (by
          rw [Real.dist_eq]
          have : t - t0 + P - P = t - t0 := by ring
          rw [this]; exact h2)
        simpa using this
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have haI : a ∈ Ioo 0 P := ⟨lt_of_le_of_ne hmem.1 (Ne.symm h0), hmem.2⟩
    have hopen : IsOpen {t : ℝ | t - (t0 - a) ∈ Ioo 0 P} :=
      (isOpen_Ioo (a := (0:ℝ)) (b := P)).preimage ((continuous_id (X := ℝ)).sub continuous_const)
    have hev : (fun t => g (toIcoMod hP 0 t)) =ᶠ[𝓝 t0] fun t => g (t - (t0 - a)) := by
      filter_upwards [hopen.mem_nhds (by simpa using haI)] with t ht
      have : toIcoMod hP 0 t = t - (t0 - a) := by
        rw [toIcoMod_eq_iff]
        refine ⟨⟨ht.1.le, by simpa using ht.2⟩, n, ?_⟩
        have : t0 - a = n • P := by linarith
        rw [this]; ring
      simp only [this]
    exact ((hg.comp (contDiff_id.sub contDiff_const)).contDiffAt).congr_of_eventuallyEq hev

/-- Fundamental lemma of the calculus of variations on a period. -/
theorem periodicFundamental : ∀ (P : ℝ), 0 < P → ∀ F : ℝ → ℝ, IntegrableOn F (Set.Ioc 0 P) →
    (∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → Function.Periodic χ P →
      ∫ τ in Set.Ioc 0 P, χ τ * F τ = 0) →
    ∀ᵐ τ ∂(MeasureTheory.volume.restrict (Set.Ioc 0 P)), F τ = 0 := by
  intro P hP F hF h
  have hloc : LocallyIntegrableOn F (Ioo 0 P) (volume.restrict (Ioc 0 P)) :=
    (hF.locallyIntegrable).locallyIntegrableOn _
  have key := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc (by
    intro g hg _ hgs
    have hχ := h (fun t => g (toIcoMod hP 0 t)) (periodise_contDiff hP hg hgs)
      (fun t => by simp only [toIcoMod_add_right])
    have hg0 : g 0 = 0 := by
      by_contra hne
      exact (by simpa using hgs (subset_tsupport g hne) : False)
    have hgP : g P = 0 := by
      by_contra hne
      exact (by simpa using hgs (subset_tsupport g hne) : False)
    refine Eq.trans ?_ hχ
    refine setIntegral_congr_fun (measurableSet_Ioc (a := (0:ℝ)) (b := P)) (fun t ht => ?_)
    simp only [smul_eq_mul]
    congr 1
    rcases eq_or_lt_of_le ht.2 with h1 | h1
    · subst h1
      rw [hgP]
      have : toIcoMod hP 0 t = 0 := by
        rw [toIcoMod_eq_iff]; exact ⟨⟨le_rfl, by simpa using hP⟩, 1, by simp⟩
      rw [this, hg0]
    · have : toIcoMod hP 0 t = t := by
        rw [toIcoMod_eq_iff]; exact ⟨⟨ht.1.le, by simpa using h1⟩, 0, by simp⟩
      rw [this])
  have hne : ∀ᵐ x ∂(volume.restrict (Ioc 0 P)), x ≠ P :=
    ae_restrict_of_ae (by
      have : volume ({P} : Set ℝ) = 0 := Real.volume_singleton
      simpa [ae_iff] using this)
  filter_upwards [key, ae_restrict_mem measurableSet_Ioc, hne] with x hx hxI hxP
  exact hx ⟨hxI.1, lt_of_le_of_ne hxI.2 hxP⟩

end UnforcedLeray.Short.PartIIa.N01
