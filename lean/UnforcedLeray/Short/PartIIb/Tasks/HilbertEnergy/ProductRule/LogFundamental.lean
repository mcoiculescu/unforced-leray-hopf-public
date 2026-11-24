import UnforcedLeray.Short.PartIIb.Sub.T15_2
import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy.ProductRule.PeriodizeCellTest

set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

/-- **Leaf `PartII-b:T15/2/6`** (periodic fundamental lemma of the calculus of variations).
Source: `the November 2 reference manuscript` lines 1975-1979. -/
theorem logFundamental : LogFundamental := by
  intro c F hc _hFm hFint hzero
  have hpos : (0 : ℝ) < c⁻¹ := inv_pos.mpr hc
  have hne0 : ENNReal.ofReal c⁻¹ ≠ 0 := (ENNReal.ofReal_pos.mpr hpos).ne'
  have hneTop : ENNReal.ofReal c⁻¹ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hRealNe : (ENNReal.ofReal c⁻¹).toReal ≠ 0 := by
    rw [ENNReal.toReal_ofReal hpos.le]
    exact hpos.ne'
  -- `S` is the cell slab `ℝ × (q ∈ [-c/2, c/2)) × ℝ`, `U` its open interior.
  set S : Set Coord := univ ×ˢ (Ico (-c / 2) (c / 2) ×ˢ univ) with hSdef
  set U : Set Coord := univ ×ˢ (Ioo (-c / 2) (c / 2) ×ˢ univ) with hUdef
  have hUS : U ⊆ S := prod_mono Subset.rfl (prod_mono Ioo_subset_Ico_self Subset.rfl)
  have hSm : MeasurableSet S :=
    MeasurableSet.univ.prod (measurableSet_Ico.prod MeasurableSet.univ)
  have hUo : IsOpen U := isOpen_univ.prod (isOpen_Ioo.prod isOpen_univ)
  -- Restriction of a product measure to a product set.
  have hkey : ∀ A : Set (ℝ × ℝ),
      (volume : Measure ℝ).prod (volume.restrict A)
        = (volume : Measure Coord).restrict (univ ×ˢ A) := by
    intro A
    rw [← Measure.restrict_univ (μ := (volume : Measure ℝ)), Measure.prod_restrict]
    rfl
  -- The chart measure is a constant multiple of Lebesgue measure restricted to the slab.
  have hlog : logMeas c = ENNReal.ofReal c⁻¹ • (volume : Measure Coord).restrict S := by
    rw [logMeas, UnforcedLeray.Cyl.avgμ, UnforcedLeray.Cyl.cellμ, Measure.prod_smul_right, hkey]
    rfl
  -- Local integrability of `F` on the open slab `U` for Lebesgue measure.
  have hLIO : LocallyIntegrableOn F U volume := by
    intro x hx
    have hxq : x.2.1 ∈ Ioo (-c / 2) (c / 2) := hx.2.1
    unfold IntegrableAtFilter
    set s : Set Coord :=
      Ioo (x.1 - 1) (x.1 + 1) ×ˢ (Ioo (-c / 2) (c / 2) ×ˢ Ioo (x.2.2 - 1) (x.2.2 + 1)) with hsdef
    have hso : IsOpen s := isOpen_Ioo.prod (isOpen_Ioo.prod isOpen_Ioo)
    have hxs : x ∈ s :=
      ⟨⟨by linarith, by linarith⟩, hxq, ⟨by linarith, by linarith⟩⟩
    have hsU : s ⊆ U := fun y hy => ⟨mem_univ _, hy.2.1, mem_univ _⟩
    refine ⟨s, mem_nhdsWithin_of_mem_nhds (hso.mem_nhds hxs), ?_⟩
    have hsb : s ⊆ {y : Coord | |y.1| ≤ |x.1| + 1 ∧ |y.2.2| ≤ |x.2.2| + 1} := by
      intro y hy
      have h1 : x.1 - 1 < y.1 ∧ y.1 < x.1 + 1 := hy.1
      have h2 : x.2.2 - 1 < y.2.2 ∧ y.2.2 < x.2.2 + 1 := hy.2.2
      exact ⟨abs_le.mpr ⟨by linarith [neg_abs_le x.1], by linarith [le_abs_self x.1]⟩,
        abs_le.mpr ⟨by linarith [neg_abs_le x.2.2], by linarith [le_abs_self x.2.2]⟩⟩
    have hint : IntegrableOn F s (logMeas c) :=
      (hFint (|x.1| + 1) (|x.2.2| + 1)).mono_set hsb
    unfold IntegrableOn at hint ⊢
    rw [hlog, Measure.restrict_smul, integrable_smul_measure hne0 hneTop] at hint
    rw [Measure.restrict_restrict hso.measurableSet, inter_eq_left.mpr (hsU.trans hUS)] at hint
    exact hint
  -- Test functions supported in `U` integrate `F` to zero against Lebesgue measure.
  have hTest : ∀ g : Coord → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ U →
      ∫ x, g x • F x ∂(volume : Measure Coord) = 0 := by
    intro g hg hgc hgU
    obtain ⟨Φ, hΦ, hΦeq⟩ := periodizeCellTest c g hc hg hgc hgU
    have h0 := hzero Φ hΦ
    rw [hlog, integral_smul_measure] at h0
    have h1a : ∫ x in S, F x * (Φ x : ℂ) = ∫ x in S, F x * (g x : ℂ) :=
      setIntegral_congr_fun hSm (fun x hx => by rw [hΦeq x hx.2.1])
    have h1b : ∫ x in S, F x * (g x : ℂ) = ∫ x, F x * (g x : ℂ) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hxS => by
        have hxU : x ∉ U := fun hxU => hxS (hUS hxU)
        have hg0 : g x = 0 := by
          by_contra hne
          exact hxU (hgU (subset_tsupport g (Function.mem_support.mpr hne)))
        simp [hg0])
    rw [h1a, h1b] at h0
    have h2 : ∫ x, F x * (g x : ℂ) = 0 :=
      (smul_eq_zero.mp h0).resolve_left hRealNe
    have hfun : (fun x => g x • F x) = fun x => F x * (g x : ℂ) :=
      funext fun x => by rw [Complex.real_smul, mul_comm]
    rw [hfun]
    exact h2
  -- Fundamental lemma on the open slab.
  have hae : ∀ᵐ x ∂(volume : Measure Coord), x ∈ U → F x = 0 :=
    hUo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hLIO hTest
  -- The hyperplane `q = -c/2` is Lebesgue-null.
  have hnull : ∀ᵐ x ∂(volume : Measure Coord), x.2.1 ≠ -c / 2 := by
    rw [ae_iff]
    apply measure_mono_null (t := univ ×ˢ ({-c / 2} ×ˢ (univ : Set ℝ)))
    · intro a ha
      simp only [Set.mem_ofPred_eq, ne_eq, not_not] at ha
      exact ⟨mem_univ _, ha, mem_univ _⟩
    · simp [Measure.volume_eq_prod]
  have hS_ae : ∀ᵐ x ∂(volume : Measure Coord), x ∈ S → F x = 0 := by
    filter_upwards [hae, hnull] with x hx1 hx2 hxS
    apply hx1
    exact ⟨mem_univ _, ⟨lt_of_le_of_ne hxS.2.1.1 (Ne.symm hx2), hxS.2.1.2⟩, mem_univ _⟩
  show ∀ᵐ x ∂(logMeas c), F x = 0
  rw [hlog]
  exact Measure.ae_smul_measure ((ae_restrict_iff' hSm).mpr hS_ae) _

end UnforcedLeray.Short.IIb
