import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T12_1_3_1_5_3
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.HelmholtzUnique.MollApprox.CylLocInt

/-!


Source: `the November 2 reference manuscript` lines 1670, 1923-1926.
Route: a bounded `g` (continuous, `c`-periodic, vanishing in the slab `|η| > L`), the cut-off
`K`-indicator of `D_i` (integrable by local integrability on a compact box), the convolution
integrability lemma `Integrable.convolution_integrand` in the variables `(z, y) ↦ (ρ(y), D(z-y))`,
then the reduction from `avgμ c ⊗ volume` to `volume ⊗ volume` restricted to `cell × univ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Complex
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

namespace CylSwapInt1Proof

/-- A continuous `c`-periodic function vanishing in a slab is bounded on the plane. -/
theorem g_bdd {c L : ℝ} (hc : 0 < c) {g : ℝ × ℝ → ℝ} (hcont : Continuous g)
    (hper : UnforcedLeray.Cyl.IsPeriodic c g) (hL : ∀ z : ℝ × ℝ, L < |z.2| → g z = 0) :
    ∃ C : ℝ, ∀ z : ℝ × ℝ, ‖g z‖ ≤ C := by
  have hK : IsCompact (Icc (0 : ℝ) c ×ˢ Icc (-|L|) |L|) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C 0, fun z => ?_⟩
  by_cases hz : |z.2| ≤ |L|
  · have hp : Function.Periodic (fun q : ℝ => g (q, z.2)) c := fun q => hper (q, z.2)
    obtain ⟨y, hy, hgy⟩ := hp.exists_mem_Ico₀ hc z.1
    have hmem : (y, z.2) ∈ Icc (0 : ℝ) c ×ˢ Icc (-|L|) |L| :=
      ⟨⟨hy.1, hy.2.le⟩, abs_le.mp hz⟩
    have hgy' : g (z.1, z.2) = g (y, z.2) := hgy
    have hb := hC (y, z.2) hmem
    show ‖g (z.1, z.2)‖ ≤ max C 0
    rw [hgy']
    exact le_trans hb (le_max_left _ _)
  · have h0 : g z = 0 := hL z (lt_of_le_of_lt (le_abs_self L) (not_le.mp hz))
    rw [h0, norm_zero]
    exact le_max_right _ _

theorem cylSwapInt1 : UnforcedLeray.Short.IIb.CylSwapInt1 := by
  intro c r hc hr D hD ρ g hg i
  obtain ⟨hgcont, hgper, L, hL⟩ := hg
  have hloc : LocallyIntegrable D volume := cylLocInt c r hc hr D hD
  obtain ⟨Cg, hCg⟩ := g_bdd hc hgcont hgper hL
  set R : ℝ := ρ.rOut with hR
  set K : Set (ℝ × ℝ) :=
    Icc (-(c / 2 + R)) (c / 2 + R) ×ˢ Icc (-(|L| + R)) (|L| + R) with hKdef
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  set Gc : ℝ × ℝ → ℂ := K.indicator (fun w => D w i) with hGc
  -- integrability of the cut-off component
  have hGint : Integrable Gc volume := by
    rw [hGc, integrable_indicator_iff hK.measurableSet]
    have h1 : IntegrableOn D K volume := hloc.integrableOn_isCompact hK
    exact ContinuousLinearMap.integrable_comp (EuclideanSpace.proj (𝕜 := ℂ) i : CMerid →L[ℂ] ℂ) h1
  -- the convolution integrability `(z, y) ↦ ρ(y) Gc(z - y)`
  have hfℂ : Integrable (fun y : ℝ × ℝ => ((ρ.normed volume y : ℝ) : ℂ)) volume :=
    (ρ.integrable_normed (μ := volume)).ofReal
  have hΦ : Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      ((ρ.normed volume p.2 : ℝ) : ℂ) * Gc (p.1 - p.2)) (volume.prod volume) :=
    Integrable.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hfℂ hGint
  -- the full integrand on `volume ⊗ volume`, with the bounded factor `g(z)`
  have hHint0 : Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      (((ρ.normed volume p.2 : ℝ) : ℂ) * Gc (p.1 - p.2)) * ((g p.1 : ℝ) : ℂ))
      (volume.prod volume) := by
    refine hΦ.mul_bdd (c := Cg) ?_ ?_
    · exact (Complex.continuous_ofReal.comp (hgcont.comp continuous_fst)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun p => by
        show ‖((g p.1 : ℝ) : ℂ)‖ ≤ Cg
        rw [Complex.norm_real]
        exact hCg p.1
  -- measure bookkeeping: `avgμ c ⊗ volume = c⁻¹ • (volume ⊗ volume)|_{cell × univ}`
  have hμT : (UnforcedLeray.Cyl.avgμ c).prod (volume : Measure (ℝ × ℝ))
      = ENNReal.ofReal c⁻¹ • (volume.prod volume).restrict (UnforcedLeray.Cyl.cell c ×ˢ univ) := by
    unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
    rw [Measure.prod_smul_left, ← Measure.prod_restrict, Measure.restrict_univ]
  have hHint : Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      (((ρ.normed volume p.2 : ℝ) : ℂ) * Gc (p.1 - p.2)) * ((g p.1 : ℝ) : ℂ))
      ((UnforcedLeray.Cyl.avgμ c).prod (volume : Measure (ℝ × ℝ))) := by
    rw [hμT]
    exact (hHint0.restrict).smul_measure ENNReal.ofReal_ne_top
  refine hHint.congr ?_
  -- the two integrands agree on `cell × univ`
  have hcellM : MeasurableSet (UnforcedLeray.Cyl.cell c) := by
    unfold UnforcedLeray.Cyl.cell
    exact measurableSet_Ico.prod MeasurableSet.univ
  have hcpos : ENNReal.ofReal c⁻¹ ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact inv_pos.mpr hc
  rw [hμT, Measure.ae_ennreal_smul_measure_eq hcpos, Filter.EventuallyEq,
    ae_restrict_iff' (hcellM.prod MeasurableSet.univ)]
  refine Filter.Eventually.of_forall fun p hp => ?_
  have hp1 : p.1.1 ∈ Ico (-c / 2) (c / 2) := by
    have h := hp.1
    unfold UnforcedLeray.Cyl.cell at h
    exact h.1
  by_cases hρ : ρ.normed volume p.2 = 0
  · simp [hρ]
  by_cases hg0 : g p.1 = 0
  · simp [hg0]
  -- `p.2` lies in the support ball, and `|p.1.2| ≤ |L|` because `g p.1 ≠ 0`
  have hball : p.2 ∈ Metric.ball (0 : ℝ × ℝ) R := by
    have hs : p.2 ∈ Function.support (ρ.normed volume) := hρ
    rw [ContDiffBump.support_normed_eq] at hs
    exact hs
  rw [mem_ball_zero_iff] at hball
  have hb1 : |p.2.1| < R := by
    have := norm_fst_le p.2
    have h2 : ‖p.2.1‖ < R := lt_of_le_of_lt this hball
    simpa [Real.norm_eq_abs] using h2
  have hb2 : |p.2.2| < R := by
    have := norm_snd_le p.2
    have h2 : ‖p.2.2‖ < R := lt_of_le_of_lt this hball
    simpa [Real.norm_eq_abs] using h2
  have hLs : |p.1.2| ≤ |L| := by
    by_contra hcon
    exact hg0 (hL p.1 (lt_of_le_of_lt (le_abs_self L) (not_le.mp hcon)))
  have hb1' := abs_lt.mp hb1
  have hb2' := abs_lt.mp hb2
  have hL' := abs_le.mp hLs
  have hmem : p.1 - p.2 ∈ K := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · simp only [Prod.fst_sub]; linarith [hp1.1, hp1.2, hb1'.1, hb1'.2]
    · simp only [Prod.fst_sub]; linarith [hp1.1, hp1.2, hb1'.1, hb1'.2]
    · simp only [Prod.snd_sub]; linarith [hL'.1, hL'.2, hb2'.1, hb2'.2, le_abs_self L]
    · simp only [Prod.snd_sub]; linarith [hL'.1, hL'.2, hb2'.1, hb2'.2, le_abs_self L]
  simp only [hGc]
  rw [Set.indicator_of_mem hmem]

end CylSwapInt1Proof

end UnforcedLeray.Short.IIb
