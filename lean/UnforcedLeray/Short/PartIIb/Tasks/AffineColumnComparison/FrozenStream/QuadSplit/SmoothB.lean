import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.QuadSplit.XGInt

/-!
# Part II-b, task `PartII-b:G4/2/2/3/2`: `smoothB`

Source of record: `the November 2 reference manuscript`, lines 2349-2352.

Route: `B r = ∫_r^∞ s⁻¹ q` splits locally as `B r = B(2r) + ∫_r^{2r} s⁻¹ q` (for `0 < r`),
so `B` has derivative `-r⁻¹ q r` on `(0,∞)` (`integral_hasDerivAt_left`), which is smooth there.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Blueprint

/-- Splitting the tail integral at `c > 0` for `0 < u ≤ c`. -/
private lemma smoothB_split (q : Planar.Profile) (hqG : Planar.MemXG q) (u c : ℝ) (hu : 0 < u)
    (huc : u ≤ c) :
    ∫ s in Ioi u, (s : ℂ)⁻¹ * q s
      = (∫ s in Ioi c, (s : ℂ)⁻¹ * q s) + ∫ s in u..c, (s : ℂ)⁻¹ * q s := by
  have hIu : IntegrableOn (fun s : ℝ => (s : ℂ)⁻¹ * q s) (Ioi u) := (xGInt q hqG).2 u hu
  have hc : 0 < c := lt_of_lt_of_le hu huc
  have hIc : IntegrableOn (fun s : ℝ => (s : ℂ)⁻¹ * q s) (Ioi c) := (xGInt q hqG).2 c hc
  have hI1 : IntegrableOn (fun s : ℝ => (s : ℂ)⁻¹ * q s) (Ioc u c) :=
    hIu.mono_set Ioc_subset_Ioi_self
  have hdisj : Disjoint (Ioc u c) (Ioi c) :=
    Set.disjoint_left.2 (fun x hx hx' => (lt_irrefl c) (lt_of_lt_of_le hx' hx.2))
  rw [← Set.Ioc_union_Ioi_eq_Ioi huc, setIntegral_union hdisj measurableSet_Ioi hI1 hIc,
    intervalIntegral.integral_of_le huc]
  exact add_comm _ _

theorem smoothB : UnforcedLeray.Short.IIb.SmoothB := by
  intro q hqG hq
  have hcont : ContinuousOn q (Ioi 0) := hq.continuousOn
  have hfc : ContinuousOn (fun s : ℝ => (s : ℂ)⁻¹ * q s) (Ioi 0) :=
    ContinuousOn.mul (ContinuousOn.inv₀ Complex.continuous_ofReal.continuousOn
      (fun s hs => Complex.ofReal_ne_zero.mpr (Set.mem_Ioi.mp hs).ne')) hcont
  have hderiv : ∀ r : ℝ, 0 < r →
      HasDerivAt (fun u : ℝ => ∫ s in Ioi u, (s : ℂ)⁻¹ * q s) (-((r : ℂ)⁻¹ * q r)) r := by
    intro r hr
    have hrc : r ≤ 2 * r := by linarith
    have hF : (fun u : ℝ => ∫ s in Ioi u, (s : ℂ)⁻¹ * q s) =ᶠ[𝓝 r]
        fun u : ℝ => (∫ s in Ioi (2 * r), (s : ℂ)⁻¹ * q s)
          + ∫ s in u..(2 * r), (s : ℂ)⁻¹ * q s := by
      filter_upwards [Ioo_mem_nhds hr (show r < 2 * r by linarith)] with u hu
      exact smoothB_split q hqG u (2 * r) hu.1 hu.2.le
    have hIR : IntervalIntegrable (fun s : ℝ => (s : ℂ)⁻¹ * q s) volume r (2 * r) := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hrc]
      exact ((xGInt q hqG).2 r hr).mono_set Ioc_subset_Ioi_self
    have hmeas : StronglyMeasurableAtFilter (fun s : ℝ => (s : ℂ)⁻¹ * q s) (𝓝 r) :=
      hfc.stronglyMeasurableAtFilter isOpen_Ioi r hr
    have hcontAt : ContinuousAt (fun s : ℝ => (s : ℂ)⁻¹ * q s) r :=
      hfc.continuousAt (Ioi_mem_nhds hr)
    have hd := (intervalIntegral.integral_hasDerivAt_left hIR hmeas hcontAt).const_add
      (∫ s in Ioi (2 * r), (s : ℂ)⁻¹ * q s)
    exact hd.congr_of_eventuallyEq hF
  have hDiff : DifferentiableOn ℝ (fun u : ℝ => ∫ s in Ioi u, (s : ℂ)⁻¹ * q s) (Ioi 0) :=
    fun r hr => (hderiv r hr).differentiableAt.differentiableWithinAt
  have hdereq : EqOn (deriv (fun u : ℝ => ∫ s in Ioi u, (s : ℂ)⁻¹ * q s))
      (fun r : ℝ => -((r : ℂ)⁻¹ * q r)) (Ioi 0) :=
    fun r hr => (hderiv r hr).deriv
  have hsmooth : ContDiffOn ℝ ∞ (fun r : ℝ => -((r : ℂ)⁻¹ * q r)) (Ioi 0) := by
    refine ContDiffOn.neg ?_
    refine ContDiffOn.mul ?_ hq
    exact ContDiffOn.inv Complex.ofRealCLM.contDiff.contDiffOn
      (fun r hr => Complex.ofReal_ne_zero.mpr (Set.mem_Ioi.mp hr).ne')
  rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi]
  exact ⟨hDiff, hsmooth.congr hdereq⟩

end UnforcedLeray.Short.IIb

end
