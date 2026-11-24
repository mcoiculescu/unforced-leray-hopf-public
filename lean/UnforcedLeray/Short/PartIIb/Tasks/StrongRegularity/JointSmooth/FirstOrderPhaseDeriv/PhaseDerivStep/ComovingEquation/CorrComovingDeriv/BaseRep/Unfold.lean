import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth.FirstOrderPhaseDeriv.PhaseDerivStep.ComovingEquation.CorrComovingDeriv.BaseRep.Chart

/-!
# Unfolding the pairing of a periodized test against a continuous periodic field
(helper of `PartII-b:S3/1/1/2/1/2/1`)

Source of record: `the November 2 reference manuscript`,
lines 2519-2523.

`pairF_perT`: for a smooth test `K` with bounded support in space and phase and a jointly
continuous `P`-periodic field `u`, `P ⟪perT P K, u⟫ = ∫_ℝ ∫ K(t, y) · u(t, y) dy dt`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb.BaseRepSub

open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace UnforcedLeray.Cons.C03.Concrete

/-- Slice integrability against a continuous field. -/
theorem integrable_slice_dotL {Φ : ℝ × Space → CVec3} (hΦc : Continuous Φ) {R : ℝ}
    (hR : ∀ τ y, R < ‖y‖ → Φ (τ, y) = 0) {u : ℝ × Space → CVec3} (hu : Continuous u) (t : ℝ) :
    Integrable (fun y => dotL (Φ (t, y)) (u (t, y))) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact (dotL.continuous.comp (hΦc.comp (Continuous.prodMk_right t))).clm_apply
      (hu.comp (Continuous.prodMk_right t))
  · refine HasCompactSupport.intro (isCompact_closedBall (0 : Space) R) fun y hy => ?_
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hy
    simp [hR t y hy]

/-- Continuity of the slice pairing in the phase. -/
theorem continuous_slice_dotL {Φ : ℝ × Space → CVec3} (hΦc : Continuous Φ) {R : ℝ}
    (hR : ∀ τ y, R < ‖y‖ → Φ (τ, y) = 0) {u : ℝ × Space → CVec3} (hu : Continuous u) :
    Continuous fun t => ∫ y, dotL (Φ (t, y)) (u (t, y)) := by
  have heq : (fun t => ∫ y, dotL (Φ (t, y)) (u (t, y))) =
      fun t => ∫ y in Metric.closedBall (0 : Space) R, dotL (Φ (t, y)) (u (t, y)) := by
    funext t
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro y hy
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hy
    simp [hR t y hy]
  rw [heq]
  have hc : Continuous (Function.uncurry fun (t : ℝ) (y : Space) => dotL (Φ (t, y)) (u (t, y))) :=
    (dotL.continuous.comp hΦc).clm_apply hu
  exact continuous_parametric_integral_of_continuous hc (isCompact_closedBall _ _)

/-- Integrability of the slice pairing of a test with bounded phase support. -/
theorem integrable_slice_dotL_time {K : ℝ × Space → CVec3} (hK0 : IsPhaseTest 0 K) {A B : ℝ}
    (hK : TimeSupp A B K) {u : ℝ × Space → CVec3} (hu : Continuous u) :
    Integrable fun t => ∫ y, dotL (K (t, y)) (u (t, y)) := by
  obtain ⟨R, hR⟩ := hK0.bounded_support
  refine Continuous.integrable_of_hasCompactSupport
    (continuous_slice_dotL hK0.smooth.continuous hR hu) ?_
  refine HasCompactSupport.intro (isCompact_Icc (a := A) (b := B)) fun t ht => ?_
  simp [hK t _ ht]

theorem periodic_int_mul {u : ℝ × Space → CVec3} {P : ℝ}
    (hper : ∀ τ y, u (τ + P, y) = u (τ, y)) (k : ℤ) (τ : ℝ) (y : Space) :
    u (τ + k * P, y) = u (τ, y) := by
  have h : Function.Periodic (fun τ : ℝ => u (τ, y)) P := fun τ => hper τ y
  exact (h.int_mul k) τ

/-- **Unfolding.** `P ⟪perT P K, u⟫ = ∫_ℝ ∫ K(t, y) · u(t, y) dy dt` for `P`-periodic continuous
`u`. -/
theorem pairF_perT {P : ℝ} (hP0 : 0 < P) {K : ℝ × Space → CVec3} (hK0 : IsPhaseTest 0 K)
    {A B : ℝ} (hAB : A ≤ B) (hK : TimeSupp A B K) {u : ℝ × Space → CVec3} (hu : Continuous u)
    (hper : ∀ τ y, u (τ + P, y) = u (τ, y)) :
    pairF P (perT P K) u = P⁻¹ • ∫ t, ∫ y, dotL (K (t, y)) (u (t, y)) := by
  obtain ⟨R, hR⟩ := hK0.bounded_support
  set h : ℝ → ℂ := fun t => ∫ y, dotL (K (t, y)) (u (t, y)) with hh
  have hHint : Integrable h := integrable_slice_dotL_time hK0 hK hu
  unfold pairF phaseInt
  congr 1
  set m : ℤ := ⌊A / P⌋ - 1 with hm
  set N : ℕ := (⌈B / P⌉ - m).toNat with hN
  set s : Finset ℤ := (Finset.range N).image (fun i : ℕ => m + i) with hs
  have hsmem : ∀ t ∈ Ioc (0 : ℝ) P, ∀ k : ℤ, t + k * P ∈ Icc A B → k ∈ s := by
    intro t ht k hk
    have hkm : m ≤ k := by
      have h1 : A / P - 1 ≤ k := by
        rw [sub_le_iff_le_add, div_le_iff₀ hP0]; linarith [ht.2, hk.1]
      have h2 : (⌊A / P⌋ : ℝ) ≤ A / P := Int.floor_le _
      have h3 : ((m : ℤ) : ℝ) ≤ k := by rw [hm]; push_cast; linarith
      exact_mod_cast h3
    have hkM : k < ⌈B / P⌉ := by
      have h1 : (k : ℝ) < B / P := by
        rw [lt_div_iff₀ hP0]; linarith [ht.1, hk.2]
      have h2 : B / P ≤ (⌈B / P⌉ : ℝ) := Int.le_ceil _
      exact_mod_cast h1.trans_le h2
    rw [hs, Finset.mem_image]
    refine ⟨(k - m).toNat, ?_, ?_⟩
    · rw [Finset.mem_range, hN]
      exact (Int.toNat_lt_toNat (by omega)).mpr (by omega)
    · rw [Int.toNat_of_nonneg (by omega)]; ring
  have hA : ∀ t ∈ Ioc (0 : ℝ) P,
      ∫ y, dotL (perT P K (t, y)) (u (t, y)) = ∑ k ∈ s, h (t + k * P) := by
    intro t ht
    have hp : ∀ y, dotL (perT P K (t, y)) (u (t, y)) =
        ∑ k ∈ s, dotL (K (t + k * P, y)) (u (t + k * P, y)) := by
      intro y
      rw [perT_eq_sum hK s (t, y) (hsmem t ht), map_sum, ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      dsimp only
      rw [periodic_int_mul hper k t y]
    simp_rw [hp]
    rw [integral_finsetSum _ fun k _ => integrable_slice_dotL hK0.smooth.continuous hR hu _]
  change ∫ t in Ioc (0 : ℝ) P, (fun t => ∫ y, dotL (perT P K (t, y)) (u (t, y))) t = ∫ t, h t
  rw [setIntegral_congr_fun measurableSet_Ioc hA,
    integral_finsetSum _ fun k _ => (hHint.comp_add_right _).integrableOn,
    Finset.sum_image (fun i _ j _ hij => by simpa using hij)]
  have hB : ∀ i : ℕ, ∫ t in Ioc (0 : ℝ) P, h (t + ((m + i : ℤ) : ℝ) * P) =
      ∫ t in ((m + i : ℤ) : ℝ) * P..((m + ((i + 1 : ℕ) : ℤ) : ℤ) : ℝ) * P, h t := by
    intro i
    rw [← intervalIntegral.integral_of_le hP0.le, intervalIntegral.integral_comp_add_right]
    congr 1 <;> push_cast <;> ring
  rw [Finset.sum_congr rfl fun i _ => hB i,
    intervalIntegral.sum_integral_adjacent_intervals
      (a := fun i : ℕ => ((m + (i : ℤ) : ℤ) : ℝ) * P) fun k _ => hHint.intervalIntegrable]
  refine intervalIntegral.integral_eq_integral_of_support_subset ?_
  intro t ht
  have htAB : t ∈ Icc A B := by
    by_contra hc
    apply ht
    simp only [hh]
    have : ∀ y, K (t, y) = 0 := fun y => hK t y hc
    simp [this]
  constructor
  · have h2 : (⌊A / P⌋ : ℝ) ≤ A / P := Int.floor_le _
    have h3 : (⌊A / P⌋ : ℝ) * P ≤ A := by rwa [le_div_iff₀ hP0] at h2
    simp only [Nat.cast_zero, add_zero, hm]
    push_cast
    nlinarith [htAB.1]
  · have hNge : ⌈B / P⌉ ≤ m + (N : ℤ) := by rw [hN]; omega
    have h2 : B / P ≤ (⌈B / P⌉ : ℝ) := Int.le_ceil _
    have h3 : B ≤ (⌈B / P⌉ : ℝ) * P := by rwa [div_le_iff₀ hP0] at h2
    have h4 : (⌈B / P⌉ : ℝ) ≤ ((m + (N : ℤ) : ℤ) : ℝ) := by exact_mod_cast hNge
    calc t ≤ B := htAB.2
      _ ≤ (⌈B / P⌉ : ℝ) * P := h3
      _ ≤ ((m + (N : ℤ) : ℤ) : ℝ) * P := by gcongr

end UnforcedLeray.Short.IIb.BaseRepSub

end
