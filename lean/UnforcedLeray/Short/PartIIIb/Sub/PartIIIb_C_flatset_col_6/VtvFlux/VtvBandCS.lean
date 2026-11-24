import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFluxLemmas

/-!
# `VtvBandCS`: the slab integral of an `L²` band function is `O(√R)` (source 3511-3514)

The slab `fibK1 c s₁ s₂ (2R)` has volume `≤ M R`.  Pointwise `x ≤ (s/2) x² + 1/(2s)` for `s > 0`
(`s = √R`) gives `∫_K ‖h‖ ≤ (s/2) ∫_K ‖h‖² + vol(K)/(2s) ≤ C √R`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (fibK1 fibK1_mem fibK1_subset_Kc)

theorem vtvBandCS : VtvBandCS := by
  intro c s₁ s₂ h hh
  obtain ⟨N2, hN2⟩ : ∃ N : ℝ, N = ∫ p in Icc s₁ s₂ ×ˢ B0579.cell c, ‖h p‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = max (s₂ - s₁) 0 * (max c 0 * 4) := ⟨_, rfl⟩
  refine ⟨(N2 + M) / 2, fun R hR => ?_⟩
  have hR0 : 0 < R := by linarith
  obtain ⟨K, hK⟩ : ∃ K : Set (ℝ × (ℝ × ℝ)), K = fibK1 c s₁ s₂ (2 * R) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt R := ⟨_, rfl⟩
  rw [← hK, ← hs]
  have hs0 : 0 < s := by rw [hs]; exact Real.sqrt_pos.2 hR0
  have hs2 : s ^ 2 = R := by rw [hs]; exact Real.sq_sqrt hR0.le
  -- `K` sits in the band `[s₁,s₂] × cell`
  have hKsub : K ⊆ Icc s₁ s₂ ×ˢ B0579.cell c := by
    rw [hK]
    intro p hp
    obtain ⟨hs', hq, _⟩ := fibK1_mem.1 hp
    exact ⟨⟨hs'.1, hs'.2⟩, hq, mem_univ _⟩
  have hKsub' : K ⊆ Icc s₁ s₂ ×ˢ B0579.box c (2 * R) := by
    rw [hK]
    exact fibK1_subset_Kc c s₁ s₂ (2 * R)
  have hKc : IsCompact (Icc s₁ s₂ ×ˢ B0579.box c (2 * R)) :=
    isCompact_Icc.prod (B0579.isCompact_box c (2 * R))
  have hKfin : volume K ≠ ⊤ := ((measure_mono hKsub').trans_lt hKc.measure_lt_top).ne
  have hfinK : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hKfin
  -- volume of the slab
  have hvol : (volume K).toReal ≤ M * R := by
    rw [hK]
    simp only [fibK1, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Ico]
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal', ENNReal.toReal_ofReal',
      ENNReal.toReal_ofReal']
    have e2 : c / 2 - -(c / 2) = c := by ring
    have e3 : 2 * R - -(2 * R) = 4 * R := by ring
    rw [e2, e3, max_eq_left (by linarith : (0 : ℝ) ≤ 4 * R), hM]
    apply le_of_eq
    ring
  -- integrability on the slab
  have hKmem : MemLp h 2 (volume.restrict K) :=
    MemLp.mono_measure (Measure.restrict_mono hKsub le_rfl) hh
  have hsqK : Integrable (fun p => ‖h p‖ ^ 2) (volume.restrict K) :=
    (memLp_two_iff_integrable_sq_norm hKmem.1).1 hKmem
  have hnorm1 : IntegrableOn (fun p => ‖h p‖) K :=
    ((hKmem.integrable one_le_two : Integrable h (volume.restrict K))).norm
  have hsqB : IntegrableOn (fun p => ‖h p‖ ^ 2) (Icc s₁ s₂ ×ˢ B0579.cell c) :=
    (memLp_two_iff_integrable_sq_norm hh.1).1 hh
  have hN2le : ∫ p in K, ‖h p‖ ^ 2 ≤ N2 := by
    rw [hN2]
    exact setIntegral_mono_set hsqB (Filter.Eventually.of_forall fun p => sq_nonneg _)
      (Filter.Eventually.of_forall fun p hp => hKsub hp)
  -- pointwise AM-GM bound
  have key : ∀ x : ℝ, 0 ≤ x → x ≤ s / 2 * x ^ 2 + 1 / (2 * s) := by
    intro x hx
    have h2s : 0 < 2 * s := by positivity
    rw [← sub_nonneg]
    have e : s / 2 * x ^ 2 + 1 / (2 * s) - x = (s * x - 1) ^ 2 / (2 * s) := by
      field_simp
      ring
    rw [e]
    positivity
  have hI2 : Integrable (fun p => s / 2 * ‖h p‖ ^ 2 + 1 / (2 * s)) (volume.restrict K) :=
    (hsqK.const_mul (s / 2)).add (integrable_const _)
  have hmono : ∫ p in K, ‖h p‖ ≤ ∫ p in K, (s / 2 * ‖h p‖ ^ 2 + 1 / (2 * s)) :=
    integral_mono hnorm1 hI2 (fun p => key _ (norm_nonneg _))
  have hsplit : ∫ p in K, (s / 2 * ‖h p‖ ^ 2 + 1 / (2 * s)) =
      s / 2 * (∫ p in K, ‖h p‖ ^ 2) + volume.real K * (1 / (2 * s)) := by
    rw [integral_add (hsqK.const_mul (s / 2)) (integrable_const _), integral_const_mul,
      setIntegral_const, smul_eq_mul]
  have hvolR : volume.real K ≤ M * R := hvol
  have hA : s / 2 * (∫ p in K, ‖h p‖ ^ 2) ≤ s / 2 * N2 :=
    mul_le_mul_of_nonneg_left hN2le (by positivity)
  have hB : volume.real K * (1 / (2 * s)) ≤ M * R * (1 / (2 * s)) :=
    mul_le_mul_of_nonneg_right hvolR (by positivity)
  have hC : M * R * (1 / (2 * s)) = M * s / 2 := by
    rw [← hs2]
    field_simp
  refine ⟨hnorm1, ?_⟩
  linarith [hmono, hsplit, hA, hB, hC]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
