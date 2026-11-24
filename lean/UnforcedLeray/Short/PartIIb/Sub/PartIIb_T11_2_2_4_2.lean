import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T11_2_2_4

/-!
# Part II-b, leaf `PartII-b:T11/2/2/4/2` (`DualGWeightedInt`): decomposition

Source: `the November 2 reference manuscript`
lines 1923-1927 (Hölder step for the commutator, `b ∈ L^r`, `∂^α g ∈ L^{r'}` on `supp χ`).
Proved here: `dualGWeightedInt_of` from `SlabCompare` and `DualGMemLp`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- On a slab `[a,a'] × ℝ²` with `0 < a`, the measures `ageμ c 0` and `hMeas c r = ageμ c (r/2-5/2)`
are mutually bounded by finite constants (SP 1923-1927; the weight `σ^{r/2-5/2}` is bounded above
and below on `[a,a']`; `Axi.ageμ_eq_withDensity`, `Tasks/HilbertEnergy/SPeriodic.lean`). -/
def SlabCompare : Prop :=
  ∀ (c r a a' : ℝ), 0 < c → 0 < a → a ≤ a' →
    ∃ K K' : ℝ≥0∞, K ≠ ⊤ ∧ K' ≠ ⊤ ∧
      (Axi.ageμ c 0).restrict (Icc a a' ×ˢ (univ : Set (ℝ × ℝ))) ≤
        K • (hMeas c r).restrict (Icc a a' ×ˢ (univ : Set (ℝ × ℝ))) ∧
      (hMeas c r).restrict (Icc a a' ×ˢ (univ : Set (ℝ × ℝ))) ≤
        K' • (Axi.ageμ c 0).restrict (Icc a a' ×ˢ (univ : Set (ℝ × ℝ)))

/-- The jet `dualG χ H s` lies in `L^{r'}` of the slab (SP 1923-1927): `dualG = 1_{tsupport χ}(σ)
Σ_{n≤3}‖∂^n g‖`, `g(σ,·) = H(s-σ,·)`; `HeatSol.deriv_memLp` on `[s-a', s-a]`, transported by the
reflection `(σ,p) ↦ (s-σ,p)` (an isometry preserving `ageμ c 0`, which is `dσ ⊗ avgμ c`):
`‖iteratedFDeriv n g x‖ = ‖iteratedFDeriv n H (s-x.1,x.2)‖` by
`LinearIsometryEquiv.norm_iteratedFDeriv_comp_right` with `iteratedFDeriv_comp_add_right`. -/
def DualGMemLp : Prop :=
  ∀ (c r ν : ℝ) (H : Coord → ℝ) (s : ℝ) (χ : ℝ → ℝ) (a a' : ℝ),
    0 < c → 0 < ν → 1 < r → 0 < s → HeatSol c ν (r / (r - 1)) H → DFChi s χ →
    0 < a → a ≤ a' → a' < s → tsupport χ ⊆ Icc a a' →
    MemLp (dualG χ H s) (ENNReal.ofReal (r / (r - 1)))
      ((Axi.ageμ c 0).restrict (Icc a a' ×ˢ (univ : Set (ℝ × ℝ))))

/-- A compactly supported cutoff in `(0,s)` has support in some `[a,a'] ⊂ (0,s)`. -/
theorem exists_slab (s : ℝ) (hs0 : 0 < s) (χ : ℝ → ℝ) (hχ : DFChi s χ) :
    ∃ a a' : ℝ, 0 < a ∧ a ≤ a' ∧ a' < s ∧ tsupport χ ⊆ Icc a a' := by
  obtain ⟨_, hc, hs⟩ := hχ
  by_cases hne : (tsupport χ).Nonempty
  · obtain ⟨m, hm, hmin⟩ := hc.exists_isMinOn hne continuous_id.continuousOn
    obtain ⟨M, hM, hmax⟩ := hc.exists_isMaxOn hne continuous_id.continuousOn
    refine ⟨m, M, (hs hm).1, hmax hm, (hs hM).2, fun x hx => ⟨hmin hx, hmax hx⟩⟩
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    refine ⟨s / 2, s / 2, by positivity, le_rfl, by linarith, ?_⟩
    rw [hne]; exact Set.empty_subset _

theorem dualGWeightedInt_of (h1 : SlabCompare) (h2 : DualGMemLp) : DualGWeightedInt := by
  intro c r ν b H s χ hc hν hr hs hb hH hχ
  obtain ⟨a, a', ha, haa, has, hsub⟩ := exists_slab s hs χ hχ
  obtain ⟨K, K', hK, hK', hle, hle'⟩ := h1 c r a a' hc ha haa
  set S : Set Coord := Icc a a' ×ˢ (univ : Set (ℝ × ℝ)) with hS
  have hG : MemLp (dualG χ H s) (ENNReal.ofReal (r / (r - 1))) ((hMeas c r).restrict S) :=
    MemLp.of_measure_le_smul hK' hle' (h2 c r ν H s χ a a' hc hν hr hs hH hχ ha haa has hsub)
  have hb' : MemLp (fun x => ‖b x‖) (ENNReal.ofReal r) ((hMeas c r).restrict S) := by
    have : MemLp b (ENNReal.ofReal r) (hMeas c r) := ⟨hb.meas, hb.finite⟩
    exact (this.restrict S).norm
  haveI : ENNReal.HolderConjugate (ENNReal.ofReal r) (ENNReal.ofReal (r / (r - 1))) := by
    rw [ENNReal.holderConjugate_iff, ← ENNReal.ofReal_inv_of_pos (by linarith),
      ← ENNReal.ofReal_inv_of_pos (by apply div_pos <;> linarith), ← ENNReal.ofReal_add
        (by positivity) (by apply inv_nonneg.2; apply div_nonneg <;> linarith)]
    rw [← ENNReal.ofReal_one]
    congr 1
    have : r - 1 ≠ 0 := by linarith
    have : r ≠ 0 := by linarith
    field_simp
    ring
  have hint : Integrable (fun x => ‖b x‖ * dualG χ H s x) ((hMeas c r).restrict S) :=
    hb'.integrable_mul hG
  have hint2 : Integrable (fun x => ‖b x‖ * dualG χ H s x) ((Axi.ageμ c 0).restrict S) :=
    Integrable.of_measure_le_smul hK hle hint
  have hsupp : Function.support (fun x => ‖b x‖ * dualG χ H s x) ⊆ S := by
    intro x hx
    have : x.1 ∈ tsupport χ := by
      by_contra h
      apply hx
      simp [dualG, h]
    exact ⟨hsub this, mem_univ _⟩
  exact (integrableOn_iff_integrable_of_support_subset hsupp).1 hint2

end UnforcedLeray.Short.IIb
