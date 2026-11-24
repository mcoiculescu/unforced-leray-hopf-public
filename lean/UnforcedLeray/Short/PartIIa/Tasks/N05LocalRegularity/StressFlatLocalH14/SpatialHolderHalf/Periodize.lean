import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.StressFlatLocalH14.SpatialHolderHalf.Shift

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff ComplexConjugate InnerProductSpace

namespace UnforcedLeray.Short.PartIIa
open UnforcedLeray.B0220 N05_4Aux N05_4_1Aux

namespace SHH

theorem exists_delta {c : ℝ} (hc : 0 < c) {ψ : Profile → ℝ} (hcs : HasCompactSupport ψ)
    (hU : tsupport ψ ⊆ Ioi 0 ×ˢ Ioo 0 c ×ˢ univ) :
    ∃ δ : ℝ, 0 < δ ∧ 2 * δ ≤ c ∧ ∀ p ∈ tsupport ψ, δ ≤ p.2.1 ∧ p.2.1 ≤ c - δ := by
  by_cases ne : (tsupport ψ).Nonempty
  · have hK : IsCompact (tsupport ψ) := hcs
    obtain ⟨x, hx, hxmin⟩ := hK.exists_isMinOn ne (f := fun p : Profile => p.2.1)
      (by fun_prop : Continuous fun p : Profile => p.2.1).continuousOn
    obtain ⟨y, hy, hymax⟩ := hK.exists_isMaxOn ne (f := fun p : Profile => p.2.1)
      (by fun_prop : Continuous fun p : Profile => p.2.1).continuousOn
    have hx0 : 0 < x.2.1 := (hU hx).2.1.1
    have hyc : y.2.1 < c := (hU hy).2.1.2
    have hxy := hxmin hy
    simp only [mem_setOf_eq] at hxy
    refine ⟨min x.2.1 (c - y.2.1), lt_min hx0 (by linarith), ?_, fun p hp => ⟨?_, ?_⟩⟩
    · have h1 := min_le_left x.2.1 (c - y.2.1)
      have h2 := min_le_right x.2.1 (c - y.2.1)
      linarith
    · exact (min_le_left _ _).trans (hxmin hp)
    · have := hymax hp
      have h2 := min_le_right x.2.1 (c - y.2.1)
      simp only [mem_setOf_eq] at this
      linarith
  · exact ⟨c / 2, by positivity, by linarith, fun p hp => (ne ⟨p, hp⟩).elim⟩

/-- `q` reduced to `[0, c)`. -/
def redq (c q : ℝ) : ℝ := q - c * ⌊q / c⌋

theorem redq_add_c {c : ℝ} (hc : 0 < c) (q : ℝ) : redq c (q + c) = redq c q := by
  unfold redq
  have : (q + c) / c = q / c + 1 := by field_simp
  rw [this, Int.floor_add_one]
  push_cast; ring

/-- the periodic extension -/
def perExt (c : ℝ) (ψ : Profile → ℝ) (p : Profile) : ℝ := ψ (p.1, redq c p.2.1, p.2.2)

theorem perExt_periodic {c : ℝ} (hc : 0 < c) (ψ : Profile → ℝ) : QPeriodic c (perExt c ψ) := by
  intro p
  simp only [perExt, redq_add_c hc]

theorem perExt_eq_on {c : ℝ} (hc : 0 < c) {ψ : Profile → ℝ} {δ : ℝ} (hδ : 0 < δ) (h2δ : 2 * δ ≤ c)
    (hδs : ∀ p ∈ tsupport ψ, δ ≤ p.2.1 ∧ p.2.1 ≤ c - δ) (k : ℤ) (p : Profile)
    (hq1 : k * c - δ < p.2.1) (hq2 : p.2.1 < (k + 1) * c) :
    perExt c ψ p = ψ (p.1, p.2.1 - k * c, p.2.2) := by
  unfold perExt redq
  by_cases hk : (k : ℝ) * c ≤ p.2.1
  · have : ⌊p.2.1 / c⌋ = k := by
      rw [Int.floor_eq_iff]
      constructor
      · rw [le_div_iff₀ hc]; exact hk
      · rw [div_lt_iff₀ hc]; exact hq2
    rw [this]; congr 2; ring
  · push_neg at hk
    have : ⌊p.2.1 / c⌋ = k - 1 := by
      rw [Int.floor_eq_iff]
      constructor
      · rw [le_div_iff₀ hc]; push_cast; nlinarith
      · rw [div_lt_iff₀ hc]; push_cast; linarith
    rw [this]
    have h1 : ψ (p.1, p.2.1 - c * ((k - 1 : ℤ) : ℝ), p.2.2) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hm
      have := (hδs _ hm).2
      simp only at this
      push_cast at this
      linarith
    have h2 : ψ (p.1, p.2.1 - k * c, p.2.2) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hm
      have := (hδs _ hm).1
      simp only at this
      linarith
    rw [h1, h2]

theorem perExt_contDiff {c : ℝ} (hc : 0 < c) {ψ : Profile → ℝ} (hψ : ContDiff ℝ ∞ ψ) {δ : ℝ}
    (hδ : 0 < δ) (h2δ : 2 * δ ≤ c) (hδs : ∀ p ∈ tsupport ψ, δ ≤ p.2.1 ∧ p.2.1 ≤ c - δ) :
    ContDiff ℝ ∞ (perExt c ψ) := by
  rw [contDiff_iff_contDiffAt]
  intro p0
  set k : ℤ := ⌊p0.2.1 / c⌋ with hk
  have hk1 : (k : ℝ) ≤ p0.2.1 / c := Int.floor_le _
  have hk2 : p0.2.1 / c < k + 1 := Int.lt_floor_add_one _
  rw [le_div_iff₀ hc] at hk1
  rw [div_lt_iff₀ hc] at hk2
  have hopen : IsOpen {p : Profile | p.2.1 ∈ Ioo (k * c - δ) ((k + 1) * c)} :=
    isOpen_Ioo.preimage (by fun_prop)
  have hmem : p0 ∈ {p : Profile | p.2.1 ∈ Ioo (k * c - δ) ((k + 1) * c)} :=
    ⟨by linarith, by linarith⟩
  have hev : perExt c ψ =ᶠ[𝓝 p0] fun p : Profile => ψ (p.1, p.2.1 - k * c, p.2.2) :=
    Filter.eventuallyEq_of_mem (hopen.mem_nhds hmem) fun p hp =>
      perExt_eq_on hc hδ h2δ hδs k p hp.1 hp.2
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  exact (hψ.contDiffAt (x := (p0.1, p0.2.1 - k * c, p0.2.2))).comp p0
    (by fun_prop : ContDiff ℝ ∞ fun p : Profile => (p.1, p.2.1 - k * c, p.2.2)).contDiffAt

theorem perExt_eq_cell {c : ℝ} (hc : 0 < c) {ψ : Profile → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hδs : ∀ p ∈ tsupport ψ, δ ≤ p.2.1 ∧ p.2.1 ≤ c - δ) (p : Profile)
    (hp : p ∈ cell c) : perExt c ψ p = ψ p := by
  obtain ⟨_, hq, _⟩ := hp
  have hq0 : 0 < p.2.1 := hq.1
  have hq1 : p.2.1 ≤ c := hq.2
  rcases lt_or_eq_of_le hq1 with hlt | heq
  · have hfl : ⌊p.2.1 / c⌋ = 0 := by
      rw [Int.floor_eq_iff]
      constructor
      · simp; positivity
      · simp; rw [div_lt_iff₀ hc]; linarith
    unfold perExt redq
    rw [hfl]; simp
  · have h1 : perExt c ψ p = 0 := by
      unfold perExt redq
      have : p.2.1 / c = 1 := by rw [heq]; exact div_self hc.ne'
      rw [this]; simp
      apply image_eq_zero_of_notMem_tsupport
      intro hm
      have := (hδs _ hm).1
      simp only at this
      linarith
    have h2 : ψ p = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hm
      have := (hδs _ hm).2
      linarith
    rw [h1, h2]

theorem exists_periodic_ext {c : ℝ} (hc : 0 < c) {ψ : Profile → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hcs : HasCompactSupport ψ) (hU : tsupport ψ ⊆ Ioi 0 ×ˢ Ioo 0 c ×ˢ univ) :
    ∃ Φ : Profile → ℝ, ContDiff ℝ ∞ Φ ∧ QPeriodic c Φ ∧ (∀ p ∈ cell c, Φ p = ψ p) ∧
      ∃ s0 s1 L : ℝ, 0 < s0 ∧ ∀ p : Profile, Φ p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L := by
  obtain ⟨δ, hδ, h2δ, hδs⟩ := exists_delta hc hcs hU
  refine ⟨perExt c ψ, perExt_contDiff hc hψ hδ h2δ hδs, perExt_periodic hc ψ,
    perExt_eq_cell hc hδ hδs, ?_⟩
  by_cases ne : (tsupport ψ).Nonempty
  · have hK : IsCompact (tsupport ψ) := hcs
    obtain ⟨x, hx, hxmin⟩ := hK.exists_isMinOn ne (f := fun p : Profile => p.1)
      (by fun_prop : Continuous fun p : Profile => p.1).continuousOn
    obtain ⟨y, hy, hymax⟩ := hK.exists_isMaxOn ne (f := fun p : Profile => p.1)
      (by fun_prop : Continuous fun p : Profile => p.1).continuousOn
    obtain ⟨z, hz, hzmax⟩ := hK.exists_isMaxOn ne (f := fun p : Profile => |p.2.2|)
      (by fun_prop : Continuous fun p : Profile => |p.2.2|).continuousOn
    refine ⟨x.1, y.1, |z.2.2|, (hU hx).1, fun p hp => ?_⟩
    have hm : (p.1, redq c p.2.1, p.2.2) ∈ tsupport ψ := subset_tsupport _ hp
    have h1 : x.1 ≤ (p.1, redq c p.2.1, p.2.2).1 := hxmin hm
    have h2 : (p.1, redq c p.2.1, p.2.2).1 ≤ y.1 := hymax hm
    have h3 : |(p.1, redq c p.2.1, p.2.2).2.2| ≤ |z.2.2| := hzmax hm
    exact ⟨⟨h1, h2⟩, h3⟩
  · refine ⟨1, 1, 0, one_pos, fun p hp => ?_⟩
    exfalso; apply hp
    unfold perExt
    apply image_eq_zero_of_notMem_tsupport
    intro hm; exact ne ⟨_, hm⟩

end SHH
end UnforcedLeray.Short.PartIIa
