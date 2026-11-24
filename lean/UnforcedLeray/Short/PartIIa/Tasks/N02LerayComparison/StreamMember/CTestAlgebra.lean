import UnforcedLeray.Short.PartIIa.Sub.N02_2

/-!
# Part II-a, task `PartII-a:N02/2/2`: algebra of complex band tests

Proves `CTestAlgebra` (`Sub/N02_2.lean`) exactly as defined there:
(1) a real profile test is a complex band test; (2) sums and (3) differences of complex band
tests are complex band tests; (4) a smooth `c`-periodic function times a complex band test is a
complex band test.

Band of a sum or difference: the union of the two bands, with `s₀ = min`, `s₁ = max`, `L = max`.
A point where `F p ± G p ≠ 0` has `F p ≠ 0` or `G p ≠ 0`, so it lies in one of the two bands.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-- A point of the first band lies in the union band. -/
theorem ctaBandLeft {s0 s1 L t0 t1 M : ℝ} {p : Profile}
    (h : p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) :
    p.1 ∈ Icc (min s0 t0) (max s1 t1) ∧ |p.2.2| ≤ max L M := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨a, b⟩ := Set.mem_Icc.mp h1
  exact ⟨Set.mem_Icc.mpr ⟨le_trans (min_le_left s0 t0) a, le_trans b (le_max_left s1 t1)⟩,
    le_trans h2 (le_max_left L M)⟩

/-- A point of the second band lies in the union band. -/
theorem ctaBandRight {s0 s1 L t0 t1 M : ℝ} {p : Profile}
    (h : p.1 ∈ Icc t0 t1 ∧ |p.2.2| ≤ M) :
    p.1 ∈ Icc (min s0 t0) (max s1 t1) ∧ |p.2.2| ≤ max L M := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨a, b⟩ := Set.mem_Icc.mp h1
  exact ⟨Set.mem_Icc.mpr ⟨le_trans (min_le_right s0 t0) a, le_trans b (le_max_right s1 t1)⟩,
    le_trans h2 (le_max_right L M)⟩

/-- (1) A real profile test is a complex band test. -/
theorem ctaOfReal : ∀ (c : ℝ) (Φ : Profile → ℝ), IsProfileTest c Φ →
    IsCTest c (fun p => (Φ p : ℂ)) := by
  intro c Φ hΦ
  obtain ⟨s0, s1, L, hs0, hb⟩ := hΦ.band
  have hper : QPeriodic c (fun p => (Φ p : ℂ)) := fun p =>
    congrArg (fun x : ℝ => (x : ℂ)) (hΦ.periodic p)
  have hband : ∃ s0 s1 L : ℝ, 0 < s0 ∧
      ∀ p : Profile, (fun p => (Φ p : ℂ)) p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L := by
    refine ⟨s0, s1, L, hs0, fun p hp => hb p ?_⟩
    intro h
    exact hp (by simp [h])
  exact ⟨Complex.ofRealCLM.contDiff.comp hΦ.smooth, hper, hband⟩

/-- (2) A sum of complex band tests is a complex band test. -/
theorem ctaAdd : ∀ (c : ℝ) (F G : Profile → ℂ), IsCTest c F → IsCTest c G →
    IsCTest c (fun p => F p + G p) := by
  intro c F G hF hG
  obtain ⟨s0, s1, L, hs0, hb⟩ := hF.band
  obtain ⟨t0, t1, M, ht0, hc⟩ := hG.band
  refine ⟨hF.smooth.add hG.smooth, ?_, ⟨min s0 t0, max s1 t1, max L M, lt_min hs0 ht0, ?_⟩⟩
  · intro p
    show F (p.1, p.2.1 + c, p.2.2) + G (p.1, p.2.1 + c, p.2.2) = F p + G p
    rw [hF.periodic p, hG.periodic p]
  · intro p hp
    by_cases hFp : F p = 0
    · have hGp : G p ≠ 0 := fun hGp => hp (by simp [hFp, hGp])
      exact ctaBandRight (hc p hGp)
    · exact ctaBandLeft (hb p hFp)

/-- (3) A difference of complex band tests is a complex band test. -/
theorem ctaSub : ∀ (c : ℝ) (F G : Profile → ℂ), IsCTest c F → IsCTest c G →
    IsCTest c (fun p => F p - G p) := by
  intro c F G hF hG
  obtain ⟨s0, s1, L, hs0, hb⟩ := hF.band
  obtain ⟨t0, t1, M, ht0, hc⟩ := hG.band
  refine ⟨hF.smooth.sub hG.smooth, ?_, ⟨min s0 t0, max s1 t1, max L M, lt_min hs0 ht0, ?_⟩⟩
  · intro p
    show F (p.1, p.2.1 + c, p.2.2) - G (p.1, p.2.1 + c, p.2.2) = F p - G p
    rw [hF.periodic p, hG.periodic p]
  · intro p hp
    by_cases hFp : F p = 0
    · have hGp : G p ≠ 0 := fun hGp => hp (by simp [hFp, hGp])
      exact ctaBandRight (hc p hGp)
    · exact ctaBandLeft (hb p hFp)

/-- (4) A smooth `c`-periodic function times a complex band test is a complex band test. -/
theorem ctaMul : ∀ (c : ℝ) (F G : Profile → ℂ), IsCTest c F → ContDiff ℝ ∞ G →
    QPeriodic c G → IsCTest c (fun p => G p * F p) := by
  intro c F G hF hG hGper
  obtain ⟨s0, s1, L, hs0, hb⟩ := hF.band
  refine ⟨hG.mul hF.smooth, ?_, ⟨s0, s1, L, hs0, ?_⟩⟩
  · intro p
    show G (p.1, p.2.1 + c, p.2.2) * F (p.1, p.2.1 + c, p.2.2) = G p * F p
    rw [hGper p, hF.periodic p]
  · intro p hp
    have hFp : F p ≠ 0 := fun h0 => hp (by simp [h0])
    exact hb p hFp

/-- The algebra of complex band tests (`CTestAlgebra`, `Sub/N02_2.lean`). -/
theorem cTestAlgebra : CTestAlgebra := by
  unfold CTestAlgebra
  exact ⟨ctaOfReal, ctaAdd, ctaSub, ctaMul⟩

end UnforcedLeray.Short.PartIIa
