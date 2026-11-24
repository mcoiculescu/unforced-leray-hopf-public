import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3.Of

/-!
# `s^{1/2} Φ` is a meridional test (organizer task `PartIII-b:C/flatset/col/7/3/3`)

Source `the November 2 reference manuscript` 1650-1656, 1684-1689.
A flat test `Φ` vanishes for `s < s₁` with `s₁ > 0`, so `s ↦ √s Φ` is smooth (locally zero near
`s < s₁`, and `√` is smooth on `s ≥ s₁`); it is `c`-periodic in `q` and supported in a band.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate InnerProductSpace ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.IIIa (IsFlatTest)
open UnforcedLeray.Short.PartIIa (IsMeridTest)

theorem zetaPhiMeridTest : ZetaPhiMeridTest := by
  intro c hc Φ hΦ
  obtain ⟨s1, s2, R, hs1, hsupp⟩ := hΦ.support
  -- smoothness of each component `s ↦ √s Φ_i`
  have hsm : ∀ i : Fin 2, ContDiff ℝ ∞ (fun p : Profile => ((Real.sqrt p.1 * Φ p.1 p.2 i : ℝ) : ℂ)) := by
    intro i
    rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : p.1 < s1
    · apply ContDiffAt.congr_of_eventuallyEq (contDiffAt_const (c := (0 : ℂ)))
      filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hp] with q hq
      simp [hsupp q.1 q.2 i (Or.inl hq)]
    · push_neg at hp
      have hp0 : p.1 ≠ 0 := (lt_of_lt_of_le hs1 hp).ne'
      have h1 : ContDiffAt ℝ ∞ (fun q : Profile => Real.sqrt q.1) p :=
        (Real.contDiffAt_sqrt hp0).comp p contDiff_fst.contDiffAt
      have h2 : ContDiffAt ℝ ∞ (fun q : Profile => Φ q.1 q.2 i) p :=
        (hΦ.smooth i).contDiffAt
      exact (Complex.ofRealCLM.contDiff.contDiffAt).comp p (h1.mul h2)
  refine ⟨?_, ?_, ?_⟩
  · -- smooth
    unfold zetaPhi
    exact contDiff_piLp' 2 (fun i => hsm i)
  · -- c-periodic in q
    intro p
    ext i
    simp [zetaPhi, hΦ.periodic]
  · -- band
    refine ⟨s1, s2, R, hs1, ?_⟩
    intro p hp
    have hex : ∃ i, Φ p.1 p.2 i ≠ 0 := by
      by_contra h
      push_neg at h
      apply hp
      ext i
      simp [zetaPhi, h i]
    obtain ⟨i, hi⟩ := hex
    have hgood : ¬ (p.1 < s1 ∨ s2 < p.1 ∨ R < |p.2.2|) := fun h => hi (hsupp p.1 p.2 i h)
    push_neg at hgood
    exact ⟨⟨hgood.1, hgood.2.1⟩, hgood.2.2⟩

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
