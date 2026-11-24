import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_2_4_6_2
import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.HeatSliceBounds

/-!
# `PartII-a:N01/9/1/2/4/6/2/1` (helper): bounds for `Ψ = σ⁻¹ • F`

Source `the November 2 reference manuscript`
lines 1684-1689.  For a smooth `c`-periodic force `F` supported in `s ∈ [s₁,s₂]`, `|η| ≤ R`, the
function `Ψ p = p.1⁻¹ • F p` is `C¹`, vanishes for `p.1 < s₁`, and `Ψ`, `DΨ` are bounded.

The bounded-derivative argument is the one of `hsb_comp_bounds` (HeatSliceBounds.lean), copied
for the `MeridC`-valued (vector) codomain `Ψ : Profile → MeridC`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.B0220 (Profile)
open UnforcedLeray.B0223 (MeridC)

/-- A `C¹`, `c`-periodic-in-`q`, `MeridC`-valued function vanishing on the band complement has
bounded values and bounded derivative. -/
theorem hgi_comp_bounds_meridC {c s₁ s₂ R : ℝ} (hc : 0 < c) {Ψ : Profile → MeridC}
    (hC : ContDiff ℝ 1 Ψ) (hper : UnforcedLeray.B0220.QPeriodic c Ψ)
    (hz : ∀ p : Profile, (p.1 < s₁ ∨ s₂ < p.1 ∨ R < |p.2.2|) → Ψ p = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ p, ‖Ψ p‖ ≤ M) ∧ (∀ p, ‖fderiv ℝ Ψ p‖ ≤ M) := by
  have hΨc : Continuous Ψ := hC.continuous
  have hD : Continuous (fderiv ℝ Ψ) := hC.continuous_fderiv (by norm_num)
  have hxa' : ∀ x : Profile, x + ((0 : ℝ), c, (0 : ℝ)) = (x.1, x.2.1 + c, x.2.2) :=
    fun x => by ext <;> simp
  have hpa : ∀ x : Profile, Ψ (x + ((0 : ℝ), c, (0 : ℝ))) = Ψ x := fun x => by
    rw [hxa' x]
    exact hper x
  have hDper : UnforcedLeray.B0220.QPeriodic c (fderiv ℝ Ψ) := by
    intro p
    have hxa : p + ((0 : ℝ), c, (0 : ℝ)) = (p.1, p.2.1 + c, p.2.2) := hxa' p
    have h1 : fderiv ℝ (fun x : Profile => Ψ (x + ((0 : ℝ), c, (0 : ℝ))))  p =
        fderiv ℝ Ψ (p + ((0 : ℝ), c, (0 : ℝ))) := fderiv_comp_add_right _
    have h2 : (fun x : Profile => Ψ (x + ((0 : ℝ), c, (0 : ℝ)))) = Ψ := funext hpa
    rw [h2] at h1
    rw [← hxa]
    exact h1.symm
  have hU : IsOpen {p : Profile | p.1 < s₁ ∨ s₂ < p.1 ∨ R < |p.2.2|} :=
    (isOpen_lt continuous_fst continuous_const).union
      ((isOpen_lt continuous_const continuous_fst).union
        (isOpen_lt continuous_const (continuous_abs.comp (continuous_snd.comp continuous_snd))))
  have hDz : ∀ p : Profile, (p.1 < s₁ ∨ s₂ < p.1 ∨ R < |p.2.2|) → fderiv ℝ Ψ p = 0 := by
    intro p hp
    have hev : Ψ =ᶠ[𝓝 p] fun _ => (0 : MeridC) :=
      Filter.eventually_of_mem (hU.mem_nhds hp) (fun y hy => hz y hy)
    rw [hev.fderiv_eq]
    simp
  obtain ⟨M1, hM1, hb1⟩ := hsb_bounded_of_periodic_band hc hΨc hper hz
  obtain ⟨M2, hM2, hb2⟩ := hsb_bounded_of_periodic_band hc hD hDper hDz
  exact ⟨max M1 M2, le_max_of_le_left hM1, fun p => (hb1 p).trans (le_max_left _ _),
    fun p => (hb2 p).trans (le_max_right _ _)⟩

theorem hgiPsiBounds : UnforcedLeray.Short.PartIIa.N01.HGIPsiBounds := by
  intro c hc F hF
  obtain ⟨hFc, hFper, s₁, s₂, R, hs₁, hz⟩ := hF
  -- smoothness of `p ↦ p.1⁻¹ • F p` (it vanishes for `p.1 < s₁`)
  have hgC : ContDiff ℝ 1 (fun p : Profile => p.1⁻¹ • F p) := by
    rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : p.1 < s₁
    · refine ContDiffAt.congr_of_eventuallyEq (contDiffAt_const (c := (0 : MeridC))) ?_
      filter_upwards [(isOpen_lt continuous_fst continuous_const :
        IsOpen {p : Profile | p.1 < s₁}).mem_nhds hp] with y hy
      simp [hz y (Or.inl hy)]
    · have hpos : p.1 ≠ 0 := (lt_of_lt_of_le hs₁ (not_lt.1 hp)).ne'
      exact (contDiffAt_fst.inv hpos).smul (hFc.of_le (by simp)).contDiffAt
  have hΨz : ∀ p : Profile, (p.1 < s₁ ∨ s₂ < p.1 ∨ R < |p.2.2|) →
      (fun q : Profile => q.1⁻¹ • F q) p = 0 := by
    intro p hp
    simp [hz p hp]
  have hper : UnforcedLeray.B0220.QPeriodic c (fun q : Profile => q.1⁻¹ • F q) := by
    intro p
    show p.1⁻¹ • F (p.1, p.2.1 + c, p.2.2) = p.1⁻¹ • F p
    rw [hFper p]
  obtain ⟨M, _hM0, hv, hd⟩ := hgi_comp_bounds_meridC hc hgC hper hΨz
  exact ⟨s₁, M, hs₁, hgC, fun p hp => by simp [hz p (Or.inl hp)],
    fun p => ⟨hv p, hd p⟩⟩

end UnforcedLeray.Short.PartIIa.N01
