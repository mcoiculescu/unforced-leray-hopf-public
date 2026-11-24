import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4

/-!
# `SFCDuhamelEverywhere` from four regularity facts (decomposition of
`PartIII-b:C/flatset/col/7/1/1/2/4/2/4/1`)

Source `the November 2 reference manuscript`
1650-1656, 1684-1689, 3426-3430.  The ae identity `b = causalHeat (sfcGp f')` is upgraded to every
`(s,x)`, `s > 0`, because both sides are continuous and `q`-periodic there and `ageμ` charges every
nonempty open subset of the strip `s > 0`, `|q| < c/2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- Regularity of `P₀` on smooth forces (source 1650-1656, 1684-1689: the flat projection of the
lift of a smooth compactly supported force is smooth, bounded, `q`-periodic, supported in
`σ ≥ s₀ > 0`). `P₀ f'` agrees `measureH`-ae with a continuous, `q`-periodic, bounded `G` vanishing
for `σ < s₀`. -/
def SFCPepsSmooth : Prop :=
  ∀ (c : ℝ) (_hc : 0 < c) (g : Hsp c) (f' : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC),
    IsSmoothForce c g → SFCLift g f' →
      ∃ G : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC,
        Continuous G ∧
        (∀ σ q η, G (σ, (q + c, η)) = G (σ, (q, η))) ∧
        (∃ M : ℝ, ∀ p, ‖G p‖ ≤ M) ∧
        (∃ s0 : ℝ, 0 < s0 ∧ ∀ p : UnforcedLeray.B0220.Profile, p.1 < s0 → G p = 0) ∧
        (UnforcedLeray.Short.PartIIa.PepsC 0 c f' : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
          =ᵐ[UnforcedLeray.B0220.measureH c] G

/-- Continuity of the Duhamel integral on `s > 0` for the datum `sfcGp` of a lift (source 3426-3430;
from `SFCPepsSmooth`: the integral over `σ ∈ [s₀, s]` of `planeHeat (ν (s-σ))` of a bounded
continuous periodic datum, continuity of parametric integrals). -/
def SFCCausalHeatCont : Prop :=
  ∀ (c ν μ : ℝ) (hc : 0 < c) (R0 : Hsp c →L[ℝ] Hsp c) (g : Hsp c), ClassicalCtx c ν μ hc R0 g →
    ∀ f' : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC, SFCLift g f' →
      ∀ i : Fin 2, ContinuousOn
        (fun p : Chart => (UnforcedLeray.B0225.causalHeat c ν (μ : ℂ) (sfcGp hc f') p) i)
        (Ioi (0 : ℝ) ×ˢ univ)

/-- `q`-periodicity of the Duhamel integral for `s > 0` (source 1650-1656: the datum is
periodized by `B0220.periodize`, so the integral is `c`-periodic in `q`). -/
def SFCCausalHeatPer : Prop :=
  ∀ (c ν μ : ℝ) (hc : 0 < c) (R0 : Hsp c →L[ℝ] Hsp c) (g : Hsp c), ClassicalCtx c ν μ hc R0 g →
    ∀ f' : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC, SFCLift g f' →
      ∀ s q η, 0 < s → ∀ i : Fin 2,
        (UnforcedLeray.B0225.causalHeat c ν (μ : ℂ) (sfcGp hc f') (s, (q + c, η))) i =
          (UnforcedLeray.B0225.causalHeat c ν (μ : ℂ) (sfcGp hc f') (s, (q, η))) i

/-- `ageμ` charges every nonempty open subset of one cell strip `s > 0`, `|q| < c/2`
(`Lib/AxisymmetricB/Lift.lean:47`: product of `s^a ds` on `(0,∞)` and the normalized cell measure). -/
def AgeμOpenPos : Prop :=
  ∀ (c a : ℝ), 0 < c → ∀ U : Set Chart, IsOpen U →
    U ⊆ Ioi (0 : ℝ) ×ˢ (Ioo (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ)) → U.Nonempty →
      0 < ageμ c a U

theorem sfcDuhamelEverywhere_of (hCont : SFCCausalHeatCont) (hPer : SFCCausalHeatPer)
    (hPos : AgeμOpenPos) : SFCDuhamelEverywhere := by
  intro c ν μ hc R0 g hctx b hb _hae f' hlift hD s hs x i
  by_contra hne
  set H : Chart → ℂ := fun p => (UnforcedLeray.B0225.causalHeat c ν (μ : ℂ) (sfcGp hc f') p) i
    with hH
  set B : Chart → ℂ := fun p => b p i with hB
  have hBc : ContinuousOn B (Ioi (0 : ℝ) ×ˢ univ) := (hb.2.1 i).continuousOn
  have hHc : ContinuousOn H (Ioi (0 : ℝ) ×ˢ univ) := hCont c ν μ hc R0 g hctx f' hlift i
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  -- the open set where they differ
  have hdiff : ContinuousOn (fun p => B p - H p) (Ioi (0 : ℝ) ×ˢ univ) := hBc.sub hHc
  have hVo : IsOpen ((Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) ∩
      (fun p => B p - H p) ⁻¹' {(0 : ℂ)}ᶜ) :=
    hdiff.isOpen_inter_preimage hopen (isOpen_compl_singleton (x := (0 : ℂ)))
  -- periodicity
  have hper : ∀ p : Chart, 0 < p.1 → B (p.1, (p.2.1 + c, p.2.2)) - H (p.1, (p.2.1 + c, p.2.2)) =
      B p - H p := by
    intro p hp
    obtain ⟨s', q, η⟩ := p
    simp only at hp ⊢
    have h1 := hb.2.2.1 s' q η hp
    have h2 := hPer c ν μ hc R0 g hctx f' hlift s' q η hp i
    simp only [hB, hH, h1, h2]
  have hperZ : ∀ (n : ℤ) (p : Chart), 0 < p.1 →
      B (p.1, (p.2.1 + n * c, p.2.2)) - H (p.1, (p.2.1 + n * c, p.2.2)) = B p - H p := by
    intro n p hp
    induction n using Int.induction_on generalizing p with
    | zero => simp
    | succ k ih =>
      have h1 := hper (p.1, (p.2.1 + ((k : ℤ) : ℝ) * c, p.2.2)) hp
      have h2 := ih p hp
      simp only [Int.cast_add, Int.cast_one, Int.cast_natCast] at h1 h2 ⊢
      have e : p.2.1 + ((k : ℝ) + 1) * c = p.2.1 + (k : ℝ) * c + c := by ring
      rw [e]
      exact h1.trans h2
    | pred k ih =>
      have := hper (p.1, (p.2.1 + (-(k:ℤ) - 1 : ℤ) * c, p.2.2)) hp
      have h2 := ih p hp
      simp only [Int.cast_sub, Int.cast_neg, Int.cast_one, Int.cast_natCast] at this h2 ⊢
      have e : p.2.1 + (-(k:ℝ) - 1) * c + c = p.2.1 + -(k:ℝ) * c := by ring
      rw [e] at this
      rw [this] at h2
      exact h2
  have hne' : B (s, x) - H (s, x) ≠ 0 := sub_ne_zero.2 hne
  -- shift into the cell
  set n : ℤ := ⌊(x.1 + c / 2) / c⌋ with hn
  have hn1 : (n : ℝ) ≤ (x.1 + c / 2) / c := Int.floor_le _
  have hn2 : (x.1 + c / 2) / c < n + 1 := Int.lt_floor_add_one _
  have hq1 : -(c / 2) ≤ x.1 + (-n : ℤ) * c := by
    push_cast
    have := (le_div_iff₀ hc).1 hn1
    linarith
  have hq2 : x.1 + (-n : ℤ) * c < c / 2 := by
    push_cast
    have := (div_lt_iff₀ hc).1 hn2
    linarith
  have hp' := hperZ (-n) (s, x) hs
  simp only at hp'
  set p' : Chart := (s, (x.1 + (-n : ℤ) * c, x.2)) with hp'def
  have hp'V : p' ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) ∩
      (fun p => B p - H p) ⁻¹' {(0 : ℂ)}ᶜ := by
    refine ⟨⟨hs, mem_univ _⟩, ?_⟩
    show B p' - H p' ≠ 0
    rw [hp']; exact hne'
  have hcl : p' ∈ closure (Ioi (0 : ℝ) ×ˢ (Ioo (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ))) := by
    rw [closure_prod_eq, closure_prod_eq, closure_Ioi, closure_Ioo (by linarith), closure_univ]
    exact ⟨le_of_lt hs, ⟨hq1, hq2.le⟩, mem_univ _⟩
  obtain ⟨w, hwV, hwS⟩ := mem_closure_iff.1 hcl _ hVo hp'V
  set W := (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) ∩ (fun p => B p - H p) ⁻¹' {(0 : ℂ)}ᶜ ∩
    (Ioi (0 : ℝ) ×ˢ (Ioo (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ))) with hW
  have hWo : IsOpen W := hVo.inter (isOpen_Ioi.prod (isOpen_Ioo.prod isOpen_univ))
  have hWpos : 0 < ageμ c (-3 / 2) W :=
    hPos c (-3 / 2) hc W hWo inter_subset_right ⟨w, hwV, hwS⟩
  have hnull : ageμ c (-3 / 2) {p : Chart | ¬ ∀ j : Fin 2, b p j =
      (UnforcedLeray.B0225.causalHeat c ν (μ : ℂ) (sfcGp hc f') p) j} = 0 := hD
  have hsub : W ⊆ {p : Chart | ¬ ∀ j : Fin 2, b p j =
      (UnforcedLeray.B0225.causalHeat c ν (μ : ℂ) (sfcGp hc f') p) j} := by
    intro p hp hall
    have := hall i
    apply hp.1.2
    show B p - H p = 0
    simp only [hB, hH]
    rw [this]; ring
  exact absurd (measure_mono_null hsub hnull) hWpos.ne'

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
