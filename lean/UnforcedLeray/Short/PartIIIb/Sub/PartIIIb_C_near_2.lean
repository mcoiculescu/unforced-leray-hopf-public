import UnforcedLeray.Short.PartIIIb.NearInst.Targets

/-!
# Sub-lemmas for `PartIII-b:C/near/2` (`FreeStressExists`, source 3427-3440, 3541-3552, 1686-1689)

The bounded operator `S₀ : Z → H` is assembled from the causal zero-entrance solution map.  We cut
the construction into four true facts about the *pin* `FreePin F h` ("`h ∈ H` is a representative of
the causal energy solution with force `F`"): existence of a pinned element for every `F`,
uniqueness, real-linear closure, and the energy bound.  The assembly (`LinearMap` + `mkContinuous`)
is `freeStressExists_of`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.Blueprint.Planar

/-- `h ∈ H` is the flat free causal response to `F ∈ Z` (the content of one instance of
`IsFreeStress`). -/
def FreePin {c mZ ρb : ℝ} (ν μ : ℝ) (F : Zsp c mZ ρb) (h : Hsp c) : Prop :=
  ∃ (b : Chart → Fin 2 → ℂ) (G : Chart → Fin 2 → Fin 2 → ℂ),
    b =ᵐ[ageμ c (-3 / 2)] velC h ∧
      UnforcedLeray.Short.IIIa.IsCausalEnergySolution c ν (μ : ℂ) (fun _ _ _ => 0)
        (merBlockC (zsum F)) b G

/-- The common regime of the four facts. -/
def FreeStressRegime (Q : ∀ {c mZ ρb : ℝ}, ℝ → ℝ → Prop) : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ Kset : Set ℝ, IsCompact Kset →
    Kset ⊆ Ioo 0 (1 / 4) → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀, ∀ c : ℝ, c = (ν ^ 2)⁻¹ →
      ∀ μ ∈ Kset, ∀ mZ ρb : ℝ, 0 ≤ mZ → 0 < ρb → @Q c mZ ρb ν μ

/-- Existence: every `F` has a real representative of the causal energy solution in `H`
(source 3427-3440: existence from `FreeCausalExistsUnique`; reality by conjugation closure of
`IsCausalEnergySolution` for real `μ` and uniqueness; `memLp` from the energy bound with
`1 ≤ g ≤ e^{γ/ν}`). -/
def FreeStressPinExists : Prop :=
  FreeStressRegime (fun {c mZ ρb} ν μ => ∀ F : Zsp c mZ ρb, ∃ h : Hsp c, FreePin ν μ F h)

/-- Uniqueness of the pinned element (source 3541-3552; `ageμ c (-3/2)`-a.e. equality of
representatives is equality in `H`). -/
def FreeStressPinUnique : Prop :=
  FreeStressRegime (fun {c mZ ρb} ν μ =>
    ∀ (F : Zsp c mZ ρb) (h h' : Hsp c), FreePin ν μ F h → FreePin ν μ F h' → h = h')

/-- Real-linear closure of the pin (the `N8` linearity `CausalSolSub` with scalar multiples). -/
def FreeStressPinLinear : Prop :=
  FreeStressRegime (fun {c mZ ρb} ν μ =>
    ∀ (F F' : Zsp c mZ ρb) (h h' : Hsp c) (r : ℝ), FreePin ν μ F h → FreePin ν μ F' h' →
      FreePin ν μ (F + r • F') (h + r • h'))

/-- Energy bound (source 3541-3552, 1686-1689): `‖h‖_H ≤ C ‖F‖_Z`, using `g⁻¹ ≤ 1`, `g ≤ e^{γ/ν}`,
`‖F₁ + F₂‖_𝒯 ≤ ‖F‖_Z` for `W ≥ 1`. -/
def FreeStressPinBound : Prop :=
  FreeStressRegime (fun {c mZ ρb} ν μ =>
    ∃ C : ℝ, ∀ (F : Zsp c mZ ρb) (h : Hsp c), FreePin ν μ F h → ‖h‖ ≤ C * ‖F‖)

theorem freeStressExists_of (h1 : FreeStressPinExists) (h2 : FreeStressPinUnique)
    (h3 : FreeStressPinLinear) (h4 : FreeStressPinBound) : FreeStressExists := by
  intro P hP Kset hK hKs
  obtain ⟨ν1, hν1, e1⟩ := h1 P hP Kset hK hKs
  obtain ⟨ν2, hν2, e2⟩ := h2 P hP Kset hK hKs
  obtain ⟨ν3, hν3, e3⟩ := h3 P hP Kset hK hKs
  obtain ⟨ν4, hν4, e4⟩ := h4 P hP Kset hK hKs
  refine ⟨min (min ν1 ν2) (min ν3 ν4), lt_min (lt_min hν1 hν2) (lt_min hν3 hν4), ?_⟩
  intro ν hν c hc μ hμ mZ ρb hmZ hρb
  have hν' : ν ∈ Ioc 0 (min (min ν1 ν2) (min ν3 ν4)) := hν
  have m1 : ν ∈ Ioc 0 ν1 := ⟨hν'.1, hν'.2.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
  have m2 : ν ∈ Ioc 0 ν2 := ⟨hν'.1, hν'.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
  have m3 : ν ∈ Ioc 0 ν3 := ⟨hν'.1, hν'.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have m4 : ν ∈ Ioc 0 ν4 := ⟨hν'.1, hν'.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  have hE := e1 ν m1 c hc μ hμ mZ ρb hmZ hρb
  have hU := e2 ν m2 c hc μ hμ mZ ρb hmZ hρb
  have hL := e3 ν m3 c hc μ hμ mZ ρb hmZ hρb
  obtain ⟨C, hC⟩ := e4 ν m4 c hc μ hμ mZ ρb hmZ hρb
  choose s hs using hE
  have hadd : ∀ F F' : Zsp c mZ ρb, s (F + F') = s F + s F' := by
    intro F F'
    refine hU (F + F') _ _ (hs _) ?_
    simpa using hL F F' (s F) (s F') 1 (hs F) (hs F')
  have hsmul : ∀ (r : ℝ) (F : Zsp c mZ ρb), s (r • F) = r • s F := by
    intro r F
    have h0 : s 0 = 0 := by
      have := hadd 0 0
      simpa using this
    refine hU (r • F) _ _ (hs _) ?_
    simpa [h0] using hL 0 F (s 0) (s F) r (hs 0) (hs F)
  let T : Zsp c mZ ρb →ₗ[ℝ] Hsp c :=
    { toFun := s, map_add' := hadd, map_smul' := hsmul }
  refine ⟨LinearMap.mkContinuous T (max C 0) ?_, ?_⟩
  · intro F
    have := hC F (s F) (hs F)
    calc ‖T F‖ ≤ C * ‖F‖ := this
      _ ≤ max C 0 * ‖F‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  · intro F
    obtain ⟨b, G, hb, hsol⟩ := hs F
    exact ⟨b, G, hb, hsol⟩

end UnforcedLeray.Short.PartIIIb.NearInst
