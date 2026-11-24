import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique

/-!
# Part II-b, task `PartII-b:T13`: decomposition of `flat_graph_bound`

Source of record: `the November 2 reference manuscript`, lines 1912-1938.

The drafted target quantified over all real `ν, c` and all `r, μ`; the source (SP 1912-1918,
1923-1927) only has `ν > 0`, `c > 0`, `1 < r < 3` and `a_r = Re μ + (3/r - 1)/2 > 0` (the
hypotheses of `flat_unique` and `FlatCausalExists`), so the target is corrected to those.
Proof of the corrected target: the causal response `b'` with the graph bound (analytic core,
SP 1920-1938) is unique in the flat class by `flat_unique` (the difference solves the equation
with `F = 0` and lies in the flat class), and the graph bound transfers along a.e. equality.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

/-- The corrected target `flat_graph_bound` (SP 1912-1938). -/
def FlatGraphBound : Prop :=
  ∀ r : ℝ, 1 < r → r < 3 → ∀ μ : ℂ, 0 < μ.re + (3 / r - 1) / 2 →
    ∃ C : ℝ, ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ F : CProf, InHr c r F → ∀ b : CProf,
      IsFlatResponse ν μ F b → InFlatClass c r b → GraphBound ν c r 0 C F b

/-- Analytic core (SP 1920-1938, dyadic windows): the causal response lies in the flat class and
satisfies the graph bound. -/
def FlatGraphExists : Prop :=
  ∀ r : ℝ, 1 < r → r < 3 → ∀ μ : ℂ, 0 < μ.re + (3 / r - 1) / 2 →
    ∃ C : ℝ, ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ F : CProf, InHr c r F →
      ∃ b : CProf, IsFlatResponse ν μ F b ∧ InFlatClass c r b ∧ GraphBound ν c r 0 C F b

/-- Linearity of the flat equation: the difference of two flat responses to `F` is a flat
response to `0` (SP 1921-1927). -/
def FlatResponseSub : Prop :=
  ∀ (ν : ℝ) (μ : ℂ) (F b b' : CProf), IsFlatResponse ν μ F b → IsFlatResponse ν μ F b' →
    IsFlatResponse ν μ 0 (b - b')

/-- The flat class is a vector space (weak derivatives are linear). -/
def FlatClassSub : Prop :=
  ∀ (c r : ℝ) (b b' : CProf), InFlatClass c r b → InFlatClass c r b' → InFlatClass c r (b - b')

/-- The graph bound depends on `b` only through its a.e. class for `hMeas c r`. -/
def GraphBoundCongr : Prop :=
  ∀ (ν c r C : ℝ) (F b b' : CProf), b =ᵐ[hMeas c r] b' → GraphBound ν c r 0 C F b' →
    GraphBound ν c r 0 C F b

theorem flatGraphBound_of (h1 : FlatGraphExists) (h2 : FlatResponseSub) (h3 : FlatClassSub)
    (h4 : GraphBoundCongr) : FlatGraphBound := by
  intro r hr hr3 μ ha
  obtain ⟨C, hC⟩ := h1 r hr hr3 μ ha
  refine ⟨C, fun ν c hν hc F hF b hb hbc => ?_⟩
  obtain ⟨b', hb', hc', hg'⟩ := hC ν c hν hc F hF
  have h0 : b - b' =ᵐ[hMeas c r] 0 :=
    flat_unique hc hν hr hr3 ha (b - b') (h3 c r b b' hbc hc') (h2 ν μ F b b' hb hb')
  refine h4 ν c r C F b b' ?_ hg'
  filter_upwards [h0] with x hx
  exact sub_eq_zero.mp hx

end UnforcedLeray.Short.IIb

end
