import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_4

/-!
# `SmoothForceDense` from three source facts (decomposition of `PartIII-b:C/flatset/col/7/1/1/1`)

Source of record `the November 2 reference manuscript` 1678, 1684-1689: smooth
periodic forces with compact support in `(s, q, η)` are dense in `H = L²(ageμ c (-3/2))`.
The `q`-cell is `Ico (-c/2) (c/2)` (`Cyl.cell`), so boxes are taken in `[a,b] ⊂ (-c/2, c/2)`.

* `SFDTrunc` : truncation of `h ∈ Hsp c` to a compact box `s ∈ [s₀,s₁]`, `q ∈ [a,b]`, `|η| ≤ L`
  (dominated convergence for the weighted `L²` norm).
* `SFDSmoothApprox` : a box-supported `h'` is approximated in the weighted `L²` norm by a smooth
  compactly supported (in the open cell) real vector field `F`
  (mollification / `C_c^∞` density; the weight `s^{-3/2}` is bounded on `s ≥ s₀/2`).
* `SFDPeriodize` : such `F` is the (a.e.) representative of a smooth force `g`
  (periodize in `q`, build the `Lp` element).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (vnorm2 tnorm2)

/-- `h` vanishes a.e. outside the box `s ∈ [s₀,s₁]`, `q ∈ [a,b]`, `|η| ≤ L`. -/
def BoxSupp (c s0 s1 a b L : ℝ) (h : Hsp c) : Prop :=
  ∀ᵐ p ∂(ageμ c (-3 / 2)), NearInst.velC h p ≠ 0 →
    p.1 ∈ Icc s0 s1 ∧ p.2.1 ∈ Icc a b ∧ |p.2.2| ≤ L

/-- **T** Truncation to a compact box (source 1678). -/
def SFDTrunc : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (h : Hsp c) (ε : ℝ), 0 < ε →
    ∃ (s0 s1 a b L : ℝ) (h' : Hsp c), 0 < s0 ∧ -(c / 2) < a ∧ b < c / 2 ∧ BoxSupp c s0 s1 a b L h' ∧
      ‖h - h'‖ < ε

/-- **S** Smooth compactly supported approximation of a box-supported field in the weighted `L²`
norm (source 1678, 1684-1689): `F` is `C^∞`, vanishes outside a box with `s ≥ s₀' > 0`,
`q ∈ [a',b'] ⊂ (-c/2,c/2)`. -/
def SFDSmoothApprox : Prop :=
  ∀ (c s0 s1 a b L : ℝ), 0 < c → 0 < s0 → -(c / 2) < a → b < c / 2 →
    ∀ h' : Hsp c, BoxSupp c s0 s1 a b L h' → ∀ ε : ℝ, 0 < ε →
    ∃ F : Chart → Fin 2 → ℝ, (∀ i, ContDiff ℝ ∞ fun p => F p i) ∧
      (∃ s0' s1' a' b' L' : ℝ, 0 < s0' ∧ -(c / 2) < a' ∧ b' < c / 2 ∧
        ∀ p, F p ≠ 0 → p.1 ∈ Icc s0' s1' ∧ p.2.1 ∈ Icc a' b' ∧ |p.2.2| ≤ L') ∧
      ∫⁻ p, ENNReal.ofReal
          (vnorm2 (NearInst.velC h' p - fun i => ((F p i : ℝ) : ℂ)) ^ 2) ∂(ageμ c (-3 / 2)) <
        ENNReal.ofReal (ε ^ 2)

/-- **P** Periodization and `Lp` packaging (source 1684-1689): a smooth `F` supported in a compact
box inside the open cell is a.e. the representative of a smooth force. -/
def SFDPeriodize : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ F : Chart → Fin 2 → ℝ, (∀ i, ContDiff ℝ ∞ fun p => F p i) →
    (∃ s0' s1' a' b' L' : ℝ, 0 < s0' ∧ -(c / 2) < a' ∧ b' < c / 2 ∧
        ∀ p, F p ≠ 0 → p.1 ∈ Icc s0' s1' ∧ p.2.1 ∈ Icc a' b' ∧ |p.2.2| ≤ L') →
    ∃ g : Hsp c, IsSmoothForce c g ∧
      ∀ᵐ p ∂(ageμ c (-3 / 2)), NearInst.velC g p = fun i => ((F p i : ℝ) : ℂ)

theorem smoothForceDense_of (hT : SFDTrunc) (hS : SFDSmoothApprox) (hP : SFDPeriodize) :
    SmoothForceDense := by
  intro c hc h ε hε
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨s0, s1, a, b, L, h', hs0, ha, hb, hbox, hh⟩ := hT c hc h (ε / 2) hε2
  obtain ⟨F, hF, hFs, hint⟩ := hS c s0 s1 a b L hc hs0 ha hb h' hbox (ε / 2) hε2
  obtain ⟨g, hg, hgF⟩ := hP c hc F hF hFs
  refine ⟨g, hg, ?_⟩
  have e1 : ∫⁻ p, ENNReal.ofReal (vnorm2 (NearInst.velC h' p - NearInst.velC g p) ^ 2)
        ∂(ageμ c (-3 / 2)) =
      ∫⁻ p, ENNReal.ofReal
          (vnorm2 (NearInst.velC h' p - fun i => ((F p i : ℝ) : ℂ)) ^ 2) ∂(ageμ c (-3 / 2)) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hgF] with p hp
    rw [hp]
  rw [← e1, hspNormLintegral c h' g] at hint
  have h2 : ‖h' - g‖ ^ 2 < (ε / 2) ^ 2 := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 hint
  have h3 : ‖h' - g‖ < ε / 2 := lt_of_pow_lt_pow_left₀ 2 hε2.le h2
  calc ‖h - g‖ = ‖(h - h') + (h' - g)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖h - h'‖ + ‖h' - g‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hh h3
    _ = ε := by ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
