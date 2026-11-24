import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_5_2

/-!
# Part II-b, task `PartII-b:G4/5/2/1` (`RingLiftJet`): decomposition

Source of record: `the November 2 reference manuscript` (SP) lines 2346-2366,
2386-2387.  `Nv R b τ y = √(age R y) • frameL y (b (chart R τ y))`.

`RingLiftJet` splits into
* `RingLiftVanish` (locality): `Nv R b τ` vanishes near the axis and where `age > S`;
* `RingLiftOffAxis`: the jet bound at off-axis points with `age ≤ S`, itself assembled
  (Faà di Bruno + Leibniz on the open set `axisᶜ`) from `ChartJets` and `SqrtFrameJets`, the
  explicit chart calculus (`ϱ⁻¹ = √age / R < √S` for `R ≥ 1`).

The chart bound carries the factor `1 + |η|`, `η = trans R y = R y₃/ϱ`: `∂_ϱ η = -η/ϱ` is
unbounded on `{age < S}` (`not_chartJets` in `Sub/PartII-b_G4_5_2_1_2.lean` refutes the unweighted
form, which was the earlier statement of `ChartJets`).  It is the only unbounded factor, and it is
absorbed by the transverse weight `(1+|η|)^j` of the profile jets in `RingLiftOffAxis`.  A bound
by powers of `|y₃|` instead (region `|y₃| ≤ T`) would not be absorbed: `|y₃| = ϱ|η|/R` with `ϱ`
unbounded above on `{age < S}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- **Leaf A (locality).** If `b` is supported in `{s ≤ S}` then `N_v b` vanishes in a
neighbourhood of every point of the axis and of every point with `age R y > S`.
(`age R y = R²/ϱ²` is `0` on the axis in Lean, `√0 = 0`; near the axis `age > S` by continuity of `ϱ`.) -/
def RingLiftVanish : Prop :=
  ∀ (S R τ : ℝ) (b : ℝ × (ℝ × ℝ) → Axi.Merid), 0 < S → 1 ≤ R →
    (∀ x : ℝ × (ℝ × ℝ), S < x.1 → b x = 0) →
    ∀ y : Space, (y ∈ Axi.axis ∨ S < Axi.age R y) → Axi.Nv R b τ =ᶠ[𝓝 y] 0

/-- **Leaf B (chart jets, SP 2346-2366).** On `{y ∉ axis, age R y < S}` the chart `(s, ξ, η)` has
derivatives of every order `j ≥ 1` bounded by `C_j (1+S)^{k_j} (1 + |η(y)|)`, uniformly in `R ≥ 1`,
`τ`: with `t = ϱ⁻¹ ≤ R t = √s < 1 + S`, `‖D^j s‖ ≲ R² t^{j+2} = s t^j`, `‖D^j ξ‖ ≲ R t^j`
(`j ≥ 1`), `‖D^j η‖ ≲ R|y₃| t^{j+1} + R t^j = |η| t^j + R t^j`. -/
def ChartJets : Prop :=
  ∀ j : ℕ, 1 ≤ j → ∃ (C : ℝ) (k : ℕ), 0 < C ∧
    ∀ (S R τ : ℝ), 0 < S → 1 ≤ R → ∀ y : Space, y ∉ Axi.axis → Axi.age R y < S →
      ‖iteratedFDeriv ℝ j (Axi.chart R τ) y‖ ≤ C * (1 + S) ^ k * (1 + |Axi.trans R y|)

/-- **Leaf C (amplitude and frame jets).** Same region: `√age` and the frame `e_r ⊗ ·+ e₃ ⊗ ·`
have derivatives of every order `j` bounded by `C_j (1+S)^{k_j}` (`‖∂^j e_r‖ ≲ ϱ^{-j} ≤ S^{j/2}`). -/
def SqrtFrameJets : Prop :=
  ∀ j : ℕ, ∃ (C : ℝ) (k : ℕ), 0 < C ∧
    ∀ (S R : ℝ), 0 < S → 1 ≤ R → ∀ y : Space, y ∉ Axi.axis → Axi.age R y < S →
      ‖iteratedFDeriv ℝ j (fun z => √(Axi.age R z)) y‖ ≤ C * (1 + S) ^ k ∧
      ‖iteratedFDeriv ℝ j Axi.frameL y‖ ≤ C * (1 + S) ^ k

/-- **Leaf D (off-axis jet bound).** The statement of `RingLiftJet` at off-axis points with
`age ≤ S` (SP 2360-2366, 2386-2387): if the profile jets of order `≤ j` satisfy
`(1+|η|)^j ‖D^l b‖ ≤ M`, then `‖D^j N_v b(τ, y)‖ ≤ C_j (1+S)^{k_j} M`.  Faà di Bruno
(`norm_iteratedFDerivWithin_comp_le`) for `b ∘ chart` with `ChartJets` (the `l`-th chart derivative
carries one factor `1+|η|`, at most `j` of them occur), then Leibniz
(`norm_iteratedFDerivWithin_smul_le`, `norm_iteratedFDerivWithin_clm_apply`) with `SqrtFrameJets`, all
on the open set `axisᶜ` at the point `y` (bounds taken at level `S + 1 > age R y`). -/
def RingLiftOffAxis : Prop :=
  ∀ j : ℕ, ∃ (C : ℝ) (k : ℕ), 0 < C ∧
    ∀ (S R τ M : ℝ) (b : ℝ × (ℝ × ℝ) → Axi.Merid), 0 < S → 1 ≤ R → 0 ≤ M →
      ContDiff ℝ ∞ b → (∀ x : ℝ × (ℝ × ℝ), S < x.1 → b x = 0) →
      (∀ l ≤ j, ∀ x : ℝ × (ℝ × ℝ), (1 + |x.2.2|) ^ j * ‖iteratedFDeriv ℝ l b x‖ ≤ M) →
      ∀ y : Space, y ∉ Axi.axis → Axi.age R y ≤ S →
        ‖iteratedFDeriv ℝ j (Axi.Nv R b τ) y‖ ≤ C * (1 + S) ^ k * M

/-- `RingLiftJet` from the locality and off-axis leaves. -/
theorem ringLiftJet_of (hV : RingLiftVanish) (hD : RingLiftOffAxis) : RingLiftJet := by
  unfold RingLiftVanish at hV
  intro j
  obtain ⟨C, k, hC, h⟩ := hD j
  refine ⟨C, k, hC, ?_⟩
  intro S R τ M b hS hR hM hb hsupp hder y
  by_cases hy : y ∈ Axi.axis ∨ S < Axi.age R y
  · have hev := hV S R τ b hS hR hsupp y hy
    have h0 : iteratedFDeriv ℝ j (Axi.Nv R b τ) y = iteratedFDeriv ℝ j (0 : Space → Space) y :=
      (hev.iteratedFDeriv ℝ j).self_of_nhds
    rw [h0, show (0 : Space → Space) = fun _ => 0 from rfl, iteratedFDeriv_fun_zero]
    have : 0 ≤ C * (1 + S) ^ k * M := by positivity
    simpa using this
  · push Not at hy
    exact h S R τ M b hS hR hM hb hsupp hder y hy.1 hy.2

end UnforcedLeray.Short.IIb
