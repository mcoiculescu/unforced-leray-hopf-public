import UnforcedLeray.Short.PartIIa.Sub.N02_4_4

/-!
# Part II-a, task `PartII-a:N02/4/5` (`NzModeSolve`): decomposition into five lemma Props

Source of record: `the November 2 reference manuscript`, lines 1713-1722 (on a nonzero
`q`-frequency the flat field is `(φ_q, φ_η) + (-ψ_η, ψ_q)`, so the potentials solve the one-mode
system `i k φ - ∂_η ψ = a`, `∂_η φ + i k ψ = b`).

Route. `G_k(t) = -e^{-|k||t|}/(2|k|)` is the Green kernel of `∂_t² - k²` (`G'' = k² G + δ`). Write
`conv h (s, η) = ∫ G_k(t) h(s, η - t) dt` (`nzConv`, convolution in `η`, `s` a parameter). With
`h₁ = i k a + ∂_η b`, `h₂ = i k b - ∂_η a` (smooth, compactly supported), take `φ = conv h₁`,
`ψ = conv h₂`. Derivatives in `η` fall on the data, the mixed terms `i k ∂_η b`, `i k ∂_η a` cancel,
and `G * (∂_η² u - k² u) = u` (`NzGreenKey2D`) gives both equations.

Leaves (new tasks, `PartII-a:N02/4/5/1-6`): `NzGreenKey1D` (the one-dimensional Green identity),
`NzGreenKey2D` (its `ℝ × ℝ` form, from `NzGreenKey1D`), `NzConvGenHyp` (the domination hypotheses of
the Green family, `N02_4_5/Gen.lean`), `NzConvFderiv` and `NzConvDecay` (from `NzConvGenHyp`),
`NzConvIntegrable`. `NzConvSmooth` follows from `NzConvGenHyp` (`nzConvSmooth_of`, `N02_4_5/Gen.lean`).

`nzModeSolve_of` (`N02_4_5/Cond.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- The Green kernel `G_k(t) = -e^{-|k||t|}/(2|k|)` of `∂_t² - k²`. -/
def nzGreen (k t : ℝ) : ℝ := -Real.exp (-|k| * |t|) / (2 * |k|)

/-- Convolution in `η` with the Green kernel, `s` a parameter:
`nzConv k h (s, η) = ∫ G_k(t) h(s, η - t) dt`. -/
def nzConv (k : ℝ) (h : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ := fun x =>
  ∫ t : ℝ, (nzGreen k t : ℂ) * h (x.1, x.2 - t)

/-! ### The lemma Props -/

/-- **Leaf `NzGreenKey1D`: the one-dimensional Green identity.** For `k ≠ 0` and `u ∈ C²_c(ℝ)`:
`∫ G_k(t) (u''(η - t) - k² u(η - t)) dt = u(η)`. Proof (variation of constants): substitute
`t ↦ η - t` (`G_k` is even), split the integral at `t = η`, integrate by parts twice on `(-∞, η]` and
`[η, ∞)` (`MeasureTheory.integral_Iic_mul_deriv_eq_deriv_mul`, `integral_Ioi_mul_deriv_eq_deriv_mul`);
the boundary terms at `η` come from the jump `G'(η+) - G'(η-) = 1` of `G_k'`, and `G'' = k² G` away
from `η` gives the cancellation. -/
def NzGreenKey1D : Prop :=
  ∀ (k : ℝ), k ≠ 0 → ∀ (u : ℝ → ℂ), ContDiff ℝ 2 u → HasCompactSupport u → ∀ η : ℝ,
    ∫ t : ℝ, (nzGreen k t : ℂ) * (iteratedDeriv 2 u (η - t) - (k : ℂ) ^ 2 * u (η - t)) = u η

/-- **Leaf `NzGreenKey2D`: the Green identity for smooth compactly supported data on `ℝ × ℝ`**
(`s` is a parameter): `conv (∂_η² a - k² a) = a`. Follows from `NzGreenKey1D` applied to
`u(t) = a(s, t)` (chain rule: `iteratedDeriv 2 u t = ∂_η(∂_η a)(s, t)`;
`HasCompactSupport u` from `HasCompactSupport.comp_isClosedEmbedding`). -/
def NzGreenKey2D : Prop :=
  ∀ (k : ℝ), k ≠ 0 → ∀ (a : ℝ × ℝ → ℂ), ContDiff ℝ ∞ a → HasCompactSupport a → ∀ x : ℝ × ℝ,
    nzConv k (fun q => fderiv ℝ (fun y => fderiv ℝ a y (0, 1)) q (0, 1) - (k : ℂ) ^ 2 * a q) x =
      a x

/-- **`NzConvSmooth` (follows from `NzConvGenHyp`, `nzConvSmooth_of` in `N02_4_5/Gen.lean`): the Green
convolution of smooth compactly supported data is smooth in `(s, η)`.** Differentiation under the integral with the integrable majorant
`|G_k(t)| · sup |D^j h|` (`G_k` is integrable with `∫|G_k| = 1/k²`; `D^j h` is bounded since `h` is
smooth with compact support; `iteratedFDeriv_comp_add_right` for the translate). Mathlib route:
`ParamIntegralSmoothAux.pm_contDiff` in `Tasks/F05aAdjResolventSolution/ParamIntegralSmooth.lean`
(generic target space, family `t ↦ h(s, η - t)` of `ℝ × ℝ`-functions with the measure
`G_k(t) dt` or with the factor `G_k(t)` inside), or `contDiffOn_integral` in
`Loc/L09CompactDatum/ParamIntegral.lean`. -/
def NzConvSmooth : Prop :=
  ∀ k : ℝ, k ≠ 0 → ∀ h : ℝ × ℝ → ℂ, ContDiff ℝ ∞ h → HasCompactSupport h →
    ContDiff ℝ ∞ (nzConv k h)

/-- **Leaf `NzConvFderiv` (from `NzConvGenHyp`): `∂_η` commutes with the Green convolution** (derivative under the integral;
`fderiv (fun x => h (x.1, x.2 - t)) x (0, 1) = fderiv h (x.1, x.2 - t) (0, 1)`). -/
def NzConvFderiv : Prop :=
  ∀ k : ℝ, k ≠ 0 → ∀ h : ℝ × ℝ → ℂ, ContDiff ℝ ∞ h → HasCompactSupport h → ∀ x : ℝ × ℝ,
    fderiv ℝ (nzConv k h) x (0, 1) = nzConv k (fun q => fderiv ℝ h q (0, 1)) x

/-- **Leaf `NzConvIntegrable`: the convolution integrand is integrable** (continuous compactly
supported `h` is bounded; `G_k` is integrable: `∫ e^{-|k||t|} dt = 2/|k|`; `Integrable.bdd_mul`). -/
def NzConvIntegrable : Prop :=
  ∀ k : ℝ, k ≠ 0 → ∀ h : ℝ × ℝ → ℂ, Continuous h → HasCompactSupport h → ∀ x : ℝ × ℝ,
    Integrable (fun t : ℝ => (nzGreen k t : ℂ) * h (x.1, x.2 - t))

/-- **Leaf `NzConvDecay` (from `NzConvGenHyp`): exponential decay of the convolution and its derivatives.** For smooth `h`
with compact support in `|η| ≤ L` and every order `m`, `‖D^m (conv h)(s, η)‖ ≤ C e^{-|k||η|}`.
Proof: `D^m (conv h) = conv (D^m h)` (the derivatives fall on `h`; the `CLM`-valued version of
`NzConvFderiv`, or `ParamIntegralSmoothAux.pm_deriv_formula`); for `|η| ≥ L` the integrand is
supported in `|t| ≥ |η| - L`, where `|G_k(t)| ≤ e^{-|k||t|}/(2|k|)`, so the integral is at most
`sup‖D^m h‖ · vol · e^{-|k|(|η| - L)}/(2|k|)` (use `∫_{|t| ≥ r} e^{-|k||t|} dt = 2 e^{-|k|r}/|k|`);
for `|η| ≤ L` use the bound `sup‖D^m h‖ ∫|G_k|` and `e^{-|k||η|} ≥ e^{-|k|L}`. -/
def NzConvDecay : Prop :=
  ∀ k : ℝ, k ≠ 0 → ∀ h : ℝ × ℝ → ℂ, ContDiff ℝ ∞ h → HasCompactSupport h → ∀ m : ℕ,
    ∃ C : ℝ, ∀ x : ℝ × ℝ, ‖iteratedFDeriv ℝ m (nzConv k h) x‖ ≤ C * Real.exp (-|k| * |x.2|)

/-! ### Band bookkeeping -/

/-- Joint band support in the `s`-band `[s₀, s₁]` and `|η| ≤ L`. -/
def NzBandJ (s0 s1 L : ℝ) (g : ℝ × ℝ → ℂ) : Prop :=
  ∀ x : ℝ × ℝ, g x ≠ 0 → x.1 ∈ Icc s0 s1 ∧ |x.2| ≤ L

theorem NzBandJ.mono {s0 s1 L s0' s1' L' : ℝ} {g : ℝ × ℝ → ℂ} (h : NzBandJ s0 s1 L g)
    (h0 : s0' ≤ s0) (h1 : s1 ≤ s1') (hL : L ≤ L') : NzBandJ s0' s1' L' g := fun x hx =>
  let ⟨⟨a, b⟩, c⟩ := h x hx
  ⟨⟨h0.trans a, b.trans h1⟩, c.trans hL⟩

theorem NzBandJ.const_mul {s0 s1 L : ℝ} {g : ℝ × ℝ → ℂ} (h : NzBandJ s0 s1 L g) (z : ℂ) :
    NzBandJ s0 s1 L (fun q => z * g q) := fun x hx =>
  h x fun h0 => hx (by simp [h0])

theorem NzBandJ.add {s0 s1 L : ℝ} {g g' : ℝ × ℝ → ℂ} (h : NzBandJ s0 s1 L g)
    (h' : NzBandJ s0 s1 L g') : NzBandJ s0 s1 L (fun q => g q + g' q) := fun x hx => by
  by_cases h0 : g x = 0
  · exact h' x fun h1 => hx (by simp [h0, h1])
  · exact h x h0

theorem NzBandJ.sub {s0 s1 L : ℝ} {g g' : ℝ × ℝ → ℂ} (h : NzBandJ s0 s1 L g)
    (h' : NzBandJ s0 s1 L g') : NzBandJ s0 s1 L (fun q => g q - g' q) := fun x hx => by
  by_cases h0 : g x = 0
  · exact h' x fun h1 => hx (by simp [h0, h1])
  · exact h x h0

theorem NzBandJ.hasCompactSupport {s0 s1 L : ℝ} {g : ℝ × ℝ → ℂ} (h : NzBandJ s0 s1 L g) :
    HasCompactSupport g := by
  refine HasCompactSupport.intro (K := Icc s0 s1 ×ˢ Icc (-L) L)
    (isCompact_Icc.prod isCompact_Icc) fun x hx => ?_
  by_contra h0
  obtain ⟨h1, h2⟩ := h x h0
  exact hx ⟨h1, abs_le.1 h2⟩

theorem NzBandJ.dEta {s0 s1 L : ℝ} {g : ℝ × ℝ → ℂ} (h : NzBandJ s0 s1 L g) :
    NzBandJ s0 s1 L (fun q => fderiv ℝ g q (0, 1)) := by
  intro x hx
  by_contra hne
  apply hx
  have hclosed : IsClosed {q : ℝ × ℝ | q.1 ∈ Icc s0 s1 ∧ |q.2| ≤ L} :=
    (isClosed_Icc.preimage continuous_fst).inter
      (isClosed_le (continuous_abs.comp continuous_snd) continuous_const)
  have hev : g =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
    filter_upwards [hclosed.isOpen_compl.mem_nhds hne] with q hq
    by_contra h0
    exact hq (h q h0)
  have hz : fderiv ℝ g x = 0 := by
    rw [hev.fderiv_eq]
    exact fderiv_const_apply _
  simp [hz]

theorem nzms_dEta_smooth {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun q => fderiv ℝ g q (0, 1)) :=
  (hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-! ### Linearity of the convolution -/

theorem nzConv_const_mul (k : ℝ) (z : ℂ) (h : ℝ × ℝ → ℂ) (x : ℝ × ℝ) :
    nzConv k (fun q => z * h q) x = z * nzConv k h x := by
  unfold nzConv
  rw [← integral_const_mul]
  congr 1
  funext t
  ring

theorem nzConv_add (hI : NzConvIntegrable) {k : ℝ} (hk : k ≠ 0) {h h' : ℝ × ℝ → ℂ}
    (hc : Continuous h) (hcs : HasCompactSupport h) (hc' : Continuous h')
    (hcs' : HasCompactSupport h') (x : ℝ × ℝ) :
    nzConv k (fun q => h q + h' q) x = nzConv k h x + nzConv k h' x := by
  unfold nzConv
  rw [← integral_add (hI k hk h hc hcs x) (hI k hk h' hc' hcs' x)]
  congr 1
  funext t
  ring

theorem nzConv_sub (hI : NzConvIntegrable) {k : ℝ} (hk : k ≠ 0) {h h' : ℝ × ℝ → ℂ}
    (hc : Continuous h) (hcs : HasCompactSupport h) (hc' : Continuous h')
    (hcs' : HasCompactSupport h') (x : ℝ × ℝ) :
    nzConv k (fun q => h q - h' q) x = nzConv k h x - nzConv k h' x := by
  unfold nzConv
  rw [← integral_sub (hI k hk h hc hcs x) (hI k hk h' hc' hcs' x)]
  congr 1
  funext t
  ring

theorem nzConv_eq_zero {k : ℝ} {s0 s1 : ℝ} {h : ℝ × ℝ → ℂ}
    (hb : ∀ y : ℝ × ℝ, h y ≠ 0 → y.1 ∈ Icc s0 s1) {x : ℝ × ℝ} (hx : x.1 ∉ Icc s0 s1) :
    nzConv k h x = 0 := by
  unfold nzConv
  have : ∀ t : ℝ, h (x.1, x.2 - t) = 0 := fun t => by
    by_contra h0
    exact hx (hb (x.1, x.2 - t) h0)
  simp [this]

end UnforcedLeray.Short.PartIIa
