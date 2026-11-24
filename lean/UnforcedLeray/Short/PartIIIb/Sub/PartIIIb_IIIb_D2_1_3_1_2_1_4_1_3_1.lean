import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1_3

/-!
# `selMollify`: decomposition

Source `the November 2 reference manuscript` lines 1334-1337, 1351-1362, 1470-1480.
Mollification in `y` with an even, nonnegative, smooth, compactly supported bump of integral one,
`η_n(y) = (n+1)³ η((n+1) y)`.  Five independent analytic facts, then the assembly `selMollify_of`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- A mollifier: smooth, compactly supported, even, nonnegative, integral one. -/
def IsMollifier (η : Space → ℝ) : Prop :=
  ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ (∀ y, η (-y) = η y) ∧ (∀ y, 0 ≤ η y) ∧
    ∫ y : Space, η y = 1

/-- Rescaled mollifier `η_n(y) = (n+1)³ η((n+1) y)`. -/
def molScale (η : Space → ℝ) (n : ℕ) (y : Space) : ℝ :=
  ((n : ℝ) + 1) ^ 3 * η (((n : ℝ) + 1) • y)

/-- `y`-convolution of a field with a scalar kernel: `(K *_y Φ)(t, y) = ∫ K(y - z) Φ(t, z) dz`. -/
def convYMol (K : Space → ℝ) (Φ : ℝ × Space → CVec3) : ℝ × Space → CVec3 :=
  fun x => ∫ z : Space, K (x.2 - z) • Φ (x.1, z)

/-- `y`-convolution with the `j`-th partial derivative of the kernel. -/
def convDY (K : Space → ℝ) (j : Fin 3) (Φ : ℝ × Space → CVec3) : ℝ × Space → CVec3 :=
  fun x => ∫ z : Space, (fderiv ℝ K (x.2 - z) (EuclideanSpace.single j (1 : ℝ))) • Φ (x.1, z)

/-- (1) A mollifier exists (source 1351-1362): `ContDiffBump` on `ℝ³`, symmetrised
`(b(y) + b(-y))/2` and normalised by its integral. -/
def MollExists : Prop := ∃ η : Space → ℝ, IsMollifier η

/-- (2) Young in `y` (source 1351-1362): for a mollifier kernel `K` (smooth, compactly supported,
`∫|K| ≤ 1`) and `Φ ∈ Y_2`, the fields `K *_y Φ` and `(∂ⱼK) *_y Φ` lie in `Y_2` (periodic a.e.
from periodicity of `Φ`, jointly `AEStronglyMeasurable` by Fubini–Tonelli measurability of the
parametric integral, finite norm by Minkowski's integral inequality), and
`‖K *_y Φ‖_{Y_2} ≤ (∫|K|) ‖Φ‖_{Y_2}`, `‖(∂ⱼK) *_y Φ‖_{Y_2} ≤ (∫|∂ⱼK|) ‖Φ‖_{Y_2}`. -/
def ConvYMembership : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ (K : Space → ℝ), ContDiff ℝ ∞ K → HasCompactSupport K →
    ∀ Φ : ℝ × Space → CVec3, UnforcedLeray.Short.IIb.IsInYr P 2 Φ →
      UnforcedLeray.Short.IIb.IsInYr P 2 (convYMol K Φ) ∧
      (∀ j, UnforcedLeray.Short.IIb.IsInYr P 2 (convDY K j Φ)) ∧
      UnforcedLeray.Short.IIb.phaseLpNorm P 2 (convYMol K Φ)
        ≤ ENNReal.ofReal (∫ y : Space, |K y|) * UnforcedLeray.Short.IIb.phaseLpNorm P 2 Φ

/-- (3) Approximate identity in `Y_2` (source 1351-1362): for a mollifier `η` and `Φ ∈ Y_2`,
`η_n *_y Φ → Φ` in `Y_2` (approximate identity in `L²(ℝ³)` for a.e. slice, Young bound
`‖η_n * f‖ ≤ ‖f‖`, dominated convergence in `τ ∈ (0,P]`). -/
def ConvYApprox : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ η : Space → ℝ, IsMollifier η →
    ∀ Φ : ℝ × Space → CVec3, UnforcedLeray.Short.IIb.IsInYr P 2 Φ →
      YConv P (fun n => convYMol (molScale η n) Φ) Φ

/-- (4) The slice Laplacian identity survives mollification (source 1351-1362): if
`ν ∫ Φ(τ)·Δθ = ∫ a(τ)·θ` for a.e. `τ` (with `Φ, a ∈ Y_2`) then the same holds for
`(η_n *_y Φ, η_n *_y a)`.  Fubini (a.e. slice in `L²`, `η_n` compactly supported bounded) and
evenness of `η_n`: `∫ (η_n * Φ)·Δθ = ∫ Φ·Δ(η_n * θ)` with `η_n * θ` smooth compactly supported
and `Δ(η_n * θ) = η_n * Δθ`. -/
def ConvYSliceId : Prop :=
  ∀ (P ν : ℝ), 0 < P → 0 < ν → ∀ η : Space → ℝ, IsMollifier η →
    ∀ (n : ℕ) (Φ a : ℝ × Space → CVec3),
      UnforcedLeray.Short.IIb.IsInYr P 2 Φ → UnforcedLeray.Short.IIb.IsInYr P 2 a →
      SliceLapId ν Φ a →
        SliceLapId ν (convYMol (molScale η n) Φ) (convYMol (molScale η n) a)

/-- (5) The slice derivative of the mollified field (source 1351-1362): for a.e. `τ`,
`((∂ⱼη_n) *_y Φ)(τ)` is the weak `∂ⱼ`-derivative of `(η_n *_y Φ)(τ)` (it is the classical
derivative of a smooth function: differentiation under the integral, then
`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`, Fubini with the test function). -/
def ConvYWeakD : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ (K : Space → ℝ), ContDiff ℝ ∞ K → HasCompactSupport K →
    ∀ Φ : ℝ × Space → CVec3, UnforcedLeray.Short.IIb.IsInYr P 2 Φ → ∀ j : Fin 3,
      SliceWeakD (convYMol K Φ) j (convDY K j Φ)

theorem selMollify_of (h1 : MollExists) (h2 : ConvYMembership) (h3 : ConvYApprox)
    (h4 : ConvYSliceId) (h5 : ConvYWeakD) : SelMollify := by
  intro P ν hP hν Φ a hΦ ha hid
  obtain ⟨η, hη⟩ := h1
  have hs : ∀ n, ContDiff ℝ ∞ (molScale η n) ∧ HasCompactSupport (molScale η n) := by
    intro n
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    refine ⟨?_, ?_⟩
    · unfold molScale
      exact contDiff_const.mul (hη.1.comp (contDiff_const_smul _))
    · unfold molScale
      have := (hη.2.1.comp_isClosedEmbedding
        ((Homeomorph.smulOfNeZero ((n : ℝ) + 1) hn).isClosedEmbedding))
      exact this.mul_left
  refine ⟨fun n => convYMol (molScale η n) Φ, fun n => convYMol (molScale η n) a,
    fun n j => convDY (molScale η n) j Φ, ?_, ?_, ?_, h3 P hP η hη Φ hΦ, h3 P hP η hη a ha,
    fun n => h4 P ν hP hν η hη n Φ a hΦ ha hid, fun n j => h5 P hP _ (hs n).1 (hs n).2 Φ hΦ j⟩
  · exact fun n => (h2 P hP _ (hs n).1 (hs n).2 Φ hΦ).1
  · exact fun n => (h2 P hP _ (hs n).1 (hs n).2 a ha).1
  · exact fun n j => (h2 P hP _ (hs n).1 (hs n).2 Φ hΦ).2.1 j

end UnforcedLeray.Short.PartIIIb.Concrete
