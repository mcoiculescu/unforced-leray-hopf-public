import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1

/-!
# `sliceSelect`: decomposition

Source `the November 2 reference manuscript` lines 1334-1337, 1351-1362, 1470-1480.
Mollify in `y`, show the slice derivatives of the mollified fields are Cauchy in `Y_2` (one-slice
`H¹` bound, `SliceH1`), pass to the `Y_2` limit and identify it as the slice weak derivative.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Slice Laplacian identity `ν ∫ Φ(τ)·Δθ = ∫ a(τ)·θ` for a.e. `τ` and all smooth compactly
supported tests `θ` (source 1351-1362). -/
def SliceLapId (ν : ℝ) (Φ a : ℝ × Space → CVec3) : Prop :=
  ∀ᵐ τ : ℝ, ∀ θ : Space → CVec3, ContDiff ℝ ∞ θ → HasCompactSupport θ →
    ν * (∫ y : Space, ∑ i : Fin 3, Φ (τ, y) i * lapS θ y i)
      = ∫ y : Space, ∑ i : Fin 3, a (τ, y) i * θ y i

/-- `G(τ)` is the weak `∂ⱼ`-derivative of `Φ(τ)` for a.e. `τ` (source 1351-1362). -/
def SliceWeakD (Φ : ℝ × Space → CVec3) (j : Fin 3) (G : ℝ × Space → CVec3) : Prop :=
  ∀ᵐ τ : ℝ, ∀ θ : Space → CVec3, ContDiff ℝ ∞ θ → HasCompactSupport θ →
    -(∫ y : Space, ∑ i : Fin 3,
        Φ (τ, y) i * fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single j (1 : ℝ)))
      = ∫ y : Space, ∑ i : Fin 3, G (τ, y) i * θ y i

/-- Convergence in `Y_2`: `‖Ψ n - Φ‖_{Y_2} → 0` (norm of source 1341-1344). -/
def YConv (P : ℝ) (Ψ : ℕ → ℝ × Space → CVec3) (Φ : ℝ × Space → CVec3) : Prop :=
  Tendsto (fun n => UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => Ψ n x - Φ x))
    atTop (nhds 0)

/-- Cauchy sequence in `Y_2`. -/
def YCauchy (P : ℝ) (f : ℕ → ℝ × Space → CVec3) : Prop :=
  ∀ ε : ENNReal, 0 < ε → ∃ N : ℕ, ∀ n m, N ≤ n → N ≤ m →
    UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => f n x - f m x) < ε

/-- (1) Mollification in `y` (source 1351-1362): `Ψₙ = η_{1/n} *_y Φ`, `Aₙ = η_{1/n} *_y a`,
`Dₙⱼ = ∂ⱼΨₙ = (∂ⱼη_{1/n}) *_y Φ` are periodic jointly measurable members of `Y_2`
(Minkowski/Young in `y`), `Ψₙ → Φ`, `Aₙ → a` in `Y_2` (approximate identity per slice, dominated
convergence in `τ`), the slice identity `ν ∫ Ψₙ·Δθ = ∫ Aₙ·θ` holds (Fubini, symmetric mollifier),
and `Dₙⱼ(τ)` is the weak derivative of `Ψₙ(τ)` (it is the classical derivative of a smooth
slice; integration by parts). -/
def SelMollify : Prop :=
  ∀ (P ν : ℝ), 0 < P → 0 < ν → ∀ Φ a : ℝ × Space → CVec3,
    UnforcedLeray.Short.IIb.IsInYr P 2 Φ → UnforcedLeray.Short.IIb.IsInYr P 2 a →
    SliceLapId ν Φ a →
      ∃ (Ψ A : ℕ → ℝ × Space → CVec3) (D : ℕ → Fin 3 → ℝ × Space → CVec3),
        (∀ n, UnforcedLeray.Short.IIb.IsInYr P 2 (Ψ n)) ∧
        (∀ n, UnforcedLeray.Short.IIb.IsInYr P 2 (A n)) ∧
        (∀ n j, UnforcedLeray.Short.IIb.IsInYr P 2 (D n j)) ∧
        YConv P Ψ Φ ∧ YConv P A a ∧
        (∀ n, SliceLapId ν (Ψ n) (A n)) ∧
        (∀ n j, SliceWeakD (Ψ n) j (D n j))

/-- (2) Cauchy property of the derivatives (source 1351-1362, 1470-1480): apply `sliceH1`
(file `Slice/H1.lean`) on a.e. slice to `f = Ψₙ(τ) - Ψₘ(τ)`, `h = ν⁻¹(Aₙ(τ) - Aₘ(τ))`; the
resulting `L²` weak derivative equals `Dₙⱼ(τ) - Dₘⱼ(τ)` a.e. (uniqueness of weak derivatives, i.e.
`ae_eq_zero_of_integral_contDiff_smul_eq_zero`-type argument on `ℝ³`), so
`∑ⱼ ‖Dₙⱼ(τ) - Dₘⱼ(τ)‖² ≤ ν⁻¹ ‖Ψₙ(τ)-Ψₘ(τ)‖ ‖Aₙ(τ)-Aₘ(τ)‖`; integrate over a period with
Cauchy–Schwarz in `τ`: `∑ⱼ ‖Dₙⱼ-Dₘⱼ‖²_{Y_2} ≤ ν⁻¹ ‖Ψₙ-Ψₘ‖_{Y_2} ‖Aₙ-Aₘ‖_{Y_2}`, and
`Ψₙ`, `Aₙ` are Cauchy in `Y_2` since convergent. -/
def SelCauchy : Prop :=
  ∀ (P ν : ℝ), 0 < P → 0 < ν → ∀ (Φ a : ℝ × Space → CVec3)
    (Ψ A : ℕ → ℝ × Space → CVec3) (D : ℕ → Fin 3 → ℝ × Space → CVec3),
    UnforcedLeray.Short.IIb.IsInYr P 2 Φ → UnforcedLeray.Short.IIb.IsInYr P 2 a →
    (∀ n, UnforcedLeray.Short.IIb.IsInYr P 2 (Ψ n)) →
    (∀ n, UnforcedLeray.Short.IIb.IsInYr P 2 (A n)) →
    (∀ n j, UnforcedLeray.Short.IIb.IsInYr P 2 (D n j)) →
    YConv P Ψ Φ → YConv P A a →
    (∀ n, SliceLapId ν (Ψ n) (A n)) →
    (∀ n j, SliceWeakD (Ψ n) j (D n j)) →
      ∀ j, YCauchy P (fun n => D n j)

/-- (3) Completeness of `Y_2` (jointly measurable periodic representative): a Cauchy sequence of
members of `Y_2` converges in `Y_2` to a member of `Y_2` (source 1341-1344; `Y_2` is an `L²`
space over `(0,P] × ℝ³` on periodic functions; periodicity of the limit from a.e. periodicity along
an a.e.-convergent subsequence). -/
def SelComplete : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ f : ℕ → ℝ × Space → CVec3,
    (∀ n, UnforcedLeray.Short.IIb.IsInYr P 2 (f n)) → YCauchy P f →
      ∃ F : ℝ × Space → CVec3, UnforcedLeray.Short.IIb.IsInYr P 2 F ∧ YConv P f F

/-- (4) Limit identification (source 1351-1362): if `Ψₙ → Φ` and `Dₙ → F` in `Y_2` and `Dₙ(τ)` is
the weak `∂ⱼ`-derivative of `Ψₙ(τ)`, then `F(τ)` is the weak `∂ⱼ`-derivative of `Φ(τ)` for a.e.
`τ`.  Sketch: `Y_2` convergence gives a subsequence along which, for a.e. `τ`, both slices
converge in `L²(ℝ³)`; pass to the limit in `-∫ Ψₙ ∂ⱼθ = ∫ Dₙ θ` for every `θ` (the null set only
concerns the subsequence, not `θ`). -/
def SelLimit : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ (Φ F : ℝ × Space → CVec3) (Ψ : ℕ → ℝ × Space → CVec3)
    (D : ℕ → ℝ × Space → CVec3) (j : Fin 3),
    UnforcedLeray.Short.IIb.IsInYr P 2 Φ → UnforcedLeray.Short.IIb.IsInYr P 2 F →
    (∀ n, UnforcedLeray.Short.IIb.IsInYr P 2 (Ψ n)) →
    (∀ n, UnforcedLeray.Short.IIb.IsInYr P 2 (D n)) →
    YConv P Ψ Φ → YConv P D F →
    (∀ n, SliceWeakD (Ψ n) j (D n)) → SliceWeakD Φ j F

theorem sliceSelect_of (h1 : SelMollify) (h2 : SelCauchy) (h3 : SelComplete) (h4 : SelLimit) :
    SliceSelect := by
  intro P ν hP hν Φ a hΦ ha hid
  obtain ⟨Ψ, A, D, hΨ, hA, hD, hΨΦ, hAa, hlap, hwk⟩ := h1 P ν hP hν Φ a hΦ ha hid
  have hC := h2 P ν hP hν Φ a Ψ A D hΦ ha hΨ hA hD hΨΦ hAa hlap hwk
  have hF : ∀ j : Fin 3, ∃ F : ℝ × Space → CVec3,
      UnforcedLeray.Short.IIb.IsInYr P 2 F ∧ YConv P (fun n => D n j) F :=
    fun j => h3 P hP (fun n => D n j) (fun n => hD n j) (hC j)
  choose F hFY hFc using hF
  exact ⟨F, fun j => ⟨hFY j, h4 P hP Φ (F j) Ψ (fun n => D n j) j hΦ (hFY j) hΨ
    (fun n => hD n j) hΨΦ (hFc j) (fun n => hwk n j)⟩⟩

end UnforcedLeray.Short.PartIIIb.Concrete
