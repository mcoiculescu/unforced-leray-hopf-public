import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.Sub.PartIIIa_T21_2_7_2_1_2_1_3
import UnforcedLeray.Short.PartIIIa.Sub.T18_2_4_2

/-!
# `PartIII-a:T21/2/7/2/1/2/1/3/3`: `SmoothAeJet` from three analytic leaves

Source of record: `the November 2 reference manuscript` (SP) lines 3060-3061 (the
weighted `H^j_{-m}` energies of the reverse-time adjoint; their weak spatial derivatives are the
classical ones for the smooth version).

The classical spatial partials `∂^w h` of a smooth `c`-periodic `h` that equals a cell jet almost
everywhere are the weak derivative fields.  Three analytic facts are used:
`PdCxPeriodic` (the derivative of a periodic smooth function is periodic), `IbpPdCxWeak` (classical
derivatives are weak cell derivatives; integration by parts, no seam term), and
`WeakCellAeUnique` (weak cell derivatives are unique almost everywhere on the cell; fundamental
lemma on the cylinder).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **Leaf**: the classical derivative of a smooth `c`-periodic function is `c`-periodic
(differentiate `g (· + (c, 0)) = g`). -/
def PdCxPeriodic : Prop :=
  ∀ (c : ℝ) (k : Fin 2) (g : ℝ × ℝ → ℂ), ContDiff ℝ ∞ g →
    (∀ x : ℝ × ℝ, g (x.1 + c, x.2) = g x) →
    ∀ x : ℝ × ℝ, pdCx k g (x.1 + c, x.2) = pdCx k g x

/-- **Leaf**: a smooth `c`-periodic function `g` has weak cell derivative `pdCx j g`
(integrate by parts against a cylinder test `ψ`: `g ψ` is smooth, `c`-periodic and vanishes for
`|η|` large, so `∫_cell ∂_j (g ψ) = 0` as in `B0579.integral_pd_eq_zero`; both pairings are
integrable because the cell has finite width and `ψ`, `∂_jψ` are bounded with bounded `η`-support;
split `g` into real and imaginary parts or redo the argument for complex fields). -/
def IbpPdCxWeak : Prop :=
  ∀ (c : ℝ) (j : Fin 2) (g : ℝ × ℝ → ℂ), 0 < c → ContDiff ℝ ∞ g →
    (∀ x : ℝ × ℝ, g (x.1 + c, x.2) = g x) → HasWeakCellDerivC c j g (pdCx j g)

/-- **Leaf**: weak cell derivatives are unique almost everywhere on the cell (the difference
`g₁ - g₂` is integrable against, and has zero integral against, every cylinder test; this makes
it locally integrable on the cell and the fundamental lemma applies, e.g.
`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` on the open strip `(-c/2, c/2) × ℝ` with
periodization of the compactly supported tests). -/
def WeakCellAeUnique : Prop :=
  ∀ (c : ℝ) (j : Fin 2) (φ g₁ g₂ : ℝ × ℝ → ℂ), HasWeakCellDerivC c j φ g₁ →
    HasWeakCellDerivC c j φ g₂ → g₁ =ᵐ[volume.restrict (B0579.cell c)] g₂

theorem contDiff_pdCx {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (k : Fin 2) :
    ContDiff ℝ ∞ (pdCx k g) :=
  ((contDiff_infty_iff_fderiv.1 hg).2).clm_apply contDiff_const

theorem contDiff_adjSpatial {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (w : List (Fin 2)) :
    ContDiff ℝ ∞ (adjSpatial w g) := by
  induction w with
  | nil => exact hg
  | cons k w ih => exact contDiff_pdCx ih k

theorem smoothAeJet_of (hI : IbpPdCxWeak) (hU : WeakCellAeUnique) (hP : PdCxPeriodic) :
    SmoothAeJet := by
  intro c m K h f D hc hh hJ hae w hw
  have hf : ∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x := by
    have := hJ.periodic [] (Nat.zero_le _)
    rw [hJ.base] at this
    exact this
  have hper0 : ∀ x : ℝ × ℝ, h (x.1 + c, x.2) = h x :=
    adjPeriodic_of_ae_eq hh.continuous hae hf
  have hper : ∀ w : List (Fin 2), ∀ x : ℝ × ℝ,
      adjSpatial w h (x.1 + c, x.2) = adjSpatial w h x := by
    intro w
    induction w with
    | nil => exact hper0
    | cons k w ih => exact hP c k _ (contDiff_adjSpatial hh w) ih
  have hcell : ∀ w : List (Fin 2), w.length ≤ K →
      adjSpatial w h =ᵐ[volume.restrict (B0579.cell c)] D w := by
    intro w
    induction w with
    | nil =>
      intro _
      have : D [] = f := hJ.base
      rw [this]
      exact ae_restrict_of_ae hae
    | cons k w ih =>
      intro hw
      have hlt : w.length < K := by simpa using hw
      have h1 := hI c k (adjSpatial w h) hc (contDiff_adjSpatial hh w) (hper w)
      have h1' : HasWeakCellDerivC c k (D w) (adjSpatial (k :: w) h) :=
        HasWeakCellDerivC.congr_ae (ih hlt.le).symm (Eventually.of_forall fun _ => rfl) h1
      exact hU c k (D w) _ _ h1' (hJ.deriv k w hlt)
  exact ⟨hper w, periodicAeOfCell c hc _ _ (hper w) (hJ.periodic w hw) (hcell w hw)⟩

end UnforcedLeray.Short.IIIa
