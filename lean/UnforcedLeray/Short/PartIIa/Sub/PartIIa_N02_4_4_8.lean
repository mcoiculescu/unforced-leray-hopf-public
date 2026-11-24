import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Set
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N02_4_4

/-!
# Part II-a, task `PartII-a:N02/4/4/8` (`NzFpParsevalMerid`): decomposition into lemma Props

Source of record: `the November 2 reference manuscript`, lines 1713-1727 and 1744-1745.

The `ℂ²`-valued Parseval is the scalar Parseval `NzFpParseval` (task `PartII-a:N02/4/4/7`) applied to the
two coordinate mode sums, since `‖v‖² = ‖v 0‖² + ‖v 1‖²` and `opS^[α]` commutes with taking coordinates.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-- A smooth scalar function with `s`-band and compact `η`-support satisfies `NzDecay1`
(`‖g‖` and `‖∂_s g‖` are continuous, hence bounded on the compact set `[s0, s1] × [-L, L]` by some `C`;
they vanish outside it, so the bound `C e^{-κ|η|}` holds with `κ = 1`, `C' = C e^{L}`; note
`g = 0` on a neighbourhood of every point outside the closed support, so `fderiv g = 0` there). -/
def NzFpBand2Decay1 : Prop :=
  ∀ g : ℝ × ℝ → ℂ, ContDiff ℝ ∞ g → NzBand2 g → NzDecay1 g

/-- `opS^[α]` (`α ∈ {0, 1}`) of a `ℂ²`-valued finite mode sum, read in coordinate `i`, is `opS^[α]` of
the scalar mode sum of the `i`-th coordinates (`opS f p = p.1 • fderiv f p (1,0,0)`; coordinates are
continuous linear, so commute with `fderiv`; for `α = 1` use `nzfpOpSModeSum` or `nzfpPdS`). -/
def NzFpMeridOpS : Prop :=
  ∀ (c : ℝ) (M : Finset ℤ) (a : ℤ → ℝ × ℝ → MeridC), (∀ n ∈ M, ContDiff ℝ ∞ (a n)) →
    ∀ α ∈ Finset.range 2, ∀ (i : Fin 2) (p : Profile),
      (opS^[α] (nzModeSum c M a)) p i =
        (opS^[α] (nzModeSum c M (fun n x => a n x i))) p

/-- **`NzFpParsevalMerid` from the scalar Parseval and the two Props above.** -/
theorem nzFpParsevalMerid_of (h7 : NzFpParseval) (h1 : NzFpBand2Decay1) (h2 : NzFpMeridOpS) :
    NzFpParsevalMerid := by
  intro c hc M a ha α hα i hi
  have hsm : ∀ n ∈ M, ContDiff ℝ ∞ (a n) := fun n hn => (ha n hn).1
  have hcomp : ∀ (k : Fin 2) (n : ℤ), n ∈ M → NzDecay1 (fun x => a n x k) := by
    intro k n hn
    obtain ⟨hsmooth, s0, s1, L, hs0, hsupp⟩ := ha n hn
    refine h1 _ ?_ ?_
    · exact ((EuclideanSpace.proj k : MeridC →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp hsmooth
    · refine ⟨s0, s1, L, hs0, fun x hx => hsupp x ?_⟩
      intro h0; apply hx; simp [h0]
  have P0 := h7 c hc M (fun n x => a n x 0) (fun n hn => hcomp 0 n hn)
  have P1 := h7 c hc M (fun n x => a n x 1) (fun n hn => hcomp 1 n hn)
  have hnorm : ∀ p : Profile, ‖(opS^[α] (nzModeSum c M a)) p‖ ^ 2 =
      ‖(opS^[α] (nzModeSum c M (fun n x => a n x 0))) p‖ ^ 2 +
        ‖(opS^[α] (nzModeSum c M (fun n x => a n x 1))) p‖ ^ 2 := by
    intro p
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, ← h2 c M a hsm α hα 0 p,
      ← h2 c M a hsm α hα 1 p]
  have I0 := (P0.1 α hα i hi)
  have I1 := (P1.1 α hα i hi)
  unfold nzSq
  have : (fun p : Profile => (|p.2.2| ^ i) ^ 2 * ‖(opS^[α] (nzModeSum c M a)) p‖ ^ 2) =
      fun p => (|p.2.2| ^ i) ^ 2 * ‖(opS^[α] (nzModeSum c M (fun n x => a n x 0))) p‖ ^ 2 +
        (|p.2.2| ^ i) ^ 2 * ‖(opS^[α] (nzModeSum c M (fun n x => a n x 1))) p‖ ^ 2 := by
    funext p; rw [hnorm p]; ring
  rw [this, integral_add I0 I1]
  have e0 := (P0.2 α hα i hi)
  have e1 := (P1.2 α hα i hi)
  unfold nzSq at e0 e1
  rw [e0, e1, ← mul_add, ← Finset.sum_add_distrib]

end UnforcedLeray.Short.PartIIa
