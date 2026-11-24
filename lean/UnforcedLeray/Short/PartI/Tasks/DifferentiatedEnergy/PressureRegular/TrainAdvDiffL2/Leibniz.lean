import UnforcedLeray.Short.PartI.Sub.T08_3
import UnforcedLeray.Lib.TrainB.SmoothProduct
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Leibniz closure for `bounded-words × L²-words` (helper of `trainAdvDiffL2_proof`)

Source: `the November 2 reference manuscript` lines 326-329. Instead of an
explicit shuffle formula we use the class `Gp` of finite sums of products `f * g`, `f` smooth with
all word derivatives bounded, `g` smooth with all word derivatives in `L²(cell)`; it is closed
under every coordinate derivative (one-step Leibniz), hence under all words.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.Short.PartI.AdvLeib

open UnforcedLeray.Cyl (Plane)

/-- Smooth with all word derivatives bounded. -/
def BW (f : Plane → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ ∀ w : List Bool, ∃ M : ℝ, ∀ z : Plane, |B0151.derivWord w f z| ≤ M

/-- Smooth with all word derivatives in `L²(cell)`. -/
def LW (c : ℝ) (g : Plane → ℝ) : Prop :=
  ContDiff ℝ ∞ g ∧ ∀ w : List Bool, MemLp (B0151.derivWord w g) 2 (Cyl.cellμ c)

theorem derivWord_append (b : Bool) (h : Plane → ℝ) :
    ∀ u : List Bool, B0151.derivWord (u ++ [b]) h = B0151.derivWord u (B0151.derivWord [b] h)
  | [] => rfl
  | true :: u => by
      show GaussianVortex.partialX (B0151.derivWord (u ++ [b]) h) = _
      rw [derivWord_append b h u]
      rfl
  | false :: u => by
      show GaussianVortex.partialY (B0151.derivWord (u ++ [b]) h) = _
      rw [derivWord_append b h u]
      rfl

theorem BW.deriv {f : Plane → ℝ} (hf : BW f) (b : Bool) : BW (B0151.derivWord [b] f) := by
  refine ⟨B0151.contDiff_derivWord hf.1 [b], fun w => ?_⟩
  rw [← derivWord_append]
  first | exact hf.2 _ | skip

theorem LW.deriv {c : ℝ} {f : Plane → ℝ} (hf : LW c f) (b : Bool) :
    LW c (B0151.derivWord [b] f) := by
  refine ⟨B0151.contDiff_derivWord hf.1 [b], fun w => ?_⟩
  rw [← derivWord_append]
  first | exact hf.2 _ | skip

/-- Finite sums of products (bounded words) × (`L²` words). -/
inductive Gp (c : ℝ) : (Plane → ℝ) → Prop
  | prod {f g : Plane → ℝ} : BW f → LW c g → Gp c (fun z => f z * g z)
  | add {a b : Plane → ℝ} : Gp c a → Gp c b → Gp c (fun z => a z + b z)

theorem Gp.smooth {c : ℝ} {h : Plane → ℝ} (hh : Gp c h) : ContDiff ℝ ∞ h := by
  induction hh with
  | prod hf hg => exact hf.1.mul hg.1
  | add _ _ ih1 ih2 => exact ih1.add ih2

theorem Gp.deriv {c : ℝ} {h : Plane → ℝ} (hh : Gp c h) (b : Bool) :
    Gp c (B0151.derivWord [b] h) := by
  induction hh with
  | @prod f g hf hg =>
      rw [TrainB.derivWord_singleton_mul hf.1 hg.1 b]
      exact Gp.add (Gp.prod (hf.deriv b) hg) (Gp.prod hf (hg.deriv b))
  | @add a a' h1 h2 ih1 ih2 =>
      rw [TrainB.derivWord_singleton_add h1.smooth h2.smooth b]
      exact Gp.add ih1 ih2

theorem Gp.word {c : ℝ} {h : Plane → ℝ} (hh : Gp c h) :
    ∀ w : List Bool, Gp c (B0151.derivWord w h)
  | [] => hh
  | b :: w => by
      have := (Gp.word hh w).deriv b
      cases b <;> exact this

theorem Gp.memLp {c : ℝ} {h : Plane → ℝ} (hh : Gp c h) : MemLp h 2 (Cyl.cellμ c) := by
  induction hh with
  | @prod f g hf hg =>
      obtain ⟨M, hM⟩ := hf.2 []
      have hg0 : MemLp g 2 (Cyl.cellμ c) := hg.2 []
      refine MemLp.of_le_mul (c := M) hg0
        ((hf.1.continuous.mul hg.1.continuous).aestronglyMeasurable) ?_
      refine Filter.Eventually.of_forall fun z => ?_
      have := hM z
      change |f z| ≤ M at this
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
  | add _ _ ih1 ih2 => exact ih1.add ih2

theorem Gp.lw {c : ℝ} {h : Plane → ℝ} (hh : Gp c h) : LW c h :=
  ⟨hh.smooth, fun w => (hh.word w).memLp⟩

theorem LW.mul_BW {c : ℝ} {f g : Plane → ℝ} (hf : BW f) (hg : LW c g) :
    LW c (fun z => f z * g z) := (Gp.prod hf hg).lw

end UnforcedLeray.Short.PartI.AdvLeib
