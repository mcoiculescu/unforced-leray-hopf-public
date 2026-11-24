import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# `sliceH1`: decomposition into real/imaginary parts

Source `the November 2 reference manuscript` lines 1351-1362 (one-slice `H¹`
bound from `|ξ|² |f̂|² ≤ |f̂| |ĥ|`).  Route: split `f, h` into real and imaginary parts, apply the
real-valued one-slice regularity (`ModeId.laplacianH1Regularity`), recombine.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Real part of a `ℂ³`-valued field, viewed again as `ℂ³`-valued. -/
def reC (f : Space → CVec3) (y : Space) : CVec3 := WithLp.toLp 2 fun i => (((f y i).re : ℝ) : ℂ)

/-- Imaginary part of a `ℂ³`-valued field, viewed again as `ℂ³`-valued. -/
def imC (f : Space → CVec3) (y : Space) : CVec3 := WithLp.toLp 2 fun i => (((f y i).im : ℝ) : ℂ)

/-- Real-valued `ℂ³` field. -/
def IsRealV (f : Space → CVec3) : Prop := ∀ y i, (f y i).im = 0

/-- The slice Laplacian identity for the pair `(f, h)`. -/
def SliceLapPair (f h : Space → CVec3) : Prop :=
  ∀ θ : Space → CVec3, ContDiff ℝ ∞ θ → HasCompactSupport θ →
    (∫ y : Space, ∑ i : Fin 3, f y i * lapS θ y i) = ∫ y : Space, ∑ i : Fin 3, h y i * θ y i

/-- The weak-derivative identity for `g` against `f` in direction `j`. -/
def WeakDer (f : Space → CVec3) (j : Fin 3) (g : Space → CVec3) : Prop :=
  ∀ θ : Space → CVec3, ContDiff ℝ ∞ θ → HasCompactSupport θ →
    -(∫ y : Space, ∑ i : Fin 3,
        f y i * fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single j (1 : ℝ)))
      = ∫ y : Space, ∑ i : Fin 3, g y i * θ y i

/-- (1) Real-valued one-slice `H¹` regularity (source 1351-1362; library
`Blueprint.ModeId.laplacianH1Regularity` / Fourier): for real-valued `L²` data satisfying the
identity against all (complex) tests, there are real-valued `gⱼ ∈ L²` with the weak derivative
identity and `∑ⱼ ‖gⱼ‖² ≤ ‖f‖‖h‖`. -/
def SliceH1Real : Prop :=
  ∀ f h : Space → CVec3, IsRealV f → IsRealV h → MemLp f 2 volume → MemLp h 2 volume →
    SliceLapPair f h →
    ∃ g : Fin 3 → Space → CVec3, (∀ j, MemLp (g j) 2 volume) ∧ (∀ j, IsRealV (g j)) ∧
      (∀ j, WeakDer f j (g j)) ∧
      ∑ j : Fin 3, (∫ y : Space, ‖g j y‖ ^ 2)
        ≤ (∫ y : Space, ‖f y‖ ^ 2) ^ (1 / 2 : ℝ) * (∫ y : Space, ‖h y‖ ^ 2) ^ (1 / 2 : ℝ)

/-- (2) Splitting the identity (source 1351-1362): if `(f,h)` satisfies `SliceLapPair` with
`f, h ∈ L²`, then so do `(reC f, reC h)` and `(imC f, imC h)` (test with real `θ` and `iθ`,
take real and imaginary parts; `lapS` commutes with `re`, `im` of tests), and all four are in `L²`
and real-valued. -/
def SplitIdentity : Prop :=
  ∀ f h : Space → CVec3, MemLp f 2 volume → MemLp h 2 volume → SliceLapPair f h →
    MemLp (reC f) 2 volume ∧ MemLp (reC h) 2 volume ∧ MemLp (imC f) 2 volume ∧
    MemLp (imC h) 2 volume ∧ IsRealV (reC f) ∧ IsRealV (reC h) ∧ IsRealV (imC f) ∧
    IsRealV (imC h) ∧ SliceLapPair (reC f) (reC h) ∧ SliceLapPair (imC f) (imC h)

/-- (3) Recombining weak derivatives by linearity: `f = reC f + i imC f`. -/
def CombineWeak : Prop :=
  ∀ (f gr gi : Space → CVec3) (j : Fin 3), MemLp f 2 volume → MemLp gr 2 volume →
    MemLp gi 2 volume → WeakDer (reC f) j gr → WeakDer (imC f) j gi →
      WeakDer f j (fun y => gr y + Complex.I • gi y)

/-- (4) Pythagoras for the splitting: `∫‖f‖² = ∫‖reC f‖² + ∫‖imC f‖²` for `f ∈ L²`, and
`∫‖gr + i gi‖² = ∫‖gr‖² + ∫‖gi‖²` for real-valued `gr, gi ∈ L²`. -/
def SplitNorms : Prop :=
  (∀ f : Space → CVec3, MemLp f 2 volume →
    (∫ y : Space, ‖f y‖ ^ 2) = (∫ y : Space, ‖reC f y‖ ^ 2) + ∫ y : Space, ‖imC f y‖ ^ 2) ∧
  (∀ gr gi : Space → CVec3, IsRealV gr → IsRealV gi → MemLp gr 2 volume → MemLp gi 2 volume →
    (∫ y : Space, ‖gr y + Complex.I • gi y‖ ^ 2)
      = (∫ y : Space, ‖gr y‖ ^ 2) + ∫ y : Space, ‖gi y‖ ^ 2)

/-- Cauchy–Schwarz for two nonnegative pairs. -/
theorem sqrt_pair_le (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    a ^ (1 / 2 : ℝ) * b ^ (1 / 2 : ℝ) + c ^ (1 / 2 : ℝ) * d ^ (1 / 2 : ℝ)
      ≤ (a + c) ^ (1 / 2 : ℝ) * (b + d) ^ (1 / 2 : ℝ) := by
  simp only [← Real.sqrt_eq_rpow]
  rw [← Real.sqrt_mul ha, ← Real.sqrt_mul hc, ← Real.sqrt_mul (by positivity)]
  apply Real.le_sqrt_of_sq_le
  have h1 := Real.sqrt_nonneg (a * b)
  have h2 := Real.sqrt_nonneg (c * d)
  have e1 := Real.sq_sqrt (mul_nonneg ha hb)
  have e2 := Real.sq_sqrt (mul_nonneg hc hd)
  have key : Real.sqrt (a * b) * Real.sqrt (c * d) ≤ Real.sqrt (a * d) * Real.sqrt (c * b) := by
    rw [← Real.sqrt_mul (mul_nonneg ha hb), ← Real.sqrt_mul (mul_nonneg ha hd)]
    apply Real.sqrt_le_sqrt
    nlinarith [mul_nonneg ha hb, mul_nonneg hc hd, mul_nonneg ha hd, mul_nonneg hc hb,
      sq_nonneg (a * d - c * b)]
  have k2 : Real.sqrt (a * d) * Real.sqrt (c * b) ≤ (a * d + c * b) / 2 := by
    nlinarith [sq_nonneg (Real.sqrt (a * d) - Real.sqrt (c * b)),
      Real.sq_sqrt (mul_nonneg ha hd), Real.sq_sqrt (mul_nonneg hc hb)]
  nlinarith [key, k2]

theorem sliceH1_of (h1 : SliceH1Real) (h2 : SplitIdentity) (h3 : CombineWeak)
    (h4 : SplitNorms) : SliceH1 := by
  intro f h hf hh hid
  obtain ⟨rf, rh, jf, jh, rrf, rrh, rjf, rjh, idr, idi⟩ := h2 f h hf hh hid
  obtain ⟨gr, mgr, rgr, wgr, bgr⟩ := h1 _ _ rrf rrh rf rh idr
  obtain ⟨gi, mgi, rgi, wgi, bgi⟩ := h1 _ _ rjf rjh jf jh idi
  refine ⟨fun j y => gr j y + Complex.I • gi j y, fun j => ?_, fun j => h3 f (gr j) (gi j) j hf (mgr j) (mgi j) (wgr j) (wgi j), ?_⟩
  · exact (mgr j).add ((mgi j).const_smul Complex.I)
  · have hn : ∀ j, (∫ y : Space, ‖gr j y + Complex.I • gi j y‖ ^ 2)
        = (∫ y : Space, ‖gr j y‖ ^ 2) + ∫ y : Space, ‖gi j y‖ ^ 2 :=
      fun j => h4.2 _ _ (rgr j) (rgi j) (mgr j) (mgi j)
    simp only [hn, Finset.sum_add_distrib]
    rw [h4.1 f hf, h4.1 h hh]
    exact (add_le_add bgr bgi).trans (sqrt_pair_le _ _ _ _
      (integral_nonneg fun _ => by positivity) (integral_nonneg fun _ => by positivity)
      (integral_nonneg fun _ => by positivity) (integral_nonneg fun _ => by positivity))

end UnforcedLeray.Short.PartIIIb.Concrete
