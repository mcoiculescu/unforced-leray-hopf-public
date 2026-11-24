import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_8
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Leaf `PartII-b:T13/1/8/3`: measurable periodic gluing (SP 1928-1933)

`WglMeasGlue`: windows `(a_k, 2a_k)` with `a_k = (3/2)^k`, `k ∈ ℤ`, are indexed by the integer
`K(s) = ⌈logb (3/2) s⌉ - 1`, which satisfies `a_{K(s)} < s ≤ (3/2) a_{K(s)}` for `s > 0`. The glue
is `Gl x = g (a_{K(x.1)}) x`: it is `q`-periodic and measurable because `K` depends only on `x.1`,
and on each window it agrees a.e. with `g a` by the overlap hypothesis for the countably many pairs
`(a, a_k)`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff

/-- The window index of a positive real `s`. -/
def wglm_K (s : ℝ) : ℤ := ⌈Real.logb (3 / 2) s⌉ - 1

/-- The window radius `a_k = (3/2)^k`. -/
def wglm_A (k : ℤ) : ℝ := (3 / 2 : ℝ) ^ k

theorem wglm_A_pos (k : ℤ) : 0 < wglm_A k := by
  unfold wglm_A; positivity

theorem wglm_spec_of (s : ℝ) (hs : 0 < s) (k : ℤ) (h1 : (k : ℝ) < Real.logb (3 / 2) s)
    (h2 : Real.logb (3 / 2) s ≤ (k : ℝ) + 1) :
    wglm_A k < s ∧ s ≤ 3 / 2 * wglm_A k := by
  have hst : (3 / 2 : ℝ) ^ (Real.logb (3 / 2) s) = s := Real.rpow_logb (by norm_num) (by norm_num) hs
  unfold wglm_A
  constructor
  · calc (3 / 2 : ℝ) ^ k = (3 / 2 : ℝ) ^ ((k : ℝ)) := (Real.rpow_intCast _ _).symm
      _ < (3 / 2 : ℝ) ^ (Real.logb (3 / 2) s) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h1
      _ = s := hst
  · calc s = (3 / 2 : ℝ) ^ (Real.logb (3 / 2) s) := hst.symm
      _ ≤ (3 / 2 : ℝ) ^ ((k : ℝ) + 1) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h2
      _ = 3 / 2 * (3 / 2 : ℝ) ^ k := by
          rw [Real.rpow_add (by norm_num), Real.rpow_one, Real.rpow_intCast]
          ring

theorem wglm_spec (s : ℝ) (hs : 0 < s) :
    wglm_A (wglm_K s) < s ∧ s ≤ 3 / 2 * wglm_A (wglm_K s) := by
  apply wglm_spec_of s hs
  · have := Int.ceil_lt_add_one (Real.logb (3 / 2) s)
    unfold wglm_K
    push_cast
    linarith
  · have := Int.le_ceil (Real.logb (3 / 2) s)
    unfold wglm_K
    push_cast
    linarith

theorem wglm_K_measurable : Measurable wglm_K := by
  unfold wglm_K Real.logb
  exact (Int.measurable_ceil.comp (Real.measurable_log.div_const _)).sub_const 1

theorem wglMeasGlue : WglMeasGlue := by
  intro c g hg hov
  let Gl : CProf := fun x => g (wglm_A (wglm_K x.1)) x
  have hgA : ∀ k : ℤ, QPeriodic c (g (wglm_A k)) ∧ AEStronglyMeasurable (g (wglm_A k)) volume :=
    fun k => hg (wglm_A k) (wglm_A_pos k)
  have hper : ∀ᵐ x ∂((volume : Measure Coord).restrict {x : Coord | 0 < x.1}), ∀ k : ℤ,
      g (wglm_A k) (qShift c x) = g (wglm_A k) x :=
    ae_all_iff.mpr (fun k => (hgA k).1)
  refine ⟨Gl, ?_, ?_, ?_⟩
  · -- periodicity in `q`
    filter_upwards [hper] with x hx
    exact hx (wglm_K x.1)
  · -- measurability through the countable partition by the window index
    have hEm : ∀ k : ℤ, MeasurableSet ((fun x : Coord => wglm_K x.1) ⁻¹' {k}) := fun k =>
      (wglm_K_measurable.comp measurable_fst) (measurableSet_singleton k)
    have hpiece : ∀ k : ℤ, AEStronglyMeasurable Gl (volume.restrict
        ((fun x : Coord => wglm_K x.1) ⁻¹' {k})) := by
      intro k
      refine ((hgA k).2.restrict).congr ?_
      filter_upwards [ae_restrict_mem (hEm k)] with x hx
      have hx' : wglm_K x.1 = k := hx
      show g (wglm_A k) x = g (wglm_A (wglm_K x.1)) x
      rw [hx']
    have hcover : (⋃ k : ℤ, (fun x : Coord => wglm_K x.1) ⁻¹' {k}) = univ := by
      ext x
      simp
    have hall : AEStronglyMeasurable Gl (volume.restrict
        (⋃ k : ℤ, (fun x : Coord => wglm_K x.1) ⁻¹' {k})) :=
      aestronglyMeasurable_iUnion_iff.mpr hpiece
    rw [hcover, Measure.restrict_univ] at hall
    exact hall
  · -- agreement with `g a` on each window
    intro a ha
    have hovk : ∀ᵐ x ∂(volume : Measure Coord), ∀ k : ℤ,
        (x ∈ winOpen a → x ∈ winOpen (wglm_A k) → g a x = g (wglm_A k) x) :=
      ae_all_iff.mpr (fun k => hov a (wglm_A k) ha (wglm_A_pos k))
    filter_upwards [hovk] with x hx hxa
    have hxpos : 0 < x.1 := lt_trans ha hxa.1.1
    obtain ⟨h1, h2⟩ := wglm_spec x.1 hxpos
    have hpos := wglm_A_pos (wglm_K x.1)
    have hxw : x ∈ winOpen (wglm_A (wglm_K x.1)) :=
      ⟨⟨h1, by linarith⟩, trivial⟩
    exact (hx (wglm_K x.1) hxa hxw).symm

end UnforcedLeray.Short.IIb
