import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_data_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_data_1.GaussPointBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_data_1.PeriodizeMeas
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Separation.Basic

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- The clock is `srcA ν s = 1 + ν max(s,0)`. -/
theorem srcA_eq (ν s : ℝ) : srcA ν s = 1 + ν * max s 0 := rfl

theorem srcA_ge_one (ν : ℝ) (hν : 0 < ν) (s : ℝ) : 1 ≤ srcA ν s := by
  rw [srcA_eq]
  have : 0 ≤ ν * max s 0 := mul_nonneg hν.le (le_max_right _ _)
  linarith

theorem srcA_mono (ν : ℝ) (hν : 0 < ν) {s S : ℝ} (h : s ≤ S) : srcA ν s ≤ srcA ν S := by
  rw [srcA_eq, srcA_eq]
  have : ν * max s 0 ≤ ν * max S 0 := mul_le_mul_of_nonneg_left (max_le_max h le_rfl) hν.le
  linarith

theorem srcA_continuous (ν : ℝ) : Continuous (srcA ν) := by
  unfold srcA ageA
  fun_prop

/-- The closed form of `a ↦ gaussRdE a r` is continuous at each `a ≠ 0`. -/
theorem gaussRdE_contAt (r a : ℝ) (ha : a ≠ 0) :
    ContinuousAt (fun b => gaussRdE b r) a := by
  have hc : ContinuousAt (fun b : ℝ => -((b ^ 2)⁻¹ * (r ^ 2 / (2 * b)) * (4 - r ^ 2 / (2 * b))
      * Real.exp (-(r ^ 2) / (4 * b)))) a := by
    fun_prop (disch := simp [ha])
  apply hc.congr
  filter_upwards [eventually_ne_nhds ha] with b hb
  exact (gaussRdE_eq b r hb).symm

/-- `a ↦ gaussE a r` is continuous at each `a ≠ 0`. -/
theorem gaussE_contAt (r a : ℝ) (ha : a ≠ 0) :
    ContinuousAt (fun b => gaussE b r) a := by
  unfold gaussE
  fun_prop (disch := simp [ha])

/-- `a ↦ hMode a y` is continuous on `[1, ∞)`. -/
theorem hMode_contOn (y : ℝ × ℝ) : ContinuousOn (fun a => hMode a y) (Ici 1) := by
  intro a ha
  have ha0 : a ≠ 0 := by
    have : (1 : ℝ) ≤ a := Set.mem_Ici.1 ha
    exact (by linarith : (0 : ℝ) < a).ne'
  apply ContinuousAt.continuousWithinAt
  unfold hMode
  exact (Complex.continuous_ofReal.continuousAt.comp (gaussRdE_contAt (planeR y) a ha0)).mul
    continuousAt_const

/-- `a ↦ rMode a y` is continuous on `[1, ∞)`. -/
theorem rMode_contOn (y : ℝ × ℝ) : ContinuousOn (fun a => rMode a y) (Ici 1) := by
  intro a ha
  have ha0 : a ≠ 0 := by
    have : (1 : ℝ) ≤ a := Set.mem_Ici.1 ha
    exact (by linarith : (0 : ℝ) < a).ne'
  apply ContinuousAt.continuousWithinAt
  unfold rMode
  exact Complex.continuous_ofReal.continuousAt.comp
    ((gaussRdE_contAt (planeR y) a ha0).add (continuousAt_const.mul (gaussE_contAt (planeR y) a ha0)))

/-- The generic continuity of a Gaussian-periodized profile in the age, for a family `F` of
profiles continuous in the age with Gaussian bounds. -/
theorem gauss_cont_of (ν : ℝ) (hν : 0 < ν) (c : ℝ) (hc : 0 < c)
    (F : ℝ → ℝ × ℝ → ℂ)
    (hcont : ∀ y : ℝ × ℝ, ContinuousOn (fun a => F a y) (Ici 1))
    (hbd : ∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, ∀ a ∈ Icc (1 : ℝ) A, ∀ x : ℝ × ℝ,
      ‖F a x‖ ≤ C * (1 + x.1 ^ 2 + x.2 ^ 2) ^ 2 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (4 * A)))
    (x : ℝ × ℝ) :
    Continuous (fun s => ∑' n : ℤ, F (srcA ν s) (x.1 - n * c, x.2)) := by
  rw [continuous_iff_continuousAt]
  intro s0
  set S : ℝ := s0 + 1 with hS
  set A : ℝ := srcA ν S with hAdef
  have hA1 : 1 ≤ A := srcA_ge_one ν hν S
  have hA0 : 0 < A := by linarith
  obtain ⟨C, hC⟩ := hbd A hA1
  have hC0 : 0 ≤ C := by
    have h0 := hC 1 ⟨le_rfl, hA1⟩ (0, 0)
    norm_num at h0
    linarith [norm_nonneg (F 1 (0, 0))]
  have hU : Summable (fun n : ℤ => (C * (1 + 16 * A) ^ 2 * Real.exp (x.1 ^ 2 / (8 * A))) *
      Real.exp (-((c ^ 2 / (16 * A)) * (n : ℝ) ^ 2))) :=
    (pm_summable (c ^ 2 / (16 * A)) (div_pos (pow_pos hc 2) (by linarith))).mul_left _
  have hcontOn : ContinuousOn (fun s => ∑' n : ℤ, F (srcA ν s) (x.1 - n * c, x.2)) (Iio S) := by
    refine continuousOn_tsum (f := fun (n : ℤ) (s : ℝ) => F (srcA ν s) (x.1 - n * c, x.2))
      (fun n => ?_) hU (fun n s hs => ?_)
    · exact (hcont (x.1 - n * c, x.2)).comp (srcA_continuous ν).continuousOn
        (fun s _ => srcA_ge_one ν hν s)
    · have hsA : srcA ν s ∈ Icc (1 : ℝ) A :=
        ⟨srcA_ge_one ν hν s, srcA_mono ν hν (le_of_lt (Set.mem_Iio.1 hs))⟩
      exact pm_term_bound A c C (F (srcA ν s)) hA0 hC0 (fun y => hC _ hsA y) x n
  have hs0 : s0 ∈ Iio S := by
    rw [Set.mem_Iio, hS]
    linarith
  exact hcontOn.continuousAt (isOpen_Iio.mem_nhds hs0)

theorem gaussProfPtCont : GaussProfPtCont := by
  intro ν hν x
  have hc : 0 < cOf ν := inv_pos.2 (pow_pos hν 2)
  have hHbd : ∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, ∀ a ∈ Icc (1 : ℝ) A, ∀ x : ℝ × ℝ,
      ‖hMode a x‖ ≤ C * (1 + x.1 ^ 2 + x.2 ^ 2) ^ 2 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (4 * A)) := by
    intro A hA
    obtain ⟨C, hC⟩ := gaussPointBound A hA
    exact ⟨C, fun a ha x => (hC a ha x).1⟩
  have hRbd : ∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, ∀ a ∈ Icc (1 : ℝ) A, ∀ x : ℝ × ℝ,
      ‖rMode a x‖ ≤ C * (1 + x.1 ^ 2 + x.2 ^ 2) ^ 2 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (4 * A)) := by
    intro A hA
    obtain ⟨C, hC⟩ := gaussPointBound A hA
    exact ⟨C, fun a ha x => (hC a ha x).2⟩
  exact ⟨gauss_cont_of ν hν (cOf ν) hc (fun a => hMode a) (fun y => hMode_contOn y) hHbd x,
    gauss_cont_of ν hν (cOf ν) hc (fun a => rMode a) (fun y => rMode_contOn y) hRbd x⟩

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
