import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_5
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_5.MollifyApprox
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_5.CutoffApprox
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_5.AeOfFastLp
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Data.ENNReal.Inv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Sub.Defs

/-!
# `HardyApprox`: a `C_c^∞` approximation of `u ∈ L⁶` with weak gradient in `L²`

Source `the November 2 reference manuscript` lines 1351-1362, 1470-1480.

Composition of the three approximation steps:
* `mollifyApprox_holds`: smooth `v k`, `v k → u` in `L⁶`, `∂ⱼ (v k) → Dⱼ` in `L²`;
* `cutoffApprox_holds`: for a fixed smooth `w`, `C_c^∞` fields `φ m → w` in `L⁶` and `∂ⱼ φ m → ∂ⱼ w`
  in `L²`;
* `aeOfFastLp_holds`: `L⁶` convergence with summable error gives a.e. convergence.

The step lemma `hardyApprox_step` chooses `ψ` within any prescribed tolerance `δ > 0`; the main
theorem applies it with tolerance `(1/2)^(n+1)` and passes to the a.e. and energy limits.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Continuity of the Cartesian derivative of a smooth field. -/
theorem pdir_continuous_of {w : Space → CVec3} (hw : ContDiff ℝ ∞ w) (j : Fin 3) :
    Continuous (pdir j w) := by
  unfold pdir
  exact (hw.continuous_fderiv (by simp)).clm_apply continuous_const

/-- The squared `L²` norm is the Lebesgue integral of the squared enorm. -/
theorem eLpNorm_two_sq_eq (f : Space → CVec3) :
    eLpNorm f 2 volume ^ 2 = ∫⁻ y, ‖f y‖ₑ ^ 2 := by
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
  rw [ENNReal.toReal_ofNat]
  simp only [ENNReal.rpow_two]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- Tolerance step: for every `δ > 0` there is a `C_c^∞` field within `δ` of `u` in `L⁶` and
within `δ` of `D` in the gradient `L²` norms. -/
theorem hardyApprox_step (u : Space → CVec3) (D : Fin 3 → Space → CVec3)
    (hu : MemLp u 6 volume) (hD : ∀ j, MemLp (D j) 2 volume) (hweak : ∀ j, WeakDeriv j u (D j))
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ ψ : Space → CVec3, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      eLpNorm (ψ - u) 6 volume ≤ δ ∧ ∀ j, eLpNorm (pdir j ψ - D j) 2 volume ≤ δ := by
  obtain ⟨v, hvs, hv6, hv2, hvL, hvg⟩ := mollifyApprox_holds u D hu hD hweak
  have hpos : 0 < δ / 2 := ENNReal.half_pos hδ.ne'
  have hev : ∀ᶠ k in atTop, eLpNorm (v k - u) 6 volume < δ / 2 ∧
      ∀ j, eLpNorm (pdir j (v k) - D j) 2 volume < δ / 2 :=
    ((tendsto_order.1 hvL).2 _ hpos).and
      (eventually_all.2 fun j => (tendsto_order.1 (hvg j)).2 _ hpos)
  obtain ⟨k, hk1, hk2⟩ := hev.exists
  obtain ⟨φ, hφs, hφL, hφg⟩ := cutoffApprox_holds (v k) (hvs k) (hv6 k) (hv2 k)
  have hev2 : ∀ᶠ m in atTop, eLpNorm (φ m - v k) 6 volume < δ / 2 ∧
      ∀ j, eLpNorm (pdir j (φ m) - pdir j (v k)) 2 volume < δ / 2 :=
    ((tendsto_order.1 hφL).2 _ hpos).and
      (eventually_all.2 fun j => (tendsto_order.1 (hφg j)).2 _ hpos)
  obtain ⟨m, hm1, hm2⟩ := hev2.exists
  refine ⟨φ m, (hφs m).1, (hφs m).2, ?_, ?_⟩
  · have e : φ m - u = (φ m - v k) + (v k - u) := by abel
    rw [e]
    calc eLpNorm ((φ m - v k) + (v k - u)) 6 volume
        ≤ eLpNorm (φ m - v k) 6 volume + eLpNorm (v k - u) 6 volume :=
          eLpNorm_add_le ((hφs m).1.continuous.aestronglyMeasurable.sub
              (hv6 k).aestronglyMeasurable)
            ((hv6 k).aestronglyMeasurable.sub hu.aestronglyMeasurable) (by norm_num)
      _ ≤ δ / 2 + δ / 2 := add_le_add hm1.le hk1.le
      _ = δ := ENNReal.add_halves δ
  · intro j
    have e : pdir j (φ m) - D j = (pdir j (φ m) - pdir j (v k)) + (pdir j (v k) - D j) := by
      abel
    rw [e]
    calc eLpNorm ((pdir j (φ m) - pdir j (v k)) + (pdir j (v k) - D j)) 2 volume
        ≤ eLpNorm (pdir j (φ m) - pdir j (v k)) 2 volume
          + eLpNorm (pdir j (v k) - D j) 2 volume :=
          eLpNorm_add_le
            ((pdir_continuous_of (hφs m).1 j).aestronglyMeasurable.sub
              (pdir_continuous_of (hvs k) j).aestronglyMeasurable)
            ((pdir_continuous_of (hvs k) j).aestronglyMeasurable.sub
              (hD j).aestronglyMeasurable) (by norm_num)
      _ ≤ δ / 2 + δ / 2 := add_le_add (hm2 j).le (hk2 j).le
      _ = δ := ENNReal.add_halves δ

/-- `C_c^∞` approximation of `u ∈ L⁶` with weak gradient `D ∈ L²` (source 1351-1362, 1470-1480). -/
theorem hardyApprox_holds : HardyApprox := by
  intro u D hu hD hweakAll
  have hweak : ∀ j, WeakDeriv j u (D j) := fun j φ hφ hc => hweakAll j φ hφ hc
  have h2pos : (0 : ℝ≥0∞) < 1 / 2 := ENNReal.half_pos one_ne_zero
  have h2lt : (1 / 2 : ℝ≥0∞) < 1 := ENNReal.half_lt_self one_ne_zero ENNReal.one_ne_top
  have hT : Tendsto (fun n : ℕ => (1 / 2 : ℝ≥0∞) ^ (n + 1)) atTop (𝓝 0) :=
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one h2lt).comp (tendsto_add_atTop_nat 1)
  have hstep : ∀ n : ℕ, ∃ ψ : Space → CVec3, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      eLpNorm (ψ - u) 6 volume ≤ (1 / 2 : ℝ≥0∞) ^ (n + 1) ∧
      ∀ j, eLpNorm (pdir j ψ - D j) 2 volume ≤ (1 / 2 : ℝ≥0∞) ^ (n + 1) :=
    fun n => hardyApprox_step u D hu hD hweak (ENNReal.pow_pos h2pos (n + 1))
  choose φ hφs hφc hφL hφg using hstep
  refine ⟨φ, fun n => ⟨hφs n, hφc n⟩, ?_, ?_⟩
  · refine aeOfFastLp_holds φ u (fun n => (hφs n).continuous.aestronglyMeasurable)
      hu.aestronglyMeasurable ?_
    intro n
    calc eLpNorm (φ n - u) 6 volume ≤ (1 / 2 : ℝ≥0∞) ^ (n + 1) := hφL n
      _ ≤ (1 / 2 : ℝ≥0∞) ^ n := by
        rw [pow_succ]
        exact mul_le_of_le_one_right zero_le h2lt.le
  · intro j
    have hg : Tendsto (fun n => eLpNorm (pdir j (φ n) - D j) 2 volume) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT (fun n => zero_le)
        (fun n => hφg n j)
    have hfin : eLpNorm (D j) 2 volume ≠ ⊤ := (hD j).2.ne
    have hup : Tendsto (fun n => eLpNorm (D j) 2 volume + eLpNorm (pdir j (φ n) - D j) 2 volume)
        atTop (𝓝 (eLpNorm (D j) 2 volume)) := by
      simpa using (tendsto_const_nhds (x := eLpNorm (D j) 2 volume)).add hg
    have hlo : Tendsto (fun n => eLpNorm (D j) 2 volume - eLpNorm (pdir j (φ n) - D j) 2 volume)
        atTop (𝓝 (eLpNorm (D j) 2 volume)) := by
      simpa using ENNReal.Tendsto.sub (tendsto_const_nhds (x := eLpNorm (D j) 2 volume)) hg
        (Or.inl hfin)
    have hlim : Tendsto (fun n => eLpNorm (pdir j (φ n)) 2 volume) atTop
        (𝓝 (eLpNorm (D j) 2 volume)) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hup ?_ ?_
      · intro n
        refine tsub_le_iff_right.2 ?_
        have e : D j = pdir j (φ n) - (pdir j (φ n) - D j) := by abel
        calc eLpNorm (D j) 2 volume
            = eLpNorm (pdir j (φ n) - (pdir j (φ n) - D j)) 2 volume := by rw [← e]
          _ ≤ eLpNorm (pdir j (φ n)) 2 volume + eLpNorm (pdir j (φ n) - D j) 2 volume :=
            eLpNorm_sub_le (pdir_continuous_of (hφs n) j).aestronglyMeasurable
              ((pdir_continuous_of (hφs n) j).aestronglyMeasurable.sub
                (hD j).aestronglyMeasurable) (by norm_num)
      · intro n
        have e : pdir j (φ n) = D j + (pdir j (φ n) - D j) := by abel
        calc eLpNorm (pdir j (φ n)) 2 volume
            = eLpNorm (D j + (pdir j (φ n) - D j)) 2 volume := by rw [← e]
          _ ≤ eLpNorm (D j) 2 volume + eLpNorm (pdir j (φ n) - D j) 2 volume :=
            eLpNorm_add_le (hD j).aestronglyMeasurable
              ((pdir_continuous_of (hφs n) j).aestronglyMeasurable.sub
                (hD j).aestronglyMeasurable) (by norm_num)
    have hsq : Tendsto (fun n => eLpNorm (pdir j (φ n)) 2 volume ^ 2) atTop
        (𝓝 (eLpNorm (D j) 2 volume ^ 2)) :=
      ((ENNReal.continuous_pow 2).tendsto _).comp hlim
    simp only [eLpNorm_two_sq_eq] at hsq
    exact hsq

end UnforcedLeray.Short.PartIIIb.Concrete
