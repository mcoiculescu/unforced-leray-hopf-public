import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_3_1_2_1_3
import UnforcedLeray.Lib.Cylinder.Basic
import UnforcedLeray.Lib.SobolevC.CylSmooth

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ContDiff ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Cyl (Vec2 Plane)

/-- A `c`-cylinder smooth field is `Cyl.IsPeriodic c`. -/
theorem m2_isPeriodic {c : ℝ} {g : Plane → Vec2} (hg : UnforcedLeray.Sob.IsCylSmooth c g) :
    UnforcedLeray.Cyl.IsPeriodic c g := by
  intro z
  have e : z + (c, 0) = (z.1 + c, z.2) := by ext <;> simp
  have h := hg.periodic z
  rw [e] at h
  exact h

/-- Integer multiples of the period are periods. -/
theorem m2_periodic_nat {c : ℝ} {f : Plane → Vec2} (hf : UnforcedLeray.Sob.IsCylSmooth c f)
    (n : ℕ) (z : Plane) : f (z + ((n : ℝ) * c, 0)) = f z := by
  induction n with
  | zero =>
    have e0 : z + (((0 : ℕ) : ℝ) * c, 0) = z := by ext <;> simp
    rw [e0]
  | succ n ih =>
    have e : z + (((n + 1 : ℕ) : ℝ) * c, 0) = (z + ((n : ℝ) * c, 0)) + (c, 0) := by
      ext <;> simp <;> ring
    rw [e, hf.periodic, ih]

/-- Integral over a strip of `n` periods is `n` times the integral over one cell. -/
theorem m2_strip_sum {c : ℝ} (hc : 0 < c) {φ : Plane → ℝ≥0∞}
    (hφ : UnforcedLeray.Cyl.IsPeriodic c φ) (a : ℝ) (n : ℕ) :
    ∫⁻ z in Ico a (a + (n : ℝ) * c) ×ˢ (univ : Set ℝ), φ z =
      (n : ℝ≥0∞) * ∫⁻ z in UnforcedLeray.Cyl.cell c, φ z := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hnc : 0 ≤ (n : ℝ) * c := by positivity
    have e : a + ((n + 1 : ℕ) : ℝ) * c = (a + (n : ℝ) * c) + c := by push_cast; ring
    rw [e, ← Set.Ico_union_Ico_eq_Ico (by linarith : a ≤ a + (n : ℝ) * c)
        (by linarith : a + (n : ℝ) * c ≤ a + (n : ℝ) * c + c), Set.union_prod,
      MeasureTheory.lintegral_union (measurableSet_Ico.prod MeasurableSet.univ)
        (Set.disjoint_prod.mpr (Or.inl Set.Ico_disjoint_Ico_same)), ih,
      UnforcedLeray.Cyl.lintegral_strip_eq_cell hc hφ, Nat.cast_succ, add_mul, one_mul]

/-- Conversion of the `L²` norm on a restricted measure to a lower integral of `‖g‖ₑ ^ 2`. -/
theorem m2_eLpNorm_restrict (g : Plane → Vec2) (s : Set Plane) :
    eLpNorm g 2 (volume.restrict s) = (∫⁻ z in s, ‖g z‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat]

/-- Main estimate: for a `c`-cylinder smooth field, the `L²` norm over the cell of width `N c`
is at most `√N` times the one over the cell of width `c` (in fact equal). -/
theorem m2_main {c : ℝ} (hc : 0 < c) (N : ℕ) {g : Plane → Vec2}
    (hg : UnforcedLeray.Sob.IsCylSmooth c g) :
    eLpNorm g 2 (UnforcedLeray.Cyl.cellμ ((N : ℝ) * c)) ≤
      ENNReal.ofReal (Real.sqrt N) * eLpNorm g 2 (UnforcedLeray.Cyl.cellμ c) := by
  have hper := m2_isPeriodic hg
  have hφp : UnforcedLeray.Cyl.IsPeriodic c (fun z => ‖g z‖ₑ ^ (2 : ℝ)) := by
    intro z
    show ‖g (z.1 + c, z.2)‖ₑ ^ (2 : ℝ) = ‖g z‖ₑ ^ (2 : ℝ)
    rw [hper z]
  have hbig : ∫⁻ z in UnforcedLeray.Cyl.cell ((N : ℝ) * c), ‖g z‖ₑ ^ (2 : ℝ) =
      (N : ℝ≥0∞) * ∫⁻ z in UnforcedLeray.Cyl.cell c, ‖g z‖ₑ ^ (2 : ℝ) := by
    rw [UnforcedLeray.Cyl.cell_eq_strip]
    exact m2_strip_sum hc hφp (-((N : ℝ) * c) / 2) N
  have hN : (N : ℝ≥0∞) ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt N) := by
    rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
      (by norm_num : (0 : ℝ) ≤ 1 / 2), ENNReal.ofReal_natCast]
  unfold UnforcedLeray.Cyl.cellμ
  rw [m2_eLpNorm_restrict, m2_eLpNorm_restrict]
  refine le_of_eq ?_
  rw [hbig, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2), hN]

theorem cellPeriodReduction_proof : CellPeriodReduction := by
  unfold CellPeriodReduction
  intro c hc N hN f hf
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hsm : UnforcedLeray.Sob.IsCylSmooth ((N : ℝ) * c) f :=
    { smooth := hf.smooth
      periodic := fun z => m2_periodic_nat hf N z
      bounded := hf.bounded }
  refine ⟨hsm, fun v => ?_⟩
  exact m2_main hc N (hf.iterD v)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
