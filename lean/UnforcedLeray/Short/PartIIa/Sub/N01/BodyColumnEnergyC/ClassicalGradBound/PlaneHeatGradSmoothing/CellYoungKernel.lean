import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_3_3_2_1_1
import UnforcedLeray.Units.B0224.PlaneHeat
import UnforcedLeray.Units.B0579
import UnforcedLeray.Lib.Cylinder.Basic

/-!
# `PartII-a:N01/9/1/3/3/2/1/1/3`: Young on the cell for an `L¹` kernel

Source `the November 2 reference manuscript`,
lines 1650-1658 and 3379-3383.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIa.N01.CellYoungAux

open UnforcedLeray.Gaussian (Euc)

/-- Cauchy-Schwarz for a real kernel: `|∫ k g|² ≤ (∫ |k|) (∫ |k| |g|²)`. -/
theorem enorm_integral_L1_sq_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : Euc 2 → ℝ} (hk : AEStronglyMeasurable k volume) {g : Euc 2 → E}
    (hg : AEStronglyMeasurable g volume) :
    ‖∫ y, k y • g y‖ₑ ^ 2 ≤ (∫⁻ y, ‖k y‖ₑ) * ∫⁻ y, ‖k y‖ₑ * ‖g y‖ₑ ^ 2 := by
  have h1 : ‖∫ y, k y • g y‖ₑ ≤ ∫⁻ y, ‖k y‖ₑ * ‖g y‖ₑ := by
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    exact lintegral_congr fun y => enorm_smul _ _
  have hG0 : ∀ y, 0 ≤ ‖k y‖ := fun y => norm_nonneg _
  set a : Euc 2 → ℝ≥0∞ := fun y => ENNReal.ofReal (√‖k y‖) * ‖g y‖ₑ with ha
  set b : Euc 2 → ℝ≥0∞ := fun y => ENNReal.ofReal (√‖k y‖) with hb
  have hbm : AEMeasurable b volume :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (Real.continuous_sqrt.measurable.comp_aemeasurable hk.norm.aemeasurable)
  have ham : AEMeasurable a volume := hbm.mul hg.enorm
  have hsq : ∀ y, ENNReal.ofReal (√‖k y‖) * ENNReal.ofReal (√‖k y‖) = ‖k y‖ₑ := by
    intro y
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), Real.mul_self_sqrt (hG0 y),
      ofReal_norm]
  have hab : ∀ y, (a * b) y = ‖k y‖ₑ * ‖g y‖ₑ := by
    intro y
    simp only [Pi.mul_apply, ha, hb]
    rw [mul_right_comm, hsq]
  have ha2 : ∀ y, a y ^ (2 : ℝ) = ‖k y‖ₑ * ‖g y‖ₑ ^ 2 := by
    intro y
    simp only [ha, ENNReal.rpow_two]
    rw [mul_pow, sq (ENNReal.ofReal (√‖k y‖)), hsq]
  have hb2 : ∀ y, b y ^ (2 : ℝ) = ‖k y‖ₑ := by
    intro y
    simp only [hb, ENNReal.rpow_two]
    rw [sq, hsq]
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume : Measure (Euc 2))
    Real.HolderConjugate.two_two ham hbm
  simp only [hab, ha2, hb2] at hH
  have key : ∀ A : ℝ≥0∞, (A ^ (1 / 2 : ℝ)) ^ 2 = A := by
    intro A
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  calc ‖∫ y, k y • g y‖ₑ ^ 2 ≤ (∫⁻ y, ‖k y‖ₑ * ‖g y‖ₑ) ^ 2 := by gcongr
    _ ≤ ((∫⁻ y, ‖k y‖ₑ * ‖g y‖ₑ ^ 2) ^ (1 / 2 : ℝ) * (∫⁻ y, ‖k y‖ₑ) ^ (1 / 2 : ℝ)) ^ 2 := by
        gcongr
    _ = (∫⁻ y, ‖k y‖ₑ) * ∫⁻ y, ‖k y‖ₑ * ‖g y‖ₑ ^ 2 := by
        rw [mul_pow, key, key, mul_comm]

end UnforcedLeray.Short.PartIIa.N01.CellYoungAux

open UnforcedLeray.Gaussian (Euc)
open UnforcedLeray.Short.PartIIa.N01.CellYoungAux in
theorem cellYoungKernel : UnforcedLeray.Short.PartIIa.N01.CellYoungKernel := by
  intro c hc k hk u hu hper
  have hcell : UnforcedLeray.B0579.cell c = UnforcedLeray.Cyl.cell c := by
    simp only [UnforcedLeray.B0579.cell, UnforcedLeray.Cyl.cell, neg_div]
  have hshift : ∀ (z v : ℝ × ℝ), ((z.1 + c, z.2) - v) = ((z - v).1 + c, (z - v).2) := by
    intro z v
    ext <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> ring
  have hupu : UnforcedLeray.Cyl.IsPeriodic c (fun z : ℝ × ℝ => ‖u z‖ₑ ^ 2) := by
    intro z
    dsimp only
    rw [hper z]
  have hint : ∀ z : ℝ × ℝ, (∫ y : Euc 2, k y • u ((z.1 + c, z.2) - UnforcedLeray.B0224.planeι y))
      = ∫ y : Euc 2, k y • u (z - UnforcedLeray.B0224.planeι y) := by
    intro z
    congr 1
    funext y
    rw [hshift z (UnforcedLeray.B0224.planeι y), hper _]
  have hFper : UnforcedLeray.Cyl.IsPeriodic c
      (fun x : ℝ × ℝ => ‖∫ y : Euc 2, k y • u (x - UnforcedLeray.B0224.planeι y)‖ₑ ^ 2) := by
    intro z
    dsimp only
    rw [hint z]
  have hkm : AEMeasurable (fun y : Euc 2 => ‖k y‖ₑ) volume :=
    hk.aestronglyMeasurable.enorm
  have hMtop : (∫⁻ y : Euc 2, ‖k y‖ₑ) ≠ ⊤ := by
    have h := hk.2
    unfold HasFiniteIntegral at h
    exact h.ne
  have hpF_bound : ∀ x : ℝ × ℝ,
      ‖∫ y : Euc 2, k y • u (x - UnforcedLeray.B0224.planeι y)‖ₑ ^ 2 ≤
        (∫⁻ y : Euc 2, ‖k y‖ₑ) *
          ∫⁻ y : Euc 2, ‖k y‖ₑ * ‖u (x - UnforcedLeray.B0224.planeι y)‖ₑ ^ 2 := fun x =>
    enorm_integral_L1_sq_le (k := k) hk.aestronglyMeasurable
      (g := fun y : Euc 2 => u (x - UnforcedLeray.B0224.planeι y))
      (hu.comp (continuous_const.sub UnforcedLeray.B0224.continuous_planeι)).aestronglyMeasurable
  have hmeas : AEMeasurable
      (Function.uncurry fun (x : ℝ × ℝ) (y : Euc 2) =>
        ‖k y‖ₑ * ‖u (x - UnforcedLeray.B0224.planeι y)‖ₑ ^ 2)
      ((volume.restrict (UnforcedLeray.B0224.strip c)).prod volume) := by
    have h1 : AEMeasurable (fun p : (ℝ × ℝ) × Euc 2 => ‖k p.2‖ₑ)
        ((volume.restrict (UnforcedLeray.B0224.strip c)).prod volume) :=
      hkm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    have h2 : Measurable (fun p : (ℝ × ℝ) × Euc 2 =>
        ‖u (p.1 - UnforcedLeray.B0224.planeι p.2)‖ₑ ^ 2) :=
      ((hu.measurable.comp (measurable_fst.sub
        (UnforcedLeray.B0224.measurable_planeι.comp measurable_snd)))).enorm.pow_const 2
    exact h1.mul h2.aemeasurable
  have hcomp : ∀ y : Euc 2, ∫⁻ x in UnforcedLeray.B0224.strip c,
      ‖u (x - UnforcedLeray.B0224.planeι y)‖ₑ ^ 2 = ∫⁻ x in UnforcedLeray.B0224.strip c,
      ‖u x‖ₑ ^ 2 := fun y =>
    UnforcedLeray.B0224.lintegral_strip_comp_sub hc hupu (UnforcedLeray.B0224.planeι y)
  have hS1 : ∫⁻ x in UnforcedLeray.B0224.strip c,
      ‖∫ y : Euc 2, k y • u (x - UnforcedLeray.B0224.planeι y)‖ₑ ^ 2 =
      ∫⁻ x in UnforcedLeray.Cyl.cell c,
        ‖∫ y : Euc 2, k y • u (x - UnforcedLeray.B0224.planeι y)‖ₑ ^ 2 :=
    UnforcedLeray.B0224.lintegral_strip_eq_cell hc hFper
  have hS2 : ∫⁻ x in UnforcedLeray.B0224.strip c, ‖u x‖ₑ ^ 2 =
      ∫⁻ x in UnforcedLeray.Cyl.cell c, ‖u x‖ₑ ^ 2 :=
    UnforcedLeray.B0224.lintegral_strip_eq_cell hc hupu
  rw [hcell, ← hS1, ← hS2]
  calc ∫⁻ x in UnforcedLeray.B0224.strip c,
        ‖∫ y : Euc 2, k y • u (x - UnforcedLeray.B0224.planeι y)‖ₑ ^ 2
      ≤ ∫⁻ x in UnforcedLeray.B0224.strip c, (∫⁻ y : Euc 2, ‖k y‖ₑ) *
          ∫⁻ y : Euc 2, ‖k y‖ₑ * ‖u (x - UnforcedLeray.B0224.planeι y)‖ₑ ^ 2 :=
        lintegral_mono fun x => hpF_bound x
    _ = (∫⁻ y : Euc 2, ‖k y‖ₑ) * ∫⁻ x in UnforcedLeray.B0224.strip c,
          ∫⁻ y : Euc 2, ‖k y‖ₑ * ‖u (x - UnforcedLeray.B0224.planeι y)‖ₑ ^ 2 :=
        lintegral_const_mul' _ _ hMtop
    _ = (∫⁻ y : Euc 2, ‖k y‖ₑ) * ∫⁻ y : Euc 2, ∫⁻ x in UnforcedLeray.B0224.strip c,
          ‖k y‖ₑ * ‖u (x - UnforcedLeray.B0224.planeι y)‖ₑ ^ 2 := by
        congr 1
        exact lintegral_lintegral_swap hmeas
    _ = (∫⁻ y : Euc 2, ‖k y‖ₑ) * ∫⁻ y : Euc 2, ‖k y‖ₑ *
          ∫⁻ x in UnforcedLeray.B0224.strip c, ‖u x‖ₑ ^ 2 := by
        congr 1
        refine lintegral_congr fun y => ?_
        rw [lintegral_const_mul' _ _ enorm_ne_top, hcomp y]
    _ = (∫⁻ y : Euc 2, ‖k y‖ₑ) * ((∫⁻ y : Euc 2, ‖k y‖ₑ) *
          ∫⁻ x in UnforcedLeray.B0224.strip c, ‖u x‖ₑ ^ 2) := by
        rw [lintegral_mul_const'' _ hkm]
    _ = (∫⁻ y : Euc 2, ‖k y‖ₑ) ^ 2 * ∫⁻ x in UnforcedLeray.B0224.strip c, ‖u x‖ₑ ^ 2 := by
        ring
