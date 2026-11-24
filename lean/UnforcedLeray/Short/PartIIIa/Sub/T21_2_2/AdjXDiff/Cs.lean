import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.AdjXDiff

/-!
# `PartIII-a:T21/2/2`, helper: Cauchy-Schwarz on an interval for the difference quotient

Source of record: `the November 2 reference manuscript` (SP) lines 3060-3073.

For a continuous `G : ℝ → ℂ` on `[r, r']`, the average `(r' - r)⁻¹ ∫_r^{r'} G` satisfies
`‖(r' - r)⁻¹ ∫_r^{r'} G‖² ≤ |r' - r|⁻¹ ∫_{Ι r r'} ‖G‖²` (Jensen/Cauchy-Schwarz; no majorant).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology intervalIntegral
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

/-- Cauchy-Schwarz on `Ioc a b` (real, continuous, `a ≤ b`). -/
theorem cs_Ioc (a b : ℝ) (hab : a ≤ b) (g : ℝ → ℝ) (hg : ContinuousOn g (Icc a b)) :
    (∫ x in Ioc a b, g x) ^ 2 ≤ (b - a) * ∫ x in Ioc a b, g x ^ 2 := by
  rcases eq_or_lt_of_le hab with h | h
  · subst h
    simp
  set L := b - a with hL
  have hLpos : 0 < L := by rw [hL]; linarith
  have hIcc : IntegrableOn g (Icc a b) := hg.integrableOn_Icc
  have hIoc : IntegrableOn g (Ioc a b) := hIcc.mono_set Ioc_subset_Icc_self
  have hg2 : IntegrableOn (fun x => g x ^ 2) (Ioc a b) :=
    (hg.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  set I := ∫ x in Ioc a b, g x with hI
  set Q := ∫ x in Ioc a b, g x ^ 2 with hQ
  set t := I / L with ht
  have hnn : 0 ≤ ∫ x in Ioc a b, (g x - t) ^ 2 :=
    setIntegral_nonneg measurableSet_Ioc fun x _ => sq_nonneg _
  have hexp : ∫ x in Ioc a b, (g x - t) ^ 2 = Q - 2 * t * I + t ^ 2 * L := by
    have e : ∀ x, (g x - t) ^ 2 = g x ^ 2 + (-(2 * t)) * g x + t ^ 2 := fun x => by ring
    simp_rw [e]
    have i1 : IntegrableOn (fun x => g x ^ 2) (Ioc a b) := hg2
    have i2 : IntegrableOn (fun x => (-(2 * t)) * g x) (Ioc a b) := hIoc.const_mul _
    have i3 : IntegrableOn (fun _ : ℝ => t ^ 2) (Ioc a b) :=
      integrableOn_const measure_Ioc_lt_top.ne
    have i12 : IntegrableOn (fun x => g x ^ 2 + -(2 * t) * g x) (Ioc a b) := i1.add i2
    rw [MeasureTheory.integral_add i12 i3, MeasureTheory.integral_add i1 i2,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const]
    have hvol : (volume.restrict (Ioc a b)).real univ = b - a := by
      rw [Measure.real, Measure.restrict_apply_univ, Real.volume_Ioc,
        ENNReal.toReal_ofReal (by linarith)]
    simp only [hvol, smul_eq_mul, hL, hI, hQ]
    ring
  have key : 0 ≤ Q - 2 * t * I + t ^ 2 * L := hexp ▸ hnn
  have hI2 : I ^ 2 ≤ L * Q := by
    have : t * L = I := by rw [ht]; field_simp
    nlinarith [sq_nonneg (I - t * L), this]
  simpa [hL, hI, hQ] using hI2

/-- Cauchy-Schwarz on the unordered interval `Ι r r'`. -/
theorem cs_uIoc (r r' : ℝ) (g : ℝ → ℝ) (hg : ContinuousOn g (uIcc r r')) :
    (∫ x in Ι r r', g x) ^ 2 ≤ |r' - r| * ∫ x in Ι r r', g x ^ 2 := by
  rcases le_total r r' with h | h
  · have hg' : ContinuousOn g (Icc r r') := by rwa [uIcc_of_le h] at hg
    rw [uIoc_of_le h, abs_of_nonneg (by linarith : (0:ℝ) ≤ r' - r)]
    exact cs_Ioc r r' h g hg'
  · have hg' : ContinuousOn g (Icc r' r) := by rwa [uIcc_of_ge h] at hg
    rw [uIoc_of_ge h]
    have := cs_Ioc r' r h g hg'
    have e : |r' - r| = r - r' := by rw [abs_of_nonpos (by linarith)]; ring
    rw [e]
    exact this

/-- **Jensen bound for the difference quotient** (pointwise in `x`): the norm of the average of a
continuous complex `G` on `Ι r r'` is controlled by the `L²` norm of `G` on `Ι r r'`. -/
theorem norm_avg_sq (r r' : ℝ) (hrr : r ≠ r') (G : ℝ → ℂ) (hG : ContinuousOn G (uIcc r r')) :
    ‖((r' - r)⁻¹ : ℝ) • ∫ ρ in r..r', G ρ‖ ^ 2 ≤
      |r' - r|⁻¹ * ∫ ρ in Ι r r', ‖G ρ‖ ^ 2 := by
  have hn : ‖∫ ρ in r..r', G ρ‖ ≤ ∫ ρ in Ι r r', ‖G ρ‖ :=
    intervalIntegral.norm_integral_le_integral_norm_uIoc
  have hgn : ContinuousOn (fun ρ => ‖G ρ‖) (uIcc r r') := hG.norm
  have hcs := cs_uIoc r r' (fun ρ => ‖G ρ‖) hgn
  have hpos : 0 < |r' - r| := abs_pos.2 (sub_ne_zero.2 hrr.symm)
  have hsq : ‖∫ ρ in r..r', G ρ‖ ^ 2 ≤ (∫ ρ in Ι r r', ‖G ρ‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hA : ‖∫ ρ in r..r', G ρ‖ ^ 2 ≤ |r' - r| * ∫ ρ in Ι r r', ‖G ρ‖ ^ 2 :=
    le_trans hsq hcs
  have hLHS : ‖((r' - r)⁻¹ : ℝ) • ∫ ρ in r..r', G ρ‖ = |r' - r|⁻¹ * ‖∫ ρ in r..r', G ρ‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv]
  rw [hLHS, mul_pow]
  calc (|r' - r|⁻¹) ^ 2 * ‖∫ ρ in r..r', G ρ‖ ^ 2
      ≤ (|r' - r|⁻¹) ^ 2 * (|r' - r| * ∫ ρ in Ι r r', ‖G ρ‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hA (sq_nonneg _)
    _ = |r' - r|⁻¹ * ∫ ρ in Ι r r', ‖G ρ‖ ^ 2 := by
        field_simp

end UnforcedLeray.Short.IIIa
