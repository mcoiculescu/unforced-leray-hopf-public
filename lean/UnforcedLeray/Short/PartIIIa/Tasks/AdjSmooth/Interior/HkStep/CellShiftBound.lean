import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Shared
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.CellPeriodicLocInt

/-!
# `PartIII-a:T21/2/7/2/1/1/5/3`: translates by `‖y‖ ≤ 1` are bounded on the periodic `X_{-m,c}`

Source of record: `the November 2 reference manuscript` (SP), lines 3044-3047
(the weight is translation quasi-invariant), 3060-3061.

Weight: `cellMeasure c (-m)` has density `⟨x⟩^{-m}` on the cell, `jb x = 1 + x₁² + x₂²`.
Peetre: `jb(u+v) ≤ 2 jb u jb v`; for `‖y‖ ≤ 1`, `jb y ≤ 3`, so `jb(z+y)^{-m} ≤ 6^{|m|} jb z^{-m}`.
A shift by `s = (kc, 0)` changes the weight by a factor `(2 jb s)^{|m|}`, and `f` is periodic.
The plane is covered by finitely many translates `cell - s_k` of the cell meeting `cell - y`, so
`∫_{cell} w |f(· - y)|² ≤ (Σ_k A_k) ∫_{cell} w |f|²` (pointwise bound, then translation invariance).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The weight of `cellMeasure c (-m)` as an extended nonnegative function. -/
def wCS (m : ℝ) (x : ℝ × ℝ) : ℝ≥0∞ := ENNReal.ofReal (B0579.jb x ^ (-m))

theorem wCS_meas (m : ℝ) : Measurable (wCS m) :=
  ENNReal.measurable_ofReal.comp (B0579.continuous_jb_rpow (-m)).measurable

theorem jb_add_le_cs (u v : ℝ × ℝ) : B0579.jb (u + v) ≤ 2 * B0579.jb u * B0579.jb v := by
  unfold B0579.jb
  simp only [Prod.fst_add, Prod.snd_add]
  nlinarith [sq_nonneg (u.1 - v.1), sq_nonneg (u.2 - v.2), mul_nonneg (sq_nonneg u.1) (sq_nonneg v.1),
    mul_nonneg (sq_nonneg u.1) (sq_nonneg v.2), mul_nonneg (sq_nonneg u.2) (sq_nonneg v.1),
    mul_nonneg (sq_nonneg u.2) (sq_nonneg v.2)]

theorem jb_neg_cs (v : ℝ × ℝ) : B0579.jb (-v) = B0579.jb v := by
  unfold B0579.jb
  simp only [Prod.fst_neg, Prod.snd_neg, neg_sq]

theorem jb_ge_one_cs (v : ℝ × ℝ) : 1 ≤ B0579.jb v := by
  unfold B0579.jb
  nlinarith [sq_nonneg v.1, sq_nonneg v.2]

theorem jb_le_three_cs {y : ℝ × ℝ} (hy : ‖y‖ ≤ 1) : B0579.jb y ≤ 3 := by
  have h1 : |y.1| ≤ 1 := by simpa [Real.norm_eq_abs] using (norm_fst_le y).trans hy
  have h2 : |y.2| ≤ 1 := by simpa [Real.norm_eq_abs] using (norm_snd_le y).trans hy
  unfold B0579.jb
  have h3 : y.1 ^ 2 ≤ 1 := by nlinarith [sq_abs y.1, abs_nonneg y.1]
  have h4 : y.2 ^ 2 ≤ 1 := by nlinarith [sq_abs y.2, abs_nonneg y.2]
  linarith

/-- Ratio of weights: if `a ≤ B b` and `b ≤ B a` then `a^{-m} ≤ B^{|m|} b^{-m}`. -/
theorem rpow_ratio_cs {a b B : ℝ} (ha : 0 < a) (hb : 0 < b) (hB : 1 ≤ B) (h1 : a ≤ B * b)
    (h2 : b ≤ B * a) (m : ℝ) : a ^ (-m) ≤ B ^ |m| * b ^ (-m) := by
  have hB0 : 0 < B := by linarith
  rcases le_total 0 m with hm | hm
  · rw [abs_of_nonneg hm]
    have hp : -m ≤ 0 := by linarith
    have hba : b / B ≤ a := (div_le_iff₀ hB0).2 (by rw [mul_comm]; exact h2)
    have h3 : a ^ (-m) ≤ (b / B) ^ (-m) :=
      Real.rpow_le_rpow_of_nonpos (div_pos hb hB0) hba hp
    have key : (b / B) ^ (-m) = B ^ m * b ^ (-m) := by
      rw [Real.div_rpow hb.le hB0.le, div_eq_mul_inv, ← Real.rpow_neg hB0.le, neg_neg, mul_comm]
    rw [← key]
    exact h3
  · rw [abs_of_nonpos hm]
    have hp : 0 ≤ -m := by linarith
    calc a ^ (-m) ≤ (B * b) ^ (-m) := Real.rpow_le_rpow ha.le h1 hp
      _ = B ^ (-m) * b ^ (-m) := Real.mul_rpow hB0.le hb.le

theorem shift_W_cs {m : ℝ} {y z : ℝ × ℝ} (hy : ‖y‖ ≤ 1) :
    wCS m (z + y) ≤ ENNReal.ofReal (6 ^ |m|) * wCS m z := by
  have hy3 := jb_le_three_cs hy
  have hz0 : 0 < B0579.jb z := B0579.jb_pos z
  have hzy : 0 < B0579.jb (z + y) := B0579.jb_pos _
  have h1 : B0579.jb (z + y) ≤ 6 * B0579.jb z := by
    have := jb_add_le_cs z y
    nlinarith [mul_le_mul_of_nonneg_left hy3 hz0.le]
  have h2 : B0579.jb z ≤ 6 * B0579.jb (z + y) := by
    have := jb_add_le_cs (z + y) (-y)
    have e : z + y + -y = z := by abel
    rw [e, jb_neg_cs] at this
    nlinarith [mul_le_mul_of_nonneg_left hy3 hzy.le]
  have hr := rpow_ratio_cs hzy hz0 (by norm_num : (1 : ℝ) ≤ 6) h1 h2 m
  unfold wCS
  rw [← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hr

theorem step_W_cs (m : ℝ) (z s : ℝ × ℝ) :
    wCS m z ≤ ENNReal.ofReal ((2 * B0579.jb s) ^ |m|) * wCS m (z - s) := by
  have hs1 : 1 ≤ B0579.jb s := jb_ge_one_cs s
  have hz : 0 < B0579.jb z := B0579.jb_pos z
  have hzs : 0 < B0579.jb (z - s) := B0579.jb_pos _
  have h1 : B0579.jb z ≤ (2 * B0579.jb s) * B0579.jb (z - s) := by
    have := jb_add_le_cs (z - s) s
    rw [sub_add_cancel] at this
    calc B0579.jb z ≤ 2 * B0579.jb (z - s) * B0579.jb s := this
      _ = (2 * B0579.jb s) * B0579.jb (z - s) := by ring
  have h2 : B0579.jb (z - s) ≤ (2 * B0579.jb s) * B0579.jb z := by
    have := jb_add_le_cs z (-s)
    rw [jb_neg_cs, ← sub_eq_add_neg] at this
    calc B0579.jb (z - s) ≤ 2 * B0579.jb z * B0579.jb s := this
      _ = (2 * B0579.jb s) * B0579.jb z := by ring
  have hr := rpow_ratio_cs hz hzs (by linarith : (1 : ℝ) ≤ 2 * B0579.jb s) h1 h2 m
  unfold wCS
  rw [← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hr

/-- Periodicity under the lattice shift `(kc, 0)`. -/
theorem per_sub_cs {c : ℝ} {f : ℝ × ℝ → ℂ} (hper : ∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x)
    (k : ℤ) (z : ℝ × ℝ) : f (z - ((k : ℝ) * c, 0)) = f z := by
  have h := per_shift' hper k (z - ((k : ℝ) * c, 0))
  have e : ((z - ((k : ℝ) * c, 0)).1 + k * c, (z - ((k : ℝ) * c, 0)).2) = z := by
    ext <;> simp
  rw [e] at h
  exact h.symm

theorem ceil_mul_ge_cs {c : ℝ} (hc : 0 < c) (a : ℝ) : a ≤ (⌈a / c⌉ : ℝ) * c :=
  (div_le_iff₀ hc).1 (Int.le_ceil _)

/-- Some lattice translate of `z` lies in the cell, with the index in a fixed finite range. -/
theorem floor_cell_cs {c : ℝ} (hc : 0 < c) {z : ℝ × ℝ} (hz1 : -(c / 2) - 1 ≤ z.1)
    (hz2 : z.1 ≤ c / 2 + 1) :
    ∃ k ∈ Finset.Icc (-(⌈(c + 2) / c⌉)) ⌈(c + 2) / c⌉,
      z - (((k : ℝ) * c), 0) ∈ B0579.cell c := by
  have hK0 : c + 2 ≤ (⌈(c + 2) / c⌉ : ℝ) * c := ceil_mul_ge_cs hc _
  set k : ℤ := ⌊(z.1 + c / 2) / c⌋ with hkd
  have hfl1 : (k : ℝ) ≤ (z.1 + c / 2) / c := Int.floor_le _
  have hfl2 : (z.1 + c / 2) / c < (k : ℝ) + 1 := Int.lt_floor_add_one _
  have h1 : (k : ℝ) * c ≤ z.1 + c / 2 := by rwa [le_div_iff₀ hc] at hfl1
  have h2 : z.1 + c / 2 < (k : ℝ) * c + c := by
    have := hfl2
    rw [div_lt_iff₀ hc] at this
    linarith [show ((k : ℝ) + 1) * c = (k : ℝ) * c + c by ring]
  refine ⟨k, ?_, ?_⟩
  · rw [Finset.mem_Icc]
    have hu : (k : ℝ) < (⌈(c + 2) / c⌉ : ℤ) := by
      have : (k : ℝ) * c < (⌈(c + 2) / c⌉ : ℝ) * c := by linarith
      exact lt_of_mul_lt_mul_right this hc.le
    have hl : -((⌈(c + 2) / c⌉ : ℤ) : ℝ) < (k : ℝ) := by
      have : -(((⌈(c + 2) / c⌉ : ℤ) : ℝ) * c) < (k : ℝ) * c := by linarith
      have h3 : -((⌈(c + 2) / c⌉ : ℤ) : ℝ) * c < (k : ℝ) * c := by linarith
      exact lt_of_mul_lt_mul_right h3 hc.le
    constructor
    · have : -(⌈(c + 2) / c⌉ : ℤ) < k := by exact_mod_cast hl
      omega
    · have : k < ⌈(c + 2) / c⌉ := by exact_mod_cast hu
      omega
  · simp only [B0579.cell, Set.mem_prod, Set.mem_Ico, Set.mem_univ, and_true, Prod.fst_sub,
      Prod.snd_sub, sub_zero]
    constructor <;> linarith

/-- The pointwise bound: the weighted integrand of the translate is dominated by a finite sum of
translates of the weighted integrand on the cell. -/
theorem pointwise_cs {c m : ℝ} (hc : 0 < c) {f : ℝ × ℝ → ℂ}
    (hper : ∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x) {y : ℝ × ℝ} (hy : ‖y‖ ≤ 1) (z : ℝ × ℝ) :
    (B0579.cell c).indicator (fun x => wCS m x * ‖f (x - y)‖ₑ ^ (2 : ℝ)) (z + y) ≤
      ∑ k ∈ Finset.Icc (-(⌈(c + 2) / c⌉)) ⌈(c + 2) / c⌉,
        ENNReal.ofReal (6 ^ |m| * (2 * B0579.jb (((k : ℝ) * c), 0)) ^ |m|) *
          (B0579.cell c).indicator (fun u => wCS m u * ‖f u‖ₑ ^ (2 : ℝ))
            (z - (((k : ℝ) * c), 0)) := by
  by_cases hu : z + y ∈ B0579.cell c
  swap
  · rw [Set.indicator_of_notMem hu]
    exact zero_le
  have hcell := hu
  simp only [B0579.cell, Set.mem_prod, Set.mem_Ico, Set.mem_univ, and_true] at hcell
  have hyb : |y.1| ≤ 1 := by simpa [Real.norm_eq_abs] using (norm_fst_le y).trans hy
  have hc1 : -(c / 2) ≤ z.1 + y.1 := hcell.1
  have hc2 : z.1 + y.1 < c / 2 := hcell.2
  have hz1 : -(c / 2) - 1 ≤ z.1 := by
    have := abs_le.1 hyb
    linarith [this.2]
  have hz2 : z.1 ≤ c / 2 + 1 := by
    have := abs_le.1 hyb
    linarith [this.1]
  obtain ⟨k, hk, hkcell⟩ := floor_cell_cs hc hz1 hz2
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun k : ℤ => ENNReal.ofReal (6 ^ |m| * (2 * B0579.jb (((k : ℝ) * c), 0)) ^ |m|) *
      (B0579.cell c).indicator (fun u => wCS m u * ‖f u‖ₑ ^ (2 : ℝ))
        (z - (((k : ℝ) * c), 0)))
    (fun _ _ => zero_le) hk)
  rw [Set.indicator_of_mem hu, Set.indicator_of_mem hkcell, add_sub_cancel_right,
    per_sub_cs hper k z]
  have h1 := shift_W_cs (m := m) (z := z) hy
  have h2 := step_W_cs m z ((k : ℝ) * c, 0)
  calc wCS m (z + y) * ‖f z‖ₑ ^ (2 : ℝ)
      ≤ (ENNReal.ofReal (6 ^ |m|) * wCS m z) * ‖f z‖ₑ ^ (2 : ℝ) := by gcongr
    _ ≤ (ENNReal.ofReal (6 ^ |m|) * (ENNReal.ofReal ((2 * B0579.jb (((k : ℝ) * c), 0)) ^ |m|) *
          wCS m (z - (((k : ℝ) * c), 0)))) * ‖f z‖ₑ ^ (2 : ℝ) := by gcongr
    _ = ENNReal.ofReal (6 ^ |m| * (2 * B0579.jb (((k : ℝ) * c), 0)) ^ |m|) *
          (wCS m (z - (((k : ℝ) * c), 0)) * ‖f z‖ₑ ^ (2 : ℝ)) := by
        rw [ENNReal.ofReal_mul (by positivity)]
        ring

theorem Aterm_nonneg_cs (c m : ℝ) (k : ℤ) :
    0 ≤ 6 ^ |m| * (2 * B0579.jb (((k : ℝ) * c), 0)) ^ |m| := by
  have := B0579.jb_pos (((k : ℝ) * c), 0)
  positivity

/-- The weighted lintegral of the translate is bounded by `Σ_k A_k` times the weighted lintegral. -/
theorem lintegral_shift_cs {c m : ℝ} (hc : 0 < c) {f : ℝ × ℝ → ℂ}
    (hper : ∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x) {y : ℝ × ℝ} (hy : ‖y‖ ≤ 1)
    (hfa : AEMeasurable (fun x => ‖f x‖ₑ ^ (2 : ℝ)) volume) :
    ∫⁻ x in B0579.cell c, wCS m x * ‖f (x - y)‖ₑ ^ (2 : ℝ) ≤
      (∑ k ∈ Finset.Icc (-(⌈(c + 2) / c⌉)) ⌈(c + 2) / c⌉,
        ENNReal.ofReal (6 ^ |m| * (2 * B0579.jb (((k : ℝ) * c), 0)) ^ |m|)) *
        ∫⁻ x in B0579.cell c, wCS m x * ‖f x‖ₑ ^ (2 : ℝ) := by
  set T : ℝ × ℝ → ℝ≥0∞ := (B0579.cell c).indicator (fun u => wCS m u * ‖f u‖ₑ ^ (2 : ℝ))
    with hTdef
  have hTm : AEMeasurable T volume :=
    ((wCS_meas m).aemeasurable.mul hfa).indicator (B0579.measurableSet_cell c)
  have hT : ∫⁻ u, T u = ∫⁻ x in B0579.cell c, wCS m x * ‖f x‖ₑ ^ (2 : ℝ) :=
    lintegral_indicator (B0579.measurableSet_cell c) _
  have hL : ∫⁻ x in B0579.cell c, wCS m x * ‖f (x - y)‖ₑ ^ (2 : ℝ) =
      ∫⁻ x, (B0579.cell c).indicator (fun x => wCS m x * ‖f (x - y)‖ₑ ^ (2 : ℝ)) x :=
    (lintegral_indicator (B0579.measurableSet_cell c) _).symm
  rw [hL]
  calc ∫⁻ x, (B0579.cell c).indicator (fun x => wCS m x * ‖f (x - y)‖ₑ ^ (2 : ℝ)) x
      = ∫⁻ z, (B0579.cell c).indicator (fun x => wCS m x * ‖f (x - y)‖ₑ ^ (2 : ℝ)) (z + y) :=
        (lintegral_add_right_eq_self _ y).symm
    _ ≤ ∫⁻ z, ∑ k ∈ Finset.Icc (-(⌈(c + 2) / c⌉)) ⌈(c + 2) / c⌉,
          ENNReal.ofReal (6 ^ |m| * (2 * B0579.jb (((k : ℝ) * c), 0)) ^ |m|) *
            T (z - (((k : ℝ) * c), 0)) :=
        lintegral_mono fun z => pointwise_cs hc hper hy z
    _ = ∑ k ∈ Finset.Icc (-(⌈(c + 2) / c⌉)) ⌈(c + 2) / c⌉,
          ENNReal.ofReal (6 ^ |m| * (2 * B0579.jb (((k : ℝ) * c), 0)) ^ |m|) *
            ∫⁻ z, T (z - (((k : ℝ) * c), 0)) := by
        rw [lintegral_finsetSum']
        · apply Finset.sum_congr rfl
          intro k _
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        · intro k _
          exact (hTm.comp_quasiMeasurePreserving (measurePreserving_sub_right volume _).quasiMeasurePreserving).const_mul _
    _ = ∑ k ∈ Finset.Icc (-(⌈(c + 2) / c⌉)) ⌈(c + 2) / c⌉,
          ENNReal.ofReal (6 ^ |m| * (2 * B0579.jb (((k : ℝ) * c), 0)) ^ |m|) * ∫⁻ u, T u := by
        apply Finset.sum_congr rfl
        intro k _
        rw [lintegral_sub_right_eq_self T]
    _ = (∑ k ∈ Finset.Icc (-(⌈(c + 2) / c⌉)) ⌈(c + 2) / c⌉,
          ENNReal.ofReal (6 ^ |m| * (2 * B0579.jb (((k : ℝ) * c), 0)) ^ |m|)) * ∫⁻ u, T u :=
        (Finset.sum_mul _ _ _).symm
    _ = _ := by rw [hT]

/-- The `X_{-m,c}` norm as a weighted lintegral. -/
theorem xNorm_eq_cs (c m : ℝ) (g : ℝ × ℝ → ℂ)
    (hg : AEMeasurable (fun x => ‖g x‖ₑ ^ (2 : ℝ)) volume) :
    xNorm c (-m) g = (∫⁻ x in B0579.cell c, wCS m x * ‖g x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  unfold xNorm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  congr 1
  unfold B0579.cellMeasure
  rw [lintegral_withDensity_eq_lintegral_mul₀
    ((B0579.measurable_density (-m)).coe_nnreal_ennreal.aemeasurable) hg.restrict]
  apply lintegral_congr
  intro x
  simp only [Pi.mul_apply, wCS]
  rw [← ENNReal.ofReal_coe_nnreal, B0579.coe_density]

theorem cellShiftBound : CellShiftBound := by
  intro c m hc
  set F : Finset ℤ := Finset.Icc (-(⌈(c + 2) / c⌉)) ⌈(c + 2) / c⌉ with hF
  set Kr : ℝ := ∑ k ∈ F, 6 ^ |m| * (2 * B0579.jb (((k : ℝ) * c), 0)) ^ |m| with hKr
  have hKr0 : 0 ≤ Kr := Finset.sum_nonneg (fun k _ => Aterm_nonneg_cs c m k)
  refine ⟨Kr ^ (1 / 2 : ℝ), Real.rpow_nonneg hKr0 _, fun f y hper hf hy => ?_⟩
  have hfa : AEMeasurable (fun x => ‖f x‖ₑ ^ (2 : ℝ)) volume :=
    ((perField_aesm hc hper hf).enorm).pow_const (2 : ℝ)
  have hcomp : AEMeasurable (fun x => ‖f (x - y)‖ₑ ^ (2 : ℝ)) volume :=
    hfa.comp_quasiMeasurePreserving (measurePreserving_sub_right volume y).quasiMeasurePreserving
  have hI := lintegral_shift_cs (m := m) hc hper hy hfa
  have hK : (∑ k ∈ F, ENNReal.ofReal (6 ^ |m| * (2 * B0579.jb (((k : ℝ) * c), 0)) ^ |m|)) =
      ENNReal.ofReal Kr :=
    (ENNReal.ofReal_sum_of_nonneg (fun k _ => Aterm_nonneg_cs c m k)).symm
  have hcellAc : B0579.cellMeasure c (-m) ≪ volume :=
    (B0579.cellMeasure_ac c (-m)).trans (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  have hbound : xNorm c (-m) (fun x => f (x - y)) ≤
      ENNReal.ofReal (Kr ^ (1 / 2 : ℝ)) * xNorm c (-m) f := by
    rw [xNorm_eq_cs c m _ hcomp, xNorm_eq_cs c m f hfa,
      ← ENNReal.ofReal_rpow_of_nonneg hKr0 (by norm_num), ← hK]
    exact (ENNReal.rpow_le_rpow hI (by norm_num)).trans_eq
      (ENNReal.mul_rpow_of_nonneg _ _ (by norm_num))
  refine ⟨⟨(perField_aesm hc hper hf |>.comp_measurePreserving
      (measurePreserving_sub_right volume y)).mono_ac hcellAc, ?_⟩, hbound⟩
  exact lt_of_le_of_lt hbound (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.2)

end UnforcedLeray.Short.IIIa
