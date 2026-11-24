import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_18_3_2
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# `FullOutMajorant` (source 3611-3621, 3996-4011)

Pointwise triangle inequality: `|fullOut f x| ≤ 4 s^{-1/2} fullMaj f x`.
`‖(a,b)‖ ≤ |a| + |b|` for the meridional vector, `|Re w| ≤ |w|`, the norm of the
Bochner integral is at most the lintegral of the norm, `|T_jk| ≤ ‖T‖`, and
`‖(l:ℂ)^(2μ+2)‖ = l^(2μ+2)` for real `μ` and `l > 0`. The factor `2` of `-2` and the two
meridional components give the constant `4`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

open UnforcedLeray
open UnforcedLeray.Short.IIIa
open UnforcedLeray.Short.PartIIIb.NearInst
open UnforcedLeray.Short.PartIIIb.NearInst.Masked
open UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

theorem fm_abs_entry_le (M : Matrix (Fin 3) (Fin 3) ℝ) (j k : Fin 3) :
    |M j k| ≤ tensorNorm M := by
  unfold tensorNorm
  apply Real.abs_le_sqrt
  calc M j k ^ 2 ≤ ∑ j', M j j' ^ 2 :=
        Finset.single_le_sum (f := fun j' => M j j' ^ 2) (fun _ _ => sq_nonneg _)
          (Finset.mem_univ k)
    _ ≤ ∑ i', ∑ j', M i' j' ^ 2 :=
        Finset.single_le_sum (f := fun i' => ∑ j', M i' j' ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ j)

theorem fm_abs_sum_le (D M : Matrix (Fin 3) (Fin 3) ℝ) :
    |∑ j, ∑ k, D j k * M j k| ≤ (∑ j, ∑ k, |D j k|) * tensorNorm M := by
  calc |∑ j, ∑ k, D j k * M j k| ≤ ∑ j, ∑ k, |D j k * M j k| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ j, ∑ k, |D j k| * |M j k| := by simp only [abs_mul]
    _ ≤ ∑ j, ∑ k, |D j k| * tensorNorm M :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_left (fm_abs_entry_le M j k) (abs_nonneg _)
    _ = (∑ j, ∑ k, |D j k|) * tensorNorm M := by simp only [Finset.sum_mul]

theorem fm_row_norm (t : ℝ) (w : Space) (i : Fin 3) (M : Matrix (Fin 3) (Fin 3) ℝ) :
    ‖∑ j : Fin 3, ∑ k : Fin 3,
        ((fderiv ℝ (fun x => UnforcedLeray.Short.IIIa.heatLerayK t i j x) w
          (coordinateVector k) : ℝ) : ℂ) * ((M j k : ℝ) : ℂ)‖ₑ
      ≤ gradKNorm t w * ENNReal.ofReal (tensorNorm M) := by
  have hcast : ∑ j : Fin 3, ∑ k : Fin 3,
        ((fderiv ℝ (fun x => UnforcedLeray.Short.IIIa.heatLerayK t i j x) w
          (coordinateVector k) : ℝ) : ℂ) * ((M j k : ℝ) : ℂ)
      = (((∑ j : Fin 3, ∑ k : Fin 3,
          fderiv ℝ (fun x => UnforcedLeray.Short.IIIa.heatLerayK t i j x) w
            (coordinateVector k) * M j k : ℝ)) : ℂ) := by
    push_cast
    rfl
  rw [hcast, ← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs]
  have hA : 0 ≤ ∑ j : Fin 3, ∑ k : Fin 3,
      |fderiv ℝ (fun x => UnforcedLeray.Short.IIIa.heatLerayK t i j x) w (coordinateVector k)| :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  calc ENNReal.ofReal |∑ j : Fin 3, ∑ k : Fin 3,
          fderiv ℝ (fun x => UnforcedLeray.Short.IIIa.heatLerayK t i j x) w
            (coordinateVector k) * M j k|
      ≤ ENNReal.ofReal ((∑ j : Fin 3, ∑ k : Fin 3,
          |fderiv ℝ (fun x => UnforcedLeray.Short.IIIa.heatLerayK t i j x) w
            (coordinateVector k)|) * tensorNorm M) :=
        ENNReal.ofReal_le_ofReal (fm_abs_sum_le
          (fun j k => fderiv ℝ (fun x => UnforcedLeray.Short.IIIa.heatLerayK t i j x) w
            (coordinateVector k)) M)
    _ = ENNReal.ofReal (∑ j : Fin 3, ∑ k : Fin 3,
          |fderiv ℝ (fun x => UnforcedLeray.Short.IIIa.heatLerayK t i j x) w
            (coordinateVector k)|) * ENNReal.ofReal (tensorNorm M) :=
        ENNReal.ofReal_mul hA
    _ ≤ gradKNorm t w * ENNReal.ofReal (tensorNorm M) := by
        unfold gradKNorm
        apply mul_le_mul_of_nonneg_right _ (by simp)
        apply ENNReal.ofReal_le_ofReal
        refine Finset.single_le_sum (f := fun i' : Fin 3 => ∑ j : Fin 3, ∑ k : Fin 3,
          |fderiv ℝ (fun x => UnforcedLeray.Short.IIIa.heatLerayK t i' j x) w
            (coordinateVector k)|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
          (Finset.mem_univ i)

theorem fm_sepW_le (ν : ℝ) (μ : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (y : Space) (τ : ℝ) (i : Fin 3) :
    ‖sepW ν (μ : ℂ) T y τ i‖ₑ ≤ ENNReal.ofReal 2 *
      ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (2 * μ + 2)) *
        ∫⁻ z : Space, gradKNorm (ν * (1 - l ^ 2)) (y - l • z) *
          ENNReal.ofReal (tensorNorm (T (τ + 2 * Real.log l) z)) := by
  unfold sepW
  have hm2 : ‖(-2 : ℂ)‖ₑ = ENNReal.ofReal 2 := by
    rw [← ofReal_norm_eq_enorm]
    norm_num
  rw [enorm_mul, hm2]
  gcongr
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  refine setLIntegral_mono' measurableSet_Ioo fun l hl => ?_
  have hl0 : 0 < l := hl.1
  have hc : ‖(l : ℂ) ^ (2 * (μ : ℂ) + 2)‖ₑ = ENNReal.ofReal (l ^ (2 * μ + 2)) := by
    rw [← ofReal_norm_eq_enorm, Complex.norm_cpow_eq_rpow_re_of_pos hl0]
    congr 1
    simp
  rw [enorm_mul, hc]
  gcongr
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun z => ?_)
  exact fm_row_norm (ν * (1 - l ^ 2)) (y - l • z) i (T (τ + 2 * Real.log l) z)

theorem fm_merRe_le (W : Fin 3 → ℂ) :
    ‖merRe W‖ₑ ≤ ‖W 0‖ₑ + ‖W 2‖ₑ := by
  rw [← ofReal_norm_eq_enorm (merRe W), ← ofReal_norm_eq_enorm (W 0),
    ← ofReal_norm_eq_enorm (W 2), ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hre : ∀ z : ℂ, ‖z.re‖ ≤ ‖z‖ := fun z => by
    rw [Real.norm_eq_abs]
    exact Complex.abs_re_le_norm z
  have hx0 : ‖(merRe W) 0‖ ≤ ‖W 0‖ := by simpa [merRe] using hre (W 0)
  have hx1 : ‖(merRe W) 1‖ ≤ ‖W 2‖ := by simpa [merRe] using hre (W 2)
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  calc √(‖(merRe W) 0‖ ^ 2 + ‖(merRe W) 1‖ ^ 2)
      ≤ √((‖W 0‖ + ‖W 2‖) ^ 2) := by
        apply Real.sqrt_le_sqrt
        nlinarith [mul_nonneg (norm_nonneg (W 0)) (norm_nonneg (W 2)),
          mul_le_mul hx0 hx0 (norm_nonneg _) (norm_nonneg _),
          mul_le_mul hx1 hx1 (norm_nonneg _) (norm_nonneg _)]
    _ = ‖W 0‖ + ‖W 2‖ := Real.sqrt_sq (by positivity)

theorem fullOutMajorant :
    UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.FullOutMajorant := by
  unfold UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.FullOutMajorant
  intro R c ν μ hR hc hν f _hf x
  by_cases hs : x.1 ≤ 0
  · have h0 : fullOut R c ν μ f x = 0 := by
      unfold fullOut
      simp [Real.sqrt_eq_zero'.2 hs]
    rw [h0, norm_zero, ENNReal.ofReal_zero]
    simp
  · push_neg at hs
    have ha0 : 0 < (Real.sqrt x.1)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hs)
    have hfo : ‖fullOut R c ν μ f x‖ₑ
        = ENNReal.ofReal (Real.sqrt x.1)⁻¹ *
          ‖merRe (-sepW ν (μ : ℂ) (cartLift R c f) (chartY R x) (chartTau R x))‖ₑ := by
      unfold fullOut
      rw [enorm_smul, Real.enorm_eq_ofReal ha0.le]
    have hW : ∀ i : Fin 3,
        ‖(-sepW ν (μ : ℂ) (cartLift R c f) (chartY R x) (chartTau R x)) i‖ₑ
          ≤ ENNReal.ofReal 2 * fullMaj R c ν μ f x := by
      intro i
      rw [Pi.neg_apply, enorm_neg]
      exact fm_sepW_le ν μ (cartLift R c f) (chartY R x) (chartTau R x) i
    have hmer : ‖merRe (-sepW ν (μ : ℂ) (cartLift R c f) (chartY R x) (chartTau R x))‖ₑ
        ≤ ENNReal.ofReal 4 * fullMaj R c ν μ f x := by
      refine (fm_merRe_le _).trans ?_
      have h4 : ENNReal.ofReal 4 = ENNReal.ofReal 2 + ENNReal.ofReal 2 := by
        rw [← ENNReal.ofReal_add] <;> norm_num
      rw [h4, add_mul]
      exact add_le_add (hW 0) (hW 2)
    rw [ofReal_norm_eq_enorm, hfo]
    calc ENNReal.ofReal (Real.sqrt x.1)⁻¹ *
          ‖merRe (-sepW ν (μ : ℂ) (cartLift R c f) (chartY R x) (chartTau R x))‖ₑ
        ≤ ENNReal.ofReal (Real.sqrt x.1)⁻¹ * (ENNReal.ofReal 4 * fullMaj R c ν μ f x) :=
          mul_le_mul_of_nonneg_left hmer (by simp)
      _ = ENNReal.ofReal 4 * (ENNReal.ofReal (Real.sqrt x.1)⁻¹ * fullMaj R c ν μ f x) := by
          ring
