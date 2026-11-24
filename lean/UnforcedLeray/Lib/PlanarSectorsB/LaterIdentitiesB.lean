import UnforcedLeray.Lib.PlanarSectorsB.LaterIdentities
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Later-chapter planar identities, part 2 (INF12 target P10: B0832, B0232 core)


§5, Level P, target **P10** ("explicit angular integrals and radial moments, one lemma per
unit"); continues `LaterIdentities.lean`.

* **B0832** (`eq:affine-4-80`, `eq:affine-4-81`, `paper/main.tex` lines 12274–12286): the mean
  thin sheet `Σ_rr = ρ⁻¹E_η`, `Σ_zz = ρ⁻¹E_q`, `Σ_rz = ρ⁻¹C` (`ρ = u^{-1/2}`, azimuthal entries
  `0`), rotated to Cartesian coordinates (`cartSheet`) and integrated over the transverse disk
  `ρ < ρ_o = u_o^{-1/2}` (i.e. `u > u_o`), is `diag(T_h, T_h, T_z)` with
  `T_h = (π/2)∫_{u_o}^∞ E_η u^{-3/2}du`, `T_z = π∫_{u_o}^∞ E_q u^{-3/2}du`
  (`integratedSheet_eq_diagonal`), hence `T_z - T_h = (π/2)I_T`,
  `I_T = ∫_{u_o}^∞(2E_q - E_η)u^{-3/2}du` (`Tz_sub_Th`); the cross stress `Σ_rz` has zero
  integrated Cartesian tensor. The angular integrals are `integral_cos_sq_two_pi`,
  `integral_sin_sq_two_pi`, `integral_sin_mul_cos_two_pi`, `integral_cos_two_pi`,
  `integral_sin_two_pi`, and the substitution `dρ = -½u^{-3/2}du` is `integral_sheet_subst`.
  Hypotheses: `u_o > 0` and integrability of `E_η u^{-3/2}`, `E_q u^{-3/2}`, `C u^{-3/2}` on
  `(u_o, ∞)` (the manuscript's integrals exist). The contraction of `T_hI` against `∂_iΔN` at the
  receiver (harmonicity of the Newton kernel) is not built here.
* **B0232**, core only (`paper/main.tex` lines 3978–3987, "combining the two real angular
  modes"): `angularTwo_farField`:
  `(α cos2θ + β sin2θ)/r² = ½(α + iβ)(q + iη)^{-2} + ½(α - iβ)(q - iη)^{-2}` at
  `q + iη = re^{iθ}`, `r > 0`. The heat scaling of `g_H` and the Gaussian remainder bounds of
  `r_H` are not built (they use the dual kernel of later chapters).

Not built: `B0824` (curl of the isolated affine source) and the consequence `Q_∞D = 0` of
`B0372`. The plane part of `B0388` is in `StressMoments.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real Metric
open scoped ComplexConjugate

namespace UnforcedLeray.Planar

open UnforcedLeray.Planar.NUE

/-! ### Angular integrals over a full turn -/

theorem integral_cos_sq_two_pi : ∫ θ in (0 : ℝ)..2 * π, Real.cos θ ^ 2 = π := by
  rw [integral_cos_sq, Real.sin_two_pi, Real.sin_zero]
  ring

theorem integral_sin_sq_two_pi : ∫ θ in (0 : ℝ)..2 * π, Real.sin θ ^ 2 = π := by
  rw [integral_sin_sq, Real.sin_two_pi, Real.sin_zero]
  ring

theorem integral_sin_mul_cos_two_pi :
    ∫ θ in (0 : ℝ)..2 * π, Real.sin θ * Real.cos θ = 0 := by
  rw [integral_sin_mul_cos₁, Real.sin_two_pi, Real.sin_zero]
  ring

theorem integral_cos_two_pi : ∫ θ in (0 : ℝ)..2 * π, Real.cos θ = 0 := by
  rw [integral_cos, Real.sin_two_pi, Real.sin_zero, sub_zero]

theorem integral_sin_two_pi : ∫ θ in (0 : ℝ)..2 * π, Real.sin θ = 0 := by
  rw [integral_sin, Real.cos_two_pi, Real.cos_zero, sub_self]

theorem circleMap_zero_re (r θ : ℝ) : (circleMap 0 r θ).re = r * Real.cos θ := by
  rw [circleMap_zero]
  simp [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

theorem circleMap_zero_im (r θ : ℝ) : (circleMap 0 r θ).im = r * Real.sin θ := by
  rw [circleMap_zero]
  simp [Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

theorem re_div_norm_circleMap {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    (circleMap 0 r θ).re / ‖circleMap 0 r θ‖ = Real.cos θ := by
  rw [circleMap_zero_re, norm_circleMap_zero, abs_of_pos hr]
  field_simp

theorem im_div_norm_circleMap {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    (circleMap 0 r θ).im / ‖circleMap 0 r θ‖ = Real.sin θ := by
  rw [circleMap_zero_im, norm_circleMap_zero, abs_of_pos hr]
  field_simp

theorem abs_re_div_norm_le_one (x : ℂ) : |x.re / ‖x‖| ≤ 1 := by
  rw [abs_div, abs_norm]
  rcases eq_or_lt_of_le (norm_nonneg x) with h | h
  · rw [← h, div_zero]
    exact zero_le_one
  · exact div_le_one_of_le₀ (Complex.abs_re_le_norm x) h.le

theorem abs_im_div_norm_le_one (x : ℂ) : |x.im / ‖x‖| ≤ 1 := by
  rw [abs_div, abs_norm]
  rcases eq_or_lt_of_le (norm_nonneg x) with h | h
  · rw [← h, div_zero]
    exact zero_le_one
  · exact div_le_one_of_le₀ (Complex.abs_im_le_norm x) h.le

theorem measurable_re_div_norm : Measurable fun x : ℂ => x.re / ‖x‖ :=
  Complex.measurable_re.div measurable_norm

theorem measurable_im_div_norm : Measurable fun x : ℂ => x.im / ‖x‖ :=
  Complex.measurable_im.div measurable_norm

/-! ### Disk integrals of angular factors times radial profiles -/

/-- `∫_{B_ρ} A(x) S(|x|) dx = ∫₀^ρ r S(r) (∫₀^{2π} A(re^{iθ}) dθ) dr` for a bounded measurable
angular factor `A` and `r S(r)` integrable on `(0, ρ)`. -/
theorem setIntegral_ball_angular {S : ℝ → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hS : IntegrableOn (fun r => r * S r) (Ioo 0 ρ)) {A : ℂ → ℝ} (hA : Measurable A)
    (hA1 : ∀ x, |A x| ≤ 1) :
    ∫ x in ball (0 : ℂ) ρ, A x * S ‖x‖ =
      ∫ r in (0 : ℝ)..ρ, r * S r * ∫ θ in (0 : ℝ)..2 * π, A (circleMap 0 r θ) := by
  have hSb : IntegrableOn (fun x : ℂ => S ‖x‖) (ball 0 ρ) :=
    (Polar.integrableOn_ball_comp_norm_iff hρ).2 (by simpa only [smul_eq_mul] using hS)
  have hF : IntegrableOn (fun x : ℂ => A x * S ‖x‖) (ball 0 ρ) := by
    refine hSb.norm.mono' (hA.aestronglyMeasurable.mul hSb.1) (Eventually.of_forall fun x => ?_)
    rw [norm_mul, Real.norm_eq_abs]
    calc |A x| * ‖S ‖x‖‖ ≤ 1 * ‖S ‖x‖‖ := mul_le_mul_of_nonneg_right (hA1 x) (norm_nonneg _)
      _ = ‖S ‖x‖‖ := one_mul _
  rw [← integral_indicator measurableSet_ball,
    Polar.integral_eq_integral_Ioi_intervalIntegral (hF.integrable_indicator measurableSet_ball)]
  have hin : ∀ r ∈ Ioi (0 : ℝ), r • ∫ θ in (0 : ℝ)..2 * π,
      (ball (0 : ℂ) ρ).indicator (fun x => A x * S ‖x‖) (circleMap 0 r θ) =
      (Iio ρ).indicator (fun r => r * S r * ∫ θ in (0 : ℝ)..2 * π, A (circleMap 0 r θ)) r := by
    intro r hr
    have hr' : (0 : ℝ) < r := hr
    have hmem : ∀ θ, circleMap 0 r θ ∈ ball (0 : ℂ) ρ ↔ r < ρ := fun θ => by
      rw [mem_ball_zero_iff, norm_circleMap_zero, abs_of_pos hr']
    by_cases h : r < ρ
    · rw [indicator_of_mem (show r ∈ Iio ρ from h)]
      have e : ∀ θ, (ball (0 : ℂ) ρ).indicator (fun x => A x * S ‖x‖) (circleMap 0 r θ) =
          S r * A (circleMap 0 r θ) := fun θ => by
        rw [indicator_of_mem ((hmem θ).2 h), norm_circleMap_zero, abs_of_pos hr', mul_comm]
      simp_rw [e]
      rw [intervalIntegral.integral_const_mul, smul_eq_mul]
      ring
    · rw [indicator_of_notMem (show r ∉ Iio ρ from h)]
      have e : ∀ θ, (ball (0 : ℂ) ρ).indicator (fun x => A x * S ‖x‖) (circleMap 0 r θ) = 0 :=
        fun θ => indicator_of_notMem (fun hm => h ((hmem θ).1 hm)) _
      simp_rw [e]
      simp
  rw [setIntegral_congr_fun measurableSet_Ioi hin, setIntegral_indicator measurableSet_Iio,
    Ioi_inter_Iio, intervalIntegral.integral_of_le hρ, integral_Ioc_eq_integral_Ioo]

/-! ### The substitution `ρ = u^{-1/2}` -/

theorem rpow_neg_half_sq_inv {u : ℝ} (hu : 0 < u) : ((u ^ (-(1 / 2 : ℝ))) ^ 2)⁻¹ = u := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le]
  norm_num
  rw [Real.rpow_neg_one, inv_inv]

theorem rpow_neg_half_lt_iff {u uo : ℝ} (hu : 0 < u) (huo : 0 < uo) :
    u ^ (-(1 / 2 : ℝ)) < uo ^ (-(1 / 2 : ℝ)) ↔ uo < u :=
  Real.rpow_lt_rpow_iff_of_neg hu huo (by norm_num)

/-- The pulled-back integrand of the substitution. -/
theorem sheet_subst_pointwise (E : ℝ → ℝ) {uo u : ℝ} (huo : 0 < uo) (hu : 0 < u) :
    (|(-(1 / 2 : ℝ))| * u ^ (-(1 / 2 : ℝ) - 1)) •
        (Iio (uo ^ (-(1 / 2 : ℝ)))).indicator (fun r => E ((r ^ 2)⁻¹)) (u ^ (-(1 / 2 : ℝ))) =
      (Ioi uo).indicator (fun u => 1 / 2 * (E u * u ^ (-(3 / 2 : ℝ)))) u := by
  have h32 : -(1 / 2 : ℝ) - 1 = -(3 / 2) := by norm_num
  have hab : |(-(1 / 2 : ℝ))| = 1 / 2 := by norm_num
  rw [h32, hab, smul_eq_mul]
  by_cases h : uo < u
  · rw [indicator_of_mem (show u ^ (-(1 / 2 : ℝ)) ∈ Iio (uo ^ (-(1 / 2 : ℝ))) from
      (rpow_neg_half_lt_iff hu huo).2 h), indicator_of_mem (show u ∈ Ioi uo from h),
      rpow_neg_half_sq_inv hu]
    ring
  · rw [indicator_of_notMem (show u ^ (-(1 / 2 : ℝ)) ∉ Iio (uo ^ (-(1 / 2 : ℝ))) from
      fun hm => h ((rpow_neg_half_lt_iff hu huo).1 hm)), indicator_of_notMem (show u ∉ Ioi uo
      from h), mul_zero]

theorem sheet_integrableOn {E : ℝ → ℝ} {uo : ℝ} (huo : 0 < uo)
    (hE : IntegrableOn (fun u => E u * u ^ (-(3 / 2 : ℝ))) (Ioi uo)) :
    IntegrableOn (fun r => r * (r⁻¹ * E ((r ^ 2)⁻¹))) (Ioo 0 (uo ^ (-(1 / 2 : ℝ)))) := by
  set f : ℝ → ℝ := (Iio (uo ^ (-(1 / 2 : ℝ)))).indicator (fun r => E ((r ^ 2)⁻¹))
  have key := (integrableOn_Ioi_comp_rpow_iff f (p := -(1 / 2 : ℝ)) (by norm_num)).1 (by
    have h1 : IntegrableOn ((Ioi uo).indicator fun u => 1 / 2 * (E u * u ^ (-(3 / 2 : ℝ))))
        (Ioi 0) := by
      rw [integrableOn_indicator_iff measurableSet_Ioi]
      exact IntegrableOn.mono_set (hE.const_mul (1 / 2)) inter_subset_left
    refine h1.congr_fun (fun u hu => (sheet_subst_pointwise E huo hu).symm) measurableSet_Ioi)
  rw [integrableOn_indicator_iff measurableSet_Iio, inter_comm, Ioi_inter_Iio] at key
  refine key.congr_fun (fun r hr => ?_) measurableSet_Ioo
  have hr0 : r ≠ 0 := hr.1.ne'
  field_simp

/-- **The substitution `ρ = u^{-1/2}`, `dρ = -½u^{-3/2}du`** (`paper/main.tex` line 12279):
`∫₀^{ρ_o} ρ·ρ⁻¹E(ρ^{-2}) dρ = ½∫_{u_o}^∞ E(u)u^{-3/2} du`, `ρ_o = u_o^{-1/2}` (no integrability
hypothesis: both sides are Bochner integrals related by `integral_comp_rpow_Ioi`). -/
theorem integral_sheet_subst (E : ℝ → ℝ) {uo : ℝ} (huo : 0 < uo) :
    ∫ r in (0 : ℝ)..uo ^ (-(1 / 2 : ℝ)), r * (r⁻¹ * E ((r ^ 2)⁻¹)) =
      1 / 2 * ∫ u in Ioi uo, E u * u ^ (-(3 / 2 : ℝ)) := by
  have hρ : 0 < uo ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos huo _
  set f : ℝ → ℝ := (Iio (uo ^ (-(1 / 2 : ℝ)))).indicator (fun r => E ((r ^ 2)⁻¹))
  have key := integral_comp_rpow_Ioi f (p := -(1 / 2 : ℝ)) (by norm_num)
  rw [setIntegral_congr_fun measurableSet_Ioi (fun u hu => sheet_subst_pointwise E huo hu),
    setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right huo.le,
    setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio, integral_const_mul] at key
  rw [key, intervalIntegral.integral_of_le hρ.le, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun r hr => ?_
  have hr0 : r ≠ 0 := hr.1.ne'
  field_simp

/-! ### B0832: the integrated Cartesian tensor of the mean thin sheet -/

/-- A sheet stress component `ρ⁻¹E(u)` at the transverse point `x`, `ρ = |x|`, `u = ρ⁻²`
(`eq:affine-4-80`, `paper/main.tex` lines 12268–12272). -/
def sheetStress (E : ℝ → ℝ) (x : ℂ) : ℝ := ‖x‖⁻¹ * E ((‖x‖ ^ 2)⁻¹)

/-- The cylindrical sheet tensor in the frame `(e_ρ, e_φ, e_z)`: `Σ_rr = ρ⁻¹E_η`,
`Σ_zz = ρ⁻¹E_q`, `Σ_rz = ρ⁻¹C`, azimuthal entries `0` (`eq:affine-4-80`). -/
def cylSheet (Eη Eq C : ℝ → ℝ) (x : ℂ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![sheetStress Eη x, 0, sheetStress C x; 0, 0, 0; sheetStress C x, 0, sheetStress Eq x]

/-- The rotation from the cylindrical frame at `x = ρe^{iφ}` to Cartesian axes:
columns `e_ρ = (cos φ, sin φ, 0)`, `e_φ = (-sin φ, cos φ, 0)`, `e_z`. -/
def cylFrame (x : ℂ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![x.re / ‖x‖, -(x.im / ‖x‖), 0; x.im / ‖x‖, x.re / ‖x‖, 0; 0, 0, 1]

/-- The Cartesian sheet tensor `R Σ_cyl Rᵀ`. -/
def cartSheet (Eη Eq C : ℝ → ℝ) (x : ℂ) : Matrix (Fin 3) (Fin 3) ℝ :=
  cylFrame x * cylSheet Eη Eq C x * (cylFrame x).transpose

theorem cartSheet_eq (Eη Eq C : ℝ → ℝ) (x : ℂ) :
    cartSheet Eη Eq C x =
      !![(x.re / ‖x‖) ^ 2 * sheetStress Eη x, (x.re / ‖x‖) * (x.im / ‖x‖) * sheetStress Eη x,
          (x.re / ‖x‖) * sheetStress C x;
        (x.re / ‖x‖) * (x.im / ‖x‖) * sheetStress Eη x, (x.im / ‖x‖) ^ 2 * sheetStress Eη x,
          (x.im / ‖x‖) * sheetStress C x;
        (x.re / ‖x‖) * sheetStress C x, (x.im / ‖x‖) * sheetStress C x, sheetStress Eq x] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cartSheet, cylFrame, cylSheet, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

/-- The integrated Cartesian tensor of the sheet over the transverse disk `|x| < ρ_o`
(`paper/main.tex` line 12276). -/
def integratedSheet (Eη Eq C : ℝ → ℝ) (ρo : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => ∫ x in ball (0 : ℂ) ρo, cartSheet Eη Eq C x i j

theorem sheet_integrableOn_ball {E : ℝ → ℝ} {uo : ℝ} (huo : 0 < uo)
    (hE : IntegrableOn (fun u => E u * u ^ (-(3 / 2 : ℝ))) (Ioi uo)) :
    IntegrableOn (fun r => r * (r⁻¹ * E ((r ^ 2)⁻¹))) (Ioo 0 (uo ^ (-(1 / 2 : ℝ)))) :=
  sheet_integrableOn huo hE

/-- One angular-factor disk integral of a sheet component. -/
theorem integral_ball_sheet {E : ℝ → ℝ} {uo : ℝ} (huo : 0 < uo)
    (hE : IntegrableOn (fun u => E u * u ^ (-(3 / 2 : ℝ))) (Ioi uo)) {A : ℂ → ℝ}
    (hA : Measurable A) (hA1 : ∀ x, |A x| ≤ 1) {a : ℝ}
    (hAc : ∀ r : ℝ, 0 < r → ∫ θ in (0 : ℝ)..2 * π, A (circleMap 0 r θ) = a) :
    ∫ x in ball (0 : ℂ) (uo ^ (-(1 / 2 : ℝ))), A x * sheetStress E x =
      a / 2 * ∫ u in Ioi uo, E u * u ^ (-(3 / 2 : ℝ)) := by
  have hρ : 0 < uo ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos huo _
  have h := setIntegral_ball_angular (S := fun r => r⁻¹ * E ((r ^ 2)⁻¹)) hρ.le
    (sheet_integrableOn huo hE) hA hA1
  have e : ∫ r in (0 : ℝ)..uo ^ (-(1 / 2 : ℝ)), r * (r⁻¹ * E ((r ^ 2)⁻¹)) *
      ∫ θ in (0 : ℝ)..2 * π, A (circleMap 0 r θ) =
      ∫ r in (0 : ℝ)..uo ^ (-(1 / 2 : ℝ)), r * (r⁻¹ * E ((r ^ 2)⁻¹)) * a := by
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun r hr => ?_)
    rw [uIoc_of_le hρ.le] at hr
    rw [hAc r hr.1]
  unfold sheetStress
  rw [h, e, intervalIntegral.integral_mul_const, integral_sheet_subst E huo]
  ring

/-- **B0832** (`eq:affine-4-81`, `paper/main.tex` lines 12274–12286): the integrated Cartesian
tensor of the mean thin sheet over `u > u_o` (`ρ < ρ_o = u_o^{-1/2}`) is `diag(T_h, T_h, T_z)`
with `T_h = (π/2)∫_{u_o}^∞ E_η u^{-3/2}du` and `T_z = π∫_{u_o}^∞ E_q u^{-3/2}du`; in particular
the cross stress `Σ_rz` has zero integrated Cartesian tensor. -/
theorem integratedSheet_eq_diagonal {Eη Eq C : ℝ → ℝ} {uo : ℝ} (huo : 0 < uo)
    (hη : IntegrableOn (fun u => Eη u * u ^ (-(3 / 2 : ℝ))) (Ioi uo))
    (hq : IntegrableOn (fun u => Eq u * u ^ (-(3 / 2 : ℝ))) (Ioi uo))
    (hC : IntegrableOn (fun u => C u * u ^ (-(3 / 2 : ℝ))) (Ioi uo)) :
    integratedSheet Eη Eq C (uo ^ (-(1 / 2 : ℝ))) =
      Matrix.diagonal ![π / 2 * ∫ u in Ioi uo, Eη u * u ^ (-(3 / 2 : ℝ)),
        π / 2 * ∫ u in Ioi uo, Eη u * u ^ (-(3 / 2 : ℝ)),
        π * ∫ u in Ioi uo, Eq u * u ^ (-(3 / 2 : ℝ))] := by
  have hc2 : ∀ x : ℂ, |(x.re / ‖x‖) ^ 2| ≤ 1 := fun x => by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (abs_re_div_norm_le_one x)
  have hs2 : ∀ x : ℂ, |(x.im / ‖x‖) ^ 2| ≤ 1 := fun x => by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (abs_im_div_norm_le_one x)
  have hcs : ∀ x : ℂ, |(x.re / ‖x‖) * (x.im / ‖x‖)| ≤ 1 := fun x => by
    rw [abs_mul]
    exact mul_le_one₀ (abs_re_div_norm_le_one x) (abs_nonneg _) (abs_im_div_norm_le_one x)
  have h1 : ∀ x : ℂ, |(1 : ℝ)| ≤ 1 := fun _ => by norm_num
  set ρ := uo ^ (-(1 / 2 : ℝ))
  have Ixx := integral_ball_sheet huo hη (A := fun x => (x.re / ‖x‖) ^ 2)
    (measurable_re_div_norm.pow_const 2) hc2 (a := π)
    (fun r hr => by simp_rw [re_div_norm_circleMap hr]; exact integral_cos_sq_two_pi)
  have Iyy := integral_ball_sheet huo hη (A := fun x => (x.im / ‖x‖) ^ 2)
    (measurable_im_div_norm.pow_const 2) hs2 (a := π)
    (fun r hr => by simp_rw [im_div_norm_circleMap hr]; exact integral_sin_sq_two_pi)
  have Ixy := integral_ball_sheet huo hη (A := fun x => x.re / ‖x‖ * (x.im / ‖x‖))
    (measurable_re_div_norm.mul measurable_im_div_norm) hcs (a := 0) (fun r hr => by
      simp_rw [re_div_norm_circleMap hr, im_div_norm_circleMap hr, mul_comm (Real.cos _)]
      exact integral_sin_mul_cos_two_pi)
  have Ixz := integral_ball_sheet huo hC (A := fun x => x.re / ‖x‖) measurable_re_div_norm
    abs_re_div_norm_le_one (a := 0)
    (fun r hr => by simp_rw [re_div_norm_circleMap hr]; exact integral_cos_two_pi)
  have Iyz := integral_ball_sheet huo hC (A := fun x => x.im / ‖x‖) measurable_im_div_norm
    abs_im_div_norm_le_one (a := 0)
    (fun r hr => by simp_rw [im_div_norm_circleMap hr]; exact integral_sin_two_pi)
  have Izz := integral_ball_sheet huo hq (A := fun _ => (1 : ℝ)) measurable_const h1 (a := 2 * π)
    (fun r _ => by simp)
  have Izz' : ∫ x in ball (0 : ℂ) ρ, sheetStress Eq x =
      π * ∫ u in Ioi uo, Eq u * u ^ (-(3 / 2 : ℝ)) := by
    have e : (fun x => sheetStress Eq x) = fun x => (fun _ : ℂ => (1 : ℝ)) x * sheetStress Eq x :=
      funext fun x => (one_mul _).symm
    rw [e, Izz]
    ring
  have c : ∀ i j, integratedSheet Eη Eq C ρ i j =
      ∫ x in ball (0 : ℂ) ρ, cartSheet Eη Eq C x i j := fun i j => rfl
  have c00 : ∀ x, cartSheet Eη Eq C x 0 0 = (x.re / ‖x‖) ^ 2 * sheetStress Eη x := fun x => by
    rw [cartSheet_eq]; rfl
  have c01 : ∀ x, cartSheet Eη Eq C x 0 1 = x.re / ‖x‖ * (x.im / ‖x‖) * sheetStress Eη x :=
    fun x => by rw [cartSheet_eq]; rfl
  have c02 : ∀ x, cartSheet Eη Eq C x 0 2 = x.re / ‖x‖ * sheetStress C x := fun x => by
    rw [cartSheet_eq]; rfl
  have c10 : ∀ x, cartSheet Eη Eq C x 1 0 = x.re / ‖x‖ * (x.im / ‖x‖) * sheetStress Eη x :=
    fun x => by rw [cartSheet_eq]; rfl
  have c11 : ∀ x, cartSheet Eη Eq C x 1 1 = (x.im / ‖x‖) ^ 2 * sheetStress Eη x := fun x => by
    rw [cartSheet_eq]; rfl
  have c12 : ∀ x, cartSheet Eη Eq C x 1 2 = x.im / ‖x‖ * sheetStress C x := fun x => by
    rw [cartSheet_eq]; rfl
  have c20 : ∀ x, cartSheet Eη Eq C x 2 0 = x.re / ‖x‖ * sheetStress C x := fun x => by
    rw [cartSheet_eq]; rfl
  have c21 : ∀ x, cartSheet Eη Eq C x 2 1 = x.im / ‖x‖ * sheetStress C x := fun x => by
    rw [cartSheet_eq]; rfl
  have c22 : ∀ x, cartSheet Eη Eq C x 2 2 = sheetStress Eq x := fun x => by
    rw [cartSheet_eq]; rfl
  rw [Matrix.eta_fin_three (integratedSheet Eη Eq C ρ), Matrix.eta_fin_three (Matrix.diagonal _)]
  simp only [c]
  simp_rw [c00, c01, c02, c10, c11, c12, c20, c21, c22]
  rw [Ixx, Iyy, Ixy, Ixz, Iyz, Izz']
  simp [Matrix.diagonal]

/-- **B0832**, `eq:affine-4-81`: `T_z - T_h = (π/2) I_T`,
`I_T = ∫_{u_o}^∞ (2E_q - E_η) u^{-3/2} du`. -/
theorem Tz_sub_Th {Eη Eq C : ℝ → ℝ} {uo : ℝ} (huo : 0 < uo)
    (hη : IntegrableOn (fun u => Eη u * u ^ (-(3 / 2 : ℝ))) (Ioi uo))
    (hq : IntegrableOn (fun u => Eq u * u ^ (-(3 / 2 : ℝ))) (Ioi uo))
    (hC : IntegrableOn (fun u => C u * u ^ (-(3 / 2 : ℝ))) (Ioi uo)) :
    integratedSheet Eη Eq C (uo ^ (-(1 / 2 : ℝ))) 2 2 -
        integratedSheet Eη Eq C (uo ^ (-(1 / 2 : ℝ))) 0 0 =
      π / 2 * ∫ u in Ioi uo, (2 * Eq u - Eη u) * u ^ (-(3 / 2 : ℝ)) := by
  rw [integratedSheet_eq_diagonal huo hη hq hC]
  have e : (fun u => (2 * Eq u - Eη u) * u ^ (-(3 / 2 : ℝ))) =
      fun u => 2 * (Eq u * u ^ (-(3 / 2 : ℝ))) - Eη u * u ^ (-(3 / 2 : ℝ)) := by
    funext u
    ring
  rw [e, integral_sub (hq.const_mul 2) hη, integral_const_mul]
  simp [Matrix.diagonal]
  ring

/-! ### B0232 (core): the real angular-two modes as `(q ± iη)^{-2}` -/

/-- **B0232**, the complex-variable identification of the two real angular-two modes
(`paper/main.tex` lines 3978–3987): at `q + iη = re^{iθ}`, `r > 0`,
`(α cos2θ + β sin2θ)/r² = ½(α + iβ)(q + iη)^{-2} + ½(α - iβ)(q - iη)^{-2}`. -/
theorem angularTwo_farField (α β : ℂ) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    (α * (Real.cos (2 * θ) : ℂ) + β * (Real.sin (2 * θ) : ℂ)) / (r : ℂ) ^ 2 =
      (α + Complex.I * β) / 2 * ((circleMap 0 r θ) ^ 2)⁻¹ +
        (α - Complex.I * β) / 2 * ((conj (circleMap 0 r θ)) ^ 2)⁻¹ := by
  set X := Complex.exp ((θ : ℂ) * Complex.I) with hX
  have hX0 : X ≠ 0 := Complex.exp_ne_zero _
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hconj : conj X = X⁻¹ := by
    rw [hX, ← Complex.exp_conj, ← Complex.exp_neg]
    congr 1
    simp [Complex.conj_ofReal]
  have hc : ((Real.cos (2 * θ) : ℝ) : ℂ) = (X ^ 2 + X⁻¹ ^ 2) / 2 := by
    rw [Complex.ofReal_cos, Complex.cos, hX, ← Complex.exp_nat_mul, ← Complex.exp_neg,
      ← Complex.exp_nat_mul]
    push_cast
    congr 2 <;> ring_nf
  have hs : ((Real.sin (2 * θ) : ℝ) : ℂ) = (X⁻¹ ^ 2 - X ^ 2) * Complex.I / 2 := by
    have e1 : X ^ 2 = Complex.exp (2 * θ * Complex.I) := by
      rw [hX, ← Complex.exp_nat_mul]
      push_cast
      ring_nf
    have e2 : X⁻¹ ^ 2 = Complex.exp (-(2 * θ * Complex.I)) := by
      rw [hX, ← Complex.exp_neg, ← Complex.exp_nat_mul]
      push_cast
      ring_nf
    rw [e1, e2, Complex.ofReal_sin, Complex.sin]
    push_cast
    ring_nf
  rw [hc, hs, circleMap_zero, map_mul, Complex.conj_ofReal, ← hX, hconj]
  field_simp
  ring_nf

end UnforcedLeray.Planar
