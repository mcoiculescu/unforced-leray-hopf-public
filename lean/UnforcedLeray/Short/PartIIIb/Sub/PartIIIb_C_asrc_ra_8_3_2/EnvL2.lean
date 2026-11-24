import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8_3_2
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# `PartIII-b:C/asrc/ra/8/3/2/2` : the cell `L²` bound of the Gaussian lattice envelope (`GEnvL2`)

Source: `the November 2 reference manuscript` 4963-4977.

Proof, with `c = cOf ν = ν⁻²` (so `c ≥ 1` for `0 < ν ≤ 1`) and the cell `|q| ≤ c/2`:

* `(1+t)^4 e^{-t²/9} ≤ 5200 e^{-t²/18}` for `t ≥ 0`;
* the norm on `ℝ × ℝ` is the sup norm, so `t² ≥ (a² + η²)/2` for `t = ‖(a,η)‖`;
* `(q - jc)² ≥ j²/4` on the cell (`c ≥ 1`), hence every summand of `gEnv` is at most
  `5200 e^{-η²/36} e^{-(q-jc)²/36} ≤ 5200 e^{-η²/36} e^{-j²/144}`, uniformly in `q`;
* so `gEnv ν x ≤ M e^{-η²/36}` on the cell, with `M = 5200 Σ_j e^{-j²/144} < ∞`;
* integrating over the cell (length `c`) against `c⁻¹ dq dη` gives a bound independent of `ν`,
  with `k = 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Elementary: `(1+t)^4 e^{-t²/9} ≤ 5200 e^{-t²/18}` for `t ≥ 0`. -/
theorem gEnv_summand_le {t : ℝ} (ht : 0 ≤ t) :
    (1 + t) ^ 4 * Real.exp (-(t ^ 2) / 9) ≤ 5200 * Real.exp (-(t ^ 2) / 18) := by
  have hy : 0 ≤ t ^ 2 / 18 := by positivity
  have hq := Real.quadratic_le_exp_of_nonneg hy
  have h1 : 1 ≤ Real.exp (t ^ 2 / 18) := Real.one_le_exp hy
  have e1 : t ^ 4 = 648 * ((t ^ 2 / 18) ^ 2 / 2) := by ring
  have ht4 : t ^ 4 ≤ 648 * Real.exp (t ^ 2 / 18) := by
    rw [e1]; nlinarith [hq, hy]
  have hpoly : (1 + t) ^ 4 ≤ 8 * (1 + t ^ 4) := by
    nlinarith [mul_nonneg (sq_nonneg (t - 1)) (by positivity : (0:ℝ) ≤ 7 * t ^ 2 + 10 * t + 7)]
  have hE : (1 + t) ^ 4 ≤ 5200 * Real.exp (t ^ 2 / 18) := by
    nlinarith [hpoly, ht4, h1]
  have key : Real.exp (t ^ 2 / 18) * Real.exp (-(t ^ 2) / 9) = Real.exp (-(t ^ 2) / 18) := by
    rw [← Real.exp_add]; congr 1; ring
  calc (1 + t) ^ 4 * Real.exp (-(t ^ 2) / 9)
      ≤ 5200 * Real.exp (t ^ 2 / 18) * Real.exp (-(t ^ 2) / 9) :=
        mul_le_mul_of_nonneg_right hE (Real.exp_pos _).le
    _ = 5200 * Real.exp (-(t ^ 2) / 18) := by rw [mul_assoc, key]

/-- The sup norm on `ℝ × ℝ` dominates both coordinates: `y.1² + y.2² ≤ 2‖y‖²`. -/
theorem sq_add_sq_le_two_norm_sq (y : ℝ × ℝ) : y.1 ^ 2 + y.2 ^ 2 ≤ 2 * ‖y‖ ^ 2 := by
  have h1 := norm_fst_le y
  have h2 := norm_snd_le y
  have a1 : y.1 ^ 2 ≤ ‖y‖ ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) h1 2
    rwa [Real.norm_eq_abs, sq_abs] at this
  have a2 : y.2 ^ 2 ≤ ‖y‖ ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) h2 2
    rwa [Real.norm_eq_abs, sq_abs] at this
  linarith

/-- The lattice sum `Σ_j e^{-j²/144}` (summable over `ℤ`). -/
def gaussLatticeSum : ℝ := ∑' j : ℤ, Real.exp (-((j : ℝ) ^ 2) / 144)

theorem summable_gaussLattice : Summable (fun j : ℤ => Real.exp (-((j : ℝ) ^ 2) / 144)) := by
  have hsum4 : Summable (fun j : ℤ => 1 / (j : ℝ) ^ 4) :=
    (Real.summable_one_div_int_pow (p := 4)).2 (by norm_num)
  refine Summable.of_norm_bounded_eventually
    (g := fun j : ℤ => (2 * 144 ^ 2 : ℝ) * (1 / (j : ℝ) ^ 4)) (hsum4.mul_left _) ?_
  filter_upwards [Filter.eventually_cofinite_ne 0] with j hj
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast hj
  have hj4 : 0 < (j : ℝ) ^ 4 := by positivity
  have hu : 0 ≤ (j : ℝ) ^ 2 / 144 := by positivity
  have hq := Real.quadratic_le_exp_of_nonneg hu
  have hexp_u : (j : ℝ) ^ 4 / (2 * 144 ^ 2) ≤ Real.exp ((j : ℝ) ^ 2 / 144) := by
    have e : (j : ℝ) ^ 4 / (2 * 144 ^ 2) = ((j : ℝ) ^ 2 / 144) ^ 2 / 2 := by ring
    rw [e]; nlinarith [hq, hu]
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  rw [show -((j : ℝ) ^ 2) / 144 = -((j : ℝ) ^ 2 / 144) by ring, Real.exp_neg]
  calc (Real.exp ((j : ℝ) ^ 2 / 144))⁻¹ ≤ ((j : ℝ) ^ 4 / (2 * 144 ^ 2))⁻¹ :=
        inv_anti₀ (div_pos hj4 (by norm_num)) hexp_u
    _ = (2 * 144 ^ 2 : ℝ) * (1 / (j : ℝ) ^ 4) := by rw [inv_div]; ring

/-- On the cell `|q| ≤ c/2` with `c ≥ 1`: `j²/4 ≤ (q - jc)²`. -/
theorem sq_sub_ge_of_cell {q c : ℝ} (hc1 : 1 ≤ c) (hq : |q| ≤ c / 2) (j : ℤ) :
    (j : ℝ) ^ 2 / 4 ≤ (q - j * c) ^ 2 := by
  rcases eq_or_ne j 0 with rfl | hj
  · norm_num <;> positivity
  · have hJ : (1 : ℝ) ≤ |(j : ℝ)| := by exact_mod_cast Int.one_le_abs hj
    have hc0 : 0 < c := by linarith
    have habs : |(j : ℝ) * c| = |(j : ℝ)| * c := by rw [abs_mul, abs_of_pos hc0]
    have h3 := abs_add_le q (-(q - j * c))
    rw [show q + -(q - j * c) = j * c by ring, abs_neg] at h3
    have h4 : |(j : ℝ)| / 2 ≤ |q - j * c| := by
      nlinarith [mul_nonneg (sub_nonneg.2 hc1) (by linarith : (0:ℝ) ≤ |(j : ℝ)| - 1 / 2),
        abs_nonneg q]
    have h5 : (|(j : ℝ)| / 2) ^ 2 ≤ |q - j * c| ^ 2 :=
      pow_le_pow_left₀ (by positivity) h4 2
    have h6 : (|(j : ℝ)| / 2) ^ 2 = (j : ℝ) ^ 2 / 4 := by
      rw [div_pow, sq_abs]; norm_num
    rw [sq_abs] at h5
    linarith

/-- Pointwise bound of the lattice envelope on the cell: `gEnv ν x ≤ 5200 Σ_j e^{-j²/144} e^{-η²/36}`. -/
theorem gEnv_le_on_cell {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (x : ℝ × ℝ)
    (hx : |x.1| ≤ cOf ν / 2) :
    gEnv ν x ≤ (5200 * gaussLatticeSum) * Real.exp (-(x.2 ^ 2) / 36) := by
  have hc1 : 1 ≤ cOf ν := by
    unfold cOf
    exact (one_le_inv₀ (pow_pos hν 2)).2 (pow_le_one₀ hν.le hν1)
  have hsep := sq_sub_ge_of_cell hc1 hx
  -- termwise bound
  have hterm : ∀ j : ℤ,
      (1 + ‖xj ν j x‖) ^ 4 * Real.exp (-(‖xj ν j x‖ ^ 2) / 9)
        ≤ 5200 * (Real.exp (-(x.2 ^ 2) / 36) * Real.exp (-((x.1 - j * cOf ν) ^ 2) / 36)) := by
    intro j
    have ht0 : 0 ≤ ‖xj ν j x‖ := norm_nonneg _
    have hcoord := sq_add_sq_le_two_norm_sq (xj ν j x)
    have hy1 : (xj ν j x).1 = x.1 - j * cOf ν := rfl
    have hy2 : (xj ν j x).2 = x.2 := rfl
    rw [hy1, hy2] at hcoord
    have hexp : Real.exp (-(‖xj ν j x‖ ^ 2) / 18)
        ≤ Real.exp (-((x.1 - j * cOf ν) ^ 2 + x.2 ^ 2) / 36) := by
      apply Real.exp_le_exp.2
      linarith
    have hsplit : Real.exp (-((x.1 - j * cOf ν) ^ 2 + x.2 ^ 2) / 36)
        = Real.exp (-((x.1 - j * cOf ν) ^ 2) / 36) * Real.exp (-(x.2 ^ 2) / 36) := by
      rw [← Real.exp_add]; congr 1; ring
    calc (1 + ‖xj ν j x‖) ^ 4 * Real.exp (-(‖xj ν j x‖ ^ 2) / 9)
        ≤ 5200 * Real.exp (-(‖xj ν j x‖ ^ 2) / 18) := gEnv_summand_le ht0
      _ ≤ 5200 * Real.exp (-((x.1 - j * cOf ν) ^ 2 + x.2 ^ 2) / 36) :=
          mul_le_mul_of_nonneg_left hexp (by norm_num)
      _ = 5200 * (Real.exp (-(x.2 ^ 2) / 36) * Real.exp (-((x.1 - j * cOf ν) ^ 2) / 36)) := by
          rw [hsplit]; ring
  -- comparison with the lattice sum
  have hw : ∀ j : ℤ, Real.exp (-((x.1 - j * cOf ν) ^ 2) / 36)
      ≤ Real.exp (-((j : ℝ) ^ 2) / 144) := by
    intro j
    apply Real.exp_le_exp.2
    linarith [hsep j]
  have hSw := summable_gaussLattice
  have hSg : Summable (fun j : ℤ => Real.exp (-((x.1 - j * cOf ν) ^ 2) / 36)) :=
    Summable.of_nonneg_of_le (fun j => (Real.exp_pos _).le) hw hSw
  have hB : Summable (fun j : ℤ =>
      5200 * (Real.exp (-(x.2 ^ 2) / 36) * Real.exp (-((x.1 - j * cOf ν) ^ 2) / 36))) :=
    ((hSg.mul_left _).mul_left _)
  have hU : Summable (fun j : ℤ =>
      (1 + ‖xj ν j x‖) ^ 4 * Real.exp (-(‖xj ν j x‖ ^ 2) / 9)) := by
    refine Summable.of_nonneg_of_le (fun j => ?_) hterm hB
    have := norm_nonneg (xj ν j x)
    positivity
  unfold gEnv
  calc ∑' j : ℤ, (1 + ‖xj ν j x‖) ^ 4 * Real.exp (-(‖xj ν j x‖ ^ 2) / 9)
      ≤ ∑' j : ℤ, 5200 * (Real.exp (-(x.2 ^ 2) / 36) * Real.exp (-((x.1 - j * cOf ν) ^ 2) / 36)) :=
        hU.tsum_le_tsum hterm hB
    _ = 5200 * (Real.exp (-(x.2 ^ 2) / 36) * ∑' j : ℤ, Real.exp (-((x.1 - j * cOf ν) ^ 2) / 36)) := by
        rw [tsum_mul_left, tsum_mul_left]
    _ ≤ 5200 * (Real.exp (-(x.2 ^ 2) / 36) * gaussLatticeSum) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        exact hSg.tsum_le_tsum hw hSw
    _ = (5200 * gaussLatticeSum) * Real.exp (-(x.2 ^ 2) / 36) := by ring

/-- The cell integral of a function of the second coordinate: `∫_{[a,b)×ℝ} G(η) = (b-a) ∫ G`. -/
theorem lintegral_cell_snd (a b : ℝ) (G : ℝ → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ x in Ico a b ×ˢ (univ : Set ℝ), G x.2 = volume (Ico a b) * ∫⁻ y, G y := by
  have hsplit : (volume.restrict (Ico a b ×ˢ (univ : Set ℝ)) : Measure (ℝ × ℝ))
      = (volume.restrict (Ico a b)).prod (volume.restrict (univ : Set ℝ)) := by
    rw [Measure.prod_restrict, Measure.volume_eq_prod ℝ ℝ]
  rw [hsplit]
  have h := lintegral_prod_mul (μ := volume.restrict (Ico a b))
    (ν := volume.restrict (univ : Set ℝ)) (f := fun _ => (1 : ℝ≥0∞)) (g := G)
    aemeasurable_const hG.aemeasurable
  simp only [one_mul] at h
  rw [h, lintegral_one, Measure.restrict_apply_univ, Measure.restrict_univ]

/-- **Leaf (iii): cell `L²` bound of the envelope** (source 4963-4977), with `k = 0`. -/
theorem gEnvL2 : UnforcedLeray.Short.PartIIIb.Concrete.GEnvL2 := by
  set J : ℝ := ∫ y : ℝ, Real.exp (-(1 / 18) * y ^ 2) with hJdef
  have hJi : Integrable (fun y : ℝ => Real.exp (-(1 / 18) * y ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num)
  have hJnn : 0 ≤ J := integral_nonneg (fun y => (Real.exp_pos _).le)
  have hJl : ENNReal.ofReal J = ∫⁻ y, ENNReal.ofReal (Real.exp (-(1 / 18) * y ^ 2)) :=
    ofReal_integral_eq_lintegral_ofReal hJi (ae_of_all _ fun y => (Real.exp_pos _).le)
  refine ⟨(5200 * gaussLatticeSum) * Real.sqrt J, 0, ?_⟩
  intro ν hν hν1
  set M : ℝ := 5200 * gaussLatticeSum with hMdef
  have hc0 : 0 < cOf ν := inv_pos.2 (pow_pos hν 2)
  have hc1 : 1 ≤ cOf ν := by
    unfold cOf
    exact (one_le_inv₀ (pow_pos hν 2)).2 (pow_le_one₀ hν.le hν1)
  -- pointwise bound on the cell
  have hpt : ∀ x ∈ Ico (-cOf ν / 2) (cOf ν / 2) ×ˢ (univ : Set ℝ),
      ENNReal.ofReal (gEnv ν x ^ 2)
        ≤ ENNReal.ofReal (M ^ 2) * ENNReal.ofReal (Real.exp (-(1 / 18) * x.2 ^ 2)) := by
    intro x hx
    obtain ⟨⟨h1, h2⟩, _⟩ := hx
    have habs : |x.1| ≤ cOf ν / 2 := abs_le.2 ⟨by linarith, by linarith⟩
    have hb := gEnv_le_on_cell hν hν1 x habs
    have e : Real.exp (-(x.2 ^ 2) / 36) ^ 2 = Real.exp (-(1 / 18) * x.2 ^ 2) := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    have hsq : gEnv ν x ^ 2 ≤ M ^ 2 * Real.exp (-(1 / 18) * x.2 ^ 2) := by
      calc gEnv ν x ^ 2 ≤ (M * Real.exp (-(x.2 ^ 2) / 36)) ^ 2 :=
            pow_le_pow_left₀ (gEnv_nonneg _ _) hb 2
        _ = M ^ 2 * Real.exp (-(x.2 ^ 2) / 36) ^ 2 := by ring
        _ = M ^ 2 * Real.exp (-(1 / 18) * x.2 ^ 2) := by rw [e]
    rw [← ENNReal.ofReal_mul (sq_nonneg M)]
    exact ENNReal.ofReal_le_ofReal hsq
  -- the cell integral
  have hcell : ∫⁻ x, ENNReal.ofReal (gEnv ν x ^ 2) ∂(UnforcedLeray.Cyl.avgμ (cOf ν))
      = ENNReal.ofReal (cOf ν)⁻¹ * ∫⁻ x in Ico (-cOf ν / 2) (cOf ν / 2) ×ˢ (univ : Set ℝ),
          ENNReal.ofReal (gEnv ν x ^ 2) := by
    unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ UnforcedLeray.Cyl.cell
    rw [lintegral_smul_measure, smul_eq_mul]
  have hmono : ∫⁻ x in Ico (-cOf ν / 2) (cOf ν / 2) ×ˢ (univ : Set ℝ),
      ENNReal.ofReal (gEnv ν x ^ 2)
        ≤ ∫⁻ x in Ico (-cOf ν / 2) (cOf ν / 2) ×ˢ (univ : Set ℝ),
          ENNReal.ofReal (M ^ 2) * ENNReal.ofReal (Real.exp (-(1 / 18) * x.2 ^ 2)) :=
    setLIntegral_mono' (measurableSet_Ico.prod MeasurableSet.univ) hpt
  have hG : Measurable (fun y : ℝ => ENNReal.ofReal (Real.exp (-(1 / 18) * y ^ 2))) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  have hval : ∫⁻ x in Ico (-cOf ν / 2) (cOf ν / 2) ×ˢ (univ : Set ℝ),
      ENNReal.ofReal (M ^ 2) * ENNReal.ofReal (Real.exp (-(1 / 18) * x.2 ^ 2))
        = ENNReal.ofReal (M ^ 2) * (volume (Ico (-cOf ν / 2) (cOf ν / 2)) * ENNReal.ofReal J) := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_cell_snd _ _ (fun y => ENNReal.ofReal (Real.exp (-(1 / 18) * y ^ 2))) hG, ← hJl]
  have hvol : volume (Ico (-cOf ν / 2) (cOf ν / 2)) = ENNReal.ofReal (cOf ν) := by
    rw [Real.volume_Ico]; congr 1; ring
  rw [show (ν ^ 2)⁻¹ = cOf ν from rfl, hcell]
  simp only [pow_zero, mul_one]
  calc ENNReal.ofReal (cOf ν)⁻¹ * ∫⁻ x in Ico (-cOf ν / 2) (cOf ν / 2) ×ˢ (univ : Set ℝ),
          ENNReal.ofReal (gEnv ν x ^ 2)
      ≤ ENNReal.ofReal (cOf ν)⁻¹ * ∫⁻ x in Ico (-cOf ν / 2) (cOf ν / 2) ×ˢ (univ : Set ℝ),
          ENNReal.ofReal (M ^ 2) * ENNReal.ofReal (Real.exp (-(1 / 18) * x.2 ^ 2)) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = ENNReal.ofReal (cOf ν)⁻¹ * (ENNReal.ofReal (M ^ 2) * (ENNReal.ofReal (cOf ν) * ENNReal.ofReal J)) := by
        rw [hval, hvol]
    _ = ENNReal.ofReal (M ^ 2 * J) := by
        have hinv : ENNReal.ofReal (cOf ν)⁻¹ * ENNReal.ofReal (cOf ν) = 1 := by
          rw [← ENNReal.ofReal_mul (inv_nonneg.2 hc0.le), inv_mul_cancel₀ hc0.ne', ENNReal.ofReal_one]
        rw [ENNReal.ofReal_mul (sq_nonneg M)]
        calc ENNReal.ofReal (cOf ν)⁻¹ * (ENNReal.ofReal (M ^ 2) * (ENNReal.ofReal (cOf ν) * ENNReal.ofReal J))
            = ENNReal.ofReal (M ^ 2) * ENNReal.ofReal J *
                (ENNReal.ofReal (cOf ν)⁻¹ * ENNReal.ofReal (cOf ν)) := by ring
          _ = ENNReal.ofReal (M ^ 2) * ENNReal.ofReal J := by rw [hinv, mul_one]
    _ = ENNReal.ofReal ((M * Real.sqrt J) ^ 2) := by
        congr 1
        rw [mul_pow M (Real.sqrt J), Real.sq_sqrt hJnn]

end UnforcedLeray.Short.PartIIIb.Concrete
