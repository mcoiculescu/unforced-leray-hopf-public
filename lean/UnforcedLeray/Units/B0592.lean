import UnforcedLeray.Units.B0579
import UnforcedLeray.Units.B0592.Kernel
import UnforcedLeray.Units.B0592.Schur
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# B0592 `prepared:p4.4a`: local Biot–Savart bound independent of `c` and `ν`

Blueprint unit **B0592**, label `prepared:p4.4a`, `paper/main.tex` lines 9594–9608
(Section P4 of the prepared train; dependency B0579 `prepared:p1.1`).

**Statement (tex 9594–9608).** "The cylinder Biot–Savart kernel is locally bounded by `C/|x|`,
with uniformly bounded local `L¹` norm, and uniformly bounded away from the diagonal for `c ≥ 2`.
Young's inequality near the diagonal and `‖ω‖₁ ≤ C_m ‖ω‖_{X_m}`, `m > 1`, elsewhere give on the
fixed observation disk
`‖K_c ω‖_{L²(supp φ)} ≤ C_{Σ,φ} ‖ω‖_{X_m}`. The constant is independent of `c, ν`. Thus a
finite-band vorticity error `O_Σ(ν + c^{-2}/ν)` remains `o(1)` after observation. A diverging
unspecified `P_ν` is not multiplied into that Gram error."

**Lean conventions.**
* Coordinates, cell and weights are those of B0579 (`UnforcedLeray.B0579`): `Plane = ℝ × ℝ`,
  `x = (q, η)`, the centered cell `cell c = [-c/2, c/2) × ℝ` (unnormalized Lebesgue measure,
  `paper/main.tex:2110`), and `X c m = L²(cell, ⟨x⟩^{2m} dx)` (`paper/main.tex:9373`).
* `K_c` is the cylinder Biot–Savart operator `∇^⊥Δ^{-1}` on `C_c = (ℝ/cℤ) × ℝ`, realized by its
  periodic kernel (`bsKernel`, file `B0592/Kernel.lean`, infrastructure INF22): the kernel is
  `∇^⊥` of the periodic Green function `(2π)^{-1} log|sin(π(q + iη)/c)|`
  (`hasDerivAt_stream_fst/snd`) and is `c`-periodic in `q` (`bsKernel_sub_int`). For a field
  `ω` on the cell, `velocity c ω x = ∫_{cell c} K_c(x - y) ω(y) dy` (a `c`-periodic function of
  `x ∈ ℝ²`; velocities `(u₁, u₂)` are the complex numbers `u₁ + i u₂`, as in unit B0009).
  The convolution exists for every `ω ∈ X_m`, `m > 1` (all `x` outside a null set); where the
  Bochner integral would diverge Lean returns `0`, but every estimate below bounds the
  `ℝ≥0∞`-valued majorant `∫ |K_c(x-y)| |ω(y)| dy`, so no junk value enters a claim.
  No zero-circulation condition is needed for this local bound (it is needed only for the global
  `H¹` bound `prepared:p1.4`, unit B0582, tex 9406–9431), so none is assumed.
* "The fixed observation disk" / `supp φ` is any bounded set `S ⊆ ℝ²`
  (`velocity_local_bound`; `velocity_bound_tsupport` is the case `S = tsupport φ` of a compactly
  supported test). `C_{Σ,φ}` depends only on `m` and `S` (`∃ C, ∀ c ≥ 2, ∀ ω`): it is independent
  of `c`, and `ν` does not occur in `K_c` or `X_m` at all.
* The norm is `eLpNorm _ 2 (volume.restrict S)` in `ℝ≥0∞`, bounded by `ENNReal.ofReal (C‖ω‖)`
  (so finiteness is part of the claim, and `MemLp` is stated as well).
* "`O_Σ(ν + c^{-2}/ν)` remains `o(1)` after observation": with the train coupling `c = ν^{-ρ}`,
  `ρ > 1/2` (`paper/main.tex:2104–2106`), `observed_error_tendsto_zero` shows that every
  family `ω_ν ∈ X_{c(ν)}` with `‖ω_ν‖_{X_m} ≤ A(ν + c^{-2}/ν)` has observed norm
  `‖K_c ω_ν‖_{L²(S)} → 0` as `ν → 0⁺`; the constant multiplying the error is the `c, ν`-free
  `C`, not a diverging `P_ν`. `tendsto_eLpNorm_velocity` is the general filter form.

**Proof (tex 9594–9598).** For `x` in a box `|x| ≤ R` and `y` in the cell, periodicity reduces
`x - y` to the centered strip, where `|K_c(z)| ≤ 1/(2c) + 1/(4|z|)` (`B0592/Kernel.lean`). For
`c ≥ 2` this gives `|K_c(x - y)| ≤ 1/2 + (1/4) Σ_{|j| ≤ N} g(x - y - (jc, 0))` with
`g = 1_{|z|<1}|z|^{-1} ∈ L¹(ℝ²)` and `N = ⌈R/2⌉ + 1` independent of `c`
(`norm_bsKernel_le_sum`). The bounded part is controlled by
`‖ω‖_{L¹(cell)} ≤ C_m ‖ω‖_{X_m}`, `C_m² = ∫_{ℝ²} ⟨y⟩^{-2m}` (`lintegral_cell_le`, `m > 1`);
the near part by the Schur form of Young's inequality (`schur_test`, `B0592/Schur.lean`), whose
row and column integrals are at most `(2N+1)‖g‖₁` by translation invariance
(`lintegral_schurKernel_row/col`). Minkowski's inequality assembles the two parts
(`eLpNorm_velocity_closedBall_le`).

**Main declarations.** `velocity`, `bsKernel_bounds`, `lintegral_bsKernel_ball_le`,
`lintegral_cell_le`,
`eLpNorm_velocity_closedBall_le`, `velocity_local_bound`, `velocity_bound_tsupport`,
`tendsto_eLpNorm_velocity`, `observed_error_tendsto_zero`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal Real

namespace UnforcedLeray.B0592

open UnforcedLeray.B0579 (Plane cell jb jb_pos X continuous_jb_rpow measurableSet_cell
  eLpNorm_cellMeasure)

/-! ### The kernel facts of tex 9594–9596 -/

/-- **Kernel bounds** (`paper/main.tex:9594–9596`), for `c ≥ 2` on the centered strip
`|q| ≤ c/2` (every point of the cylinder has such a representative, `bsKernel_sub_int`):
`|K_c(x)| ≤ 1/4 + 1/(4|x|)` ("locally bounded by `C/|x|`") and `|K_c(x)| ≤ 1/2` for `|x| ≥ 1`
("uniformly bounded away from the diagonal"); the local majorant `1_{|x|<1}|x|^{-1}` is
integrable (`integrable_nearKernel`, "uniformly bounded local `L¹` norm"). -/
theorem bsKernel_bounds {c : ℝ} (hc : 2 ≤ c) {z : Plane} (hz : |z.1| ≤ c / 2) :
    ‖bsKernel c z‖ ≤ 1 / 4 + 1 / (4 * ‖z‖) ∧ (1 ≤ ‖z‖ → ‖bsKernel c z‖ ≤ 1 / 2) := by
  have hc0 : 0 < c := by linarith
  have h := norm_bsKernel_le_reduced hc0 hz
  have hc4 : 1 / (2 * c) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  refine ⟨by linarith, fun hz1 => ?_⟩
  have : 1 / (4 * ‖z‖) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  linarith

/-! ### The velocity -/

/-- **The cylinder Biot–Savart velocity** `K_c ω (x) = ∫_{cell} K_c(x - y) ω(y) dy`
(`paper/main.tex:9600`; `K_c = ∇^⊥Δ^{-1}` on `C_c`, realized by its periodic kernel). -/
def velocity (c : ℝ) (ω : Plane → ℝ) (x : Plane) : ℂ :=
  ∫ y in cell c, bsKernel c (x - y) * (ω y : ℂ)

theorem stronglyMeasurable_velocity (c : ℝ) {ω : Plane → ℝ} (hω : Measurable ω) :
    StronglyMeasurable (velocity c ω) := by
  have hf : Measurable (Function.uncurry fun x y : Plane => bsKernel c (x - y) * (ω y : ℂ)) :=
    ((measurable_bsKernel c).comp measurable_sub).mul
      (Complex.measurable_ofReal.comp (hω.comp measurable_snd))
  unfold velocity
  exact StronglyMeasurable.integral_prod_right hf.stronglyMeasurable

/-! ### `‖ω‖_{L¹(cell)} ≤ C_m ‖ω‖_{X_m}` for `m > 1` -/

theorem integrable_jb_rpow_neg {m : ℝ} (hm : 1 < m) :
    Integrable (fun y : Plane => jb y ^ (-m)) := by
  have := volume_isAddHaarMeasure
  have h := integrable_rpow_neg_one_add_norm_sq (E := Plane) (μ := volume) (r := 2 * m)
    (by norm_num; linarith)
  refine h.mono' (continuous_jb_rpow (-m)).aestronglyMeasurable ?_
  filter_upwards with y
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (jb_pos y).le _), show -(2 * m) / 2 = -m by ring]
  refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith)
  show 1 + ‖y‖ ^ 2 ≤ 1 + y.1 ^ 2 + y.2 ^ 2
  linarith [norm_sq_le y]

/-- `C_m = (∫_{ℝ²} ⟨y⟩^{-2m} dy)^{1/2}`, finite for `m > 1` and independent of `c`. -/
def weightConst (m : ℝ) : ℝ≥0∞ := (∫⁻ y : Plane, ENNReal.ofReal (jb y ^ (-m))) ^ (1 / 2 : ℝ)

theorem weightConst_lt_top {m : ℝ} (hm : 1 < m) : weightConst m < ∞ :=
  ENNReal.rpow_lt_top_of_nonneg (by norm_num) (integrable_jb_rpow_neg hm).lintegral_lt_top.ne

theorem eLpNorm_two_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} (f : α → ℝ) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  exact ennreal_rpow_half_sq _

/-- `‖ω‖²_{X_m} = ∫_{cell} |⟨y⟩^m ω(y)|² dy`. -/
theorem ofReal_norm_X_sq (c m : ℝ) (ω : X c m) :
    ENNReal.ofReal ‖ω‖ ^ 2 = ∫⁻ y in cell c, ‖jb y ^ (m / 2) * ω y‖ₑ ^ 2 := by
  have hW : ENNReal.ofReal ‖ω‖ =
      eLpNorm (fun y => jb y ^ (m / 2) * ω y) 2 (volume.restrict (cell c)) := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top ω), eLpNorm_cellMeasure]
  rw [hW, eLpNorm_two_sq]

/-- **`‖ω‖_{L¹(cell)} ≤ C_m ‖ω‖_{X_m}`** (`paper/main.tex:9597`), by Cauchy–Schwarz against
`⟨y⟩^{-m}`; `C_m` does not depend on `c`. -/
theorem lintegral_cell_le {m : ℝ} (c : ℝ) (ω : X c m) :
    ∫⁻ y in cell c, ‖ω y‖ₑ ≤ weightConst m * ENNReal.ofReal ‖ω‖ := by
  have hω : Measurable (ω : Plane → ℝ) := (Lp.stronglyMeasurable ω).measurable
  have hpt : ∀ y, ‖ω y‖ₑ =
      ENNReal.ofReal (jb y ^ (-m / 2)) * ‖jb y ^ (m / 2) * ω y‖ₑ := by
    intro y
    have h1 : 0 ≤ jb y ^ (m / 2) := Real.rpow_nonneg (jb_pos y).le _
    rw [enorm_mul, Real.enorm_eq_ofReal h1, ← mul_assoc,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (jb_pos y).le _), ← Real.rpow_add (jb_pos y),
      show -m / 2 + m / 2 = 0 by ring, Real.rpow_zero, ENNReal.ofReal_one, one_mul]
  have hF : Measurable fun y : Plane => ENNReal.ofReal (jb y ^ (-m / 2)) :=
    ENNReal.measurable_ofReal.comp (continuous_jb_rpow _).measurable
  have hG : Measurable fun y : Plane => ‖jb y ^ (m / 2) * ω y‖ₑ :=
    ((continuous_jb_rpow _).measurable.mul hω).enorm
  have hcs := lintegral_mul_sq_le (μ := volume.restrict (cell c)) hF.aemeasurable
    hG.aemeasurable
  have hF2 : ∫⁻ y in cell c, ENNReal.ofReal (jb y ^ (-m / 2)) ^ 2 ≤ weightConst m ^ 2 := by
    rw [weightConst, ennreal_rpow_half_sq]
    refine (setLIntegral_le_lintegral _ _).trans (le_of_eq (lintegral_congr fun y => ?_))
    rw [← ENNReal.ofReal_pow (Real.rpow_nonneg (jb_pos y).le _), ← Real.rpow_natCast,
      ← Real.rpow_mul (jb_pos y).le]
    congr 2
    push_cast
    ring
  rw [lintegral_congr hpt]
  apply ennreal_le_of_sq_le_sq
  calc (∫⁻ y in cell c, ENNReal.ofReal (jb y ^ (-m / 2)) * ‖jb y ^ (m / 2) * ω y‖ₑ) ^ 2
      ≤ (∫⁻ y in cell c, ENNReal.ofReal (jb y ^ (-m / 2)) ^ 2) *
          ∫⁻ y in cell c, ‖jb y ^ (m / 2) * ω y‖ₑ ^ 2 := hcs
    _ ≤ weightConst m ^ 2 * ENNReal.ofReal ‖ω‖ ^ 2 := by
        rw [← ofReal_norm_X_sq]
        exact mul_le_mul_left hF2 _
    _ = (weightConst m * ENNReal.ofReal ‖ω‖) ^ 2 := by ring

/-- `‖ω‖_{L²(cell)} ≤ ‖ω‖_{X_m}` for `m ≥ 0`. -/
theorem lintegral_cell_sq_le {m : ℝ} (hm : 0 ≤ m) (c : ℝ) (ω : X c m) :
    ∫⁻ y in cell c, ‖ω y‖ₑ ^ 2 ≤ ENNReal.ofReal ‖ω‖ ^ 2 := by
  rw [ofReal_norm_X_sq]
  refine lintegral_mono fun y => ?_
  have h1 : 1 ≤ ‖jb y ^ (m / 2)‖ₑ := by
    rw [Real.enorm_eq_ofReal (Real.rpow_nonneg (jb_pos y).le _)]
    refine ENNReal.one_le_ofReal.mpr (Real.one_le_rpow ?_ (by linarith))
    show (1 : ℝ) ≤ 1 + y.1 ^ 2 + y.2 ^ 2
    nlinarith [sq_nonneg y.1, sq_nonneg y.2]
  have h2 : ‖ω y‖ₑ ≤ ‖jb y ^ (m / 2) * ω y‖ₑ := by
    rw [enorm_mul]
    calc ‖ω y‖ₑ = 1 * ‖ω y‖ₑ := (one_mul _).symm
      _ ≤ ‖jb y ^ (m / 2)‖ₑ * ‖ω y‖ₑ := mul_le_mul_left h1 _
  exact pow_le_pow_left₀ zero_le h2 2

/-! ### The Schur kernel of the near-diagonal part -/

/-- `k(x, y) = Σ_{|j| ≤ N} g(x - y - (jc, 0))`, `g = 1_{|z|<1}|z|^{-1}`. -/
def schurKernel (c R : ℝ) (x y : Plane) : ℝ≥0∞ :=
  ENNReal.ofReal (∑ j ∈ shifts R, nearKernel (x - y - shiftVec c j))

theorem measurable_schurKernel (c R : ℝ) : Measurable (Function.uncurry (schurKernel c R)) := by
  have h : Measurable fun p : Plane × Plane =>
      ∑ j ∈ shifts R, nearKernel (p.1 - p.2 - shiftVec c j) :=
    Finset.measurable_sum _ fun j _ =>
      measurable_nearKernel.comp ((measurable_fst.sub measurable_snd).sub_const _)
  exact ENNReal.measurable_ofReal.comp h

/-- `‖g‖₁`, finite and independent of `c`. -/
def nearMass : ℝ≥0∞ := ∫⁻ w : Plane, ENNReal.ofReal (nearKernel w)

theorem lintegral_nearKernel_sub (a : Plane) :
    ∫⁻ w : Plane, ENNReal.ofReal (nearKernel (w - a)) = nearMass := by
  have := volume_isAddRightInvariant
  exact lintegral_sub_right_eq_self (fun w => ENNReal.ofReal (nearKernel w)) a

/-- **"Uniformly bounded local `L¹` norm"** of the kernel (`paper/main.tex:9595`): for every
`c ≥ 2`, `∫_{|z|<1} |K_c(z)| dz ≤ (1/2)|B₁| + (1/4)‖g‖₁`, a bound free of `c`
(`ballConst_lt_top`). -/
theorem lintegral_bsKernel_ball_le {c : ℝ} (hc : 2 ≤ c) :
    ∫⁻ z in Metric.ball (0 : Plane) 1, ‖bsKernel c z‖ₑ ≤
      ENNReal.ofReal (1 / 2) * volume (Metric.ball (0 : Plane) 1) +
        ENNReal.ofReal (1 / 4) * nearMass := by
  have hpt : ∀ z ∈ Metric.ball (0 : Plane) 1, ‖bsKernel c z‖ₑ ≤
      ENNReal.ofReal (1 / 2) + ENNReal.ofReal (1 / 4) * ENNReal.ofReal (nearKernel z) := by
    intro z hz
    have hz1 : |z.1| ≤ c / 2 := by
      have h1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
      have h2 : ‖z.1‖ ≤ ‖z‖ := norm_fst_le z
      rw [Real.norm_eq_abs] at h2
      linarith
    have h := norm_bsKernel_le_near hc hz1
    rw [← ofReal_norm, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (mul_nonneg (by norm_num) (nearKernel_nonneg z))]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  calc ∫⁻ z in Metric.ball (0 : Plane) 1, ‖bsKernel c z‖ₑ
      ≤ ∫⁻ z in Metric.ball (0 : Plane) 1,
          (ENNReal.ofReal (1 / 2) + ENNReal.ofReal (1 / 4) * ENNReal.ofReal (nearKernel z)) :=
        setLIntegral_mono' Metric.isOpen_ball.measurableSet hpt
    _ = ENNReal.ofReal (1 / 2) * volume (Metric.ball (0 : Plane) 1) +
          ENNReal.ofReal (1 / 4) *
            ∫⁻ z in Metric.ball (0 : Plane) 1, ENNReal.ofReal (nearKernel z) := by
        have hmn : Measurable fun z : Plane => ENNReal.ofReal (nearKernel z) :=
          ENNReal.measurable_ofReal.comp measurable_nearKernel
        rw [lintegral_add_left measurable_const, lintegral_const, Measure.restrict_apply_univ,
          lintegral_const_mul _ hmn]
    _ ≤ ENNReal.ofReal (1 / 2) * volume (Metric.ball (0 : Plane) 1) +
          ENNReal.ofReal (1 / 4) * nearMass :=
        add_le_add le_rfl (mul_le_mul_right (setLIntegral_le_lintegral _ _) _)

theorem ballConst_lt_top :
    ENNReal.ofReal (1 / 2) * volume (Metric.ball (0 : Plane) 1) +
      ENNReal.ofReal (1 / 4) * nearMass < ∞ := by
  have := volume_isAddHaarMeasure
  have h1 : volume (Metric.ball (0 : Plane) 1) < ∞ := measure_ball_lt_top
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top h1,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top lintegral_nearKernel_lt_top⟩

theorem lintegral_schurKernel_row (c R : ℝ) (x : Plane) :
    ∫⁻ y in cell c, schurKernel c R x y ≤ (shifts R).card * nearMass := by
  have hmeas : ∀ j ∈ shifts R,
      Measurable fun y : Plane => ENNReal.ofReal (nearKernel (x - y - shiftVec c j)) :=
    fun j _ => ENNReal.measurable_ofReal.comp
      (measurable_nearKernel.comp ((measurable_const.sub measurable_id).sub_const _))
  calc ∫⁻ y in cell c, schurKernel c R x y ≤ ∫⁻ y, schurKernel c R x y :=
        setLIntegral_le_lintegral _ _
    _ = ∫⁻ y, ∑ j ∈ shifts R, ENNReal.ofReal (nearKernel (x - y - shiftVec c j)) :=
        lintegral_congr fun y => ENNReal.ofReal_sum_of_nonneg fun j _ => nearKernel_nonneg _
    _ = ∑ j ∈ shifts R, ∫⁻ y, ENNReal.ofReal (nearKernel (x - y - shiftVec c j)) :=
        lintegral_finsetSum _ hmeas
    _ = ∑ _j ∈ shifts R, nearMass := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← lintegral_nearKernel_sub (x - shiftVec c j)]
        refine lintegral_congr fun y => ?_
        rw [← nearKernel_neg]
        congr 2
        abel
    _ = (shifts R).card * nearMass := by rw [Finset.sum_const, nsmul_eq_mul]

theorem lintegral_schurKernel_col (c R : ℝ) (y : Plane) :
    ∫⁻ x in Metric.closedBall (0 : Plane) R, schurKernel c R x y ≤
      (shifts R).card * nearMass := by
  have hmeas : ∀ j ∈ shifts R,
      Measurable fun x : Plane => ENNReal.ofReal (nearKernel (x - y - shiftVec c j)) :=
    fun j _ => ENNReal.measurable_ofReal.comp
      (measurable_nearKernel.comp ((measurable_id.sub measurable_const).sub_const _))
  calc ∫⁻ x in Metric.closedBall (0 : Plane) R, schurKernel c R x y ≤
        ∫⁻ x, schurKernel c R x y := setLIntegral_le_lintegral _ _
    _ = ∫⁻ x, ∑ j ∈ shifts R, ENNReal.ofReal (nearKernel (x - y - shiftVec c j)) :=
        lintegral_congr fun x => ENNReal.ofReal_sum_of_nonneg fun j _ => nearKernel_nonneg _
    _ = ∑ j ∈ shifts R, ∫⁻ x, ENNReal.ofReal (nearKernel (x - y - shiftVec c j)) :=
        lintegral_finsetSum _ hmeas
    _ = ∑ _j ∈ shifts R, nearMass := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← lintegral_nearKernel_sub (y + shiftVec c j)]
        refine lintegral_congr fun x => ?_
        congr 2
        abel
    _ = (shifts R).card * nearMass := by rw [Finset.sum_const, nsmul_eq_mul]

/-- The near-diagonal majorant `T(x) = ∫_{cell} k(x, y) |ω(y)| dy`. -/
def schurOp (c R : ℝ) (ω : Plane → ℝ) (x : Plane) : ℝ≥0∞ :=
  ∫⁻ y in cell c, schurKernel c R x y * ‖ω y‖ₑ

theorem measurable_schurOp (c R : ℝ) {ω : Plane → ℝ} (hω : Measurable ω) :
    Measurable (schurOp c R ω) :=
  ((measurable_schurKernel c R).mul (hω.enorm.comp measurable_snd)).lintegral_prod_right'

/-! ### The estimate on a box -/

/-- The constant `C_{Σ,φ}` for the box `|x| ≤ R`:
`(1/2) C_m |B_R|^{1/2} + (1/4)(2N + 1)‖g‖₁`; it depends on `m` and `R` only. -/
def boxConst (m R : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / 2) * weightConst m * volume (Metric.closedBall (0 : Plane) R) ^ (1 / 2 : ℝ) +
    ENNReal.ofReal (1 / 4) * ((shifts R).card * nearMass)

theorem boxConst_lt_top {m : ℝ} (hm : 1 < m) (R : ℝ) : boxConst m R < ∞ := by
  have := volume_isAddHaarMeasure
  have h2 : volume (Metric.closedBall (0 : Plane) R) < ∞ := measure_closedBall_lt_top
  have h2' := ENNReal.rpow_lt_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) h2.ne
  have h3 : nearMass < ∞ := lintegral_nearKernel_lt_top
  unfold boxConst
  exact ENNReal.add_lt_top.mpr
    ⟨ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (weightConst_lt_top hm)) h2',
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) h3)⟩

/-- **The local Biot–Savart bound on a box** (`paper/main.tex:9594–9604`): for `c ≥ 2`, `m > 1`
and `ω ∈ X_m`, `‖K_c ω‖_{L²(|x| ≤ R)} ≤ boxConst m R · ‖ω‖_{X_m}`. -/
theorem eLpNorm_velocity_closedBall_le {m : ℝ} (hm : 1 < m) (R : ℝ) {c : ℝ} (hc : 2 ≤ c)
    (ω : X c m) :
    eLpNorm (velocity c ω) 2 (volume.restrict (Metric.closedBall (0 : Plane) R)) ≤
      boxConst m R * ENNReal.ofReal ‖ω‖ := by
  have hω : Measurable (ω : Plane → ℝ) := (Lp.stronglyMeasurable ω).measurable
  have hωe : Measurable fun y => ‖(ω : Plane → ℝ) y‖ₑ := hω.enorm
  have hTm := measurable_schurOp c R hω
  -- pointwise: `|K_c ω (x)| ≤ (1/2) ‖ω‖₁ + (1/4) T(x)` on the box
  have hpt : ∀ x ∈ Metric.closedBall (0 : Plane) R,
      ‖velocity c ω x‖ₑ ≤ ENNReal.ofReal (1 / 2) * (∫⁻ y in cell c, ‖(ω : Plane → ℝ) y‖ₑ) +
        ENNReal.ofReal (1 / 4) * schurOp c R ω x := by
    intro x hx
    have hx1 : |x.1| ≤ R := by
      have h1 : ‖x‖ ≤ R := mem_closedBall_zero_iff.mp hx
      have h2 : ‖x.1‖ ≤ ‖x‖ := norm_fst_le x
      rw [Real.norm_eq_abs] at h2
      linarith
    have hK : ∀ y ∈ cell c, ‖bsKernel c (x - y)‖ₑ ≤
        ENNReal.ofReal (1 / 2) + ENNReal.ofReal (1 / 4) * schurKernel c R x y := by
      intro y hy
      have h := norm_bsKernel_le_sum hc hx1 hy
      have hS : 0 ≤ ∑ j ∈ shifts R, nearKernel (x - y - shiftVec c j) :=
        Finset.sum_nonneg fun j _ => nearKernel_nonneg _
      rw [← ofReal_norm, schurKernel, ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_add (by norm_num) (mul_nonneg (by norm_num) hS)]
      exact ENNReal.ofReal_le_ofReal h
    calc ‖velocity c ω x‖ₑ
        ≤ ∫⁻ y in cell c, ‖bsKernel c (x - y) * ((ω : Plane → ℝ) y : ℂ)‖ₑ :=
          enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ y in cell c, ‖bsKernel c (x - y)‖ₑ * ‖(ω : Plane → ℝ) y‖ₑ := by
          refine lintegral_congr fun y => ?_
          rw [enorm_mul, ← ofReal_norm (((ω : Plane → ℝ) y : ℂ)), Complex.norm_real, ofReal_norm]
      _ ≤ ∫⁻ y in cell c, (ENNReal.ofReal (1 / 2) + ENNReal.ofReal (1 / 4) *
            schurKernel c R x y) * ‖(ω : Plane → ℝ) y‖ₑ :=
          setLIntegral_mono' (measurableSet_cell c) fun y hy => mul_le_mul_left (hK y hy) _
      _ = ENNReal.ofReal (1 / 2) * (∫⁻ y in cell c, ‖(ω : Plane → ℝ) y‖ₑ) +
            ENNReal.ofReal (1 / 4) * schurOp c R ω x := by
          have hm2 : Measurable fun y => schurKernel c R x y * ‖(ω : Plane → ℝ) y‖ₑ :=
            ((measurable_schurKernel c R).of_uncurry_left).mul hωe
          simp only [add_mul, mul_assoc]
          rw [lintegral_add_left (hωe.const_mul _), lintegral_const_mul _ hωe,
            lintegral_const_mul _ hm2]
          rfl
  -- Minkowski
  have hsplit : eLpNorm (velocity c ω) 2 (volume.restrict (Metric.closedBall (0 : Plane) R)) ≤
      (∫⁻ _x in Metric.closedBall (0 : Plane) R,
          (ENNReal.ofReal (1 / 2) * ∫⁻ y in cell c, ‖(ω : Plane → ℝ) y‖ₑ) ^ (2 : ℝ)) ^
          (1 / 2 : ℝ) +
        (∫⁻ x in Metric.closedBall (0 : Plane) R,
          (ENNReal.ofReal (1 / 4) * schurOp c R ω x) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
      ENNReal.toReal_ofNat]
    refine le_trans ?_ (ENNReal.lintegral_Lp_add_le
      (μ := volume.restrict (Metric.closedBall (0 : Plane) R))
      (f := fun _ => ENNReal.ofReal (1 / 2) * ∫⁻ y in cell c, ‖(ω : Plane → ℝ) y‖ₑ)
      (g := fun x => ENNReal.ofReal (1 / 4) * schurOp c R ω x) aemeasurable_const
      (hTm.const_mul _).aemeasurable (by norm_num))
    refine ENNReal.rpow_le_rpow (lintegral_mono_ae ?_) (by norm_num)
    filter_upwards [ae_restrict_mem Metric.isClosed_closedBall.measurableSet] with x hx
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    simp only [Pi.add_apply]
    exact hpt x hx
  -- the bounded part
  have hconst : (∫⁻ _x in Metric.closedBall (0 : Plane) R,
      (ENNReal.ofReal (1 / 2) * ∫⁻ y in cell c, ‖(ω : Plane → ℝ) y‖ₑ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (1 / 2) * (∫⁻ y in cell c, ‖(ω : Plane → ℝ) y‖ₑ) *
        volume (Metric.closedBall (0 : Plane) R) ^ (1 / 2 : ℝ) := by
    rw [lintegral_const, Measure.restrict_apply_univ,
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.rpow_two, ennreal_sq_rpow_half]
  -- the near-diagonal part (Schur/Young)
  have hschur := schur_test (μ := volume.restrict (Metric.closedBall (0 : Plane) R))
    (ν := volume.restrict (cell c)) (measurable_schurKernel c R) hωe
    (lintegral_schurKernel_row c R) (lintegral_schurKernel_col c R)
  have hω2 := lintegral_cell_sq_le (by linarith : (0 : ℝ) ≤ m) c ω
  have hTpart : (∫⁻ x in Metric.closedBall (0 : Plane) R,
      (ENNReal.ofReal (1 / 4) * schurOp c R ω x) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (1 / 4) * (((shifts R).card * nearMass) * ENNReal.ofReal ‖ω‖) := by
    simp_rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2), ENNReal.rpow_two]
    rw [lintegral_const_mul _ (hTm.pow_const 2), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      ennreal_sq_rpow_half]
    refine mul_le_mul_right ?_ _
    apply ennreal_le_of_sq_le_sq
    rw [ennreal_rpow_half_sq]
    calc ∫⁻ x in Metric.closedBall (0 : Plane) R, schurOp c R ω x ^ 2
        ≤ ((shifts R).card * nearMass) * ((shifts R).card * nearMass) *
            ∫⁻ y in cell c, ‖(ω : Plane → ℝ) y‖ₑ ^ 2 := hschur
      _ ≤ ((shifts R).card * nearMass) * ((shifts R).card * nearMass) *
            ENNReal.ofReal ‖ω‖ ^ 2 := mul_le_mul_right hω2 _
      _ = (((shifts R).card * nearMass) * ENNReal.ofReal ‖ω‖) ^ 2 := by ring
  have hA := lintegral_cell_le c ω
  calc eLpNorm (velocity c ω) 2 (volume.restrict (Metric.closedBall (0 : Plane) R))
      ≤ _ := hsplit
    _ ≤ ENNReal.ofReal (1 / 2) * (weightConst m * ENNReal.ofReal ‖ω‖) *
          volume (Metric.closedBall (0 : Plane) R) ^ (1 / 2 : ℝ) +
        ENNReal.ofReal (1 / 4) * (((shifts R).card * nearMass) * ENNReal.ofReal ‖ω‖) := by
        rw [hconst]
        exact add_le_add (mul_le_mul_left (mul_le_mul_right hA _) _) hTpart
    _ = boxConst m R * ENNReal.ofReal ‖ω‖ := by
        unfold boxConst
        ring

/-! ### The claim of `prepared:p4.4a` -/

/-- **`prepared:p4.4a`** (`paper/main.tex:9594–9604`): for `m > 1` and a fixed bounded
observation set `S`, there is `C = C_{Σ,φ}` such that for every `c ≥ 2` and every `ω ∈ X_m` on the
`c`-cell, `K_c ω ∈ L²(S)` and `‖K_c ω‖_{L²(S)} ≤ C ‖ω‖_{X_m}`. The constant is chosen before `c`
and `ω` (independent of `c`; `ν` does not enter). -/
theorem velocity_local_bound {m : ℝ} (hm : 1 < m) {S : Set Plane}
    (hS : Bornology.IsBounded S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 2 ≤ c → ∀ ω : X c m,
      MemLp (velocity c ω) 2 (volume.restrict S) ∧
        eLpNorm (velocity c ω) 2 (volume.restrict S) ≤ ENNReal.ofReal (C * ‖ω‖) := by
  obtain ⟨R, hR⟩ := hS.subset_closedBall (0 : Plane)
  refine ⟨(boxConst m R).toReal, ENNReal.toReal_nonneg, fun c hc ω => ?_⟩
  have hle : eLpNorm (velocity c ω) 2 (volume.restrict S) ≤
      ENNReal.ofReal ((boxConst m R).toReal * ‖ω‖) := by
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (boxConst_lt_top hm R).ne]
    exact (eLpNorm_mono_measure _ (Measure.restrict_mono hR le_rfl)).trans
      (eLpNorm_velocity_closedBall_le hm R hc ω)
  exact ⟨⟨(stronglyMeasurable_velocity c (Lp.stronglyMeasurable ω).measurable).aestronglyMeasurable,
    hle.trans_lt ENNReal.ofReal_lt_top⟩, hle⟩

/-- `prepared:p4.4a` on `supp φ` for a compactly supported observation test `φ`
(`paper/main.tex:9600`). -/
theorem velocity_bound_tsupport {m : ℝ} (hm : 1 < m) {φ : Plane → ℝ}
    (hφ : HasCompactSupport φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 2 ≤ c → ∀ ω : X c m,
      MemLp (velocity c ω) 2 (volume.restrict (tsupport φ)) ∧
        eLpNorm (velocity c ω) 2 (volume.restrict (tsupport φ)) ≤ ENNReal.ofReal (C * ‖ω‖) :=
  velocity_local_bound hm hφ.isCompact.isBounded

/-- Since the constant does not depend on `c`: along any filter, vorticity errors with
`‖ω_i‖_{X_m} → 0` (on cells `c_i ≥ 2`) have observed norm `‖K_{c_i} ω_i‖_{L²(S)} → 0`. -/
theorem tendsto_eLpNorm_velocity {m : ℝ} (hm : 1 < m) {S : Set Plane}
    (hS : Bornology.IsBounded S) {ι : Type*} {l : Filter ι} {c : ι → ℝ}
    (hc : ∀ᶠ i in l, 2 ≤ c i) (ω : ∀ i, X (c i) m) (hω : Tendsto (fun i => ‖ω i‖) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm (velocity (c i) (ω i)) 2 (volume.restrict S)) l (𝓝 0) := by
  obtain ⟨C, -, hbound⟩ := velocity_local_bound hm hS
  have hup : Tendsto (fun i => ENNReal.ofReal (C * ‖ω i‖)) l (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (hω.const_mul C)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun i => zero_le) ?_
  filter_upwards [hc] with i hi
  exact (hbound (c i) hi (ω i)).2

theorem rpow_neg_rpow_neg_two_div {ν ρ : ℝ} (hν : 0 < ν) :
    (ν ^ (-ρ)) ^ (-2 : ℝ) / ν = ν ^ (2 * ρ - 1) := by
  rw [← Real.rpow_mul hν.le, Real.rpow_sub_one hν.ne']
  congr 2
  ring

/-- **"A finite-band vorticity error `O_Σ(ν + c^{-2}/ν)` remains `o(1)` after observation"**
(`paper/main.tex:9604–9606`), with the train coupling `c = ν^{-ρ}`, `ρ > 1/2`
(`paper/main.tex:2104–2106`): if `‖ω_ν‖_{X_m} ≤ A(ν + c^{-2}/ν)` for `0 < ν ≤ 1`, then
`‖K_c ω_ν‖_{L²(S)} → 0` as `ν → 0⁺`. The bound uses only the `c, ν`-free constant of
`velocity_local_bound`, no diverging `P_ν`. -/
theorem observed_error_tendsto_zero {m ρ A : ℝ} (hm : 1 < m) (hρ : 1 / 2 < ρ) {S : Set Plane}
    (hS : Bornology.IsBounded S) (ω : ∀ ν : ℝ, X (ν ^ (-ρ)) m)
    (hω : ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ‖ω ν‖ ≤ A * (ν + (ν ^ (-ρ)) ^ (-2 : ℝ) / ν)) :
    Tendsto (fun ν => eLpNorm (velocity (ν ^ (-ρ)) (ω ν)) 2 (volume.restrict S))
      (𝓝[>] 0) (𝓝 0) := by
  have hc : ∀ᶠ ν in 𝓝[>] (0 : ℝ), 2 ≤ ν ^ (-ρ) :=
    (tendsto_rpow_neg_nhdsGT_zero (by linarith : -ρ < 0)).eventually_ge_atTop 2
  have h1 : Tendsto (fun ν : ℝ => ν ^ (2 * ρ - 1)) (𝓝[>] 0) (𝓝 0) := by
    have hcont : ContinuousAt (fun ν : ℝ => ν ^ (2 * ρ - 1)) 0 :=
      Real.continuousAt_rpow_const 0 _ (Or.inr (by linarith))
    have := hcont.tendsto
    rw [Real.zero_rpow (by linarith : (0 : ℝ) < 2 * ρ - 1).ne'] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  have hup : Tendsto (fun ν : ℝ => A * (ν + ν ^ (2 * ρ - 1))) (𝓝[>] 0) (𝓝 0) := by
    have := ((tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).add h1).const_mul A
    simpa using this
  have hωt : Tendsto (fun ν => ‖ω ν‖) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
      (Eventually.of_forall fun ν => norm_nonneg _) ?_
    filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with ν hν
    have := hω ν hν.1 hν.2
    rwa [rpow_neg_rpow_neg_two_div hν.1] at this
  exact tendsto_eLpNorm_velocity hm hS (c := fun ν => ν ^ (-ρ)) hc ω hωt

end UnforcedLeray.B0592
