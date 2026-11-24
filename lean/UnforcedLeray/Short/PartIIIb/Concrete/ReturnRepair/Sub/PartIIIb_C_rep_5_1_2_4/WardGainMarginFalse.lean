import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4.WardBin
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.EpsForm
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# `WardGainMarginG` is false; the two true gain margins of the source

Source `the November 2 reference manuscript` 5594-5599 (margins), 5303-5316 (the
far mask, its young-old rectangle and its complement), 4171-4199 (the Ward displacement and the
shifted-resolvent cutoff formula), 5688-5689 ("The decomposition of `S_far T + Y[T]` consists exactly
of the early-source and late-output regions and the two stream transitions"), 5936-5940 (`ε`).

## The finding

`WardGainMarginG` (`WardBin.lean`) asks `ε^{3/2} e^{γ/ν} ≤ C ν^{-k} e^{γ/(10ν)} g(s_{j+1})` for
**every** output bin `j`.  For bins of small output age (`s_{j+1} ≤ 1`, `g(s_{j+1}) ≤ e^γ`) this
is `ν^{3r/2+k} e^{2γ/(5ν)} ≤ C'`, false as `ν → 0` (`not_wardGainMarginG`).

The source has no further mechanism in 5585-5593 (the factor `l^{2μ+2}` of `sepW` is bounded, the
order-four kernel only gives the polynomial `ε^{3/2}(s^{1/2}+s^{3/4})`, sharp for a source with
nonzero mass at a fixed fractional radial gap).  The margins of 5594-5599 are used only for the
pieces of the **sum** `S_far T + Y[T]`:  on output ages `s ≤ 4/(5ν)` (`χ_y = 1`) the stream
transition is `Y = W_μ = -S_μ(χ_oT)` (4171-4199), and every pair (young output, source of age
`≥ 6/(5ν)`) lies in the far mask (5303-5306), so the young-old rectangle cancels exactly and
`S_far T + Y[T] = (1-χ_y)S_far T + χ_y S_far((1-χ_o)T) + (𝒞_y-χ_y)W_μ + [D_{μ+1},𝒞_y]X_0`
(5306-5316, 5688-5689).  The source never bounds `Y` (or `S_far`) alone in the gain norms; the
old-source/young-output part of either alone grows like `e^{γ/(6ν)}` already for sources at age
`2/ν`.

The two margins that the source does use are proved here:

* `lateGainMarginG` (late output, `ν u ≥ 2/3`, so `g(u) ≥ e^{2γ/(5ν)}`; the source threshold
  `4/5` gives `-γ/18`): `ε^{3/2} e^{γ/ν} ≤ C ν^{-k} e^{γ/(10ν)} g(u)`;
* `earlyGainMarginG` (early source, `ν t ≤ 3/2`, `g(t) ≤ e^{3γ/(5ν)}`):
  `ε^{3/2} g(t) ≤ C ν^{-k} e^{γ/(10ν)}`.

If `ν s_{j+1} < 2/3` then `ν s_j < (2/3)e^{δ/4} < 4/5`: such a bin lies in the plateau `χ_y = 1`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `ε^{3/2} = A^{3/2} ν^{(3/2)r} e^{-(γ/2)/ν}` with `A = (2|𝒞(σ₀)|)^{-1/3}`,
`r = (Re κ - 5 - 2σ₀)/3` (source 5936-5940). -/
theorem retEps_rpow32 {Pl : UnforcedLeray.Blueprint.Planar.PlanarData} {σ₀ : ℝ}
    (hC : Pl.signedCoeff σ₀ ≠ 0) (n : ℕ) :
    retEps Pl σ₀ n ^ (3 / 2 : ℝ) =
      ((2 * ‖Pl.signedCoeff σ₀‖) ^ (-(1 / 3 : ℝ))) ^ (3 / 2 : ℝ) *
        retNu Pl σ₀ n ^ ((Pl.kappa.re - 5 - 2 * σ₀) / 3 * (3 / 2)) *
          Real.exp (-(Pl.eigenvalue.re / 2) / retNu Pl σ₀ n) := by
  have hν : 0 < retNu Pl σ₀ n := retNu_pos Pl σ₀ n
  have hd : 0 < 2 * ‖Pl.signedCoeff σ₀‖ := mul_pos two_pos (norm_pos_iff.2 hC)
  have hA : 0 < (2 * ‖Pl.signedCoeff σ₀‖) ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hd _
  rw [retEps_eq_form hC n, Real.mul_rpow (by positivity) (Real.exp_pos _).le,
    Real.mul_rpow hA.le (Real.rpow_pos_of_pos hν _).le, ← Real.rpow_mul hν.le, ← Real.exp_mul]
  congr 2
  ring

/-- `ν^{a} ≤ (ν⁻¹)^k` for `0 < ν ≤ 1` and `-k ≤ a`. -/
theorem rpow_le_inv_pow {ν a : ℝ} {k : ℕ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hk : -(k : ℝ) ≤ a) :
    ν ^ a ≤ ν⁻¹ ^ k := by
  have h := Real.rpow_le_rpow_of_exponent_ge hν hν1 hk
  rwa [Real.rpow_neg hν.le, Real.rpow_natCast, ← inv_pow] at h

/-- The polynomial part of `ε^{3/2}`: `ε^{3/2} ≤ C ν^{-k} e^{-(γ/2)/ν}` eventually. -/
theorem eps32_le (D : SeqData) (hω : D.Pl.eigenvalue.im ≠ 0) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      (D.level n).ε ^ (3 / 2 : ℝ) ≤
        C * (D.level n).ν⁻¹ ^ k * Real.exp (-(gRate D.Pl / 2) / (D.level n).ν) := by
  set A := ((2 * ‖D.Pl.signedCoeff D.σ₀‖) ^ (-(1 / 3 : ℝ))) ^ (3 / 2 : ℝ) with hAdef
  set a := (D.Pl.kappa.re - 5 - 2 * D.σ₀) / 3 * (3 / 2) with hadef
  have hd : 0 < 2 * ‖D.Pl.signedCoeff D.σ₀‖ := mul_pos two_pos (norm_pos_iff.2 D.coeff_ne)
  have hA : 0 ≤ A := (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hd _) _).le
  obtain ⟨k, hk⟩ := exists_nat_ge (-a)
  refine ⟨A, k, hA, ?_⟩
  filter_upwards [(retNu_tendsto D.σ₀ hω).eventually (ge_mem_nhds one_pos)] with n hn
  have hν : 0 < retNu D.Pl D.σ₀ n := retNu_pos D.Pl D.σ₀ n
  have e : (D.level n).ε ^ (3 / 2 : ℝ) =
      A * retNu D.Pl D.σ₀ n ^ a * Real.exp (-(gRate D.Pl / 2) / retNu D.Pl D.σ₀ n) :=
    retEps_rpow32 D.coeff_ne n
  rw [e]
  have hp : retNu D.Pl D.σ₀ n ^ a ≤ (retNu D.Pl D.σ₀ n)⁻¹ ^ k :=
    rpow_le_inv_pow hν hn (by linarith)
  have hE : 0 ≤ Real.exp (-(gRate D.Pl / 2) / retNu D.Pl D.σ₀ n) := (Real.exp_pos _).le
  show A * retNu D.Pl D.σ₀ n ^ a * Real.exp (-(gRate D.Pl / 2) / retNu D.Pl D.σ₀ n) ≤
    A * (retNu D.Pl D.σ₀ n)⁻¹ ^ k * Real.exp (-(gRate D.Pl / 2) / retNu D.Pl D.σ₀ n)
  gcongr

/-- The ratio `ε^{3/2} e^{γ/ν} ν^k / e^{(γ/10)/ν} = A^{3/2} e^{(2γ/5)ν⁻¹}/(ν⁻¹)^{a+k}` tends to `∞`. -/
theorem wardGain_ratio_tendsto (D : SeqData) (hω : D.Pl.eigenvalue.im ≠ 0)
    (hγ : 0 < gRate D.Pl) (k : ℕ) :
    Tendsto (fun n : ℕ => (D.level n).ε ^ (3 / 2 : ℝ) * Real.exp (gRate D.Pl / (D.level n).ν) *
      (D.level n).ν ^ k / Real.exp ((gRate D.Pl / 10) / (D.level n).ν)) atTop atTop := by
  set A := ((2 * ‖D.Pl.signedCoeff D.σ₀‖) ^ (-(1 / 3 : ℝ))) ^ (3 / 2 : ℝ) with hAdef
  set a := (D.Pl.kappa.re - 5 - 2 * D.σ₀) / 3 * (3 / 2) with hadef
  have hd : 0 < 2 * ‖D.Pl.signedCoeff D.σ₀‖ := mul_pos two_pos (norm_pos_iff.2 D.coeff_ne)
  have hA : 0 < A := Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hd _) _
  have hνpos : ∀ n : ℕ, 0 < retNu D.Pl D.σ₀ n := fun n => retNu_pos D.Pl D.σ₀ n
  have hνT : Tendsto (retNu D.Pl D.σ₀) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨retNu_tendsto D.σ₀ hω, Eventually.of_forall hνpos⟩
  have hxT : Tendsto (fun n : ℕ => (retNu D.Pl D.σ₀ n)⁻¹) atTop atTop :=
    tendsto_inv_nhdsGT_zero.comp hνT
  have hb : 0 < 2 * gRate D.Pl / 5 := by positivity
  have hG := ((tendsto_exp_mul_div_rpow_atTop (a + k) _ hb).comp hxT).const_mul_atTop hA
  refine hG.congr' (Eventually.of_forall fun n => ?_)
  have hν := hνpos n
  have e : (D.level n).ε ^ (3 / 2 : ℝ) =
      A * retNu D.Pl D.σ₀ n ^ a * Real.exp (-(gRate D.Pl / 2) / retNu D.Pl D.σ₀ n) :=
    retEps_rpow32 D.coeff_ne n
  show A * (Real.exp (2 * gRate D.Pl / 5 * (retNu D.Pl D.σ₀ n)⁻¹) /
      (retNu D.Pl D.σ₀ n)⁻¹ ^ (a + k)) = (D.level n).ε ^ (3 / 2 : ℝ) *
        Real.exp (gRate D.Pl / retNu D.Pl D.σ₀ n) * retNu D.Pl D.σ₀ n ^ k /
          Real.exp ((gRate D.Pl / 10) / retNu D.Pl D.σ₀ n)
  rw [e, Real.inv_rpow hν.le, Real.rpow_add hν, Real.rpow_natCast, div_inv_eq_mul]
  have hE : Real.exp (-(gRate D.Pl / 2) / retNu D.Pl D.σ₀ n) *
      Real.exp (gRate D.Pl / retNu D.Pl D.σ₀ n) /
        Real.exp ((gRate D.Pl / 10) / retNu D.Pl D.σ₀ n) =
      Real.exp (2 * gRate D.Pl / 5 * (retNu D.Pl D.σ₀ n)⁻¹) := by
    rw [← Real.exp_add, ← Real.exp_sub]
    congr 1
    field_simp
    ring
  rw [← hE]
  have hE10 : 0 < Real.exp ((gRate D.Pl / 10) / retNu D.Pl D.σ₀ n) := Real.exp_pos _
  field_simp

/-- A bin of upper age `≤ 1`: for `h > 0` some `j` has `binUpper S h (j+1) ≤ 1`. -/
theorem exists_binUpper_le_one {S h : ℝ} (hh : 0 < h) :
    ∃ j : ℕ, binUpper S h (j + 1) ≤ 1 := by
  obtain ⟨j, hj⟩ := exists_nat_gt (S / h)
  refine ⟨j, ?_⟩
  unfold binUpper
  have hm : S < h * ((j + 1 : ℕ) : ℝ) := by
    have : S / h * h = S := div_mul_cancel₀ S hh.ne'
    push_cast
    nlinarith
  have he : S < Real.exp (h * ((j + 1 : ℕ) : ℝ)) :=
    hm.trans_le ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _))
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
  exact he.le

/-- **`WardGainMarginG` is false** (output bins of age `≤ 1`, any source of the gained norm):
`ε^{3/2}e^{γ/ν} / (ν^{-k}e^{γ/(10ν)}e^γ) → ∞`. -/
theorem not_wardGainMarginG (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    ¬ D.WardGainMarginG := by
  rintro ⟨C, k, hC⟩
  have hγ : 0 < gRate D.Pl := hst.gamma_pos
  have hT := (wardGain_ratio_tendsto D hst.omega_ne hγ k).eventually_gt_atTop
    (|C| * Real.exp (gRate D.Pl))
  obtain ⟨n, hn1, hn2⟩ := (hC.and hT).exists
  have hν : 0 < (D.level n).ν := (D.level n).ν_pos
  have hh : 0 < D.K.hbin := by unfold ReturnConsts.hbin; linarith [hst.δ_pos]
  obtain ⟨j, hj⟩ := exists_binUpper_le_one (S := (D.level n).Scut D.K) hh
  set u := binUpper ((D.level n).Scut D.K) D.K.hbin (j + 1) with hu
  have hS : 0 < (D.level n).Scut D.K := Real.rpow_pos_of_pos (D.level n).ε_pos _
  have hu0 : 0 ≤ u := by
    rw [hu]; unfold binUpper; exact mul_nonneg hS.le (Real.exp_pos _).le
  have hg : UnforcedLeray.Short.IIIa.gainG (gRate D.Pl) (D.level n).ν u ≤
      Real.exp (gRate D.Pl) := by
    unfold UnforcedLeray.Short.IIIa.gainG
    refine Real.exp_le_exp.2 ?_
    have h1 : gRate D.Pl * u / (1 + (D.level n).ν * u) ≤ gRate D.Pl * u :=
      div_le_self (by positivity) (by nlinarith)
    have h2 : gRate D.Pl * u ≤ gRate D.Pl := mul_le_of_le_one_right hγ.le hj
    linarith
  have hb := hn1 j
  rw [← hu] at hb
  have hX : 0 ≤ (D.level n).ν⁻¹ ^ k * Real.exp ((gRate D.Pl / 10) / (D.level n).ν) := by
    positivity
  have hg0 : 0 < UnforcedLeray.Short.IIIa.gainG (gRate D.Pl) (D.level n).ν u := Real.exp_pos _
  have hb2 : (D.level n).ε ^ (3 / 2 : ℝ) * Real.exp (gRate D.Pl / (D.level n).ν) ≤
      |C| * (D.level n).ν⁻¹ ^ k * Real.exp ((gRate D.Pl / 10) / (D.level n).ν) *
        Real.exp (gRate D.Pl) := by
    refine hb.trans ?_
    calc C * (D.level n).ν⁻¹ ^ k * Real.exp ((gRate D.Pl / 10) / (D.level n).ν) *
          UnforcedLeray.Short.IIIa.gainG (gRate D.Pl) (D.level n).ν u
        ≤ |C| * (D.level n).ν⁻¹ ^ k * Real.exp ((gRate D.Pl / 10) / (D.level n).ν) *
          UnforcedLeray.Short.IIIa.gainG (gRate D.Pl) (D.level n).ν u := by
          have := mul_le_mul_of_nonneg_right (le_abs_self C)
            (mul_nonneg hX hg0.le)
          nlinarith
      _ ≤ |C| * (D.level n).ν⁻¹ ^ k * Real.exp ((gRate D.Pl / 10) / (D.level n).ν) *
          Real.exp (gRate D.Pl) :=
          mul_le_mul_of_nonneg_left hg (by positivity)
  have hE10 : 0 < Real.exp ((gRate D.Pl / 10) / (D.level n).ν) := Real.exp_pos _
  have hνk : 0 < (D.level n).ν ^ k := pow_pos hν k
  have hlt : (D.level n).ε ^ (3 / 2 : ℝ) * Real.exp (gRate D.Pl / (D.level n).ν) *
      (D.level n).ν ^ k / Real.exp ((gRate D.Pl / 10) / (D.level n).ν) ≤
      |C| * Real.exp (gRate D.Pl) := by
    rw [div_le_iff₀ hE10]
    have hm := mul_le_mul_of_nonneg_right hb2 hνk.le
    have hc : (D.level n).ν⁻¹ ^ k * (D.level n).ν ^ k = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hν.ne', one_pow]
    calc (D.level n).ε ^ (3 / 2 : ℝ) * Real.exp (gRate D.Pl / (D.level n).ν) *
          (D.level n).ν ^ k
        ≤ |C| * (D.level n).ν⁻¹ ^ k * Real.exp ((gRate D.Pl / 10) / (D.level n).ν) *
          Real.exp (gRate D.Pl) * (D.level n).ν ^ k := hm
      _ = |C| * Real.exp (gRate D.Pl) * Real.exp ((gRate D.Pl / 10) / (D.level n).ν) *
          ((D.level n).ν⁻¹ ^ k * (D.level n).ν ^ k) := by ring
      _ = |C| * Real.exp (gRate D.Pl) * Real.exp ((gRate D.Pl / 10) / (D.level n).ν) := by
          rw [hc, mul_one]
  linarith

/-! ## The two margins the source uses (5594-5599) -/

/-- **Late-output margin** (5594-5599, `ν u ≥ 2/3`): `ε^{3/2}e^{γ/ν} ≤ C ν^{-k}e^{γ/(10ν)}g(u)`. -/
def SeqData.LateGainMarginG (D : SeqData) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, 2 / 3 ≤ (D.level n).ν * u →
    (D.level n).ε ^ (3 / 2 : ℝ) * Real.exp (gRate D.Pl / (D.level n).ν) ≤
      C * (D.level n).ν⁻¹ ^ k * Real.exp ((gRate D.Pl / 10) / (D.level n).ν) *
        UnforcedLeray.Short.IIIa.gainG (gRate D.Pl) (D.level n).ν u

/-- **Early-source margin** (5594-5599, `0 ≤ t`, `ν t ≤ 3/2`): `ε^{3/2}g(t) ≤ C ν^{-k}e^{γ/(10ν)}`. -/
def SeqData.EarlyGainMarginG (D : SeqData) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ t : ℝ, 0 ≤ t → (D.level n).ν * t ≤ 3 / 2 →
    (D.level n).ε ^ (3 / 2 : ℝ) * UnforcedLeray.Short.IIIa.gainG (gRate D.Pl) (D.level n).ν t ≤
      C * (D.level n).ν⁻¹ ^ k * Real.exp ((gRate D.Pl / 10) / (D.level n).ν)

theorem lateGainMarginG (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    D.LateGainMarginG := by
  obtain ⟨C, k, hC0, hC⟩ := eps32_le D hst.omega_ne
  have hγ : 0 < gRate D.Pl := hst.gamma_pos
  refine ⟨C, k, ?_⟩
  filter_upwards [hC] with n hn u hu
  have hν : 0 < (D.level n).ν := (D.level n).ν_pos
  have hupos : 0 < u := by
    by_contra hneg
    have hneg' := not_lt.1 hneg
    nlinarith
  have hgl : Real.exp ((2 * gRate D.Pl / 5) / (D.level n).ν) ≤
      UnforcedLeray.Short.IIIa.gainG (gRate D.Pl) (D.level n).ν u := by
    unfold UnforcedLeray.Short.IIIa.gainG
    refine Real.exp_le_exp.2 ?_
    have h1 : 0 < 1 + (D.level n).ν * u := by positivity
    rw [div_le_div_iff₀ hν h1]
    nlinarith [mul_le_mul_of_nonneg_left hu hγ.le]
  have hX : 0 ≤ C * (D.level n).ν⁻¹ ^ k := by positivity
  have e : Real.exp (-(gRate D.Pl / 2) / (D.level n).ν) * Real.exp (gRate D.Pl / (D.level n).ν) =
      Real.exp ((gRate D.Pl / 10) / (D.level n).ν) *
        Real.exp ((2 * gRate D.Pl / 5) / (D.level n).ν) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    field_simp
    ring
  calc (D.level n).ε ^ (3 / 2 : ℝ) * Real.exp (gRate D.Pl / (D.level n).ν)
      ≤ C * (D.level n).ν⁻¹ ^ k * Real.exp (-(gRate D.Pl / 2) / (D.level n).ν) *
          Real.exp (gRate D.Pl / (D.level n).ν) :=
        mul_le_mul_of_nonneg_right hn (Real.exp_pos _).le
    _ = C * (D.level n).ν⁻¹ ^ k * Real.exp ((gRate D.Pl / 10) / (D.level n).ν) *
          Real.exp ((2 * gRate D.Pl / 5) / (D.level n).ν) := by
        rw [mul_assoc, e]; ring
    _ ≤ C * (D.level n).ν⁻¹ ^ k * Real.exp ((gRate D.Pl / 10) / (D.level n).ν) *
          UnforcedLeray.Short.IIIa.gainG (gRate D.Pl) (D.level n).ν u :=
        mul_le_mul_of_nonneg_left hgl (mul_nonneg hX (Real.exp_pos _).le)

theorem earlyGainMarginG (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    D.EarlyGainMarginG := by
  obtain ⟨C, k, hC0, hC⟩ := eps32_le D hst.omega_ne
  have hγ : 0 < gRate D.Pl := hst.gamma_pos
  refine ⟨C, k, ?_⟩
  filter_upwards [hC] with n hn t ht0 ht
  have hν : 0 < (D.level n).ν := (D.level n).ν_pos
  have hge : UnforcedLeray.Short.IIIa.gainG (gRate D.Pl) (D.level n).ν t ≤
      Real.exp ((3 * gRate D.Pl / 5) / (D.level n).ν) := by
    unfold UnforcedLeray.Short.IIIa.gainG
    refine Real.exp_le_exp.2 ?_
    have h1 : 0 < 1 + (D.level n).ν * t := by positivity
    rw [div_le_div_iff₀ h1 hν]
    nlinarith [mul_le_mul_of_nonneg_left ht hγ.le]
  have hX : 0 ≤ C * (D.level n).ν⁻¹ ^ k := by positivity
  have e : Real.exp (-(gRate D.Pl / 2) / (D.level n).ν) *
      Real.exp ((3 * gRate D.Pl / 5) / (D.level n).ν) =
      Real.exp ((gRate D.Pl / 10) / (D.level n).ν) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  have hg0 : 0 ≤ UnforcedLeray.Short.IIIa.gainG (gRate D.Pl) (D.level n).ν t :=
    (Real.exp_pos _).le
  calc (D.level n).ε ^ (3 / 2 : ℝ) * UnforcedLeray.Short.IIIa.gainG (gRate D.Pl) (D.level n).ν t
      ≤ C * (D.level n).ν⁻¹ ^ k * Real.exp (-(gRate D.Pl / 2) / (D.level n).ν) *
          Real.exp ((3 * gRate D.Pl / 5) / (D.level n).ν) := by
        refine mul_le_mul hn hge hg0 ?_
        exact mul_nonneg hX (Real.exp_pos _).le
    _ = C * (D.level n).ν⁻¹ ^ k * Real.exp ((gRate D.Pl / 10) / (D.level n).ν) := by
        rw [mul_assoc, e]

end UnforcedLeray.Short.PartIIIb.Concrete

end
