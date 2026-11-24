import UnforcedLeray.Loc.Hyp.HeatProfileRegularity.Conv
import UnforcedLeray.Units.B0306

/-!
# `HeatProfileRegularity` helper: heat smoothing of `|x|^{-1}`-type fields, with constants

Helper module of `Loc/Hyp/HeatProfileRegularity.lean` (hypothesis `HeatProfileRegularity`,
infrastructure INF04, blueprint unit B0710; `paper/main.tex` lines 274–281, where the
manuscript states `|D^j H_h[u_dss]| ≤ C_j⟨y⟩^{-1-j}`, `j ≤ 2`, "by splitting the heat integral
into the near and far regions").

`InvDist b ε` says: `b` is smooth off `0` and `‖D^k b(x)‖ ≤ ε |x|^{-1-k}` for `k ≤ 3`, `x ≠ 0`
(the manuscript's bounds of lines 152–156, with one constant `ε`). The main result,
`heat_smoothing`, is the near/far estimate at a fixed heat time `h > 0`:
`e^{hΔ} b` is `C²` and `‖D^n e^{hΔ} b (y)‖ ≤ ε Q_n (1 + |y|)^{-1-n}` for `n ≤ 2`, with `Q_n`
depending only on `h`. The point of the explicit factor `ε` is linearity: applied to differences
of fields it gives Lipschitz continuity in phase (`Loc/Hyp/HeatProfileRegularity.lean`).

Proof, as in `Units/B0306.lean` (tex lines 5915–5921) and with its cutoff `cut`:
* near part `cut • b`: integrable with `∫|cut • b| ≤ ε ∫ cut(x)|x|^{-1}`; the derivatives fall on
  the Gaussian (`B0306.average_nearPart_contDiff`), whose derivatives decay faster than every
  power (`kernel_deriv_decay`), and `|y - x| ≥ |y| - 1/2` on the support;
* far part `(1 - cut) • b`: smooth with `‖D^k‖ ≤ ε B_k (1 + |x|)^{-1-k}` for `k ≤ 3`
  (`far_deriv_pointwise`); the derivatives fall on the datum (`iteratedFDeriv_bconv_upTo`),
  and Peetre's inequality `1 + |y| ≤ (1 + |y - x|)(1 + |x|)` with the Gaussian moments gives the
  decay.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Metric
open scoped ContDiff Topology

namespace UnforcedLeray.HeatProfileReg

open UnforcedLeray.B0306

/-- A field smooth off `0` with `‖D^k b(x)‖ ≤ ε |x|^{-1-k}` for `k ≤ 3` (tex lines 152–156,
with a single constant). -/
structure InvDist (b : SpatialField) (ε : ℝ) : Prop where
  smooth : ContDiffOn ℝ ∞ b {0}ᶜ
  bound : ∀ k : ℕ, k ≤ 3 → ∀ x : Space, x ≠ 0 → ‖iteratedFDeriv ℝ k b x‖ ≤ ε / ‖x‖ ^ (k + 1)

theorem InvDist.eps_nonneg {b : SpatialField} {ε : ℝ} (hb : InvDist b ε) : 0 ≤ ε := by
  have hn : ‖(EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : Space)‖ = 1 := by simp
  have he : (EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : Space) ≠ 0 := by
    intro h; rw [h, norm_zero] at hn; exact zero_ne_one hn
  have h := (norm_nonneg _).trans (hb.bound 0 (by omega) _ he)
  rw [hn, one_pow, div_one] at h
  exact h

/-! ### Elementary inequalities -/

theorem one_add_norm_le_mul (y x : Space) : 1 + ‖y‖ ≤ (1 + ‖y - x‖) * (1 + ‖x‖) := by
  have h := norm_sub_norm_le y x
  nlinarith [norm_nonneg (y - x), norm_nonneg x, mul_nonneg (norm_nonneg (y - x)) (norm_nonneg x)]

/-- Peetre's inequality in the form used for convolutions. -/
theorem inv_one_add_pow_le (y x : Space) (m : ℕ) :
    1 / (1 + ‖y - x‖) ^ m ≤ (1 + ‖x‖) ^ m / (1 + ‖y‖) ^ m := by
  have h1 : 0 < (1 + ‖y - x‖) ^ m := by positivity
  have h2 : 0 < (1 + ‖y‖) ^ m := by positivity
  rw [div_le_div_iff₀ h1 h2, one_mul, ← mul_pow, mul_comm]
  exact pow_le_pow_left₀ (by positivity) (one_add_norm_le_mul y x) m

theorem one_add_pow_le (r : ℝ) (hr : 0 ≤ r) (m : ℕ) : (1 + r) ^ m ≤ 2 ^ m * (1 + r ^ m) := by
  rcases le_total r 1 with h | h
  · calc (1 + r) ^ m ≤ 2 ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
      _ ≤ 2 ^ m * (1 + r ^ m) :=
        le_mul_of_one_le_right (by positivity) (by linarith [pow_nonneg hr m])
  · calc (1 + r) ^ m ≤ (2 * r) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
      _ = 2 ^ m * r ^ m := mul_pow _ _ _
      _ ≤ 2 ^ m * (1 + r ^ m) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- `(1 + r)^m e^{-a r²}` is bounded on `r ≥ 0`. -/
theorem one_add_pow_mul_exp_le {a : ℝ} (ha : 0 < a) (m : ℕ) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ r : ℝ, 0 ≤ r → (1 + r) ^ m * Real.exp (-(a * r ^ 2)) ≤ G := by
  obtain ⟨C, hC0, hC⟩ := Gaussian.rpow_mul_exp_neg_mul_sq_le (m := (m : ℝ)) (b := a / 2)
    (Nat.cast_nonneg m) (by positivity)
  refine ⟨Real.exp a * C, by positivity, fun r hr => ?_⟩
  have h1 := hC (1 + r) (by linarith)
  rw [Real.rpow_natCast] at h1
  have h2 : Real.exp (-(a * r ^ 2)) ≤ Real.exp a * Real.exp (-(a / 2 * (1 + r) ^ 2)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith [mul_nonneg ha.le (sq_nonneg (1 - r))]
  calc (1 + r) ^ m * Real.exp (-(a * r ^ 2))
      ≤ (1 + r) ^ m * (Real.exp a * Real.exp (-(a / 2 * (1 + r) ^ 2))) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = Real.exp a * ((1 + r) ^ m * Real.exp (-(a / 2 * (1 + r) ^ 2))) := by ring
    _ ≤ Real.exp a * C := mul_le_mul_of_nonneg_left h1 (Real.exp_pos a).le

/-- The derivatives of the heat kernel decay faster than every power. -/
theorem kernel_deriv_decay {h : ℝ} (hh : 0 < h) (n m : ℕ) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ z : Space,
      ‖iteratedFDeriv ℝ n (Heat.kernel h) z‖ ≤ E / (1 + ‖z‖) ^ m := by
  obtain ⟨G, hG0, hG⟩ := one_add_pow_mul_exp_le (a := (8 * h)⁻¹) (by positivity) m
  have hE0 : 0 ≤ Kernels.heatDerivConst n * h ^ (-((3 + n : ℝ) / 2)) :=
    mul_nonneg (Kernels.heatDerivConst_pos n).le (Real.rpow_nonneg hh.le _)
  refine ⟨Kernels.heatDerivConst n * h ^ (-((3 + n : ℝ) / 2)) * G, mul_nonneg hE0 hG0,
    fun z => ?_⟩
  have hk := Kernels.norm_iteratedFDeriv_heatKernel_le n hh z
  have hpos : 0 < (1 + ‖z‖) ^ m := by positivity
  rw [le_div_iff₀ hpos]
  have he : Real.exp (-‖z‖ ^ 2 / (8 * h)) = Real.exp (-((8 * h)⁻¹ * ‖z‖ ^ 2)) := by
    congr 1; ring
  have hg := hG ‖z‖ (norm_nonneg z)
  rw [he] at hk
  calc ‖iteratedFDeriv ℝ n (Heat.kernel h) z‖ * (1 + ‖z‖) ^ m
      ≤ (Kernels.heatDerivConst n * h ^ (-((3 + n : ℝ) / 2)) *
          Real.exp (-((8 * h)⁻¹ * ‖z‖ ^ 2))) * (1 + ‖z‖) ^ m :=
        mul_le_mul_of_nonneg_right hk hpos.le
    _ = Kernels.heatDerivConst n * h ^ (-((3 + n : ℝ) / 2)) *
          ((1 + ‖z‖) ^ m * Real.exp (-((8 * h)⁻¹ * ‖z‖ ^ 2))) := by ring
    _ ≤ Kernels.heatDerivConst n * h ^ (-((3 + n : ℝ) / 2)) * G :=
        mul_le_mul_of_nonneg_left hg hE0

/-- Polynomially weighted Gaussian moments are finite. -/
theorem integrable_kernel_mul_one_add_pow {h : ℝ} (hh : 0 < h) (m : ℕ) :
    Integrable (fun x : Space => Heat.kernel h x * (1 + ‖x‖) ^ m) := by
  refine (((Heat.kernel_integrable hh).add (integrable_pow_mul_kernel hh m)).const_mul
    (2 ^ m)).mono' ?_ (Eventually.of_forall fun x => ?_)
  · exact ((Kernels.heatKernel_smooth h).continuous.mul
      ((continuous_const.add continuous_norm).pow m)).aestronglyMeasurable
  · have hK := Heat.kernel_nonneg hh x
    rw [Real.norm_of_nonneg (by positivity)]
    have h1 := one_add_pow_le ‖x‖ (norm_nonneg x) m
    calc Heat.kernel h x * (1 + ‖x‖) ^ m ≤ Heat.kernel h x * (2 ^ m * (1 + ‖x‖ ^ m)) :=
          mul_le_mul_of_nonneg_left h1 hK
      _ = 2 ^ m * (Heat.kernel h x + ‖x‖ ^ m * Heat.kernel h x) := by ring

/-! ### The near part -/

/-- `cut(x) |x|^{-1}`, the scalar majorant of the near part. -/
def nearWeight (x : Space) : ℝ := cut x * ‖x‖⁻¹

theorem nearWeight_nonneg (x : Space) : 0 ≤ nearWeight x :=
  mul_nonneg cut.nonneg (inv_nonneg.2 (norm_nonneg x))

/-- `|x|^{-1}` is locally integrable in three dimensions. -/
theorem integrable_nearWeight : Integrable nearWeight := by
  have hm : AEStronglyMeasurable nearWeight volume :=
    (cut_smooth.continuous.measurable.mul measurable_norm.inv).aestronglyMeasurable
  have hfin : Module.finrank ℝ Space = 3 := finrank_euclideanSpace_fin
  have hloc : LocallyIntegrable nearWeight volume := by
    refine locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1) ?_ ?_ ?_ hm
    · rw [hfin]; norm_num
    · rw [hfin]; norm_num
    · filter_upwards with x
      rw [Real.norm_of_nonneg (nearWeight_nonneg x), nearWeight, Real.rpow_neg_one, one_mul]
      exact mul_le_of_le_one_left (inv_nonneg.2 (norm_nonneg x)) cut.le_one
  have hint : IntegrableOn nearWeight (closedBall 0 (1 / 2)) volume :=
    hloc.integrableOn_isCompact (isCompact_closedBall 0 _)
  refine hint.integrable_of_forall_notMem_eq_zero fun x hx => ?_
  rw [mem_closedBall_zero_iff, not_le] at hx
  simp [nearWeight, cut_eq_zero hx.le]

theorem norm_nearPart_le_weight {b : SpatialField} {ε : ℝ} (hb : InvDist b ε) {x : Space}
    (hx : x ≠ 0) : ‖nearPart b x‖ ≤ ε * nearWeight x := by
  rw [nearPart, norm_smul, Real.norm_of_nonneg cut.nonneg, nearWeight]
  have h := hb.bound 0 (by omega) x hx
  rw [norm_iteratedFDeriv_zero, zero_add, pow_one] at h
  calc cut x * ‖b x‖ ≤ cut x * (ε / ‖x‖) := mul_le_mul_of_nonneg_left h cut.nonneg
    _ = ε * (cut x * ‖x‖⁻¹) := by rw [div_eq_mul_inv]; ring

theorem nearPart_integrable_of {b : SpatialField} {ε : ℝ} (hb : InvDist b ε) :
    Integrable (nearPart b) := by
  have hm : AEStronglyMeasurable (nearPart b) volume :=
    cut_smooth.continuous.aestronglyMeasurable.smul
      (aestronglyMeasurable_of_contDiffOn hb.smooth)
  refine (integrable_nearWeight.const_mul ε).mono' hm ?_
  filter_upwards [Measure.ae_ne volume (0 : Space)] with x hx
  exact norm_nearPart_le_weight hb hx

/-- Derivatives of the smoothed near part, with a constant linear in `ε`. -/
theorem near_deriv_bound {h : ℝ} (hh : 0 < h) (n : ℕ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ (b : SpatialField) (ε : ℝ), InvDist b ε → ∀ y : Space,
      ‖iteratedFDeriv ℝ n (Heat.average h (nearPart b)) y‖ ≤ ε * Q / (1 + ‖y‖) ^ (n + 1) := by
  obtain ⟨E, hE0, hE⟩ := kernel_deriv_decay hh n (n + 1)
  have hLf : 0 ≤ ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Space →L[ℝ] Space).flip‖ :=
    ContinuousLinearMap.opNorm_nonneg _
  have hW0 : 0 ≤ ∫ x, nearWeight x := integral_nonneg nearWeight_nonneg
  refine ⟨‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Space →L[ℝ] Space).flip‖ * E *
    (3 / 2) ^ (n + 1) * ∫ x, nearWeight x,
    mul_nonneg (mul_nonneg (mul_nonneg hLf hE0) (by positivity)) hW0, fun b ε hb y => ?_⟩
  have hε := hb.eps_nonneg
  have hnear := nearPart_integrable_of hb
  rw [(average_nearPart_contDiff hh hnear n).2]
  have hpos : 0 < (1 + ‖y‖) ^ (n + 1) := by positivity
  have hc0 : 0 ≤ ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Space →L[ℝ] Space).flip‖ * E *
      (3 / 2) ^ (n + 1) / (1 + ‖y‖) ^ (n + 1) * ε :=
    mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg hLf hE0) (by positivity)) hpos.le) hε
  have hpt : ∀ᵐ x ∂(volume : Measure Space),
      ‖((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Space →L[ℝ] Space).flip
        (nearPart b x)).compContinuousMultilinearMap
          (iteratedFDeriv ℝ n (Heat.kernel h) (y - x))‖ ≤
      (‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Space →L[ℝ] Space).flip‖ * E *
        (3 / 2) ^ (n + 1) / (1 + ‖y‖) ^ (n + 1) * ε) * nearWeight x := by
    filter_upwards [Measure.ae_ne volume (0 : Space)] with x hx0
    refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
    by_cases hx : ‖x‖ < 1 / 2
    · have hK : ‖iteratedFDeriv ℝ n (Heat.kernel h) (y - x)‖ ≤
          E * (3 / 2) ^ (n + 1) / (1 + ‖y‖) ^ (n + 1) := by
        refine (hE (y - x)).trans ?_
        have h1 := inv_one_add_pow_le y x (n + 1)
        have h2 : (1 + ‖x‖) ^ (n + 1) ≤ (3 / 2) ^ (n + 1) :=
          pow_le_pow_left₀ (by positivity) (by linarith) _
        calc E / (1 + ‖y - x‖) ^ (n + 1) = E * (1 / (1 + ‖y - x‖) ^ (n + 1)) := by ring
          _ ≤ E * ((1 + ‖x‖) ^ (n + 1) / (1 + ‖y‖) ^ (n + 1)) :=
            mul_le_mul_of_nonneg_left h1 hE0
          _ ≤ E * ((3 / 2) ^ (n + 1) / (1 + ‖y‖) ^ (n + 1)) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h2 hpos.le) hE0
          _ = E * (3 / 2) ^ (n + 1) / (1 + ‖y‖) ^ (n + 1) := by ring
      have hN := norm_nearPart_le_weight hb hx0
      have hKpos : 0 ≤ E * (3 / 2) ^ (n + 1) / (1 + ‖y‖) ^ (n + 1) :=
        div_nonneg (mul_nonneg hE0 (by positivity)) hpos.le
      calc ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Space →L[ℝ] Space).flip (nearPart b x)‖ *
            ‖iteratedFDeriv ℝ n (Heat.kernel h) (y - x)‖
          ≤ (‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Space →L[ℝ] Space).flip‖ *
              ‖nearPart b x‖) * (E * (3 / 2) ^ (n + 1) / (1 + ‖y‖) ^ (n + 1)) :=
            mul_le_mul (ContinuousLinearMap.le_opNorm _ _) hK (norm_nonneg _)
              (mul_nonneg hLf (norm_nonneg _))
        _ ≤ (‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Space →L[ℝ] Space).flip‖ *
              (ε * nearWeight x)) * (E * (3 / 2) ^ (n + 1) / (1 + ‖y‖) ^ (n + 1)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN hLf) hKpos
        _ = (‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Space →L[ℝ] Space).flip‖ * E *
              (3 / 2) ^ (n + 1) / (1 + ‖y‖) ^ (n + 1) * ε) * nearWeight x := by ring
    · have h0 : nearPart b x = 0 := nearPart_eq_zero b (not_lt.1 hx)
      rw [h0, map_zero, norm_zero, zero_mul]
      exact mul_nonneg hc0 (nearWeight_nonneg x)
  refine (norm_integral_le_of_norm_le (integrable_nearWeight.const_mul _) hpt).trans
    (le_of_eq ?_)
  rw [integral_const_mul]
  ring

/-! ### The far part -/

/-- A bound on the `i`-th derivative of `1 - cut`. -/
def cutA (i : ℕ) : ℝ := (one_sub_cut_bdd i).choose

theorem cutA_nonneg (i : ℕ) : 0 ≤ cutA i := (one_sub_cut_bdd i).choose_spec.1

theorem cutA_bound (i : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ i (fun x => 1 - (cut : Space → ℝ) x) x‖ ≤ cutA i :=
  (one_sub_cut_bdd i).choose_spec.2 x

/-- The Leibniz constant of the far part on the transition shell `1/4 ≤ |x| ≤ 1/2`. -/
def farS (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * cutA i * 4 ^ (k - i + 1)

theorem farS_nonneg (k : ℕ) : 0 ≤ farS k :=
  Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (cutA_nonneg i)) (by positivity)

/-- The constant of `far_deriv_pointwise`. -/
def farB (k : ℕ) : ℝ := 3 ^ (k + 1) + farS k * (3 / 2) ^ (k + 1)

theorem farB_nonneg (k : ℕ) : 0 ≤ farB k :=
  add_nonneg (by positivity) (mul_nonneg (farS_nonneg k) (by positivity))

/-- **The far part decays like the datum**: `‖D^k((1 - cut) b)(x)‖ ≤ ε B_k (1 + |x|)^{-1-k}`
for `k ≤ 3`. -/
theorem far_deriv_pointwise {b : SpatialField} {ε : ℝ} (hb : InvDist b ε) {k : ℕ} (hk : k ≤ 3)
    (x : Space) :
    ‖iteratedFDeriv ℝ k (farPart b) x‖ ≤ ε * farB k / (1 + ‖x‖) ^ (k + 1) := by
  have hε := hb.eps_nonneg
  have hpos : 0 < (1 + ‖x‖) ^ (k + 1) := by positivity
  have hR0 : 0 ≤ ε * farB k / (1 + ‖x‖) ^ (k + 1) :=
    div_nonneg (mul_nonneg hε (farB_nonneg k)) hpos.le
  by_cases hx1 : ‖x‖ < 1 / 4
  · rw [((farPart_eventuallyEq_zero b hx1).iteratedFDeriv ℝ k).eq_of_nhds]
    simpa using hR0
  have hx0 : x ≠ 0 := by
    rintro rfl; rw [norm_zero] at hx1; norm_num at hx1
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx0
  by_cases hx2 : 1 / 2 < ‖x‖
  · rw [((farPart_eventuallyEq b hx2).iteratedFDeriv ℝ k).eq_of_nhds]
    refine (hb.bound k hk x hx0).trans ?_
    have hp1 : 0 < ‖x‖ ^ (k + 1) := pow_pos hxn _
    rw [div_le_div_iff₀ hp1 hpos]
    have h3 : (1 + ‖x‖) ^ (k + 1) ≤ 3 ^ (k + 1) * ‖x‖ ^ (k + 1) := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) _
    have h4 : 3 ^ (k + 1) * ‖x‖ ^ (k + 1) ≤ farB k * ‖x‖ ^ (k + 1) :=
      mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right (mul_nonneg (farS_nonneg k) (by positivity))) hp1.le
    calc ε * (1 + ‖x‖) ^ (k + 1) ≤ ε * (farB k * ‖x‖ ^ (k + 1)) :=
          mul_le_mul_of_nonneg_left (h3.trans h4) hε
      _ = ε * farB k * ‖x‖ ^ (k + 1) := by ring
  · push Not at hx1 hx2
    have hmem : x ∈ ({0}ᶜ : Set Space) := hx0
    have hopen : IsOpen ({0}ᶜ : Set Space) := isOpen_compl_singleton
    have hf : ContDiffOn ℝ ∞ (fun x => 1 - (cut : Space → ℝ) x) {0}ᶜ :=
      (contDiff_const.sub cut_smooth).contDiffOn
    have key := norm_iteratedFDerivWithin_smul_le hf hb.smooth hopen.uniqueDiffOn hmem (n := k)
      (by exact_mod_cast le_top)
    rw [iteratedFDerivWithin_of_isOpen k hopen hmem] at key
    have hsum : (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        ‖iteratedFDerivWithin ℝ i (fun x => 1 - (cut : Space → ℝ) x) {0}ᶜ x‖ *
        ‖iteratedFDerivWithin ℝ (k - i) b {0}ᶜ x‖) ≤ ε * farS k := by
      rw [farS, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [iteratedFDerivWithin_of_isOpen i hopen hmem,
        iteratedFDerivWithin_of_isOpen (k - i) hopen hmem]
      have h2 : ‖iteratedFDeriv ℝ (k - i) b x‖ ≤ ε * 4 ^ (k - i + 1) := by
        refine (hb.bound (k - i) (by omega) x hx0).trans ?_
        rw [div_le_iff₀ (pow_pos hxn _)]
        have h1 : 1 ≤ 4 ^ (k - i + 1) * ‖x‖ ^ (k - i + 1) := by
          rw [← mul_pow]; exact one_le_pow₀ (by linarith)
        calc ε = ε * 1 := (mul_one ε).symm
          _ ≤ ε * (4 ^ (k - i + 1) * ‖x‖ ^ (k - i + 1)) := mul_le_mul_of_nonneg_left h1 hε
          _ = ε * 4 ^ (k - i + 1) * ‖x‖ ^ (k - i + 1) := by ring
      calc (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun x => 1 - (cut : Space → ℝ) x) x‖ *
            ‖iteratedFDeriv ℝ (k - i) b x‖
          ≤ (k.choose i : ℝ) * cutA i * (ε * 4 ^ (k - i + 1)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (cutA_bound i x) (Nat.cast_nonneg _)) h2
              (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (cutA_nonneg i))
        _ = ε * ((k.choose i : ℝ) * cutA i * 4 ^ (k - i + 1)) := by ring
    refine (key.trans hsum).trans ?_
    rw [le_div_iff₀ hpos]
    have h3 : (1 + ‖x‖) ^ (k + 1) ≤ (3 / 2) ^ (k + 1) :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    have h4 : farS k * (3 / 2) ^ (k + 1) ≤ farB k := le_add_of_nonneg_left (by positivity)
    calc ε * farS k * (1 + ‖x‖) ^ (k + 1) ≤ ε * farS k * (3 / 2) ^ (k + 1) :=
          mul_le_mul_of_nonneg_left h3 (mul_nonneg hε (farS_nonneg k))
      _ = ε * (farS k * (3 / 2) ^ (k + 1)) := by ring
      _ ≤ ε * farB k := mul_le_mul_of_nonneg_left h4 hε

theorem farPart_bddUpTo {b : SpatialField} {ε : ℝ} (hb : InvDist b ε) :
    BddDerivsUpTo 3 (farPart b) := by
  intro k hk
  refine ⟨ε * farB k, fun x => (far_deriv_pointwise hb hk x).trans ?_⟩
  have hpos : 1 ≤ (1 + ‖x‖) ^ (k + 1) := one_le_pow₀ (by linarith [norm_nonneg x])
  exact div_le_self (mul_nonneg hb.eps_nonneg (farB_nonneg k)) hpos

/-- The smoothed far part, to order `n ≤ 2`: derivatives fall on the datum. -/
theorem average_farPart_upTo {h : ℝ} (hh : 0 < h) {b : SpatialField}
    (hfs : ContDiff ℝ ∞ (farPart b)) (hfb : BddDerivsUpTo 3 (farPart b)) {n : ℕ} (hn : n ≤ 2) :
    ContDiff ℝ n (Heat.average h (farPart b)) ∧
      iteratedFDeriv ℝ n (Heat.average h (farPart b)) =
        fun y => ∫ x, Heat.kernel h x • iteratedFDeriv ℝ n (farPart b) (y - x) := by
  rw [average_farPart_eq]
  obtain ⟨h1, h2⟩ := iteratedFDeriv_bconv_upTo (Heat.kernel_integrable hh) n
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Space →L[ℝ] Space) (farPart b) hfs
    (fun k hk => hfb k (by omega))
  refine ⟨h1, ?_⟩
  rw [h2]
  funext y
  congr 1

/-- The constant of `far_deriv_bound`. -/
def farQ (h : ℝ) (n : ℕ) : ℝ := farB n * ∫ x : Space, Heat.kernel h x * (1 + ‖x‖) ^ (n + 1)

/-- Derivatives of the smoothed far part, with a constant linear in `ε`. -/
theorem far_deriv_bound {h : ℝ} (hh : 0 < h) {n : ℕ} (hn : n ≤ 2) {b : SpatialField} {ε : ℝ}
    (hb : InvDist b ε) (y : Space) :
    ‖iteratedFDeriv ℝ n (Heat.average h (farPart b)) y‖ ≤ ε * farQ h n / (1 + ‖y‖) ^ (n + 1) := by
  have hε := hb.eps_nonneg
  rw [(average_farPart_upTo hh (farPart_smooth hb.smooth) (farPart_bddUpTo hb) hn).2]
  have hpos : 0 < (1 + ‖y‖) ^ (n + 1) := by positivity
  have hc0 : 0 ≤ ε * farB n / (1 + ‖y‖) ^ (n + 1) :=
    div_nonneg (mul_nonneg hε (farB_nonneg n)) hpos.le
  have hpt : ∀ x : Space, ‖Heat.kernel h x • iteratedFDeriv ℝ n (farPart b) (y - x)‖ ≤
      ε * farB n / (1 + ‖y‖) ^ (n + 1) * (Heat.kernel h x * (1 + ‖x‖) ^ (n + 1)) := by
    intro x
    have hK := Heat.kernel_nonneg hh x
    rw [norm_smul, Real.norm_of_nonneg hK]
    have h1 := far_deriv_pointwise hb (k := n) (by omega) (y - x)
    have h2 := inv_one_add_pow_le y x (n + 1)
    have h3 : ε * farB n / (1 + ‖y - x‖) ^ (n + 1) ≤
        ε * farB n / (1 + ‖y‖) ^ (n + 1) * (1 + ‖x‖) ^ (n + 1) := by
      calc ε * farB n / (1 + ‖y - x‖) ^ (n + 1)
          = ε * farB n * (1 / (1 + ‖y - x‖) ^ (n + 1)) := by ring
        _ ≤ ε * farB n * ((1 + ‖x‖) ^ (n + 1) / (1 + ‖y‖) ^ (n + 1)) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hε (farB_nonneg n))
        _ = ε * farB n / (1 + ‖y‖) ^ (n + 1) * (1 + ‖x‖) ^ (n + 1) := by ring
    calc Heat.kernel h x * ‖iteratedFDeriv ℝ n (farPart b) (y - x)‖
        ≤ Heat.kernel h x * (ε * farB n / (1 + ‖y‖) ^ (n + 1) * (1 + ‖x‖) ^ (n + 1)) :=
          mul_le_mul_of_nonneg_left (h1.trans h3) hK
      _ = ε * farB n / (1 + ‖y‖) ^ (n + 1) * (Heat.kernel h x * (1 + ‖x‖) ^ (n + 1)) := by ring
  refine (norm_integral_le_of_norm_le
    ((integrable_kernel_mul_one_add_pow hh (n + 1)).const_mul _)
    (Eventually.of_forall hpt)).trans (le_of_eq ?_)
  rw [integral_const_mul, farQ]
  ring

/-! ### The heat smoothing estimate -/

theorem heat_integrand_integrable {h : ℝ} (hh : 0 < h) {b : SpatialField} {ε : ℝ}
    (hb : InvDist b ε) (y : Space) : Integrable (fun x => Heat.kernel h x • b (y - x)) := by
  have hn := integrable_near_integrand hh (nearPart_integrable_of hb) y
  have hfs := farPart_smooth hb.smooth
  have hf : Integrable (fun x => Heat.kernel h x • farPart b (y - x)) := by
    refine (Heat.kernel_integrable hh).smul_bdd (ε * farB 0)
      (hfs.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    have h1 := far_deriv_pointwise hb (k := 0) (by omega) (y - x)
    rw [norm_iteratedFDeriv_zero] at h1
    refine h1.trans (div_le_self (mul_nonneg hb.eps_nonneg (farB_nonneg 0)) ?_)
    exact one_le_pow₀ (by linarith [norm_nonneg (y - x)])
  refine (hn.add hf).congr (Eventually.of_forall fun x => ?_)
  simp only [Pi.add_apply, ← smul_add, nearPart_add_farPart]

theorem average_eq_near_add_far {h : ℝ} (hh : 0 < h) {b : SpatialField} {ε : ℝ}
    (hb : InvDist b ε) :
    Heat.average h b = Heat.average h (nearPart b) + Heat.average h (farPart b) := by
  funext y
  have hfs := farPart_smooth hb.smooth
  have hf : Integrable (fun x => Heat.kernel h x • farPart b (y - x)) := by
    refine (Heat.kernel_integrable hh).smul_bdd (ε * farB 0)
      (hfs.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    have h1 := far_deriv_pointwise hb (k := 0) (by omega) (y - x)
    rw [norm_iteratedFDeriv_zero] at h1
    refine h1.trans (div_le_self (mul_nonneg hb.eps_nonneg (farB_nonneg 0)) ?_)
    exact one_le_pow₀ (by linarith [norm_nonneg (y - x)])
  simp only [Heat.average, Pi.add_apply]
  rw [← integral_add (integrable_near_integrand hh (nearPart_integrable_of hb) y) hf]
  congr 1
  funext x
  rw [← smul_add, nearPart_add_farPart]

/-- **Heat smoothing with constants** (tex lines 274–281, near/far splitting): for `h > 0` there
are constants `Q_n` such that every `InvDist b ε` field has `e^{hΔ}b ∈ C²` and
`‖D^n e^{hΔ} b (y)‖ ≤ ε Q_n (1 + |y|)^{-1-n}` for `n ≤ 2`. -/
theorem heat_smoothing {h : ℝ} (hh : 0 < h) :
    ∃ Q : ℕ → ℝ, (∀ n, 0 ≤ Q n) ∧ ∀ (b : SpatialField) (ε : ℝ), InvDist b ε →
      ContDiff ℝ 2 (Heat.average h b) ∧
      ∀ n : ℕ, n ≤ 2 → ∀ y : Space,
        ‖iteratedFDeriv ℝ n (Heat.average h b) y‖ ≤ ε * Q n / (1 + ‖y‖) ^ (n + 1) := by
  choose Qn hQn0 hQn using fun n => near_deriv_bound hh n
  have hfQ0 : ∀ n, 0 ≤ farQ h n := fun n =>
    mul_nonneg (farB_nonneg n) (integral_nonneg fun x =>
      mul_nonneg (Heat.kernel_nonneg hh x) (by positivity))
  refine ⟨fun n => Qn n + farQ h n, fun n => add_nonneg (hQn0 n) (hfQ0 n),
    fun b ε hb => ?_⟩
  have hnear := nearPart_integrable_of hb
  have hfs := farPart_smooth hb.smooth
  have hfb := farPart_bddUpTo hb
  have hA : ∀ n : ℕ, ContDiff ℝ n (Heat.average h (nearPart b)) := fun n =>
    (average_nearPart_contDiff hh hnear n).1
  have hB : ∀ n : ℕ, n ≤ 2 → ContDiff ℝ n (Heat.average h (farPart b)) := fun n hn =>
    (average_farPart_upTo hh hfs hfb hn).1
  rw [average_eq_near_add_far hh hb]
  refine ⟨(hA 2).add (hB 2 le_rfl), fun n hn y => ?_⟩
  rw [iteratedFDeriv_add_apply (hA n).contDiffAt (hB n hn).contDiffAt]
  refine (norm_add_le _ _).trans ?_
  have h1 := hQn n b ε hb y
  have h2 := far_deriv_bound hh hn hb y
  calc ‖iteratedFDeriv ℝ n (Heat.average h (nearPart b)) y‖ +
        ‖iteratedFDeriv ℝ n (Heat.average h (farPart b)) y‖
      ≤ ε * Qn n / (1 + ‖y‖) ^ (n + 1) + ε * farQ h n / (1 + ‖y‖) ^ (n + 1) := add_le_add h1 h2
    _ = ε * (Qn n + farQ h n) / (1 + ‖y‖) ^ (n + 1) := by ring

end UnforcedLeray.HeatProfileReg
