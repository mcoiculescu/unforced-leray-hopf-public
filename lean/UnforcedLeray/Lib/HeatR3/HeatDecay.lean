import UnforcedLeray.Lib.HeatR3.Decay
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Heat decay for the scale-invariant class (INF04 T9, `InvDistClass.heat_decay`)


bypass BP3. For `u` in `𝒦₂(C)` (`|D^i u(x)| ≤ C|x|^{-1-i}`, `i ≤ 2`, `x ≠ 0`):

`|D^j e^{tΔ}u(x)| ≤ K (|x| + √t)^{-1-j}`,   `j ≤ 2`, `t > 0`,

with `K` depending only on `C` (B0710, tex 275–278; B0722, tex 468–491).

Proof (BP3). At heat time `1`, split `v = χv + (v - χv)` with a fixed bump `χ` (`= 1` on
`B̄(0,1)`, supported in `B(0,2)`):
* the near part `χv` is compactly supported with `|χv| ≤ C|x|^{-1}`; the kernel-side bound
  `|D^j e^{Δ}(χv)(y)| ≤ ∫ |D^jG_1(y - z)| |χv(z)| dz` and the weight transfer give
  `≤ K₁(1 + |y|)^{-1-j}`;
* the far part `v - χv` is `C²` on `ℝ³` with `|D^i(v - χv)(z)| ≤ K₂(1 + |z|)^{-1-i}`; derivatives
  pass through the heat flow (`iteratedFDeriv_average`) and the weighted bound
  (`norm_average_le_weight`, Peetre) gives `≤ K₃(1 + |y|)^{-1-j}`.
The class is invariant under `u ↦ λu(λ·)` with the same constant (`InvDistClass.dilate`), and
`e^{tΔ}u(x) = λ^{-1}e^{Δ}[u_λ](x/λ)` with `λ = √t` (`average_dilate'`), which transports the
estimate from `t = 1` to every `t > 0`.
-/

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace UnforcedLeray.Heat

open MeasureTheory Filter Set Topology
open scoped ENNReal ContDiff
open UnforcedLeray.Gaussian (Euc gaussKernel)

/-! ### The fixed cutoff -/

/-- The bump `= 1` on `B̄(0,1)`, supported in `B(0,2)`. -/
def cutBump : ContDiffBump (0 : Space) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The cutoff function `χ`. -/
def cut (y : Space) : ℝ := cutBump y

theorem contDiff_cut : ContDiff ℝ ∞ cut := cutBump.contDiff

theorem cut_nonneg (y : Space) : 0 ≤ cut y := cutBump.nonneg

theorem cut_le_one (y : Space) : cut y ≤ 1 := cutBump.le_one

theorem contDiff_cut_two : ContDiff ℝ 2 cut := by
  simpa using contDiff_infty.mp contDiff_cut 2

theorem cut_eq_one {y : Space} (hy : ‖y‖ ≤ 1) : cut y = 1 :=
  cutBump.one_of_mem_closedBall (by simpa [cutBump] using hy)

theorem cut_eq_zero {y : Space} (hy : 2 ≤ ‖y‖) : cut y = 0 :=
  cutBump.zero_of_le_dist (by simpa [cutBump, dist_zero_right] using hy)

theorem cut_deriv_bound (i : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ y, ‖iteratedFDeriv ℝ i cut y‖ ≤ B := by
  have hc : Continuous (iteratedFDeriv ℝ i cut) :=
    contDiff_cut.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  obtain ⟨B, hB⟩ := hc.bounded_above_of_compact_support
    ((cutBump.hasCompactSupport (E := Space)).iteratedFDeriv i)
  exact ⟨max B 0, le_max_right _ _, fun y => (hB y).trans (le_max_left _ _)⟩

theorem iteratedFDeriv_cut_eq_zero (i : ℕ) {y : Space} (hy : 2 < ‖y‖) :
    iteratedFDeriv ℝ i cut y = 0 := by
  have h : cut =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
    have : {z : Space | 2 < ‖z‖} ∈ 𝓝 y :=
      (isOpen_lt continuous_const continuous_norm).mem_nhds hy
    filter_upwards [this] with z hz
    exact cut_eq_zero hz.le
  rw [(h.iteratedFDeriv (𝕜 := ℝ) i).eq_of_nhds, iteratedFDeriv_fun_zero]
  rfl

/-! ### Elementary weight inequalities -/

theorem rpow_neg_le_two_pow_mul {r : ℝ} (hr : 1 ≤ r) (n : ℕ) :
    r ^ (-(n : ℝ)) ≤ 2 ^ n * (1 + r) ^ (-(n : ℝ)) := by
  have hr0 : 0 < r := by linarith
  rw [Real.rpow_neg hr0.le, Real.rpow_neg (by linarith), Real.rpow_natCast, Real.rpow_natCast,
    ← div_eq_mul_inv]
  rw [inv_eq_one_div, div_le_div_iff₀ (pow_pos hr0 n) (pow_pos (by linarith) n), one_mul]
  calc (1 + r) ^ n ≤ (2 * r) ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
    _ = 2 ^ n * r ^ n := mul_pow _ _ _

theorem one_le_three_pow_mul {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 2) (n : ℕ) :
    1 ≤ 3 ^ n * (1 + r) ^ (-(n : ℝ)) := by
  rw [Real.rpow_neg (by linarith), Real.rpow_natCast, ← div_eq_mul_inv,
    le_div_iff₀ (pow_pos (by linarith) n), one_mul]
  exact pow_le_pow_left₀ (by linarith) (by linarith) n

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- `|D^i v(x)| ≤ C|x|^{-1-i}` with the exponent as a natural cast. -/
theorem InvDistClass.bound' {C : ℝ} {v : Space → E} (hv : InvDistClass 2 C v) {i : ℕ}
    (hi : i ≤ 2) {x : Space} (hx : x ≠ 0) :
    ‖iteratedFDeriv ℝ i v x‖ ≤ C * ‖x‖ ^ (-((1 + i : ℕ) : ℝ)) := by
  have h := hv.bound i hi x hx
  simpa only [Nat.cast_add, Nat.cast_one] using h

theorem InvDistClass.const_nonneg {C : ℝ} {v : Space → E} (hv : InvDistClass 2 C v) :
    0 ≤ C := by
  set x : Space := EuclideanSpace.single 0 1
  have hx : x ≠ 0 := by simp [x]
  have h := hv.bound 0 (Nat.zero_le 2) x hx
  have hpos : 0 < ‖x‖ ^ (-(1 + ((0 : ℕ) : ℝ))) := Real.rpow_pos_of_pos (norm_pos_iff.mpr hx) _
  exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans h) hpos

theorem InvDistClass.norm_le {C : ℝ} {v : Space → E} (hv : InvDistClass 2 C v) {x : Space}
    (hx : x ≠ 0) : ‖v x‖ ≤ C * ‖x‖⁻¹ := by
  have h := hv.bound 0 (Nat.zero_le 2) x hx
  rwa [norm_iteratedFDeriv_zero, Nat.cast_zero, add_zero, Real.rpow_neg_one] at h

/-! ### The near part `χv` -/

theorem integrableOn_inv_norm_closedBall_two :
    IntegrableOn (fun y : Space => ‖y‖ ^ (-(1 : ℝ))) (Metric.closedBall (0 : Space) 2) := by
  have hdim : Module.finrank ℝ Space = 3 := by simp [Space]
  have hloc : LocallyIntegrable (fun y : Space => ‖y‖ ^ (-(1 : ℝ))) volume := by
    refine locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1) (by rw [hdim]; norm_num)
      (by rw [hdim]; norm_num) (Eventually.of_forall fun y => ?_) ?_
    · rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    · exact (continuous_norm.measurable.pow_const _).aestronglyMeasurable
  exact hloc.integrableOn_isCompact (isCompact_closedBall 0 2)

/-- The constant of the near part. -/
def nearConst (C : ℝ) : ℝ :=
  27 * C * ∫ y in Metric.closedBall (0 : Space) 2, ‖y‖ ^ (-(1 : ℝ))

theorem heatNear_bound {C : ℝ} {j : ℕ} (hj : j ≤ 2) :
    ∃ K : ℝ, ∀ v : Space → E, InvDistClass 2 C v → ∀ y : Space,
      ‖iteratedFDeriv ℝ j (average 1 (fun z => cut z • v z)) y‖ ≤
        K * (1 + ‖y‖) ^ (-((1 + j : ℕ) : ℝ)) := by
  obtain ⟨C', hC'0, hC'⟩ := norm_iteratedFDeriv_gaussKernel_le_weight 3 j one_pos
    (m := ((1 + j : ℕ) : ℝ)) (by positivity)
  refine ⟨C' * nearConst C, fun v hv y => ?_⟩
  have hC := hv.const_nonneg
  have hadm : HeatAdmissible (fun z => cut z • v z) := by
    refine HeatAdmissible.of_inv_bound ?_ (C := C) fun x hx => ?_
    · have hm := hv.heatAdmissible.1
      exact (contDiff_cut.continuous.aestronglyMeasurable).smul hm
    · rw [norm_smul, Real.norm_of_nonneg (cut_nonneg x)]
      exact (mul_le_of_le_one_left (norm_nonneg _) (cut_le_one x)).trans (hv.norm_le hx)
  refine (norm_iteratedFDeriv_average_le_kernel hadm one_pos j y).trans ?_
  set g : Space → ℝ := fun z => 27 * C *
    (Metric.closedBall (0 : Space) 2).indicator (fun z => ‖z‖ ^ (-(1 : ℝ))) z with hg
  have hgi : Integrable g :=
    (integrableOn_inv_norm_closedBall_two.integrable_indicator
      Metric.isClosed_closedBall.measurableSet).const_mul _
  have hbound : ∀ᵐ z ∂(volume : Measure Space),
      ‖iteratedFDeriv ℝ j (kernel 1) (y - z)‖ * ‖cut z • v z‖ ≤
        C' * (1 + ‖y‖) ^ (-((1 + j : ℕ) : ℝ)) * g z := by
    filter_upwards [Measure.ae_ne volume (0 : Space)] with z hz
    have hK : ‖iteratedFDeriv ℝ j (kernel 1) (y - z)‖ ≤
        C' * ((1 + ‖z‖) ^ ((1 + j : ℕ) : ℝ) * (1 + ‖y‖) ^ (-((1 + j : ℕ) : ℝ))) := by
      rw [← Gaussian.gaussKernel_three_eq]
      refine (hC' (y - z)).trans (mul_le_mul_of_nonneg_left ?_ hC'0.le)
      have h := one_add_norm_sub_rpow_neg_le (m := ((1 + j : ℕ) : ℝ)) (by positivity) z y
      rwa [norm_sub_rev] at h
    by_cases hz2 : 2 ≤ ‖z‖
    · rw [cut_eq_zero hz2, zero_smul, norm_zero, mul_zero]
      exact mul_nonneg (mul_nonneg hC'0.le (Real.rpow_nonneg (by positivity) _))
        (mul_nonneg (mul_nonneg (by norm_num) hC)
          (Set.indicator_nonneg (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _) _))
    · push_neg at hz2
      have hmem : z ∈ Metric.closedBall (0 : Space) 2 := by
        simpa using hz2.le
      have hvz : ‖cut z • v z‖ ≤ C * ‖z‖ ^ (-(1 : ℝ)) := by
        rw [norm_smul, Real.norm_of_nonneg (cut_nonneg z), Real.rpow_neg_one]
        exact (mul_le_of_le_one_left (norm_nonneg _) (cut_le_one z)).trans (hv.norm_le hz)
      have h27 : (1 + ‖z‖) ^ ((1 + j : ℕ) : ℝ) ≤ 27 := by
        rw [Real.rpow_natCast]
        calc (1 + ‖z‖) ^ (1 + j) ≤ 3 ^ (1 + j) :=
              pow_le_pow_left₀ (by positivity) (by linarith) _
          _ ≤ 3 ^ 3 := pow_le_pow_right₀ (by norm_num) (by omega)
          _ = 27 := by norm_num
      rw [hg]
      simp only [Set.indicator_of_mem hmem]
      have hw : 0 ≤ (1 + ‖y‖) ^ (-((1 + j : ℕ) : ℝ)) := Real.rpow_nonneg (by positivity) _
      calc ‖iteratedFDeriv ℝ j (kernel 1) (y - z)‖ * ‖cut z • v z‖
          ≤ C' * ((1 + ‖z‖) ^ ((1 + j : ℕ) : ℝ) * (1 + ‖y‖) ^ (-((1 + j : ℕ) : ℝ))) *
              (C * ‖z‖ ^ (-(1 : ℝ))) := by gcongr
        _ ≤ C' * (27 * (1 + ‖y‖) ^ (-((1 + j : ℕ) : ℝ))) * (C * ‖z‖ ^ (-(1 : ℝ))) := by
            gcongr
        _ = C' * (1 + ‖y‖) ^ (-((1 + j : ℕ) : ℝ)) * (27 * C * ‖z‖ ^ (-(1 : ℝ))) := by ring
  calc ∫ z : Space, ‖iteratedFDeriv ℝ j (kernel 1) (y - z)‖ * ‖cut z • v z‖
      ≤ ∫ z : Space, C' * (1 + ‖y‖) ^ (-((1 + j : ℕ) : ℝ)) * g z :=
        integral_mono_of_nonneg (Eventually.of_forall fun z =>
          mul_nonneg (norm_nonneg _) (norm_nonneg _)) (hgi.const_mul _) hbound
    _ = C' * nearConst C * (1 + ‖y‖) ^ (-((1 + j : ℕ) : ℝ)) := by
        rw [integral_const_mul, hg, integral_const_mul, integral_indicator
          Metric.isClosed_closedBall.measurableSet, nearConst]
        ring

/-! ### The far part `v - χv` -/

/-- The Leibniz constant of `χv` on `|z| ≥ 1`. -/
theorem cut_smul_deriv_bound (C : ℝ) {i : ℕ} (hi : i ≤ 2) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ v : Space → E, InvDistClass 2 C v → ∀ z : Space, 1 ≤ ‖z‖ →
      ‖iteratedFDeriv ℝ i (fun z => cut z • v z) z‖ ≤ L := by
  choose B hB0 hB using cut_deriv_bound
  refine ⟨∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * B l * |C|,
    Finset.sum_nonneg fun l _ => mul_nonneg (mul_nonneg (by positivity) (hB0 l)) (abs_nonneg C),
    fun v hv z hz => ?_⟩
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; linarith
  have hopen : IsOpen ({0}ᶜ : Set Space) := isOpen_compl_singleton
  have hmem : z ∈ ({0}ᶜ : Set Space) := hz0
  have hcut : ContDiffOn ℝ 2 cut {0}ᶜ := contDiff_cut_two.contDiffOn
  have hL := norm_iteratedFDerivWithin_smul_le hcut hv.smooth hopen.uniqueDiffOn hmem
    (n := i) (by exact_mod_cast hi)
  rw [iteratedFDerivWithin_of_isOpen i hopen hmem] at hL
  refine hL.trans (Finset.sum_le_sum fun l hl => ?_)
  rw [iteratedFDerivWithin_of_isOpen l hopen hmem,
    iteratedFDerivWithin_of_isOpen (i - l) hopen hmem]
  have hil : i - l ≤ 2 := by omega
  have hv' := hv.bound' hil hz0
  have hzpow : ‖z‖ ^ (-((1 + (i - l) : ℕ) : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hz (neg_nonpos.mpr (Nat.cast_nonneg _))
  have hvl : ‖iteratedFDeriv ℝ (i - l) v z‖ ≤ |C| := by
    refine hv'.trans ?_
    calc C * ‖z‖ ^ (-((1 + (i - l) : ℕ) : ℝ)) ≤ |C| * ‖z‖ ^ (-((1 + (i - l) : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (norm_nonneg _) _)
      _ ≤ |C| * 1 := by gcongr
      _ = |C| := mul_one _
  calc (i.choose l : ℝ) * ‖iteratedFDeriv ℝ l cut z‖ * ‖iteratedFDeriv ℝ (i - l) v z‖
      ≤ (i.choose l : ℝ) * B l * |C| :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hB l z) (by positivity)) hvl (norm_nonneg _)
          (mul_nonneg (by positivity) (hB0 l))

theorem iteratedFDeriv_cut_smul_eq_zero {v : Space → E} (i : ℕ) {z : Space} (hz : 2 < ‖z‖) :
    iteratedFDeriv ℝ i (fun z => cut z • v z) z = 0 := by
  have h : (fun z => cut z • v z) =ᶠ[𝓝 z] fun _ => (0 : E) := by
    have : {w : Space | 2 < ‖w‖} ∈ 𝓝 z :=
      (isOpen_lt continuous_const continuous_norm).mem_nhds hz
    filter_upwards [this] with w hw
    rw [cut_eq_zero hw.le, zero_smul]
  rw [(h.iteratedFDeriv (𝕜 := ℝ) i).eq_of_nhds, iteratedFDeriv_fun_zero]
  rfl

/-- The far part vanishes on the unit ball. -/
theorem far_eq_zero {v : Space → E} {z : Space} (hz : ‖z‖ ≤ 1) : v z - cut z • v z = 0 := by
  rw [cut_eq_one hz, one_smul, sub_self]

theorem contDiffAt_far {C : ℝ} {v : Space → E} (hv : InvDistClass 2 C v) (z : Space) :
    ContDiffAt ℝ 2 (fun z => v z - cut z • v z) z := by
  by_cases hz : z = 0
  · subst hz
    have h : (fun z => v z - cut z • v z) =ᶠ[𝓝 (0 : Space)] fun _ => (0 : E) := by
      filter_upwards [Metric.ball_mem_nhds (0 : Space) one_pos] with w hw
      exact far_eq_zero (by simpa using (Metric.mem_ball.mp hw).le)
    exact contDiffAt_const.congr_of_eventuallyEq h
  · have hopen : IsOpen ({0}ᶜ : Set Space) := isOpen_compl_singleton
    have hvz : ContDiffAt ℝ 2 v z := hv.smooth.contDiffAt (hopen.mem_nhds hz)
    exact hvz.sub (contDiff_cut_two.contDiffAt.smul hvz)

theorem contDiff_far {C : ℝ} {v : Space → E} (hv : InvDistClass 2 C v) :
    ContDiff ℝ 2 (fun z => v z - cut z • v z) :=
  contDiff_iff_contDiffAt.mpr (contDiffAt_far hv)

theorem far_deriv_bound (C : ℝ) {i : ℕ} (hi : i ≤ 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v : Space → E, InvDistClass 2 C v → ∀ z : Space,
      ‖iteratedFDeriv ℝ i (fun z => v z - cut z • v z) z‖ ≤
        K * (1 + ‖z‖) ^ (-((1 + i : ℕ) : ℝ)) := by
  obtain ⟨L, hL0, hL⟩ := cut_smul_deriv_bound (E := E) C hi
  refine ⟨8 * |C| + 27 * L, by positivity, fun v hv z => ?_⟩
  have hw : 0 ≤ (1 + ‖z‖) ^ (-((1 + i : ℕ) : ℝ)) := Real.rpow_nonneg (by positivity) _
  by_cases hz1 : ‖z‖ < 1
  · have h : (fun z => v z - cut z • v z) =ᶠ[𝓝 z] fun _ => (0 : E) := by
      have : {w : Space | ‖w‖ < 1} ∈ 𝓝 z :=
        (isOpen_lt continuous_norm continuous_const).mem_nhds hz1
      filter_upwards [this] with w hw
      exact far_eq_zero hw.le
    rw [(h.iteratedFDeriv (𝕜 := ℝ) i).eq_of_nhds, iteratedFDeriv_fun_zero]
    simp only [Pi.zero_apply, norm_zero]
    positivity
  push_neg at hz1
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz1; linarith
  have hopen : IsOpen ({0}ᶜ : Set Space) := isOpen_compl_singleton
  have hvz : ContDiffAt ℝ i v z :=
    (hv.smooth.contDiffAt (hopen.mem_nhds hz0)).of_le (by exact_mod_cast hi)
  have hwz : ContDiffAt ℝ i (fun z => cut z • v z) z :=
    (contDiff_cut.of_le (by exact_mod_cast le_top)).contDiffAt.smul hvz
  have hsub : iteratedFDeriv ℝ i (fun z => v z - cut z • v z) z =
      iteratedFDeriv ℝ i v z - iteratedFDeriv ℝ i (fun z => cut z • v z) z :=
    iteratedFDeriv_sub_apply (f := v) (g := fun z => cut z • v z) hvz hwz
  rw [hsub]
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖iteratedFDeriv ℝ i v z‖ ≤ 8 * |C| * (1 + ‖z‖) ^ (-((1 + i : ℕ) : ℝ)) := by
    refine (hv.bound' hi hz0).trans ?_
    have h2 := rpow_neg_le_two_pow_mul hz1 (1 + i)
    have h8 : (2 : ℝ) ^ (1 + i) ≤ 8 := by
      calc (2 : ℝ) ^ (1 + i) ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) (by omega)
        _ = 8 := by norm_num
    calc C * ‖z‖ ^ (-((1 + i : ℕ) : ℝ)) ≤ |C| * ‖z‖ ^ (-((1 + i : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (norm_nonneg _) _)
      _ ≤ |C| * (2 ^ (1 + i) * (1 + ‖z‖) ^ (-((1 + i : ℕ) : ℝ))) := by gcongr
      _ ≤ |C| * (8 * (1 + ‖z‖) ^ (-((1 + i : ℕ) : ℝ))) := by gcongr
      _ = 8 * |C| * (1 + ‖z‖) ^ (-((1 + i : ℕ) : ℝ)) := by ring
  have h2 : ‖iteratedFDeriv ℝ i (fun z => cut z • v z) z‖ ≤
      27 * L * (1 + ‖z‖) ^ (-((1 + i : ℕ) : ℝ)) := by
    by_cases hz2 : 2 < ‖z‖
    · rw [iteratedFDeriv_cut_smul_eq_zero i hz2, norm_zero]; positivity
    · push_neg at hz2
      have h3 := one_le_three_pow_mul (norm_nonneg z) hz2 (1 + i)
      have h27 : (3 : ℝ) ^ (1 + i) ≤ 27 := by
        calc (3 : ℝ) ^ (1 + i) ≤ 3 ^ 3 := pow_le_pow_right₀ (by norm_num) (by omega)
          _ = 27 := by norm_num
      calc ‖iteratedFDeriv ℝ i (fun z => cut z • v z) z‖ ≤ L := hL v hv z hz1
        _ ≤ L * (3 ^ (1 + i) * (1 + ‖z‖) ^ (-((1 + i : ℕ) : ℝ))) := le_mul_of_one_le_right hL0 h3
        _ ≤ L * (27 * (1 + ‖z‖) ^ (-((1 + i : ℕ) : ℝ))) := by gcongr
        _ = 27 * L * (1 + ‖z‖) ^ (-((1 + i : ℕ) : ℝ)) := by ring
  linarith

theorem heatFar_bound (C : ℝ) {j : ℕ} (hj : j ≤ 2) :
    ∃ K : ℝ, ∀ v : Space → E, InvDistClass 2 C v → ∀ y : Space,
      ‖iteratedFDeriv ℝ j (average 1 (fun z => v z - cut z • v z)) y‖ ≤
        K * (1 + ‖y‖) ^ (-((1 + j : ℕ) : ℝ)) := by
  have hall : ∀ i ≤ 2, ∃ K : ℝ, 0 ≤ K ∧ ∀ v : Space → E, InvDistClass 2 C v → ∀ z : Space,
      ‖iteratedFDeriv ℝ i (fun z => v z - cut z • v z) z‖ ≤
        K * (1 + ‖z‖) ^ (-((1 + i : ℕ) : ℝ)) := fun i hi => far_deriv_bound C hi
  choose! K hK0 hK using hall
  set M := K 0 + K 1 + K 2 with hM
  refine ⟨momentConst |(-((1 + j : ℕ) : ℝ))| 1 * K j, fun v hv y => ?_⟩
  have hbd : ∀ k ≤ 2, ∀ z, ‖iteratedFDeriv ℝ k (fun z => v z - cut z • v z) z‖ ≤ M := by
    intro k hk z
    have h := hK k hk v hv z
    have hw : (1 + ‖z‖) ^ (-((1 + k : ℕ) : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by simp) (neg_nonpos.mpr (Nat.cast_nonneg _))
    have hKk : K k ≤ M := by
      interval_cases k <;> simp only [hM] <;> linarith [hK0 0 (by norm_num), hK0 1 (by norm_num),
        hK0 2 (by norm_num)]
    calc _ ≤ K k * (1 + ‖z‖) ^ (-((1 + k : ℕ) : ℝ)) := h
      _ ≤ K k * 1 := by gcongr; exact hK0 k hk
      _ ≤ M := by rw [mul_one]; exact hKk
  rw [iteratedFDeriv_average one_pos (contDiff_far hv) hbd j hj]
  exact norm_average_le_weight one_pos le_rfl (hK j hj v hv) y

/-! ### The decay estimate -/

/-- **INF04 T9, heat time one.** For `v ∈ 𝒦₂(C)` and `j ≤ 2`:
`|D^j e^{Δ}v(y)| ≤ K (1 + |y|)^{-1-j}`, with `K` depending only on `C` and `j`. -/
theorem InvDistClass.heat_decay_one (C : ℝ) {j : ℕ} (hj : j ≤ 2) :
    ∃ K : ℝ, ∀ v : Space → E, InvDistClass 2 C v → ∀ y : Space,
      ‖iteratedFDeriv ℝ j (average 1 v) y‖ ≤ K * (1 + ‖y‖) ^ (-((1 + j : ℕ) : ℝ)) := by
  obtain ⟨K₁, hK₁⟩ := heatNear_bound (E := E) (C := C) hj
  obtain ⟨K₂, hK₂⟩ := heatFar_bound (E := E) C hj
  refine ⟨K₁ + K₂, fun v hv y => ?_⟩
  have hadm := hv.heatAdmissible
  have hnear : HeatAdmissible (fun z => cut z • v z) := by
    refine HeatAdmissible.of_inv_bound ?_ (C := C) fun x hx => ?_
    · exact (contDiff_cut.continuous.aestronglyMeasurable).smul hadm.1
    · rw [norm_smul, Real.norm_of_nonneg (cut_nonneg x)]
      exact (mul_le_of_le_one_left (norm_nonneg _) (cut_le_one x)).trans (hv.norm_le hx)
  have hfar : HeatAdmissible (fun z => v z - cut z • v z) := by
    have h := hadm.sub hnear
    exact h
  have hsplit : average 1 v =
      average 1 (fun z => cut z • v z) + average 1 (fun z => v z - cut z • v z) := by
    rw [← average_add' hnear hfar one_pos]
    congr 1
    funext z
    simp only [Pi.add_apply, add_sub_cancel]
  rw [hsplit, iteratedFDeriv_add_apply ((contDiff_average hnear one_pos).contDiffAt.of_le
    (by exact_mod_cast le_top)) ((contDiff_average hfar one_pos).contDiffAt.of_le
    (by exact_mod_cast le_top))]
  refine (norm_add_le _ _).trans ?_
  have h1 := hK₁ v hv y
  have h2 := hK₂ v hv y
  linarith

/-- **INF04 T9 `InvDistClass.heat_decay`** (BP3; B0710, B0722). For `u ∈ 𝒦₂(C)`, `j ≤ 2`:
there is `K = K(C, j)` with `|D^j e^{tΔ}u(x)| ≤ K (|x| + √t)^{-1-j}` for every `t > 0` and
every `x`, uniformly over the class. -/
theorem InvDistClass.heat_decay (C : ℝ) {j : ℕ} (hj : j ≤ 2) :
    ∃ K : ℝ, ∀ u : Space → E, InvDistClass 2 C u → ∀ t : ℝ, 0 < t → ∀ x : Space,
      ‖iteratedFDeriv ℝ j (average t u) x‖ ≤
        K * (‖x‖ + Real.sqrt t) ^ (-((1 + j : ℕ) : ℝ)) := by
  obtain ⟨K, hK⟩ := InvDistClass.heat_decay_one (E := E) C hj
  refine ⟨K, fun u hu t ht x => ?_⟩
  set lam := Real.sqrt t with hlam
  have hl0 : 0 < lam := Real.sqrt_pos.mpr ht
  have hl2 : lam ^ 2 * 1 = t := by rw [mul_one]; exact Real.sq_sqrt ht.le
  set v : Space → E := fun y => lam • u (lam • y) with hv
  have hvc : InvDistClass 2 C v := hu.dilate hl0
  have hdil : average 1 v = fun y => lam • average t u (lam • y) := by
    rw [hv, average_dilate' hl0 one_pos, hl2]
  have hrep : average t u = fun x => lam⁻¹ • average 1 v (lam⁻¹ • x) := by
    funext x
    rw [hdil]
    simp only [smul_smul, inv_mul_cancel₀ hl0.ne', mul_inv_cancel₀ hl0.ne', one_smul]
  rw [hrep, Gaussian.iteratedFDeriv_comp_smul j (average 1 v) lam⁻¹ lam⁻¹ x, norm_smul,
    Real.norm_of_nonneg (by positivity)]
  have h1 := hK v hvc (lam⁻¹ • x)
  rw [norm_smul, Real.norm_of_nonneg (by positivity)] at h1
  have hK0 : 0 ≤ K := by
    have := (norm_nonneg _).trans h1
    exact nonneg_of_mul_nonneg_left this (Real.rpow_pos_of_pos (by positivity) _)
  have heq : lam⁻¹ * lam⁻¹ ^ j * (1 + lam⁻¹ * ‖x‖) ^ (-((1 + j : ℕ) : ℝ)) =
      (‖x‖ + lam) ^ (-((1 + j : ℕ) : ℝ)) := by
    have hb : 1 + lam⁻¹ * ‖x‖ = lam⁻¹ * (‖x‖ + lam) := by field_simp; ring
    have hA : 0 < ‖x‖ + lam := by positivity
    rw [Real.rpow_neg (by positivity), Real.rpow_neg hA.le, Real.rpow_natCast, Real.rpow_natCast,
      hb, mul_pow, pow_add, pow_one]
    field_simp
  calc lam⁻¹ * lam⁻¹ ^ j * ‖iteratedFDeriv ℝ j (average 1 v) (lam⁻¹ • x)‖
      ≤ lam⁻¹ * lam⁻¹ ^ j * (K * (1 + lam⁻¹ * ‖x‖) ^ (-((1 + j : ℕ) : ℝ))) := by gcongr
    _ = K * (lam⁻¹ * lam⁻¹ ^ j * (1 + lam⁻¹ * ‖x‖) ^ (-((1 + j : ℕ) : ℝ))) := by ring
    _ = K * (‖x‖ + lam) ^ (-((1 + j : ℕ) : ℝ)) := by rw [heq]

end UnforcedLeray.Heat
