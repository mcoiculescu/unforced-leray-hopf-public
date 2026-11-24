import UnforcedLeray.Lib.HeatR3.Bounded
import UnforcedLeray.Lib.Gaussian.IteratedDeriv
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Heat-admissible data on `ℝ³`: polynomially weighted integrable fields (INF04 T8)


Covers the heat integrals of non-`L²` data in units B0576, B0697, B0707, B0718 and B1028:
`|x|^{-1}`-type data (the DSS datum, tex 5205–5216), `L^p` data and their sums.

`HeatAdmissible f` asks that `f` be a.e. strongly measurable and that `(1 + |y|)^{-m} f(y)` be
integrable for some `m ∈ ℕ`. Every Gaussian integral `∫ G_θ(x - y) f(y) dy` of such an `f` then
converges absolutely (Gaussian decay beats any polynomial), at every `x` and every `θ > 0`.

Main results:
* `one_add_norm_sub_rpow_neg_le` (weight transfer), `norm_iteratedFDeriv_gaussKernel_le_weight`
  (`|D^n G_θ(z)| ≤ C (1 + |z|)^{-m}`);
* `HeatAdmissible`, `HeatAdmissible.of_memLp` (`1 ≤ p ≤ ∞`), `HeatAdmissible.of_inv_bound`
  (`|f(x)| ≤ C|x|^{-1}`), `HeatAdmissible.add`, `HeatAdmissible.smul`;
* `integrable_heat`: the heat integrand is integrable at every point;
* `average_add'`, `average_add_time'` (semigroup law at every point), `average_dilate'`.
-/

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace UnforcedLeray.Heat

open MeasureTheory Filter Set Topology
open scoped ENNReal
open UnforcedLeray.Gaussian (Euc gaussKernel)

/-! ### Weights -/

section Weights

variable {F : Type*} [SeminormedAddCommGroup F]

theorem one_add_norm_le_mul (x y : F) :
    1 + ‖y‖ ≤ (1 + ‖x‖) * (1 + ‖x - y‖) := by
  have h : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by
    calc ‖y‖ = ‖x - (x - y)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖x‖ + ‖x - y‖ := norm_sub_le _ _
  nlinarith [norm_nonneg x, norm_nonneg (x - y), mul_nonneg (norm_nonneg x) (norm_nonneg (x - y))]

/-- Weight transfer: `(1 + |x - y|)^{-m} ≤ (1 + |x|)^m (1 + |y|)^{-m}` for `m ≥ 0`. -/
theorem one_add_norm_sub_rpow_neg_le {m : ℝ} (hm : 0 ≤ m) (x y : F) :
    (1 + ‖x - y‖) ^ (-m) ≤ (1 + ‖x‖) ^ m * (1 + ‖y‖) ^ (-m) := by
  have ha : 0 < 1 + ‖x‖ := by positivity
  have hb : 0 < 1 + ‖x - y‖ := by positivity
  have hc : 0 < 1 + ‖y‖ := by positivity
  have h1 : (1 + ‖y‖) ^ m ≤ (1 + ‖x‖) ^ m * (1 + ‖x - y‖) ^ m := by
    rw [← Real.mul_rpow ha.le hb.le]
    exact Real.rpow_le_rpow hc.le (one_add_norm_le_mul x y) hm
  rw [Real.rpow_neg hb.le, Real.rpow_neg hc.le]
  have hA : 0 < (1 + ‖x - y‖) ^ m := Real.rpow_pos_of_pos hb m
  have hC : 0 < (1 + ‖y‖) ^ m := Real.rpow_pos_of_pos hc m
  rw [inv_le_iff_one_le_mul₀ hA]
  calc (1 : ℝ) = (1 + ‖y‖) ^ m * ((1 + ‖y‖) ^ m)⁻¹ := (mul_inv_cancel₀ hC.ne').symm
    _ ≤ ((1 + ‖x‖) ^ m * (1 + ‖x - y‖) ^ m) * ((1 + ‖y‖) ^ m)⁻¹ := by gcongr
    _ = (1 + ‖x‖) ^ m * ((1 + ‖y‖) ^ m)⁻¹ * (1 + ‖x - y‖) ^ m := by ring

end Weights

/-- `(1 + r)^m e^{-b r²}` is bounded on `r ≥ 0` (`m ≥ 0`, `b > 0`). -/
theorem one_add_rpow_mul_exp_le {m b : ℝ} (hm : 0 ≤ m) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 ≤ r → (1 + r) ^ m * Real.exp (-(b * r ^ 2)) ≤ C := by
  obtain ⟨C, hC0, hC⟩ := Gaussian.rpow_mul_exp_neg_mul_sq_le (m := m) (b := b / 2) hm
    (by positivity)
  refine ⟨Real.exp b * C, by positivity, fun r hr => ?_⟩
  have hexp : Real.exp (-(b * r ^ 2)) ≤ Real.exp b * Real.exp (-(b / 2 * (1 + r) ^ 2)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (r - 1)])
  calc (1 + r) ^ m * Real.exp (-(b * r ^ 2))
      ≤ (1 + r) ^ m * (Real.exp b * Real.exp (-(b / 2 * (1 + r) ^ 2))) := by
        gcongr
    _ = Real.exp b * ((1 + r) ^ m * Real.exp (-(b / 2 * (1 + r) ^ 2))) := by ring
    _ ≤ Real.exp b * C := by gcongr; exact hC (1 + r) (by linarith)

/-- **INF04 T2/T8.** Polynomial decay of every Gaussian derivative:
`‖D^n G_θ(z)‖ ≤ C (1 + |z|)^{-m}` for `θ > 0`, `m ≥ 0`, with `C = C(d, n, m, θ)`. -/
theorem norm_iteratedFDeriv_gaussKernel_le_weight (d n : ℕ) {θ : ℝ} (hθ : 0 < θ) {m : ℝ}
    (hm : 0 ≤ m) : ∃ C : ℝ, 0 < C ∧ ∀ z : Euc d,
      ‖iteratedFDeriv ℝ n (gaussKernel d θ) z‖ ≤ C * (1 + ‖z‖) ^ (-m) := by
  obtain ⟨C₁, hC₁, h₁⟩ := Gaussian.norm_iteratedFDeriv_gaussKernel_le d n
  obtain ⟨C₂, hC₂, h₂⟩ := one_add_rpow_mul_exp_le (m := m) (b := 1 / (8 * θ)) hm
    (by positivity)
  refine ⟨C₁ * θ ^ (-(((d : ℝ) + n) / 2)) * C₂, by positivity, fun z => ?_⟩
  have hpos : 0 < (1 + ‖z‖) ^ m := Real.rpow_pos_of_pos (by positivity) m
  have hz := h₂ ‖z‖ (norm_nonneg z)
  have he : Real.exp (-‖z‖ ^ 2 / (8 * θ)) = Real.exp (-(1 / (8 * θ) * ‖z‖ ^ 2)) := by
    congr 1; ring
  have hz' : Real.exp (-(1 / (8 * θ) * ‖z‖ ^ 2)) ≤ C₂ * (1 + ‖z‖) ^ (-m) := by
    rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv, le_div_iff₀ hpos]
    linarith [hz, mul_comm ((1 + ‖z‖) ^ m) (Real.exp (-(1 / (8 * θ) * ‖z‖ ^ 2)))]
  refine (h₁ hθ z).trans ?_
  rw [he]
  calc C₁ * θ ^ (-(((d : ℝ) + n) / 2)) * Real.exp (-(1 / (8 * θ) * ‖z‖ ^ 2))
      ≤ C₁ * θ ^ (-(((d : ℝ) + n) / 2)) * (C₂ * (1 + ‖z‖) ^ (-m)) := by gcongr
    _ = C₁ * θ ^ (-(((d : ℝ) + n) / 2)) * C₂ * (1 + ‖z‖) ^ (-m) := by ring

/-- Zeroth-order form: `G_θ(z) ≤ C (1 + |z|)^{-m}`. -/
theorem gaussKernel_le_weight (d : ℕ) {θ : ℝ} (hθ : 0 < θ) {m : ℝ} (hm : 0 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : Euc d, gaussKernel d θ z ≤ C * (1 + ‖z‖) ^ (-m) := by
  obtain ⟨C, hC, h⟩ := norm_iteratedFDeriv_gaussKernel_le_weight d 0 hθ hm
  refine ⟨C, hC, fun z => ?_⟩
  have := h z
  rwa [norm_iteratedFDeriv_zero, Real.norm_of_nonneg (Gaussian.gaussKernel_nonneg hθ z)] at this

/-! ### Admissible data -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **INF04 T8 `HeatAdmissible`.** `f` is a.e. strongly measurable and `(1 + |y|)^{-m} f(y)` is
integrable for some `m ∈ ℕ`: the class on which the Gaussian integral converges absolutely at
every point and every positive time (tex 5205–5216, B0697; B0576, B0707, B0718, B1028). -/
def HeatAdmissible (f : Space → E) : Prop :=
  AEStronglyMeasurable f volume ∧
    ∃ m : ℕ, Integrable (fun y : Space => (1 + ‖y‖) ^ (-(m : ℝ)) • f y)

theorem continuous_weight (m : ℝ) : Continuous fun y : Space => (1 + ‖y‖) ^ (-m) :=
  Continuous.rpow_const (f := fun y : Space => 1 + ‖y‖) (continuous_const.add continuous_norm)
    (fun y => Or.inl (by positivity))

/-- Raising the weight exponent keeps integrability. -/
theorem integrable_weight_mono {f : Space → E} (hf : AEStronglyMeasurable f volume) {m m' : ℕ}
    (hmm' : m ≤ m') (hi : Integrable (fun y : Space => (1 + ‖y‖) ^ (-(m : ℝ)) • f y)) :
    Integrable (fun y : Space => (1 + ‖y‖) ^ (-(m' : ℝ)) • f y) := by
  refine hi.norm.mono' ?_ (Eventually.of_forall fun y => ?_)
  · exact (continuous_weight _).aestronglyMeasurable.smul hf
  · have h1 : 1 ≤ 1 + ‖y‖ := by simp
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _),
      Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    gcongr

theorem HeatAdmissible.add {f g : Space → E} (hf : HeatAdmissible f) (hg : HeatAdmissible g) :
    HeatAdmissible (f + g) := by
  obtain ⟨hfm, m, hm⟩ := hf
  obtain ⟨hgm, n, hn⟩ := hg
  refine ⟨hfm.add hgm, max m n, ?_⟩
  have h1 := integrable_weight_mono hfm (le_max_left m n) hm
  have h2 := integrable_weight_mono hgm (le_max_right m n) hn
  exact (h1.add h2).congr (Eventually.of_forall fun y => by
    simp only [Pi.add_apply, smul_add])

theorem HeatAdmissible.smul {f : Space → E} (hf : HeatAdmissible f) (c : ℝ) :
    HeatAdmissible (c • f) := by
  obtain ⟨hfm, m, hm⟩ := hf
  refine ⟨hfm.const_smul c, m, ?_⟩
  exact (hm.smul c).congr (Eventually.of_forall fun y => by
    simp only [Pi.smul_apply]; rw [smul_comm])

theorem HeatAdmissible.neg {f : Space → E} (hf : HeatAdmissible f) : HeatAdmissible (-f) := by
  simpa using hf.smul (-1)

theorem HeatAdmissible.sub {f g : Space → E} (hf : HeatAdmissible f) (hg : HeatAdmissible g) :
    HeatAdmissible (f - g) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

theorem memLp_weight {q : ℝ≥0∞} (hq : 1 ≤ q) :
    MemLp (fun y : Space => (1 + ‖y‖) ^ (-(4 : ℝ))) q volume := by
  have hmeas : AEStronglyMeasurable (fun y : Space => (1 + ‖y‖) ^ (-(4 : ℝ))) volume :=
    (continuous_weight 4).aestronglyMeasurable
  rcases eq_or_ne q ∞ with rfl | hqt
  · refine memLp_top_of_bound hmeas 1 (Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by simp) (by norm_num)
  have hq0 : q ≠ 0 := (lt_of_lt_of_le zero_lt_one hq).ne'
  rw [← integrable_norm_rpow_iff hmeas hq0 hqt]
  have hqr : 1 ≤ q.toReal := by
    have := ENNReal.toReal_mono hqt hq; rwa [ENNReal.toReal_one] at this
  have hfin : (Module.finrank ℝ Space : ℝ) < 4 * q.toReal := by
    rw [show Module.finrank ℝ Space = 3 by simp [Space]]; push_cast; linarith
  refine (integrable_one_add_norm (μ := (volume : Measure Space)) hfin).congr
    (Eventually.of_forall fun y => ?_)
  simp only
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _), ← Real.rpow_mul (by positivity)]
  ring_nf

/-- **INF04 T8 `HeatAdmissible.of_memLp`.** Every `L^p` field, `1 ≤ p ≤ ∞`, is admissible
(Hölder against `(1 + |y|)^{-4} ∈ L^{p'}`). -/
theorem HeatAdmissible.of_memLp {f : Space → E} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hf : MemLp f p volume) : HeatAdmissible f := by
  refine ⟨hf.1, 4, ?_⟩
  set q : ℝ≥0∞ := (1 - p⁻¹)⁻¹ with hq_def
  have hpinv : p⁻¹ ≤ 1 := ENNReal.inv_le_one.mpr hp
  have hq1 : 1 ≤ q := by
    rw [hq_def]; exact ENNReal.one_le_inv.mpr tsub_le_self
  haveI : ENNReal.HolderConjugate q p := by
    rw [ENNReal.holderConjugate_iff, hq_def, inv_inv]
    exact tsub_add_cancel_of_le hpinv
  have h := hf.smul (memLp_weight (q := q) hq1) (r := 1)
  rw [memLp_one_iff_integrable] at h
  exact_mod_cast h

/-- `|y|^{-1}` is integrable on the closed unit ball of `ℝ³`. -/
theorem integrableOn_inv_norm_closedBall :
    IntegrableOn (fun y : Space => ‖y‖ ^ (-(1 : ℝ))) (Metric.closedBall (0 : Space) 1) := by
  have hdim : Module.finrank ℝ Space = 3 := by simp [Space]
  have hloc : LocallyIntegrable (fun y : Space => ‖y‖ ^ (-(1 : ℝ))) volume := by
    refine locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1) (by rw [hdim]; norm_num)
      (by rw [hdim]; norm_num) (Eventually.of_forall fun y => ?_) ?_
    · rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    · exact (continuous_norm.measurable.pow_const _).aestronglyMeasurable
  exact hloc.integrableOn_isCompact (isCompact_closedBall 0 1)

/-- **INF04 T8 `HeatAdmissible.of_inv_bound`.** A measurable field with
`|f(x)| ≤ C|x|^{-1}` for `x ≠ 0` is admissible (the DSS datum class, tex 5205–5216, B0697). -/
theorem HeatAdmissible.of_inv_bound {f : Space → E} (hm : AEStronglyMeasurable f volume)
    {C : ℝ} (h : ∀ x ≠ 0, ‖f x‖ ≤ C * ‖x‖⁻¹) : HeatAdmissible f := by
  refine ⟨hm, 4, ?_⟩
  set g : Space → ℝ := fun y => (Metric.closedBall (0 : Space) 1).indicator
    (fun y => ‖y‖ ^ (-(1 : ℝ))) y + (1 + ‖y‖) ^ (-(4 : ℝ)) with hg
  have hgi : Integrable g := by
    refine (integrableOn_inv_norm_closedBall.integrable_indicator
      Metric.isClosed_closedBall.measurableSet).add ?_
    have hfin : (Module.finrank ℝ Space : ℝ) < 4 := by
      rw [show Module.finrank ℝ Space = 3 by simp [Space]]; norm_num
    exact integrable_one_add_norm hfin
  refine (hgi.const_mul |C|).mono' ((continuous_weight 4).aestronglyMeasurable.smul hm) ?_
  filter_upwards [Measure.ae_ne volume (0 : Space)] with y hy
  simp only [Nat.cast_ofNat]
  have hny : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hw0 : 0 ≤ (1 + ‖y‖) ^ (-(4 : ℝ)) := Real.rpow_nonneg (by positivity) _
  have hw1 : (1 + ‖y‖) ^ (-(4 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by simp) (by norm_num)
  have hfy : ‖f y‖ ≤ |C| * ‖y‖⁻¹ :=
    (h y hy).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (inv_nonneg.mpr hny.le))
  rw [norm_smul, Real.norm_of_nonneg hw0]
  have hind : 0 ≤ (Metric.closedBall (0 : Space) 1).indicator
      (fun y => ‖y‖ ^ (-(1 : ℝ))) y :=
    Set.indicator_nonneg (fun z _ => Real.rpow_nonneg (norm_nonneg z) _) y
  by_cases hb : ‖y‖ ≤ 1
  · have hmem : y ∈ Metric.closedBall (0 : Space) 1 := by simpa using hb
    rw [hg]
    simp only [Set.indicator_of_mem hmem, Real.rpow_neg_one]
    calc (1 + ‖y‖) ^ (-(4 : ℝ)) * ‖f y‖ ≤ 1 * (|C| * ‖y‖⁻¹) := by
          gcongr
      _ ≤ |C| * (‖y‖⁻¹ + (1 + ‖y‖) ^ (-(4 : ℝ))) := by
          rw [one_mul]; gcongr; linarith
  · have hy1 : 1 < ‖y‖ := lt_of_not_ge hb
    have hinv : ‖y‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hy1.le
    calc (1 + ‖y‖) ^ (-(4 : ℝ)) * ‖f y‖ ≤ (1 + ‖y‖) ^ (-(4 : ℝ)) * (|C| * 1) := by
          gcongr; exact hfy.trans (mul_le_mul_of_nonneg_left hinv (abs_nonneg C))
      _ = |C| * (1 + ‖y‖) ^ (-(4 : ℝ)) := by ring
      _ ≤ |C| * g y := by
          gcongr; rw [hg]; simp only; linarith

/-! ### Convergence of the heat integral -/

/-- **INF04 T8 `integrable_heat`.** For admissible `f`, `θ > 0` and every `x`, the heat
integrand `y ↦ G_θ(y) f(x - y)` is integrable. -/
theorem integrable_heat {f : Space → E} (hf : HeatAdmissible f) {θ : ℝ} (hθ : 0 < θ)
    (x : Space) : Integrable (fun y : Space => kernel θ y • f (x - y)) := by
  obtain ⟨hfm, m, hm⟩ := hf
  obtain ⟨C, hC, hK⟩ := gaussKernel_le_weight 3 hθ (m := (m : ℝ)) (by positivity)
  have h1 : Integrable (fun y : Space => kernel θ (x - y) • f y) := by
    refine (hm.norm.const_mul (C * (1 + ‖x‖) ^ (m : ℝ))).mono'
      (((continuous_kernel θ).comp (continuous_const.sub continuous_id)).aestronglyMeasurable.smul
        hfm) (Eventually.of_forall fun y => ?_)
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (kernel_nonneg hθ _),
      Real.norm_of_nonneg (by positivity)]
    have hk : kernel θ (x - y) ≤ C * ((1 + ‖x‖) ^ (m : ℝ) * (1 + ‖y‖) ^ (-(m : ℝ))) := by
      rw [← Gaussian.gaussKernel_three_eq]
      exact (hK (x - y)).trans (mul_le_mul_of_nonneg_left
        (one_add_norm_sub_rpow_neg_le (by positivity) x y) hC.le)
    calc kernel θ (x - y) * ‖f y‖
        ≤ C * ((1 + ‖x‖) ^ (m : ℝ) * (1 + ‖y‖) ^ (-(m : ℝ))) * ‖f y‖ := by gcongr
      _ = C * (1 + ‖x‖) ^ (m : ℝ) * ((1 + ‖y‖) ^ (-(m : ℝ)) * ‖f y‖) := by ring
  have h2 := h1.comp_sub_left x
  simpa only [sub_sub_cancel] using h2

theorem aestronglyMeasurable_section {f : Space → E} (hf : AEStronglyMeasurable f volume)
    (x : Space) : AEStronglyMeasurable (fun y : Space => f (x - y)) volume :=
  hf.comp_measurePreserving (Measure.measurePreserving_sub_left volume x)

/-- **INF04 T8 `average_add`.** Additivity of the heat integral on admissible data, at every
point. -/
theorem average_add' {f g : Space → E} (hf : HeatAdmissible f) (hg : HeatAdmissible g)
    {θ : ℝ} (hθ : 0 < θ) : average θ (f + g) = average θ f + average θ g := by
  funext x
  simp only [average, Pi.add_apply, smul_add]
  exact integral_add (integrable_heat hf hθ x) (integrable_heat hg hθ x)

theorem average_sub' {f g : Space → E} (hf : HeatAdmissible f) (hg : HeatAdmissible g)
    {θ : ℝ} (hθ : 0 < θ) : average θ (f - g) = average θ f - average θ g := by
  funext x
  simp only [average, Pi.sub_apply, smul_sub]
  exact integral_sub (integrable_heat hf hθ x) (integrable_heat hg hθ x)

/-- **INF04 T8 `average_add_time'`.** The semigroup law at every point for admissible data:
`e^{(s+t)Δ}f = e^{sΔ}e^{tΔ}f`, `s, t > 0`. -/
theorem average_add_time' {f : Space → E} (hf : HeatAdmissible f) {s t : ℝ} (hs : 0 < s)
    (ht : 0 < t) : average (s + t) f = average s (average t f) := by
  funext x
  have hfin : heatAbs (AddMonoidHom.id Space) (s + t) f x < ∞ := by
    have h := (integrable_heat hf (add_pos hs ht) x).2
    rw [hasFiniteIntegral_iff_enorm] at h
    simpa only [heatAbs, AddMonoidHom.id_apply, enorm_smul,
      Gaussian.gaussKernel_three_eq] using h
  have h := heatConv_add_time_of_lt_top (AddMonoidHom.id Space) hs ht
    (by simpa only [AddMonoidHom.id_apply] using aestronglyMeasurable_section hf.1 x) hfin
  rwa [heatConv_space_eq_average, heatConv_space_eq_average, heatConv_space_eq_average] at h

/-- **INF04 T8 `average_dilate'`.** For `λ, θ > 0`:
`e^{θΔ}[λ f(λ·)](y) = λ (e^{λ²θΔ}f)(λy)` (B0697), for every field (no admissibility needed). -/
theorem average_dilate' {lam θ : ℝ} (hlam : 0 < lam) (hθ : 0 < θ) (f : Space → E) :
    average θ (fun y => lam • f (lam • y)) =
      fun y => lam • average (lam ^ 2 * θ) f (lam • y) := by
  have h := average_smul θ lam (fun y => f (lam • y))
  rw [show (fun y => lam • f (lam • y)) = lam • fun y => f (lam • y) from rfl, h,
    average_dilate hlam hθ]
  rfl

end UnforcedLeray.Heat
