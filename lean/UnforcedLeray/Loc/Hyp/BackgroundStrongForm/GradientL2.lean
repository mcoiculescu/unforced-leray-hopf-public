import UnforcedLeray.Loc.Hyp.BackgroundStrongForm.Hypotheses
import UnforcedLeray.Loc.Hyp.HeatProfileRegularity.Scaling

/-!
# H-BgStrong, helpers: `∇H_h[u_dss] ∈ C(ℝ; L²)` (`HeatProfileGradientL2`)

Proof of `HeatProfileGradientL2` (`Loc/Hyp/BackgroundStrongForm/Hypotheses.lean`;
`paper/main.tex` lines 274–281, "`|D^j H_h[u_dss]| ≤ C_j⟨y⟩^{-1-j}` uniformly in phase";
blueprint unit B0710).

The proof is that of `HeatProfileRegularity` (`Loc/Hyp/HeatProfileRegularity.lean`) with the
exponent `3` of the gradient replaced by `2`: by the change of variables
`H_h[u](·, τ) = e^{hΔ}u_τ`, `u_τ(x) = e^{τ/2}u(e^{τ/2}x)` (`heatProfile_eq_average`), and the
near/far heat smoothing `‖D e^{hΔ}b(y)‖ ≤ εQ₁(1 + |y|)⁻²` (`heat_smoothing`), the classical
gradient of `H(τ)` is bounded by `CQ₁(1 + |y|)⁻²`, which is in `L²(ℝ³)` (`2·2 > 3`); applied to
`u_σ - u_τ` (constant `3C|σ - τ|`, `invDist_dil_sub`) the same bound makes the gradient
Lipschitz in the phase in `L²`.

The analytic lemmas are imported from the compiled `Loc/Hyp/HeatProfileRegularity/Scaling.lean`
and `Smoothing.lean`. The small lemmas of `Loc/Hyp/HeatProfileRegularity/Fields.lean` used here
(classical derivative field, weights in `Lᵖ`, `Lᵖ` distance bound, continuity from a Lipschitz
bound) are copied, with the same proofs, from that file

-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Metric
open scoped ContDiff Topology ENNReal

namespace UnforcedLeray.Blueprint.HypBg

open UnforcedLeray.HeatProfileReg (dil heatProfile_eq_average invDist_dil invDist_dil_sub
  uniform_bound average_sub heat_smoothing InvDist)

/-! ## Copied from `Loc/Hyp/HeatProfileRegularity/Fields.lean` -/

/-- The classical coordinate derivative `∂ᵢA`. -/
def gd1 (A : SpatialField) (i : Fin 3) : SpatialField :=
  fun y => fderiv ℝ A y (coordinateVector i)

theorem norm_coordinateVector' (i : Fin 3) : ‖coordinateVector i‖ = 1 := by
  simp [coordinateVector]

theorem gd1_contDiff {A : SpatialField} (hA : ContDiff ℝ 2 A) (i : Fin 3) :
    ContDiff ℝ 1 (gd1 A i) :=
  (hA.fderiv_right (m := 1) one_add_one_eq_two.le).clm_apply contDiff_const

theorem norm_gd1_le (A : SpatialField) (i : Fin 3) (y : Space) :
    ‖gd1 A i y‖ ≤ ‖iteratedFDeriv ℝ 1 A y‖ := by
  rw [norm_iteratedFDeriv_one]
  calc ‖gd1 A i y‖ ≤ ‖fderiv ℝ A y‖ * ‖coordinateVector i‖ := (fderiv ℝ A y).le_opNorm _
    _ = ‖fderiv ℝ A y‖ := by rw [norm_coordinateVector', mul_one]

theorem gd1_sub {A B : SpatialField} (hA : ContDiff ℝ 2 A) (hB : ContDiff ℝ 2 B) (i : Fin 3)
    (y : Space) : gd1 (A - B) i y = gd1 A i y - gd1 B i y := by
  simp only [gd1]
  rw [fderiv_sub ((hA.differentiable (by norm_num)) y) ((hB.differentiable (by norm_num)) y)]
  rfl

/-- `(1 + |y|)^{-m} ∈ Lᵖ(ℝ³)` when `mp > 3`. -/
theorem memLp_weight' (m : ℕ) (p : ℝ≥0∞) (hp0 : p ≠ 0) (hpt : p ≠ ⊤)
    (hmp : 3 < (m : ℝ) * p.toReal) :
    MemLp (fun y : Space => ((1 + ‖y‖) ^ m)⁻¹) p volume := by
  have hmeas : AEStronglyMeasurable (fun y : Space => ((1 + ‖y‖) ^ m)⁻¹) volume := by
    have : Measurable (fun y : Space => ((1 + ‖y‖) ^ m)⁻¹) := by fun_prop
    exact this.aestronglyMeasurable
  rw [← integrable_norm_rpow_iff hmeas hp0 hpt]
  have hfin : (Module.finrank ℝ Space : ℝ) = 3 := by simp
  have hint := integrable_one_add_norm (E := Space) (μ := volume) (r := (m : ℝ) * p.toReal)
    (by rw [hfin]; exact hmp)
  refine hint.congr (Eventually.of_forall fun y => ?_)
  have hpos : 0 < 1 + ‖y‖ := by positivity
  show (1 + ‖y‖) ^ (-((m : ℝ) * p.toReal)) = ‖((1 + ‖y‖) ^ m)⁻¹‖ ^ p.toReal
  rw [Real.norm_of_nonneg (by positivity), ← Real.rpow_natCast, ← Real.rpow_neg hpos.le,
    ← Real.rpow_mul hpos.le, neg_mul]

theorem norm_weight' (m : ℕ) (y : Space) : ‖((1 + ‖y‖) ^ m)⁻¹‖ = 1 / (1 + ‖y‖) ^ m := by
  rw [Real.norm_of_nonneg (by positivity), one_div]

/-- An `Lᵖ` distance bound from a pointwise bound. -/
theorem dist_toLp_le' {p : ℝ≥0∞} {f g : SpatialField} (hf : MemLp f p volume)
    (hg : MemLp g p volume) {w : Space → ℝ} (hw : MemLp w p volume) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ y, ‖f y - g y‖ ≤ c * ‖w y‖) :
    dist (hf.toLp f) (hg.toLp g) ≤ c * (eLpNorm w p volume).toReal := by
  rw [Lp.dist_def]
  have he : (⇑(hf.toLp f) - ⇑(hg.toLp g)) =ᵐ[volume] (f - g) :=
    hf.coeFn_toLp.sub hg.coeFn_toLp
  rw [eLpNorm_congr_ae he]
  have h1 := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := volume) (f := f - g) (g := w) (c := c)
    (Eventually.of_forall h) p
  calc (eLpNorm (f - g) p volume).toReal ≤ (ENNReal.ofReal c * eLpNorm w p volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hw.eLpNorm_ne_top) h1
    _ = c * (eLpNorm w p volume).toReal := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc]

/-- Continuity from a Lipschitz bound in the phase. -/
theorem continuous_of_dist_le' {X : Type} [PseudoMetricSpace X] {F : ℝ → X} {K : ℝ}
    (hK : 0 ≤ K) (h : ∀ σ τ, dist (F σ) (F τ) ≤ K * |σ - τ|) : Continuous F :=
  (LipschitzWith.of_dist_le_mul (K := Real.toNNReal K) fun σ τ => by
    rw [Real.coe_toNNReal _ hK, Real.dist_eq]; exact h σ τ).continuous

/-- Decay `c / (1 + |y|)` gives vanishing at infinity (copied from `Fields.lean`). -/
theorem tendsto_zero_of_decay' {f : SpatialField} {c : ℝ} (h : ∀ y, ‖f y‖ ≤ c / (1 + ‖y‖)) :
    Tendsto f (cocompact Space) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h1 : Tendsto (fun y : Space => c / (1 + ‖y‖)) (cocompact Space) (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_left _ 1 (tendsto_norm_cocompact_atTop (E := Space)))
  exact squeeze_zero (fun y => norm_nonneg _) h h1

/-- A `C₀` distance bound from a pointwise bound (copied from `Fields.lean`). -/
theorem dist_C0_le' {F G : ZeroAtInftyContinuousMap Space Space} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ y, ‖F y - G y‖ ≤ c) : dist F G ≤ c := by
  rw [← ZeroAtInftyContinuousMap.dist_toBCF_eq_dist, BoundedContinuousFunction.dist_le hc]
  intro y
  rw [dist_eq_norm]
  exact h y

/-! ## The `C₀` representative of the heat profile -/

/-- The part of `HeatProfileRegularity` used for `BackgroundStrongForm`: under the package
clauses on `u` (lines 151–156), `H_h[u](τ)` has a `C₀` representative continuous in `τ` for
the sup norm (line 280: `U_* ∈ C_per C₀`). -/
def HeatProfileC0 : Prop :=
  ∀ (h period : ℝ) (u : SpatialField), 0 < h → 0 < period → ContDiffOn ℝ ∞ u {0}ᶜ →
    (∀ x : Space, x ≠ 0 → u (Real.exp (period / 2) • x) = Real.exp (-(period / 2)) • u x) →
    (∀ k : ℕ, k ≤ 4 → ∃ C : ℝ, ∀ x : Space, x ≠ 0 →
      ‖iteratedFDeriv ℝ k u x‖ * ‖x‖ ^ (k + 1) ≤ C) →
    ∃ V : ℝ → ZeroAtInftyContinuousMap Space Space, Continuous V ∧
      ∀ τ, (V τ : SpatialField) =ᵐ[volume] heatProfile h u τ

theorem heatProfileC0_of_regularity (hH : HeatProfileRegularity) : HeatProfileC0 := by
  intro h period u hh hp hs hd hb
  obtain ⟨V, -, -, hVc, -, -, hV, -, -⟩ := hH h period u hh hp hs hd hb
  exact ⟨V, hVc, hV⟩

/-- **`HeatProfileC0`**, by the argument of `Loc/Hyp/HeatProfileRegularity.lean`: `V(τ) = e^{hΔ}u_τ`
decays like `(1 + |y|)⁻¹` and is Lipschitz in the phase for the sup norm. -/
theorem heatProfileC0 : HeatProfileC0 := by
  intro h period u hh _hperiod hsmooth _hdss hbounds
  obtain ⟨C, hC0, hC⟩ := uniform_bound hbounds
  obtain ⟨Q, hQ0, hQ⟩ := heat_smoothing hh
  have hinv : ∀ τ, InvDist (dil τ u) C := invDist_dil hsmooth (fun k hk => hC k (by omega))
  have hdif : ∀ σ τ, InvDist (dil σ u - dil τ u) (3 * C * |σ - τ|) :=
    invDist_dil_sub hsmooth hC0 hC
  have hprof : ∀ τ, heatProfile h u τ = Heat.average h (dil τ u) := heatProfile_eq_average hh u
  have hreg : ∀ τ, ContDiff ℝ 2 (Heat.average h (dil τ u)) := fun τ => (hQ _ _ (hinv τ)).1
  have hsub : ∀ σ τ, Heat.average h (dil σ u) - Heat.average h (dil τ u) =
      Heat.average h (dil σ u - dil τ u) := fun σ τ => (average_sub hh (hinv σ) (hinv τ)).symm
  have hb0 : ∀ (b : SpatialField) (ε : ℝ), InvDist b ε → ∀ y : Space,
      ‖Heat.average h b y‖ ≤ ε * Q 0 / (1 + ‖y‖) := by
    intro b ε hb y
    have h0 := (hQ b ε hb).2 0 (by omega) y
    rwa [norm_iteratedFDeriv_zero, zero_add, pow_one] at h0
  have hQ0' := hQ0 0
  have hd0 : ∀ σ τ : ℝ, 0 ≤ 3 * C * |σ - τ| := fun σ τ =>
    mul_nonneg (mul_nonneg (by norm_num) hC0) (abs_nonneg _)
  refine ⟨fun τ => ⟨⟨Heat.average h (dil τ u), (hreg τ).continuous⟩,
      tendsto_zero_of_decay' (hb0 _ _ (hinv τ))⟩, ?_, ?_⟩
  · refine continuous_of_dist_le' (K := 3 * C * Q 0)
      (mul_nonneg (mul_nonneg (by norm_num) hC0) hQ0') fun σ τ => ?_
    refine dist_C0_le' (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC0) hQ0')
      (abs_nonneg _)) fun y => ?_
    show ‖Heat.average h (dil σ u) y - Heat.average h (dil τ u) y‖ ≤ 3 * C * Q 0 * |σ - τ|
    have e : Heat.average h (dil σ u) y - Heat.average h (dil τ u) y =
        Heat.average h (dil σ u - dil τ u) y := congrFun (hsub σ τ) y
    rw [e]
    refine (hb0 _ _ (hdif σ τ) y).trans ?_
    calc 3 * C * |σ - τ| * Q 0 / (1 + ‖y‖) ≤ 3 * C * |σ - τ| * Q 0 :=
          div_le_self (mul_nonneg (hd0 σ τ) hQ0') (by linarith [norm_nonneg y])
      _ = 3 * C * Q 0 * |σ - τ| := by ring
  · exact fun τ => Eventually.of_forall fun y => (congrFun (hprof τ) y).symm

/-! ## The `L²` gradient of the heat profile -/

/-- **`HeatProfileGradientL2`** (tex lines 274–281, B0710): the weak gradient of
`H_h[u](·, τ)` is `∇e^{hΔ}u_τ ∈ L²`, Lipschitz in the phase. -/
theorem heatProfileGradientL2 : HeatProfileGradientL2 := by
  intro h period u hh _hperiod hsmooth _hdss hbounds
  obtain ⟨C, hC0, hC⟩ := uniform_bound hbounds
  obtain ⟨Q, hQ0, hQ⟩ := heat_smoothing hh
  have hinv : ∀ τ, InvDist (dil τ u) C := invDist_dil hsmooth (fun k hk => hC k (by omega))
  have hdif : ∀ σ τ, InvDist (dil σ u - dil τ u) (3 * C * |σ - τ|) :=
    invDist_dil_sub hsmooth hC0 hC
  have hprof : ∀ τ, heatProfile h u τ = Heat.average h (dil τ u) := heatProfile_eq_average hh u
  have hreg : ∀ τ, ContDiff ℝ 2 (Heat.average h (dil τ u)) := fun τ => (hQ _ _ (hinv τ)).1
  have hsub : ∀ σ τ, Heat.average h (dil σ u) - Heat.average h (dil τ u) =
      Heat.average h (dil σ u - dil τ u) := fun σ τ => (average_sub hh (hinv σ) (hinv τ)).symm
  have hb1 : ∀ (b : SpatialField) (ε : ℝ), InvDist b ε → ∀ (i : Fin 3) (y : Space),
      ‖gd1 (Heat.average h b) i y‖ ≤ (ε * Q 1) * ‖((1 + ‖y‖) ^ 2)⁻¹‖ := by
    intro b ε hb i y
    refine (norm_gd1_le _ i y).trans (((hQ b ε hb).2 1 (by omega) y).trans (le_of_eq ?_))
    rw [norm_weight']
    ring
  have hw2 : MemLp (fun y : Space => ((1 + ‖y‖) ^ 2)⁻¹) 2 volume :=
    memLp_weight' 2 2 (by norm_num) (by norm_num) (by norm_num)
  have hW : ∀ (τ : ℝ) (i : Fin 3), MemLp (gd1 (Heat.average h (dil τ u)) i) 2 volume :=
    fun τ i => hw2.of_le_mul ((gd1_contDiff (hreg τ) i).continuous.aestronglyMeasurable)
      (Eventually.of_forall fun y => hb1 _ _ (hinv τ) i y)
  have hQ1' := hQ0 1
  have hd0 : ∀ σ τ : ℝ, 0 ≤ 3 * C * |σ - τ| := fun σ τ =>
    mul_nonneg (mul_nonneg (by norm_num) hC0) (abs_nonneg _)
  refine ⟨fun τ i => (hW τ i).toLp _, ?_, ?_⟩
  · refine continuous_pi fun i => continuous_of_dist_le'
      (K := 3 * C * Q 1 * (eLpNorm (fun y : Space => ((1 + ‖y‖) ^ 2)⁻¹) 2 volume).toReal)
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC0) hQ1') ENNReal.toReal_nonneg)
      fun σ τ => ?_
    refine (dist_toLp_le' (hW σ i) (hW τ i) hw2 (c := 3 * C * |σ - τ| * Q 1)
      (mul_nonneg (hd0 σ τ) hQ1') fun y => ?_).trans (le_of_eq (by ring))
    rw [← gd1_sub (hreg σ) (hreg τ), hsub σ τ]
    exact hb1 _ _ (hdif σ τ) i y
  · intro τ i
    rw [hprof τ]
    exact (hasWeakSpatialDerivative_of_contDiff ((hreg τ).of_le (by norm_num)) i).congr
      EventuallyEq.rfl (hW τ i).coeFn_toLp.symm

end UnforcedLeray.Blueprint.HypBg
