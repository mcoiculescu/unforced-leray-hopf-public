import UnforcedLeray.Lib.Semigroups.ExpSemigroup
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Multiplication and diagonal semigroups (INF07 T7.4)


§5, target **T7.4** (Wave 1, block 1G), bypasses BP1 and BP7; uses B0106, B0107 (tex 1655-1667:
the free evolutions `E_β(t, s) = exp[D ∫_s^t β]` are diagonal in the Hermite basis) and B0124
(tex 1879-1888, `eq:st18-t00101`: `‖e^{aD}‖_{X_{G,j} → X_{G,j+1}} ≤ C_j a^{-1/2}` for
`0 < a ≤ 1`, which in sector two reduces to `sup_ℓ (1 + ℓ)^{1/2} e^{-aℓ} ≤ C a^{-1/2}`,
scoping note line 336).

Contents:
* `Mult.mulOp m`: multiplication by a bounded a.e.-strongly measurable complex function on
  `Lp E p μ`, with `‖mulOp m‖ ≤ max C 0` when `‖m‖ ≤ C` a.e.; composition and identity rules;
* `Mult.tendsto_eLpNorm_smul_of_dominated`: dominated convergence for `‖g_i f‖_{L^p}`
  (`p < ∞`), along any countably generated filter;
* `Mult.mulSemigroup a`: the multiplication semigroup `f ↦ e^{t a} f` on `Lp E p μ`
  (`1 ≤ p < ∞`) for `Re a ≤ ω` a.e., an `ExpSemigroup` with `M = 1` and growth rate `ω`
  (strong continuity by dominated convergence);
* `Mult.diagSemigroup λ`: the diagonal semigroup `diag(e^{t λ_k})` on `ℓ^p(ι; E)`, realised as
  `Lp E p (Measure.count)` on a discrete index type, for `Re λ_k ≤ ω`;
* `Mult.sqrt_one_add_mul_exp_neg_le`: the "Hermite level" smoothing bound
  `(1 + ℓ)^{1/2} e^{-aℓ} ≤ a^{-1/2}` for `0 < a ≤ 1`, `ℓ ≥ 0`, and its operator form
  `Mult.norm_hermiteSmoothing_le` on `ℓ^p(ℕ; E)`.

The concrete Gaussian instance on `X_G` (through the Laguerre/Hermite basis of INF10) is not
built here: it needs INF10 H1-H2, which belong to Wave 1 block 1H.

Times `t < 0`: the semigroup uses `e^{max t 0 · a}`, which is bounded; negative times are never
used (`ExpSemigroup` constrains only `t ≥ 0`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace UnforcedLeray.Infra

namespace Mult

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem memLp_smul_of_bdd {m : α → ℂ} (hm : AEStronglyMeasurable m μ) {C : ℝ}
    (hC : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) {f : α → E} (hf : MemLp f p μ) :
    MemLp (fun x => m x • f x) p μ :=
  hf.of_le_mul (hm.smul hf.1) (by
    filter_upwards [hC] with x hx
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _))

/-- Multiplication by a bounded a.e.-strongly measurable complex function on `L^p`. -/
def mulOp (m : α → ℂ) (hm : AEStronglyMeasurable m μ) {C : ℝ} (hC : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) :
    Lp E p μ →L[ℂ] Lp E p μ :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_smul_of_bdd hm hC (Lp.memLp f)).toLp _
      map_add' := fun f g => by
        apply Lp.ext
        filter_upwards [(memLp_smul_of_bdd hm hC (Lp.memLp (f + g))).coeFn_toLp,
          (memLp_smul_of_bdd hm hC (Lp.memLp f)).coeFn_toLp,
          (memLp_smul_of_bdd hm hC (Lp.memLp g)).coeFn_toLp,
          Lp.coeFn_add ((memLp_smul_of_bdd hm hC (Lp.memLp f)).toLp _)
            ((memLp_smul_of_bdd hm hC (Lp.memLp g)).toLp _),
          Lp.coeFn_add f g] with x h1 h2 h3 h4 h5
        simp only [h1, h2, h3, h4, h5, Pi.add_apply, smul_add]
      map_smul' := fun c f => by
        apply Lp.ext
        filter_upwards [(memLp_smul_of_bdd hm hC (Lp.memLp (c • f))).coeFn_toLp,
          (memLp_smul_of_bdd hm hC (Lp.memLp f)).coeFn_toLp,
          Lp.coeFn_smul c ((memLp_smul_of_bdd hm hC (Lp.memLp f)).toLp _),
          Lp.coeFn_smul c f] with x h1 h2 h3 h4
        simp only [RingHom.id_apply, h1, h2, h3, h4, Pi.smul_apply]
        rw [smul_comm] }
    (max C 0) fun f => by
      refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
      filter_upwards [(memLp_smul_of_bdd hm hC (Lp.memLp f)).coeFn_toLp, hC] with x hx hCx
      simp only [LinearMap.coe_mk, AddHom.coe_mk, hx, norm_smul]
      exact mul_le_mul_of_nonneg_right (hCx.trans (le_max_left _ _)) (norm_nonneg _)

theorem coeFn_mulOp {m : α → ℂ} (hm : AEStronglyMeasurable m μ) {C : ℝ}
    (hC : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) (f : Lp E p μ) :
    ⇑(mulOp m hm hC f) =ᵐ[μ] fun x => m x • f x :=
  (memLp_smul_of_bdd hm hC (Lp.memLp f)).coeFn_toLp

theorem norm_mulOp_le {m : α → ℂ} (hm : AEStronglyMeasurable m μ) {C : ℝ}
    (hC : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) : ‖(mulOp m hm hC : Lp E p μ →L[ℂ] Lp E p μ)‖ ≤ max C 0 :=
  LinearMap.mkContinuous_norm_le _ (le_max_right _ _) _

/-- Multipliers that agree a.e. and multiply a.e. compose. -/
theorem mulOp_eq_comp {m m₁ m₂ : α → ℂ} (hm : AEStronglyMeasurable m μ)
    (hm₁ : AEStronglyMeasurable m₁ μ) (hm₂ : AEStronglyMeasurable m₂ μ) {C C₁ C₂ : ℝ}
    (hC : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) (hC₁ : ∀ᵐ x ∂μ, ‖m₁ x‖ ≤ C₁) (hC₂ : ∀ᵐ x ∂μ, ‖m₂ x‖ ≤ C₂)
    (h : ∀ᵐ x ∂μ, m x = m₁ x * m₂ x) :
    (mulOp m hm hC : Lp E p μ →L[ℂ] Lp E p μ) = mulOp m₁ hm₁ hC₁ ∘L mulOp m₂ hm₂ hC₂ := by
  ext1 f
  apply Lp.ext
  filter_upwards [coeFn_mulOp hm hC f, coeFn_mulOp hm₁ hC₁ (mulOp m₂ hm₂ hC₂ f),
    coeFn_mulOp hm₂ hC₂ f, h] with x h1 h2 h3 h4
  rw [ContinuousLinearMap.comp_apply, h1, h2, h3, h4, mul_smul]

/-- A multiplier equal to `1` a.e. is the identity. -/
theorem mulOp_eq_one {m : α → ℂ} (hm : AEStronglyMeasurable m μ) {C : ℝ}
    (hC : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) (h : ∀ᵐ x ∂μ, m x = 1) :
    (mulOp m hm hC : Lp E p μ →L[ℂ] Lp E p μ) = 1 := by
  ext1 f
  apply Lp.ext
  filter_upwards [coeFn_mulOp hm hC f, h] with x h1 h2
  rw [h1, h2, one_smul, ContinuousLinearMap.one_apply]

/-- Dominated convergence in `L^p`, `p < ∞`: if `‖g i‖ ≤ B` a.e. and `g i → 0` a.e., then
`‖g i f‖_{L^p} → 0` for `f ∈ L^p`. -/
theorem tendsto_eLpNorm_smul_of_dominated {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (hp : p ≠ ∞) {g : ι → α → ℂ} (hg : ∀ᶠ i in l, AEStronglyMeasurable (g i) μ) {B : ℝ}
    (hB : ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖g i x‖ ≤ B)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i => g i x) l (𝓝 0)) {f : α → E} (hf : MemLp f p μ) :
    Tendsto (fun i => eLpNorm (fun x => g i x • f x) p μ) l (𝓝 0) := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hp0 : p ≠ 0 := (lt_of_lt_of_le one_pos hp1).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  simp_rw [eLpNorm_eq_eLpNorm' hp0 hp, eLpNorm']
  have hfin : ∫⁻ x, (ENNReal.ofReal B * ‖f x‖ₑ) ^ p.toReal ∂μ ≠ ∞ := by
    simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le]
    rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq.le ENNReal.ofReal_ne_top)]
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hq.le ENNReal.ofReal_ne_top)
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hp hf.2).ne
  have hint : Tendsto (fun i => ∫⁻ x, ‖g i x • f x‖ₑ ^ p.toReal ∂μ) l (𝓝 0) := by
    have h := tendsto_lintegral_filter_of_dominated_convergence' (μ := μ) (l := l)
      (F := fun i x => ‖g i x • f x‖ₑ ^ p.toReal) (f := fun _ => 0)
      (fun x => (ENNReal.ofReal B * ‖f x‖ₑ) ^ p.toReal)
      (hg.mono fun i hi => ((hi.smul hf.1).enorm).pow_const _)
      (hB.mono fun i hi => hi.mono fun x hx => by
        rw [enorm_smul]
        refine ENNReal.rpow_le_rpow (mul_le_mul_left ?_ _) hq.le
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal hx)
      hfin
      (hlim.mono fun x hx => by
        have h1 : Tendsto (fun i => ‖g i x • f x‖ₑ) l (𝓝 0) := by
          simpa using (hx.smul_const (f x)).enorm
        have h2 := ((ENNReal.continuous_rpow_const (y := p.toReal)).tendsto 0).comp h1
        simpa [Function.comp_def, ENNReal.zero_rpow_of_pos hq] using h2)
    simpa using h
  have h := ((ENNReal.continuous_rpow_const (y := 1 / p.toReal)).tendsto 0).comp hint
  simpa [Function.comp_def, ENNReal.zero_rpow_of_pos (inv_pos.2 hq)] using h

/-- The multiplier `e^{max t 0 · a}` of the multiplication semigroup. -/
def expMul (a : α → ℂ) (t : ℝ) : α → ℂ := fun x => Complex.exp (max t 0 * a x)

theorem aestronglyMeasurable_expMul {a : α → ℂ} (ha : AEStronglyMeasurable a μ) (t : ℝ) :
    AEStronglyMeasurable (expMul a t) μ :=
  Complex.continuous_exp.comp_aestronglyMeasurable (ha.const_mul _)

theorem norm_expMul (a : α → ℂ) (t : ℝ) (x : α) :
    ‖expMul a t x‖ = Real.exp (max t 0 * (a x).re) := by
  rw [expMul, Complex.norm_exp, Complex.re_ofReal_mul]

/-- `‖e^{s a}‖ ≤ e^{|ω| b}` for `0 ≤ s ≤ b` where `Re a ≤ ω`. -/
theorem norm_expMul_le_of_le {a : α → ℂ} {ω : ℝ} {x : α} (hx : (a x).re ≤ ω) {t b : ℝ}
    (htb : max t 0 ≤ b) : ‖expMul a t x‖ ≤ Real.exp (|ω| * b) := by
  rw [norm_expMul]
  refine Real.exp_le_exp.2 ?_
  have h0 : 0 ≤ max t 0 := le_max_right _ _
  calc max t 0 * (a x).re ≤ max t 0 * ω := mul_le_mul_of_nonneg_left hx h0
    _ ≤ max t 0 * |ω| := mul_le_mul_of_nonneg_left (le_abs_self _) h0
    _ ≤ b * |ω| := mul_le_mul_of_nonneg_right htb (abs_nonneg _)
    _ = |ω| * b := mul_comm _ _

theorem norm_expMul_le {a : α → ℂ} {ω : ℝ} (hω : ∀ᵐ x ∂μ, (a x).re ≤ ω) (t : ℝ) :
    ∀ᵐ x ∂μ, ‖expMul a t x‖ ≤ Real.exp (ω * max t 0) := by
  filter_upwards [hω] with x hx
  rw [norm_expMul, mul_comm ω]
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hx (le_max_right _ _))

/-- Strong continuity of the multiplication semigroup (dominated convergence). -/
theorem continuousOn_mulOp_expMul (hp : p ≠ ∞) {a : α → ℂ} (ha : AEStronglyMeasurable a μ)
    {ω : ℝ} (hω : ∀ᵐ x ∂μ, (a x).re ≤ ω) (f : Lp E p μ) :
    ContinuousOn (fun t => mulOp (expMul a t) (aestronglyMeasurable_expMul ha t)
      (norm_expMul_le hω t) f) (Ici 0) := by
  intro t₀ ht₀
  rw [mem_Ici] at ht₀
  have hnorm : ∀ t, ‖mulOp (expMul a t) (aestronglyMeasurable_expMul ha t) (norm_expMul_le hω t) f -
      mulOp (expMul a t₀) (aestronglyMeasurable_expMul ha t₀) (norm_expMul_le hω t₀) f‖ =
      (eLpNorm (fun x => (expMul a t x - expMul a t₀ x) • f x) p μ).toReal := by
    intro t
    rw [Lp.norm_def]
    congr 1
    refine eLpNorm_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (mulOp (expMul a t) (aestronglyMeasurable_expMul ha t)
        (norm_expMul_le hω t) f) (mulOp (expMul a t₀) (aestronglyMeasurable_expMul ha t₀)
        (norm_expMul_le hω t₀) f),
      coeFn_mulOp (aestronglyMeasurable_expMul ha t) (norm_expMul_le hω t) f,
      coeFn_mulOp (aestronglyMeasurable_expMul ha t₀) (norm_expMul_le hω t₀) f] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3, sub_smul]
  have hkey : Tendsto (fun t => eLpNorm (fun x => (expMul a t x - expMul a t₀ x) • f x) p μ)
      (𝓝[Ici 0] t₀) (𝓝 0) := by
    refine tendsto_eLpNorm_smul_of_dominated hp
      (Eventually.of_forall fun t => (aestronglyMeasurable_expMul ha t).sub
        (aestronglyMeasurable_expMul ha t₀))
      (B := 2 * Real.exp (|ω| * (t₀ + 1))) ?_ ?_ (Lp.memLp f)
    · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds
        (show t₀ < t₀ + 1 by linarith))] with t ht ht'
      filter_upwards [hω] with x hx
      have h1 : ‖expMul a t x‖ ≤ Real.exp (|ω| * (t₀ + 1)) :=
        norm_expMul_le_of_le hx (max_le (le_of_lt ht') (by linarith))
      have h2 : ‖expMul a t₀ x‖ ≤ Real.exp (|ω| * (t₀ + 1)) :=
        norm_expMul_le_of_le hx (max_le (by linarith) (by linarith))
      calc ‖expMul a t x - expMul a t₀ x‖ ≤ ‖expMul a t x‖ + ‖expMul a t₀ x‖ := norm_sub_le _ _
        _ ≤ 2 * Real.exp (|ω| * (t₀ + 1)) := by linarith
    · refine Eventually.of_forall fun x => ?_
      have hc : Continuous fun t : ℝ => expMul a t x := by
        unfold expMul
        fun_prop
      have := ((hc.tendsto t₀).sub_const (expMul a t₀ x)).mono_left
        (nhdsWithin_le_nhds (s := Ici (0 : ℝ)))
      simpa using this
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  simp_rw [hnorm]
  simpa [Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hkey

/-- **T7.4, multiplication semigroup** `f ↦ e^{t a} f` on `L^p(μ; E)`, `1 ≤ p < ∞`, for a
measurable multiplier with `Re a ≤ ω` a.e.: an `ExpSemigroup` with `M = 1` and rate `ω`. -/
def mulSemigroup (hp : p ≠ ∞) (a : α → ℂ) (ha : AEStronglyMeasurable a μ) {ω : ℝ}
    (hω : ∀ᵐ x ∂μ, (a x).re ≤ ω) : ExpSemigroup (Lp E p μ) where
  T t := mulOp (expMul a t) (aestronglyMeasurable_expMul ha t) (norm_expMul_le hω t)
  T_zero := mulOp_eq_one _ _ (Eventually.of_forall fun x => by simp [expMul])
  T_add s t hs ht := mulOp_eq_comp _ _ _ _ _ _ (Eventually.of_forall fun x => by
    simp only [expMul, max_eq_left hs, max_eq_left ht, max_eq_left (add_nonneg hs ht)]
    rw [← Complex.exp_add]
    push_cast
    ring_nf)
  T_cont f := continuousOn_mulOp_expMul hp ha hω f
  M := 1
  ω := ω
  M_nonneg := zero_le_one
  T_le t ht := (norm_mulOp_le _ _).trans (by
    rw [max_eq_left (Real.exp_pos _).le, max_eq_left ht, one_mul])

theorem mulSemigroup_T_apply (hp : p ≠ ∞) {a : α → ℂ} (ha : AEStronglyMeasurable a μ) {ω : ℝ}
    (hω : ∀ᵐ x ∂μ, (a x).re ≤ ω) {t : ℝ} (ht : 0 ≤ t) (f : Lp E p μ) :
    ⇑((mulSemigroup hp a ha hω).T t f) =ᵐ[μ] fun x => Complex.exp (t * a x) • f x := by
  filter_upwards [coeFn_mulOp (aestronglyMeasurable_expMul ha t) (norm_expMul_le hω t) f]
    with x hx
  rw [mulSemigroup, hx, expMul, max_eq_left ht]

/-- **T7.4, diagonal semigroup** `diag(e^{t λ_k})` on `ℓ^p(ι; E) = L^p(count)`, `1 ≤ p < ∞`,
for `Re λ_k ≤ ω`. -/
def diagSemigroup {ι : Type*} [MeasurableSpace ι] [DiscreteMeasurableSpace ι] (hp : p ≠ ∞)
    (lam : ι → ℂ) {ω : ℝ} (hω : ∀ k, (lam k).re ≤ ω) :
    ExpSemigroup (Lp E p (Measure.count : Measure ι)) :=
  mulSemigroup hp lam Measurable.of_discrete.aestronglyMeasurable (Eventually.of_forall hω)

theorem diagSemigroup_T_apply {ι : Type*} [MeasurableSpace ι] [DiscreteMeasurableSpace ι]
    (hp : p ≠ ∞) {lam : ι → ℂ} {ω : ℝ} (hω : ∀ k, (lam k).re ≤ ω) {t : ℝ} (ht : 0 ≤ t)
    (f : Lp E p (Measure.count : Measure ι)) :
    ⇑((diagSemigroup hp lam hω).T t f) =ᵐ[Measure.count] fun k => Complex.exp (t * lam k) • f k :=
  mulSemigroup_T_apply hp _ _ ht f

/-- **T7.4, Hermite-level smoothing** (tex 1879-1888, `eq:st18-t00101` in sector two):
`(1 + ℓ)^{1/2} e^{-aℓ} ≤ a^{-1/2}` for `0 < a ≤ 1` and `ℓ ≥ 0`. -/
theorem sqrt_one_add_mul_exp_neg_le {a ℓ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hℓ : 0 ≤ ℓ) :
    Real.sqrt (1 + ℓ) * Real.exp (-(a * ℓ)) ≤ 1 / Real.sqrt a := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  rw [le_div_iff₀ hsa]
  set X := Real.sqrt (1 + ℓ) * Real.exp (-(a * ℓ)) * Real.sqrt a with hX
  have hX0 : 0 ≤ X := by positivity
  have hX2 : X ^ 2 = (1 + ℓ) * a * Real.exp (-(2 * a * ℓ)) := by
    rw [hX, mul_pow, mul_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt ha.le, ← Real.exp_nat_mul]
    push_cast
    ring_nf
  have hexp : 1 + 2 * a * ℓ ≤ Real.exp (2 * a * ℓ) := by
    have := Real.add_one_le_exp (2 * a * ℓ)
    linarith
  have hle : (1 + ℓ) * a ≤ Real.exp (2 * a * ℓ) := by nlinarith
  have hX21 : X ^ 2 ≤ 1 := by
    rw [hX2, Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
    exact hle
  nlinarith

theorem sqrt_one_add_mul_exp_neg_nonneg (a ℓ : ℝ) : 0 ≤ Real.sqrt (1 + ℓ) * Real.exp (-(a * ℓ)) :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le

/-- The Hermite-level smoothing multiplier `diag((1 + k)^{1/2} e^{-ak})` on `ℓ^p(ℕ; E)`. -/
def hermiteSmoothing {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    Lp E p (Measure.count : Measure ℕ) →L[ℂ] Lp E p (Measure.count : Measure ℕ) :=
  mulOp (fun k : ℕ => ((Real.sqrt (1 + k) * Real.exp (-(a * k)) : ℝ) : ℂ))
    Measurable.of_discrete.aestronglyMeasurable (C := 1 / Real.sqrt a)
    (Eventually.of_forall fun k => by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sqrt_one_add_mul_exp_neg_nonneg a k)]
      exact sqrt_one_add_mul_exp_neg_le ha ha1 (Nat.cast_nonneg k))

/-- **T7.4, Hermite-level smoothing, operator form**:
`‖diag((1 + k)^{1/2} e^{-ak})‖ ≤ a^{-1/2}` for `0 < a ≤ 1`. -/
theorem norm_hermiteSmoothing_le {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    ‖(hermiteSmoothing ha ha1 : Lp E p (Measure.count : Measure ℕ) →L[ℂ] _)‖ ≤
      1 / Real.sqrt a :=
  (norm_mulOp_le _ _).trans (max_le le_rfl (by positivity))

end Mult

end UnforcedLeray.Infra
