import UnforcedLeray.Lib.HeatR3.Transverse
import UnforcedLeray.Lib.HeatR3.Weighted
import NonUniqueEuler.P.Infra.ConvMinkowski.Minkowski

/-!
# The mixed-norm `L^q_{x'}L¹_z → L^q` heat bound on `ℝ³` (INF04 T12)


item `eLpNorm_average_mixed`. Unit B0740 (tex 9188–9247, proof of `eq:stress-setup:3.19`):
"apply ... horizontal heat contraction and the vertical `L¹ → L^{q_*}` heat bound to the inner
part" whose "`L^{q_*}_{x'}L¹_z` norm is at most `P_ν R^{2/q_*}`".

For `1 ≤ q < ∞`, `θ > 0` and measurable `a : ℝ³ → E`:

`‖e^{θΔ}a‖_{L^q(ℝ³)} ≤ ‖G^{(1)}_θ‖_{L^q(ℝ)} ‖a‖_{L^q_{x'}L¹_z}
  = c_q θ^{-(1 - 1/q)/2} ‖a‖_{L^q_{x'}L¹_z}`

(`eLpNorm_average_mixed`, `eLpNorm_average_mixed_pow`), with
`‖a‖_{L^q_{x'}L¹_z} = (∫_{ℝ²} (∫_ℝ |a(x', z)| dz)^q dx')^{1/q}` (`mixedNormHV`).

Proof: `|e^{θΔ}a| ≤ Φ := ∫ G^{(2)}_θ(x_h - y_h) Ψ(y_h, x₃) dy_h` with
`Ψ(y_h, s) = ∫ G^{(1)}_θ(s - z)|a(y_h, z)| dz` (`kernel_factor`, splitting `vsplit` of
`Transverse`); Minkowski's integral inequality (the vendored
`NonUniqueEuler.Conv.lintegral_lintegral_rpow_le`) in the horizontal translation variable and
unit mass of `G^{(2)}` give `‖Φ‖_{L^q} ≤ ‖Ψ‖_{L^q}`; Minkowski in `z` on each vertical line gives
`‖Ψ(y_h, ·)‖_{L^q} ≤ ‖G^{(1)}_θ‖_{L^q} ∫|a(y_h, z)| dz`. All integrals are lower integrals (no
finiteness assumed; a non-integrable heat integrand has the junk value `0`, which only lowers
the left side).
-/

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace UnforcedLeray.Heat

open MeasureTheory Filter Set Topology Real
open scoped ENNReal
open UnforcedLeray.Gaussian (Euc gaussKernel)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **The mixed norm `‖a‖_{L^q_{x'}L¹_z}`** of `a : ℝ³ → E`:
`(∫_{ℝ²} (∫_ℝ |a(x', z)| dz)^q dx')^{1/q}` (lower integrals). -/
def mixedNormHV (q : ℝ) (a : Space → E) : ℝ≥0∞ :=
  (∫⁻ x' : Euc 2, (∫⁻ z : ℝ, ‖a (mkPoint x' z)‖ₑ) ^ q) ^ q⁻¹

theorem measurable_mkPoint : Measurable fun p : Euc 2 × ℝ => mkPoint p.1 p.2 :=
  vsplit.symm.measurable.comp (measurable_snd.prodMk measurable_fst)

theorem kernel_mkPoint_sub {θ : ℝ} (hθ : 0 < θ) (x' y' : Euc 2) (s z : ℝ) :
    kernel θ (mkPoint x' s - mkPoint y' z) = gaussKernel 2 θ (x' - y') * lineGauss θ (s - z) := by
  rw [kernel_factor hθ, horiz_sub, horiz_mkPoint, horiz_mkPoint, PiLp.sub_apply, mkPoint_two,
    mkPoint_two]

theorem lintegral_ofReal_gaussKernel_two {θ : ℝ} (hθ : 0 < θ) :
    ∫⁻ w : Euc 2, ENNReal.ofReal (gaussKernel 2 θ w) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (Gaussian.integrable_gaussKernel hθ)
    (Eventually.of_forall fun w => Gaussian.gaussKernel_nonneg hθ w),
    Gaussian.integral_gaussKernel hθ, ENNReal.ofReal_one]

/-- The vertical line profile `|a(y', z)|`. -/
def vline (a : Space → E) (y' : Euc 2) (z : ℝ) : ℝ≥0∞ := ‖a (mkPoint y' z)‖ₑ

theorem measurable_vline {a : Space → E} (ha : StronglyMeasurable a) :
    Measurable (Function.uncurry (vline a)) := by
  have h1 : Measurable fun p : Euc 2 × ℝ => mkPoint p.1 p.2 := measurable_mkPoint
  have h2 : Measurable fun y : Space => ‖a y‖ₑ := ha.enorm
  show Measurable fun p : Euc 2 × ℝ => ‖a (mkPoint p.1 p.2)‖ₑ
  exact h2.comp h1

/-- The absolute heat integrand `G_θ(x - y)|a(y)|`. -/
def kabs (θ : ℝ) (a : Space → E) (x y : Space) : ℝ≥0∞ :=
  ENNReal.ofReal (kernel θ (x - y)) * ‖a y‖ₑ

theorem measurable_kabs (θ : ℝ) {a : Space → E} (ha : StronglyMeasurable a) (x : Space) :
    Measurable (kabs θ a x) := by
  have h1 : Measurable fun y : Space => ENNReal.ofReal (kernel θ (x - y)) :=
    ENNReal.measurable_ofReal.comp ((continuous_kernel θ).comp
      (continuous_const.sub continuous_id)).measurable
  have h2 : Measurable fun y : Space => ‖a y‖ₑ := ha.enorm
  exact h1.mul h2

/-- The vertical heat smoothing of the line profile, `∫ G^{(1)}_θ(s - z)|a(y', z)| dz`. -/
def vpsi (θ : ℝ) (a : Space → E) (y' : Euc 2) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ z : ℝ, ENNReal.ofReal (lineGauss θ (s - z)) * vline a y' z

theorem measurable_vpsi (θ : ℝ) {a : Space → E} (ha : StronglyMeasurable a) :
    Measurable (Function.uncurry (vpsi θ a)) := by
  have hf : Measurable fun q : (Euc 2 × ℝ) × ℝ => (q.1.1, q.2) :=
    measurable_fst.fst.prodMk measurable_snd
  have h2 := (measurable_vline ha).comp hf
  have h3 : Measurable fun q : (Euc 2 × ℝ) × ℝ => ENNReal.ofReal (lineGauss θ (q.1.2 - q.2)) :=
    ENNReal.measurable_ofReal.comp ((continuous_lineGauss θ).comp
      (continuous_fst.snd.sub continuous_snd)).measurable
  exact (h3.mul h2).lintegral_prod_right'

/-- **INF04 T12 `eLpNorm_average_mixed`** (B0740, tex 9188–9247). For `1 ≤ q < ∞`, `θ > 0` and
strongly measurable `a : ℝ³ → E`:
`‖e^{θΔ}a‖_{L^q(ℝ³)} ≤ ‖G^{(1)}_θ‖_{L^q(ℝ)} ‖a‖_{L^q_{x'}L¹_z}`. -/
theorem eLpNorm_average_mixed {q : ℝ} (hq : 1 ≤ q) {θ : ℝ} (hθ : 0 < θ) {a : Space → E}
    (ha : StronglyMeasurable a) :
    eLpNorm (average θ a) (ENNReal.ofReal q) volume ≤
      eLpNorm (lineGauss θ) (ENNReal.ofReal q) volume * mixedNormHV q a := by
  have hq0 : 0 < q := by linarith
  have hqp : ENNReal.ofReal q ≠ 0 := by simp; linarith
  have hqt : ENNReal.ofReal q ≠ ⊤ := ENNReal.ofReal_ne_top
  have hqr : (ENNReal.ofReal q).toReal = q := ENNReal.toReal_ofReal hq0.le
  have hAm : Measurable fun p : Euc 2 × ℝ => vline a p.1 p.2 := measurable_vline ha
  have hΨm : Measurable fun p : Euc 2 × ℝ => vpsi θ a p.1 p.2 := measurable_vpsi θ ha
  -- the dominating function
  have hpt : ∀ x, ‖average θ a x‖ₑ ≤ ∫⁻ y : Space, kabs θ a x y := by
    intro x
    have h1 : average θ a x = ∫ y : Space, kernel θ (x - y) • a y := by
      rw [average, ← integral_sub_left_eq_self (fun y => kernel θ y • a (x - y)) volume x]
      simp only [sub_sub_cancel]
    rw [h1]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun y => ?_
    rw [enorm_smul, Real.enorm_of_nonneg (kernel_nonneg hθ _)]
    rfl
  -- `Φ` along the splitting
  have hΦsplit : ∀ x' : Euc 2, ∀ s : ℝ, ∫⁻ y : Space, kabs θ a (mkPoint x' s) y =
      ∫⁻ w : Euc 2, ENNReal.ofReal (gaussKernel 2 θ w) * vpsi θ a (x' - w) s := by
    intro x' s
    have hm := measurable_kabs θ ha (mkPoint x' s)
    have h1 : ∫⁻ p : ℝ × Euc 2, kabs θ a (mkPoint x' s) (vsplit.symm p) =
        ∫⁻ y : Space, kabs θ a (mkPoint x' s) y :=
      (measurePreserving_vsplit.symm).lintegral_comp_emb vsplit.symm.measurableEmbedding _
    have h2 : ∫⁻ p : ℝ × Euc 2, kabs θ a (mkPoint x' s) (vsplit.symm p) =
        ∫⁻ y' : Euc 2, ∫⁻ z : ℝ, kabs θ a (mkPoint x' s) (vsplit.symm (z, y')) :=
      lintegral_prod_symm _ (hm.comp vsplit.symm.measurable).aemeasurable
    have h3 : ∀ y' : Euc 2, ∫⁻ z : ℝ, kabs θ a (mkPoint x' s) (vsplit.symm (z, y')) =
        ENNReal.ofReal (gaussKernel 2 θ (x' - y')) * vpsi θ a y' s := by
      intro y'
      rw [vpsi, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun z => ?_
      show ENNReal.ofReal (kernel θ (mkPoint x' s - mkPoint y' z)) * ‖a (mkPoint y' z)‖ₑ = _
      rw [kernel_mkPoint_sub hθ, ENNReal.ofReal_mul (Gaussian.gaussKernel_nonneg hθ _), mul_assoc]
      rfl
    rw [← h1, h2, lintegral_congr h3, ← lintegral_sub_left_eq_self (μ := volume)
      (fun y' : Euc 2 => ENNReal.ofReal (gaussKernel 2 θ (x' - y')) * vpsi θ a y' s) x']
    simp only [sub_sub_cancel]
  -- the `L^q` norm of `Φ` through the splitting
  have hΦL : ∫⁻ x : Space, (∫⁻ y : Space, kabs θ a x y) ^ q =
      ∫⁻ p : ℝ × Euc 2, (∫⁻ y : Space, kabs θ a (mkPoint p.2 p.1) y) ^ q := by
    have h1 := (measurePreserving_vsplit.symm).lintegral_comp_emb vsplit.symm.measurableEmbedding
      (fun x : Space => (∫⁻ y : Space, kabs θ a x y) ^ q)
    rw [← h1]
    rfl
  -- horizontal Minkowski
  have hH : (∫⁻ p : ℝ × Euc 2, (∫⁻ y : Space, kabs θ a (mkPoint p.2 p.1) y) ^ q) ^ (1 / q) ≤
      (∫⁻ p : ℝ × Euc 2, vpsi θ a p.2 p.1 ^ q) ^ (1 / q) := by
    have hFm : Measurable (Function.uncurry fun (p : ℝ × Euc 2) (w : Euc 2) =>
        ENNReal.ofReal (gaussKernel 2 θ w) * vpsi θ a (p.2 - w) p.1) := by
      have hf : Measurable fun q : (ℝ × Euc 2) × Euc 2 => (q.1.2 - q.2, q.1.1) :=
        (continuous_fst.snd.sub continuous_snd).measurable.prodMk measurable_fst.fst
      have h1 : Measurable fun q : (ℝ × Euc 2) × Euc 2 => ENNReal.ofReal (gaussKernel 2 θ q.2) :=
        ENNReal.measurable_ofReal.comp
          ((Gaussian.continuous_gaussKernel θ).comp continuous_snd).measurable
      have h2 := hΨm.comp hf
      exact h1.mul h2
    have hM := NonUniqueEuler.Conv.lintegral_lintegral_rpow_le
      (μ := (volume : Measure (ℝ × Euc 2))) (ν := (volume : Measure (Euc 2)))
      hFm.aemeasurable hq
    simp_rw [hΦsplit]
    refine hM.trans (le_of_eq ?_)
    have hinner : ∀ w : Euc 2, (∫⁻ p : ℝ × Euc 2,
        (ENNReal.ofReal (gaussKernel 2 θ w) * vpsi θ a (p.2 - w) p.1) ^ q) ^ (1 / q) =
        ENNReal.ofReal (gaussKernel 2 θ w) * (∫⁻ p : ℝ × Euc 2, vpsi θ a p.2 p.1 ^ q) ^ (1 / q) := by
      intro w
      simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le]
      rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq0.le ENNReal.ofReal_ne_top),
        ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
        mul_one_div_cancel hq0.ne', ENNReal.rpow_one]
      congr 2
      -- translation invariance on `ℝ × ℝ²`
      have hm : Measurable fun p : ℝ × Euc 2 => vpsi θ a p.2 p.1 ^ q :=
        (hΨm.comp (measurable_snd.prodMk measurable_fst)).pow_const q
      have hm' : Measurable fun p : ℝ × Euc 2 => vpsi θ a (p.2 - w) p.1 ^ q :=
        (hΨm.comp (((continuous_snd.sub continuous_const).measurable :
          Measurable fun p : ℝ × Euc 2 => p.2 - w).prodMk measurable_fst)).pow_const q
      rw [show (volume : Measure (ℝ × Euc 2)) = (volume : Measure ℝ).prod volume from rfl,
        lintegral_prod _ hm'.aemeasurable, lintegral_prod _ hm.aemeasurable]
      refine lintegral_congr fun s => ?_
      exact lintegral_sub_right_eq_self (fun y' : Euc 2 => vpsi θ a y' s ^ q) w
    simp_rw [hinner]
    have hGm : Measurable fun w : Euc 2 => ENNReal.ofReal (gaussKernel 2 θ w) :=
      ENNReal.measurable_ofReal.comp (Gaussian.continuous_gaussKernel θ).measurable
    rw [lintegral_mul_const _ hGm, lintegral_ofReal_gaussKernel_two hθ, one_mul]
  -- vertical Minkowski on each line
  set g : ℝ≥0∞ := (∫⁻ s : ℝ, ENNReal.ofReal (lineGauss θ s) ^ q) ^ (1 / q) with hg
  have hV : ∀ y' : Euc 2, ∫⁻ s : ℝ, vpsi θ a y' s ^ q ≤ (g * ∫⁻ z : ℝ, vline a y' z) ^ q := by
    intro y'
    have hFm : Measurable (Function.uncurry fun (s z : ℝ) =>
        ENNReal.ofReal (lineGauss θ (s - z)) * vline a y' z) := by
      have hf2 : Measurable fun q : ℝ × ℝ => (y', q.2) := measurable_const.prodMk measurable_snd
      have h2 := hAm.comp hf2
      have h1 : Measurable fun q : ℝ × ℝ => ENNReal.ofReal (lineGauss θ (q.1 - q.2)) :=
        ENNReal.measurable_ofReal.comp ((continuous_lineGauss θ).comp
          (continuous_fst.sub continuous_snd)).measurable
      exact h1.mul h2
    have hM := NonUniqueEuler.Conv.lintegral_lintegral_rpow_le
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) hFm.aemeasurable hq
    have hline : ∀ z : ℝ, (∫⁻ s : ℝ, (ENNReal.ofReal (lineGauss θ (s - z)) * vline a y' z) ^ q) ^ (1 / q)
        = g * vline a y' z := by
      intro z
      simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le]
      have hmz : Measurable fun s : ℝ => ENNReal.ofReal (lineGauss θ (s - z)) ^ q :=
        (ENNReal.measurable_ofReal.comp ((continuous_lineGauss θ).measurable.comp
          (measurable_id.sub_const z))).pow_const q
      rw [lintegral_mul_const _ hmz, ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
        ← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne', ENNReal.rpow_one, hg]
      congr 2
      exact lintegral_sub_right_eq_self (fun s : ℝ => ENNReal.ofReal (lineGauss θ s) ^ q) z
    simp_rw [hline] at hM
    have hAz : Measurable fun z : ℝ => vline a y' z := by
      have hf3 : Measurable fun z : ℝ => (y', z) := measurable_const.prodMk measurable_id
      have h := hAm.comp hf3
      exact h
    rw [lintegral_const_mul _ hAz] at hM
    rw [one_div, ENNReal.rpow_inv_le_iff hq0] at hM
    exact hM
  have hJ : ∫⁻ p : ℝ × Euc 2, vpsi θ a p.2 p.1 ^ q ≤
      g ^ q * ∫⁻ y' : Euc 2, (∫⁻ z : ℝ, vline a y' z) ^ q := by
    have hm : Measurable fun p : ℝ × Euc 2 => vpsi θ a p.2 p.1 ^ q :=
      (hΨm.comp (measurable_snd.prodMk measurable_fst)).pow_const q
    rw [show (volume : Measure (ℝ × Euc 2)) = (volume : Measure ℝ).prod volume from rfl,
      lintegral_prod_symm _ hm.aemeasurable]
    have hmA : Measurable fun y' : Euc 2 => (∫⁻ z : ℝ, vline a y' z) ^ q :=
      hAm.lintegral_prod_right'.pow_const q
    rw [← lintegral_const_mul _ hmA]
    refine lintegral_mono fun y' => ?_
    rw [← ENNReal.mul_rpow_of_nonneg _ _ hq0.le]
    exact hV y'
  -- assembly
  have hgL : eLpNorm (lineGauss θ) (ENNReal.ofReal q) volume = g := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hqp hqt, hqr, hg]
    congr 1
    refine lintegral_congr fun s => ?_
    rw [Real.enorm_of_nonneg (lineGauss_nonneg hθ s)]
  have hstep : eLpNorm (average θ a) (ENNReal.ofReal q) volume ≤
      (∫⁻ x : Space, (∫⁻ y : Space, kabs θ a x y) ^ q) ^ (1 / q) := by
    refine (eLpNorm_mono_enorm (g := fun x => ∫⁻ y : Space, kabs θ a x y) fun x => ?_).trans
      (le_of_eq ?_)
    · rw [enorm_eq_self]; exact hpt x
    · rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hqp hqt, hqr]
      simp only [enorm_eq_self]
  refine hstep.trans ?_
  rw [hΦL, hgL]
  refine hH.trans ?_
  calc (∫⁻ p : ℝ × Euc 2, vpsi θ a p.2 p.1 ^ q) ^ (1 / q)
      ≤ (g ^ q * ∫⁻ y' : Euc 2, (∫⁻ z : ℝ, vline a y' z) ^ q) ^ (1 / q) :=
        ENNReal.rpow_le_rpow hJ (by positivity)
    _ = g * mixedNormHV q a := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          mul_one_div_cancel hq0.ne', ENNReal.rpow_one, mixedNormHV, one_div]
        rfl

/-- **INF04 T12 `eLpNorm_average_mixed`, explicit power** (B0740). For `1 ≤ q < ∞`, `θ > 0` and
strongly measurable `a`:
`‖e^{θΔ}a‖_{L^q} ≤ c_q θ^{-(1 - 1/q)/2} ‖a‖_{L^q_{x'}L¹_z}` with `c_q = ‖G^{(1)}_1‖_{L^q}`
(`Gaussian.derivLpConst 1 0 q`). -/
theorem eLpNorm_average_mixed_pow {q : ℝ} (hq : 1 ≤ q) {θ : ℝ} (hθ : 0 < θ) {a : Space → E}
    (ha : StronglyMeasurable a) :
    eLpNorm (average θ a) (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal (Gaussian.derivLpConst 1 0 (ENNReal.ofReal q) *
        θ ^ (-((0 : ℕ) : ℝ) / 2 - (1 : ℝ) / 2 * (1 - (1 / ENNReal.ofReal q).toReal))) *
        mixedNormHV q a := by
  rw [← eLpNorm_lineGauss_eq hθ]
  exact eLpNorm_average_mixed hq hθ ha

end UnforcedLeray.Heat
