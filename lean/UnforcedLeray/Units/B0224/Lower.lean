import UnforcedLeray.Units.B0224.Operators
import UnforcedLeray.Lib.HeatR3.Continuity

/-!
# B0224 helper: the norm of `T_0(t)` is exactly `e^{-t/4}`

Blueprint unit B0224 (label `eq:st18-t00117`), `paper/main.tex` lines 3370–3379: "Both have
norm `e^{-t/4}` on `H`". The upper bound is `norm_T0_le`; this file proves the lower bound
(scoping note INF04-INF05 R11: "add a lower bound by a concentrating test function").

Test functions: `F(s, q, η) = 1_{(δ, 2δ]}(s) V(η)` with `V ∈ L²(ℝ; E)` independent of `q`
(`prodFun`). Then `T_0(t)F = H_θ D F` and `‖DF‖ = e^{-t/4}‖F‖`, while on `DF`, which is supported
in ages `s ≤ 2δe^t`, the heat time `θ_t(s) = νs(1 - e^{-t})` is small; on `q`-independent
functions the cylinder heat is the heat in `η` (`fiberHeat_prodFun`), whose strong continuity at
time `0` is `Heat.tendsto_heatLp_sub` (INF04 T3, here on `L²(ℝ)` with `ι y = y₁`). Hence
`‖T_0(t)F‖ ≥ ‖DF‖ - ‖(H_θ - 1)DF‖ ≥ (1 - κ)e^{-t/4}‖F‖` for every `κ > 0`
(`le_norm_T0`, needs `E ≠ 0`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace UnforcedLeray.B0224

open UnforcedLeray.Gaussian (Euc gaussKernel)
open UnforcedLeray.B0220

/-- The coordinate `y ↦ y₁` (the `η`-translations). -/
def etaι : Euc 2 →+ ℝ where
  toFun y := y 1
  map_zero' := by simp
  map_add' x y := by simp

theorem continuous_etaι : Continuous etaι := PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The heat in `η` alone, with the convention `e^{θΔ} = id` for `θ ≤ 0`. -/
def heat1 (θ : ℝ) (v : ℝ → E) : ℝ → E := if 0 < θ then Heat.heatConv etaι θ v else v

/-- `q`-independent profiles `F(s, q, η) = g(s) V(η)`. -/
def prodFun (g : ℝ → ℝ) (v : ℝ → E) (p : Profile) : E := g p.1 • v p.2.2

theorem fiberHeat_prodFun {c : ℝ} (θ : ℝ → ℝ) (g : ℝ → ℝ) (v : ℝ → E) (p : Profile) :
    fiberHeat c θ (prodFun g v) p = g p.1 • heat1 (θ p.1) v p.2.2 := by
  by_cases h : 0 < θ p.1
  · rw [fiberHeat_of_pos _ h]
    simp only [heat1, h, ↓reduceIte, Heat.heatConv, prodFun, periodize, Prod.snd_sub,
      planeι_apply]
    rw [← integral_smul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [smul_comm (g p.1)]
    rfl
  · rw [fiberHeat_of_nonpos _ (not_lt.1 h)]
    simp only [heat1, h, ↓reduceIte, prodFun, periodize]

theorem stronglyMeasurable_heat1 (θ : ℝ) {v : ℝ → E} (hv : StronglyMeasurable v) :
    StronglyMeasurable (heat1 θ v) := by
  by_cases h : 0 < θ
  · simp only [heat1, h, ↓reduceIte, Heat.heatConv]
    refine StronglyMeasurable.integral_prod_right' (f := fun q : ℝ × Euc 2 =>
      gaussKernel 2 θ q.2 • v (q.1 - etaι q.2)) ?_
    exact ((Gaussian.continuous_gaussKernel θ).comp continuous_snd).stronglyMeasurable.smul
      (hv.comp_measurable (measurable_fst.sub (continuous_etaι.measurable.comp measurable_snd)))
  · simp only [heat1, h, ↓reduceIte]
    exact hv

theorem dil_prodFun (a : ℝ) (g : ℝ → ℝ) (v : ℝ → E) :
    dil a (prodFun g v) = prodFun (fun s => g (a * s)) v := rfl

theorem stronglyMeasurable_prodFun {g : ℝ → ℝ} {v : ℝ → E} (hg : Measurable g)
    (hv : StronglyMeasurable v) : StronglyMeasurable (prodFun g v) :=
  (hg.comp measurable_fst).stronglyMeasurable.smul
    (hv.comp_measurable (measurable_snd.comp measurable_snd))

/-! ### Integrals of functions of `(s, η)` -/

theorem lintegral_strip_snd {c : ℝ} (hc : 0 < c) {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ x in strip c, φ x.2 = ENNReal.ofReal c * ∫⁻ η, φ η := by
  rw [strip, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ,
    lintegral_prod (fun x : ℝ × ℝ => φ x.2) (hφ.comp measurable_snd).aemeasurable]
  simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
  rw [mul_comm]

/-- An `H`-integral of a function of `(s, η)` only. -/
theorem lintegral_measureH_snd {c : ℝ} (hc : 0 < c) {Ψ : Profile → ℝ≥0∞} (hΨ : Measurable Ψ)
    (hq : ∀ p : Profile, Ψ p = Ψ (p.1, (0, p.2.2))) :
    ∫⁻ p, Ψ p ∂measureH c = ∫⁻ s in Ioi (0 : ℝ),
      ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) * (ENNReal.ofReal c * ∫⁻ η, Ψ (s, (0, η))) := by
  have hw : Measurable fun p : Profile => ENNReal.ofReal (p.1 ^ (-(3 / 2 : ℝ))) :=
    ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)
  rw [lintegral_measureH_eq _ hΨ, cellMeasure_eq_prod',
    lintegral_prod (fun p : Profile => ENNReal.ofReal (p.1 ^ (-(3 / 2 : ℝ))) * Ψ p)
      (hw.mul hΨ).aemeasurable]
  refine lintegral_congr fun s => ?_
  have hm : Measurable fun x : ℝ × ℝ => Ψ (s, x) := hΨ.comp measurable_prodMk_left
  dsimp only
  rw [lintegral_const_mul _ hm]
  congr 1
  have hφ : Measurable fun η : ℝ => Ψ (s, (0, η)) :=
    hΨ.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  rw [← lintegral_strip_snd hc hφ]
  exact lintegral_congr fun x => hq (s, x)

/-! ### The norm and the heat defect of a product -/

theorem lintegral_prodFun_sq {c : ℝ} (hc : 0 < c) {g : ℝ → ℝ} {v : ℝ → E} (hg : Measurable g)
    (hv : StronglyMeasurable v) :
    ∫⁻ p, ‖prodFun g v p‖ₑ ^ 2 ∂measureH c = ∫⁻ s in Ioi (0 : ℝ),
      ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) *
        (ENNReal.ofReal c * (‖g s‖ₑ ^ 2 * ∫⁻ η, ‖v η‖ₑ ^ 2)) := by
  rw [lintegral_measureH_snd hc ((stronglyMeasurable_prodFun hg hv).enorm.pow_const 2)
    (fun p => rfl)]
  refine lintegral_congr fun s => ?_
  simp only [prodFun, enorm_smul, mul_pow]
  rw [lintegral_const_mul _ (hv.enorm.pow_const 2)]

/-- The heat in `η` of `v ∈ L²(ℝ)` is the `L²(ℝ)` heat operator `Heat.heatLp`. -/
theorem coeFn_heatLp_eta [CompleteSpace E] (θ : ℝ) (V : Lp E 2 (volume : Measure ℝ)) :
    (Heat.heatLp etaι continuous_etaι θ V : ℝ → E) =ᵐ[volume] heat1 θ (V : ℝ → E) := by
  by_cases h : 0 < θ
  · simpa only [heat1, h, ↓reduceIte] using Heat.heatLp_rep etaι continuous_etaι h V
  · rw [Heat.heatLp_of_nonpos etaι continuous_etaι (not_lt.1 h)]
    simp only [heat1, h, ↓reduceIte, ContinuousLinearMap.id_apply]
    rfl

theorem enorm_sq_Lp (V : Lp E 2 (volume : Measure ℝ)) :
    ‖V‖ₑ ^ 2 = ∫⁻ η, ‖V η‖ₑ ^ 2 := by
  rw [Lp.enorm_def, eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem lintegral_heat1_sub_sq [CompleteSpace E] (θ : ℝ) (V : Lp E 2 (volume : Measure ℝ)) :
    ∫⁻ η, ‖heat1 θ (V : ℝ → E) η - V η‖ₑ ^ 2 =
      ‖Heat.heatLp etaι continuous_etaι θ V - V‖ₑ ^ 2 := by
  rw [enorm_sq_Lp]
  refine lintegral_congr_ae ?_
  filter_upwards [coeFn_heatLp_eta θ V, Lp.coeFn_sub (Heat.heatLp etaι continuous_etaι θ V) V]
    with η h1 h2
  rw [h2, Pi.sub_apply, h1]

/-- The heat defect of a product: `‖(H_θ - 1)(gV)‖²_H = ∫ s^{-3/2} c |g(s)|² ‖e^{θ(s)Δ}V - V‖²`. -/
theorem lintegral_fiberHeat_prodFun_sub_sq [CompleteSpace E] {c : ℝ} (hc : 0 < c)
    {θ : ℝ → ℝ} (hθ : Measurable θ) {g : ℝ → ℝ} (hg : Measurable g)
    (V : Lp E 2 (volume : Measure ℝ)) :
    ∫⁻ p, ‖fiberHeat c θ (prodFun g V) p - prodFun g V p‖ₑ ^ 2 ∂measureH c =
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) *
        (ENNReal.ofReal c * (‖g s‖ₑ ^ 2 *
          ‖Heat.heatLp etaι continuous_etaι (θ s) V - V‖ₑ ^ 2)) := by
  have hK := stronglyMeasurable_prodFun hg (Lp.stronglyMeasurable V)
  have hm : Measurable fun p : Profile =>
      ‖fiberHeat c θ (prodFun g V) p - prodFun g V p‖ₑ ^ 2 :=
    ((stronglyMeasurable_fiberHeat hθ hK).sub hK).enorm.pow_const 2
  rw [lintegral_measureH_snd hc hm (fun p => by simp only [fiberHeat_prodFun, prodFun])]
  refine lintegral_congr fun s => ?_
  congr 2
  simp only [fiberHeat_prodFun, prodFun, ← smul_sub, enorm_smul, mul_pow]
  have hm2 : Measurable fun η : ℝ => ‖heat1 (θ s) (V : ℝ → E) η - V η‖ₑ ^ 2 :=
    ((stronglyMeasurable_heat1 (θ s) (Lp.stronglyMeasurable V)).sub
      (Lp.stronglyMeasurable V)).enorm.pow_const 2
  rw [lintegral_const_mul _ hm2, lintegral_heat1_sub_sq]

end UnforcedLeray.B0224
