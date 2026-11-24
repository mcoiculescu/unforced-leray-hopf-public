import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_2
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.ClassicalGradBound.HeatIntGradSlice
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.ClassicalGradBound.HardyGradKernel
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.ClassicalGradBound.HSqNormEq
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.ClassicalGradBound.GradAgeSliceBound
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.SmoothClassicalEnergyBound
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.EnergyGradUnique
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.EnergyGradLimit
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.EnergyVelLimit
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.EnergyLimitLoc
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.EnergyLimitDivFree
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.EnergyLimitWeakGrad

/-!
# Explicit `Gamma` bound on the flat body gradient `Gr` (`PartII-a:N05/2/1`)

Source of record: `the November 2 reference manuscript`,
lines 1684–1689, 1794–1799.

Combines the proved `N01` energy-class and Hardy-kernel components with an explicit
`O(γs⁻¹ + 1)` bound on the Beta integral `∫₀¹ t^{Re μ - 3/4} (1 - t)^{-1/2} dt` for
`Re μ + 1/4 ≥ γs > 0` to obtain a universal constant `C_G ≥ 0` such that for every
`b : HSpace c MeridC`, the energy-class representative `(w_rep, Gr)` of `T0flat hc ν μ b`
satisfies
`ENNReal.ofReal (Real.sqrt c) * tCalNorm c Gr ≤ ENNReal.ofReal (C_G * Gamma^2 * ‖b‖)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa.N05_2_1Aux

open UnforcedLeray.Axi
open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226
open UnforcedLeray.Short.PartIIIb.Concrete (Chart)
open UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst (IsEnergyFieldAE forcedIntegrand)
open UnforcedLeray.Short.PartIIIb.NearInst.Delta (velF)
open UnforcedLeray.Short.IIIa (IsFlatTest tnorm2 tCalNorm)
open N05_2Aux

/-! ### 1. Explicit `O(γs⁻¹ + 1)` bound on the Hardy-Beta integral on `Ioo (0 : ℝ) 1` -/

/-- The Beta integral appearing in `N01.hardyGradKernel_of`. -/
def hardyBetaInt (a : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioo (0 : ℝ) 1,
    ENNReal.ofReal (t ^ (a - 1) * (1 - t) ^ (-(1 / 2 : ℝ))) * ENNReal.ofReal (t ^ (1 / 4 : ℝ))

theorem integrableOn_Ioc_rpow_gamma {γs : ℝ} (hγ : 0 < γs) :
    IntegrableOn (fun t : ℝ => t ^ (γs - 1)) (Ioc (0 : ℝ) 1) volume := by
  have hint : IntervalIntegrable (fun t : ℝ => t ^ (γs - 1)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  simpa [uIoc_of_le (zero_le_one' ℝ)] using hint.1

theorem setIntegral_Ioc_rpow_gamma {γs : ℝ} (hγ : 0 < γs) :
    ∫ t in Ioc (0 : ℝ) 1, t ^ (γs - 1) = γs⁻¹ := by
  have h1 : γs - 1 + 1 = γs := by ring
  rw [← intervalIntegral.integral_of_le (zero_le_one' ℝ),
    integral_rpow (Or.inl (by linarith)), h1, Real.one_rpow, Real.zero_rpow hγ.ne']
  ring

theorem lintegral_Ioo_rpow_gamma_le {γs : ℝ} (hγ : 0 < γs) :
    ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (2 * t ^ (γs - 1)) ≤ ENNReal.ofReal (2 * γs⁻¹) := by
  have hint : IntegrableOn (fun t : ℝ => 2 * t ^ (γs - 1)) (Ioc (0 : ℝ) 1) volume :=
    (integrableOn_Ioc_rpow_gamma hγ).const_mul 2
  have hnn : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)), 0 ≤ 2 * t ^ (γs - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact mul_nonneg zero_le_two (Real.rpow_nonneg ht.1.le _)
  calc ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (2 * t ^ (γs - 1))
      ≤ ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (2 * t ^ (γs - 1)) :=
        lintegral_mono_set Ioo_subset_Ioc_self
    _ = ENNReal.ofReal (∫ t in Ioc (0 : ℝ) 1, 2 * t ^ (γs - 1)) :=
        (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
    _ = ENNReal.ofReal (2 * γs⁻¹) := by
        rw [integral_const_mul, setIntegral_Ioc_rpow_gamma hγ]

theorem lintegral_Ioo_one_sub_rpow_neg_half_le :
    ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (2 * (1 - t) ^ (-(1 / 2 : ℝ))) ≤ ENNReal.ofReal 4 := by
  have hmp := Measure.measurePreserving_sub_left (volume : Measure ℝ) 1
  have hpre : (fun t : ℝ => 1 - t) ⁻¹' Ioo (0 : ℝ) 1 = Ioo (0 : ℝ) 1 := by
    ext t
    simp only [mem_preimage, mem_Ioo]
    constructor <;> intro h <;> constructor <;> linarith
  have heq : ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (2 * (1 - t) ^ (-(1 / 2 : ℝ))) =
      ∫⁻ u in Ioo (0 : ℝ) 1, ENNReal.ofReal (2 * u ^ (-(1 / 2 : ℝ))) := by
    conv_lhs => rw [← hpre]
    exact hmp.setLIntegral_comp_preimage_emb (MeasurableEquiv.subLeft (1 : ℝ)).measurableEmbedding
      (fun u : ℝ => ENNReal.ofReal (2 * u ^ (-(1 / 2 : ℝ)))) (Ioo (0 : ℝ) 1)
  have hint : IntegrableOn (fun u : ℝ => 2 * u ^ (-(1 / 2 : ℝ))) (Ioc (0 : ℝ) 1) volume :=
    integrableOn_Ioc_rpow_neg_half.const_mul 2
  have hnn : ∀ᵐ u ∂(volume.restrict (Ioc (0 : ℝ) 1)), 0 ≤ 2 * u ^ (-(1 / 2 : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact mul_nonneg zero_le_two (Real.rpow_nonneg hu.1.le _)
  rw [heq]
  calc ∫⁻ u in Ioo (0 : ℝ) 1, ENNReal.ofReal (2 * u ^ (-(1 / 2 : ℝ)))
      ≤ ∫⁻ u in Ioc (0 : ℝ) 1, ENNReal.ofReal (2 * u ^ (-(1 / 2 : ℝ))) :=
        lintegral_mono_set Ioo_subset_Ioc_self
    _ = ENNReal.ofReal (∫ u in Ioc (0 : ℝ) 1, 2 * u ^ (-(1 / 2 : ℝ))) :=
        (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
    _ = ENNReal.ofReal 4 := by
        rw [integral_const_mul, setIntegral_Ioc_rpow_neg_half]
        norm_num

theorem hardyBetaInt_le {a γs : ℝ} (hγ : 0 < γs) (haγ : γs ≤ a + 1 / 4) :
    hardyBetaInt a ≤ ENNReal.ofReal (2 * γs⁻¹ + 4) := by
  have hpt : ∀ t ∈ Ioo (0 : ℝ) 1,
      ENNReal.ofReal (t ^ (a - 1) * (1 - t) ^ (-(1 / 2 : ℝ))) * ENNReal.ofReal (t ^ (1 / 4 : ℝ)) ≤
        ENNReal.ofReal (2 * t ^ (γs - 1)) + ENNReal.ofReal (2 * (1 - t) ^ (-(1 / 2 : ℝ))) := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have ht1 : t < 1 := ht.2
    have h1t : 0 < 1 - t := by linarith
    have hmul : ENNReal.ofReal (t ^ (a - 1) * (1 - t) ^ (-(1 / 2 : ℝ))) *
          ENNReal.ofReal (t ^ (1 / 4 : ℝ)) =
        ENNReal.ofReal (t ^ (a - 3 / 4) * (1 - t) ^ (-(1 / 2 : ℝ))) := by
      rw [← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg ht0.le _) (Real.rpow_nonneg h1t.le _))]
      congr 1
      have hp : t ^ (a - 1) * t ^ (1 / 4 : ℝ) = t ^ (a - 3 / 4) := by
        rw [← Real.rpow_add ht0]
        congr 1
        ring
      calc t ^ (a - 1) * (1 - t) ^ (-(1 / 2 : ℝ)) * t ^ (1 / 4 : ℝ)
          = (t ^ (a - 1) * t ^ (1 / 4 : ℝ)) * (1 - t) ^ (-(1 / 2 : ℝ)) := by ring
        _ = t ^ (a - 3 / 4) * (1 - t) ^ (-(1 / 2 : ℝ)) := by rw [hp]
    rw [hmul, ← ENNReal.ofReal_add (mul_nonneg zero_le_two (Real.rpow_nonneg ht0.le _))
      (mul_nonneg zero_le_two (Real.rpow_nonneg h1t.le _))]
    refine ENNReal.ofReal_le_ofReal ?_
    have h_exp : t ^ (a - 3 / 4) ≤ t ^ (γs - 1) :=
      Real.rpow_le_rpow_of_exponent_ge ht0 ht1.le (by linarith)
    by_cases hhalf : t ≤ 1 / 2
    · have h14 : (1 / 4 : ℝ) ≤ 1 - t := by linarith
      have hr : (1 - t) ^ (-(1 / 2 : ℝ)) ≤ 2 := by
        calc (1 - t) ^ (-(1 / 2 : ℝ))
            ≤ (1 / 4 : ℝ) ^ (-(1 / 2 : ℝ)) :=
              Real.rpow_le_rpow_of_nonpos (by norm_num) h14 (by norm_num)
          _ = 2 := by
              rw [show (1 / 4 : ℝ) = (2 : ℝ) ^ (-2 : ℝ) by norm_num,
                ← Real.rpow_mul (by norm_num)]
              norm_num
      have hprod : t ^ (a - 3 / 4) * (1 - t) ^ (-(1 / 2 : ℝ)) ≤ 2 * t ^ (γs - 1) := by
        calc t ^ (a - 3 / 4) * (1 - t) ^ (-(1 / 2 : ℝ))
            ≤ t ^ (γs - 1) * 2 :=
              mul_le_mul h_exp hr (Real.rpow_nonneg h1t.le _) (Real.rpow_nonneg ht0.le _)
          _ = 2 * t ^ (γs - 1) := by ring
      linarith [Real.rpow_nonneg h1t.le (-(1 / 2 : ℝ))]
    · have hhalf' : (1 / 2 : ℝ) ≤ t := le_of_not_ge hhalf
      have ht_le2 : t ^ (a - 3 / 4) ≤ 2 := by
        calc t ^ (a - 3 / 4)
            ≤ t ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge ht0 ht1.le (by linarith)
          _ ≤ (1 / 2 : ℝ) ^ (-1 : ℝ) :=
              Real.rpow_le_rpow_of_nonpos (by norm_num) hhalf' (by norm_num)
          _ = 2 := by norm_num
      have hprod : t ^ (a - 3 / 4) * (1 - t) ^ (-(1 / 2 : ℝ)) ≤ 2 * (1 - t) ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right ht_le2 (Real.rpow_nonneg h1t.le _)
      linarith [Real.rpow_nonneg ht0.le (γs - 1)]
  have hm1 : Measurable (fun t : ℝ => ENNReal.ofReal (2 * t ^ (γs - 1))) := by fun_prop
  have hm2 : Measurable (fun t : ℝ => ENNReal.ofReal (2 * (1 - t) ^ (-(1 / 2 : ℝ)))) := by fun_prop
  calc hardyBetaInt a
      ≤ ∫⁻ t in Ioo (0 : ℝ) 1,
          (ENNReal.ofReal (2 * t ^ (γs - 1)) + ENNReal.ofReal (2 * (1 - t) ^ (-(1 / 2 : ℝ)))) :=
        setLIntegral_mono' measurableSet_Ioo hpt
    _ = (∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (2 * t ^ (γs - 1))) +
          ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (2 * (1 - t) ^ (-(1 / 2 : ℝ))) :=
        lintegral_add_left hm1 _
    _ ≤ ENNReal.ofReal (2 * γs⁻¹) + ENNReal.ofReal 4 :=
        add_le_add (lintegral_Ioo_rpow_gamma_le hγ) lintegral_Ioo_one_sub_rpow_neg_half_le
    _ = ENNReal.ofReal (2 * γs⁻¹ + 4) := by
        rw [← ENNReal.ofReal_add (by positivity) (by norm_num)]

/-! ### 2. Explicit Hardy kernel and smooth-force gradient bound -/

theorem hardyGradKernel_explicit {a ν γs : ℝ} (hγ : 0 < γs) (haγ : γs ≤ a + 1 / 4)
    (hν : 0 < ν) {Φ : ℝ → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-(1 / 2 : ℝ))) *
        (∫⁻ σ in Ioo (0 : ℝ) s, ENNReal.ofReal (N01.gradKernel a ν s σ) * Φ σ) ^ 2 ≤
      ENNReal.ofReal (ν⁻¹ * (2 * γs⁻¹ + 4) ^ 2) *
        ∫⁻ σ in Ioi (0 : ℝ), ENNReal.ofReal (σ ^ (-(3 / 2 : ℝ))) * Φ σ ^ 2 := by
  have hwm : Measurable fun t : ℝ => ENNReal.ofReal (t ^ (a - 1) * (1 - t) ^ (-(1 / 2 : ℝ))) := by
    fun_prop
  have h3' := N01.hardyMinkowski _ hwm Φ hΦ
  have hpt : ∀ s ∈ Ioi (0 : ℝ),
      ENNReal.ofReal (s ^ (-(1 / 2 : ℝ))) *
        (∫⁻ σ in Ioo (0 : ℝ) s, ENNReal.ofReal (N01.gradKernel a ν s σ) * Φ σ) ^ 2 =
      ENNReal.ofReal ν⁻¹ * (ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) *
        (∫⁻ t in Ioo (0 : ℝ) 1,
          ENNReal.ofReal (t ^ (a - 1) * (1 - t) ^ (-(1 / 2 : ℝ))) * Φ (t * s)) ^ 2) := by
    intro s hs
    have hs' : 0 < s := hs
    rw [N01.hardySubst a ν s hν hs' Φ hΦ, mul_pow]
    have key : s ^ (-(1 / 2 : ℝ)) * (ν ^ (-(1 / 2 : ℝ)) * s ^ (-(1 / 2 : ℝ))) ^ 2 =
        ν⁻¹ * s ^ (-(3 / 2 : ℝ)) := by
      have e1 : (ν ^ (-(1 / 2 : ℝ))) ^ 2 = ν⁻¹ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hν.le]; norm_num [Real.rpow_neg_one]
      have e2 : s ^ (-(1 / 2 : ℝ)) * (s ^ (-(1 / 2 : ℝ))) ^ 2 = s ^ (-(3 / 2 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hs'.le, ← Real.rpow_add hs']; norm_num
      calc _ = (ν ^ (-(1 / 2 : ℝ))) ^ 2 * (s ^ (-(1 / 2 : ℝ)) * (s ^ (-(1 / 2 : ℝ))) ^ 2) := by ring
        _ = _ := by rw [e1, e2]
    have hm : ENNReal.ofReal (s ^ (-(1 / 2 : ℝ))) *
        ENNReal.ofReal (ν ^ (-(1 / 2 : ℝ)) * s ^ (-(1 / 2 : ℝ))) ^ 2 =
        ENNReal.ofReal ν⁻¹ * ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) := by
      rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity), key]
    calc _ = (ENNReal.ofReal (s ^ (-(1 / 2 : ℝ))) *
          ENNReal.ofReal (ν ^ (-(1 / 2 : ℝ)) * s ^ (-(1 / 2 : ℝ))) ^ 2) *
          (∫⁻ t in Ioo (0 : ℝ) 1,
            ENNReal.ofReal (t ^ (a - 1) * (1 - t) ^ (-(1 / 2 : ℝ))) * Φ (t * s)) ^ 2 := by ring
      _ = _ := by rw [hm]; ring
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hbeta := hardyBetaInt_le hγ haγ
  calc ENNReal.ofReal ν⁻¹ * ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) *
          (∫⁻ t in Ioo (0 : ℝ) 1,
            ENNReal.ofReal (t ^ (a - 1) * (1 - t) ^ (-(1 / 2 : ℝ))) * Φ (t * s)) ^ 2
      ≤ ENNReal.ofReal ν⁻¹ * (hardyBetaInt a ^ 2 * ∫⁻ σ in Ioi (0 : ℝ),
          ENNReal.ofReal (σ ^ (-(3 / 2 : ℝ))) * Φ σ ^ 2) := by
        gcongr
        exact h3'
    _ ≤ ENNReal.ofReal ν⁻¹ * (ENNReal.ofReal (2 * γs⁻¹ + 4) ^ 2 * ∫⁻ σ in Ioi (0 : ℝ),
          ENNReal.ofReal (σ ^ (-(3 / 2 : ℝ))) * Φ σ ^ 2) := by
        gcongr
    _ = ENNReal.ofReal (ν⁻¹ * (2 * γs⁻¹ + 4) ^ 2) * ∫⁻ σ in Ioi (0 : ℝ),
          ENNReal.ofReal (σ ^ (-(3 / 2 : ℝ))) * Φ σ ^ 2 := by
        rw [← ENNReal.ofReal_pow (by positivity), ← mul_assoc,
          ← ENNReal.ofReal_mul (by positivity)]

/-- Universal constant `C0` from `heatIntGradSlice` gives an explicit smooth-force gradient bound. -/
theorem smoothForce_grad_lintegral_le :
    ∃ C0 : ℝ, 0 ≤ C0 ∧
      ∀ (c ν γs : ℝ) (hc : 0 < c), 0 < ν → 0 < γs → ∀ (μ : ℂ), γs ≤ μ.re + 1 / 4 →
        ∀ (g : HSpace c MeridC), g ∈ N01.SmoothForceSet c →
        ∀ (b : Chart → Fin 2 → ℂ) (G : Chart → Fin 2 → Fin 2 → ℂ),
        b =ᵐ[ageμ c (-3 / 2)] velF c (UnforcedLeray.B0225.R0 hc ν μ g : HSpace c MeridC) →
        IsEnergyFieldAE c b G →
        ∫⁻ p, ENNReal.ofReal (tnorm2 (G p) ^ 2) ∂(ageμ c (-1 / 2)) ≤
          ENNReal.ofReal (2 * c⁻¹ * C0 ^ 2 * (ν⁻¹ * (2 * γs⁻¹ + 4) ^ 2) * ‖g‖ ^ 2) := by
  obtain ⟨C0, hC0⟩ := heatIntGradSlice
  refine ⟨|C0|, abs_nonneg C0, ?_⟩
  intro c ν γs hc hν hγ μ hμγ g hg b G hb hE
  have hμ : 0 < μ.re + 1 / 4 := lt_of_lt_of_le hγ hμγ
  obtain ⟨hs, F, hF, hgF⟩ := hg
  have hrep := N01.smoothForceRepr c ν hc hν μ hμ g ⟨hs, F, hF, hgF⟩ F hF hgF
  have hcongr := N01.velFAeCongr c hc _ _ hrep
  obtain ⟨δ, hδ, hint⟩ := N01.r0Entrance c ν hc hν μ hμ (g : HSpace c MeridC)
  obtain ⟨Gr₀, hGr₀⟩ := N01.heatIntEnergy c ν hc hν μ hμ g ⟨hs, F, hF, hgF⟩ F hF hgF ⟨δ, hδ, by
    have hae : ∀ᵐ p ∂((ageμ c (-3 / 2)).restrict (Ioo 0 δ ×ˢ univ)),
        velF c (UnforcedLeray.B0225.R0 hc ν μ g : HSpace c MeridC) p
          = velF c (N01.smoothHeatInt c ν μ F) p := ae_restrict_of_ae hcongr
    have : ∫⁻ p, ENNReal.ofReal (UnforcedLeray.Short.IIIa.vnorm2 (velF c (N01.smoothHeatInt c ν μ F) p) ^ 2)
        ∂((ageμ c (-3 / 2)).restrict (Ioo 0 δ ×ˢ univ)) =
        ∫⁻ p, ENNReal.ofReal (UnforcedLeray.Short.IIIa.vnorm2
          (velF c (UnforcedLeray.B0225.R0 hc ν μ g : HSpace c MeridC) p) ^ 2)
        ∂((ageμ c (-3 / 2)).restrict (Ioo 0 δ ×ˢ univ)) :=
      lintegral_congr_ae (hae.mono fun p hp => by simp only [hp])
    rw [this]; exact hint⟩
  have hG_eq_Gr0 : G =ᵐ[ageμ c (-1 / 2)] Gr₀ :=
    N01.energyGradUnique c hc b (velF c (N01.smoothHeatInt c ν μ F)) G Gr₀ hE hGr₀ (hb.trans hcongr)
  have hGr0_eq_class : Gr₀ =ᵐ[ageμ c (-1 / 2)] N01.gradOf (velF c (N01.smoothHeatInt c ν μ F)) :=
    N01.weakGradIsClassical c ν hc hν μ F hF Gr₀ hGr₀
  have hG_eq_class : G =ᵐ[ageμ c (-1 / 2)] N01.gradOf (velF c (N01.smoothHeatInt c ν μ F)) :=
    hG_eq_Gr0.trans hGr0_eq_class
  have hlint_eq : ∫⁻ p, ENNReal.ofReal (tnorm2 (G p) ^ 2) ∂(ageμ c (-1 / 2)) =
      ∫⁻ p, ENNReal.ofReal
        (tnorm2 (N01.gradOf (velF c (N01.smoothHeatInt c ν μ F)) p) ^ 2) ∂(ageμ c (-1 / 2)) :=
    lintegral_congr_ae (hG_eq_class.mono fun p hp => by simp only [hp])
  rw [hlint_eq]
  -- Now apply the slab decomposition and explicit Hardy bound
  set Φ : Fin 2 → ℝ → ℝ≥0∞ := fun i σ =>
    (∫⁻ x in UnforcedLeray.B0579.cell c, ‖F (σ, x) i‖ₑ ^ 2) ^ (1 / 2 : ℝ) with hΦ
  have hΦm : ∀ i, Measurable (Φ i) := by
    intro i
    have hFc : Continuous F := hF.1.continuous
    have hm : Measurable fun p : ℝ × (ℝ × ℝ) => ‖F p i‖ₑ ^ 2 := by
      have : Continuous fun p : ℝ × (ℝ × ℝ) => ‖F p i‖ₑ ^ 2 := by fun_prop
      exact this.measurable
    exact (hm.lintegral_prod_right' (ν := volume.restrict (UnforcedLeray.B0579.cell c))).pow_const _
  set M_i : Fin 2 → ℝ≥0∞ := fun i => ∫⁻ σ in Ioi (0 : ℝ), ENNReal.ofReal (σ ^ (-(3 / 2 : ℝ))) *
      ∫⁻ x in UnforcedLeray.B0579.cell c, ‖F (σ, x) i‖ₑ ^ 2 with hM_i
  have hΦsq : ∀ i σ, Φ i σ ^ 2 = ∫⁻ x in UnforcedLeray.B0579.cell c, ‖F (σ, x) i‖ₑ ^ 2 := by
    intro i σ
    simp only [hΦ]
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  set B_val : ℝ := ν⁻¹ * (2 * γs⁻¹ + 4) ^ 2
  have hB_pos : 0 ≤ B_val := by dsimp [B_val]; positivity
  have hC0_sq : |C0| ^ 2 = C0 ^ 2 := sq_abs C0
  have hcomp : ∀ i j : Fin 2, (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-(1 / 2 : ℝ))) *
          ∫⁻ x in UnforcedLeray.B0579.cell c,
            ‖fderiv ℝ (fun y : ℝ × ℝ => N01.smoothHeatInt c ν μ F (s, y) i) x
              (UnforcedLeray.B0579.dir j)‖ₑ ^ 2) ≤
        ENNReal.ofReal (|C0| ^ 2) * (ENNReal.ofReal B_val * M_i i) := by
    intro i j
    rw [hC0_sq]
    calc _ ≤ ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (C0 ^ 2) *
          (ENNReal.ofReal (s ^ (-(1 / 2 : ℝ))) *
            (∫⁻ σ in Ioo (0 : ℝ) s, ENNReal.ofReal (N01.gradKernel μ.re ν s σ) * Φ i σ) ^ 2) := by
          refine setLIntegral_mono' measurableSet_Ioi fun s hs_mem => ?_
          rw [mul_left_comm]
          gcongr
          exact hC0 c ν hc hν μ F hF s hs_mem i j
      _ = ENNReal.ofReal (C0 ^ 2) * ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-(1 / 2 : ℝ))) *
            (∫⁻ σ in Ioo (0 : ℝ) s, ENNReal.ofReal (N01.gradKernel μ.re ν s σ) * Φ i σ) ^ 2 :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (C0 ^ 2) * (ENNReal.ofReal B_val * ∫⁻ σ in Ioi (0 : ℝ),
            ENNReal.ofReal (σ ^ (-(3 / 2 : ℝ))) * Φ i σ ^ 2) := by
          gcongr
          exact hardyGradKernel_explicit hγ hμγ hν (hΦm i)
      _ = ENNReal.ofReal (C0 ^ 2) * (ENNReal.ofReal B_val * M_i i) := by
          have hMi : ∫⁻ σ in Ioi (0 : ℝ), ENNReal.ofReal (σ ^ (-(3 / 2 : ℝ))) * Φ i σ ^ 2 = M_i i :=
            lintegral_congr fun σ => by rw [hΦsq]
          rw [hMi]
  have hnorm := N01.hSqNormEq c hc g F hF hgF
  calc ∫⁻ p, ENNReal.ofReal
          (tnorm2 (N01.gradOf (velF c (N01.smoothHeatInt c ν μ F)) p) ^ 2) ∂(ageμ c (-1 / 2))
      ≤ ENNReal.ofReal c⁻¹ * ∑ i : Fin 2, ∑ j : Fin 2,
          ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-(1 / 2 : ℝ))) *
            ∫⁻ x in UnforcedLeray.B0579.cell c,
              ‖fderiv ℝ (fun y : ℝ × ℝ => N01.smoothHeatInt c ν μ F (s, y) i) x
                (UnforcedLeray.B0579.dir j)‖ₑ ^ 2 :=
        N01.gradAgeSliceBound c ν hc hν μ F hF
    _ ≤ ENNReal.ofReal c⁻¹ * ∑ i : Fin 2, ∑ _j : Fin 2,
          (ENNReal.ofReal (|C0| ^ 2) * (ENNReal.ofReal B_val * M_i i)) := by
        gcongr with i _ j _
        exact hcomp i j
    _ = ENNReal.ofReal (2 * c⁻¹ * |C0| ^ 2 * B_val) * ENNReal.ofReal (‖g‖ ^ 2) := by
        have e : ENNReal.ofReal (2 * c⁻¹ * |C0| ^ 2 * B_val) =
            2 * ENNReal.ofReal c⁻¹ * ENNReal.ofReal (|C0| ^ 2) * ENNReal.ofReal B_val := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
        rw [e, hnorm]
        simp only [Fin.sum_univ_two, hM_i]
        ring
    _ = ENNReal.ofReal (2 * c⁻¹ * |C0| ^ 2 * B_val * ‖g‖ ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity)]

/-! ### 3. Passage to general `b : HSpace c MeridC` and `Gamma^2` bound on `√c ‖Gr‖_𝒯` -/

theorem measurable_tnorm2_sq {X : Type*} [MeasurableSpace X] {G : X → Fin 2 → Fin 2 → ℂ}
    (hG : ∀ i j, Measurable (fun x => G x i j)) :
    Measurable (fun x => tnorm2 (G x) ^ 2) := by
  have heq : (fun x => tnorm2 (G x) ^ 2) = fun x => ∑ i : Fin 2, ∑ j : Fin 2, ‖G x i j‖ ^ 2 := by
    ext x
    exact N01.EnergyGradLimitAux.tnorm2_sq_eq (G x)
  rw [heq]
  exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
    (hG i j).norm.pow_const 2

theorem tnorm2_sq_le_two_mul_add (A B : Fin 2 → Fin 2 → ℂ) :
    tnorm2 B ^ 2 ≤ 2 * tnorm2 (fun i j => A i j - B i j) ^ 2 + 2 * tnorm2 A ^ 2 := by
  have h1 : ∀ i j : Fin 2, ‖B i j‖ ^ 2 ≤ 2 * ‖A i j - B i j‖ ^ 2 + 2 * ‖A i j‖ ^ 2 := fun i j => by
    have htri : ‖B i j‖ ≤ ‖A i j - B i j‖ + ‖A i j‖ := by
      calc ‖B i j‖ = ‖A i j - (A i j - B i j)‖ := by congr 1; ring
        _ ≤ ‖A i j‖ + ‖A i j - B i j‖ := norm_sub_le _ _
        _ = ‖A i j - B i j‖ + ‖A i j‖ := add_comm _ _
    have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith [sq_nonneg (‖A i j - B i j‖ - ‖A i j‖)]
  rw [N01.EnergyGradLimitAux.tnorm2_sq_eq, N01.EnergyGradLimitAux.tnorm2_sq_eq,
    N01.EnergyGradLimitAux.tnorm2_sq_eq]
  simp only [Fin.sum_univ_two]
  linarith [h1 0 0, h1 0 1, h1 1 0, h1 1 1]

/-- For every `b : HSpace c MeridC`, `w = T0flat hc ν μ b` admits an energy-class representative
`(w_rep, Gr)` solving the weak flat equation and satisfying
`ENNReal.ofReal (Real.sqrt c) * tCalNorm c Gr ≤ ENNReal.ofReal (C_G * Gamma^2 * ‖b‖)`. -/
theorem flat_body_energy_weak_and_gradBound :
    ∃ C_G : ℝ, 0 ≤ C_G ∧
      ∀ (ν c σ H1 L1 M γs : ℝ) (χ χ1 : Profile → ℝ),
        0 < ν → ∀ (hc : 0 < c), 0 < σ → σ ≤ H1 → 0 ≤ L1 → 0 < γs →
        ∀ μ : ℂ, ‖μ‖ ≤ M → γs ≤ μ.re + 1 / 4 →
        ∀ b : HSpace c MeridC,
          ∃ (w_rep : Chart → Fin 2 → ℂ) (Gr : Chart → Fin 2 → Fin 2 → ℂ),
            w_rep =ᵐ[ageμ c (-3 / 2)] velF c (T0flat hc ν μ b) ∧
            IsEnergyFieldAE c w_rep Gr ∧
            ENNReal.ofReal (Real.sqrt c) * tCalNorm c Gr ≤
              ENNReal.ofReal (C_G * Gamma ν c σ H1 L1 M γs χ χ1 ^ 2 * ‖b‖) ∧
            ∀ Φ, IsFlatTest c Φ →
              IntegrableOn (forcedIntegrand ν μ (fun _ _ _ => 0)
                  (fun x i => velF c (PepsC 0 c b : Profile → MeridC) x i / (x.1 : ℂ)) w_rep Φ)
                (Ioi (0 : ℝ) ×ˢ B0579.cell c) ∧
              ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
                forcedIntegrand ν μ (fun _ _ _ => 0)
                  (fun x i => velF c (PepsC 0 c b : Profile → MeridC) x i / (x.1 : ℂ)) w_rep Φ p = 0 := by
  obtain ⟨C0, hC0_nonneg, hSmoothBd⟩ := smoothForce_grad_lintegral_le
  refine ⟨12 * C0, by positivity, ?_⟩
  intro ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ μ hμM hμγ b
  have hM0 : 0 ≤ M := (norm_nonneg μ).trans hμM
  have hμ : 0 < μ.re + 1 / 4 := lt_of_lt_of_le hγ hμγ
  set g : HSpace c MeridC := PepsC 0 c b
  have hgs : g ∈ solenoidalHC 0 c := Submodule.starProjection_apply_mem _ _
  have hD := N01.smoothForceDense c hc g hgs
  have hex : ∀ k : ℕ, ∃ y ∈ N01.SmoothForceSet c, dist g y < 1 / ((k : ℝ) + 1) := fun k =>
    Metric.mem_closure_iff.1 hD _ (by positivity)
  choose gk hgk hdist using hex
  have hlim : Tendsto gk atTop (𝓝 g) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun _ => dist_nonneg) (fun k => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [dist_comm]; exact (hdist k).le
  have hfld := fun k => smoothForceFields c ν hc hν μ hμ (gk k) (hgk k)
  choose bk Gk hbk hEk using hfld
  obtain ⟨C_cau, hC_cau⟩ := smoothForceGradBound c ν hc hν μ hμ
  have hCauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k ≥ N, ∀ l ≥ N,
      ∫⁻ p, ENNReal.ofReal (tnorm2 (fun i j => Gk k p i j - Gk l p i j) ^ 2)
        ∂(ageμ c (-1 / 2)) < ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (4 * (|C_cau| + 1) / ε)
    refine ⟨N, fun k hk l hl => ?_⟩
    refine lt_of_le_of_lt
      (hC_cau (gk k) (hgk k) (gk l) (hgk l) _ _ _ _ (hbk k) (hEk k) (hbk l) (hEk l))
      ((ENNReal.ofReal_lt_ofReal_iff hε).2 ?_)
    have hk1 : 1 / ((k : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (N : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have hl1 : 1 / ((l : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (N : ℝ) ≤ l := by exact_mod_cast hl
      linarith
    have hnorm : ‖gk k - gk l‖ ≤ 2 / ((N : ℝ) + 1) := by
      have h1' := hdist k
      have h2' := hdist l
      have : ‖gk k - gk l‖ ≤ dist g (gk k) + dist g (gk l) := by
        calc ‖gk k - gk l‖ = dist (gk k) (gk l) := (dist_eq_norm _ _).symm
          _ ≤ dist (gk k) g + dist g (gk l) := dist_triangle _ _ _
          _ = _ := by rw [dist_comm (gk k) g]
      have : dist g (gk k) + dist g (gk l) ≤ 2 / ((N : ℝ) + 1) := by
        have e2 : 2 / ((N : ℝ) + 1) = 1 / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 1) := by ring
        linarith
      linarith
    have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hq : ‖gk k - gk l‖ ^ 2 ≤ 4 / ((N : ℝ) + 1) := by
      have hle : ‖gk k - gk l‖ ^ 2 ≤ (2 / ((N : ℝ) + 1)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      have hN1' : (1 : ℝ) ≤ (N : ℝ) + 1 := by have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith
      calc ‖gk k - gk l‖ ^ 2 ≤ (2 / ((N : ℝ) + 1)) ^ 2 := hle
        _ = 4 / ((N : ℝ) + 1) ^ 2 := by field_simp; norm_num
        _ ≤ 4 / ((N : ℝ) + 1) := by
            apply div_le_div_of_nonneg_left (by norm_num) hN1
            nlinarith
    have hcN : ε * ((N : ℝ) + 1) > 4 * (|C_cau| + 1) := by
      have := (div_lt_iff₀ hε).1 hN
      nlinarith
    calc C_cau * ‖gk k - gk l‖ ^ 2 ≤ |C_cau| * ‖gk k - gk l‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (le_abs_self C_cau) (sq_nonneg _)
      _ ≤ |C_cau| * (4 / ((N : ℝ) + 1)) := mul_le_mul_of_nonneg_left hq (abs_nonneg C_cau)
      _ < ε := by
          rw [← mul_div_assoc, div_lt_iff₀ hN1]
          nlinarith [abs_nonneg C_cau]
  obtain ⟨Gr, hGm, hGlim⟩ := energyGradLimit c hc Gk (fun k => (hEk k).gradMeasurable) hCauchy
  obtain ⟨w_rep, hbm, hw_rep, hblim, hbfin⟩ :=
    N01.energyVelLimit c ν hc hν μ hμ g gk hlim bk hbk (fun k => (hEk k).measurable)
  have hL : N01.EnergyL2Limit c bk Gk w_rep Gr := ⟨hblim, hGlim⟩
  have hE : IsEnergyFieldAE c w_rep Gr :=
    ⟨hbm, hGm, N01.energyLimitLoc c hc bk Gk w_rep Gr hEk hL hbm hGm,
      ⟨1, one_pos, lt_of_le_of_lt (lintegral_mono' Measure.restrict_le_self le_rfl) hbfin⟩,
      N01.energyLimitDivFree c hc bk Gk w_rep Gr hEk hL hbm,
      N01.energyLimitWeakGrad c hc bk Gk w_rep Gr hEk hL hbm hGm⟩
  refine ⟨w_rep, Gr, hw_rep, hE, ?_, fun Φ hΦ =>
    N01.weakAllForces c ν hc hν μ hμ g hgs w_rep Gr hw_rep hE Φ hΦ⟩
  -- Deduce the explicit bound on `Gr` from `hGlim` and `hSmoothBd`
  set K_op : ℝ := 2 * c⁻¹ * C0 ^ 2 * (ν⁻¹ * (2 * γs⁻¹ + 4) ^ 2)
  have hKop_nonneg : 0 ≤ K_op := by dsimp [K_op]; positivity
  have hGr_lint_le : ∀ k : ℕ,
      ∫⁻ p, ENNReal.ofReal (tnorm2 (Gr p) ^ 2) ∂(ageμ c (-1 / 2)) ≤
        2 * ∫⁻ p, ENNReal.ofReal (tnorm2 (fun i j => Gk k p i j - Gr p i j) ^ 2) ∂(ageμ c (-1 / 2)) +
          2 * ENNReal.ofReal (K_op * ‖gk k‖ ^ 2) := by
    intro k
    have hm_diff : Measurable (fun p : Chart =>
        ENNReal.ofReal (tnorm2 (fun i j => Gk k p i j - Gr p i j) ^ 2)) :=
      ENNReal.measurable_ofReal.comp
        (measurable_tnorm2_sq fun i j => ((hEk k).gradMeasurable i j).sub (hGm i j))
    have hm_Gk : Measurable (fun p : Chart => ENNReal.ofReal (tnorm2 (Gk k p) ^ 2)) :=
      ENNReal.measurable_ofReal.comp (measurable_tnorm2_sq (hEk k).gradMeasurable)
    calc ∫⁻ p, ENNReal.ofReal (tnorm2 (Gr p) ^ 2) ∂(ageμ c (-1 / 2))
        ≤ ∫⁻ p, (2 * ENNReal.ofReal (tnorm2 (fun i j => Gk k p i j - Gr p i j) ^ 2) +
            2 * ENNReal.ofReal (tnorm2 (Gk k p) ^ 2)) ∂(ageμ c (-1 / 2)) := by
          refine lintegral_mono fun p => ?_
          have hpt := tnorm2_sq_le_two_mul_add (Gk k p) (Gr p)
          have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by norm_num
          rw [h2, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          exact ENNReal.ofReal_le_ofReal hpt
      _ = 2 * (∫⁻ p, ENNReal.ofReal (tnorm2 (fun i j => Gk k p i j - Gr p i j) ^ 2) ∂(ageμ c (-1 / 2))) +
            2 * ∫⁻ p, ENNReal.ofReal (tnorm2 (Gk k p) ^ 2) ∂(ageμ c (-1 / 2)) := by
          rw [lintegral_add_left (hm_diff.const_mul 2), lintegral_const_mul _ hm_diff,
            lintegral_const_mul _ hm_Gk]
      _ ≤ 2 * (∫⁻ p, ENNReal.ofReal (tnorm2 (fun i j => Gk k p i j - Gr p i j) ^ 2) ∂(ageμ c (-1 / 2))) +
            2 * ENNReal.ofReal (K_op * ‖gk k‖ ^ 2) := by
          gcongr
          exact hSmoothBd c ν γs hc hν hγ μ hμγ (gk k) (hgk k) (bk k) (Gk k) (hbk k) (hEk k)
  have htend_rhs : Tendsto (fun k : ℕ =>
      2 * (∫⁻ p, ENNReal.ofReal (tnorm2 (fun i j => Gk k p i j - Gr p i j) ^ 2) ∂(ageμ c (-1 / 2))) +
        2 * ENNReal.ofReal (K_op * ‖gk k‖ ^ 2))
      atTop (𝓝 (0 + 2 * ENNReal.ofReal (K_op * ‖g‖ ^ 2))) := by
    refine Tendsto.add ?_ ?_
    · simpa using ENNReal.Tendsto.const_mul hGlim (Or.inr ENNReal.ofNat_ne_top)
    · refine ENNReal.Tendsto.const_mul ?_ (Or.inr ENNReal.ofNat_ne_top)
      refine ENNReal.tendsto_ofReal ?_
      exact ((continuous_const.mul (continuous_norm.pow 2)).tendsto g).comp hlim
  have hGr_lint : ∫⁻ p, ENNReal.ofReal (tnorm2 (Gr p) ^ 2) ∂(ageμ c (-1 / 2)) ≤
      ENNReal.ofReal (2 * K_op * ‖g‖ ^ 2) := by
    have h1 := ge_of_tendsto htend_rhs (Eventually.of_forall hGr_lint_le)
    rw [zero_add] at h1
    refine h1.trans (le_of_eq ?_)
    rw [mul_assoc (2 : ℝ) K_op, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  -- Convert `∫⁻ tnorm2 (Gr p)^2 ∂(ageμ c (-1/2))` into `ENNReal.ofReal (Real.sqrt c) * tCalNorm c Gr`
  set Gam := Gamma ν c σ H1 L1 M γs χ χ1
  have hG1 : 1 ≤ Gam := one_le_gamma_flat χ χ1 hν hc hσ hσH hL1 hγ hM0
  have hG0 : 0 ≤ Gam := by linarith
  have hν_G : ν⁻¹ ≤ Gam := by
    unfold Gam Gamma GammaBox
    have : 0 < c⁻¹ := inv_pos.2 hc
    have : 0 < σ⁻¹ := inv_pos.2 hσ
    have : 0 < γs⁻¹ := inv_pos.2 hγ
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hγ_G : γs⁻¹ ≤ Gam := by
    unfold Gam Gamma GammaBox
    have : 0 < ν⁻¹ := inv_pos.2 hν
    have : 0 < c⁻¹ := inv_pos.2 hc
    have : 0 < σ⁻¹ := inv_pos.2 hσ
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have h2γ4_G : 2 * γs⁻¹ + 4 ≤ 6 * Gam := by linarith
  have hKop_bound : c * (2 * K_op * ‖g‖ ^ 2) ≤ (12 * C0 * Gam ^ 2 * ‖b‖) ^ 2 := by
    have hg_le_b : ‖g‖ ^ 2 ≤ ‖b‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg g) (norm_PepsC0_apply_le c b) 2
    have hν_le_G2 : ν⁻¹ ≤ Gam ^ 2 := by
      calc ν⁻¹ ≤ Gam := hν_G
        _ ≤ Gam * Gam := le_mul_of_one_le_left hG0 hG1
        _ = Gam ^ 2 := (sq Gam).symm
    have hbeta_sq : (2 * γs⁻¹ + 4) ^ 2 ≤ 36 * Gam ^ 2 := by
      have h0 : 0 ≤ 2 * γs⁻¹ + 4 := by positivity
      calc (2 * γs⁻¹ + 4) ^ 2 ≤ (6 * Gam) ^ 2 := pow_le_pow_left₀ h0 h2γ4_G 2
        _ = 36 * Gam ^ 2 := by ring
    have hprod_G4 : ν⁻¹ * (2 * γs⁻¹ + 4) ^ 2 ≤ 36 * Gam ^ 4 := by
      calc ν⁻¹ * (2 * γs⁻¹ + 4) ^ 2
          ≤ Gam ^ 2 * (36 * Gam ^ 2) :=
            mul_le_mul hν_le_G2 hbeta_sq (by positivity) (sq_nonneg Gam)
        _ = 36 * Gam ^ 4 := by ring
    calc c * (2 * K_op * ‖g‖ ^ 2)
        = 4 * C0 ^ 2 * (ν⁻¹ * (2 * γs⁻¹ + 4) ^ 2) * ‖g‖ ^ 2 := by
          dsimp [K_op]
          field_simp [hc.ne']
          ring
      _ ≤ 4 * C0 ^ 2 * (36 * Gam ^ 4) * ‖b‖ ^ 2 := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hprod_G4 (by positivity))
            hg_le_b (sq_nonneg _) (by positivity)
      _ = (12 * C0 * Gam ^ 2 * ‖b‖) ^ 2 := by ring
  have hCal_sq : (ENNReal.ofReal (Real.sqrt c) * tCalNorm c Gr) ^ (2 : ℝ) =
      ENNReal.ofReal c * ∫⁻ p, ENNReal.ofReal (tnorm2 (Gr p) ^ 2) ∂(ageμ c (-1 / 2)) := by
    have heq := eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := ageμ c (-1 / 2))
      (f := fun x => tnorm2 (Gr x)) two_ne_zero ENNReal.ofNat_ne_top
    rw [ENNReal.toReal_ofNat] at heq
    have hpow := congrArg (fun x : ℝ≥0∞ => x ^ (2 : ℝ)) heq
    rw [← ENNReal.rpow_mul, show (1 / (2 : ℝ)) * 2 = 1 by norm_num, ENNReal.rpow_one] at hpow
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg c) (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_two, Real.sq_sqrt hc.le]
    congr 1
    rw [tCalNorm, hpow]
    refine lintegral_congr fun p => ?_
    have htn0 : 0 ≤ tnorm2 (Gr p) := by unfold tnorm2; exact Real.sqrt_nonneg _
    rw [Real.enorm_eq_ofReal htn0, ENNReal.ofReal_rpow_of_nonneg htn0 (by norm_num), Real.rpow_two]
  have hCal_sq_le : (ENNReal.ofReal (Real.sqrt c) * tCalNorm c Gr) ^ (2 : ℝ) ≤
      (ENNReal.ofReal (12 * C0 * Gam ^ 2 * ‖b‖)) ^ (2 : ℝ) := by
    rw [hCal_sq, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_two]
    calc ENNReal.ofReal c * ∫⁻ p, ENNReal.ofReal (tnorm2 (Gr p) ^ 2) ∂(ageμ c (-1 / 2))
        ≤ ENNReal.ofReal c * ENNReal.ofReal (2 * K_op * ‖g‖ ^ 2) := by gcongr
      _ = ENNReal.ofReal (c * (2 * K_op * ‖g‖ ^ 2)) := by
          rw [← ENNReal.ofReal_mul hc.le]
      _ ≤ ENNReal.ofReal ((12 * C0 * Gam ^ 2 * ‖b‖) ^ 2) :=
          ENNReal.ofReal_le_ofReal hKop_bound
  have hpow_half := ENNReal.rpow_le_rpow hCal_sq_le (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num,
    ENNReal.rpow_one, ENNReal.rpow_one] at hpow_half
  exact hpow_half

end UnforcedLeray.Short.PartIIa.N05_2_1Aux
