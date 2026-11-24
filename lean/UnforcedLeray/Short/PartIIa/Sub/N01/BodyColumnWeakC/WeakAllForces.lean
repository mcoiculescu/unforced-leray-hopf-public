import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_2
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.SmoothForceDense
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.SmoothForceFields
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnWeakC.WeakSmoothForce

/-!
# `PartII-a:N01/9/2/2`: `weakAllForces`

Source `the November 2 reference manuscript`
lines 1650-1658, 1684-1689. Pass `WeakSmoothForce` (`N01/9/2/1`) from `SmoothForceSet c` to every
`g ∈ solenoidalHC 0 c` by density (`smoothForceDense`, `N01/9/1/1`), existence of smooth-force
energy representatives (`smoothForceFields`, `N01/9/1/2`), and continuity of the `𝓗`-pairings
against the compactly supported flat test `Φ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ENNReal ComplexConjugate InnerProductSpace ContDiff

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.B0220 (Profile HSpace measureH cellMeasure weightH QPeriodic)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIIb.Concrete (Chart)
open UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
  (IsEnergyFieldAE forcedIntegrand A0adj resolventTest zetaPhi
   memLp_test_A0adj isMeridTest_A0adj zetaPhiMeridTest
   resolventTestZetaPhi volCyl_ac_ageμ)
open UnforcedLeray.Short.PartIIIb.NearInst.Delta (velF)
open UnforcedLeray.Short.PartIIIb.NearInst.Masked (cellPtInv measurable_cellPtInv)
open UnforcedLeray.Short.IIIa (IsFlatTest flatIntegrand flatDt flatLap)

/-- The chart pairing kernel `(weightH x).toReal • ⟪w x, velF c f x⟫` on `(0, ∞) × cell c`. -/
private def chartPairKernel (c : ℝ) (w f : Profile → MeridC) (x : Chart) : ℂ :=
  (weightH x).toReal • ∑ i : Fin 2, star (w x i) * velF c f x i

private theorem qPeriodic_cellPtInv {c : ℝ} {w : Profile → MeridC} (hw : QPeriodic c w)
    (x : Chart) : w (cellPtInv c x) = w x := by
  rcases x with ⟨s, q, η⟩
  unfold cellPtInv
  by_cases h : 0 < q
  · simp [h]
  · simp only [ite_eq_right_iff.2 (fun h' => False.elim (h h'))]
    exact hw (s, q, η)

/-- Unwinding an `H`-inner product `⟪W, f⟫` with a `c`-periodic representative `w` to the chart. -/
private theorem inner_unwind_chart {c : ℝ} (hc : 0 < c) {W : HSpace c MeridC}
    {w : Profile → MeridC} (hW : (W : Profile → MeridC) =ᵐ[measureH c] w)
    (hw_per : QPeriodic c w) (f : HSpace c MeridC) :
    IntegrableOn (chartPairKernel c w (f : Profile → MeridC))
        (Ioi (0 : ℝ) ×ˢ B0579.cell c) ∧
      inner ℂ W f = ∫ x in Ioi (0 : ℝ) ×ˢ B0579.cell c,
        chartPairKernel c w (f : Profile → MeridC) x := by
  have hcell_pos : ∀ᵐ a ∂(cellMeasure c), 0 < a.1 := by
    unfold cellMeasure
    filter_upwards [ae_restrict_mem (UnforcedLeray.B0220.measurableSet_cell c)] with a ha
    exact ha.1
  have hcell_ne : ∀ᵐ a ∂(cellMeasure c), weightH a ≠ 0 := by
    filter_upwards [hcell_pos] with a ha
    unfold weightH
    exact (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos ha _)).ne'
  have hw_meas : Measurable weightH := UnforcedLeray.B0220.measurable_weightH
  have hWcell : ∀ᵐ a ∂(cellMeasure c), W a = w a :=
    (withDensity_absolutelyContinuous' hw_meas.aemeasurable hcell_ne).ae_le hW
  let K : Profile → ℂ := fun a => (weightH a).toReal • inner ℂ (w a) (f a)
  have hpoint : (fun a => (weightH a).toReal • inner ℂ (W a) (f a)) =ᵐ[cellMeasure c] K := by
    filter_upwards [hWcell] with a h1
    simp only [K, h1]
  have hIntH : Integrable (fun a => inner ℂ (W a) (f a)) (measureH c) := L2.integrable_inner W f
  have hIntC : Integrable (fun a => (weightH a).toReal • inner ℂ (W a) (f a)) (cellMeasure c) := by
    have h := hIntH
    unfold measureH at h
    rw [integrable_withDensity_iff_integrable_smul' hw_meas
      (UnforcedLeray.B0226.ae_weightH_lt_top c)] at h
    exact h
  have hKint : Integrable K (cellMeasure c) := hIntC.congr hpoint
  have hmap : Measure.map (cellPtInv c)
      (volume.restrict (Ioi (0 : ℝ) ×ˢ B0579.cell c)) = cellMeasure c :=
    cellPtInv_map hc
  have hmp : MeasurePreserving (cellPtInv c)
      (volume.restrict (Ioi (0 : ℝ) ×ˢ B0579.cell c)) (cellMeasure c) :=
    ⟨measurable_cellPtInv c, hmap⟩
  have hfun : chartPairKernel c w (f : Profile → MeridC) = K ∘ cellPtInv c := by
    funext x
    simp only [Function.comp_apply, K, chartPairKernel]
    have hw_eq : w (cellPtInv c x) = w x := qPeriodic_cellPtInv hw_per x
    have hwt : weightH (cellPtInv c x) = weightH x := by
      rcases x with ⟨s, q, η⟩
      rfl
    rw [hwt, hw_eq]
    congr 1
    simp only [PiLp.inner_apply, RCLike.inner_apply, velF]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, mul_comm]
  refine ⟨?_, ?_⟩
  · rw [IntegrableOn, hfun]
    exact (hmp.integrable_comp hKint.aestronglyMeasurable).2 hKint
  · rw [L2.inner_def]
    have e1 : ∫ a, inner ℂ (W a) (f a) ∂(measureH c) =
        ∫ a, (weightH a).toReal • inner ℂ (W a) (f a) ∂(cellMeasure c) := by
      unfold measureH
      exact integral_withDensity_eq_integral_toReal_smul hw_meas
        (UnforcedLeray.B0226.ae_weightH_lt_top c) _
    have e2 : ∫ a, (weightH a).toReal • inner ℂ (W a) (f a) ∂(cellMeasure c) =
        ∫ a, K a ∂(cellMeasure c) := integral_congr_ae hpoint
    have e3 : ∫ a, K a ∂(cellMeasure c) =
        ∫ x, K (cellPtInv c x)
          ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ B0579.cell c)) := by
      rw [← hmap]
      exact integral_map (measurable_cellPtInv c).aemeasurable
        (by rw [hmap]; exact hKint.aestronglyMeasurable)
    rw [e1, e2, e3]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => (congrFun hfun x).symm)

private theorem chartPairKernel_zetaPhi {c : ℝ} (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ)
    (f : Profile → MeridC) {x : Chart} (hx : 0 < x.1) :
    chartPairKernel c (zetaPhi Φ) f x =
      ∑ i : Fin 2, (velF c f x i / (x.1 : ℂ)) * (Φ x.1 x.2 i : ℂ) := by
  have hw : (weightH x).toReal = x.1 ^ (-(3 / 2 : ℝ)) := by
    unfold weightH
    exact ENNReal.toReal_ofReal (Real.rpow_nonneg hx.le _)
  have hk : x.1 ^ (-(3 / 2 : ℝ)) * Real.sqrt x.1 = x.1⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx, show (-(3 / 2 : ℝ) + 1 / 2) = -1 by norm_num,
      Real.rpow_neg_one]
  have hkC : ((x.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * ((Real.sqrt x.1 : ℝ) : ℂ) = ((x.1 : ℂ))⁻¹ := by
    rw [← Complex.ofReal_mul, hk, Complex.ofReal_inv]
  unfold chartPairKernel zetaPhi
  rw [hw]
  simp only [Fin.sum_univ_two, Complex.real_smul, Complex.star_def, Complex.conj_ofReal]
  push_cast
  linear_combination (((Φ x.1 x.2 0 : ℝ) : ℂ) * velF c f x 0 +
    ((Φ x.1 x.2 1 : ℝ) : ℂ) * velF c f x 1) * hkC

private theorem chartPairKernel_resolvent {c ν : ℝ} (μ : ℂ) (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ)
    (hΦ : IsFlatTest c Φ) (B : Profile → MeridC) {x : Chart} (hx : 0 < x.1) :
    chartPairKernel c (fun p => star μ • zetaPhi Φ p - A0adj ν (zetaPhi Φ) p) B x =
      flatIntegrand ν μ (fun _ _ _ => 0) (fun _ _ _ => 0) (velF c B) Φ x := by
  have hw : (weightH x).toReal = x.1 ^ (-(3 / 2 : ℝ)) := by
    unfold weightH
    exact ENNReal.toReal_ofReal (Real.rpow_nonneg hx.le _)
  have hk : x.1 ^ (-(3 / 2 : ℝ)) * Real.sqrt x.1 = x.1⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx, show (-(3 / 2 : ℝ) + 1 / 2) = -1 by norm_num,
      Real.rpow_neg_one]
  have hkC : ((x.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * ((Real.sqrt x.1 : ℝ) : ℂ) = ((x.1 : ℂ))⁻¹ := by
    rw [← Complex.ofReal_mul, hk, Complex.ofReal_inv]
  have hx0 : (x.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx.ne'
  have hres0 := resolventTestZetaPhi c ν 0 Φ hΦ x hx
  have hA0 : ∀ i : Fin 2, A0adj ν (zetaPhi Φ) x i =
      ((Real.sqrt x.1 * (x.1 * flatDt Φ x.1 x.2 i + ν * x.1 * flatLap Φ x.1 x.2 i) : ℝ) : ℂ) := by
    intro i
    have hi := congr_arg (fun v : MeridC => v i) hres0
    simp only [resolventTest, zero_smul, zero_sub, PiLp.neg_apply, zero_mul] at hi
    push_cast at hi ⊢
    linear_combination -hi
  unfold chartPairKernel flatIntegrand
  rw [hw]
  simp only [Fin.sum_univ_two, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, hA0, zetaPhi,
    map_sub, map_mul, Complex.real_smul, Complex.star_def, Complex.conj_conj,
    Complex.conj_ofReal, Complex.ofReal_zero, zero_mul, mul_zero, sub_zero, add_zero]
  push_cast
  linear_combination
    (velF c B x 0 * (μ * (Φ x.1 x.2 0 : ℂ) - (x.1 : ℂ) * (flatDt Φ x.1 x.2 0 : ℂ) -
      (ν : ℂ) * (x.1 : ℂ) * (flatLap Φ x.1 x.2 0 : ℂ)) +
     velF c B x 1 * (μ * (Φ x.1 x.2 1 : ℂ) - (x.1 : ℂ) * (flatDt Φ x.1 x.2 1 : ℂ) -
      (ν : ℂ) * (x.1 : ℂ) * (flatLap Φ x.1 x.2 1 : ℂ))) * hkC -
    (velF c B x 0 * (flatDt Φ x.1 x.2 0 : ℂ) +
     (ν : ℂ) * velF c B x 0 * (flatLap Φ x.1 x.2 0 : ℂ) +
     velF c B x 1 * (flatDt Φ x.1 x.2 1 : ℂ) +
     (ν : ℂ) * velF c B x 1 * (flatLap Φ x.1 x.2 1 : ℂ)) * (inv_mul_cancel₀ hx0)

/-- For any force `g ∈ 𝓗` and any a.e. representatives `F` of `g` and `b` of `velF c (R₀ g)`,
the forced integrand against a flat test `Φ` is integrable on `(0, ∞) × cell c` and its integral
equals the `𝓗`-pairing `⟪μ* Z - A₀* Z, R₀ g⟫ - ⟪Z, g⟫`. -/
private theorem forcedIntegrand_eq_inner {c ν : ℝ} (hc : 0 < c) (μ : ℂ)
    (g : HSpace c MeridC) {F : Profile → MeridC} (hgF : (g : Profile → MeridC) =ᵐ[measureH c] F)
    {b : Chart → Fin 2 → ℂ}
    (hb : b =ᵐ[ageμ c (-3 / 2)] velF c (UnforcedLeray.B0225.R0 hc ν μ g : HSpace c MeridC))
    {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ} (hΦ : IsFlatTest c Φ)
    {Z AZ : HSpace c MeridC}
    (hZ : (Z : Profile → MeridC) =ᵐ[measureH c] zetaPhi Φ)
    (hAZ : (AZ : Profile → MeridC) =ᵐ[measureH c] A0adj ν (zetaPhi Φ)) :
    IntegrableOn (forcedIntegrand ν μ (fun _ _ _ => 0)
        (fun x i => velF c F x i / (x.1 : ℂ)) b Φ) (Ioi (0 : ℝ) ×ˢ B0579.cell c) ∧
      ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
        forcedIntegrand ν μ (fun _ _ _ => 0)
          (fun x i => velF c F x i / (x.1 : ℂ)) b Φ p =
        inner ℂ (star μ • Z - AZ) (UnforcedLeray.B0225.R0 hc ν μ g) - inner ℂ Z g := by
  let B : HSpace c MeridC := UnforcedLeray.B0225.R0 hc ν μ g
  let S : Set Chart := Ioi (0 : ℝ) ×ˢ B0579.cell c
  have hSm : MeasurableSet S := measurableSet_Ioi.prod (B0579.measurableSet_cell c)
  have hpos : ∀ᵐ x ∂((volume : Measure Chart).restrict S), 0 < x.1 :=
    (ae_restrict_iff' hSm).2 (Filter.Eventually.of_forall fun x hx => hx.1)
  have hζM : IsMeridTest c (zetaPhi Φ) := zetaPhiMeridTest c hc Φ hΦ
  let wRes : Profile → MeridC := fun p => star μ • zetaPhi Φ p - A0adj ν (zetaPhi Φ) p
  have hWRes_ae : ((star μ • Z - AZ : HSpace c MeridC) : Profile → MeridC) =ᵐ[measureH c] wRes := by
    filter_upwards [Lp.coeFn_sub (star μ • Z) AZ, Lp.coeFn_smul (star μ) Z, hZ, hAZ]
      with p h1 h2 h3 h4
    rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3, h4]
  have hwRes_per : QPeriodic c wRes := by
    intro p
    simp only [wRes, hζM.periodic p, (isMeridTest_A0adj ν hζM).periodic p]
  obtain ⟨hIntB_k, hValB_k⟩ := inner_unwind_chart hc hWRes_ae hwRes_per B
  obtain ⟨hIntG_k, hValG_k⟩ := inner_unwind_chart hc hZ hζM.periodic g
  have hcongrB : chartPairKernel c wRes (B : Profile → MeridC) =ᵐ[volume.restrict S]
      flatIntegrand ν μ (fun _ _ _ => 0) (fun _ _ _ => 0) (velF c (B : Profile → MeridC)) Φ := by
    filter_upwards [hpos] with x hx
    exact chartPairKernel_resolvent μ Φ hΦ (B : Profile → MeridC) hx
  have hcongrG : chartPairKernel c (zetaPhi Φ) (g : Profile → MeridC) =ᵐ[volume.restrict S]
      fun x : Chart => ∑ i : Fin 2, (velF c (g : Profile → MeridC) x i / (x.1 : ℂ)) * (Φ x.1 x.2 i : ℂ) := by
    filter_upwards [hpos] with x hx
    exact chartPairKernel_zetaPhi Φ (g : Profile → MeridC) hx
  have hIntB : IntegrableOn
      (flatIntegrand ν μ (fun _ _ _ => 0) (fun _ _ _ => 0) (velF c (B : Profile → MeridC)) Φ) S :=
    hIntB_k.congr hcongrB
  have hIntG : IntegrableOn
      (fun x : Chart => ∑ i : Fin 2, (velF c (g : Profile → MeridC) x i / (x.1 : ℂ)) * (Φ x.1 x.2 i : ℂ)) S :=
    hIntG_k.congr hcongrG
  have hValB : inner ℂ (star μ • Z - AZ) B =
      ∫ x in S, flatIntegrand ν μ (fun _ _ _ => 0) (fun _ _ _ => 0) (velF c (B : Profile → MeridC)) Φ x := by
    rw [hValB_k]
    exact integral_congr_ae hcongrB
  have hValG : inner ℂ Z g =
      ∫ x in S, ∑ i : Fin 2, (velF c (g : Profile → MeridC) x i / (x.1 : ℂ)) * (Φ x.1 x.2 i : ℂ) := by
    rw [hValG_k]
    exact integral_congr_ae hcongrG
  have hInt_gB : IntegrableOn
      (forcedIntegrand ν μ (fun _ _ _ => 0)
        (fun x i => velF c (g : Profile → MeridC) x i / (x.1 : ℂ))
        (velF c (B : Profile → MeridC)) Φ) S :=
    hIntB.sub hIntG
  have hVal_gB : ∫ x in S,
      forcedIntegrand ν μ (fun _ _ _ => 0)
        (fun x i => velF c (g : Profile → MeridC) x i / (x.1 : ℂ))
        (velF c (B : Profile → MeridC)) Φ x =
      inner ℂ (star μ • Z - AZ) B - inner ℂ Z g := by
    change ∫ x in S, (flatIntegrand ν μ (fun _ _ _ => 0) (fun _ _ _ => 0)
        (velF c (B : Profile → MeridC)) Φ x -
      ∑ i : Fin 2, (velF c (g : Profile → MeridC) x i / (x.1 : ℂ)) * (Φ x.1 x.2 i : ℂ)) = _
    rw [integral_sub hIntB hIntG, ← hValB, ← hValG]
  have hac := volCyl_ac_ageμ hc (-3 / 2)
  have hb_ae : b =ᵐ[volume.restrict S] velF c (B : Profile → MeridC) := hac.ae_le hb
  have hgF_ae : velF c (g : Profile → MeridC) =ᵐ[volume.restrict S] velF c F :=
    hac.ae_le (velFAeTransfer c hc (g : Profile → MeridC) F hgF)
  have hcongr_final : forcedIntegrand ν μ (fun _ _ _ => 0)
        (fun x i => velF c (g : Profile → MeridC) x i / (x.1 : ℂ))
        (velF c (B : Profile → MeridC)) Φ =ᵐ[volume.restrict S]
      forcedIntegrand ν μ (fun _ _ _ => 0)
        (fun x i => velF c F x i / (x.1 : ℂ)) b Φ := by
    filter_upwards [hb_ae, hgF_ae] with x hbx hgx
    unfold forcedIntegrand flatIntegrand
    dsimp only
    rw [hbx, hgx]
  refine ⟨hInt_gB.congr hcongr_final, ?_⟩
  rw [← hVal_gB]
  exact integral_congr_ae hcongr_final.symm

theorem weakAllForces : UnforcedLeray.Short.PartIIa.N01.WeakAllForces := by
  intro c ν hc hν μ hμ g hg b _Gr hb _hE Φ hΦ
  have hζM : IsMeridTest c (zetaPhi Φ) := zetaPhiMeridTest c hc Φ hΦ
  obtain ⟨hZm, hAm⟩ := memLp_test_A0adj c ν (zetaPhi Φ) hζM
  let Z : HSpace c MeridC := hZm.toLp (zetaPhi Φ)
  have hZ : (Z : Profile → MeridC) =ᵐ[measureH c] zetaPhi Φ := hZm.coeFn_toLp
  let AZ : HSpace c MeridC := hAm.toLp (A0adj ν (zetaPhi Φ))
  have hAZ : (AZ : Profile → MeridC) =ᵐ[measureH c] A0adj ν (zetaPhi Φ) := hAm.coeFn_toLp
  have hD := smoothForceDense c hc g hg
  have hex : ∀ k : ℕ, ∃ y ∈ SmoothForceSet c, dist g y < 1 / ((k : ℝ) + 1) := fun k =>
    Metric.mem_closure_iff.1 hD _ (by positivity)
  choose gk hgk hdist using hex
  have hlim : Tendsto gk atTop (𝓝 g) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    refine squeeze_zero (fun k => dist_nonneg) (fun k => ?_) this
    rw [dist_comm]
    exact (hdist k).le
  have hk_zero : ∀ k : ℕ,
      inner ℂ (star μ • Z - AZ) (UnforcedLeray.B0225.R0 hc ν μ (gk k)) - inner ℂ Z (gk k) = 0 := by
    intro k
    obtain ⟨_, Fk, hFk, hgkFk⟩ := hgk k
    obtain ⟨bk, Gk, hbk, hEk⟩ := _root_.smoothForceFields c ν hc hν μ hμ (gk k) (hgk k)
    have hws := weakSmoothForce c ν hc hν μ hμ Fk hFk (gk k) hgkFk bk Gk hbk hEk Φ hΦ
    have heq := (forcedIntegrand_eq_inner hc μ (gk k) hgkFk hbk hΦ hZ hAZ).2
    rw [← heq, hws.2]
  have hcont : Continuous (fun y : HSpace c MeridC =>
      inner ℂ (star μ • Z - AZ) (UnforcedLeray.B0225.R0 hc ν μ y) - inner ℂ Z y) :=
    (continuous_const.inner (UnforcedLeray.B0225.R0 hc ν μ).continuous).sub
      (continuous_const.inner continuous_id)
  have htend : Tendsto (fun k : ℕ =>
      inner ℂ (star μ • Z - AZ) (UnforcedLeray.B0225.R0 hc ν μ (gk k)) - inner ℂ Z (gk k))
      atTop (𝓝 (inner ℂ (star μ • Z - AZ) (UnforcedLeray.B0225.R0 hc ν μ g) - inner ℂ Z g)) :=
    (hcont.tendsto g).comp hlim
  have hlim_zero :
      inner ℂ (star μ • Z - AZ) (UnforcedLeray.B0225.R0 hc ν μ g) - inner ℂ Z g = 0 :=
    tendsto_nhds_unique htend
      ((tendsto_const_nhds (x := (0 : ℂ))).congr fun k => (hk_zero k).symm)
  obtain ⟨hInt, hVal⟩ :=
    forcedIntegrand_eq_inner hc μ g (Filter.EventuallyEq.rfl) hb hΦ hZ hAZ
  exact ⟨hInt, hVal.trans hlim_zero⟩

end UnforcedLeray.Short.PartIIa.N01
