import UnforcedLeray.Short.PartIIb.Tasks.LocalInteractionComparison.RemainderBound.Pointwise
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T16_2
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_2
import UnforcedLeray.Lib.AxisymmetricB.Jv

/-!
# `PartII-b:T20/2`: `LocalInteractionRemainderBound` from the leaves `KOutChartAe`, `RawBoxJet`

Source of record: `the November 2 reference manuscript` (SP), lines 2007-2023.

`K_ε - K_0 = sB_0(T_ε - T_0) + s(B_ε - B_0)T_ε`; this file bounds the second term
`ϑ(g_ε - K_0 b_ε)`, `b_ε = T_εF`, `g_ε = K_εF`:
* `KOutChartAe` identifies `g_ε` a.e. with the chart formula `kOutChart` (`sB_εb_ε`);
* `hasWeakVec_dqOf` and uniqueness of weak derivatives identify `∂_qb_ε = Q_εb_ε + ε(2S + η∂_η + 1)b_ε`
  and `∂_ηb_ε` with the derivatives of the physical graph bound (`phys_graph_at_zero`);
* `RemBd.diff_norm_le` (exact chart substitution) bounds the difference pointwise by
  `22εsJ(1+|η|)(‖b‖ + ‖Sb‖ + ‖∂_ηb‖)`, `J` the chart jets of `v` and `He_z`;
* on the observation box `RawBoxJet` bounds `J ≤ CΓ^k`, `s ≥ σ` turns `∂_ηb` into `√s∂_ηb`, and
  the graph bound `‖b‖ + ‖Sb‖ + √ν‖√s∂_ηb‖ ≤ CΓ²‖F‖` closes the estimate.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete

namespace RemBd

/-- A property holding a.e. on the open strip `s > 0, |q| < c/2` holds `hMeas c r`-a.e. -/
theorem hMeas_ae_of_strip {c r : ℝ} (hc : 0 < c) {P : Coord → Prop}
    (h : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ (Ioo (-c / 2) (c / 2) ×ˢ (univ : Set ℝ)))),
      P x) :
    ∀ᵐ x ∂(hMeas c r), P x := by
  have hT : MeasurableSet (Ioi (0 : ℝ) ×ˢ (Ioo (-c / 2) (c / 2) ×ˢ (univ : Set ℝ))) :=
    measurableSet_Ioi.prod (measurableSet_Ioo.prod MeasurableSet.univ)
  have h1 : ∀ᵐ x ∂(volume : Measure Coord),
      x ∈ Ioi (0 : ℝ) ×ˢ (Ioo (-c / 2) (c / 2) ×ˢ (univ : Set ℝ)) → P x :=
    (ae_restrict_iff' hT).1 h
  have hnull : (volume : Measure Coord) {x : Coord | x.2.1 = -c / 2} = 0 := by
    have hset : {x : Coord | x.2.1 = -c / 2} =
        (univ : Set ℝ) ×ˢ (({-c / 2} : Set ℝ) ×ˢ (univ : Set ℝ)) := by
      ext x
      simp
    rw [hset, Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod,
      Measure.prod_prod]
    simp
  have h2 : ∀ᵐ x ∂(volume : Measure Coord), x.2.1 ≠ -c / 2 := by
    rw [ae_iff]
    simpa using hnull
  have hac : hMeas c r ≪ (volume : Measure Coord) := ageμ_ac_volume c (r / 2 - 5 / 2)
  have h3 : ∀ᵐ x ∂(hMeas c r), x ∈ Ioi (0 : ℝ) ×ˢ Axi.qCell c :=
    Axi.ae_ageμ_mem hc (r / 2 - 5 / 2)
  filter_upwards [hac.ae_le h1, hac.ae_le h2, h3] with x h1x h2x h3x
  apply h1x
  obtain ⟨hs, hq⟩ := h3x
  exact ⟨hs, ⟨lt_of_le_of_ne hq.1.1 (Ne.symm h2x), hq.1.2⟩, trivial⟩

/-- `H_p` bound of a profile dominated a.e. by `A(‖b‖ + ‖Sb‖ + ‖E‖)`. -/
theorem hNorm_le_three {c A : ℝ} (hA : 0 ≤ A) (G b Sb E : CProf)
    (hb : AEStronglyMeasurable b (hMeas c bgp)) (hS : AEStronglyMeasurable Sb (hMeas c bgp))
    (hE : AEStronglyMeasurable E (hMeas c bgp))
    (hpt : ∀ᵐ x ∂(hMeas c bgp), ‖G x‖ ≤ A * (‖b x‖ + ‖Sb x‖ + ‖E x‖)) :
    hNorm c bgp G ≤ ENNReal.ofReal A * (hNorm c bgp b + hNorm c bgp Sb + hNorm c bgp E) := by
  have hp1 : 1 ≤ ENNReal.ofReal bgp := by
    rw [ENNReal.one_le_ofReal]
    norm_num [bgp]
  let fb : Coord → ℝ := fun x => A • ‖b x‖
  let fS : Coord → ℝ := fun x => A • ‖Sb x‖
  let fE : Coord → ℝ := fun x => A • ‖E x‖
  have hfb : AEStronglyMeasurable fb (hMeas c bgp) := hb.norm.const_smul A
  have hfS : AEStronglyMeasurable fS (hMeas c bgp) := hS.norm.const_smul A
  have hfE : AEStronglyMeasurable fE (hMeas c bgp) := hE.norm.const_smul A
  have hae : ∀ᵐ x ∂(hMeas c bgp), ‖G x‖ ≤ ‖(fb + fS + fE) x‖ := by
    filter_upwards [hpt] with x hx
    have hnn : 0 ≤ (fb + fS + fE) x := by
      change 0 ≤ A * ‖b x‖ + A * ‖Sb x‖ + A * ‖E x‖
      positivity
    rw [Real.norm_of_nonneg hnn]
    change ‖G x‖ ≤ A * ‖b x‖ + A * ‖Sb x‖ + A * ‖E x‖
    linarith
  have h1 : hNorm c bgp G ≤ eLpNorm (fb + fS + fE) (ENNReal.ofReal bgp) (hMeas c bgp) :=
    eLpNorm_mono_ae hae
  have h2 : eLpNorm (fb + fS + fE) (ENNReal.ofReal bgp) (hMeas c bgp) ≤
      eLpNorm (fb + fS) (ENNReal.ofReal bgp) (hMeas c bgp) +
        eLpNorm fE (ENNReal.ofReal bgp) (hMeas c bgp) :=
    eLpNorm_add_le (hfb.add hfS) hfE hp1
  have h3 : eLpNorm (fb + fS) (ENNReal.ofReal bgp) (hMeas c bgp) ≤
      eLpNorm fb (ENNReal.ofReal bgp) (hMeas c bgp) +
        eLpNorm fS (ENNReal.ofReal bgp) (hMeas c bgp) :=
    eLpNorm_add_le hfb hfS hp1
  have e : ∀ g : CProf, eLpNorm (fun x => A • ‖g x‖) (ENNReal.ofReal bgp) (hMeas c bgp) =
      ENNReal.ofReal A * hNorm c bgp g := by
    intro g
    change eLpNorm (A • fun x => ‖g x‖) (ENNReal.ofReal bgp) (hMeas c bgp) = _
    rw [eLpNorm_const_smul, eLpNorm_norm, Real.enorm_eq_ofReal hA]
    rfl
  calc hNorm c bgp G ≤ eLpNorm fb (ENNReal.ofReal bgp) (hMeas c bgp) +
        eLpNorm fS (ENNReal.ofReal bgp) (hMeas c bgp) +
        eLpNorm fE (ENNReal.ofReal bgp) (hMeas c bgp) :=
        h1.trans (h2.trans (add_le_add h3 le_rfl))
    _ = ENNReal.ofReal A * (hNorm c bgp b + hNorm c bgp Sb + hNorm c bgp E) := by
        rw [e b, e Sb, e E, mul_add, mul_add]

/-- `1 ≤ Γ√y` from `1 ≤ Γ y`, `1 ≤ Γ`. -/
theorem one_le_mul_sqrt {Γ y : ℝ} (hΓ1 : 1 ≤ Γ) (hy0 : 0 ≤ y) (h : 1 ≤ Γ * y) :
    1 ≤ Γ * Real.sqrt y := by
  have hΓ0 : 0 ≤ Γ := by linarith
  have hss : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy0
  have hz0 : 0 ≤ Γ * Real.sqrt y := mul_nonneg hΓ0 (Real.sqrt_nonneg _)
  have hz2 : 1 ≤ (Γ * Real.sqrt y) * (Γ * Real.sqrt y) := by
    have e : (Γ * Real.sqrt y) * (Γ * Real.sqrt y) = Γ * (Γ * y) := by
      rw [show Γ * Real.sqrt y * (Γ * Real.sqrt y) = Γ * Γ * (Real.sqrt y * Real.sqrt y) by ring,
        hss]
      ring
    rw [e]
    nlinarith
  nlinarith

/-- The pointwise estimate on the observation box (SP 2015-2018). -/
theorem ptwise_bound {p : Params} {d dm dp : ℝ} (hbg : BgRegime p d dm dp)
    {Γ σ H₁ L₁ CJ : ℝ} {kJ : ℕ} (hΓ1 : 1 ≤ Γ) (hσi : σ⁻¹ ≤ Γ) (hH₁ : H₁ ≤ Γ) (hL₁ : L₁ ≤ Γ)
    (hσ0 : 0 < σ) (ϑ : ObsCut σ H₁ L₁ Γ) (hCJ : 0 < CJ)
    (hJb : ∀ x : Coord, 0 < x.1 → x.1 ≤ Γ → |x.2.2| ≤ Γ →
      chartJet (trainProf p) x + chartJet (raisedMerid p) x ≤ CJ * Γ ^ kJ)
    (bε gε gqε gηε Sb Qb Eb : CProf) (x : Coord) (hx0 : 0 < x.1)
    (hx1 : gε x = kOutChart p bε Qb Eb x) (hx2 : gqε x = dqOf p.ε bε Sb Qb Eb x)
    (hx3 : gηε x = Eb x) :
    ‖(ϑ.ϑ x : ℂ) • (gε x - flatK p.train bε gqε gηε x)‖ ≤
      (p.ε * (44 * CJ * Γ ^ (kJ + 4))) * (‖bε x‖ + ‖Sb x‖ + ‖sqrtS Eb x‖) := by
  have hΓ0 : 0 ≤ Γ := by linarith
  have hε0 : 0 ≤ p.ε := p.ε_pos.le
  have hN0 : 0 ≤ ‖bε x‖ + ‖Sb x‖ + ‖sqrtS Eb x‖ := by positivity
  by_cases hbox : x ∈ obsBox σ H₁ L₁
  · have hs_le : x.1 ≤ Γ := hbox.1.2.trans hH₁
    have hσs : σ ≤ x.1 := hbox.1.1
    have hη_le : |x.2.2| ≤ Γ :=
      abs_le.mpr ⟨by linarith [hbox.2.2.1], hbox.2.2.2.trans hL₁⟩
    have hJx := hJb x hx0 hs_le hη_le
    have hJ0 : 0 ≤ chartJet (trainProf p) x + chartJet (raisedMerid p) x :=
      add_nonneg (beF_chartJet_nonneg _ x) (beF_chartJet_nonneg _ x)
    have hϑ : ‖(ϑ.ϑ x : ℂ)‖ ≤ Γ := by
      have h := ϑ.bounded 0 (by norm_num) x
      rw [norm_iteratedFDeriv_zero] at h
      rwa [Complex.norm_real]
    have hfl : flatK p.train bε gqε gηε x = flatK p.train bε (dqOf p.ε bε Sb Qb Eb) Eb x := by
      unfold flatK
      rw [hx2, hx3]
    have hdiff := diff_norm_le hbg hx0 bε Sb Qb Eb
    rw [← hx1, ← hfl] at hdiff
    have hsq : ‖sqrtS Eb x‖ = Real.sqrt x.1 * ‖Eb x‖ := by
      simp only [sqrtS]
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    have hσΓ : 1 ≤ Γ * σ := by
      calc (1 : ℝ) = σ⁻¹ * σ := (inv_mul_cancel₀ hσ0.ne').symm
        _ ≤ Γ * σ := mul_le_mul_of_nonneg_right hσi hσ0.le
    have hΓs : 1 ≤ Γ * Real.sqrt x.1 :=
      one_le_mul_sqrt hΓ1 hx0.le (hσΓ.trans (mul_le_mul_of_nonneg_left hσs hΓ0))
    have hEb : ‖Eb x‖ ≤ Γ * ‖sqrtS Eb x‖ := by
      rw [hsq]
      have := norm_nonneg (Eb x)
      nlinarith
    have hN : ‖bε x‖ + ‖Sb x‖ + ‖Eb x‖ ≤ Γ * (‖bε x‖ + ‖Sb x‖ + ‖sqrtS Eb x‖) := by
      have := norm_nonneg (bε x)
      have := norm_nonneg (Sb x)
      nlinarith
    have hη1 : 1 + |x.2.2| ≤ 2 * Γ := by linarith
    have hstep : 22 * p.ε * x.1 * (chartJet (trainProf p) x + chartJet (raisedMerid p) x) *
          (1 + |x.2.2|) * (‖bε x‖ + ‖Sb x‖ + ‖Eb x‖) ≤
        22 * p.ε * Γ * (CJ * Γ ^ kJ) * (2 * Γ) *
          (Γ * (‖bε x‖ + ‖Sb x‖ + ‖sqrtS Eb x‖)) := by
      have hn0 : 0 ≤ ‖bε x‖ + ‖Sb x‖ + ‖Eb x‖ := by positivity
      have ha0 : 0 ≤ 1 + |x.2.2| := by positivity
      gcongr
    rw [norm_smul]
    calc ‖(ϑ.ϑ x : ℂ)‖ * ‖gε x - flatK p.train bε gqε gηε x‖
        ≤ Γ * (22 * p.ε * Γ * (CJ * Γ ^ kJ) * (2 * Γ) *
          (Γ * (‖bε x‖ + ‖Sb x‖ + ‖sqrtS Eb x‖))) :=
          mul_le_mul hϑ (hdiff.trans hstep) (norm_nonneg _) hΓ0
      _ = p.ε * (44 * CJ * Γ ^ (kJ + 4)) * (‖bε x‖ + ‖Sb x‖ + ‖sqrtS Eb x‖) := by ring
  · rw [ϑ.supp x hbox]
    simp only [Complex.ofReal_zero, zero_smul, norm_zero]
    positivity

/-- The closing `ℝ≥0∞` arithmetic: graph bound and `1 ≤ Γ√ν`. -/
theorem ennreal_close {Γ ν A B C' : ℝ} {X Y Z W Fn G : ℝ≥0∞} (hΓ0 : 0 ≤ Γ) (hA0 : 0 ≤ A)
    (hB0 : 0 ≤ B) (hΓν : 1 ≤ Γ * Real.sqrt ν)
    (hmain : G ≤ ENNReal.ofReal B * (X + Y + Z))
    (hgraph : X + Y + ENNReal.ofReal (Real.sqrt ν) * (W + Z) ≤ ENNReal.ofReal A * Fn)
    (hreal : B * (A * (1 + Γ)) ≤ C') : G ≤ ENNReal.ofReal C' * Fn := by
  have hXY : X + Y ≤ ENNReal.ofReal A * Fn := le_trans le_self_add hgraph
  have hZ' : ENNReal.ofReal (Real.sqrt ν) * Z ≤ ENNReal.ofReal A * Fn := by
    refine le_trans ?_ (le_trans le_add_self hgraph)
    gcongr
    exact le_add_self
  have hZ : Z ≤ ENNReal.ofReal Γ * (ENNReal.ofReal A * Fn) := by
    calc Z = 1 * Z := (one_mul _).symm
      _ ≤ ENNReal.ofReal (Γ * Real.sqrt ν) * Z := by
          gcongr
          exact ENNReal.one_le_ofReal.mpr hΓν
      _ = ENNReal.ofReal Γ * (ENNReal.ofReal (Real.sqrt ν) * Z) := by
          rw [ENNReal.ofReal_mul hΓ0, mul_assoc]
      _ ≤ ENNReal.ofReal Γ * (ENNReal.ofReal A * Fn) := by gcongr
  have hsum : X + Y + Z ≤ ENNReal.ofReal (A * (1 + Γ)) * Fn := by
    calc X + Y + Z ≤ ENNReal.ofReal A * Fn + ENNReal.ofReal Γ * (ENNReal.ofReal A * Fn) :=
          add_le_add hXY hZ
      _ = ENNReal.ofReal (A * (1 + Γ)) * Fn := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hΓ0, ← add_mul,
            ← ENNReal.ofReal_add hA0 (mul_nonneg hΓ0 hA0)]
          congr 2
          ring
  calc G ≤ ENNReal.ofReal B * (X + Y + Z) := hmain
    _ ≤ ENNReal.ofReal B * (ENNReal.ofReal (A * (1 + Γ)) * Fn) := by gcongr
    _ = ENNReal.ofReal (B * (A * (1 + Γ))) * Fn := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hB0]
    _ ≤ ENNReal.ofReal C' * Fn := by gcongr

end RemBd

open RemBd in
/-- **`LocalInteractionRemainderBound` from the identification leaf `KOutChartAe` and the
coefficient leaf `RawBoxJet`** (SP 2007-2023). -/
theorem localInteractionRemainderBound_of_leaves (hId : KOutChartAe) (hJ : RawBoxJet) :
    LocalInteractionRemainderBound := by
  obtain ⟨kJ, CJ, νJ, hCJ, hνJ, hJb⟩ := hJ
  obtain ⟨Cph, hCph, hph⟩ := phys_graph_at_zero
  refine ⟨kJ + 7, 88 * CJ * Cph, νJ, by positivity, hνJ, ?_⟩
  intro p d dm dp hbg hν hper Γ σ H₁ L₁ hΓ1 _hνΓ hνi hσi hH₁ hL₁ hσ0 ϑ F bε gε gqε gηε hF hbε
    hresp hgε hK hgq hgη
  obtain ⟨Sb, Qb, Eb, hS, hQ, hE, hmS, _hmQ, hmE, hgraph⟩ :=
    hph p d dm dp hbg hper Γ hΓ1 F bε hF hresp
  have hc : 0 < p.c := p.c_pos
  have hchart : ∀ᵐ x ∂(hMeas p.c bgp), gε x = kOutChart p bε Qb Eb x :=
    hMeas_ae_of_strip hc (hId p d dm dp hbg bε gε Qb Eb hbε hgε hQ hE hK)
  have hdq : gqε =ᵐ[hMeas p.c bgp] dqOf p.ε bε Sb Qb Eb :=
    hasWeakVec_unique_ae hc hgq (hasWeakVec_dqOf p.ε hS hQ hE)
  have heta : gηε =ᵐ[hMeas p.c bgp] Eb := hasWeakVec_unique_ae hc hgη hE
  have hpos : ∀ᵐ x ∂(hMeas p.c bgp), 0 < x.1 :=
    (Axi.ae_ageμ_mem hc (bgp / 2 - 5 / 2)).mono fun x hx => hx.1
  have hΓ0 : 0 ≤ Γ := by linarith
  have hpt : ∀ᵐ x ∂(hMeas p.c bgp),
      ‖(fun x => (ϑ.ϑ x : ℂ) • (gε x - flatK p.train bε gqε gηε x)) x‖ ≤
        (p.ε * (44 * CJ * Γ ^ (kJ + 4))) * (‖bε x‖ + ‖Sb x‖ + ‖sqrtS Eb x‖) := by
    filter_upwards [hchart, hdq, heta, hpos] with x hx1 hx2 hx3 hx0
    exact ptwise_bound hbg hΓ1 hσi hH₁ hL₁ hσ0 ϑ hCJ (hJb p d dm dp hbg hν Γ hΓ1 hνi)
      bε gε gqε gηε Sb Qb Eb x hx0 hx1 hx2 hx3
  have hB0 : 0 ≤ p.ε * (44 * CJ * Γ ^ (kJ + 4)) := by
    have := p.ε_pos
    positivity
  have hmain := hNorm_le_three hB0 _ bε Sb (sqrtS Eb) hbε.meas hmS hmE hpt
  have hΓν : 1 ≤ Γ * Real.sqrt p.ν := by
    have hν0 := p.ν_pos
    refine one_le_mul_sqrt hΓ1 hν0.le ?_
    calc (1 : ℝ) = p.ν⁻¹ * p.ν := (inv_mul_cancel₀ hν0.ne').symm
      _ ≤ Γ * p.ν := mul_le_mul_of_nonneg_right hνi hν0.le
  refine ennreal_close hΓ0 (by positivity) hB0 hΓν hmain hgraph ?_
  have h1 : 1 + Γ ≤ 2 * Γ := by linarith
  have hεMA : 0 ≤ p.ε * (44 * CJ * Γ ^ (kJ + 4)) * (Cph * Γ ^ 2) := by
    have := p.ε_pos
    positivity
  calc p.ε * (44 * CJ * Γ ^ (kJ + 4)) * (Cph * Γ ^ 2 * (1 + Γ))
      = (p.ε * (44 * CJ * Γ ^ (kJ + 4)) * (Cph * Γ ^ 2)) * (1 + Γ) := by ring
    _ ≤ (p.ε * (44 * CJ * Γ ^ (kJ + 4)) * (Cph * Γ ^ 2)) * (2 * Γ) :=
        mul_le_mul_of_nonneg_left h1 hεMA
    _ = 88 * CJ * Cph * Γ ^ (kJ + 7) * p.ε := by ring

end UnforcedLeray.Short.IIb

end
