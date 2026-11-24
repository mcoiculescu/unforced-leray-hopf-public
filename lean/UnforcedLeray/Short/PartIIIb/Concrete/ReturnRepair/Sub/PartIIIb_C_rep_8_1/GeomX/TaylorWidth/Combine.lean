import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.TaylorWidth.Bridge
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.N0

/-!
# `PartIII-b:C/rep/8/1/1/1/3/2`: combination of heat and Newton sides with `SepMeanFar`

Source `the November 2 reference manuscript`
lines 5415-5427, 5439-5443.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace TWBridge

open PhasePrim

/-- Every stress in `StrG c mZ ρb γ ν` has `OldThinFinite` when `3 / 2 < mZ` and `ν ≤ 1`. -/
theorem oldThinFinite_of_strG {c mZ ρb γ ν : ℝ} (hmZ : 3 / 2 < mZ) (hc : 0 < c)
    (hν : 0 < ν) (hν1 : ν ≤ 1) (T : StrG c mZ ρb γ ν) :
    OldThinFinite c ν (thinRep T) := by
  set γ' : ℝ := max γ 1
  have hγ' : 0 < γ' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hle : gainZ1Measure c mZ γ' ν ≤ gainZ1Measure c mZ γ ν := by
    unfold gainZ1Measure
    refine withDensity_mono (Eventually.of_forall fun p => ?_)
    apply ENNReal.ofReal_le_ofReal
    have hpos : 0 ≤ ginv γ' ν p := (slGinv_pos γ' ν p).le
    have hginv : ginv γ' ν p ≤ ginv γ ν p := by
      unfold ginv UnforcedLeray.Short.IIIa.gainG
      rw [inv_le_inv₀ (Real.exp_pos _) (Real.exp_pos _), Real.exp_le_exp]
      have hs : 0 ≤ max p.1 0 := le_max_right _ _
      have hd : 0 < 1 + ν * max p.1 0 := by positivity
      gcongr
      exact le_max_left γ 1
    exact pow_le_pow_left₀ hpos hginv 2
  have hf : MemLp ((WithLp.ofLp T).1) 2 (gainZ1Measure c mZ γ' ν) :=
    (Lp.memLp ((WithLp.ofLp T).1)).mono_measure hle
  set T' : StrG c mZ ρb γ' ν := WithLp.toLp 1 (hf.toLp ((WithLp.ofLp T).1), 0)
  obtain ⟨Cf, kf, hCf⟩ := sourceLN0 mZ γ' hmZ hγ'
  have hOTF' : OldThinFinite c ν (thinRep T') := (hCf c ν ρb hc hν hν1 T').1
  have hae : thinRep T' =ᵐ[oldMeasure c ν] thinRep T := by
    filter_upwards [(oldMeasureAC c mZ γ' ν hν).ae_le (MemLp.coeFn_toLp hf)] with p hp
    show Ten3.toMatrix (((hf.toLp ((WithLp.ofLp T).1)) : Chart → Ten3) p) =
      Ten3.toMatrix (((WithLp.ofLp T).1 : Chart → Ten3) p)
    rw [hp]
  exact ⟨hOTF'.1.congr hae, hOTF'.2.congr (hae.mono fun p hp => by dsimp only; rw [hp])⟩

theorem norm_reMap_comp_sub_le (W₁ W₂ V₁ V₂ : Space →L[ℝ] (Fin 3 → ℂ)) (ε : ℝ) :
    ‖reMap.comp (W₁ - W₂) - (ε ^ 3 : ℝ) • reMap.comp (V₁ - V₂)‖ ≤
      2 * (‖W₁ - (ε ^ 3 : ℝ) • V₁‖ + ‖W₂ - (ε ^ 3 : ℝ) • V₂‖) := by
  have heq : reMap.comp (W₁ - W₂) - (ε ^ 3 : ℝ) • reMap.comp (V₁ - V₂) =
      reMap.comp ((W₁ - (ε ^ 3 : ℝ) • V₁) - (W₂ - (ε ^ 3 : ℝ) • V₂)) := by
    ext v i
    simp only [sub_apply, ContinuousLinearMap.comp_apply,
      smul_apply, map_sub, map_smul, WithLp.ofLp_sub, WithLp.ofLp_smul,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [heq]
  calc ‖reMap.comp ((W₁ - (ε ^ 3 : ℝ) • V₁) - (W₂ - (ε ^ 3 : ℝ) • V₂))‖
      ≤ ‖reMap‖ * ‖(W₁ - (ε ^ 3 : ℝ) • V₁) - (W₂ - (ε ^ 3 : ℝ) • V₂)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 2 * (‖W₁ - (ε ^ 3 : ℝ) • V₁‖ + ‖W₂ - (ε ^ 3 : ℝ) • V₂‖) :=
        mul_le_mul opNorm_reMap_le (norm_sub_le _ _) (norm_nonneg _) (by norm_num)

end TWBridge

open PhasePrim TWBridge in
/-- **Uniform regime bound `TaylorWidthAt`** (source 5415-5427, 5439-5443): combines the heat
bridge `fderiv_zMid_eq`, the Newton bridge `NewtonBridge`, the moment bound `thinMoment_meanSrc_le`,
and the far-field comparison `SepMeanFar` at `μ` and `μ + 1`. -/
theorem taylorWidthAt_uniform_of (hF : SepMeanFar) (hN : TWBridge.NewtonBridge)
    (Pl : PlanarData) (K : ReturnConsts) (hC0 : 0 < K.C0) (hmZ : 3 / 2 < K.mZ) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧
      ∀ (L : ReturnLevel) (μ : ℝ), 0 < μ → μ ≤ 1 / 4 → L.ν ≤ 1 → L.ε ≤ 1 →
        TaylorWidthAt Pl K L μ C k := by
  obtain ⟨C, k, hC, hlf⟩ := hF Kmu Kmu_compact Kmu_re
  refine ⟨4 * Real.pi * (C + 1) * 16 ^ k, 2 * k, by have := Real.pi_pos; positivity, ?_⟩
  intro L μ hμ0 hμ14 hν1 hε1 T hAzi s hs η q
  have hν : 0 < L.ν := L.ν_pos
  have hε : 0 < L.ε := L.ε_pos
  have hc : 0 < cOf L.ν := cOf_pos hν
  have hs0 : 0 < s := hs.1
  have hss : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
  have hνs : L.ν * s ≤ 1 := by
    have := hs.2
    rw [le_div_iff₀ hν] at this
    linarith
  set N := oldN1 Pl K L T with hNdef
  have hcoef : 0 < 4 * Real.pi * (C + 1) * 16 ^ k * L.ν⁻¹ ^ (2 * k) *
      (L.ε ^ 4 * s ^ (5 / 2 : ℝ)) := by
    have := Real.pi_pos
    have : 0 < s ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hs0 _
    positivity
  by_cases hNtop : N = ⊤
  · rw [hNtop, ENNReal.mul_top (by simpa using hcoef)]
    exact le_top
  -- the receiver and observation point
  set τ : ℝ := NearInst.chartTau L.ε⁻¹ (s, (q, η))
  set y : Space := NearInst.chartY L.ε⁻¹ (s, (q, η)) with hy
  have hϱy : ϱ y = L.ε⁻¹ / Real.sqrt s := by
    rw [hy, GeomXAsm.chartY_eq_hpt, GeomXAsm.ϱ_hpt (by positivity)]
  set xo : Space := L.ε • y with hxo
  have hxo' : L.ε⁻¹ • xo = y := by
    rw [hxo, smul_smul, inv_mul_cancel₀ hε.ne', one_smul]
  have hxo0 : xo 0 = (Real.sqrt s)⁻¹ := by
    rw [hxo, hy, GeomXAsm.chartY_eq_hpt]
    show L.ε * (L.ε⁻¹ / Real.sqrt s) = _
    field_simp
  have hxo1 : xo 1 = 0 := by
    rw [hxo, hy, GeomXAsm.chartY_eq_hpt]
    show L.ε * 0 = _
    ring
  have hxr : Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) = (Real.sqrt s)⁻¹ := by
    rw [hxo0, hxo1, show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero, Real.sqrt_sq (by positivity)]
  have hyr : L.ε⁻¹ * Real.sqrt (5 * L.ν / 6) < ϱ y := by
    rw [hϱy, show L.ε⁻¹ / Real.sqrt s = L.ε⁻¹ * (Real.sqrt s)⁻¹ from div_eq_mul_inv _ _]
    apply mul_lt_mul_of_pos_left _ (inv_pos.2 hε)
    rw [← Real.sqrt_inv]
    apply Real.sqrt_lt_sqrt (by positivity)
    rw [← one_div, lt_div_iff₀ hs0]
    nlinarith
  have hxo_gap : 5 * L.ν / 6 < xo 0 ^ 2 + xo 1 ^ 2 := by
    rw [hxo0, hxo1, show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero, inv_pow, Real.sq_sqrt hs0.le,
      ← one_div, lt_div_iff₀ hs0]
    nlinarith
  have hρ : Real.sqrt (5 * L.ν / 6) < Real.sqrt L.ν :=
    Real.sqrt_lt_sqrt (by positivity) (by linarith)
  have hρi : Real.sqrt L.ν ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) := by
    rw [hxr, le_inv_comm₀ (Real.sqrt_pos.2 hν) hss, ← Real.sqrt_inv]
    apply Real.sqrt_le_sqrt
    exact hs.2.trans (le_of_eq (one_div _))
  -- heat and Newton bridges
  have hOTF : OldThinFinite (cOf L.ν) L.ν (thinRep T) :=
    oldThinFinite_of_strG hmZ hc hν hν1 T
  set G := meanSrc Pl K L T with hG
  have hheat := fderiv_zMid_eq Pl K L μ hμ0.le hC0 hmZ T τ y hyr
  have hnewt := hN Pl K L μ hμ0 hC0 T hAzi hOTF hNtop τ xo hxo_gap
  rw [hxo'] at hnewt
  set W₁ := fderiv ℝ (fun y => IIIa.sepW L.ν (μ : ℂ)
    (IIIa.thinSource L.ε (IIIa.meanLift G)) y 0) y
  set W₂ := fderiv ℝ (fun y => IIIa.sepW L.ν ((μ : ℂ) + 1)
    (IIIa.thinSource L.ε (IIIa.meanLift G)) y 0) y
  set V₁ := fderiv ℝ (IIIa.sepVmu0 (μ : ℂ) G) xo
  set V₂ := fderiv ℝ (IIIa.sepVmu0 ((μ : ℂ) + 1) G) xo
  have hdW : dWidth Pl K L μ T τ y ≤
      2 * (‖W₁ - (L.ε ^ 3 : ℝ) • V₁‖ + ‖W₂ - (L.ε ^ 3 : ℝ) • V₂‖) := by
    unfold dWidth
    rw [hheat, hnewt]
    exact norm_reMap_comp_sub_le W₁ W₂ V₁ V₂ L.ε
  -- the two SepMeanFar applications
  have hμK : ((μ : ℝ) : ℂ) ∈ Kmu := ⟨μ, ⟨hμ0.le, by linarith⟩, rfl⟩
  have hμ1K : ((μ : ℂ) + 1) ∈ Kmu := ⟨μ + 1, ⟨by linarith, by linarith⟩, by push_cast; rfl⟩
  have hGm : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => G w.1 w.2 i j :=
    meanSrc_measurable Pl K L T
  have hGs : ∀ x' Y, Real.sqrt (5 * L.ν / 6) < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → G x' Y = 0 :=
    meanSrc_support Pl K L T
  have hB₁ := hlf L.ν (cOf L.ν) L.ε (Real.sqrt (5 * L.ν / 6)) (Real.sqrt L.ν)
    hν hν1 hc hε hε1 (Real.sqrt_nonneg _) hρ (μ : ℂ) hμK G hGm hGs xo hρi
  have hB₂ := hlf L.ν (cOf L.ν) L.ε (Real.sqrt (5 * L.ν / 6)) (Real.sqrt L.ν)
    hν hν1 hc hε hε1 (Real.sqrt_nonneg _) hρ ((μ : ℂ) + 1) hμ1K G hGm hGs xo hρi
  rw [hxo'] at hB₁ hB₂
  -- combine constants and moments
  set M := 1 + L.ν⁻¹ + cOf L.ν + (Real.sqrt L.ν)⁻¹ +
    Real.sqrt L.ν * (Real.sqrt L.ν - Real.sqrt (5 * L.ν / 6))⁻¹ with hM
  have hM0 : 0 ≤ M := by
    have hd : 0 < Real.sqrt L.ν - Real.sqrt (5 * L.ν / 6) := by linarith
    have := hc.le
    positivity
  have hMle : M ^ k ≤ 16 ^ k * L.ν⁻¹ ^ (2 * k) := by
    rw [pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ hM0 (by have := poly_le L.ν hν hν1; rw [← hM] at this; linarith) k
  have hrad : Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) ^ (-5 : ℝ) = s ^ (5 / 2 : ℝ) := by
    rw [hxr, rpow_neg_five s hs0]
  set a := C * M ^ k * L.ε ^ 4 * s ^ (5 / 2 : ℝ) with ha
  have ha0 : 0 ≤ a := by
    have : 0 < s ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hs0 _
    rw [ha]
    positivity
  have hGN : IIIa.thinMoment (cOf L.ν) (IIIa.meanLift G) ≤ ENNReal.ofReal Real.pi * N :=
    thinMoment_meanSrc_le Pl K L hC0 T
  have hBi : ∀ E : ℝ≥0∞, E ≤ ENNReal.ofReal (C * M ^ k * L.ε ^ 4 *
        Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) ^ (-5 : ℝ)) * IIIa.thinMoment (cOf L.ν) (IIIa.meanLift G) →
      E ≤ ENNReal.ofReal (a * Real.pi) * N := by
    intro E hE
    refine hE.trans ?_
    rw [hrad, ← ha, ENNReal.ofReal_mul ha0, mul_assoc]
    exact mul_le_mul_right hGN _
  have ha_le : a * Real.pi * 4 ≤ 4 * Real.pi * (C + 1) * 16 ^ k * L.ν⁻¹ ^ (2 * k) *
      (L.ε ^ 4 * s ^ (5 / 2 : ℝ)) := by
    have hs52 : 0 < s ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hs0 _
    have hpi := Real.pi_pos
    have h1 : C * M ^ k ≤ (C + 1) * (16 ^ k * L.ν⁻¹ ^ (2 * k)) :=
      mul_le_mul (by linarith) hMle (pow_nonneg hM0 _) (by linarith)
    have h2 : 0 ≤ L.ε ^ 4 * s ^ (5 / 2 : ℝ) := by positivity
    calc a * Real.pi * 4 = 4 * Real.pi * (C * M ^ k) * (L.ε ^ 4 * s ^ (5 / 2 : ℝ)) := by
          rw [ha]; ring
      _ ≤ 4 * Real.pi * ((C + 1) * (16 ^ k * L.ν⁻¹ ^ (2 * k))) * (L.ε ^ 4 * s ^ (5 / 2 : ℝ)) := by
          gcongr
      _ = _ := by ring
  calc ENNReal.ofReal (dWidth Pl K L μ T τ y)
      ≤ ENNReal.ofReal (2 * (‖W₁ - (L.ε ^ 3 : ℝ) • V₁‖ + ‖W₂ - (L.ε ^ 3 : ℝ) • V₂‖)) :=
        ENNReal.ofReal_le_ofReal hdW
    _ = 2 * (‖W₁ - (L.ε ^ 3 : ℝ) • V₁‖ₑ + ‖W₂ - (L.ε ^ 3 : ℝ) • V₂‖ₑ) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _),
          ofReal_norm, ofReal_norm]
        norm_num
    _ ≤ 2 * (ENNReal.ofReal (a * Real.pi) * N + ENNReal.ofReal (a * Real.pi) * N) := by
        gcongr
        · exact hBi _ hB₁
        · exact hBi _ hB₂
    _ = ENNReal.ofReal (a * Real.pi * 4) * N := by
        rw [← two_mul, ← mul_assoc, ← mul_assoc,
          ENNReal.ofReal_mul (mul_nonneg ha0 Real.pi_pos.le)]
        congr 1
        rw [mul_comm, ← mul_assoc]
        norm_num
        ring
    _ ≤ ENNReal.ofReal (4 * Real.pi * (C + 1) * 16 ^ k * L.ν⁻¹ ^ (2 * k) *
          (L.ε ^ 4 * s ^ (5 / 2 : ℝ))) * N := by
        gcongr

alias TWBridge.taylorWidthAt_uniform_of := taylorWidthAt_uniform_of

end UnforcedLeray.Short.PartIIIb.Concrete
