import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.AsmYA
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.TaylorWidth

/-!
# `PartIII-b:C/rep/8/1/1/2/4/2`: `taylorWidthYA`

Source `the November 2 reference manuscript`
lines 5422-5427 (finite transverse width and heat-to-Newton error: Taylor's formula costs the first
transverse moment, strict radial gap along every Taylor segment, `s³ ≤ P_ν s^{5/2}` on the young
interval), 5400-5413 (gradient Newton kernel of degree `-5`, ratio of radii `≤ 1/√1.2`),
4764-4791 (`E`, `Σ_M`, `V_{μ,M}`, `W^mt = ε²V(εy)`).

Assembles `D.TaylorWidthYA` (the one-resolvent version of `D.TaylorWidth` for `Y_A = 𝒞_y W_μ`)
from the far-field mean comparison `sepMeanFar` (`GeomX/TaylorWidth/FarLeaf.lean`) and the
heat/Newton bridges (`GeomX/TaylorWidth/Bridge/*.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace TWBridgeYA

open PhasePrim TWBridge

section Regime

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)

/-- **(i) The heat side at one resolvent**: off the old cylinder, `D_y zWMid` is the real part of
`D_yW_μ(Ḡ)` with `W_μ(Ḡ) = IIIa.sepW ν μ (thinSource ε (meanLift Ḡ)) · 0` (phase free; source
4168-4171, 5415-5427). -/
theorem fderiv_zWMid_eq (μ : ℝ) (hμ : 0 ≤ μ) (hC0 : 0 < K.C0) (hmZ : 3 / 2 < K.mZ)
    (T : LStr Pl K L) (τ : ℝ) (y : Space) (hy : L.ε⁻¹ * Real.sqrt (5 * L.ν / 6) < ϱ y) :
    fderiv ℝ (zWMid Pl K L μ T τ) y =
      reMap.comp (fderiv ℝ (fun y => IIIa.sepW L.ν (μ : ℂ)
          (IIIa.thinSource L.ε (IIIa.meanLift (meanSrc Pl K L T))) y 0) y) := by
  have hν : 0 < L.ν := L.ν_pos
  have hε : 0 < L.ε := L.ε_pos
  have hc : 0 < cOf L.ν := cOf_pos hν
  have hρb : 0 < L.ρb Pl K := ZRegAux.rho_b_pos' Pl K L hC0
  have hgm : Measurable (thinG Pl K L T) := thinG_measurable Pl K L T
  have hmom : ∫⁻ p, ‖thinG Pl K L T p‖ₑ ^ 2 ∂(ageμ (cOf L.ν) (-1 / 2)) < ⊤ :=
    strChartL2 (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν hρb (by linarith) hν _
  have hz : ∀ᵐ p ∂(ageμ (cOf L.ν) (-1 / 2)), L.ν * p.1 ≤ 6 / 5 → thinG Pl K L T p = 0 :=
    ZRegAux.strSum_zero_young _ _ _ _ _ K.hχo hρb _
  have hz' := ZRegAux.mean_ae_zero (cOf L.ν) (-1 / 2) L.ν hc _ hgm hz
  have hmean_m := ZRegAux.measurable_meanQ' (cOf L.ν) hgm
  have hmean_mom : ∫⁻ p, ‖meanQ (cOf L.ν) (thinG Pl K L T) p‖ₑ ^ 2 ∂(ageμ (cOf L.ν) (-1 / 2)) < ⊤ :=
    lt_of_le_of_lt (ZRegAux.mean_moment_le _ _ hc _ hgm) hmom
  have hreμ : -(1 / 4) < ((μ : ℝ) : ℂ).re := by simp; linarith
  have hA := sepW_diff (cOf L.ν) L.ν L.ε _ hc hν hε hreμ _ hmean_m hmean_mom hz' τ y hy
  have e : (fun y => IIIa.sepW L.ν (μ : ℂ)
      (oldPhys L.ε⁻¹ (cOf L.ν) (meanQ (cOf L.ν) (thinG Pl K L T))) y τ) =
      fun y => IIIa.sepW L.ν (μ : ℂ) (IIIa.thinSource L.ε (IIIa.meanLift (meanSrc Pl K L T))) y 0 := by
    funext y
    rw [← sepW_mean (cOf L.ν) L.ν L.ε (μ : ℂ) hc hν hε _ hgm hmom hz' y τ]
    rfl
  have hzWMid : zWMid Pl K L μ T τ = (reMap ∘ fun y => IIIa.sepW L.ν (μ : ℂ)
      (oldPhys L.ε⁻¹ (cOf L.ν) (meanQ (cOf L.ν) (thinG Pl K L T))) y τ) := rfl
  have h := (reMap.hasFDerivAt.comp y hA.hasFDerivAt).fderiv
  rw [← hzWMid, e] at h
  exact h

/-- **(ii) The Newton side at one resolvent**: off the old disc, `D_y zWMt(ε⁻¹x_obs) =
ε³ Re D_xV_{μ,0}(Ḡ)(x_obs)` (source 4776-4791). -/
theorem fderiv_zWMt_eq (hK : KernelDict) (hS : SigmaCollapse) (μ : ℝ) (hμ : 0 < μ)
    (hC0 : 0 < K.C0) (T : LStr Pl K L) (hAzi : ThinAziZero Pl K L T)
    (hOTF : OldThinFinite (cOf L.ν) L.ν (thinRep T)) (hN1 : oldN1 Pl K L T ≠ ⊤)
    (τ : ℝ) (xo : Space) (hxo : 5 * L.ν / 6 < xo 0 ^ 2 + xo 1 ^ 2) :
    fderiv ℝ (zWMt Pl K L μ T τ) (L.ε⁻¹ • xo) =
      (L.ε ^ 3) • reMap.comp (fderiv ℝ (IIIa.sepVmu0 (μ : ℂ) (meanSrc Pl K L T)) xo) := by
  have h1 := reMap_comp_fderiv_sepVmu0 hK hS Pl K L hC0 T hAzi hOTF hN1 hμ hxo
  rw [h1]
  have hd1 : DifferentiableAt ℝ (newtonVSp Pl K L μ T) xo :=
    newtonVSp_differentiableAt Pl K L hμ T hOTF hxo
  have hzWMt : zWMt Pl K L μ T τ = fun y : Space =>
      (L.ε ^ 2) • newtonVSp Pl K L μ T (L.ε • y) := by
    funext y
    ext i
    simp [zWMt, mtField, youngW, newtonVSp]
  have hscale : L.ε • (L.ε⁻¹ • xo) = xo := by
    rw [smul_smul, mul_inv_cancel₀ L.ε_pos.ne', one_smul]
  have hsmul : HasFDerivAt (fun y : Space => L.ε • y)
      (L.ε • ContinuousLinearMap.id ℝ Space) (L.ε⁻¹ • xo) :=
    (ContinuousLinearMap.id ℝ Space).hasFDerivAt.const_smul L.ε
  have hd1' : HasFDerivAt (newtonVSp Pl K L μ T)
      (fderiv ℝ (newtonVSp Pl K L μ T) xo) (L.ε • (L.ε⁻¹ • xo)) := by
    rw [hscale]
    exact hd1.hasFDerivAt
  have hchain := (hd1'.comp (L.ε⁻¹ • xo) hsmul).const_smul (L.ε ^ 2)
  rw [hzWMt]
  refine hchain.fderiv.trans ?_
  ext v i
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_smul, WithLp.ofLp_smul,
    Pi.smul_apply, smul_eq_mul]
  ring

theorem norm_reMap_comp_sub_le' (W₁ V₁ : Space →L[ℝ] (Fin 3 → ℂ)) (ε : ℝ) :
    ‖reMap.comp W₁ - (ε ^ 3 : ℝ) • reMap.comp V₁‖ ≤
      2 * ‖W₁ - (ε ^ 3 : ℝ) • V₁‖ := by
  have heq : reMap.comp W₁ - (ε ^ 3 : ℝ) • reMap.comp V₁ =
      reMap.comp (W₁ - (ε ^ 3 : ℝ) • V₁) := by
    ext v i
    simp only [sub_apply, ContinuousLinearMap.comp_apply,
      smul_apply, map_sub, map_smul, WithLp.ofLp_sub, WithLp.ofLp_smul,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [heq]
  calc ‖reMap.comp (W₁ - (ε ^ 3 : ℝ) • V₁)‖
      ≤ ‖reMap‖ * ‖W₁ - (ε ^ 3 : ℝ) • V₁‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 2 * ‖W₁ - (ε ^ 3 : ℝ) • V₁‖ :=
        mul_le_mul_of_nonneg_right opNorm_reMap_le (norm_nonneg _)

end Regime

end TWBridgeYA

open PhasePrim TWBridge TWBridgeYA in
/-- **Uniform regime bound `TaylorWidthYAAt`** (source 5415-5427, 4764-4791): combines the heat
bridge `fderiv_zWMid_eq`, the Newton bridge `fderiv_zWMt_eq`, the moment bound
`thinMoment_meanSrc_le`, and the far-field comparison `SepMeanFar` at `μ`. -/
theorem taylorWidthYAAt_uniform_of (hF : SepMeanFar) (hK : TWBridge.KernelDict)
    (hS : TWBridge.SigmaCollapse) (Pl : PlanarData) (K : ReturnConsts)
    (hC0 : 0 < K.C0) (hmZ : 3 / 2 < K.mZ) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧
      ∀ (L : ReturnLevel) (μ : ℝ), L.ε ≤ 1 →
        TaylorWidthYAAt Pl K L μ C k := by
  obtain ⟨C, k, hC, hlf⟩ := hF Kmu Kmu_compact Kmu_re
  refine ⟨2 * Real.pi * (C + 1) * 16 ^ k, 2 * k, by have := Real.pi_pos; positivity, ?_⟩
  intro L μ hε1 hL T hAzi s hs η q
  have hν : 0 < L.ν := L.ν_pos
  have hε : 0 < L.ε := L.ε_pos
  have hc : 0 < cOf L.ν := cOf_pos hν
  have hν1 : L.ν ≤ 1 := hL.nu_le
  have hμ0 : 0 < μ := hL.mu_pos
  have hμ14 : μ < 1 / 4 := hL.mu_lt
  have hs0 : 0 < s := hs.1
  have hss : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
  have hνs : L.ν * s ≤ 1 := by
    have := hs.2
    rw [le_div_iff₀ hν] at this
    linarith
  set N := oldN1 Pl K L T with hNdef
  have hcoef : 0 < 2 * Real.pi * (C + 1) * 16 ^ k * L.ν⁻¹ ^ (2 * k) *
      (L.ε ^ 4 * s ^ (5 / 2 : ℝ)) := by
    have := Real.pi_pos
    have : 0 < s ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hs0 _
    positivity
  by_cases hNtop : N = ⊤
  · rw [hNtop, ENNReal.mul_top (by simpa using hcoef)]
    exact le_top
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
  have hOTF : OldThinFinite (cOf L.ν) L.ν (thinRep T) :=
    oldThinFinite_of_strG hmZ hc hν hν1 T
  set G := meanSrc Pl K L T with hG
  have hheat := fderiv_zWMid_eq Pl K L μ hμ0.le hC0 hmZ T τ y hyr
  have hnewt := fderiv_zWMt_eq Pl K L hK hS μ hμ0 hC0 T hAzi hOTF hNtop τ xo hxo_gap
  rw [hxo'] at hnewt
  set W₁ := fderiv ℝ (fun y => IIIa.sepW L.ν (μ : ℂ)
    (IIIa.thinSource L.ε (IIIa.meanLift G)) y 0) y
  set V₁ := fderiv ℝ (IIIa.sepVmu0 (μ : ℂ) G) xo
  have hdW : dWidthW Pl K L μ T τ y ≤ 2 * ‖W₁ - (L.ε ^ 3 : ℝ) • V₁‖ := by
    unfold dWidthW
    rw [hheat, hnewt]
    exact norm_reMap_comp_sub_le' W₁ V₁ L.ε
  have hμK : ((μ : ℝ) : ℂ) ∈ Kmu := ⟨μ, ⟨hμ0.le, by linarith⟩, rfl⟩
  have hGm : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => G w.1 w.2 i j :=
    meanSrc_measurable Pl K L T
  have hGs : ∀ x' Y, Real.sqrt (5 * L.ν / 6) < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → G x' Y = 0 :=
    meanSrc_support Pl K L T
  have hB₁ := hlf L.ν (cOf L.ν) L.ε (Real.sqrt (5 * L.ν / 6)) (Real.sqrt L.ν)
    hν hν1 hc hε hε1 (Real.sqrt_nonneg _) hρ (μ : ℂ) hμK G hGm hGs xo hρi
  rw [hxo'] at hB₁
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
  have hB₁' : ‖W₁ - (L.ε ^ 3 : ℝ) • V₁‖ₑ ≤ ENNReal.ofReal (a * Real.pi) * N := by
    refine hB₁.trans ?_
    rw [hrad, ← ha, ENNReal.ofReal_mul ha0, mul_assoc]
    exact mul_le_mul_right hGN _
  have ha_le : a * Real.pi * 2 ≤ 2 * Real.pi * (C + 1) * 16 ^ k * L.ν⁻¹ ^ (2 * k) *
      (L.ε ^ 4 * s ^ (5 / 2 : ℝ)) := by
    have hs52 : 0 < s ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hs0 _
    have hpi := Real.pi_pos
    have h1 : C * M ^ k ≤ (C + 1) * (16 ^ k * L.ν⁻¹ ^ (2 * k)) :=
      mul_le_mul (by linarith) hMle (pow_nonneg hM0 _) (by linarith)
    have h2 : 0 ≤ L.ε ^ 4 * s ^ (5 / 2 : ℝ) := by positivity
    calc a * Real.pi * 2 = 2 * Real.pi * (C * M ^ k) * (L.ε ^ 4 * s ^ (5 / 2 : ℝ)) := by
          rw [ha]; ring
      _ ≤ 2 * Real.pi * ((C + 1) * (16 ^ k * L.ν⁻¹ ^ (2 * k))) * (L.ε ^ 4 * s ^ (5 / 2 : ℝ)) := by
          gcongr
      _ = _ := by ring
  calc ENNReal.ofReal (dWidthW Pl K L μ T τ y)
      ≤ ENNReal.ofReal (2 * ‖W₁ - (L.ε ^ 3 : ℝ) • V₁‖) :=
        ENNReal.ofReal_le_ofReal hdW
    _ = 2 * ‖W₁ - (L.ε ^ 3 : ℝ) • V₁‖ₑ := by
        rw [ENNReal.ofReal_mul (by norm_num), ofReal_norm]
        norm_num
    _ ≤ 2 * (ENNReal.ofReal (a * Real.pi) * N) := by
        gcongr
    _ = ENNReal.ofReal (a * Real.pi * 2) * N := by
        rw [← mul_assoc, ENNReal.ofReal_mul (mul_nonneg ha0 Real.pi_pos.le)]
        congr 1
        rw [mul_comm]
        norm_num
    _ ≤ ENNReal.ofReal (2 * Real.pi * (C + 1) * 16 ^ k * L.ν⁻¹ ^ (2 * k) *
          (L.ε ^ 4 * s ^ (5 / 2 : ℝ))) * N := by
        gcongr

/-- **`taylorWidthYA` from the far-field mean comparison and the Newton bridge**
(source 5415-5427, 4764-4791). -/
theorem taylorWidthYA_of (hF : SepMeanFar) (hK : TWBridge.KernelDict)
    (hS : TWBridge.SigmaCollapse) (D : SeqData) {dm dp : ℝ}
    (hst : D.RepairStanding dm dp) : D.TaylorWidthYA := by
  obtain ⟨C, k, _, h⟩ := taylorWidthYAAt_uniform_of hF hK hS D.Pl D.K hst.C0_pos hst.mZ_gt
  refine ⟨C, k, ?_⟩
  filter_upwards [retNu_retEps_eventually_le_one (σ₀ := D.σ₀) hst.omega_ne hst.gamma_pos
    D.coeff_ne] with n hνε z _
  exact h (D.level n) (D.mu n z) hνε.2

theorem taylorWidthYA (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.TaylorWidthYA :=
  taylorWidthYA_of sepMeanFar kernelDict sigmaCollapse D hst

end UnforcedLeray.Short.PartIIIb.Concrete
