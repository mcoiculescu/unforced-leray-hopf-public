import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_1Org
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Proofs.MultPin
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.StressLift.CartLift
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L1
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Agree
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.WeakDmuAdd

/-!
# Proof of `RepPhasePointwiseEarly` (`PartIII-b:C/rep/5/2/1/9`, source 4147, 5169-5171)

Same argument as the proved leaf `repPhasePointwise`, with the cut `1 - χ_o` moved from the
stress to the velocity: `earlyRepTen = (1-χ_o) • snd(multOp w)` a.e. (exact multiplier pin),
`cartLift` is pointwise linear (`cartLift_smul_pt`), and the velocity factor is exact:
`𝒩_v((1-χ_o)w) = (1-χ_o(ν s)) 𝒩_v w` at the chart point, so the bound holds with `|1-χ_o|`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)
open UnforcedLeray.PhaseSpace

/-- The chart tensor of the exact multiplier (copy of the leaf `repG`). -/
def peRepG (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (w : LVel Pl L) :
    Chart → Ten3 :=
  fun p => NearInst.ten3Of (UnforcedLeray.Short.IIIa.symOuter
    (UnforcedLeray.Short.IIIa.chartCoeff L.ε⁻¹ L.rb p) (w p))

theorem pe_tensorNorm_smul (f : ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) :
    UnforcedLeray.Short.IIIa.tensorNorm (f • M) =
      |f| * UnforcedLeray.Short.IIIa.tensorNorm M := by
  unfold UnforcedLeray.Short.IIIa.tensorNorm
  have h : ∑ i, ∑ j, (f • M) i j ^ 2 = f ^ 2 * ∑ i, ∑ j, M i j ^ 2 := by
    simp [Matrix.smul_apply, mul_pow, Finset.mul_sum]
  rw [h, Real.sqrt_mul (sq_nonneg f), Real.sqrt_sq_eq_abs]

theorem pe_tensorNorm_symProd_le (a b : Space) :
    UnforcedLeray.Short.IIIa.tensorNorm (symProd a b) ≤ 2 * ‖a‖ * ‖b‖ := by
  unfold UnforcedLeray.Short.IIIa.tensorNorm
  have ha : ‖a‖ ^ 2 = ∑ i, a i ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]; simp
  have hb : ‖b‖ ^ 2 = ∑ i, b i ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]; simp
  have hab : 0 ≤ 2 * ‖a‖ * ‖b‖ := by positivity
  have h : ∑ i, ∑ j, (symProd a b) i j ^ 2 ≤ (2 * ‖a‖ * ‖b‖) ^ 2 := by
    have key : (2 * ‖a‖ * ‖b‖) ^ 2 = 4 * (‖a‖ ^ 2) * (‖b‖ ^ 2) := by ring
    rw [key, ha, hb]
    simp only [symProd, Fin.sum_univ_three]
    nlinarith [sq_nonneg (a 0 * b 1 - a 1 * b 0), sq_nonneg (a 0 * b 2 - a 2 * b 0),
      sq_nonneg (a 1 * b 2 - a 2 * b 1)]
  calc Real.sqrt (∑ i, ∑ j, (symProd a b) i j ^ 2) ≤ Real.sqrt ((2 * ‖a‖ * ‖b‖) ^ 2) :=
        Real.sqrt_le_sqrt h
    _ = 2 * ‖a‖ * ‖b‖ := Real.sqrt_sq hab

theorem pe_cartLift_congr (R c : ℝ) (F F' : Chart → Ten3) (τ : ℝ) (z : Space)
    (h : F (NearInst.chartOf R c z τ) = F' (NearInst.chartOf R c z τ)) :
    NearInst.cartLift R c F τ z = NearInst.cartLift R c F' τ z := by
  unfold NearInst.cartLift
  rw [h]

theorem pe_perExt_earlyVel (c : ℝ) (K : ReturnConsts) (L : ReturnLevel) (w : Chart → Merid)
    (p : ℝ × (ℝ × ℝ)) :
    perExt c (earlyVel K L w) p = (1 - K.χo (L.ν * p.1)) • perExt c w p := rfl

theorem pe_chart_fst (R c : ℝ) (y : Space) (τ : ℝ) :
    (chart R τ y).1 = (NearInst.chartOf R c y τ).1 := by
  show R ^ 2 / ϱ y ^ 2 = (NearInst.chartOf R c y τ).1
  simp only [NearInst.chartOf, NearInst.hRad, ϱ]

theorem pe_Nv_earlyVel (K : ReturnConsts) (L : ReturnLevel) (c : ℝ) (w : Chart → Merid)
    (τ : ℝ) (y : Space) :
    Nv L.ε⁻¹ (perExt c (earlyVel K L w)) τ y =
      (1 - K.χo (L.ν * (NearInst.chartOf L.ε⁻¹ c y τ).1)) •
        Nv L.ε⁻¹ (perExt c w) τ y := by
  unfold Nv
  have hpe : perExt c (earlyVel K L w) (chart L.ε⁻¹ τ y) =
      (1 - K.χo (L.ν * (chart L.ε⁻¹ τ y).1)) • perExt c w (chart L.ε⁻¹ τ y) := rfl
  rw [hpe, pe_chart_fst L.ε⁻¹ c y τ]
  simp only [map_smul]
  exact smul_comm _ _ _

theorem repPhasePointwiseEarly : RepPhasePointwiseEarly := by
  unfold RepPhasePointwiseEarly
  intro Pl K L μ hC0 hnear hs hax hper w
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hrhoRep : 0 < rhoRep K L := by
    unfold rhoRep
    exact mul_pos (Real.rpow_pos_of_pos hε _) (Real.exp_pos _)
  have hρpos : 0 < L.ρb Pl K := by
    rw [rhoB_eq]
    exact mul_pos (mul_pos hC0 (pow_pos (inv_pos.2 hν) _)) hrhoRep
  have hR : 0 < L.ε⁻¹ := inv_pos.2 hε
  have hc : 0 < cOf L.ν := cOf_pos hν
  -- the exact multiplier
  have hEx : IsExactMultiplier (concreteBase Pl K L μ hnear) L.ε⁻¹ L.V L.rb :=
    concreteBase_isExactMultiplier (h := hnear) NearInst.multPinOfLink hs
  have hEx2 : ((multOp Pl K L w).snd : Chart → Ten3) =ᵐ[gainHTMeasure (cOf L.ν) (L.ρb Pl K)
      (gRate Pl) L.ν] peRepG Pl K L w := (hEx w).2
  have hgood : ∀ᵐ p ∂(gainHTMeasure (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν),
      ((multOp Pl K L w).snd : Chart → Ten3) p = peRepG Pl K L w p := hEx2
  rw [NearInst.ae_gainHTMeasure, NearInst.ae_htRhoMeasure hρpos] at hgood
  have hN0 := ae_iff.mp hgood
  have hpt := chartOfNullPullback L.ε⁻¹ (cOf L.ν) hR hc _ hN0
  have hcart := cartLiftSymOuter_proved L.ε⁻¹ (cOf L.ν) L.rb hR hc hax hper w
  have hae : ∀ᵐ x ∂(volume : Measure (ℝ × Space)),
      UnforcedLeray.Short.IIIa.tensorNorm (strPhys L.ε⁻¹ (cOf L.ν) (earlyRepTen Pl K L w) x) ≤
        2 * ‖L.rb x.1 x.2‖ * ‖velPhys L.ε⁻¹ (cOf L.ν) (earlyVel K L (w : Chart → Merid)) x‖ := by
    filter_upwards [hpt] with x hx
    have hP : ((multOp Pl K L w).snd : Chart → Ten3)
        (NearInst.chartOf L.ε⁻¹ (cOf L.ν) x.2 x.1) =
          peRepG Pl K L w (NearInst.chartOf L.ε⁻¹ (cOf L.ν) x.2 x.1) :=
      not_not.mp hx
    have hPe : earlyRepTen Pl K L w (NearInst.chartOf L.ε⁻¹ (cOf L.ν) x.2 x.1) =
        (fun p => (1 - K.χo (L.ν * p.1)) • peRepG Pl K L w p)
          (NearInst.chartOf L.ε⁻¹ (cOf L.ν) x.2 x.1) := by
      simp only [earlyRepTen]
      rw [hP]
    have e1 : strPhys L.ε⁻¹ (cOf L.ν) (earlyRepTen Pl K L w) x =
        NearInst.cartLift L.ε⁻¹ (cOf L.ν) (fun p => (1 - K.χo (L.ν * p.1)) • peRepG Pl K L w p)
          x.1 x.2 :=
      pe_cartLift_congr L.ε⁻¹ (cOf L.ν) _ _ x.1 x.2 hPe
    have e3 : NearInst.cartLift L.ε⁻¹ (cOf L.ν)
          (fun p => (1 - K.χo (L.ν * p.1)) • peRepG Pl K L w p) x.1 x.2 =
        (1 - K.χo (L.ν * (NearInst.chartOf L.ε⁻¹ (cOf L.ν) x.2 x.1).1)) •
          NearInst.cartLift L.ε⁻¹ (cOf L.ν) (peRepG Pl K L w) x.1 x.2 :=
      cartLift_smul_pt L.ε⁻¹ (cOf L.ν) (fun p => 1 - K.χo (L.ν * p.1)) (peRepG Pl K L w) x.1 x.2
    have e4 : NearInst.cartLift L.ε⁻¹ (cOf L.ν) (peRepG Pl K L w) x.1 x.2 =
        symProd (L.rb x.1 x.2) (Nv L.ε⁻¹ (perExt (cOf L.ν) w) x.1 x.2) :=
      hcart x.1 x.2
    have hv : ‖velPhys L.ε⁻¹ (cOf L.ν) (earlyVel K L (w : Chart → Merid)) x‖ =
        |1 - K.χo (L.ν * (NearInst.chartOf L.ε⁻¹ (cOf L.ν) x.2 x.1).1)| *
          ‖Nv L.ε⁻¹ (perExt (cOf L.ν) w) x.1 x.2‖ := by
      unfold velPhys
      rw [wda_norm_realC, pe_Nv_earlyVel K L (cOf L.ν) (w : Chart → Merid) x.1 x.2, norm_smul,
        Real.norm_eq_abs]
    have hs2 := mul_le_mul_of_nonneg_left
      (pe_tensorNorm_symProd_le (L.rb x.1 x.2) (Nv L.ε⁻¹ (perExt (cOf L.ν) w) x.1 x.2))
      (abs_nonneg (1 - K.χo (L.ν * (NearInst.chartOf L.ε⁻¹ (cOf L.ν) x.2 x.1).1)))
    rw [e1, e3, e4, hv, pe_tensorNorm_smul]
    refine le_trans hs2 (le_of_eq ?_)
    ring
  rw [Measure.volume_eq_prod] at hae
  have h2 := Measure.ae_ae_of_ae_prod hae
  exact ae_restrict_of_ae h2

end UnforcedLeray.Short.PartIIIb.Concrete
