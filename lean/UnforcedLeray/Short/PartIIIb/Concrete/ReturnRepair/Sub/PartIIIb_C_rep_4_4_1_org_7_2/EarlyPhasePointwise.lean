import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4_4_1_org_7_2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_1.RepPhasePointwise

/-!
# Proof of the leaf `EarlyPhasePointwise` (`PartIII-b:C/rep/4/4/1/org/7/2/1`)

Source 4147, 5153-5157, 5169-5171, 4163-4166. The early physical stress is the cut stress
`(T - χ_o T).snd` for `T = M_U w`. Its chart tensor is `(1 - χ̂_o(νs))` times the exact chart tensor
`r_b ⊗ w + w ⊗ r_b`. The factor `1 - χ̂_o(νs)` lies in `[0,1]` and vanishes where `νs ≥ 3/2`,
so the chart tensor equals `(1 - χ̂_o(νs))` times the exact chart tensor of `earlyTrunc ν w`.
The rest is the pointwise argument of `repPhasePointwise`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)
open UnforcedLeray.PhaseSpace

/-- The chart tensor of the early-truncated velocity (exact multiplier pattern, `earlyTrunc`). -/
def earlyChartTen (Pl : PlanarData) (L : ReturnLevel) (w : LVel Pl L) : Chart → Ten3 :=
  fun p => NearInst.ten3Of (UnforcedLeray.Short.IIIa.symOuter
    (UnforcedLeray.Short.IIIa.chartCoeff L.ε⁻¹ L.rb p) (earlyTrunc L.ν w p))

theorem earlyPhasePointwise : EarlyPhasePointwise := by
  unfold EarlyPhasePointwise
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
      (gRate Pl) L.ν] repG Pl K L w := (hEx w).2
  -- the cut stress
  have hC : ((chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo (multOp Pl K L w)).snd :
      Chart → Ten3) =ᵐ[gainHTMeasure (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν]
        fun p => cutFun K.χo L.ν p • ((multOp Pl K L w).snd : Chart → Ten3) p :=
    (chiOStrApply (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.χo K.hχo (multOp Pl K L w)).2
  -- the early stress is the difference (subtraction of the `snd` components)
  have hD : ∀ᵐ p ∂(gainHTMeasure (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν),
      ((multOp Pl K L w - chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo
          (multOp Pl K L w)).snd : Chart → Ten3) p =
        ((multOp Pl K L w).snd : Chart → Ten3) p -
          ((chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo (multOp Pl K L w)).snd :
            Chart → Ten3) p := by
    filter_upwards [MeasureTheory.Lp.coeFn_sub ((multOp Pl K L w).snd)
      ((chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo (multOp Pl K L w)).snd)]
      with p hp
    rw [WithLp.sub_snd]
    exact hp
  have hgood : ∀ᵐ p ∂(gainHTMeasure (cOf L.ν) (L.ρb Pl K) (gRate Pl) L.ν),
      ((multOp Pl K L w - chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo
          (multOp Pl K L w)).snd : Chart → Ten3) p =
        (1 - cutFun K.χo L.ν p) • repG Pl K L w p := by
    filter_upwards [hD, hC, hEx2] with p h1 h2 h3
    simp only [h1, h2, h3, sub_smul, one_smul]
  have hgood' := hgood
  rw [NearInst.ae_gainHTMeasure, NearInst.ae_htRhoMeasure hρpos] at hgood'
  have hN0 := ae_iff.mp hgood'
  have hpt := chartOfNullPullback L.ε⁻¹ (cOf L.ν) hR hc _ hN0
  have hcart := cartLiftSymOuter_proved L.ε⁻¹ (cOf L.ν) L.rb hR hc hax hper
  -- the factor `1 - χ̂_o(νs)` lies in `[0,1]`
  have hfb : ∀ p : Chart, |1 - cutFun K.χo L.ν p| ≤ 1 := by
    intro p
    have hr := K.hχo.range (L.ν * p.1)
    unfold cutFun
    rw [abs_le]
    constructor <;> linarith [hr.1, hr.2]
  -- the factor kills the early-truncated part and agrees with the exact stress below `3/(2ν)`
  have hfG : ∀ p : Chart, (1 - cutFun K.χo L.ν p) • repG Pl K L w p =
      (1 - cutFun K.χo L.ν p) • earlyChartTen Pl L w p := by
    intro p
    by_cases hp : L.ν * p.1 ≤ 3 / 2
    · simp [repG, earlyChartTen, earlyTrunc, hp]
    · have h1 : 3 / 2 ≤ L.ν * p.1 := le_of_lt (not_le.mp hp)
      have hcut : cutFun K.χo L.ν p = 1 := K.hχo.one _ h1
      rw [hcut]
      simp
  have hae : ∀ᵐ x : ℝ × Space ∂(volume : Measure (ℝ × Space)),
      UnforcedLeray.Short.IIIa.tensorNorm (ertSrcPhys Pl K L (multOp Pl K L w) x) ≤
        2 * ‖L.rb x.1 x.2‖ * ‖velPhys L.ε⁻¹ (cOf L.ν) (earlyTrunc L.ν w) x‖ := by
    filter_upwards [hpt] with x hx
    have hP := not_not.mp hx
    have e1 : ertSrcPhys Pl K L (multOp Pl K L w) x =
        NearInst.cartLift L.ε⁻¹ (cOf L.ν)
          (fun p => (1 - cutFun K.χo L.ν p) • earlyChartTen Pl L w p) x.1 x.2 :=
      cartLift_congr_pt _ _ _ _ _ _ (hP.trans (hfG _))
    have e2 : NearInst.cartLift L.ε⁻¹ (cOf L.ν)
        (fun p => (1 - cutFun K.χo L.ν p) • earlyChartTen Pl L w p) x.1 x.2 =
        (1 - cutFun K.χo L.ν (NearInst.chartOf L.ε⁻¹ (cOf L.ν) x.2 x.1)) •
          NearInst.cartLift L.ε⁻¹ (cOf L.ν) (earlyChartTen Pl L w) x.1 x.2 :=
      cartLift_smul_pt _ _ _ _ _ _
    have e3 : NearInst.cartLift L.ε⁻¹ (cOf L.ν) (earlyChartTen Pl L w) x.1 x.2 =
        symProd (L.rb x.1 x.2) (Nv L.ε⁻¹ (perExt (cOf L.ν) (earlyTrunc L.ν w)) x.1 x.2) :=
      hcart (earlyTrunc L.ν w) x.1 x.2
    have hv : ‖velPhys L.ε⁻¹ (cOf L.ν) (earlyTrunc L.ν w) x‖ =
        ‖Nv L.ε⁻¹ (perExt (cOf L.ν) (earlyTrunc L.ν w)) x.1 x.2‖ :=
      wda_norm_realC _
    rw [e1, e2, e3, hv]
    exact le_trans (tensorNorm_smul_le' _ (hfb _) _) (tensorNorm_symProd_le' _ _)
  rw [Measure.volume_eq_prod] at hae
  have h2 := Measure.ae_ae_of_ae_prod hae
  exact ae_restrict_of_ae h2

end UnforcedLeray.Short.PartIIIb.Concrete
