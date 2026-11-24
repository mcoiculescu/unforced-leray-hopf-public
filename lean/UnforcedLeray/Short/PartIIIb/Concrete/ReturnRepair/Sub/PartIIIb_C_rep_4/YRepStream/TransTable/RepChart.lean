import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.TransTable.RepChart.Const
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.TransTable.RepChart.Mer
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymNuEps

/-!
# `PartIII-b:C/rep/4/4/1/org/3/4`: repair multiplication on the transition window

Source `the November 2 reference manuscript` 5134-5139 (`‖r_b‖_{C_τL^{11/4}} ≤ ρ_b`,
the field `energy` of `IIb.ExactSplitII`), 2698-2713 (`ρ_b`, the scaled repair receiver),
2683-2689 (chart to physical), 5338-5339 (Hölder `1/2 = 4/11 + 3/22` against the `L^{22/3}`
receiver).

Chain (all proved, `RepChart/*.lean`): `RC.multMaj_eq` (`multMaj = s⁻¹ G(τ(p),y(p))` with
`G = |r_b|_mer f`), `RC.htMaj_multMaj_le` (`chartPhysL2`, `ρ_b^{-1/2}π^{-1/2}R⁻¹‖G‖_{L²_τL²}`),
`RC.ltauLq_two_le` (Hölder in `z`), `RC.repConst` (`ρ_b` algebra).

The meridional-trace facts (`SeqData.rbMerFacts`, `RepChart/Mer.lean`): for large `n` the repair is
`r_b = p.corr z` (`ExactSplitII.state`), jointly continuous (`IIIa.corr_continuous`), `P`-periodic
(`Params.corr_periodic`) and axisymmetric without swirl at every phase
(`Params.corr_isAxisymmetricNoSwirl` with continuity, `axiNoSwirlPt_of_ae`), once `P = 2εc ≤ 1`
(`pf2b_period_le_one`); so `|r_b|_mer(τ,y) = |(r_b)_{r,z}(τ,(ϱ,0,y₃))|` is jointly measurable,
`2εc`-periodic and at most `|r_b(τ,y)|` pointwise.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace SeqData

variable (D : SeqData)

/-- **The meridional trace of the repair** (source 5134-5139, 2706): for large `n` the function
`(τ, y) ↦ |(r_b)_{r,z}(τ, (ϱ y, 0, y₃))|` is jointly measurable and `2εc`-periodic, and its
`L^{11/4}_y` norm at every phase is at most that of `r_b(τ)` (equality for an axisymmetric field
without swirl). -/
def RbMerFacts : Prop := ∀ᶠ n : ℕ in atTop,
  Measurable (Function.uncurry fun τ y => ENNReal.ofReal (RC.merTr (D.level n).rb τ y)) ∧
  (∀ τ y, RC.merTr (D.level n).rb (τ + 2 * (D.level n).ε * cOf (D.level n).ν) y =
    RC.merTr (D.level n).rb τ y) ∧
  ∀ τ, ∫⁻ y, ENNReal.ofReal (RC.merTr (D.level n).rb τ y) ^ (11 / 4 : ℝ) ≤
    ∫⁻ y, ‖(D.level n).rb τ y‖ₑ ^ (11 / 4 : ℝ)

/-- **The meridional-trace facts of the repair hold along every standing sequence** (source
121-124, 2031, 2522-2523, 2664-2713, 5134-5139). -/
theorem rbMerFacts {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.RbMerFacts := by
  filter_upwards [hst.actual, pf2b_period_le_one D hst] with n hn hP1
  obtain ⟨z, -, -, hrb, -⟩ := hn.split.state
  have hrb' : (D.level n).rb = ((D.level n).params D.Pl).corr z := hrb
  have hc : Continuous (fun x : ℝ × Space => ((D.level n).params D.Pl).corr z x.1 x.2) :=
    UnforcedLeray.Short.IIIa.corr_continuous _ hP1 z
  rw [hrb']
  refine ⟨RC.merTr_measurable hc, fun τ y => ?_, fun τ => ?_⟩
  · exact RC.merTr_periodic (P := 2 * (D.level n).ε * cOf (D.level n).ν)
      (fun τ => ((D.level n).params D.Pl).corr_periodic z τ) τ y
  · have hsl : Continuous (((D.level n).params D.Pl).corr z τ) :=
      hc.comp (Continuous.prodMk_right (Y := Space) τ)
    exact RC.merTr_lintegral_le
      (axiNoSwirlPt_of_ae hsl (((D.level n).params D.Pl).corr_isAxisymmetricNoSwirl hP1 z τ))

end SeqData

/-- **Repair multiplication on the transition window**, from the meridional-trace facts of the
repair (source 5134-5139, 2698-2713, 5338-5339). -/
theorem repChart_of
    (hRb : ∀ D : SeqData, ∀ dm dp : ℝ, D.RepairStanding dm dp → D.RbMerFacts) (dm dp : ℝ) :
    RepChart dm dp := by
  intro D hst
  refine ⟨Real.sqrt D.K.C0 * Real.sqrt Real.pi⁻¹, D.K.k0, by positivity, ?_⟩
  have hev2 := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  filter_upwards [hst.actual, hRb D dm dp hst, hev2] with n hn hF e2 f hf hvan
  obtain ⟨hMm, hMper, hMle⟩ := hF
  have hν0 : 0 < (D.level n).ν := (D.level n).ν_pos
  have hε : 0 < (D.level n).ε := (D.level n).ε_pos
  have hR : 0 < (D.level n).ε⁻¹ := inv_pos.2 hε
  have hc : 0 < cOf (D.level n).ν := cOf_pos hν0
  have hρdef : (D.level n).ρb D.Pl D.K = D.K.C0 * ((D.level n).ν ^ D.K.k0)⁻¹ *
      Real.exp (D.K.m0 / (D.level n).ν) * (D.level n).ε ^ (3 / 11 : ℝ) := rfl
  have hρ : 0 < (D.level n).ρb D.Pl D.K := by rw [hρdef]; have := hst.C0_pos; positivity
  have hP : 2 * (D.level n).ε * cOf (D.level n).ν = 2 * cOf (D.level n).ν / (D.level n).ε⁻¹ := by
    field_simp
  rw [hP] at hf hMper ⊢
  have h1 := RC.htMaj_multMaj_le hR hc hρ hMm hMper hf
  have hMb : ∀ τ, (∫⁻ y, ENNReal.ofReal (RC.merTr (D.level n).rb τ y) ^ (11 / 4 : ℝ)) ^
      (4 / 11 : ℝ) ≤ ENNReal.ofReal ((D.level n).ρb D.Pl D.K) := by
    intro τ
    have hen := (hn.split.energy τ)
    have hen' : eLpNorm ((D.level n).rb τ) (ENNReal.ofReal (11 / 4)) volume ≤
        ENNReal.ofReal ((D.level n).ρb D.Pl D.K) :=
      le_trans le_self_add hen
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp) (by simp),
      ENNReal.toReal_ofReal (by norm_num)] at hen'
    refine le_trans (ENNReal.rpow_le_rpow (hMle τ) (by norm_num)) ?_
    have e : (4 / 11 : ℝ) = 1 / (11 / 4) := by norm_num
    rw [e]
    exact hen'
  have h2 := RC.ltauLq_two_le (P := 2 * cOf (D.level n).ν / (D.level n).ε⁻¹)
    (fun τ y => ENNReal.ofReal (RC.merTr (D.level n).rb τ y)) f hMm hf.1
    (ENNReal.ofReal ((D.level n).ρb D.Pl D.K)) hMb
  refine h1.trans ?_
  calc ENNReal.ofReal (Real.sqrt (((D.level n).ρb D.Pl D.K)⁻¹ * Real.pi⁻¹) * ((D.level n).ε⁻¹)⁻¹) *
        IIIa.ltauLq (2 * cOf (D.level n).ν / (D.level n).ε⁻¹) 2
          (fun τ y => ENNReal.ofReal (RC.merTr (D.level n).rb τ y) * f τ y)
      ≤ ENNReal.ofReal (Real.sqrt (((D.level n).ρb D.Pl D.K)⁻¹ * Real.pi⁻¹) * ((D.level n).ε⁻¹)⁻¹) *
        (ENNReal.ofReal ((D.level n).ρb D.Pl D.K) *
          IIIa.ltauLq (2 * cOf (D.level n).ν / (D.level n).ε⁻¹) (22 / 3) f) :=
        mul_le_mul' le_rfl h2
    _ = ENNReal.ofReal (Real.sqrt (((D.level n).ρb D.Pl D.K)⁻¹ * Real.pi⁻¹) *
          ((D.level n).ε⁻¹)⁻¹ * (D.level n).ρb D.Pl D.K) *
        IIIa.ltauLq (2 * cOf (D.level n).ν / (D.level n).ε⁻¹) (22 / 3) f := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ _ := by
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        rw [hρdef]
        exact RC.repConst D.K.k0 hst.C0_pos hν0 e2.1 hε

/-- **Repair multiplication on the transition window** (source 5134-5139: `‖r_b‖_{C_τL^{11/4}} ≤
P_νρ`; 2698-2713: the scaled repair receiver `ρ_b^{-1/2}H_T`; 2683-2689: chart to physical;
5338-5339: Hölder `1/2 = 4/11 + 3/22` against the `L^{22/3}` receiver). -/
theorem repChart (dm dp : ℝ) : RepChart dm dp :=
  repChart_of (fun D _ _ hst => D.rbMerFacts hst) dm dp

end UnforcedLeray.Short.PartIIIb.Concrete

end
