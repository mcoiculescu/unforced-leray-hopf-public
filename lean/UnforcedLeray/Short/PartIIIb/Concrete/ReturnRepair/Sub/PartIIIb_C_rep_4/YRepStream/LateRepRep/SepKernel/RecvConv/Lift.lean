import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepRep.SepKernel.RecvConv.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_1.RbFacts
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.StressLift.CartLift
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_4
import UnforcedLeray.Short.PartIIIa.Compose
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.AgeShift
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.PolarReduction
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.ChartChange
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.ChartChangeSE
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.ChartChangeTQ
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.ChartL2Source
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.GAxFacts
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.CartLiftNormOffAxis
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.AxisNull

/-!
# `PartIII-b:C/rep/4/4/1/org/6/1/3` (lift leaf): the lift identity for the repair receiver

Source `the November 2 reference manuscript` 2683-2700 (`𝒩_T T = sT`,
`‖𝒩_T T‖²_{Y₂} = πR²‖T‖²_{H_T}`).  For the measurable symmetric no-swirl chart tensor `repG w`
(`r_b` jointly continuous, `w` an `L²` representative), `ChartL2Source` (chart change, polar
reduction, age shift) gives `P⁻¹∫₀ᴾ∫|𝒩_T repG w|² = πR² ∫|repG w|² d(ageμ c (-1/2))`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Masked

/-- The Euclidean norm of `ten3Of M` is the Frobenius norm of `M`. -/
theorem rcl_norm_ten3Of (M : Matrix (Fin 3) (Fin 3) ℝ) :
    ‖ten3Of M‖ = UnforcedLeray.Short.IIIa.tensorNorm M := by
  rw [EuclideanSpace.norm_eq]
  unfold UnforcedLeray.Short.IIIa.tensorNorm
  congr 1
  simp [ten3Of, Fintype.sum_prod_type, Real.norm_eq_abs, sq_abs]

theorem rcl_continuous_symOuter :
    Continuous (fun x : Merid × Merid => ten3Of (UnforcedLeray.Short.IIIa.symOuter x.1 x.2)) := by
  unfold ten3Of
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun ab => ?_)
  obtain ⟨i, j⟩ := ab
  have h0 : Continuous fun x : Merid × Merid => x.1 0 := (PiLp.continuous_apply 2 _ 0).comp continuous_fst
  have h1 : Continuous fun x : Merid × Merid => x.1 1 := (PiLp.continuous_apply 2 _ 1).comp continuous_fst
  have h2 : Continuous fun x : Merid × Merid => x.2 0 := (PiLp.continuous_apply 2 _ 0).comp continuous_snd
  have h3 : Continuous fun x : Merid × Merid => x.2 1 := (PiLp.continuous_apply 2 _ 1).comp continuous_snd
  fin_cases i <;> fin_cases j <;>
    simp [UnforcedLeray.Short.IIIa.symOuter, UnforcedLeray.Short.IIIa.embedMerid] <;>
    first | exact continuous_const | fun_prop


/-- **The lift identity for a measurable symmetric no-swirl chart tensor** (source 2683-2700,
`ChartL2Source`, axis null, `cartLiftNormOffAxis`). -/
theorem rcl_phase_eq (R c : ℝ) (hR : 0 < R) (hc : 0 < c) (g : Chart → Ten3) (hg : Measurable g)
    (hns : ∀ p, ‖g p‖ₑ = ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm (nsSym (g p)))) :
    (∫⁻ τ in Ioc (0 : ℝ) (2 * c / R), ∫⁻ z : Space,
        ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm (strPhys R c g (τ, z))) ^ (2 : ℝ)) =
      ENNReal.ofReal (2 * Real.pi * R * c) * ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂(ageμ c (-1 / 2)) := by
  have hL2 := chartL2Source_of ageShift_holds polarReduction_holds
    (chartChange_of chartChangeSE_holds chartChangeTQ_holds) gAxFacts_holds R c hR hc g hg
  have hae : ∀ᵐ z ∂(volume : Measure Space), hRad z ≠ 0 := by
    rw [ae_iff]
    refine measure_mono_null (fun z hz => ?_) axisNull_holds
    exact not_not.1 hz
  have hstep : ∀ τ : ℝ,
      (∫⁻ z : Space, ENNReal.ofReal
          (UnforcedLeray.Short.IIIa.tensorNorm (strPhys R c g (τ, z))) ^ (2 : ℝ)) =
        ∫⁻ z : Space, gAx R c g τ z ^ (2 : ℝ) := by
    intro τ
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with z hz
    have := cartLiftNormOffAxis_holds R c g τ z hz
    unfold UnforcedLeray.Short.IIIa.srcNorm at this
    show ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm (cartLift R c g τ z)) ^ (2 : ℝ) = _
    rw [this]
  have hIoc : (∫⁻ τ in Ioc (0 : ℝ) (2 * c / R), ∫⁻ z : Space, gAx R c g τ z ^ (2 : ℝ)) =
      ∫⁻ τ in Ico (0 : ℝ) (2 * c / R), ∫⁻ z : Space, gAx R c g τ z ^ (2 : ℝ) :=
    setLIntegral_congr (Ico_ae_eq_Ioc.symm : Ioc 0 (2 * c / R) =ᵐ[volume] Ico 0 (2 * c / R))
  rw [lintegral_congr hstep, hIoc, hL2]
  congr 1
  exact lintegral_congr fun x => by rw [hns x]


private theorem rcl_mul_rpow_half (x y : ℝ≥0∞) : x * y ^ (1 / 2 : ℝ) = (x ^ 2 * y) ^ (1 / 2 : ℝ) := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- **(ii) The lift identity** for `repG w`. -/
theorem RecvConvOrg.recvLift : RecvConvOrg.RecvLift := by
  intro Pl K L S hC0 hsplit hP w
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
  -- measurability of `repG w`
  obtain ⟨z, -, -, hrb, -⟩ := hsplit.state
  have hP1 : (L.params Pl).period ≤ 1 := hP
  have hcont : Continuous (fun x : ℝ × Space => L.rb x.1 x.2) := by
    rw [hrb]
    exact UnforcedLeray.Short.IIIa.corr_continuous (L.params Pl) hP1 z
  have hcc : Measurable (UnforcedLeray.Short.IIIa.chartCoeff L.ε⁻¹ L.rb) :=
    measurable_chartCoeff_of_continuous L.ε⁻¹ hcont
  have hw : Measurable (w : Chart → Merid) := (Lp.stronglyMeasurable w).measurable
  have hg : Measurable (repG Pl K L w) :=
    rcl_continuous_symOuter.measurable.comp (hcc.prodMk hw)
  have hns : ∀ p, ‖repG Pl K L w p‖ₑ = ENNReal.ofReal
      (UnforcedLeray.Short.IIIa.tensorNorm (nsSym (repG Pl K L w p))) := by
    intro p
    have e : nsSym (repG Pl K L w p) = UnforcedLeray.Short.IIIa.symOuter
        (UnforcedLeray.Short.IIIa.chartCoeff L.ε⁻¹ L.rb p) (w p) := cl_nsSym_symOuter _ _
    rw [e, ← ofReal_norm]
    show ENNReal.ofReal ‖ten3Of _‖ = _
    rw [rcl_norm_ten3Of]
  have hphase := rcl_phase_eq L.ε⁻¹ (cOf L.ν) hR hc _ hg hns
  have hP2 : 2 * (cOf L.ν) / L.ε⁻¹ = 2 * L.ε * cOf L.ν := by
    field_simp
  rw [hP2] at hphase
  set I := ∫⁻ x, ‖repG Pl K L w x‖ₑ ^ (2 : ℝ) ∂(ageμ (cOf L.ν) (-1 / 2)) with hI
  have h2 : (2 : ℝ) / 2 = 1 := by norm_num
  have hphaseL : phaseL2Lr (2 * L.ε * cOf L.ν) 2 (strPhys L.ε⁻¹ (cOf L.ν) (repG Pl K L w)) =
      (ENNReal.ofReal (2 * L.ε * cOf L.ν)⁻¹ *
        (ENNReal.ofReal (2 * Real.pi * L.ε⁻¹ * cOf L.ν) * I)) ^ (1 / 2 : ℝ) := by
    unfold phaseL2Lr
    rw [← hphase]
    congr 2
    refine setLIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
    rw [h2, ENNReal.rpow_one]
  have hhT : htUng (cOf L.ν) (L.ρb Pl K) (repG Pl K L w) =
      (ENNReal.ofReal (L.ρb Pl K)⁻¹ * I) ^ (1 / 2 : ℝ) := by
    unfold htUng htRhoMeasure
    rw [lintegral_smul_measure]
    rfl
  rw [hhT, hphaseL, rcl_mul_rpow_half]
  congr 1
  have hρ0 : 0 < L.ρb Pl K * (Real.pi * (L.ε⁻¹) ^ 2) := by positivity
  rw [← mul_assoc, ← ENNReal.ofReal_pow (inv_nonneg.2 (Real.sqrt_nonneg _)),
    ← ENNReal.ofReal_mul (by positivity), ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [inv_pow, Real.sq_sqrt hρ0.le]
  field_simp

end UnforcedLeray.Short.PartIIIb.Concrete
