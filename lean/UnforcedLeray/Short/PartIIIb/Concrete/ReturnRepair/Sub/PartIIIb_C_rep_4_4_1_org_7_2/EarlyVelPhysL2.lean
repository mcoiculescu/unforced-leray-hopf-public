import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4_4_1_org_7_2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.SrcPairing.Lift
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Isos

/-!
# Proof of the leaf `EarlyVelPhysL2` (`PartIII-b:C/rep/4/4/1/org/7/2/3`, source 2683-2689, 5173-5176)

With `C₁ = 1`. The early truncation `earlyTrunc ν w` is supported in `νs ≤ 3/2`, where
`g(max s 0) ≤ Γ` by hypothesis (at `s = 0` for `s < 0`), so `g⁻¹ Γ ≥ 1` there. Pointwise
`|earlyTrunc ν w|² ≤ Γ²π⁻¹ · (π g⁻²) |w|²`, and integrating against `π g⁻² dageμ(-3/2)` gives the
body norm `‖w‖²`. The phase identity `sp_lintegral_velPhys` supplies the factor `π ε⁻²`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)
open UnforcedLeray.PhaseSpace

theorem earlyVelPhysL2 : EarlyVelPhysL2 := by
  refine ⟨1, zero_le_one, ?_⟩
  intro Pl L w Γ hΓ
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hc := cOf_pos hν
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hπ' : Real.pi * Real.pi⁻¹ = 1 := mul_inv_cancel₀ hπ
  have hmeas : Measurable (w : Chart → Merid) := (Lp.stronglyMeasurable w).measurable
  have hb : Measurable (earlyTrunc L.ν (w : Chart → Merid)) := by
    unfold earlyTrunc
    exact Measurable.ite
      (measurableSet_le (measurable_const.mul measurable_fst) measurable_const) hmeas
      measurable_const
  have h1 := SrcPairing.sp_lintegral_velPhys hc hε hb
  have e1 : ∀ (t : ℝ) (y : Space),
      ENNReal.ofReal ‖velPhys L.ε⁻¹ (cOf L.ν) (earlyTrunc L.ν (w : Chart → Merid)) (t, y)‖ ^ 2 =
        ‖velPhys L.ε⁻¹ (cOf L.ν) (earlyTrunc L.ν (w : Chart → Merid)) (t, y)‖ₑ ^ (2 : ℝ) :=
    fun t y => by rw [ofReal_norm, ENNReal.rpow_two]
  simp only [e1]
  rw [h1]
  -- pointwise bound on the early truncation
  have hpt : ∀ p : Chart,
      ‖earlyTrunc L.ν (w : Chart → Merid) p‖ₑ ^ (2 : ℝ) ≤
        ENNReal.ofReal (Real.pi⁻¹ * Γ ^ 2) *
          (ENNReal.ofReal (Real.pi * ginv (gRate Pl) L.ν p ^ 2) *
            ‖(w : Chart → Merid) p‖ₑ ^ (2 : ℝ)) := by
    intro p
    by_cases hp : L.ν * p.1 ≤ 3 / 2
    · have hb' : earlyTrunc L.ν (w : Chart → Merid) p = (w : Chart → Merid) p := by
        unfold earlyTrunc
        rw [if_pos hp]
      rw [hb']
      have hgmax : UnforcedLeray.Short.IIIa.gainG (gRate Pl) L.ν (max p.1 0) ≤ Γ := by
        rcases le_total 0 p.1 with h0 | h0
        · rw [max_eq_left h0]
          apply hΓ p.1 h0
          rw [le_div_iff₀ hν, mul_comm]
          exact hp
        · rw [max_eq_right h0]
          exact hΓ 0 le_rfl (by positivity)
      have hg : 0 < UnforcedLeray.Short.IIIa.gainG (gRate Pl) L.ν (max p.1 0) := by
        unfold UnforcedLeray.Short.IIIa.gainG
        exact Real.exp_pos _
      have h1g : 1 ≤ Γ * ginv (gRate Pl) L.ν p := by
        unfold ginv
        rw [← div_eq_mul_inv, le_div_iff₀ hg, one_mul]
        exact hgmax
      have hsq : 1 ≤ Γ ^ 2 * ginv (gRate Pl) L.ν p ^ 2 := by
        calc (1 : ℝ) ≤ (Γ * ginv (gRate Pl) L.ν p) ^ 2 := one_le_pow₀ h1g
          _ = Γ ^ 2 * ginv (gRate Pl) L.ν p ^ 2 := mul_pow _ _ _
      have hk : 1 ≤ ENNReal.ofReal (Real.pi⁻¹ * Γ ^ 2) *
          ENNReal.ofReal (Real.pi * ginv (gRate Pl) L.ν p ^ 2) := by
        rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ Real.pi⁻¹ * Γ ^ 2 by positivity)]
        apply ENNReal.one_le_ofReal.2
        have e : Real.pi⁻¹ * Γ ^ 2 * (Real.pi * ginv (gRate Pl) L.ν p ^ 2) =
            Γ ^ 2 * ginv (gRate Pl) L.ν p ^ 2 := by
          linear_combination (Γ ^ 2 * ginv (gRate Pl) L.ν p ^ 2) * hπ'
        rw [e]
        exact hsq
      calc ‖(w : Chart → Merid) p‖ₑ ^ (2 : ℝ)
          = 1 * ‖(w : Chart → Merid) p‖ₑ ^ (2 : ℝ) := (one_mul _).symm
        _ ≤ (ENNReal.ofReal (Real.pi⁻¹ * Γ ^ 2) *
              ENNReal.ofReal (Real.pi * ginv (gRate Pl) L.ν p ^ 2)) *
              ‖(w : Chart → Merid) p‖ₑ ^ (2 : ℝ) := by gcongr
        _ = ENNReal.ofReal (Real.pi⁻¹ * Γ ^ 2) *
              (ENNReal.ofReal (Real.pi * ginv (gRate Pl) L.ν p ^ 2) *
                ‖(w : Chart → Merid) p‖ₑ ^ (2 : ℝ)) := mul_assoc _ _ _
    · have hb' : earlyTrunc L.ν (w : Chart → Merid) p = 0 := by
        unfold earlyTrunc
        rw [if_neg hp]
      rw [hb', enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num)]
      exact zero_le
  -- measurability and the exact integral identity for the density `π g⁻²`
  have hgm : Measurable fun p : Chart => ENNReal.ofReal (Real.pi * ginv (gRate Pl) L.ν p ^ 2) :=
    (((NearInst.ginv_measurable' (gRate Pl) L.ν).pow_const 2).const_mul Real.pi).ennreal_ofReal
  have hwm : Measurable fun p : Chart => ‖(w : Chart → Merid) p‖ₑ ^ (2 : ℝ) :=
    hmeas.enorm.pow_const _
  have hI : ∫⁻ p, ‖(w : Chart → Merid) p‖ₑ ^ (2 : ℝ)
        ∂bodyMeasure (cOf L.ν) (gRate Pl) L.ν =
      ∫⁻ p, ENNReal.ofReal (Real.pi * ginv (gRate Pl) L.ν p ^ 2) *
          ‖(w : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂ageμ (cOf L.ν) (-3 / 2) := by
    unfold bodyMeasure
    exact lintegral_withDensity_eq_lintegral_mul _ hgm hwm
  have hI2 : ∫⁻ p, ‖earlyTrunc L.ν (w : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂ageμ (cOf L.ν) (-3 / 2) ≤
      ENNReal.ofReal (Real.pi⁻¹ * Γ ^ 2) *
        ∫⁻ p, ‖(w : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂bodyMeasure (cOf L.ν) (gRate Pl) L.ν := by
    rw [hI, ← lintegral_const_mul' (ENNReal.ofReal (Real.pi⁻¹ * Γ ^ 2)) _ ENNReal.ofReal_ne_top]
    exact lintegral_mono hpt
  -- the body norm
  have hnorm : ENNReal.ofReal ‖w‖ =
      eLpNorm (w : Chart → Merid) 2 (bodyMeasure (cOf L.ν) (gRate Pl) L.ν) := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.memLp w).eLpNorm_lt_top.ne]
  have hE : eLpNorm (w : Chart → Merid) 2 (bodyMeasure (cOf L.ν) (gRate Pl) L.ν) ^ 2 =
      ∫⁻ p, ‖(w : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂bodyMeasure (cOf L.ν) (gRate Pl) L.ν := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hEn : ENNReal.ofReal ‖w‖ ^ 2 =
      ∫⁻ p, ‖(w : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂bodyMeasure (cOf L.ν) (gRate Pl) L.ν := by
    rw [hnorm, hE]
  calc ENNReal.ofReal (Real.pi * L.ε⁻¹ ^ 2) *
        ∫⁻ p, ‖earlyTrunc L.ν (w : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂ageμ (cOf L.ν) (-3 / 2)
      ≤ ENNReal.ofReal (Real.pi * L.ε⁻¹ ^ 2) *
          (ENNReal.ofReal (Real.pi⁻¹ * Γ ^ 2) *
            ∫⁻ p, ‖(w : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂bodyMeasure (cOf L.ν) (gRate Pl) L.ν) :=
        by gcongr
    _ = ENNReal.ofReal (Real.pi * L.ε⁻¹ ^ 2) *
          (ENNReal.ofReal (Real.pi⁻¹ * Γ ^ 2) * ENNReal.ofReal ‖w‖ ^ 2) := by rw [hEn]
    _ = ENNReal.ofReal ((1 * L.ε⁻¹ * Γ * ‖w‖) ^ 2) := by
        rw [← ENNReal.ofReal_pow (norm_nonneg _),
          ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ Real.pi⁻¹ * Γ ^ 2 by positivity),
          ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ Real.pi * L.ε⁻¹ ^ 2 by positivity)]
        congr 1
        linear_combination (L.ε⁻¹ ^ 2 * Γ ^ 2 * ‖w‖ ^ 2) * hπ'

end UnforcedLeray.Short.PartIIIb.Concrete
