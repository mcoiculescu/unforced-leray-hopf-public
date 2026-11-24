import UnforcedLeray.Short.PartI.Sub.PartI_T13
import UnforcedLeray.Short.PartI.Sub.PartI_T13.SmoothL2
import UnforcedLeray.Short.PartI.Tasks.OverlapHighNorm
import UnforcedLeray.Short.PartI.Sub.PartI_T14

/-!
# `PartI:T13/2` (`Sub/PartI_T13/EnergyBalance.lean`): `OverlapFluctuationEnergyBalance`

Source of record: `the November 2 reference manuscript`, lines 390-394
(old 354-358).

Proves `overlapFluctuationEnergyBalance_proof (hSmooth : OverlapFluctuationSmoothL2) :
OverlapFluctuationEnergyBalance`:
1. Exact fluctuation energy identity on the unit cylinder:
   `HasDerivAt (fun t => jetEnergy 1 0 (W t))
     (2 * (-jetEnergy 1 1 (W T) - eC ν c * ∫ z in Cyl.cell 1, W T z 0 * W T z 1 * deriv b z.2)) T`;
2. Shear-production bound:
   `|∫ z in Cyl.cell 1, W T z 0 * W T z 1 * deriv b z.2| ≤
     (B0277.supNormD 1 (U T)).toReal * jetEnergy 1 0 (W T)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec jet cellL2)

/-! ### 1. Horizontal orthogonality on the unit cylinder -/

/-- Coordinate projection of `hmean 1 a` on the unit cylinder. -/
theorem hmean_unit_apply_vec {a : Plane → Vec} (ha : Continuous a) (Y : ℝ) (k : Fin 2) :
    (hmean 1 a Y) k = hmean 1 (fun w => a w k) Y := by
  have h := hfluct_unit_apply_vec ha (0, Y) k
  unfold hfluct at h
  rw [PiLp.sub_apply] at h
  linarith

/-- On each horizontal slice `Y`, `∫_{X ∈ [-1/2, 1/2)} hfluct 1 f (X, Y) * c_Y = 0`. -/
theorem slice_integral_hfluct_mul_const_unit {f : Plane → ℝ} (hf : Continuous f) (Y cY : ℝ) :
    ∫ X in Ico (-1 / 2 : ℝ) (1 / 2), hfluct 1 f (X, Y) * cY = 0 := by
  let μI : Measure ℝ := volume.restrict (Ico (-1 / 2 : ℝ) (1 / 2))
  have : IsFiniteMeasure μI :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ico_lt_top⟩
  set m : ℝ := hmean 1 f Y
  have hm_eq : m = ∫ X, f (X, Y) ∂μI := by
    simpa [m, μI] using meanEnergy_hmean_Ico (c := 1) f Y
  have hfY : Continuous (fun X : ℝ => f (X, Y)) :=
    hf.comp (continuous_id.prodMk continuous_const)
  have hi1 : Integrable (fun X : ℝ => f (X, Y)) μI :=
    hfY.integrableOn_Icc.mono_set Ico_subset_Icc_self
  have hic : Integrable (fun _ : ℝ => m) μI := integrable_const m
  have hvol : ∫ _X, m ∂μI = m := by
    change ∫ _X in Ico (-1 / 2 : ℝ) (1 / 2), m = m
    rw [setIntegral_const, Measure.real, Real.volume_Ico,
      show (1 / 2 : ℝ) - (-1 / 2) = 1 by ring, ENNReal.ofReal_one, ENNReal.toReal_one, one_smul]
  have hsub : ∫ X, hfluct 1 f (X, Y) ∂μI = 0 := by
    have h1 : ∫ X, (f (X, Y) - m) ∂μI = (∫ X, f (X, Y) ∂μI) - ∫ _X, m ∂μI :=
      integral_sub hi1 hic
    change ∫ X, (f (X, Y) - m) ∂μI = 0
    rw [h1, ← hm_eq, hvol, sub_self]
  change ∫ X, hfluct 1 f (X, Y) * cY ∂μI = 0
  rw [integral_mul_const, hsub, zero_mul]

/-- Horizontal fluctuation `hfluct 1 f` is orthogonal on `Cyl.cell 1` to `z ↦ hmean 1 g z.2`
for any continuous `f, g ∈ L²(Cyl.cell 1)`. -/
theorem integral_hfluct_mul_hmean_unit {f g : Plane → ℝ}
    (hf : Continuous f) (hfL2 : MemLp f 2 (Cyl.cellμ 1))
    (hg : Continuous g) (hgL2 : MemLp g 2 (Cyl.cellμ 1)) :
    ∫ z in Cyl.cell 1, hfluct 1 f z * hmean 1 g z.2 = 0 := by
  let μI : Measure ℝ := volume.restrict (Ico (-1 / 2 : ℝ) (1 / 2))
  have : IsFiniteMeasure μI :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ico_lt_top⟩
  have hprod_g : Integrable (fun z : Plane => g z ^ 2) (μI.prod volume) := by
    rw [← Cyl.cellμ_eq_prod 1]
    exact hgL2.integrable_sq
  let Φ : ℝ → ℝ := fun Y => 1⁻¹ * ∫ X in Ico (-1 / 2 : ℝ) (1 / 2), g (X, Y) ^ 2
  have hΦ_int : Integrable Φ volume := hprod_g.integral_prod_right.const_mul 1⁻¹
  have hΦ_prod : Integrable (fun z : Plane => Φ z.2) (Cyl.cellμ 1) := by
    rw [Cyl.cellμ_eq_prod 1]
    exact hΦ_int.comp_snd _
  have hm_cont : Continuous (fun z : Plane => hmean 1 g z.2) :=
    (cpH2_continuous_hmean one_pos hg).comp continuous_snd
  have hm_mem : MemLp (fun z : Plane => hmean 1 g z.2) 2 (Cyl.cellμ 1) := by
    refine (memLp_two_iff_integrable_sq hm_cont.aestronglyMeasurable).2 ?_
    refine Integrable.mono' hΦ_prod (hm_cont.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact meanEnergy_hmean_sq_le one_pos hg (hg.pow 2) (fun _ => le_rfl) z.2
  have hwf_mem : MemLp (hfluct 1 f) 2 (Cyl.cellμ 1) :=
    (memLp_and_integral_hfluct_unit_sq_le hf hfL2).1
  have hint : Integrable (fun z : Plane => hfluct 1 f z * hmean 1 g z.2) (μI.prod volume) := by
    rw [← Cyl.cellμ_eq_prod 1]
    exact hwf_mem.integrable_mul hm_mem
  change ∫ z, hfluct 1 f z * hmean 1 g z.2 ∂(Cyl.cellμ 1) = 0
  rw [Cyl.cellμ_eq_prod 1, MeasureTheory.integral_prod_symm _ hint]
  have hslice : ∀ Y : ℝ, ∫ X, hfluct 1 f (X, Y) * hmean 1 g Y ∂μI = 0 :=
    fun Y => slice_integral_hfluct_mul_const_unit hf Y (hmean 1 g Y)
  simp_rw [hslice, integral_zero]

/-- For continuous `f, g ∈ L²(Cyl.cell 1)`,
`∫_{Cyl.cell 1} hfluct 1 f * hfluct 1 g = ∫_{Cyl.cell 1} hfluct 1 f * g`. -/
theorem integral_hfluct_mul_hfluct_unit {f g : Plane → ℝ}
    (hf : Continuous f) (hfL2 : MemLp f 2 (Cyl.cellμ 1))
    (hg : Continuous g) (hgL2 : MemLp g 2 (Cyl.cellμ 1)) :
    ∫ z in Cyl.cell 1, hfluct 1 f z * hfluct 1 g z =
      ∫ z in Cyl.cell 1, hfluct 1 f z * g z := by
  have hwf_mem : MemLp (hfluct 1 f) 2 (Cyl.cellμ 1) :=
    (memLp_and_integral_hfluct_unit_sq_le hf hfL2).1
  have hwg_mem : MemLp (hfluct 1 g) 2 (Cyl.cellμ 1) :=
    (memLp_and_integral_hfluct_unit_sq_le hg hgL2).1
  have hm_mem : MemLp (fun z : Plane => hmean 1 g z.2) 2 (Cyl.cellμ 1) := by
    have heq : (fun z : Plane => hmean 1 g z.2) = fun z => g z - hfluct 1 g z := by
      funext z; unfold hfluct; ring
    rw [heq]
    exact hgL2.sub hwg_mem
  have hi1 : Integrable (fun z : Plane => hfluct 1 f z * g z) (Cyl.cellμ 1) :=
    hwf_mem.integrable_mul hgL2
  have hi2 : Integrable (fun z : Plane => hfluct 1 f z * hmean 1 g z.2) (Cyl.cellμ 1) :=
    hwf_mem.integrable_mul hm_mem
  have hpt : (fun z : Plane => hfluct 1 f z * hfluct 1 g z) =
      fun z : Plane => hfluct 1 f z * g z - hfluct 1 f z * hmean 1 g z.2 := by
    funext z
    unfold hfluct
    ring
  have hsub : ∫ z, (hfluct 1 f z * g z - hfluct 1 f z * hmean 1 g z.2) ∂(Cyl.cellμ 1) =
      (∫ z, hfluct 1 f z * g z ∂(Cyl.cellμ 1)) -
        ∫ z, hfluct 1 f z * hmean 1 g z.2 ∂(Cyl.cellμ 1) :=
    integral_sub hi1 hi2
  have h0 : ∫ z, hfluct 1 f z * hmean 1 g z.2 ∂(Cyl.cellμ 1) = 0 :=
    integral_hfluct_mul_hmean_unit hf hfL2 hg hgL2
  change ∫ z, hfluct 1 f z * hfluct 1 g z ∂(Cyl.cellμ 1) =
    ∫ z, hfluct 1 f z * g z ∂(Cyl.cellμ 1)
  rw [hpt, hsub, h0, sub_zero]

/-! ### 2. Shear-production bound (`Part D`) -/

/-- Pointwise bound `|deriv b Y| ≤ (B0277.supNormD 1 U).toReal` for
`b Y = hmean 1 U Y 0` when `CellSmoothL2 1 U`. -/
theorem abs_deriv_hmean_fst_le_supNormD {U : Plane → Vec} (hU : CellSmoothL2 1 U) (Y : ℝ) :
    |deriv (fun y => hmean 1 U y 0) Y| ≤ (B0277.supNormD 1 U).toReal := by
  let S : ℝ := (B0277.supNormD 1 U).toReal
  obtain ⟨CSup, _, hBrSup⟩ := jetSupBridge_proof 1
  have hSup_lt : B0277.supNormD 1 U < ⊤ :=
    (hBrSup 1 le_rfl U hU).2.trans_lt ENNReal.ofReal_lt_top
  have hSup_le : B0277.supNormD 1 U ≤ ENNReal.ofReal S :=
    le_of_eq (ENNReal.ofReal_toReal hSup_lt.ne).symm
  have hproj : ‖(EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
      simpa using PiLp.norm_apply_le x 0)
  have hU0 : ContDiff ℝ ∞ (fun z : Plane => U z 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hU.1
  have hpt : ∀ z : Plane, ‖Cyl.partialEta (fun w : Plane => U w 0) z‖ ≤ S := by
    intro z
    rw [Real.norm_eq_abs]
    have hw_le : |wordComp [false] U 0 z| ≤ ‖iteratedFDeriv ℝ 1 (fun x => U x 0) z‖ :=
      (cylJetWord_proof (fun x => U x 0) hU0 1 z).1 [false] rfl
    have hcomp := ContinuousLinearMap.norm_iteratedFDeriv_comp_left
      (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ)
      (f := U) (x := z) (n := 1) hU.1.contDiffAt (by exact_mod_cast le_top)
    have h1 : ‖iteratedFDeriv ℝ 1 (fun x => U x 0) z‖ ≤ ‖iteratedFDeriv ℝ 1 U z‖ := by
      calc ‖iteratedFDeriv ℝ 1 (fun x => U x 0) z‖
          ≤ ‖(EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ)‖ * ‖iteratedFDeriv ℝ 1 U z‖ := hcomp
        _ ≤ 1 * ‖iteratedFDeriv ℝ 1 U z‖ :=
            mul_le_mul_of_nonneg_right hproj (norm_nonneg _)
        _ = ‖iteratedFDeriv ℝ 1 U z‖ := one_mul _
    have h2 : ‖iteratedFDeriv ℝ 1 U z‖ ≤ S :=
      B0277.norm_le_of_supNormD_le ENNReal.toReal_nonneg hSup_le z
    exact (hw_le.trans h1).trans h2
  have hb_eq : (fun y : ℝ => hmean 1 U y 0) = hmean 1 (fun w : Plane => U w 0) := by
    funext y
    exact hmean_unit_apply_vec hU.1.continuous y 0
  rw [hb_eq, cpH2_deriv_hmean (hU0.of_le (by simp))]
  have hnorm := meanEnergy_norm_hmean_le one_pos continuous_const hpt Y
  have hvol : (1 : ℝ)⁻¹ * ∫ _q in Ico (-1 / 2 : ℝ) (1 / 2), S = S := by
    rw [setIntegral_const, Measure.real, Real.volume_Ico,
      show (1 / 2 : ℝ) - (-1 / 2) = 1 by ring, ENNReal.ofReal_one, ENNReal.toReal_one,
      one_smul, inv_one, one_mul]
  rw [Real.norm_eq_abs, hvol] at hnorm
  exact hnorm

/-- Shear-production integral bound on the unit cylinder:
`|∫_{Cyl.cell 1} W₀ W₁ ∂_Y b| ≤ (B0277.supNormD 1 U).toReal * jetEnergy 1 0 W`. -/
theorem overlap_shear_production_bound {U : Plane → Vec} (hU : CellSmoothL2 1 U)
    (hW : CellSmoothL2 1 (hfluct 1 U)) :
    let W := hfluct 1 U
    let b := fun Y => hmean 1 U Y 0
    Integrable (fun z : Plane => W z 0 * W z 1 * deriv b z.2) (Cyl.cellμ 1) ∧
      |∫ z in Cyl.cell 1, W z 0 * W z 1 * deriv b z.2| ≤
        (B0277.supNormD 1 U).toReal * jetEnergy 1 0 W := by
  intro W b
  let S : ℝ := (B0277.supNormD 1 U).toReal
  have hb_cont : Continuous (deriv b) := by
    have hb_eq : b = hmean 1 (fun w : Plane => U w 0) := by
      funext y; exact hmean_unit_apply_vec hU.1.continuous y 0
    have hU0 : ContDiff ℝ ∞ (fun z : Plane => U z 0) :=
      (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hU.1
    rw [hb_eq, cpH2_deriv_hmean (hU0.of_le (by simp))]
    exact (hmean_unit_contDiff (B0151.contDiff_derivWord hU0 [false])).continuous
  have hW_cont : Continuous (fun z : Plane => W z 0 * W z 1 * deriv b z.2) :=
    (((EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).continuous.comp hW.1.continuous).mul
      ((EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).continuous.comp hW.1.continuous)).mul
      (hb_cont.comp continuous_snd)
  have hi0 : Integrable (fun z : Plane => W z 0 ^ 2) (Cyl.cellμ 1) := (hW.2.2 [] 0).integrable_sq
  have hi1 : Integrable (fun z : Plane => W z 1 ^ 2) (Cyl.cellμ 1) := (hW.2.2 [] 1).integrable_sq
  have hdom_int : Integrable (fun z : Plane => S * (W z 0 ^ 2 + W z 1 ^ 2)) (Cyl.cellμ 1) :=
    (hi0.add hi1).const_mul S
  have hpt : ∀ z : Plane, ‖W z 0 * W z 1 * deriv b z.2‖ ≤ S * (W z 0 ^ 2 + W z 1 ^ 2) := by
    intro z
    rw [Real.norm_eq_abs, abs_mul]
    have hprod : |W z 0 * W z 1| ≤ W z 0 ^ 2 + W z 1 ^ 2 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (W z 0 + W z 1), sq_nonneg (W z 0 - W z 1)]
    have hb_le : |deriv b z.2| ≤ S := abs_deriv_hmean_fst_le_supNormD hU z.2
    calc |W z 0 * W z 1| * |deriv b z.2|
        ≤ (W z 0 ^ 2 + W z 1 ^ 2) * S :=
          mul_le_mul hprod hb_le (abs_nonneg _) (add_nonneg (sq_nonneg _) (sq_nonneg _))
      _ = S * (W z 0 ^ 2 + W z 1 ^ 2) := mul_comm _ _
  have hint : Integrable (fun z : Plane => W z 0 * W z 1 * deriv b z.2) (Cyl.cellμ 1) :=
    Integrable.mono' hdom_int hW_cont.aestronglyMeasurable (Eventually.of_forall hpt)
  refine ⟨hint, ?_⟩
  have hJ0 : jetEnergy 1 0 W =
      (∫ z, W z 0 ^ 2 ∂(Cyl.cellμ 1)) + (∫ z, W z 1 ^ 2 ∂(Cyl.cellμ 1)) := by
    unfold jetEnergy jetPair
    have hw0 : wordsOfLength 0 = {[]} := by
      ext w; rw [cgn_mem_wordsOfLength, Finset.mem_singleton, List.length_eq_zero_iff]
    simp_rw [hw0, Finset.sum_singleton, Fin.sum_univ_two]
    change ∫ z, (W z 0 * W z 0 + W z 1 * W z 1) ∂(Cyl.cellμ 1) = _
    simp_rw [← sq]
    exact integral_add hi0 hi1
  have hbound := norm_integral_le_of_norm_le hdom_int (Eventually.of_forall hpt)
  have hadd : ∫ z, (W z 0 ^ 2 + W z 1 ^ 2) ∂(Cyl.cellμ 1) =
      (∫ z, W z 0 ^ 2 ∂(Cyl.cellμ 1)) + (∫ z, W z 1 ^ 2 ∂(Cyl.cellμ 1)) :=
    integral_add hi0 hi1
  rw [Real.norm_eq_abs, integral_const_mul, hadd, ← hJ0] at hbound
  exact hbound

/-! ### 3. `SmoothJetL2 1` transfer and viscous/pressure/advection pairings -/

/-- Rescaling `SmoothJetL2 c F` on `Cyl.cell c` to `SmoothJetL2 1` on `Cyl.cell 1`. -/
theorem smoothJetL2_unit_of_dil {c : ℝ} (hc0 : 0 < c) (K : ℝ) {F : Plane → Vec}
    (hF : SmoothJetL2 c F) :
    SmoothJetL2 1 (fun z => K • F (B0155.dil c z)) := by
  have hsm : ContDiff ℝ ∞ (fun z : Plane => K • F (B0155.dil c z)) := by
    have hdil : ContDiff ℝ ∞ (B0155.dil c) := by
      have heq : B0155.dil c = fun z : Plane => c • z := by
        funext z; exact B0155.dil_eq_smul c z
      rw [heq]
      exact contDiff_id.const_smul c
    exact (hF.1.comp hdil).const_smul K
  refine ⟨hsm, fun w k => ?_⟩
  have hwk_sm : ContDiff ℝ ∞ (wordComp w (fun z => K • F (B0155.dil c z)) k) :=
    contDiff_wordComp hsm w k
  rw [memLp_two_iff_integrable_sq hwk_sm.continuous.aestronglyMeasurable]
  have hwc : ∀ Z : Plane, wordComp w (fun z => K • F (B0155.dil c z)) k Z =
      K * c ^ w.length * wordComp w F k (B0155.dil c Z) := by
    intro Z
    have hfun : (fun z : Plane => (K • F (B0155.dil c z)) k) =
        fun z : Plane => K * F (B0155.dil c z) k := by
      funext z; simp [PiLp.smul_apply]
    unfold wordComp
    rw [hfun]
    exact congrFun (derivWord_dil w K c (fun z => F z k)) Z
  have hsq : (fun Z : Plane => (wordComp w (fun z => K • F (B0155.dil c z)) k Z) ^ 2) =
      fun Z : Plane => (K * c ^ w.length) ^ 2 *
        (wordComp w F k (B0155.dil c Z)) ^ 2 := by
    funext Z; rw [hwc Z]; ring
  rw [hsq]
  exact B0155.integrableOn_cell_one_dil hc0 (hF.2 w k).integrable_sq ((K * c ^ w.length) ^ 2)

/-- For `U : Plane → Vec` with `CellSmoothL2 1 U` and `W = hfluct 1 U` with `CellSmoothL2 1 W`,
`jetPair 1 0 W (Train.vecLaplacian U) = -jetEnergy 1 1 W`. -/
theorem jetPair_zero_hfluct_vecLaplacian {U : Plane → Vec} (hU : CellSmoothL2 1 U)
    (hW : CellSmoothL2 1 (hfluct 1 U)) :
    jetPair 1 0 (hfluct 1 U) (Train.vecLaplacian U) = -jetEnergy 1 1 (hfluct 1 U) := by
  set W := hfluct 1 U
  have hIBP := jetViscousIBP_proof 1 one_pos W hW 0
  rw [← hIBP]
  have hcomp_eq : ∀ k : Fin 2,
      ∫ z, W z k * Train.vecLaplacian U z k ∂(Cyl.cellμ 1) =
        ∫ z, W z k * Train.vecLaplacian W z k ∂(Cyl.cellμ 1) := by
    intro k
    have hUk : ContDiff ℝ ∞ (fun z : Plane => U z k) :=
      (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).contDiff.comp hU.1
    have hWk_eq : (fun z : Plane => W z k) = hfluct 1 (fun z => U z k) := by
      funext z; exact hfluct_unit_apply_vec hU.1.continuous z k
    have hlapW : ∀ z : Plane, Train.vecLaplacian W z k =
        wordComp [true, true] U k z + hfluct 1 (wordComp [false, false] U k) z := by
      intro z
      rw [lapLocal_vecLap_apply]
      change Cyl.partialQ (Cyl.partialQ (fun y => W y k)) z +
        Cyl.partialEta (Cyl.partialEta (fun y => W y k)) z = _
      have hUk_eta : ContDiff ℝ ∞ (Cyl.partialEta (fun z => U z k)) :=
        B0151.contDiff_derivWord hUk [false]
      rw [hWk_eq, partialQ_hfluct_unit_eq hUk,
        partialEta_hfluct_unit_eq hUk,
        partialEta_hfluct_unit_eq hUk_eta]
      rfl
    have hlapU : ∀ z : Plane, Train.vecLaplacian U z k =
        wordComp [true, true] U k z + wordComp [false, false] U k z := by
      intro z
      rw [lapLocal_vecLap_apply]
      rfl
    have hiW : MemLp (fun z : Plane => W z k) 2 (Cyl.cellμ 1) := hW.2.2 [] k
    have hi_tt : Integrable (fun z : Plane => W z k * wordComp [true, true] U k z) (Cyl.cellμ 1) :=
      hiW.integrable_mul (hU.2.2 [true, true] k)
    have hi_ffU : Integrable (fun z : Plane => W z k * wordComp [false, false] U k z)
        (Cyl.cellμ 1) :=
      hiW.integrable_mul (hU.2.2 [false, false] k)
    have hff_cont : Continuous (wordComp [false, false] U k) :=
      (B0151.contDiff_derivWord hUk [false, false]).continuous
    have hi_ffW : Integrable (fun z : Plane => W z k * hfluct 1 (wordComp [false, false] U k) z)
        (Cyl.cellμ 1) :=
      hiW.integrable_mul
        (memLp_and_integral_hfluct_unit_sq_le hff_cont (hU.2.2 [false, false] k)).1
    have hptU : (fun z : Plane => W z k * Train.vecLaplacian U z k) =
        fun z : Plane => W z k * wordComp [true, true] U k z +
          W z k * wordComp [false, false] U k z := by
      funext z; rw [hlapU z]; ring
    have hptW : (fun z : Plane => W z k * Train.vecLaplacian W z k) =
        fun z : Plane => W z k * wordComp [true, true] U k z +
          W z k * hfluct 1 (wordComp [false, false] U k) z := by
      funext z; rw [hlapW z]; ring
    have h1 : ∫ z, (W z k * wordComp [true, true] U k z +
        W z k * wordComp [false, false] U k z) ∂(Cyl.cellμ 1) =
        (∫ z, W z k * wordComp [true, true] U k z ∂(Cyl.cellμ 1)) +
          ∫ z, W z k * wordComp [false, false] U k z ∂(Cyl.cellμ 1) :=
      integral_add hi_tt hi_ffU
    have h2 : ∫ z, (W z k * wordComp [true, true] U k z +
        W z k * hfluct 1 (wordComp [false, false] U k) z) ∂(Cyl.cellμ 1) =
        (∫ z, W z k * wordComp [true, true] U k z ∂(Cyl.cellμ 1)) +
          ∫ z, W z k * hfluct 1 (wordComp [false, false] U k) z ∂(Cyl.cellμ 1) :=
      integral_add hi_tt hi_ffW
    rw [hptU, hptW, h1, h2]
    congr 1
    have horth : ∫ z, hfluct 1 (fun z => U z k) z * hfluct 1 (wordComp [false, false] U k) z
        ∂(Cyl.cellμ 1) =
        ∫ z, hfluct 1 (fun z => U z k) z * wordComp [false, false] U k z ∂(Cyl.cellμ 1) :=
      integral_hfluct_mul_hfluct_unit hUk.continuous (hU.2.2 [] k) hff_cont
        (hU.2.2 [false, false] k)
    simpa [← hWk_eq] using horth.symm
  have hw0 : wordsOfLength 0 = {[]} := by
    ext w; rw [cgn_mem_wordsOfLength, Finset.mem_singleton, List.length_eq_zero_iff]
  have hLapU : ∀ k : Fin 2, MemLp (fun z => Train.vecLaplacian U z k) 2 (Cyl.cellμ 1) := by
    intro k
    have heq : (fun z : Plane => Train.vecLaplacian U z k) =
        fun z => wordComp [true, true] U k z + wordComp [false, false] U k z := by
      funext z; rw [lapLocal_vecLap_apply]; rfl
    rw [heq]
    exact (hU.2.2 [true, true] k).add (hU.2.2 [false, false] k)
  have hLapW : ∀ k : Fin 2, MemLp (fun z => Train.vecLaplacian W z k) 2 (Cyl.cellμ 1) := by
    intro k
    have heq : (fun z : Plane => Train.vecLaplacian W z k) =
        fun z => wordComp [true, true] W k z + wordComp [false, false] W k z := by
      funext z; rw [lapLocal_vecLap_apply]; rfl
    rw [heq]
    exact (hW.2.2 [true, true] k).add (hW.2.2 [false, false] k)
  unfold jetPair
  simp_rw [hw0, Finset.sum_singleton, Fin.sum_univ_two]
  have hiU0 : Integrable (fun z => W z 0 * Train.vecLaplacian U z 0) (Cyl.cellμ 1) :=
    (hW.2.2 [] 0).integrable_mul (hLapU 0)
  have hiU1 : Integrable (fun z => W z 1 * Train.vecLaplacian U z 1) (Cyl.cellμ 1) :=
    (hW.2.2 [] 1).integrable_mul (hLapU 1)
  have hiW0 : Integrable (fun z => W z 0 * Train.vecLaplacian W z 0) (Cyl.cellμ 1) :=
    (hW.2.2 [] 0).integrable_mul (hLapW 0)
  have hiW1 : Integrable (fun z => W z 1 * Train.vecLaplacian W z 1) (Cyl.cellμ 1) :=
    (hW.2.2 [] 1).integrable_mul (hLapW 1)
  have hsumU : ∫ z, (W z 0 * Train.vecLaplacian U z 0 + W z 1 * Train.vecLaplacian U z 1)
      ∂(Cyl.cellμ 1) =
      (∫ z, W z 0 * Train.vecLaplacian U z 0 ∂(Cyl.cellμ 1)) +
        ∫ z, W z 1 * Train.vecLaplacian U z 1 ∂(Cyl.cellμ 1) :=
    integral_add hiU0 hiU1
  have hsumW : ∫ z, (W z 0 * Train.vecLaplacian W z 0 + W z 1 * Train.vecLaplacian W z 1)
      ∂(Cyl.cellμ 1) =
      (∫ z, W z 0 * Train.vecLaplacian W z 0 ∂(Cyl.cellμ 1)) +
        ∫ z, W z 1 * Train.vecLaplacian W z 1 ∂(Cyl.cellμ 1) :=
    integral_add hiW0 hiW1
  exact hsumU.trans ((congrArg₂ (· + ·) (hcomp_eq 0) (hcomp_eq 1)).trans hsumW.symm)

/-- Advection pairing identity on the unit cylinder:
`jetPair 1 0 (W T) (Train.advection (U T)) = ∫ z in Cyl.cell 1, W T z 0 * W T z 1 * deriv b z.2`. -/
theorem jetPair_zero_hfluct_advection {ν c : ℝ} (hν : 0 < ν) (hc : 1 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr) {T : ℝ} (hT : 0 ≤ T)
    (hUs : CellSmoothL2 1 (overlapField ν c tr.v T))
    (hWs : CellSmoothL2 1 (hfluct 1 (overlapField ν c tr.v T))) :
    let U := overlapField ν c tr.v T
    let W := hfluct 1 U
    let b := fun Y => hmean 1 U Y 0
    jetPair 1 0 W (Train.advection U) =
      ∫ z in Cyl.cell 1, W z 0 * W z 1 * deriv b z.2 := by
  intro U W b
  have hc0 : 0 < c := zero_lt_one.trans hc
  have hs : 0 < B0155.ageOf ν c T := overlapAgeOf_pos hν hc hT
  have hs' : 0 < B0146.overlapAge ν c + c ^ 2 * T / ν := overlapAge_add_pos hν hc hT
  have hUd : ∀ z : Plane, Cyl.divergence U z = 0 :=
    (overlap_equation_of_trainSol hν hc tr).1.solenoidal T hT
  have hUb : ∀ (w : List Bool) (k : Fin 2), ∃ M : ℝ, ∀ z : Plane, |wordComp w U k z| ≤ M := by
    intro w k
    obtain ⟨M, hM⟩ := vjl_wordBoundedOn htr hs.le w k
    refine ⟨|c ^ 3 * c ^ w.length| * M, fun z => ?_⟩
    change |wordComp w (overlapField ν c tr.v T) k z| ≤ _
    rw [overlapField_eq_scaleField, wordComp_scaleField, abs_mul]
    exact mul_le_mul_of_nonneg_left
      (hM (B0155.ageOf ν c T) ⟨hs.le, le_rfl⟩ (B0155.dil c z)) (abs_nonneg _)
  have htop : ∀ k : Fin 2,
      ∫ z in Cyl.cell 1, W z k *
        (U z 0 * Cyl.partialQ (fun x => W x k) z +
          U z 1 * Cyl.partialEta (fun x => W x k) z) = 0 := by
    intro k
    have hWk : ContDiff ℝ ∞ (fun z : Plane => W z k) :=
      (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).contDiff.comp hWs.1
    have hWp : Cyl.IsPeriodic 1 (fun z : Plane => W z k) :=
      fun z => congrArg (fun v : Vec => v k) (hWs.2.1 z)
    exact ba_top_zero one_pos hUs.1 hUs.2.1 hUd hUb hWk hWp
      (hWs.2.2 [] k) (hWs.2.2 [true] k) (hWs.2.2 [false] k)
  have hW1_eq : (fun x : Plane => W x 1) = fun x : Plane => U x 1 := by
    funext x
    change U x 1 - (hmean 1 U x.2) 1 = U x 1
    rw [(overlapField_hmean_snd_eq_zero hν hc0 tr htr hs' x.2).2, sub_zero]
  have hAdv1 : SmoothJetL2 1 (Train.advection U) := by
    have hAdv_c := vel_advection_smoothJetL2 hν hc.le tr htr hs
    have heq : Train.advection U =
        fun z => (c ^ 7 : ℝ) • Train.advection (tr.v (B0155.ageOf ν c T)) (B0155.dil c z) := by
      funext z
      change Train.advection (overlapField ν c tr.v T) z = _
      rw [overlapField_eq_scaleField, advection_scaleField]
    rw [heq]
    exact smoothJetL2_unit_of_dil hc0 (c ^ 7) hAdv_c
  have hk1 : ∫ z, W z 1 * Train.advection U z 1 ∂(Cyl.cellμ 1) = 0 := by
    have hpt : (fun z : Plane => W z 1 * Train.advection U z 1) =
        fun z : Plane => W z 1 *
          (U z 0 * Cyl.partialQ (fun x => W x 1) z +
            U z 1 * Cyl.partialEta (fun x => W x 1) z) := by
      funext z
      rw [hW1_eq]
      rfl
    change ∫ z in Cyl.cell 1, W z 1 * Train.advection U z 1 = 0
    rw [hpt]
    exact htop 1
  have hk0 : ∫ z, W z 0 * Train.advection U z 0 ∂(Cyl.cellμ 1) =
      ∫ z in Cyl.cell 1, W z 0 * W z 1 * deriv b z.2 := by
    have hU0 : ContDiff ℝ ∞ (fun x : Plane => U x 0) :=
      (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hUs.1
    have hW0_eq : (fun x : Plane => W x 0) = hfluct 1 (fun x => U x 0) := by
      funext x; exact hfluct_unit_apply_vec hUs.1.continuous x 0
    have hpQ : Cyl.partialQ (fun x : Plane => W x 0) = Cyl.partialQ (fun x : Plane => U x 0) := by
      rw [hW0_eq, partialQ_hfluct_unit_eq hU0]
    have hpE : ∀ z : Plane, Cyl.partialEta (fun x : Plane => U x 0) z =
        Cyl.partialEta (fun x : Plane => W x 0) z + deriv b z.2 := by
      intro z
      have hb_eq : b = hmean 1 (fun w : Plane => U w 0) := by
        funext y; exact hmean_unit_apply_vec hUs.1.continuous y 0
      have hd : deriv b z.2 = hmean 1 (Cyl.partialEta (fun x : Plane => U x 0)) z.2 := by
        rw [hb_eq, cpH2_deriv_hmean (hU0.of_le (by simp))]
      have hfl : Cyl.partialEta (fun x : Plane => W x 0) z =
          Cyl.partialEta (fun x : Plane => U x 0) z -
            hmean 1 (Cyl.partialEta (fun x : Plane => U x 0)) z.2 := by
        rw [hW0_eq, partialEta_hfluct_unit_eq hU0]
        rfl
      linarith
    let A : Plane → ℝ := fun z => W z 0 *
      (U z 0 * Cyl.partialQ (fun x => W x 0) z + U z 1 * Cyl.partialEta (fun x => W x 0) z)
    let B : Plane → ℝ := fun z => W z 0 * W z 1 * deriv b z.2
    let C : Plane → ℝ := fun z => W z 0 * Train.advection U z 0
    have hCB : ∀ z : Plane, C z - B z = A z := by
      intro z
      dsimp only [A, B, C]
      change W z 0 * (U z 0 * Cyl.partialQ (fun x => U x 0) z +
        U z 1 * Cyl.partialEta (fun x => U x 0) z) - W z 0 * W z 1 * deriv b z.2 = _
      have hU1z : U z 1 = W z 1 := (congrFun hW1_eq z).symm
      rw [← hpQ, hpE z, hU1z]
      ring
    have hiC : Integrable C (Cyl.cellμ 1) := (hWs.2.2 [] 0).integrable_mul (hAdv1.2 [] 0)
    have hiB : Integrable B (Cyl.cellμ 1) := (overlap_shear_production_bound hUs hWs).1
    have hsub : ∫ z, (C z - B z) ∂(Cyl.cellμ 1) =
        (∫ z, C z ∂(Cyl.cellμ 1)) - ∫ z, B z ∂(Cyl.cellμ 1) :=
      integral_sub hiC hiB
    simp_rw [hCB] at hsub
    have hA0 : ∫ z, A z ∂(Cyl.cellμ 1) = 0 := htop 0
    change ∫ z, C z ∂(Cyl.cellμ 1) = ∫ z, B z ∂(Cyl.cellμ 1)
    linarith
  have hw0 : wordsOfLength 0 = {[]} := by
    ext w; rw [cgn_mem_wordsOfLength, Finset.mem_singleton, List.length_eq_zero_iff]
  unfold jetPair
  simp_rw [hw0, Finset.sum_singleton, Fin.sum_univ_two]
  have hi0 : Integrable (fun z => W z 0 * Train.advection U z 0) (Cyl.cellμ 1) :=
    (hWs.2.2 [] 0).integrable_mul (hAdv1.2 [] 0)
  have hi1 : Integrable (fun z => W z 1 * Train.advection U z 1) (Cyl.cellμ 1) :=
    (hWs.2.2 [] 1).integrable_mul (hAdv1.2 [] 1)
  have hsum : ∫ z, (W z 0 * Train.advection U z 0 + W z 1 * Train.advection U z 1) ∂(Cyl.cellμ 1) =
      (∫ z, W z 0 * Train.advection U z 0 ∂(Cyl.cellμ 1)) +
        ∫ z, W z 1 * Train.advection U z 1 ∂(Cyl.cellμ 1) :=
    integral_add hi0 hi1
  exact hsum.trans (by rw [hk0, hk1, add_zero])

/-! ### 4. Time derivative of `jetEnergy 1 0 (W t)` and assembly -/

/-- `CellSmoothL2 1 (overlapField ν c tr.v t)` whenever `0 < B0155.ageOf ν c t`. -/
theorem overlapField_cellSmoothL2_of_ageOf_pos {ν c : ℝ} (hν : 0 < ν) (hc : 1 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr) {t : ℝ}
    (ht0 : 0 < B0155.ageOf ν c t) :
    CellSmoothL2 1 (overlapField ν c tr.v t) := by
  have hc0 : 0 < c := zero_lt_one.trans hc
  have hcs := vel_cellSmoothL2 hν hc.le tr htr ht0
  have hsm : ContDiff ℝ ∞ (overlapField ν c tr.v t) := by
    rw [overlapField_eq_scaleField]
    unfold scaleField
    exact (hcs.1.comp (contDiff_id.const_smul c)).const_smul (c ^ 3)
  refine ⟨hsm, ?_, fun w m => ?_⟩
  · intro z
    rw [overlapField_eq_scaleField]
    unfold scaleField
    have h1 : c • (z.1 + 1, z.2) = (c * z.1 + c, c * z.2) := by
      ext <;> (simp [smul_eq_mul]; try ring)
    rw [h1, hcs.2.1 (c * z.1, c * z.2)]
    rfl
  · have hwm : ContDiff ℝ ∞ (wordComp w (overlapField ν c tr.v t) m) := contDiff_wordComp hsm w m
    rw [memLp_two_iff_integrable_sq hwm.continuous.aestronglyMeasurable]
    have hsq : (fun Z : Plane => (wordComp w (overlapField ν c tr.v t) m Z) ^ 2) =
        fun Z : Plane => (c ^ 3 * c ^ w.length) ^ 2 *
          (wordComp w (tr.v (B0155.ageOf ν c t)) m (B0155.dil c Z)) ^ 2 := by
      funext Z; rw [overlapField_eq_scaleField, wordComp_scaleField]; ring
    rw [hsq]
    exact B0155.integrableOn_cell_one_dil hc0 (hcs.2.2 w m).integrable_sq
      ((c ^ 3 * c ^ w.length) ^ 2)

/-- Parametric `C¹` regularity and time derivative of `r ↦ hfluct 1 (G r) z` for a jointly smooth
scalar family `G : ℝ → Plane → ℝ`. -/
theorem hfluct_param_contDiff_and_deriv {G : ℝ → Plane → ℝ}
    (hG : ContDiff ℝ ∞ (fun p : ℝ × Plane => G p.1 p.2)) (z : Plane) :
    ContDiff ℝ 1 (fun r => hfluct 1 (G r) z) ∧
      ∀ r : ℝ, deriv (fun τ => hfluct 1 (G τ) z) r =
        hfluct 1 (fun w => deriv (fun τ => G τ w) r) z := by
  let embH : Plane → ℝ × Plane := fun p => (p.2, (p.1, z.2))
  have hembH : ContDiff ℝ ∞ embH :=
    contDiff_snd.prodMk (contDiff_fst.prodMk (contDiff_const (c := z.2)))
  let H : Plane → ℝ := fun p => G p.2 (p.1, z.2)
  have hH : ContDiff ℝ ∞ H := hG.comp hembH
  let embZ : ℝ → ℝ × Plane := fun r => (r, z)
  have hembZ : ContDiff ℝ ∞ embZ := contDiff_id.prodMk (contDiff_const (c := z))
  have hGz : ContDiff ℝ ∞ (fun r : ℝ => G r z) := hG.comp hembZ
  have hMz : ContDiff ℝ ∞ (fun r : ℝ => hmean 1 (G r) z.2) := hmean_unit_contDiff hH
  refine ⟨(hGz.sub hMz).of_le (by simp), fun r => ?_⟩
  have hdG : HasDerivAt (fun τ => G τ z) (deriv (fun τ => G τ z) r) r :=
    (hGz.differentiable (by simp)).differentiableAt.hasDerivAt
  have hdM : HasDerivAt (fun τ => hmean 1 (G τ) z.2)
      (hmean 1 (fun w => deriv (fun τ => G τ (w.1, w.2)) r) z.2) r :=
    cpH2_hasDerivAt_hmean (hH.of_le (by simp)) r
  exact (hdG.sub hdM).deriv

open UnforcedLeray.Short.PartI.TrainWordEnergyInstance in
/-- Time derivative of a single coordinate energy `∫_{Cyl.cell 1} (W t z k)²` at `T ≥ 0`. -/
theorem overlap_hfluct_coord_hasDerivAt {ν c : ℝ} (hν : 0 < ν) (hc : 1 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr) {T : ℝ} (hT : 0 ≤ T)
    (hUs : CellSmoothL2 1 (overlapField ν c tr.v T))
    (hWs : CellSmoothL2 1 (hfluct 1 (overlapField ν c tr.v T))) (k : Fin 2) :
    let U := overlapField ν c tr.v
    let W := fun t => hfluct 1 (U t)
    MemLp (fun z => deriv (fun t => U t z) T k) 2 (Cyl.cellμ 1) ∧
      HasDerivAt (fun t => ∫ z in Cyl.cell 1, (W t z k) ^ 2)
        (2 * ∫ z in Cyl.cell 1, W T z k * deriv (fun t => U t z) T k) T := by
  intro U W
  have hc0 : 0 < c := zero_lt_one.trans hc
  set s : ℝ := B0155.ageOf ν c T with hs_def
  have hs : 0 < s := overlapAgeOf_pos hν hc hT
  obtain ⟨ε0, hε0, K0, hK0⟩ := vel_timeDeriv_local_l2 hν hc.le tr htr hs [] k
  have hεpos : 0 < min ε0 (s / 4) := lt_min hε0 (by linarith)
  let G : ℝ → Plane → ℝ := fun r z => c ^ 3 * tr.v (loc s r) (c • z) k
  have hG_smooth : ContDiff ℝ ∞ (fun p : ℝ × Plane => G p.1 p.2) := by
    have hv_on : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2 k) (Ici 0 ×ˢ univ) :=
      ((EuclideanSpace.proj k : Vec →L[ℝ] ℝ).contDiff).comp_contDiffOn tr.isTrain.smooth_v
    have hPhi : ContDiff ℝ ∞ (fun p : ℝ × Plane => (loc s p.1, c • p.2)) :=
      ((contDiff_loc s).comp contDiff_fst).prodMk (contDiff_snd.const_smul c)
    exact contDiff_const.mul (hv_on.comp_contDiff hPhi
      (fun p => ⟨(loc_pos hs p.1).le, mem_univ _⟩))
  let F : ℝ → Plane → ℝ := fun r z => hfluct 1 (G r) z
  have hF_C1 : ∀ z : Plane, ContDiff ℝ 1 (fun r => F r z) :=
    fun z => (hfluct_param_contDiff_and_deriv hG_smooth z).1
  have hF_deriv_loc : ∀ {r : ℝ}, 3 * s / 4 < r → ∀ z : Plane,
      deriv (fun τ => F τ z) r =
        hfluct 1 (fun w => c ^ 3 * (deriv (fun τ => tr.v τ (c • w)) r) k) z := by
    intro r hr z
    have hr0 : 0 < r := by linarith
    rw [(hfluct_param_contDiff_and_deriv hG_smooth z).2 r]
    have hfun : (fun w : Plane => deriv (fun τ => G τ w) r) =
        fun w : Plane => c ^ 3 * (deriv (fun τ => tr.v τ (c • w)) r) k := by
      funext w
      have hev : (fun τ => G τ w) =ᶠ[𝓝 r] (fun τ => c ^ 3 * tr.v τ (c • w) k) := by
        filter_upwards [Ioi_mem_nhds hr] with τ hτ
        simp [G, loc_eq_id hs hτ]
      rw [hev.deriv_eq]
      have hdv := (TrainErrorEquation.differentiableAt_time tr hr0 (c • w)).hasDerivAt
      have hdk := ((EuclideanSpace.proj k : Vec →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt r hdv).const_mul
        (c ^ 3)
      exact hdk.deriv
    rw [hfun]
  have hF_s : MemLp (F s) 2 (Cyl.cellμ 1) := by
    have heq : F s = fun z => W T z k := by
      funext z
      have hGs : G s = fun w => U T w k := by
        funext w
        change G s w = overlapField ν c tr.v T w k
        rw [overlapField_eq_scaleField, ← hs_def]
        simp [G, loc_self, scaleField, PiLp.smul_apply]
      unfold F
      rw [hGs, ← hfluct_unit_apply_vec hUs.1.continuous z k]
    rw [heq]
    exact hWs.2.2 [] k
  let K1 : ℝ := (c ^ 3) ^ 2 * (c ^ 2)⁻¹ * K0
  have hD : ∀ r, |r - s| < min ε0 (s / 4) →
      MemLp (fun z => deriv (fun τ => F τ z) r) 2 (Cyl.cellμ 1) ∧
      ∫ z, (deriv (fun τ => F τ z) r) ^ 2 ∂(Cyl.cellμ 1) ≤ K1 := by
    intro r hr
    have hr1 : |r - s| < ε0 := lt_of_lt_of_le hr (min_le_left _ _)
    have hr2 : |r - s| < s / 4 := lt_of_lt_of_le hr (min_le_right _ _)
    have hr34 : 3 * s / 4 < r := by have := (abs_lt.1 hr2).1; linarith
    have hr0 : 0 < r := by linarith
    obtain ⟨hm, hint⟩ := hK0 r hr0 hr1
    let d_r : Plane → ℝ := fun w => c ^ 3 * (deriv (fun τ => tr.v τ (c • w)) r) k
    have hvU : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2)
        (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) :=
      tr.isTrain.smooth_v.mono (Set.prod_mono Ioi_subset_Ici_self Subset.rfl)
    have hdv_sm : ContDiff ℝ ∞ (fun y => deriv (fun τ => tr.v τ y) r) :=
      ErrPressureLapAux.dt_contDiff hvU hr0
    have hdr_cont : Continuous d_r :=
      continuous_const.mul
        (((EuclideanSpace.proj k : Vec →L[ℝ] ℝ).continuous.comp hdv_sm.continuous).comp
          (continuous_id.const_smul c))
    have hdr_sq_eq : (fun w : Plane => d_r w ^ 2) =
        fun w : Plane => (c ^ 3) ^ 2 *
          ((wordComp [] (fun y => deriv (fun τ => tr.v τ y) r) k (B0155.dil c w)) ^ 2) := by
      funext w
      simp [d_r, wordComp, B0151.derivWord, B0155.dil_eq_smul]
      ring
    have hdr_mem : MemLp d_r 2 (Cyl.cellμ 1) := by
      rw [memLp_two_iff_integrable_sq hdr_cont.aestronglyMeasurable, hdr_sq_eq]
      exact B0155.integrableOn_cell_one_dil hc0 hm.integrable_sq ((c ^ 3) ^ 2)
    have hdr_int : ∫ w in Cyl.cell 1, d_r w ^ 2 ≤ K1 := by
      rw [hdr_sq_eq, integral_const_mul,
        integral_cell_one_dil hc0 (fun z => (wordComp [] (fun y => deriv (fun τ => tr.v τ y) r) k z) ^ 2)]
      have hnn : 0 ≤ (c ^ 3) ^ 2 * (c ^ 2)⁻¹ := by positivity
      calc (c ^ 3) ^ 2 * ((c ^ 2)⁻¹ *
            ∫ z in Cyl.cell c, (wordComp [] (fun y => deriv (fun τ => tr.v τ y) r) k z) ^ 2)
          = (c ^ 3) ^ 2 * (c ^ 2)⁻¹ *
              ∫ z in Cyl.cell c, (wordComp [] (fun y => deriv (fun τ => tr.v τ y) r) k z) ^ 2 := by
            ring
        _ ≤ (c ^ 3) ^ 2 * (c ^ 2)⁻¹ * K0 := mul_le_mul_of_nonneg_left hint hnn
    obtain ⟨hw_mem, hw_int⟩ := memLp_and_integral_hfluct_unit_sq_le hdr_cont hdr_mem
    simp_rw [hF_deriv_loc hr34]
    exact ⟨hw_mem, hw_int.trans hdr_int⟩
  obtain ⟨_, hder_r⟩ := L2SqDeriv.l2Sq_hasDerivAt (μ := Cyl.cellμ 1)
    F s (min ε0 (s / 4)) K1 hεpos hF_C1 hF_s hD
  have hs34 : 3 * s / 4 < s := by linarith
  have hage_deriv : HasDerivAt (B0155.ageOf ν c) (c ^ 2 / ν) T := by
    unfold B0155.ageOf
    simpa using (hasDerivAt_id T).const_mul (c ^ 2 / ν) |>.const_add (B0155.age ν c)
  have hcomp_t : HasDerivAt (fun t => ∫ z in Cyl.cell 1, (F (B0155.ageOf ν c t) z) ^ 2)
      ((2 * ∫ z in Cyl.cell 1, F s z * deriv (fun τ => F τ z) s) * (c ^ 2 / ν)) T := by
    have hder_r' : HasDerivAt (fun r => ∫ z in Cyl.cell 1, (F r z) ^ 2)
        (2 * ∫ z in Cyl.cell 1, F s z * deriv (fun τ => F τ z) s) (B0155.ageOf ν c T) := by
      rw [← hs_def]; exact hder_r
    exact hder_r'.comp T hage_deriv
  have hev_t : (fun t => ∫ z in Cyl.cell 1, (W t z k) ^ 2) =ᶠ[𝓝 T]
      (fun t => ∫ z in Cyl.cell 1, (F (B0155.ageOf ν c t) z) ^ 2) := by
    have hcont_age : ContinuousAt (B0155.ageOf ν c) T := hage_deriv.continuousAt
    filter_upwards [hcont_age (Ioi_mem_nhds hs34)] with t ht
    have ht' : 3 * s / 4 < B0155.ageOf ν c t := ht
    have ht0 : 0 < B0155.ageOf ν c t := by linarith
    congr 1
    funext z
    have hGt : G (B0155.ageOf ν c t) = fun w => U t w k := by
      funext w
      change G (B0155.ageOf ν c t) w = overlapField ν c tr.v t w k
      rw [overlapField_eq_scaleField]
      simp [G, loc_eq_id hs ht', scaleField, PiLp.smul_apply]
    unfold F
    rw [hGt, ← hfluct_unit_apply_vec
      (overlapField_cellSmoothL2_of_ageOf_pos hν hc tr htr ht0).1.continuous z k]
  have hDt1 : SmoothJetL2 1 (fun z => deriv (fun t => U t z) T) := by
    have hvU : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2)
        (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) :=
      tr.isTrain.smooth_v.mono (Set.prod_mono Ioi_subset_Ici_self Subset.rfl)
    have hDt_c : SmoothJetL2 c (fun y => deriv (fun τ => tr.v τ y) s) :=
      ⟨ErrPressureLapAux.dt_contDiff hvU hs,
        fun w m => (vel_wordEnergy_hasDerivAt hν hc.le tr htr hs w m).2.1⟩
    have heq : (fun z : Plane => deriv (fun t => U t z) T) =
        fun z : Plane => (c ^ 5 / ν : ℝ) • deriv (fun τ => tr.v τ (B0155.dil c z)) s := by
      funext z
      have hdv : HasDerivAt (fun τ => tr.v τ (B0155.dil c z))
          (deriv (fun τ => tr.v τ (B0155.dil c z)) s) (B0155.ageOf ν c T) := by
        rw [← hs_def]
        exact (TrainErrorEquation.differentiableAt_time tr hs (B0155.dil c z)).hasDerivAt
      have hcomp : HasDerivAt (fun t => c ^ 3 • tr.v (B0155.ageOf ν c t) (B0155.dil c z))
          (c ^ 3 • (c ^ 2 / ν) • deriv (fun τ => tr.v τ (B0155.dil c z)) s) T :=
        (hdv.scomp T hage_deriv).const_smul (c ^ 3)
      have hfun : (fun t => U t z) = fun t => c ^ 3 • tr.v (B0155.ageOf ν c t) (B0155.dil c z) := by
        funext t
        change overlapField ν c tr.v t z = _
        rw [overlapField_eq_scaleField]
        simp [scaleField, B0155.dil_eq_smul]
      rw [hfun, hcomp.deriv]
      ext m
      simp only [PiLp.smul_apply, smul_eq_mul]
      ring
    rw [heq]
    exact smoothJetL2_unit_of_dil hc0 (c ^ 5 / ν) hDt_c
  refine ⟨hDt1.2 [] k, (hcomp_t.congr_of_eventuallyEq hev_t).congr_deriv ?_⟩
  let d_s : Plane → ℝ := fun w => c ^ 3 * (deriv (fun τ => tr.v τ (c • w)) s) k
  have hU_dt_eq : ∀ w : Plane, deriv (fun t => U t w) T k = (c ^ 2 / ν) * d_s w := by
    intro w
    have hdv : HasDerivAt (fun τ => tr.v τ (c • w))
        (deriv (fun τ => tr.v τ (c • w)) s) (B0155.ageOf ν c T) := by
      rw [← hs_def]
      exact (TrainErrorEquation.differentiableAt_time tr hs (c • w)).hasDerivAt
    have hcomp : HasDerivAt (fun t => c ^ 3 • tr.v (B0155.ageOf ν c t) (c • w))
        (c ^ 3 • (c ^ 2 / ν) • deriv (fun τ => tr.v τ (c • w)) s) T :=
      (hdv.scomp T hage_deriv).const_smul (c ^ 3)
    have hfun : (fun t => U t w) = fun t => c ^ 3 • tr.v (B0155.ageOf ν c t) (c • w) := by
      funext t
      change overlapField ν c tr.v t w = _
      rw [overlapField_eq_scaleField]; rfl
    rw [hfun, hcomp.deriv]
    simp only [d_s, PiLp.smul_apply, smul_eq_mul]
    ring
  have hFs_eq : ∀ z : Plane, F s z = hfluct 1 (fun w => U T w k) z := by
    intro z
    have hGs : G s = fun w => U T w k := by
      funext w
      change G s w = overlapField ν c tr.v T w k
      rw [overlapField_eq_scaleField, ← hs_def]
      simp [G, loc_self, scaleField, PiLp.smul_apply]
    unfold F
    rw [hGs]
  have hd_s_eq : d_s = fun w => (c ^ 2 / ν)⁻¹ * deriv (fun t => U t w) T k := by
    funext w
    rw [hU_dt_eq w, inv_mul_cancel_left₀ (div_pos (sq_pos_of_pos hc0) hν).ne']
  have hd_s_cont : Continuous d_s := by
    rw [hd_s_eq]
    exact continuous_const.mul
      ((EuclideanSpace.proj k : Vec →L[ℝ] ℝ).continuous.comp hDt1.1.continuous)
  have hd_s_L2 : MemLp d_s 2 (Cyl.cellμ 1) := by
    rw [hd_s_eq]
    exact (hDt1.2 [] k).const_mul (c ^ 2 / ν)⁻¹
  have hUk_cont : Continuous (fun w : Plane => U T w k) :=
    ((EuclideanSpace.proj k : Vec →L[ℝ] ℝ).continuous.comp hUs.1.continuous)
  have horth := integral_hfluct_mul_hfluct_unit hUk_cont (hUs.2.2 [] k) hd_s_cont hd_s_L2
  have h1 : ∫ z in Cyl.cell 1, F s z * deriv (fun τ => F τ z) s =
      ∫ z in Cyl.cell 1, hfluct 1 (fun w => U T w k) z * d_s z := by
    refine Eq.trans ?_ horth
    congr 1
    funext z
    rw [hFs_eq z, hF_deriv_loc hs34 z]
  rw [h1]
  have h2 : (2 * ∫ z in Cyl.cell 1, hfluct 1 (fun w => U T w k) z * d_s z) * (c ^ 2 / ν) =
      2 * ∫ z in Cyl.cell 1, W T z k * deriv (fun t => U t z) T k := by
    have hmul : (∫ z in Cyl.cell 1, hfluct 1 (fun w => U T w k) z * d_s z) * (c ^ 2 / ν) =
        ∫ z in Cyl.cell 1, hfluct 1 (fun w => U T w k) z * ((c ^ 2 / ν) * d_s z) := by
      rw [← integral_mul_const]
      congr 1; funext z; ring
    calc (2 * ∫ z in Cyl.cell 1, hfluct 1 (fun w => U T w k) z * d_s z) * (c ^ 2 / ν)
        = 2 * ((∫ z in Cyl.cell 1, hfluct 1 (fun w => U T w k) z * d_s z) * (c ^ 2 / ν)) := by ring
      _ = 2 * ∫ z in Cyl.cell 1, hfluct 1 (fun w => U T w k) z * ((c ^ 2 / ν) * d_s z) := by
          rw [hmul]
      _ = 2 * ∫ z in Cyl.cell 1, W T z k * deriv (fun t => U t z) T k := by
          congr 2; funext z
          rw [← hfluct_unit_apply_vec hUs.1.continuous z k, hU_dt_eq z]
  exact h2

/-- **Proof of `OverlapFluctuationEnergyBalance` (`PartI:T13/2`)** (source lines 390-394). -/
theorem overlapFluctuationEnergyBalance_proof (hSmooth : OverlapFluctuationSmoothL2) :
    OverlapFluctuationEnergyBalance := by
  intro ν c hν hc tr htr T hT U W b
  have hc0 : 0 < c := zero_lt_one.trans hc
  obtain ⟨hUs, hWs, _⟩ := hSmooth ν c hν hc tr htr T hT
  refine ⟨?_, (overlap_shear_production_bound hUs hWs).2⟩
  obtain ⟨hDt0, hder0⟩ := overlap_hfluct_coord_hasDerivAt hν hc tr htr hT hUs hWs 0
  obtain ⟨hDt1, hder1⟩ := overlap_hfluct_coord_hasDerivAt hν hc tr htr hT hUs hWs 1
  have hder0' : HasDerivAt (fun t => ∫ z in Cyl.cell 1, (W t z 0) ^ 2)
      (2 * ∫ z in Cyl.cell 1, W T z 0 * deriv (fun t => U t z) T 0) T := hder0
  have hder1' : HasDerivAt (fun t => ∫ z in Cyl.cell 1, (W t z 1) ^ 2)
      (2 * ∫ z in Cyl.cell 1, W T z 1 * deriv (fun t => U t z) T 1) T := hder1
  have hder_sum : HasDerivAt (fun t => (∫ z in Cyl.cell 1, (W t z 0) ^ 2) +
      (∫ z in Cyl.cell 1, (W t z 1) ^ 2))
      ((2 * ∫ z in Cyl.cell 1, W T z 0 * deriv (fun t => U t z) T 0) +
        2 * ∫ z in Cyl.cell 1, W T z 1 * deriv (fun t => U t z) T 1) T :=
    HasDerivAt.fun_add hder0' hder1'
  have hJ0_eq : (fun t => jetEnergy 1 0 (W t)) =ᶠ[𝓝 T]
      fun t => (∫ z in Cyl.cell 1, (W t z 0) ^ 2) + (∫ z in Cyl.cell 1, (W t z 1) ^ 2) := by
    set s : ℝ := B0155.ageOf ν c T
    have hs : 0 < s := overlapAgeOf_pos hν hc hT
    have hage_cont : ContinuousAt (B0155.ageOf ν c) T := by
      unfold B0155.ageOf
      exact (continuous_const.add (continuous_const.mul continuous_id)).continuousAt
    filter_upwards [hage_cont (Ioi_mem_nhds hs)] with t ht
    have hUt : CellSmoothL2 1 (U t) :=
      overlapField_cellSmoothL2_of_ageOf_pos hν hc tr htr ht
    have hWt : CellSmoothL2 1 (W t) := (cellSmoothL2_hfluct_unit hUt).1
    unfold jetEnergy jetPair
    have hw0 : wordsOfLength 0 = {[]} := by
      ext w; rw [cgn_mem_wordsOfLength, Finset.mem_singleton, List.length_eq_zero_iff]
    simp_rw [hw0, Finset.sum_singleton, Fin.sum_univ_two]
    change ∫ z, (W t z 0 * W t z 0 + W t z 1 * W t z 1) ∂(Cyl.cellμ 1) = _
    simp_rw [← sq]
    exact integral_add (hWt.2.2 [] 0).integrable_sq (hWt.2.2 [] 1).integrable_sq
  have hder_pair : HasDerivAt (fun t => jetEnergy 1 0 (W t))
      (2 * jetPair 1 0 (W T) (fun z => deriv (fun t => U t z) T)) T := by
    refine (hder_sum.congr_of_eventuallyEq hJ0_eq).congr_deriv ?_
    have hw0 : wordsOfLength 0 = {[]} := by
      ext w; rw [cgn_mem_wordsOfLength, Finset.mem_singleton, List.length_eq_zero_iff]
    unfold jetPair
    simp_rw [hw0, Finset.sum_singleton, Fin.sum_univ_two]
    have hi0 : Integrable (fun z => W T z 0 * deriv (fun t => U t z) T 0) (Cyl.cellμ 1) :=
      (hWs.2.2 [] 0).integrable_mul hDt0
    have hi1 : Integrable (fun z => W T z 1 * deriv (fun t => U t z) T 1) (Cyl.cellμ 1) :=
      (hWs.2.2 [] 1).integrable_mul hDt1
    have hadd : ∫ z, (W T z 0 * deriv (fun t => U t z) T 0 +
        W T z 1 * deriv (fun t => U t z) T 1) ∂(Cyl.cellμ 1) =
        (∫ z, W T z 0 * deriv (fun t => U t z) T 0 ∂(Cyl.cellμ 1)) +
          ∫ z, W T z 1 * deriv (fun t => U t z) T 1 ∂(Cyl.cellμ 1) :=
      integral_add hi0 hi1
    change (2 * ∫ z, W T z 0 * deriv (fun t => U t z) T 0 ∂(Cyl.cellμ 1)) +
      2 * ∫ z, W T z 1 * deriv (fun t => U t z) T 1 ∂(Cyl.cellμ 1) =
      2 * ∫ z, (W T z 0 * deriv (fun t => U t z) T 0 +
        W T z 1 * deriv (fun t => U t z) T 1) ∂(Cyl.cellμ 1)
    rw [hadd, mul_add]
  refine hder_pair.congr_deriv ?_
  set s : ℝ := B0155.ageOf ν c T with hs_def
  have hs : 0 < s := overlapAgeOf_pos hν hc hT
  have hs' : 0 < B0146.overlapAge ν c + c ^ 2 * T / ν := overlapAge_add_pos hν hc hT
  have hLap1 : SmoothJetL2 1 (Train.vecLaplacian (U T)) := by
    refine ⟨?_, fun w k => ?_⟩
    · refine contDiff_euclidean.2 fun k => ?_
      have hk : ContDiff ℝ ∞ (fun y => U T y k) :=
        (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).contDiff.comp hUs.1
      have e : (fun z : Plane => Train.vecLaplacian (U T) z k) =
          fun z => Train.lapS (fun y => U T y k) z := by
        funext z; exact lapLocal_vecLap_apply _ _ _
      rw [e]
      exact lapLocal_lapS_contDiff hk
    · have hk : ContDiff ℝ ∞ (fun y => U T y k) :=
        (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).contDiff.comp hUs.1
      have eq : wordComp w (Train.vecLaplacian (U T)) k =
          fun z => wordComp (true :: true :: w) (U T) k z +
            wordComp (false :: false :: w) (U T) k z := by
        funext z
        have e1 : (fun x => Train.vecLaplacian (U T) x k) =
            fun x => Train.lapS (fun y => U T y k) x := by
          funext x; exact lapLocal_vecLap_apply _ _ _
        calc wordComp w (Train.vecLaplacian (U T)) k z
            = B0151.derivWord w (fun x => Train.lapS (fun y => U T y k) x) z := by
              unfold wordComp; rw [e1]
          _ = Train.lapS (B0151.derivWord w (fun y => U T y k)) z := by
              rw [JetViscIBP.derivWord_lap w _ hk]
          _ = wordComp (true :: true :: w) (U T) k z +
                wordComp (false :: false :: w) (U T) k z := by
              rw [lapLocal_lapS_dw]; rfl
      rw [eq]
      exact (hUs.2.2 (true :: true :: w) k).add (hUs.2.2 (false :: false :: w) k)
  have hAdv1 : SmoothJetL2 1 (Train.advection (U T)) := by
    have hAdv_c := vel_advection_smoothJetL2 hν hc.le tr htr hs
    have heq : Train.advection (U T) =
        fun z => (c ^ 7 : ℝ) • Train.advection (tr.v s) (B0155.dil c z) := by
      funext z
      change Train.advection (overlapField ν c tr.v T) z = _
      rw [overlapField_eq_scaleField, ← hs_def, advection_scaleField]
    rw [heq]
    exact smoothJetL2_unit_of_dil hc0 (c ^ 7) hAdv_c
  have hDt1_sm : SmoothJetL2 1 (fun z => deriv (fun t => U t z) T) := by
    have hvU : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2)
        (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) :=
      tr.isTrain.smooth_v.mono (Set.prod_mono Ioi_subset_Ici_self Subset.rfl)
    have hDt_c : SmoothJetL2 c (fun y => deriv (fun τ => tr.v τ y) s) :=
      ⟨ErrPressureLapAux.dt_contDiff hvU hs,
        fun w m => (vel_wordEnergy_hasDerivAt hν hc.le tr htr hs w m).2.1⟩
    have hage_deriv : HasDerivAt (B0155.ageOf ν c) (c ^ 2 / ν) T := by
      unfold B0155.ageOf
      simpa using (hasDerivAt_id T).const_mul (c ^ 2 / ν) |>.const_add (B0155.age ν c)
    have heq : (fun z : Plane => deriv (fun t => U t z) T) =
        fun z : Plane => (c ^ 5 / ν : ℝ) • deriv (fun τ => tr.v τ (B0155.dil c z)) s := by
      funext z
      have hdv : HasDerivAt (fun τ => tr.v τ (B0155.dil c z))
          (deriv (fun τ => tr.v τ (B0155.dil c z)) s) (B0155.ageOf ν c T) := by
        rw [← hs_def]
        exact (TrainErrorEquation.differentiableAt_time tr hs (B0155.dil c z)).hasDerivAt
      have hcomp : HasDerivAt (fun t => c ^ 3 • tr.v (B0155.ageOf ν c t) (B0155.dil c z))
          (c ^ 3 • (c ^ 2 / ν) • deriv (fun τ => tr.v τ (B0155.dil c z)) s) T :=
        (hdv.scomp T hage_deriv).const_smul (c ^ 3)
      have hfun : (fun t => U t z) = fun t => c ^ 3 • tr.v (B0155.ageOf ν c t) (B0155.dil c z) := by
        funext t
        change overlapField ν c tr.v t z = _
        rw [overlapField_eq_scaleField]; simp [scaleField, B0155.dil_eq_smul]
      rw [hfun, hcomp.deriv]
      ext m; simp only [PiLp.smul_apply, smul_eq_mul]; ring
    rw [heq]
    exact smoothJetL2_unit_of_dil hc0 (c ^ 5 / ν) hDt_c
  let P : Plane → ℝ := B0155.ovPi ν c tr.p T
  have hAdv_smul : SmoothJetL2 1 (fun y => eC ν c • Train.advection (U T) y) :=
    ⟨hAdv1.1.const_smul (eC ν c), fun w k => by
      have heq : wordComp w (fun y => eC ν c • Train.advection (U T) y) k =
          fun z => eC ν c * wordComp w (Train.advection (U T)) k z := by
        funext z
        have hfun : (fun y : Plane => (eC ν c • Train.advection (U T) y) k) =
            fun y => eC ν c * Train.advection (U T) y k := by
          funext y; simp [PiLp.smul_apply]
        unfold wordComp; rw [hfun]; exact lapLocal_dw_const_mul (eC ν c) w _ z
      rw [heq]
      exact (hAdv1.2 w k).const_mul (eC ν c)⟩
  have hGradP_eq : Train.gradS P =
      fun y => (Train.vecLaplacian (U T) y - (fun z => deriv (fun t => U t z) T) y) -
        (fun z => eC ν c • Train.advection (U T) z) y := by
    funext y
    have hmom : deriv (fun t => U t y) T + eC ν c • Train.advection (U T) y + Train.gradS P y =
        Train.vecLaplacian (U T) y :=
      (overlap_equation_of_trainSol hν hc tr).2 T hT y
    rw [← hmom]
    abel
  have hGradP1 : SmoothJetL2 1 (Train.gradS P) := by
    rw [hGradP_eq]
    exact pairSplit_smoothJetL2_sub (pairSplit_smoothJetL2_sub hLap1 hDt1_sm) hAdv_smul
  have hDt_eq : (fun y => deriv (fun t => U t y) T) =
      fun y => (Train.vecLaplacian (U T) y - (fun z => eC ν c • Train.advection (U T) z) y) -
        Train.gradS P y := by
    funext y
    have hmom : deriv (fun t => U t y) T + eC ν c • Train.advection (U T) y + Train.gradS P y =
        Train.vecLaplacian (U T) y :=
      (overlap_equation_of_trainSol hν hc tr).2 T hT y
    rw [← hmom]
    abel
  have hW_sol : ∀ z : Plane, Cyl.divergence (W T) z = 0 := by
    intro z
    have hU0 : ContDiff ℝ ∞ (fun x : Plane => U T x 0) :=
      (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hUs.1
    have hW0_eq : (fun x : Plane => W T x 0) = hfluct 1 (fun x => U T x 0) := by
      funext x; exact hfluct_unit_apply_vec hUs.1.continuous x 0
    have hW1_eq : (fun x : Plane => W T x 1) = fun x : Plane => U T x 1 := by
      funext x
      change U T x 1 - (hmean 1 (U T) x.2) 1 = U T x 1
      rw [(overlapField_hmean_snd_eq_zero hν hc0 tr htr hs' x.2).2, sub_zero]
    unfold Cyl.divergence
    rw [hW0_eq, partialQ_hfluct_unit_eq hU0, hW1_eq]
    exact (overlap_equation_of_trainSol hν hc tr).1.solenoidal T hT z
  have hps : ContDiff ℝ ∞ (tr.p s) :=
    TrainErrorEquation.contDiff_slice tr.isTrain.smooth_p hs.le
  have hPs : ContDiff ℝ ∞ P := by
    have hdil : ContDiff ℝ ∞ (B0155.dil c) := by
      have heq : B0155.dil c = fun z : Plane => c • z := by
        funext z; exact B0155.dil_eq_smul c z
      rw [heq]; exact contDiff_id.const_smul c
    exact contDiff_const.mul (hps.comp hdil)
  have hP_per : Cyl.IsPeriodic 1 P :=
    (overlap_equation_of_trainSol hν hc tr).1.periodic_P T hT
  have hP_bd : ∃ M : ℝ, ∀ z : Plane, |P z| ≤ M := by
    obtain ⟨Mp, hMp⟩ := periodicDecayBounded_proof c hc0 (tr.p s) hps.continuous
      (tr.isTrain.periodic_p s hs.le) (tr.isTrain.pressure_decay s hs.le)
    refine ⟨|c ^ 4 / ν| * Mp, fun z => ?_⟩
    unfold P B0155.ovPi
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hMp _) (abs_nonneg _)
  have horth := jetPressureOrth_proof 1 one_pos (W T) hWs hW_sol P hPs hP_per hP_bd hGradP1.2 0
  rw [hDt_eq,
    pairSplit_jetPair_sub 0 hWs.2.2 (pairSplit_smoothJetL2_sub hLap1 hAdv_smul) hGradP1,
    pairSplit_jetPair_sub 0 hWs.2.2 hLap1 hAdv_smul,
    pairSplit_jetPair_smul,
    jetPair_zero_hfluct_vecLaplacian hUs hWs,
    jetPair_zero_hfluct_advection hν hc tr htr hT hUs hWs,
    horth, sub_zero]

end UnforcedLeray.Short.PartI
