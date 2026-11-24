import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G2_1_org_C_1.DivMollKer
import UnforcedLeray.Short.PartIIb.Sub.T09_2_1.Weak
import UnforcedLeray.Short.PartIIb.Tasks.GradLapNvC.DivApprox.SCut
import UnforcedLeray.Short.PartIIb.Tasks.GradLapNvC.DivApprox.EtaCut
import UnforcedLeray.Short.PartIIb.Tasks.GradLapNvC.DivApprox.Refute.Cx.WeakOfSmooth
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.WeightCompare
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.WindowBound.Data.Meas
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.WindowBound.Data.Bound
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Collision-Free `DivMollApprox` and `DivApproxW` at `r = bgp` for `PartII-b:G2/1/org/C/1`

Proves `divMollApprox_bgp` and `divApproxW_bgp` without importing `Sub.PartIIb_T08_2_3` (avoiding
the `MollNice` environment collision with `Sub.«PartII-b_T13_1_5_5_7»`), using the Cartesian
cylinder mollifier infrastructure `cgiMollify` (`mollExistsRho`, `molN`, `convK`, `mollLoc_proof`,
`mollConvNice_proof`, `mollYoung_proof`, `mollDeriv_proof`, `mollApprox_proof`) together with the
Friedrichs commutator kernel `psi0` from `DivMollKer.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.PhysKOutCandMoll

open UnforcedLeray.Short.IIb

/-! ## 1. Window comparability between `hMeas c bgp` and `cylMeas c` on `[a, B] × ℝ²` -/

private def winIcc (a B : ℝ) : Set Coord := Icc a B ×ˢ univ

private theorem measurableSet_winIcc (a B : ℝ) : MeasurableSet (winIcc a B) :=
  measurableSet_Icc.prod MeasurableSet.univ

private theorem winIcc_slice_empty {c a B : ℝ} {E : Set Coord} (hsub : E ⊆ winIcc a B) {x : ℝ}
    (hx : x ∉ Icc a B) : (UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' E) = 0 := by
  have h : Prod.mk x ⁻¹' E = ∅ := by
    ext z
    simp only [mem_preimage, mem_empty_iff_false, iff_false]
    intro hz
    exact hx (hsub hz).1
  rw [h, measure_empty]

private theorem hMeas_bgp_restrict_le {c a B : ℝ} (ha : 0 < a) :
    (hMeas c bgp).restrict (winIcc a B) ≤
      ENNReal.ofReal (a ^ (bgp / 2 - 5 / 2)) • (cylMeas c).restrict (winIcc a B) := by
  set κ : ℝ := bgp / 2 - 5 / 2
  have hκ0 : κ ≤ 0 := by norm_num [κ, bgp]
  rw [Measure.le_iff]
  intro S hS
  simp only [Measure.smul_apply, Measure.restrict_apply hS, smul_eq_mul, hMeas]
  have hSW : MeasurableSet (S ∩ winIcc a B) := hS.inter (measurableSet_winIcc a B)
  have hsub : S ∩ winIcc a B ⊆ winIcc a B := inter_subset_right
  rw [wwc_ageμ_apply c κ hSW, wwc_cyl_apply c hSW]
  calc ∫⁻ x, (UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' (S ∩ winIcc a B)) * ENNReal.ofReal (x ^ κ)
        ∂((volume : Measure ℝ).restrict (Ioi 0))
      ≤ ∫⁻ x, ENNReal.ofReal (a ^ κ) *
          (UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' (S ∩ winIcc a B))
        ∂((volume : Measure ℝ).restrict (Ioi 0)) := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ Icc a B
        · have hle : ENNReal.ofReal (x ^ κ) ≤ ENNReal.ofReal (a ^ κ) :=
            ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos ha hx.1 hκ0)
          calc _ ≤ (UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' (S ∩ winIcc a B)) *
                ENNReal.ofReal (a ^ κ) := mul_le_mul_of_nonneg_left hle bot_le
            _ = _ := mul_comm _ _
        · rw [winIcc_slice_empty hsub hx]; simp
    _ = ENNReal.ofReal (a ^ κ) *
          ∫⁻ x, (UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' (S ∩ winIcc a B))
            ∂((volume : Measure ℝ).restrict (Ioi 0)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (a ^ κ) *
          ∫⁻ x, (UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' (S ∩ winIcc a B))
            ∂(volume : Measure ℝ) :=
        mul_le_mul_of_nonneg_left (lintegral_mono' Measure.restrict_le_self le_rfl) bot_le

private theorem cylMeas_restrict_le_hMeas_bgp {c a B : ℝ} (ha : 0 < a) (haB : a ≤ B) :
    (cylMeas c).restrict (winIcc a B) ≤
      ENNReal.ofReal (B ^ (-(bgp / 2 - 5 / 2))) • (hMeas c bgp).restrict (winIcc a B) := by
  set κ : ℝ := bgp / 2 - 5 / 2
  have hκ0 : κ ≤ 0 := by norm_num [κ, bgp]
  have hB0 : 0 < B := lt_of_lt_of_le ha haB
  rw [Measure.le_iff]
  intro S hS
  simp only [Measure.smul_apply, Measure.restrict_apply hS, smul_eq_mul, hMeas]
  have hSW : MeasurableSet (S ∩ winIcc a B) := hS.inter (measurableSet_winIcc a B)
  have hsub : S ∩ winIcc a B ⊆ winIcc a B := inter_subset_right
  have hsupp : Function.support
      (fun x => (UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' (S ∩ winIcc a B))) ⊆ Ioi (0 : ℝ) := by
    intro x hx
    have hxI : x ∈ Icc a B := by
      by_contra h'
      exact hx (winIcc_slice_empty hsub h')
    exact lt_of_lt_of_le ha hxI.1
  have hEq : ∫⁻ x, (UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' (S ∩ winIcc a B)) ∂(volume : Measure ℝ) =
      ∫⁻ x in Ioi (0 : ℝ), (UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' (S ∩ winIcc a B))
        ∂(volume : Measure ℝ) :=
    (setLIntegral_eq_of_support_subset hsupp).symm
  rw [wwc_ageμ_apply c κ hSW, wwc_cyl_apply c hSW, hEq]
  calc ∫⁻ x, (UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' (S ∩ winIcc a B))
        ∂((volume : Measure ℝ).restrict (Ioi 0))
      ≤ ∫⁻ x, ENNReal.ofReal (B ^ (-κ)) *
          ((UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' (S ∩ winIcc a B)) * ENNReal.ofReal (x ^ κ))
        ∂((volume : Measure ℝ).restrict (Ioi 0)) := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ Icc a B
        · have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
          have hBx : B ^ κ ≤ x ^ κ := Real.rpow_le_rpow_of_nonpos hx0 hx.2 hκ0
          have h1 : (1 : ℝ) ≤ B ^ (-κ) * x ^ κ := by
            have hmul : B ^ (-κ) * B ^ κ = 1 := by
              rw [← Real.rpow_add hB0, neg_add_cancel, Real.rpow_zero]
            have hnn : 0 ≤ B ^ (-κ) := Real.rpow_nonneg hB0.le _
            nlinarith [mul_le_mul_of_nonneg_left hBx hnn]
          have hE1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (B ^ (-κ)) * ENNReal.ofReal (x ^ κ) := by
            rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hB0.le _)]
            simpa using ENNReal.ofReal_le_ofReal h1
          calc (UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' (S ∩ winIcc a B))
              = (UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' (S ∩ winIcc a B)) * 1 := (mul_one _).symm
            _ ≤ (UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' (S ∩ winIcc a B)) *
                  (ENNReal.ofReal (B ^ (-κ)) * ENNReal.ofReal (x ^ κ)) :=
                mul_le_mul_of_nonneg_left hE1 bot_le
            _ = ENNReal.ofReal (B ^ (-κ)) *
                  ((UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' (S ∩ winIcc a B)) *
                    ENNReal.ofReal (x ^ κ)) := by ring
        · rw [winIcc_slice_empty hsub hx]; simp
    _ = ENNReal.ofReal (B ^ (-κ)) *
          ∫⁻ x, (UnforcedLeray.Cyl.avgμ c) (Prod.mk x ⁻¹' (S ∩ winIcc a B)) * ENNReal.ofReal (x ^ κ)
            ∂((volume : Measure ℝ).restrict (Ioi 0)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

private theorem hNorm_le_cylNorm_sum_of_sCut {c a B : ℝ} (ha : 0 < a) {G : CProf}
    (hcut : SCut a B G)
    (hm0 : AEStronglyMeasurable (fun x => G x 0) (cylMeas c))
    (hm1 : AEStronglyMeasurable (fun x => G x 1) (cylMeas c)) :
    hNorm c bgp G ≤
      (ENNReal.ofReal (a ^ (bgp / 2 - 5 / 2))) ^ (1 / bgp) *
        (cylNorm c bgp (fun x => G x 0) + cylNorm c bgp (fun x => G x 1)) := by
  have hsupp : Function.support G ⊆ winIcc a B := by
    intro x hx
    refine ⟨⟨?_, ?_⟩, trivial⟩
    · by_contra hlt; exact hx (hcut x (Or.inl (not_le.mp hlt)))
    · by_contra hgt; exact hx (hcut x (Or.inr (not_le.mp hgt)))
  have hp : ENNReal.ofReal bgp ≠ ⊤ := ENNReal.ofReal_ne_top
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal bgp := by
    rw [ENNReal.one_le_ofReal]; norm_num [bgp]
  have hpinv : (1 / ENNReal.ofReal bgp).toReal = 1 / bgp := by
    rw [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofReal (by norm_num [bgp]), one_div]
  have hpt : ∀ x : Coord, ‖G x‖ ≤ ‖G x 0‖ + ‖G x 1‖ := fun x => by
    calc ‖G x‖ = Real.sqrt (‖G x 0‖ ^ 2 + ‖G x 1‖ ^ 2) := by
          simp [PiLp.norm_eq_of_L2, Fin.sum_univ_two]
      _ ≤ Real.sqrt ((‖G x 0‖ + ‖G x 1‖) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [norm_nonneg (G x 0), norm_nonneg (G x 1)])
      _ = ‖G x 0‖ + ‖G x 1‖ := Real.sqrt_sq (by positivity)
  calc hNorm c bgp G
      = eLpNorm G (ENNReal.ofReal bgp) ((hMeas c bgp).restrict (winIcc a B)) := by
          unfold hNorm; rw [eLpNorm_restrict_eq_of_support_subset hsupp]
    _ ≤ eLpNorm G (ENNReal.ofReal bgp)
          (ENNReal.ofReal (a ^ (bgp / 2 - 5 / 2)) • (cylMeas c).restrict (winIcc a B)) :=
        eLpNorm_mono_measure G (hMeas_bgp_restrict_le ha)
    _ = (ENNReal.ofReal (a ^ (bgp / 2 - 5 / 2))) ^ (1 / bgp) *
          eLpNorm G (ENNReal.ofReal bgp) ((cylMeas c).restrict (winIcc a B)) := by
        rw [eLpNorm_smul_measure_of_ne_top hp, hpinv, smul_eq_mul]
    _ ≤ (ENNReal.ofReal (a ^ (bgp / 2 - 5 / 2))) ^ (1 / bgp) *
          eLpNorm G (ENNReal.ofReal bgp) (cylMeas c) :=
        mul_le_mul_of_nonneg_left (eLpNorm_mono_measure G Measure.restrict_le_self) bot_le
    _ ≤ (ENNReal.ofReal (a ^ (bgp / 2 - 5 / 2))) ^ (1 / bgp) *
          (cylNorm c bgp (fun x => G x 0) + cylNorm c bgp (fun x => G x 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ bot_le
        calc eLpNorm G (ENNReal.ofReal bgp) (cylMeas c)
            = eLpNorm (fun x => ‖G x‖) (ENNReal.ofReal bgp) (cylMeas c) := by rw [eLpNorm_norm]
          _ ≤ eLpNorm ((fun x => ‖G x 0‖) + (fun x => ‖G x 1‖))
                (ENNReal.ofReal bgp) (cylMeas c) :=
              eLpNorm_mono_real fun x => by simpa [Pi.add_apply] using hpt x
          _ ≤ eLpNorm (fun x => ‖G x 0‖) (ENNReal.ofReal bgp) (cylMeas c) +
                eLpNorm (fun x => ‖G x 1‖) (ENNReal.ofReal bgp) (cylMeas c) :=
              eLpNorm_add_le hm0.norm hm1.norm hp1
          _ = cylNorm c bgp (fun x => G x 0) + cylNorm c bgp (fun x => G x 1) := by
              rw [eLpNorm_norm, eLpNorm_norm]

private theorem hNorm_sqrtS_le_of_sCut {c a B : ℝ} (ha : 0 < a) (haB : a ≤ B) {G : CProf}
    (hcut : SCut a B G) :
    hNorm c bgp (sqrtS G) ≤ ENNReal.ofReal (Real.sqrt B) * hNorm c bgp G := by
  have hB0 : 0 ≤ B := (ha.le.trans haB)
  have hpt : ∀ x : Coord, ‖sqrtS G x‖ ≤ Real.sqrt B * ‖G x‖ := by
    intro x
    by_cases hxB : x.1 ≤ B
    · simp only [sqrtS, norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hxB) (norm_nonneg _)
    · have h0 : G x = 0 := hcut x (Or.inr (not_le.mp hxB))
      simp [sqrtS, h0]
  unfold hNorm
  calc eLpNorm (sqrtS G) (ENNReal.ofReal bgp) (hMeas c bgp)
      = eLpNorm (fun x => ‖sqrtS G x‖) (ENNReal.ofReal bgp) (hMeas c bgp) := by rw [eLpNorm_norm]
    _ ≤ eLpNorm (fun x => Real.sqrt B * ‖G x‖) (ENNReal.ofReal bgp) (hMeas c bgp) :=
        eLpNorm_mono_real fun x => by simpa using hpt x
    _ = ENNReal.ofReal (Real.sqrt B) * eLpNorm G (ENNReal.ofReal bgp) (hMeas c bgp) :=
        wbdb_smul_eLpNorm (Real.sqrt_nonneg B) G (ENNReal.ofReal bgp) (hMeas c bgp)

/-! ## 2. Extracting component `cylMeas` data from `InHr c bgp` on `[s₀, s₁]` -/

private theorem inHr_of_sqrtS_sCut {c s₀ s₁ : ℝ} (hs₀ : 0 < s₀) {G : CProf}
    (hcut : SCut s₀ s₁ G) (hin : InHr c bgp (sqrtS G)) :
    InHr c bgp G := by
  set w : Coord → ℂ := fun x => if s₀ ≤ x.1 then Complex.ofReal ((Real.sqrt x.1)⁻¹) else 0
  have hG_eq : G = fun x => w x • sqrtS G x := by
    funext x
    dsimp only [w]
    split_ifs with hx
    · have hspos : 0 < x.1 := lt_of_lt_of_le hs₀ hx
      have hsne : Real.sqrt x.1 ≠ 0 := (Real.sqrt_pos.mpr hspos).ne'
      simp only [sqrtS, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hsne,
        Complex.ofReal_one, one_smul]
    · simp only [zero_smul, hcut x (Or.inl (not_le.mp hx))]
  have hw_meas : Measurable w := by
    refine Measurable.ite (measurableSet_le measurable_const measurable_fst) ?_ measurable_const
    exact Complex.measurable_ofReal.comp measurable_fst.sqrt.inv
  have hw_bd : ∀ x : Coord, ‖w x‖ ≤ (Real.sqrt s₀)⁻¹ := by
    intro x
    dsimp only [w]
    split_ifs with hx
    · rw [Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
      exact inv_anti₀ (Real.sqrt_pos.mpr hs₀) (Real.sqrt_le_sqrt hx)
    · rw [norm_zero]
      exact inv_nonneg.mpr (Real.sqrt_nonneg _)
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hin.periodic] with x hx
    have h1 : G (qShift c x) = w (qShift c x) • sqrtS G (qShift c x) := congrFun hG_eq (qShift c x)
    have h2 : G x = w x • sqrtS G x := congrFun hG_eq x
    have hw_sh : w (qShift c x) = w x := rfl
    rw [h1, h2, hw_sh, hx]
  · rw [hG_eq]
    exact hw_meas.aestronglyMeasurable.smul hin.meas
  · unfold hNorm
    have hpt : ∀ x : Coord, ‖G x‖ ≤ (Real.sqrt s₀)⁻¹ * ‖sqrtS G x‖ := by
      intro x
      have hx_eq : G x = w x • sqrtS G x := congrFun hG_eq x
      rw [hx_eq, norm_smul]
      exact mul_le_mul_of_nonneg_right (hw_bd x) (norm_nonneg _)
    have hle : eLpNorm G (ENNReal.ofReal bgp) (hMeas c bgp) ≤
        ENNReal.ofReal (Real.sqrt s₀)⁻¹ * hNorm c bgp (sqrtS G) := by
      calc eLpNorm G (ENNReal.ofReal bgp) (hMeas c bgp)
          = eLpNorm (fun x => ‖G x‖) (ENNReal.ofReal bgp) (hMeas c bgp) := by rw [eLpNorm_norm]
        _ ≤ eLpNorm (fun x => (Real.sqrt s₀)⁻¹ * ‖sqrtS G x‖) (ENNReal.ofReal bgp) (hMeas c bgp) :=
            eLpNorm_mono_real fun x => by simpa using hpt x
        _ = ENNReal.ofReal (Real.sqrt s₀)⁻¹ * hNorm c bgp (sqrtS G) :=
            wbdb_smul_eLpNorm (inv_nonneg.mpr (Real.sqrt_nonneg _)) (sqrtS G)
              (ENNReal.ofReal bgp) (hMeas c bgp)
    exact lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hin.finite)

private theorem cylData_of_inHr_sCut {c s₀ s₁ : ℝ} (hc : 0 < c) (hs₀ : 0 < s₀) (hs₀₁ : s₀ ≤ s₁)
    {G : CProf} (hin : InHr c bgp G) (hcut : SCut s₀ s₁ G) (i : Fin 2) :
    QPeriodicS c (fun x => G x i) ∧
      AEStronglyMeasurable (fun x => G x i) volume ∧
      cylNorm c bgp (fun x => G x i) < ⊤ ∧
      LocallyIntegrable (fun x => G x i) volume := by
  have hbgp1 : (1 : ℝ) < bgp := by norm_num [bgp]
  have hper : QPeriodicS c (fun x => G x i) := by
    have hpos_open : MeasurableSet {x : Coord | 0 < x.1} :=
      (isOpen_lt continuous_const continuous_fst).measurableSet
    have hae := (ae_restrict_iff' hpos_open).mp hin.periodic
    filter_upwards [hae] with x hx
    by_cases hxp : 0 < x.1
    · exact congrArg (fun m => m i) (hx hxp)
    · have h1 : (qShift c x).1 < s₀ := by show x.1 < s₀; linarith
      have h2 : x.1 < s₀ := by linarith
      simp [hcut (qShift c x) (Or.inl h1), hcut x (Or.inl h2)]
  have hmeas : AEStronglyMeasurable (fun x => G x i) volume := by
    obtain ⟨G', hG's, hGa⟩ := exists_periodic_rep (a := bgp / 2 - 5 / 2) hc hin.periodic hin.meas
    set g' : Coord → ℂ := fun x => if 0 < x.1 then G' x i else 0
    have hg'_m : Measurable g' :=
      Measurable.ite (measurableSet_lt measurable_const measurable_fst)
        ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.measurable.comp hG's.measurable)
        measurable_const
    refine hg'_m.aestronglyMeasurable.congr ?_
    filter_upwards [hGa] with x hx
    dsimp only [g']
    split_ifs with hxp
    · simp [hx hxp]
    · simp [hcut x (Or.inl (by linarith))]
  have hfin : cylNorm c bgp (fun x => G x i) < ⊤ := by
    have hsupp : Function.support (fun x : Coord => G x i) ⊆ winIcc s₀ s₁ := by
      intro x hx
      refine ⟨⟨?_, ?_⟩, trivial⟩
      · by_contra hlt; exact hx (by simp [hcut x (Or.inl (not_le.mp hlt))])
      · by_contra hgt; exact hx (by simp [hcut x (Or.inr (not_le.mp hgt))])
    have hp : ENNReal.ofReal bgp ≠ ⊤ := ENNReal.ofReal_ne_top
    have hpinv : (1 / ENNReal.ofReal bgp).toReal = 1 / bgp := by
      rw [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofReal (by norm_num [bgp]), one_div]
    have hle : cylNorm c bgp (fun x => G x i) ≤
        (ENNReal.ofReal (s₁ ^ (-(bgp / 2 - 5 / 2)))) ^ (1 / bgp) * hNorm c bgp G := by
      calc cylNorm c bgp (fun x => G x i)
          = eLpNorm (fun x => G x i) (ENNReal.ofReal bgp) ((cylMeas c).restrict (winIcc s₀ s₁)) := by
              unfold cylNorm; rw [eLpNorm_restrict_eq_of_support_subset hsupp]
        _ ≤ eLpNorm (fun x => G x i) (ENNReal.ofReal bgp)
              (ENNReal.ofReal (s₁ ^ (-(bgp / 2 - 5 / 2))) • (hMeas c bgp).restrict (winIcc s₀ s₁)) :=
            eLpNorm_mono_measure _ (cylMeas_restrict_le_hMeas_bgp hs₀ hs₀₁)
        _ = (ENNReal.ofReal (s₁ ^ (-(bgp / 2 - 5 / 2)))) ^ (1 / bgp) *
              eLpNorm (fun x => G x i) (ENNReal.ofReal bgp)
                ((hMeas c bgp).restrict (winIcc s₀ s₁)) := by
            rw [eLpNorm_smul_measure_of_ne_top hp, hpinv, smul_eq_mul]
        _ ≤ (ENNReal.ofReal (s₁ ^ (-(bgp / 2 - 5 / 2)))) ^ (1 / bgp) *
              eLpNorm (fun x => G x i) (ENNReal.ofReal bgp) (hMeas c bgp) :=
            mul_le_mul_of_nonneg_left (eLpNorm_mono_measure _ Measure.restrict_le_self) bot_le
        _ ≤ (ENNReal.ofReal (s₁ ^ (-(bgp / 2 - 5 / 2)))) ^ (1 / bgp) * hNorm c bgp G :=
            mul_le_mul_of_nonneg_left
              (wbdb_le_norm fun x => PiLp.norm_apply_le (G x) i) bot_le
    exact lt_of_le_of_lt hle
      (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num [bgp]) ENNReal.ofReal_ne_top)
        hin.finite)
  exact ⟨hper, hmeas, hfin, mollLoc_proof c bgp hc hbgp1 _ hper hmeas hfin⟩

/-! ## 3. Pointwise classical derivatives of `b_n` (`Eb_n` and Friedrichs `Qb_n`) -/

private def mollVec (n : ℕ) (f : CProf) : CProf :=
  fun x => WithLp.toLp 2 fun i : Fin 2 => convK (molN mollExistsRho n) (fun y => f y i) x

private theorem contDiff_mollVec {c : ℝ} (n : ℕ) {f : CProf}
    (hper : ∀ i : Fin 2, QPeriodicS c (fun y => f y i))
    (hloc : ∀ i : Fin 2, LocallyIntegrable (fun y => f y i) volume) :
    ContDiff ℝ ∞ (mollVec n f) ∧ ∀ x : Coord, mollVec n f (qShift c x) = mollVec n f x := by
  have hker : IsKer (molN mollExistsRho n) :=
    (mollExists_molN_isMollifier mollExistsRho mollExists_base_isMollifier n).1
  have hcomp := fun i : Fin 2 => mollConvNice_proof c (molN mollExistsRho n) (fun y => f y i)
    hker (hper i) (hloc i)
  refine ⟨?_, ?_⟩
  · exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℂ)).symm.contDiff.comp
      (contDiff_pi.mpr fun i => (hcomp i).1)
  · intro x; ext i; exact (hcomp i).2 x

private def sCutSmooth (s₀ : ℝ) (s : ℝ) : ℝ :=
  Real.smoothTransition ((4 / s₀) * s - 1)

private theorem isCoordTest_sCut_ker {s₀ : ℝ} (hs₀ : 0 < s₀) {κ : Coord → ℝ} (hκ : IsKer κ)
    (x : Coord) :
    IsCoordTest (fun z : Coord => sCutSmooth s₀ z.1 * κ (x - z)) := by
  have hθ : ContDiff ℝ ∞ (fun z : Coord => sCutSmooth s₀ z.1) :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_fst).sub contDiff_const)
  have hk : ContDiff ℝ ∞ (fun z : Coord => κ (x - z)) :=
    hκ.1.comp (contDiff_const.sub contDiff_id)
  have hcs : HasCompactSupport (fun z : Coord => sCutSmooth s₀ z.1 * κ (x - z)) :=
    (hκ.2.comp_homeomorph (Homeomorph.subLeft x)).mul_left
  refine ⟨hθ.mul hk, hcs, ?_⟩
  intro y hy
  have hyθ : y ∈ tsupport (fun z : Coord => sCutSmooth s₀ z.1) := tsupport_mul_subset_left hy
  have hge : s₀ / 4 ≤ y.1 := by
    by_contra hlt
    have hlt' : y.1 < s₀ / 4 := not_le.mp hlt
    have hopen : IsOpen {z : Coord | z.1 < s₀ / 4} := isOpen_lt continuous_fst continuous_const
    have hzero : ∀ z ∈ {z : Coord | z.1 < s₀ / 4}, sCutSmooth s₀ z.1 = 0 := by
      intro z hz
      have hz' : z.1 < s₀ / 4 := hz
      apply Real.smoothTransition.zero_of_nonpos
      have hmul : (4 / s₀) * z.1 < (4 / s₀) * (s₀ / 4) :=
        mul_lt_mul_of_pos_left hz' (by positivity)
      have hcancel : (4 / s₀) * (s₀ / 4) = 1 := by field_simp [hs₀.ne']
      linarith
    have hnot : y ∉ tsupport (fun z : Coord => sCutSmooth s₀ z.1) := by
      rw [notMem_tsupport_iff_eventuallyEq]
      filter_upwards [hopen.mem_nhds hlt'] with z hz
      exact hzero z hz
    exact hnot hyθ
  exact ⟨lt_of_lt_of_le (by positivity) hge, trivial⟩

private theorem sCut_ker_eventuallyEq_of_ge {s₀ : ℝ} (hs₀ : 0 < s₀) (κ : Coord → ℝ) (x : Coord)
    {y : Coord} (hy : s₀ ≤ y.1) :
    (fun z : Coord => sCutSmooth s₀ z.1 * κ (x - z)) =ᶠ[𝓝 y] fun z : Coord => κ (x - z) := by
  have hopen : IsOpen {z : Coord | s₀ / 2 < z.1} := isOpen_lt continuous_const continuous_fst
  have hmem : y ∈ {z : Coord | s₀ / 2 < z.1} := by show s₀ / 2 < y.1; linarith
  filter_upwards [hopen.mem_nhds hmem] with z hz
  have hz' : s₀ / 2 < z.1 := hz
  have h1 : sCutSmooth s₀ z.1 = 1 := by
    apply Real.smoothTransition.one_of_one_le
    have hmul : (4 / s₀) * (s₀ / 2) ≤ (4 / s₀) * z.1 :=
      mul_le_mul_of_nonneg_left hz'.le (by positivity)
    have hcancel : (4 / s₀) * (s₀ / 2) = 2 := by field_simp [hs₀.ne']; ring
    linarith
  rw [h1, one_mul]

private theorem coordTranspose_sCut_ker_eq {s₀ : ℝ} (hs₀ : 0 < s₀)
    (v : Coord → Fin 3 → ℝ) (d : Coord → ℝ) (κ : Coord → ℝ) (x : Coord)
    {y : Coord} (hy : s₀ ≤ y.1) :
    coordTranspose v d (fun z : Coord => sCutSmooth s₀ z.1 * κ (x - z)) y =
      coordTranspose v d (fun z : Coord => κ (x - z)) y := by
  have hev := sCut_ker_eventuallyEq_of_ge hs₀ κ x hy
  have hφ : sCutSmooth s₀ y.1 * κ (x - y) = κ (x - y) := hev.eq_of_nhds
  have hcpd : ∀ j : Fin 3,
      cpd j (fun z => v z j * (sCutSmooth s₀ z.1 * κ (x - z))) y =
        cpd j (fun z => v z j * κ (x - z)) y := by
    intro j
    have hevj : (fun z => v z j * (sCutSmooth s₀ z.1 * κ (x - z))) =ᶠ[𝓝 y]
        fun z => v z j * κ (x - z) :=
      hev.mono fun z hz => by dsimp only at hz ⊢; rw [hz]
    unfold cpd
    rw [hevj.fderiv_eq]
  simp only [coordTranspose, hcpd, hφ]

private theorem fderiv_mollVec_cdir {c : ℝ} (n : ℕ) {f : CProf}
    (hper : ∀ i : Fin 2, QPeriodicS c (fun y => f y i))
    (hloc : ∀ i : Fin 2, LocallyIntegrable (fun y => f y i) volume)
    (j : Fin 3) (x : Coord) (i : Fin 2) :
    fderiv ℝ (mollVec n f) x (cdir j) i =
      convK (cpd j (molN mollExistsRho n)) (fun y => f y i) x := by
  have hsm := (contDiff_mollVec n hper hloc).1
  have hbd : DifferentiableAt ℝ (mollVec n f) x := hsm.differentiable (by simp) x
  have hL := ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).restrictScalars ℝ).hasFDerivAt.comp
    x hbd.hasFDerivAt
  have h1 : fderiv ℝ (fun y => mollVec n f y i) x =
      ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).restrictScalars ℝ).comp
        (fderiv ℝ (mollVec n f) x) := hL.fderiv
  have h2 : fderiv ℝ (mollVec n f) x (cdir j) i =
      cdv j (convK (molN mollExistsRho n) (fun y => f y i)) x := by
    have := congrArg (fun L : Coord →L[ℝ] ℂ => L (cdir j)) h1
    simpa [cdv, mollVec] using this.symm
  have hker : IsKer (molN mollExistsRho n) :=
    (mollExists_molN_isMollifier mollExistsRho mollExists_base_isMollifier n).1
  rw [h2, mollDeriv_proof (molN mollExistsRho n) (fun y => f y i) hker (hloc i) j]

private theorem classOp_vEta_mollVec_eq {c s₀ s₁ : ℝ} (hs₀ : 0 < s₀) (n : ℕ)
    {b Eb : CProf} (hb_cut : SCut s₀ s₁ b) (hEb_cut : SCut s₀ s₁ Eb)
    (hper : ∀ i : Fin 2, QPeriodicS c (fun y => b y i))
    (hloc : ∀ i : Fin 2, LocallyIntegrable (fun y => b y i) volume)
    (hEb : HasWeakVec vEta dZero b Eb) (x : Coord) (i : Fin 2) :
    classOp vEta dZero (mollVec n b) x i =
      convK (molN mollExistsRho n) (fun y => Eb y i) x := by
  set κ := molN mollExistsRho n
  have hker : IsKer κ :=
    (mollExists_molN_isMollifier mollExistsRho mollExists_base_isMollifier n).1
  have hcl : classOp vEta dZero (mollVec n b) x i = convK (cpd 2 κ) (fun y => b y i) x := by
    simp only [classOp, vEta, dZero, Fin.sum_univ_three, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Complex.ofReal_zero, Complex.ofReal_one,
      zero_smul, one_smul, zero_add, add_zero]
    exact fderiv_mollVec_cdir n hper hloc 2 x i
  rw [hcl]
  set φ := fun z : Coord => sCutSmooth s₀ z.1 * κ (x - z)
  have hφ : IsCoordTest φ := isCoordTest_sCut_ker hs₀ hker x
  have hweak := (hEb i).2 φ hφ
  have hL : (∫ y : Coord, Eb y i * (φ y : ℂ)) = convK κ (fun y => Eb y i) x := by
    unfold convK
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only [φ]
    by_cases hy : s₀ ≤ y.1
    · rw [(sCut_ker_eventuallyEq_of_ge hs₀ κ x hy).eq_of_nhds]
    · simp [hEb_cut y (Or.inl (not_le.mp hy))]
  have hR : (∫ y : Coord, b y i * (coordTranspose vEta dZero φ y : ℂ)) =
      convK (cpd 2 κ) (fun y => b y i) x := by
    unfold convK
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only [φ]
    by_cases hy : s₀ ≤ y.1
    · rw [coordTranspose_sCut_ker_eq hs₀ vEta dZero κ x hy]
      have hct : coordTranspose vEta dZero (fun z => κ (x - z)) y = cpd 2 κ (x - y) := by
        have e0 : (fun z : Coord => vEta z 0 * κ (x - z)) = fun _ => 0 := by funext z; simp [vEta]
        have e1 : (fun z : Coord => vEta z 1 * κ (x - z)) = fun _ => 0 := by funext z; simp [vEta]
        have e2 : (fun z : Coord => vEta z 2 * κ (x - z)) = fun z => κ (x - z) := by
          funext z; simp [vEta]
        unfold coordTranspose
        rw [Fin.sum_univ_three, e0, e1, e2,
          mwd2_cpd_reflect 2 κ (hker.1.differentiable (by simp)) x y]
        simp [cpd, dZero]
      rw [hct]
    · simp [hb_cut y (Or.inl (not_le.mp hy))]
  rw [← hR, ← hweak, hL]

private theorem coordTranspose_vQ_reflect {ε : ℝ} {κ : Coord → ℝ} (hκ : ContDiff ℝ ∞ κ)
    (x y : Coord) :
    coordTranspose (vQ ε) (dQ ε) (fun z : Coord => κ (x - z)) y =
      (-2 * ε * y.1) * cpd 0 κ (x - y) + cpd 1 κ (x - y) +
        (-ε * y.2.2) * cpd 2 κ (x - y) + 2 * ε * κ (x - y) := by
  have hκd : Differentiable ℝ κ := hκ.differentiable (by simp)
  have hg_diff : DifferentiableAt ℝ (fun z : Coord => κ (x - z)) y :=
    (hκ.comp (contDiff_const.sub contDiff_id)).differentiable (by simp) y
  have lin_cpd : ∀ (ℓ : Coord →L[ℝ] ℝ) (j : Fin 3),
      cpd j (fun z : Coord => ℓ z * κ (x - z)) y =
        -(ℓ y * cpd j κ (x - y)) + ℓ (cdir j) * κ (x - y) := by
    intro ℓ j
    have hp := ℓ.hasFDerivAt.mul hg_diff.hasFDerivAt
    have href := mwd2_cpd_reflect j κ hκd x y
    unfold cpd at href ⊢
    change fderiv ℝ ((fun z : Coord => ℓ z) * fun z : Coord => κ (x - z)) y (cdir j) = _
    rw [hp.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul, href]
    ring
  have e0 : (fun z : Coord => vQ ε z 0 * κ (x - z)) =
      fun z => (((-2 * ε) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) z) * κ (x - z) := by
    funext z; simp [vQ]
  have e1 : (fun z : Coord => vQ ε z 1 * κ (x - z)) = fun z => κ (x - z) := by
    funext z; simp [vQ]
  have e2 : (fun z : Coord => vQ ε z 2 * κ (x - z)) =
      fun z => (((-ε) • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) z) * κ (x - z) := by
    funext z; simp [vQ]
  unfold coordTranspose
  rw [Fin.sum_univ_three, e0, e1, e2, lin_cpd _ 0,
    mwd2_cpd_reflect 1 κ hκd x y, lin_cpd _ 2]
  simp [dQ, cdir]
  ring

private theorem int_ker_mul {κ : Coord → ℝ} (hκ : IsKer κ) {u : Coord → ℂ}
    (hu : LocallyIntegrable u volume) (x : Coord) :
    Integrable (fun y : Coord => u y * (κ (x - y) : ℂ)) volume := by
  have hc : Continuous (fun y : Coord => (κ (x - y) : ℂ)) :=
    Complex.continuous_ofReal.comp (hκ.1.continuous.comp (continuous_const.sub continuous_id))
  have hs : HasCompactSupport (fun y : Coord => (κ (x - y) : ℂ)) :=
    (hκ.2.comp_homeomorph (Homeomorph.subLeft x)).comp_left Complex.ofReal_zero
  simpa [mul_comm] using hu.integrable_smul_left_of_hasCompactSupport hc hs

private theorem classOp_vQ_mollVec_eq {c ε s₀ s₁ : ℝ} (hs₀ : 0 < s₀) (n : ℕ)
    {b Qb : CProf} (hb_cut : SCut s₀ s₁ b) (hQb_cut : SCut s₀ s₁ Qb)
    (hper : ∀ i : Fin 2, QPeriodicS c (fun y => b y i))
    (hloc : ∀ i : Fin 2, LocallyIntegrable (fun y => b y i) volume)
    (hQb : HasWeakVec (vQ ε) (dQ ε) b Qb) (x : Coord) (i : Fin 2) :
    classOp (vQ ε) (dQ ε) (mollVec n b) x i =
      convK (molN mollExistsRho n) (fun y => Qb y i) x -
        (ε : ℂ) * convK (molN psi0 n) (fun y => b y i) x := by
  set κ := molN mollExistsRho n
  set u : Coord → ℂ := fun y => b y i
  have hker : IsKer κ :=
    (mollExists_molN_isMollifier mollExistsRho mollExists_base_isMollifier n).1
  have hcl : classOp (vQ ε) (dQ ε) (mollVec n b) x i =
      ((-2 * ε * x.1 : ℝ) : ℂ) * convK (cpd 0 κ) u x +
        convK (cpd 1 κ) u x +
        ((-ε * x.2.2 : ℝ) : ℂ) * convK (cpd 2 κ) u x +
        ((-ε : ℝ) : ℂ) * convK κ u x := by
    have f0 := fderiv_mollVec_cdir n hper hloc 0 x i
    have f1 := fderiv_mollVec_cdir n hper hloc 1 x i
    have f2 := fderiv_mollVec_cdir n hper hloc 2 x i
    simp only [classOp, vQ, dQ, Fin.sum_univ_three, Fin.isValue, PiLp.add_apply, PiLp.smul_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, smul_eq_mul, f0, f1, f2, mollVec]
    push_cast
    ring
  set φ := fun z : Coord => sCutSmooth s₀ z.1 * κ (x - z)
  have hφ : IsCoordTest φ := isCoordTest_sCut_ker hs₀ hker x
  have hweak' : (∫ y : Coord, Qb y i * (φ y : ℂ)) =
      ∫ y : Coord, u y * (coordTranspose (vQ ε) (dQ ε) φ y : ℂ) := (hQb i).2 φ hφ
  have hL : (∫ y : Coord, Qb y i * (φ y : ℂ)) = convK κ (fun y => Qb y i) x := by
    unfold convK
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only [φ]
    by_cases hy : s₀ ≤ y.1
    · rw [(sCut_ker_eventuallyEq_of_ge hs₀ κ x hy).eq_of_nhds]
    · simp [hQb_cut y (Or.inl (not_le.mp hy))]
  have hu : LocallyIntegrable u volume := hloc i
  have I0 : Integrable (fun y : Coord =>
      ((-2 * ε * x.1 : ℝ) : ℂ) * (u y * (cpd 0 κ (x - y) : ℂ))) volume :=
    (int_ker_mul (mwd2_isKer_cpd 0 κ hker) hu x).const_mul ((-2 * ε * x.1 : ℝ) : ℂ)
  have I1 : Integrable (fun y : Coord => u y * (cpd 1 κ (x - y) : ℂ)) volume :=
    int_ker_mul (mwd2_isKer_cpd 1 κ hker) hu x
  have I2 : Integrable (fun y : Coord =>
      ((-ε * x.2.2 : ℝ) : ℂ) * (u y * (cpd 2 κ (x - y) : ℂ))) volume :=
    (int_ker_mul (mwd2_isKer_cpd 2 κ hker) hu x).const_mul ((-ε * x.2.2 : ℝ) : ℂ)
  have I3 : Integrable (fun y : Coord =>
      ((-ε : ℝ) : ℂ) * (u y * (κ (x - y) : ℂ))) volume :=
    (int_ker_mul hker hu x).const_mul ((-ε : ℝ) : ℂ)
  have hadd1 := integral_add I0 I1
  have hadd2 := integral_add (I0.add I1) I2
  have hadd3 := integral_add ((I0.add I1).add I2) I3
  dsimp only [Pi.add_apply] at hadd1 hadd2 hadd3
  have hcl_int : classOp (vQ ε) (dQ ε) (mollVec n b) x i =
      ∫ y : Coord,
        (((-2 * ε * x.1 : ℝ) : ℂ) * (u y * (cpd 0 κ (x - y) : ℂ)) +
          u y * (cpd 1 κ (x - y) : ℂ) +
          ((-ε * x.2.2 : ℝ) : ℂ) * (u y * (cpd 2 κ (x - y) : ℂ)) +
          ((-ε : ℝ) : ℂ) * (u y * (κ (x - y) : ℂ))) := by
    rw [hcl]
    unfold convK
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul,
      ← hadd1, ← hadd2, ← hadd3]
  obtain ⟨I_ct_raw, _⟩ := (hQb i).1 φ hφ
  have I_ct : Integrable (fun y : Coord => u y * (coordTranspose (vQ ε) (dQ ε) φ y : ℂ)) volume :=
    I_ct_raw
  have hsub := integral_sub (((I0.add I1).add I2).add I3) I_ct
  dsimp only [Pi.add_apply] at hsub
  have hsub_int : classOp (vQ ε) (dQ ε) (mollVec n b) x i - convK κ (fun y => Qb y i) x =
      ∫ y : Coord,
        (((((-2 * ε * x.1 : ℝ) : ℂ) * (u y * (cpd 0 κ (x - y) : ℂ)) +
            u y * (cpd 1 κ (x - y) : ℂ) +
            ((-ε * x.2.2 : ℝ) : ℂ) * (u y * (cpd 2 κ (x - y) : ℂ)) +
            ((-ε : ℝ) : ℂ) * (u y * (κ (x - y) : ℂ))) -
          u y * (coordTranspose (vQ ε) (dQ ε) φ y : ℂ))) := by
    rw [hcl_int, ← hL, hweak', ← hsub]
  have hrhs_eq : (∫ y : Coord,
      (((((-2 * ε * x.1 : ℝ) : ℂ) * (u y * (cpd 0 κ (x - y) : ℂ)) +
          u y * (cpd 1 κ (x - y) : ℂ) +
          ((-ε * x.2.2 : ℝ) : ℂ) * (u y * (cpd 2 κ (x - y) : ℂ)) +
          ((-ε : ℝ) : ℂ) * (u y * (κ (x - y) : ℂ))) -
        u y * (coordTranspose (vQ ε) (dQ ε) φ y : ℂ)))) =
      -(ε : ℂ) * convK (molN psi0 n) u x := by
    have hpt : ∀ y : Coord,
        ((((-2 * ε * x.1 : ℝ) : ℂ) * (u y * (cpd 0 κ (x - y) : ℂ)) +
            u y * (cpd 1 κ (x - y) : ℂ) +
            ((-ε * x.2.2 : ℝ) : ℂ) * (u y * (cpd 2 κ (x - y) : ℂ)) +
            ((-ε : ℝ) : ℂ) * (u y * (κ (x - y) : ℂ))) -
          u y * (coordTranspose (vQ ε) (dQ ε) φ y : ℂ)) =
        (-(ε : ℂ)) * (u y * (molN psi0 n (x - y) : ℂ)) := by
      intro y
      by_cases hy : s₀ ≤ y.1
      · rw [coordTranspose_sCut_ker_eq hs₀ (vQ ε) (dQ ε) κ x hy,
          coordTranspose_vQ_reflect hker.1 x y]
        have hpsi : (molN psi0 n (x - y) : ℂ) =
            ((2 * (x.1 - y.1) * cpd 0 κ (x - y) +
              (x.2.2 - y.2.2) * cpd 2 κ (x - y) + 3 * κ (x - y) : ℝ) : ℂ) := by
          exact_mod_cast (molN_psi0_eq n (x - y)).symm
        rw [hpsi]
        push_cast
        ring
      · have hu0 : u y = 0 := by simp [u, hb_cut y (Or.inl (not_le.mp hy))]
        simp [hu0]
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_const_mul]
    simp [convK]
  have heq := hsub_int.trans hrhs_eq
  linear_combination heq

/-! ## 4. Proof of `divMollApprox_bgp` and `divApproxW_bgp` -/

private theorem isKer_molN_psi0 (n : ℕ) : IsKer (molN psi0 n) := by
  have hp := isKer_psi0
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  exact ⟨contDiff_const.mul (hp.1.comp (contDiff_const_smul _)),
    (hp.2.comp_smul hpos.ne').mul_left⟩

/-- **`DivMollApprox` specialized to `r = bgp`** (collision-free). -/
theorem divMollApprox_bgp :
    ∀ (c ε : ℝ) (b Qb Eb : CProf), 0 < c → 0 < ε → DivDataSE c bgp ε b Qb Eb →
      ∀ δ : ℝ, 0 < δ → ∃ b' Qb' Eb' : CProf, NiceProf c b' ∧ DivData c bgp ε b' Qb' Eb' ∧
        DivClose c bgp b Qb Eb b' Qb' Eb' δ := by
  intro c ε b Qb Eb hc hε hSE δ hδ
  obtain ⟨⟨hd, s₀, s₁_raw, hs₀, hb_sraw, hQ_sraw, hE_sraw⟩, L_raw, hb_Lraw, hQ_Lraw, hE_Lraw⟩ := hSE
  set s₁ : ℝ := max s₀ s₁_raw
  set L : ℝ := max 1 L_raw
  have hs₀₁ : s₀ ≤ s₁ := le_max_left _ _
  have hL_pos : 0 < L := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hb_s : SCut s₀ s₁ b := fun x hx =>
    hb_sraw x (hx.imp id fun h => lt_of_le_of_lt (le_max_right _ _) h)
  have hQ_s : SCut s₀ s₁ Qb := fun x hx =>
    hQ_sraw x (hx.imp id fun h => lt_of_le_of_lt (le_max_right _ _) h)
  have hE_s : SCut s₀ s₁ Eb := fun x hx =>
    hE_sraw x (hx.imp id fun h => lt_of_le_of_lt (le_max_right _ _) h)
  have hb_L : EtaCut L b := fun x hx => hb_Lraw x (lt_of_le_of_lt (le_max_right _ _) hx)
  have hQ_L : EtaCut L Qb := fun x hx => hQ_Lraw x (lt_of_le_of_lt (le_max_right _ _) hx)
  have hE_L : EtaCut L Eb := fun x hx => hE_Lraw x (lt_of_le_of_lt (le_max_right _ _) hx)
  have hinQb : InHr c bgp Qb := inHr_of_sqrtS_sCut hs₀ hQ_s hd.inQ
  have hinEb : InHr c bgp Eb := inHr_of_sqrtS_sCut hs₀ hE_s hd.inE
  have cyl_b := fun i : Fin 2 => cylData_of_inHr_sCut hc hs₀ hs₀₁ hd.inHr hb_s i
  have cyl_Q := fun i : Fin 2 => cylData_of_inHr_sCut hc hs₀ hs₀₁ hinQb hQ_s i
  have cyl_E := fun i : Fin 2 => cylData_of_inHr_sCut hc hs₀ hs₀₁ hinEb hE_s i
  have hbgp1 : (1 : ℝ) < bgp := by norm_num [bgp]
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal bgp := by rw [ENNReal.one_le_ofReal]; norm_num [bgp]
  have hac := mollApprox_cylMeas_ac c
  -- Enlarged window parameters
  set δ_r : ℝ := min (s₀ / 2) 1
  have hδ_r : 0 < δ_r := lt_min (half_pos hs₀) one_pos
  set a : ℝ := s₀ - δ_r
  set B : ℝ := s₁ + δ_r
  set L' : ℝ := L + δ_r
  have ha : 0 < a := by
    have : δ_r ≤ s₀ / 2 := min_le_left _ _
    linarith
  have haB : a ≤ B := by linarith
  -- Cylindrical approximate-identity convergence of all components
  have hρ := mollExists_base_isMollifier
  have hρn := fun n : ℕ => mollExists_molN_isMollifier mollExistsRho hρ n
  have tb := fun i : Fin 2 =>
    mollApprox_proof c bgp hc hbgp1 mollExistsRho hρ hρn _ (cyl_b i).1 (cyl_b i).2.1 (cyl_b i).2.2.1
  have tQ := fun i : Fin 2 =>
    mollApprox_proof c bgp hc hbgp1 mollExistsRho hρ hρn _ (cyl_Q i).1 (cyl_Q i).2.1 (cyl_Q i).2.2.1
  have tE := fun i : Fin 2 =>
    mollApprox_proof c bgp hc hbgp1 mollExistsRho hρ hρn _ (cyl_E i).1 (cyl_E i).2.1 (cyl_E i).2.2.1
  have tPsi := fun i : Fin 2 =>
    tendsto_convK_molN_psi0_zero hc hbgp1 (cyl_b i).1 (cyl_b i).2.1 (cyl_b i).2.2.1
  -- Support helper on `[s₀, s₁] × ℝ × [-L, L]`
  have win_f : ∀ {F : CProf}, SCut s₀ s₁ F → EtaCut L F → ∀ (i : Fin 2) (y : Coord),
      (y.1 < s₀ ∨ s₁ < y.1 ∨ L < |y.2.2|) → F y i = 0 := by
    intro F hs hη i y hy
    rcases hy with h1 | h2 | h3
    · simp [hs y (Or.inl h1)]
    · simp [hs y (Or.inr h2)]
    · simp [hη y h3]
  -- Eventual radius condition `2 / (n + 1) ≤ δ_r`
  have hev_rad : ∀ᶠ n : ℕ in atTop, 2 / ((n : ℝ) + 1) ≤ δ_r := by
    have ht : Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using
        (tendsto_const_nhds (x := (2 : ℝ))).mul
          (tendsto_inv_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1))
    exact (ht.eventually (gt_mem_nhds hδ_r)).mono fun n hn => hn.le
  -- Set up candidate sequence `(bn n, Qbn n, Ebn n)`
  set bn : ℕ → CProf := fun n => mollVec n b
  set Qbn : ℕ → CProf := fun n => classOp (vQ ε) (dQ ε) (bn n)
  set Ebn : ℕ → CProf := fun n => classOp vEta dZero (bn n)
  have hEbn_eq : ∀ (n : ℕ) (x : Coord) (i : Fin 2),
      Ebn n x i = convK (molN mollExistsRho n) (fun y => Eb y i) x :=
    fun n x i => classOp_vEta_mollVec_eq hs₀ n hb_s hE_s (fun j => (cyl_b j).1)
      (fun j => (cyl_b j).2.2.2) hd.weakE x i
  have hQbn_eq : ∀ (n : ℕ) (x : Coord) (i : Fin 2),
      Qbn n x i = convK (molN mollExistsRho n) (fun y => Qb y i) x -
        (ε : ℂ) * convK (molN psi0 n) (fun y => b y i) x :=
    fun n x i => classOp_vQ_mollVec_eq hs₀ n hb_s hQ_s (fun j => (cyl_b j).1)
      (fun j => (cyl_b j).2.2.2) hd.weakQ x i
  -- Convergence of `hNorm (bn n - b)`, `hNorm (sqrtS (Ebn n - Eb))`, `hNorm (sqrtS (Qbn n - Qb))`
  set Cw : ℝ≥0∞ := (ENNReal.ofReal (a ^ (bgp / 2 - 5 / 2))) ^ (1 / bgp)
  have hCw_ne : Cw ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num [bgp]) ENNReal.ofReal_ne_top
  have htb_sum : Tendsto (fun n : ℕ =>
      Cw * (cylNorm c bgp (fun x => bn n x 0 - b x 0) +
        cylNorm c bgp (fun x => bn n x 1 - b x 1))) atTop (𝓝 0) := by
    have hsum : Tendsto (fun n : ℕ =>
        cylNorm c bgp (fun x => convK (molN mollExistsRho n) (fun y => b y 0) x - b x 0) +
          cylNorm c bgp (fun x => convK (molN mollExistsRho n) (fun y => b y 1) x - b x 1))
        atTop (𝓝 (0 + 0)) := (tb 0).add (tb 1)
    rw [add_zero] at hsum
    simpa [bn, mollVec] using ENNReal.Tendsto.const_mul hsum (Or.inr hCw_ne)
  have htE_sum : Tendsto (fun n : ℕ =>
      ENNReal.ofReal (Real.sqrt B) * (Cw *
        (cylNorm c bgp (fun x => Ebn n x 0 - Eb x 0) +
          cylNorm c bgp (fun x => Ebn n x 1 - Eb x 1)))) atTop (𝓝 0) := by
    have hsum : Tendsto (fun n : ℕ =>
        cylNorm c bgp (fun x => convK (molN mollExistsRho n) (fun y => Eb y 0) x - Eb x 0) +
          cylNorm c bgp (fun x => convK (molN mollExistsRho n) (fun y => Eb y 1) x - Eb x 1))
        atTop (𝓝 (0 + 0)) := (tE 0).add (tE 1)
    rw [add_zero] at hsum
    have h1 := ENNReal.Tendsto.const_mul hsum (Or.inr hCw_ne)
    have h2 := ENNReal.Tendsto.const_mul h1 (Or.inr (ENNReal.ofReal_ne_top (r := Real.sqrt B)))
    simpa [hEbn_eq] using h2
  have htQ_i : ∀ i : Fin 2,
      Tendsto (fun n : ℕ => cylNorm c bgp (fun x => Qbn n x i - Qb x i)) atTop (𝓝 0) := by
    intro i
    have hbound : ∀ n : ℕ, cylNorm c bgp (fun x => Qbn n x i - Qb x i) ≤
        cylNorm c bgp (fun x => convK (molN mollExistsRho n) (fun y => Qb y i) x - Qb x i) +
          ENNReal.ofReal ε * cylNorm c bgp (convK (molN psi0 n) (fun y => b y i)) := by
      intro n
      have hsplit : (fun x => Qbn n x i - Qb x i) =
          (fun x => convK (molN mollExistsRho n) (fun y => Qb y i) x - Qb x i) +
            (-((ε : ℂ) • convK (molN psi0 n) (fun y => b y i))) := by
        funext x
        simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, hQbn_eq n x i]
        ring
      have hm1 : AEStronglyMeasurable
          (fun x => convK (molN mollExistsRho n) (fun y => Qb y i) x - Qb x i) (cylMeas c) :=
        ((mollConvNice_proof c _ _ (hρn n).1 (cyl_Q i).1
          (cyl_Q i).2.2.2).1.continuous.aestronglyMeasurable).sub ((cyl_Q i).2.1.mono_ac hac)
      have hm2 : AEStronglyMeasurable
          (convK (molN psi0 n) (fun y => b y i)) (cylMeas c) :=
        (mollConvNice_proof c _ _ (isKer_molN_psi0 n) (cyl_b i).1
          (cyl_b i).2.2.2).1.continuous.aestronglyMeasurable
      unfold cylNorm
      rw [hsplit]
      refine (eLpNorm_add_le hm1 ((hm2.const_smul (ε : ℂ)).neg) hp1).trans ?_
      rw [eLpNorm_neg, eLpNorm_const_smul]
      have hεn : ‖(ε : ℂ)‖ₑ = ENNReal.ofReal ε := by
        rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hε.le]
      rw [hεn]
    have hlim : Tendsto (fun n : ℕ =>
        cylNorm c bgp (fun x => convK (molN mollExistsRho n) (fun y => Qb y i) x - Qb x i) +
          ENNReal.ofReal ε * cylNorm c bgp (convK (molN psi0 n) (fun y => b y i)))
        atTop (𝓝 0) := by
      have hp_lim : Tendsto (fun n : ℕ =>
          ENNReal.ofReal ε * cylNorm c bgp (convK (molN psi0 n) (fun y => b y i)))
          atTop (𝓝 0) := by
        simpa using ENNReal.Tendsto.const_mul (tPsi i) (Or.inr ENNReal.ofReal_ne_top)
      simpa using (tQ i).add hp_lim
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => bot_le) hbound
  have htQ_sum : Tendsto (fun n : ℕ =>
      ENNReal.ofReal (Real.sqrt B) * (Cw *
        (cylNorm c bgp (fun x => Qbn n x 0 - Qb x 0) +
          cylNorm c bgp (fun x => Qbn n x 1 - Qb x 1)))) atTop (𝓝 0) := by
    have hsum : Tendsto (fun n : ℕ =>
        cylNorm c bgp (fun x => Qbn n x 0 - Qb x 0) +
          cylNorm c bgp (fun x => Qbn n x 1 - Qb x 1)) atTop (𝓝 (0 + 0)) :=
      (htQ_i 0).add (htQ_i 1)
    rw [add_zero] at hsum
    have h1 := ENNReal.Tendsto.const_mul hsum (Or.inr hCw_ne)
    simpa using ENNReal.Tendsto.const_mul h1 (Or.inr (ENNReal.ofReal_ne_top (r := Real.sqrt B)))
  have hδ' : (0 : ℝ≥0∞) < ENNReal.ofReal δ := ENNReal.ofReal_pos.mpr hδ
  obtain ⟨n, ⟨⟨hn_rad, hnb⟩, hnE⟩, hnQ⟩ :=
    ((((hev_rad.and (htb_sum.eventually (gt_mem_nhds hδ'))).and
      (htE_sum.eventually (gt_mem_nhds hδ'))).and
      (htQ_sum.eventually (gt_mem_nhds hδ')))).exists
  -- Verify `NiceProf c (bn n)`, `DivData c bgp ε (bn n) (Qbn n) (Ebn n)`, and `DivClose`
  obtain ⟨hbn_sm, hbn_per⟩ := contDiff_mollVec n (fun i => (cyl_b i).1) (fun i => (cyl_b i).2.2.2)
  have hbn_win : ∀ x : Coord, (x.1 < a ∨ B < x.1 ∨ L' < |x.2.2|) → bn n x = 0 := by
    intro x hx; ext i
    exact convK_molN_zero_off_window (fun _ hw => mollExistsRho_zero_of_two_le hw) hδ_r hn_rad
      (win_f hb_s hb_L i) hx
  have hEbn_win : SCut a B (Ebn n) := by
    intro x hx; ext i; rw [hEbn_eq n x i]
    exact convK_molN_zero_off_window (fun _ hw => mollExistsRho_zero_of_two_le hw) hδ_r hn_rad
      (win_f hE_s hE_L i) (hx.imp id Or.inl)
  have hQbn_win : SCut a B (Qbn n) := by
    intro x hx; ext i; rw [hQbn_eq n x i]
    have z1 := convK_molN_zero_off_window (fun _ hw => mollExistsRho_zero_of_two_le hw) hδ_r hn_rad
      (win_f hQ_s hQ_L i) (hx.imp id Or.inl)
    have z2 := convK_molN_zero_off_window (fun _ hw => psi0_zero_of_two_le hw) hδ_r hn_rad
      (win_f hb_s hb_L i) (hx.imp id Or.inl)
    simp [z1, z2]
  have hnice : NiceProf c (bn n) := ⟨hbn_sm, hbn_per, a, B, L', ha, hbn_win⟩
  have hvQ_sm : ∀ j : Fin 3, ContDiff ℝ ∞ (fun x : Coord => vQ ε x j) := by
    intro j; fin_cases j <;> simp [vQ] <;> fun_prop
  have hvEta_sm : ∀ j : Fin 3, ContDiff ℝ ∞ (fun x : Coord => vEta x j) := by
    intro j; fin_cases j <;> simp [vEta] <;> fun_prop
  have hwQ : HasWeakVec (vQ ε) (dQ ε) (bn n) (Qbn n) :=
    weakOfSmooth_proof (vQ ε) (dQ ε) (bn n) hvQ_sm contDiff_const hbn_sm
  have hwE : HasWeakVec vEta dZero (bn n) (Ebn n) :=
    weakOfSmooth_proof vEta dZero (bn n) hvEta_sm contDiff_const hbn_sm
  -- Close bounds on `[a, B]` (`b, Qb, Eb` also satisfy `SCut a B` since `a ≤ s₀` and `s₁ ≤ B`)
  have hb_aB : SCut a B b := fun x hx =>
    hb_s x (hx.imp (fun h => lt_of_lt_of_le h (by linarith)) (fun h => lt_of_le_of_lt (by linarith) h))
  have hQ_aB : SCut a B Qb := fun x hx =>
    hQ_s x (hx.imp (fun h => lt_of_lt_of_le h (by linarith)) (fun h => lt_of_le_of_lt (by linarith) h))
  have hE_aB : SCut a B Eb := fun x hx =>
    hE_s x (hx.imp (fun h => lt_of_lt_of_le h (by linarith)) (fun h => lt_of_le_of_lt (by linarith) h))
  have hbn_aB : SCut a B (bn n) := fun x hx => hbn_win x (hx.imp id Or.inl)
  have hdiff_b_aB : SCut a B (fun x => bn n x - b x) := fun x hx => by
    simp [hbn_aB x hx, hb_aB x hx]
  have hdiff_E_aB : SCut a B (fun x => Ebn n x - Eb x) := fun x hx => by
    simp [hEbn_win x hx, hE_aB x hx]
  have hdiff_Q_aB : SCut a B (fun x => Qbn n x - Qb x) := fun x hx => by
    simp [hQbn_win x hx, hQ_aB x hx]
  have hbn_cm : ∀ i : Fin 2, AEStronglyMeasurable (fun x => bn n x i) (cylMeas c) := fun i =>
    (mollConvNice_proof c _ _ (hρn n).1 (cyl_b i).1 (cyl_b i).2.2.2).1.continuous.aestronglyMeasurable
  have hEbn_cm : ∀ i : Fin 2, AEStronglyMeasurable (fun x => Ebn n x i) (cylMeas c) := fun i => by
    have heq : (fun x => Ebn n x i) = convK (molN mollExistsRho n) (fun y => Eb y i) :=
      funext fun x => hEbn_eq n x i
    rw [heq]
    exact (mollConvNice_proof c _ _ (hρn n).1 (cyl_E i).1
      (cyl_E i).2.2.2).1.continuous.aestronglyMeasurable
  have hQbn_cm : ∀ i : Fin 2, AEStronglyMeasurable (fun x => Qbn n x i) (cylMeas c) := fun i => by
    have heq : (fun x => Qbn n x i) = fun x =>
        convK (molN mollExistsRho n) (fun y => Qb y i) x -
          (ε : ℂ) * convK (molN psi0 n) (fun y => b y i) x :=
      funext fun x => hQbn_eq n x i
    rw [heq]
    exact ((mollConvNice_proof c _ _ (hρn n).1 (cyl_Q i).1
      (cyl_Q i).2.2.2).1.continuous.aestronglyMeasurable).sub
      (((mollConvNice_proof c _ _ (isKer_molN_psi0 n) (cyl_b i).1
        (cyl_b i).2.2.2).1.continuous.aestronglyMeasurable).const_smul (ε : ℂ))
  have hclose_b : hNorm c bgp (fun x => bn n x - b x) < ENNReal.ofReal δ :=
    lt_of_le_of_lt
      (hNorm_le_cylNorm_sum_of_sCut ha hdiff_b_aB
        ((hbn_cm 0).sub ((cyl_b 0).2.1.mono_ac hac))
        ((hbn_cm 1).sub ((cyl_b 1).2.1.mono_ac hac)))
      hnb
  have hclose_E : hNorm c bgp (sqrtS fun x => Ebn n x - Eb x) < ENNReal.ofReal δ := by
    refine lt_of_le_of_lt
      ((hNorm_sqrtS_le_of_sCut ha haB hdiff_E_aB).trans
        (mul_le_mul_of_nonneg_left
          (hNorm_le_cylNorm_sum_of_sCut ha hdiff_E_aB
            ((hEbn_cm 0).sub ((cyl_E 0).2.1.mono_ac hac))
            ((hEbn_cm 1).sub ((cyl_E 1).2.1.mono_ac hac))) bot_le))
      hnE
  have hclose_Q : hNorm c bgp (sqrtS fun x => Qbn n x - Qb x) < ENNReal.ofReal δ := by
    refine lt_of_le_of_lt
      ((hNorm_sqrtS_le_of_sCut ha haB hdiff_Q_aB).trans
        (mul_le_mul_of_nonneg_left
          (hNorm_le_cylNorm_sum_of_sCut ha hdiff_Q_aB
            ((hQbn_cm 0).sub ((cyl_Q 0).2.1.mono_ac hac))
            ((hQbn_cm 1).sub ((cyl_Q 1).2.1.mono_ac hac))) bot_le))
      hnQ
  -- `InHr` of `bn n`, `sqrtS (Qbn n)`, `sqrtS (Ebn n)` via triangle inequality from `b, Qb, Eb`
  have hin_bn : InHr c bgp (bn n) := by
    refine ⟨Eventually.of_forall hbn_per, hbn_sm.continuous.aestronglyMeasurable, ?_⟩
    have heq : bn n = (fun x => bn n x - b x) + b := by funext x; simp
    unfold hNorm; rw [heq]
    exact lt_of_le_of_lt
      (eLpNorm_add_le (hbn_sm.continuous.aestronglyMeasurable.sub hd.inHr.meas) hd.inHr.meas hp1)
      (ENNReal.add_lt_top.mpr ⟨lt_trans hclose_b ENNReal.ofReal_lt_top, hd.inHr.finite⟩)
  have hEbn_cont : Continuous (Ebn n) := by
    refine (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℂ)).symm.continuous.comp
      (continuous_pi fun i => ?_)
    have heq : (fun x => Ebn n x i) = convK (molN mollExistsRho n) (fun y => Eb y i) :=
      funext fun x => hEbn_eq n x i
    change Continuous (fun x => Ebn n x i)
    rw [heq]
    exact (mollConvNice_proof c _ _ (hρn n).1 (cyl_E i).1 (cyl_E i).2.2.2).1.continuous
  have hEbn_per : ∀ x : Coord, Ebn n (qShift c x) = Ebn n x := by
    intro x; ext i; rw [hEbn_eq n (qShift c x) i, hEbn_eq n x i]
    exact (mollConvNice_proof c _ _ (hρn n).1 (cyl_E i).1 (cyl_E i).2.2.2).2 x
  have hin_Ebn : InHr c bgp (sqrtS (Ebn n)) := by
    have hs_cont : Continuous (sqrtS (Ebn n)) :=
      (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp continuous_fst)).smul hEbn_cont
    refine ⟨Eventually.of_forall fun x => by
        dsimp only [sqrtS]; rw [show (qShift c x).1 = x.1 from rfl, hEbn_per x],
      hs_cont.aestronglyMeasurable, ?_⟩
    have hm_sub : AEStronglyMeasurable (sqrtS fun x => Ebn n x - Eb x) (hMeas c bgp) := by
      rw [sqrtS_sub]; exact hs_cont.aestronglyMeasurable.sub hd.inE.meas
    have heq : sqrtS (Ebn n) = (sqrtS fun x => Ebn n x - Eb x) + sqrtS Eb := by
      funext x; simp [sqrtS, smul_sub]
    unfold hNorm; rw [heq]
    exact lt_of_le_of_lt
      (eLpNorm_add_le hm_sub hd.inE.meas hp1)
      (ENNReal.add_lt_top.mpr ⟨lt_trans hclose_E ENNReal.ofReal_lt_top, hd.inE.finite⟩)
  have hQbn_cont : Continuous (Qbn n) := by
    refine (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℂ)).symm.continuous.comp
      (continuous_pi fun i => ?_)
    have heq : (fun x => Qbn n x i) = fun x =>
        convK (molN mollExistsRho n) (fun y => Qb y i) x -
          (ε : ℂ) * convK (molN psi0 n) (fun y => b y i) x :=
      funext fun x => hQbn_eq n x i
    change Continuous (fun x => Qbn n x i)
    rw [heq]
    exact ((mollConvNice_proof c _ _ (hρn n).1 (cyl_Q i).1 (cyl_Q i).2.2.2).1.continuous).sub
      (continuous_const.mul
        (mollConvNice_proof c _ _ (isKer_molN_psi0 n) (cyl_b i).1 (cyl_b i).2.2.2).1.continuous)
  have hQbn_per : ∀ x : Coord, Qbn n (qShift c x) = Qbn n x := by
    intro x; ext i; rw [hQbn_eq n (qShift c x) i, hQbn_eq n x i]
    rw [(mollConvNice_proof c _ _ (hρn n).1 (cyl_Q i).1 (cyl_Q i).2.2.2).2 x,
      (mollConvNice_proof c _ _ (isKer_molN_psi0 n) (cyl_b i).1 (cyl_b i).2.2.2).2 x]
  have hin_Qbn : InHr c bgp (sqrtS (Qbn n)) := by
    have hs_cont : Continuous (sqrtS (Qbn n)) :=
      (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp continuous_fst)).smul hQbn_cont
    refine ⟨Eventually.of_forall fun x => by
        dsimp only [sqrtS]; rw [show (qShift c x).1 = x.1 from rfl, hQbn_per x],
      hs_cont.aestronglyMeasurable, ?_⟩
    have hm_sub : AEStronglyMeasurable (sqrtS fun x => Qbn n x - Qb x) (hMeas c bgp) := by
      rw [sqrtS_sub]; exact hs_cont.aestronglyMeasurable.sub hd.inQ.meas
    have heq : sqrtS (Qbn n) = (sqrtS fun x => Qbn n x - Qb x) + sqrtS Qb := by
      funext x; simp [sqrtS, smul_sub]
    unfold hNorm; rw [heq]
    exact lt_of_le_of_lt
      (eLpNorm_add_le hm_sub hd.inQ.meas hp1)
      (ENNReal.add_lt_top.mpr ⟨lt_trans hclose_Q ENNReal.ofReal_lt_top, hd.inQ.finite⟩)
  exact ⟨bn n, Qbn n, Ebn n, hnice, ⟨hin_bn, hwQ, hwE, hin_Qbn, hin_Ebn⟩,
    hclose_b, hclose_Q, hclose_E⟩

/-- **`DivApproxW` at `r = bgp`** assembled from `divSCutApproxW_proof`, `divEtaCutApprox_proof`,
and `divMollApprox_bgp`. -/
theorem divApproxW_bgp (c ε : ℝ) (b Qb Eb : CProf) (hc : 0 < c) (hε : 0 < ε)
    (hp : DivData c bgp ε b Qb Eb) :
    ∃ bn Qbn Ebn : ℕ → CProf, (∀ n, NiceProf c (bn n) ∧ DivData c bgp ε (bn n) (Qbn n) (Ebn n)) ∧
      ∀ n : ℕ, DivCloseW c bgp b Qb Eb (bn n) (Qbn n) (Ebn n) (1 / ((n : ℝ) + 1)) := by
  have hr2 : (2 : ℝ) < bgp := by norm_num [bgp]
  have hr1 : (1 : ℝ) < bgp := by norm_num [bgp]
  have key : ∀ n : ℕ, ∃ b' Qb' Eb' : CProf, NiceProf c b' ∧ DivData c bgp ε b' Qb' Eb' ∧
      DivCloseW c bgp b Qb Eb b' Qb' Eb' (1 / ((n : ℝ) + 1)) := by
    intro n
    have hδ3 : (0 : ℝ) < 1 / ((n : ℝ) + 1) / 3 := by positivity
    obtain ⟨b1, Q1, E1, hp1, hc1⟩ := divSCutApproxW_proof c bgp ε b Qb Eb hc hε hr2 hp _ hδ3
    obtain ⟨b2, Q2, E2, hp2, hc2⟩ := divEtaCutApprox_proof c bgp ε b1 Q1 E1 hc hε hr2 hp1 _ hδ3
    obtain ⟨b3, Q3, E3, hn3, hp3, hc3⟩ := divMollApprox_bgp c ε b2 Q2 E2 hc hε hp2 _ hδ3
    refine ⟨b3, Q3, E3, hn3, hp3, ?_⟩
    have c12 := divCloseW_trans_close hr1 hδ3.le hδ3.le hp hp1.1 hp2.1.1 hc1 hc2
    have c123 := divCloseW_trans_close hr1 (by positivity) hδ3.le hp hp2.1.1 hp3 c12 hc3
    have e : 1 / ((n : ℝ) + 1) / 3 + 1 / ((n : ℝ) + 1) / 3 + 1 / ((n : ℝ) + 1) / 3 =
        1 / ((n : ℝ) + 1) := by ring
    rwa [e] at c123
  choose bn Qn En hn hp' hcl using key
  exact ⟨bn, Qn, En, fun n => ⟨hn n, hp' n⟩, hcl⟩

end UnforcedLeray.Short.IIb.PhysKOutCandMoll

end
