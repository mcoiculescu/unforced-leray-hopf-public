import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.BodyFlatLocalH1.FlatBodyFirstOrderLocal.GradBound
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.CellPtHT

/-!
# Spatial cut representatives and `(q, η)` integration by parts (`PartII-a:N05/2/1`)

Source of record: `the November 2 reference manuscript`,
lines 1684–1689, 1794–1799.

Constructs the box-supported `c`-periodic spatial derivative representatives
`dq = flatCutSpatialDeriv c χ W Gr 0` and `deta = flatCutSpatialDeriv c χ W Gr 1`
in `L²(cellMeasure c)` and proves their `L²(cellMeasure c)` bounds and `(q, η)` integration-by-parts
identities against `IsMeridTest c φ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff ComplexConjugate InnerProductSpace

namespace UnforcedLeray.Short.PartIIa.N05_2_1Aux

open UnforcedLeray.Axi
open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226
open UnforcedLeray.Short.PartIIIb.Concrete (Chart)
open UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
  (IsEnergyFieldAE volCyl_ac_ageμ fderiv_clm_comp')
open UnforcedLeray.Short.PartIIIb.NearInst (cellPt)
open UnforcedLeray.Short.PartIIIb.NearInst.Delta (velF)
open UnforcedLeray.Short.PartIIIb.NearInst.Masked (cellPtInv measurable_cellPtInv cpcHT_eq)
open UnforcedLeray.Short.IIIa (tnorm2 tCalNorm HasWeakCellDerivC)
open N05_2Aux N05_4Aux

/-! ### 1. Cutoff derivative bounds and `flatCutSpatialDeriv` in `L²(cellMeasure c)` -/

theorem ae_cell_cellMeasure (c : ℝ) : ∀ᵐ p ∂(cellMeasure c), p ∈ cell c :=
  ae_restrict_mem (measurableSet_cell c)

theorem fderiv_periodic_of_nearCutoff {c σ H1 L1 : ℝ} {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) (p : Profile) :
    fderiv ℝ χ (p.1, p.2.1 + c, p.2.2) = fderiv ℝ χ p := by
  have hshift : (fun q : Profile => χ (q + (0, c, 0))) = χ := by
    funext ⟨s, q, η⟩
    simpa [Prod.ext_iff] using hχ.periodic (s, q, η)
  have hcomp : fderiv ℝ (fun q : Profile => χ (q + (0, c, 0))) p =
      fderiv ℝ χ (p + (0, c, 0)) := fderiv_comp_add_right (0, c, 0)
  rw [hshift] at hcomp
  have hp : p + (0, c, 0) = (p.1, p.2.1 + c, p.2.2) := by
    rcases p with ⟨s, q, η⟩
    simp
  rw [← hp, hcomp]

theorem fderiv_support_of_nearCutoff {c σ H1 L1 : ℝ} {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) (p : Profile) (hp : fderiv ℝ χ p ≠ 0) :
    σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1 := by
  have hclosed : IsClosed {q : Profile | σ ≤ q.1 ∧ q.1 ≤ H1 ∧ |q.2.2| ≤ L1} := by
    refine (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_fst continuous_const).inter ?_)
    exact isClosed_le (continuous_abs.comp (continuous_snd.comp continuous_snd)) continuous_const
  have hsub : tsupport χ ⊆ {q : Profile | σ ≤ q.1 ∧ q.1 ≤ H1 ∧ |q.2.2| ≤ L1} :=
    closure_minimal (fun q hq => hχ.support q hq) hclosed
  exact hsub (support_fderiv_subset ℝ hp)

theorem norm_fderiv_le_cNorm8_of_nearCutoff {c σ H1 L1 : ℝ} (hc : 0 < c) {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) (p : Profile) :
    ‖fderiv ℝ χ p‖ ≤ cNorm8 χ := by
  have hcont : Continuous (fun q => ‖iteratedFDeriv ℝ 1 χ q‖) :=
    (hχ.smooth.continuous_iteratedFDeriv (by decide : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))).norm
  let K : Set Profile := Icc σ H1 ×ˢ (Icc 0 c ×ˢ Icc (-L1) L1)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨C1, hC1⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  have hbdd : BddAbove (range fun q => ‖iteratedFDeriv ℝ 1 χ q‖) := by
    refine ⟨max C1 0, ?_⟩
    rintro _ ⟨q, rfl⟩
    dsimp only
    rw [norm_iteratedFDeriv_one]
    let q' : Profile := (q.1, reduceIoc c q.2.1, q.2.2)
    have hpeq : fderiv ℝ χ q' = fderiv ℝ χ q :=
      periodic_reduceIoc_eq (fderiv ℝ χ) (fderiv_periodic_of_nearCutoff hχ) q.1 q.2.1 q.2.2
    rw [← hpeq]
    by_cases h0 : fderiv ℝ χ q' = 0
    · simp [h0]
    · obtain ⟨hs1, hs2, hη⟩ := fderiv_support_of_nearCutoff hχ q' h0
      have hq' : q' ∈ K := ⟨⟨hs1, hs2⟩, Ioc_subset_Icc_self (reduceIoc_mem hc q.2.1), abs_le.1 hη⟩
      have hle : ‖fderiv ℝ χ q'‖ ≤ C1 := by simpa using hC1 q' hq'
      exact hle.trans (le_max_left C1 0)
  rw [← norm_iteratedFDeriv_one]
  calc ‖iteratedFDeriv ℝ 1 χ p‖
      ≤ ⨆ q, ‖iteratedFDeriv ℝ 1 χ q‖ := le_ciSup hbdd p
    _ ≤ ∑ k ∈ Finset.range 9, ⨆ q, ‖iteratedFDeriv ℝ k χ q‖ :=
        Finset.single_le_sum (fun k _ => Real.iSup_nonneg fun _ => norm_nonneg _)
          (Finset.mem_range.2 (by omega))
    _ = cNorm8 χ := rfl

theorem isNearCutoff_fderiv_apply {c σ H1 L1 : ℝ} {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) (v : Profile) :
    IsNearCutoff c σ H1 L1 (fun p => fderiv ℝ χ p v) where
  smooth := (ContinuousLinearMap.apply ℝ ℝ v).contDiff.comp
    (hχ.smooth.fderiv_right (by decide))
  periodic p := by
    dsimp only
    rw [fderiv_periodic_of_nearCutoff hχ p]
  support p hp :=
    fderiv_support_of_nearCutoff hχ p fun h0 => hp (by simp [h0])

theorem abs_fderiv_apply_le_cNorm8 {c σ H1 L1 : ℝ} (hc : 0 < c) {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) {v : Profile} (hv : ‖v‖ ≤ 1) (p : Profile) :
    |fderiv ℝ χ p v| ≤ cNorm8 χ := by
  rw [← Real.norm_eq_abs]
  calc ‖fderiv ℝ χ p v‖
      ≤ ‖fderiv ℝ χ p‖ * ‖v‖ := (fderiv ℝ χ p).le_opNorm v
    _ ≤ cNorm8 χ * 1 := mul_le_mul (norm_fderiv_le_cNorm8_of_nearCutoff hc hχ p) hv
        (norm_nonneg v) (cNorm8_nonneg χ)
    _ = cNorm8 χ := mul_one _

theorem lintegral_flatStressCutRep_fderiv_sq_le {c σ H1 L1 : ℝ} (hc : 0 < c) (hσ : 0 < σ)
    (hσH : σ ≤ H1) {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ)
    {v : Profile} (hv : ‖v‖ ≤ 1) (W : HSpace c MeridC) :
    ∫⁻ p, ‖flatStressCutRep c (fun q => fderiv ℝ χ q v) W p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) ≤
      ENNReal.ofReal (((1 + H1) * cNorm8 χ * ‖W‖) ^ 2) := by
  let dχ : Profile → ℝ := fun q => fderiv ℝ χ q v
  have hdχ : IsNearCutoff c σ H1 L1 dχ := isNearCutoff_fderiv_apply hχ v
  have hm : Measurable dχ := hdχ.smooth.continuous.measurable
  let u := flatStressCutRep c dχ W
  have hu : Measurable u := measurable_flatStressCutRep c hm W
  have hstep1 : ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) ≤
      ENNReal.ofReal ((1 + H1) ^ 2) * ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(measureH c) := by
    calc ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c)
        ≤ ∫⁻ p, ENNReal.ofReal ((1 + H1) ^ 2) *
            (weightH p * ‖u p‖ₑ ^ (2 : ℝ)) ∂(cellMeasure c) :=
          lintegral_mono (flatStressCutRep_enorm_sq_le hσ hσH hdχ W)
      _ = ENNReal.ofReal ((1 + H1) ^ 2) *
            ∫⁻ p, weightH p * ‖u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) :=
          lintegral_const_mul _ (measurable_weightH.mul (hu.enorm.pow_const (2 : ℝ)))
      _ = ENNReal.ofReal ((1 + H1) ^ 2) * ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(measureH c) := by
          rw [measureH, lintegral_withDensity_eq_lintegral_mul _
            measurable_weightH (hu.enorm.pow_const (2 : ℝ))]
          rfl
  have hB : ∀ p, |dχ p| ≤ cNorm8 χ := abs_fderiv_apply_le_cNorm8 hc hχ hv
  let U₀ := mulChi (measureH c) dχ hm hB W
  have hae : (U₀ : Profile → MeridC) =ᵐ[measureH c] u :=
    flatStressCutRep_ae_eq hc dχ hm hB W
  have hU0_norm : ‖U₀‖ ≤ cNorm8 χ * ‖W‖ := by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [(memLp_chi_smul (measureH c) dχ hm hB (Lp.memLp W)).coeFn_toLp] with p hp
    change ‖((memLp_chi_smul (measureH c) dχ hm hB (Lp.memLp W)).toLp _) p‖ ≤ _
    rw [hp, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hB p) (norm_nonneg _)
  have hstep2 : ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(measureH c) ≤
      ENNReal.ofReal ((cNorm8 χ * ‖W‖) ^ 2) := by
    have hcongr : ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(measureH c) =
        ∫⁻ p, ‖(U₀ : Profile → MeridC) p‖ₑ ^ (2 : ℝ) ∂(measureH c) := by
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with p hp
      rw [hp]
    have hLp : eLpNorm (U₀ : Profile → MeridC) 2 (measureH c) = ENNReal.ofReal ‖U₀‖ := by
      rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top U₀)]
    have hlint : ∫⁻ p, ‖(U₀ : Profile → MeridC) p‖ₑ ^ (2 : ℝ) ∂(measureH c) =
        ENNReal.ofReal (‖U₀‖ ^ 2) := by
      have heq := eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := measureH c)
        (f := (U₀ : Profile → MeridC)) two_ne_zero ENNReal.ofNat_ne_top
      rw [hLp, ENNReal.toReal_ofNat] at heq
      have hpow := congrArg (fun x : ℝ≥0∞ => x ^ (2 : ℝ)) heq.symm
      rw [← ENNReal.rpow_mul, show (1 / (2 : ℝ)) * 2 = 1 by norm_num, ENNReal.rpow_one,
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg U₀) (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_two] at hpow
      exact hpow
    rw [hcongr, hlint]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg U₀) hU0_norm 2)
  calc ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c)
      ≤ ENNReal.ofReal ((1 + H1) ^ 2) * ENNReal.ofReal ((cNorm8 χ * ‖W‖) ^ 2) :=
        hstep1.trans (by gcongr)
    _ = ENNReal.ofReal (((1 + H1) * cNorm8 χ * ‖W‖) ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

theorem cellL2Norm_flatStressCutRep_fderiv_le_mul {c σ H1 L1 : ℝ} (hc : 0 < c) (hσ : 0 < σ)
    (hσH : σ ≤ H1) {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ)
    {v : Profile} (hv : ‖v‖ ≤ 1) (W : HSpace c MeridC) :
    cellL2Norm c (flatStressCutRep c (fun q => fderiv ℝ χ q v) W) ≤
      (1 + H1) * cNorm8 χ * ‖W‖ := by
  let dχ : Profile → ℝ := fun q => fderiv ℝ χ q v
  have hdχ : IsNearCutoff c σ H1 L1 dχ := isNearCutoff_fderiv_apply hχ v
  have hm : Measurable dχ := hdχ.smooth.continuous.measurable
  let u := flatStressCutRep c dχ W
  have hmem := memLp_flatStressCutRep hc hσ hσH hdχ hm W
  have hint : Integrable (fun p => ‖u p‖ ^ 2) (cellMeasure c) :=
    hmem.integrable_norm_pow two_ne_zero
  have hofReal : ENNReal.ofReal (∫ p, ‖u p‖ ^ 2 ∂(cellMeasure c)) =
      ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => sq_nonneg _)]
    refine lintegral_congr fun p => ?_
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]
  have hH1_pos : 0 < H1 := lt_of_lt_of_le hσ hσH
  have hB0 : 0 ≤ (1 + H1) * cNorm8 χ * ‖W‖ :=
    mul_nonneg (mul_nonneg (by linarith) (cNorm8_nonneg χ)) (norm_nonneg W)
  have hint_le : ∫ p, ‖u p‖ ^ 2 ∂(cellMeasure c) ≤ ((1 + H1) * cNorm8 χ * ‖W‖) ^ 2 := by
    refine (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).1 ?_
    rw [hofReal]
    exact lintegral_flatStressCutRep_fderiv_sq_le hc hσ hσH hχ hv W
  unfold cellL2Norm
  calc (∫ p, ‖u p‖ ^ 2 ∂(cellMeasure c)) ^ (1 / 2 : ℝ)
      ≤ (((1 + H1) * cNorm8 χ * ‖W‖) ^ 2) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (integral_nonneg fun _ => sq_nonneg _) hint_le (by norm_num)
    _ = (1 + H1) * cNorm8 χ * ‖W‖ := by
        rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hB0]

/-- Pullback of the `j`-th column (`j = 0` for `∂_q`, `j = 1` for `∂_η`) of a recentred gradient
`Gr : Chart → Fin 2 → Fin 2 → ℂ` to `Profile`. -/
def flatGradCol (c : ℝ) (Gr : Chart → Fin 2 → Fin 2 → ℂ) (j : Fin 2) (p : Profile) : MeridC :=
  WithLp.toLp 2 (fun i : Fin 2 => Gr (cellPt c p) i j)

/-- Concrete box-supported `c`-periodic representative of `χ • ∂_{q,η} b` on `Profile`. -/
def flatGradCutRep (c : ℝ) (χ : Profile → ℝ) (Gr : Chart → Fin 2 → Fin 2 → ℂ) (j : Fin 2)
    (p : Profile) : MeridC :=
  χ p • periodize c (flatGradCol c Gr j) p

/-- Full Leibniz spatial derivative representative `(∇_{q,η} χ) b + χ Gr` on `Profile`. -/
def flatCutSpatialDeriv (c : ℝ) (χ : Profile → ℝ) (W : HSpace c MeridC)
    (Gr : Chart → Fin 2 → Fin 2 → ℂ) (j : Fin 2) (p : Profile) : MeridC :=
  flatStressCutRep c (if j = 0 then pdQ χ else pdEta χ) W p + flatGradCutRep c χ Gr j p

theorem measurable_flatGradCol (c : ℝ) {Gr : Chart → Fin 2 → Fin 2 → ℂ}
    (hGr : ∀ i j, Measurable (fun x => Gr x i j)) (j : Fin 2) :
    Measurable (flatGradCol c Gr j) := by
  unfold flatGradCol
  refine (WithLp.measurable_toLp 2 (Fin 2 → ℂ)).comp (measurable_pi_iff.2 fun i => ?_)
  exact (hGr i j).comp (UnforcedLeray.Short.PartIIIb.NearInst.Masked.measurable_cellPt c)

theorem measurable_flatGradCutRep (c : ℝ) {χ : Profile → ℝ} (hm : Measurable χ)
    {Gr : Chart → Fin 2 → Fin 2 → ℂ} (hGr : ∀ i j, Measurable (fun x => Gr x i j)) (j : Fin 2) :
    Measurable (flatGradCutRep c χ Gr j) :=
  hm.smul (measurable_periodize_meridC c (measurable_flatGradCol c hGr j))

theorem flatGradCutRep_periodic {c σ H1 L1 : ℝ} (hc : 0 < c) {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) (Gr : Chart → Fin 2 → Fin 2 → ℂ) (j : Fin 2) :
    QPeriodic c (flatGradCutRep c χ Gr j) := by
  intro p
  simp only [flatGradCutRep, hχ.periodic p, qPeriodic_periodize hc (flatGradCol c Gr j) p]

theorem flatGradCutRep_support {c σ H1 L1 : ℝ} {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) (Gr : Chart → Fin 2 → Fin 2 → ℂ) (j : Fin 2) (p : Profile)
    (hp : flatGradCutRep c χ Gr j p ≠ 0) :
    σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1 := by
  refine hχ.support p ?_
  intro h0
  apply hp
  simp [flatGradCutRep, h0]

theorem norm_flatGradCol_le_tnorm2 (c : ℝ) (Gr : Chart → Fin 2 → Fin 2 → ℂ) (j : Fin 2)
    (p : Profile) :
    ‖flatGradCol c Gr j p‖ ≤ tnorm2 (Gr (cellPt c p)) := by
  unfold flatGradCol tnorm2
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  simp only [Fin.sum_univ_two]
  fin_cases j <;> dsimp <;>
    nlinarith [sq_nonneg ‖Gr (cellPt c p) 0 0‖, sq_nonneg ‖Gr (cellPt c p) 0 1‖,
      sq_nonneg ‖Gr (cellPt c p) 1 0‖, sq_nonneg ‖Gr (cellPt c p) 1 1‖]

theorem measurable_tnorm2 {Gr : Chart → Fin 2 → Fin 2 → ℂ}
    (hGr : ∀ i j, Measurable (fun x => Gr x i j)) :
    Measurable (fun x => tnorm2 (Gr x)) := by
  unfold tnorm2
  refine Real.continuous_sqrt.measurable.comp ?_
  exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
    (hGr i j).norm.pow_const 2

theorem lintegral_flatGradCutRep_sq_le {c σ H1 L1 : ℝ} (hc : 0 < c) (hσ : 0 < σ)
    (hσH : σ ≤ H1) {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ) (_hm : Measurable χ)
    {Gr : Chart → Fin 2 → Fin 2 → ℂ} (hGr : ∀ i j, Measurable (fun x => Gr x i j))
    {B_Gr : ℝ} (hB0 : 0 ≤ B_Gr)
    (hCal : ENNReal.ofReal (Real.sqrt c) * tCalNorm c Gr ≤ ENNReal.ofReal B_Gr) (j : Fin 2) :
    ∫⁻ p, ‖flatGradCutRep c χ Gr j p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) ≤
      ENNReal.ofReal (((1 + H1) * cNorm8 χ * B_Gr) ^ 2) := by
  let g := flatGradCutRep c χ Gr j
  have htn_meas : Measurable (fun x => tnorm2 (Gr x)) := measurable_tnorm2 hGr
  have hcell_pt : ∀ᵐ p ∂(cellMeasure c),
      ‖g p‖ₑ ^ (2 : ℝ) ≤
        ENNReal.ofReal (((1 + H1) * cNorm8 χ) ^ 2) *
          (ENNReal.ofReal (p.1 ^ (-(1 / 2 : ℝ))) * ‖tnorm2 (Gr (cellPt c p))‖ₑ ^ (2 : ℝ)) := by
    filter_upwards [ae_cell_cellMeasure c] with p hpcell
    by_cases hp0 : g p = 0
    · simp [hp0]
    · obtain ⟨hs1, hs2, _⟩ := flatGradCutRep_support hχ Gr j p hp0
      have hs_pos : 0 < p.1 := lt_of_lt_of_le hσ hs1
      have hH1_pos : 0 < H1 := lt_of_lt_of_le hσ hσH
      have h1H1 : 1 ≤ 1 + H1 := by linarith
      have hp1H1 : p.1 ≤ 1 + H1 := by linarith
      have hrpow : p.1 ^ (1 / 2 : ℝ) ≤ (1 + H1) ^ 2 := by
        calc p.1 ^ (1 / 2 : ℝ)
            ≤ (1 + H1) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hs_pos.le hp1H1 (by norm_num)
          _ ≤ (1 + H1) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1H1 (by norm_num)
          _ = (1 + H1) ^ 2 := Real.rpow_two (1 + H1)
      have h1 : 1 ≤ (1 + H1) ^ 2 * p.1 ^ (-(1 / 2 : ℝ)) := by
        calc (1 : ℝ)
            = p.1 ^ (1 / 2 : ℝ) * p.1 ^ (-(1 / 2 : ℝ)) := by
              rw [← Real.rpow_add hs_pos]; norm_num
          _ ≤ (1 + H1) ^ 2 * p.1 ^ (-(1 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_right hrpow (Real.rpow_nonneg hs_pos.le _)
      have hgnorm : ‖g p‖ ≤ cNorm8 χ * ‖tnorm2 (Gr (cellPt c p))‖ := by
        dsimp only [g, flatGradCutRep]
        rw [periodize_of_mem hc _ hpcell, norm_smul, Real.norm_eq_abs,
          Real.norm_of_nonneg (by unfold tnorm2; exact Real.sqrt_nonneg _)]
        exact mul_le_mul (abs_le_cNorm8_of_nearCutoff hc hχ p)
          (norm_flatGradCol_le_tnorm2 c Gr j p) (norm_nonneg _) (cNorm8_nonneg χ)
      have hgsq : ‖g p‖ ^ 2 ≤ ((1 + H1) * cNorm8 χ) ^ 2 *
          (p.1 ^ (-(1 / 2 : ℝ)) * ‖tnorm2 (Gr (cellPt c p))‖ ^ 2) := by
        calc ‖g p‖ ^ 2
            ≤ (cNorm8 χ * ‖tnorm2 (Gr (cellPt c p))‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) hgnorm 2
          _ = 1 * (cNorm8 χ ^ 2 * ‖tnorm2 (Gr (cellPt c p))‖ ^ 2) := by ring
          _ ≤ ((1 + H1) ^ 2 * p.1 ^ (-(1 / 2 : ℝ))) *
                (cNorm8 χ ^ 2 * ‖tnorm2 (Gr (cellPt c p))‖ ^ 2) :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
          _ = ((1 + H1) * cNorm8 χ) ^ 2 *
                (p.1 ^ (-(1 / 2 : ℝ)) * ‖tnorm2 (Gr (cellPt c p))‖ ^ 2) := by ring
      have hLHS : ‖g p‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖g p‖ ^ 2) := by
        rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
          Real.rpow_two]
      have hRHS : ENNReal.ofReal (((1 + H1) * cNorm8 χ) ^ 2) *
            (ENNReal.ofReal (p.1 ^ (-(1 / 2 : ℝ))) * ‖tnorm2 (Gr (cellPt c p))‖ₑ ^ (2 : ℝ)) =
          ENNReal.ofReal (((1 + H1) * cNorm8 χ) ^ 2 *
            (p.1 ^ (-(1 / 2 : ℝ)) * ‖tnorm2 (Gr (cellPt c p))‖ ^ 2)) := by
        rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
          Real.rpow_two, ← ENNReal.ofReal_mul (Real.rpow_nonneg hs_pos.le _),
          ← ENNReal.ofReal_mul (sq_nonneg _)]
      rw [hLHS, hRHS]
      exact ENNReal.ofReal_le_ofReal hgsq
  have hstep1 : ∫⁻ p, ‖g p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) ≤
      ENNReal.ofReal (((1 + H1) * cNorm8 χ) ^ 2) *
        ∫⁻ p, ‖tnorm2 (Gr (cellPt c p))‖ₑ ^ (2 : ℝ) ∂(measureHT c) := by
    have hm_tn : Measurable (fun p => ‖tnorm2 (Gr (cellPt c p))‖ₑ ^ (2 : ℝ)) :=
      (htn_meas.comp (UnforcedLeray.Short.PartIIIb.NearInst.Masked.measurable_cellPt c)).enorm.pow_const (2 : ℝ)
    have hm_w : Measurable (fun p : Profile => ENNReal.ofReal (p.1 ^ (-(1 / 2 : ℝ)))) :=
      ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)
    calc ∫⁻ p, ‖g p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c)
        ≤ ∫⁻ p, ENNReal.ofReal (((1 + H1) * cNorm8 χ) ^ 2) *
            (ENNReal.ofReal (p.1 ^ (-(1 / 2 : ℝ))) *
              ‖tnorm2 (Gr (cellPt c p))‖ₑ ^ (2 : ℝ)) ∂(cellMeasure c) :=
          lintegral_mono_ae hcell_pt
      _ = ENNReal.ofReal (((1 + H1) * cNorm8 χ) ^ 2) *
            ∫⁻ p, ENNReal.ofReal (p.1 ^ (-(1 / 2 : ℝ))) *
              ‖tnorm2 (Gr (cellPt c p))‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) :=
          lintegral_const_mul _ (hm_w.mul hm_tn)
      _ = ENNReal.ofReal (((1 + H1) * cNorm8 χ) ^ 2) *
            ∫⁻ p, ‖tnorm2 (Gr (cellPt c p))‖ₑ ^ (2 : ℝ) ∂(measureHT c) := by
          rw [measureHT, lintegral_withDensity_eq_lintegral_mul _ hm_w hm_tn]
          rfl
  have hstep2 : ∫⁻ p, ‖tnorm2 (Gr (cellPt c p))‖ₑ ^ (2 : ℝ) ∂(measureHT c) ≤
      ENNReal.ofReal (B_Gr ^ 2) := by
    have hmap : Measure.map (cellPt c) (measureHT c) = ENNReal.ofReal c • ageμ c (-1 / 2) :=
      cpcHT_eq c hc
    have hmap_lint : ∫⁻ p, ‖tnorm2 (Gr (cellPt c p))‖ₑ ^ (2 : ℝ) ∂(measureHT c) =
        ENNReal.ofReal c * ∫⁻ x, ‖tnorm2 (Gr x)‖ₑ ^ (2 : ℝ) ∂(ageμ c (-1 / 2)) := by
      rw [← lintegral_map (htn_meas.enorm.pow_const (2 : ℝ))
        (UnforcedLeray.Short.PartIIIb.NearInst.Masked.measurable_cellPt c), hmap,
        lintegral_smul_measure, smul_eq_mul]
    have hCal_sq : ENNReal.ofReal c * ∫⁻ x, ‖tnorm2 (Gr x)‖ₑ ^ (2 : ℝ) ∂(ageμ c (-1 / 2)) =
        (ENNReal.ofReal (Real.sqrt c) * tCalNorm c Gr) ^ (2 : ℝ) := by
      have heq := eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := ageμ c (-1 / 2))
        (f := fun x => tnorm2 (Gr x)) two_ne_zero ENNReal.ofNat_ne_top
      rw [ENNReal.toReal_ofNat] at heq
      have hpow := congrArg (fun x : ℝ≥0∞ => x ^ (2 : ℝ)) heq
      rw [← ENNReal.rpow_mul, show (1 / (2 : ℝ)) * 2 = 1 by norm_num, ENNReal.rpow_one] at hpow
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg c) (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_two, Real.sq_sqrt hc.le, ← hpow]
      rfl
    rw [hmap_lint, hCal_sq]
    calc (ENNReal.ofReal (Real.sqrt c) * tCalNorm c Gr) ^ (2 : ℝ)
        ≤ (ENNReal.ofReal B_Gr) ^ (2 : ℝ) := ENNReal.rpow_le_rpow hCal (by norm_num)
      _ = ENNReal.ofReal (B_Gr ^ 2) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hB0 (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_two]
  calc ∫⁻ p, ‖g p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c)
      ≤ ENNReal.ofReal (((1 + H1) * cNorm8 χ) ^ 2) * ENNReal.ofReal (B_Gr ^ 2) :=
        hstep1.trans (by gcongr)
    _ = ENNReal.ofReal (((1 + H1) * cNorm8 χ * B_Gr) ^ 2) := by
        rw [← ENNReal.ofReal_mul (sq_nonneg _)]
        congr 1
        ring

theorem memLp_flatGradCutRep {c σ H1 L1 : ℝ} (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1)
    {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ) (hm : Measurable χ)
    {Gr : Chart → Fin 2 → Fin 2 → ℂ} (hGr : ∀ i j, Measurable (fun x => Gr x i j))
    {B_Gr : ℝ} (hB0 : 0 ≤ B_Gr)
    (hCal : ENNReal.ofReal (Real.sqrt c) * tCalNorm c Gr ≤ ENNReal.ofReal B_Gr) (j : Fin 2) :
    MemLp (flatGradCutRep c χ Gr j) 2 (cellMeasure c) := by
  refine ⟨(measurable_flatGradCutRep c hm hGr j).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    ENNReal.toReal_ofNat]
  have hle := lintegral_flatGradCutRep_sq_le hc hσ hσH hχ hm hGr hB0 hCal j
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (lt_of_le_of_lt hle ENNReal.ofReal_lt_top).ne

theorem cellL2Norm_flatGradCutRep_le_mul {c σ H1 L1 : ℝ} (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1)
    {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ) (hm : Measurable χ)
    {Gr : Chart → Fin 2 → Fin 2 → ℂ} (hGr : ∀ i j, Measurable (fun x => Gr x i j))
    {B_Gr : ℝ} (hB0 : 0 ≤ B_Gr)
    (hCal : ENNReal.ofReal (Real.sqrt c) * tCalNorm c Gr ≤ ENNReal.ofReal B_Gr) (j : Fin 2) :
    cellL2Norm c (flatGradCutRep c χ Gr j) ≤ (1 + H1) * cNorm8 χ * B_Gr := by
  let g := flatGradCutRep c χ Gr j
  have hmem := memLp_flatGradCutRep hc hσ hσH hχ hm hGr hB0 hCal j
  have hint : Integrable (fun p => ‖g p‖ ^ 2) (cellMeasure c) :=
    hmem.integrable_norm_pow two_ne_zero
  have hofReal : ENNReal.ofReal (∫ p, ‖g p‖ ^ 2 ∂(cellMeasure c)) =
      ∫⁻ p, ‖g p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => sq_nonneg _)]
    refine lintegral_congr fun p => ?_
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]
  have hH1_pos : 0 < H1 := lt_of_lt_of_le hσ hσH
  have hC0 : 0 ≤ (1 + H1) * cNorm8 χ * B_Gr :=
    mul_nonneg (mul_nonneg (by linarith) (cNorm8_nonneg χ)) hB0
  have hint_le : ∫ p, ‖g p‖ ^ 2 ∂(cellMeasure c) ≤ ((1 + H1) * cNorm8 χ * B_Gr) ^ 2 := by
    refine (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).1 ?_
    rw [hofReal]
    exact lintegral_flatGradCutRep_sq_le hc hσ hσH hχ hm hGr hB0 hCal j
  unfold cellL2Norm
  calc (∫ p, ‖g p‖ ^ 2 ∂(cellMeasure c)) ^ (1 / 2 : ℝ)
      ≤ (((1 + H1) * cNorm8 χ * B_Gr) ^ 2) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (integral_nonneg fun _ => sq_nonneg _) hint_le (by norm_num)
    _ = (1 + H1) * cNorm8 χ * B_Gr := by
        rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hC0]

theorem cellL2Norm_add_le {c : ℝ} {f g : Profile → MeridC}
    (hf : MemLp f 2 (cellMeasure c)) (hg : MemLp g 2 (cellMeasure c)) :
    cellL2Norm c (fun p => f p + g p) ≤ cellL2Norm c f + cellL2Norm c g := by
  have hfg : MemLp (f + g) 2 (cellMeasure c) := hf.add hg
  have h_eq : ∀ (h : Profile → MeridC) (hh : MemLp h 2 (cellMeasure c)),
      cellL2Norm c h = ‖hh.toLp h‖ := fun h hh => by
    have hint : Integrable (fun p => ‖h p‖ ^ 2) (cellMeasure c) :=
      hh.integrable_norm_pow two_ne_zero
    have hLp : eLpNorm ((hh.toLp h : Lp MeridC 2 (cellMeasure c)) : Profile → MeridC)
        2 (cellMeasure c) = ENNReal.ofReal ‖hh.toLp h‖ := by
      rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top (hh.toLp h))]
    have heq := eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := cellMeasure c)
      (f := h) two_ne_zero ENNReal.ofNat_ne_top
    rw [eLpNorm_congr_ae hh.coeFn_toLp.symm, hLp, ENNReal.toReal_ofNat] at heq
    have hofReal : ∫⁻ p, ‖h p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) =
        ENNReal.ofReal (∫ p, ‖h p‖ ^ 2 ∂(cellMeasure c)) := by
      rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => sq_nonneg _)]
      refine lintegral_congr fun p => ?_
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]
    have hpow : (∫⁻ p, ‖h p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c)) ^ (1 / (2 : ℝ)) =
        ENNReal.ofReal (cellL2Norm c h) := by
      rw [hofReal, ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun _ => sq_nonneg _)
        (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      rfl
    rw [hpow] at heq
    exact ((ENNReal.ofReal_eq_ofReal_iff (norm_nonneg _) (cellL2Norm_nonneg c h)).1 heq).symm
  rw [show (fun p => f p + g p) = f + g from rfl, h_eq (f + g) hfg, h_eq f hf, h_eq g hg,
    MemLp.toLp_add]
  exact norm_add_le _ _

theorem memLp_flatCutSpatialDeriv {c σ H1 L1 : ℝ} (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1)
    {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ) (hm : Measurable χ) (W : HSpace c MeridC)
    {Gr : Chart → Fin 2 → Fin 2 → ℂ} (hGr : ∀ i j, Measurable (fun x => Gr x i j))
    {B_Gr : ℝ} (hB0 : 0 ≤ B_Gr)
    (hCal : ENNReal.ofReal (Real.sqrt c) * tCalNorm c Gr ≤ ENNReal.ofReal B_Gr) (j : Fin 2) :
    MemLp (flatCutSpatialDeriv c χ W Gr j) 2 (cellMeasure c) := by
  let v : Profile := if j = 0 then (0, 1, 0) else (0, 0, 1)
  have hdχ_eq : (if j = 0 then pdQ χ else pdEta χ) = fun q => fderiv ℝ χ q v := by
    fin_cases j <;> rfl
  have hdχ : IsNearCutoff c σ H1 L1 (if j = 0 then pdQ χ else pdEta χ) := by
    rw [hdχ_eq]
    exact isNearCutoff_fderiv_apply hχ v
  have hm_dχ : Measurable (if j = 0 then pdQ χ else pdEta χ) :=
    hdχ.smooth.continuous.measurable
  have hmem1 := memLp_flatStressCutRep hc hσ hσH hdχ hm_dχ W
  have hmem2 := memLp_flatGradCutRep hc hσ hσH hχ hm hGr hB0 hCal j
  exact hmem1.add hmem2

theorem qPeriodic_flatCutSpatialDeriv {c σ H1 L1 : ℝ} (hc : 0 < c) {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) (W : HSpace c MeridC)
    (Gr : Chart → Fin 2 → Fin 2 → ℂ) (j : Fin 2) :
    QPeriodic c (flatCutSpatialDeriv c χ W Gr j) := by
  let v : Profile := if j = 0 then (0, 1, 0) else (0, 0, 1)
  have hdχ_eq : (if j = 0 then pdQ χ else pdEta χ) = fun q => fderiv ℝ χ q v := by
    fin_cases j <;> rfl
  have hdχ : IsNearCutoff c σ H1 L1 (if j = 0 then pdQ χ else pdEta χ) := by
    rw [hdχ_eq]
    exact isNearCutoff_fderiv_apply hχ v
  have hp1 := flatStressCutRep_periodic hc hdχ W
  have hp2 := flatGradCutRep_periodic hc hχ Gr j
  intro p
  simp only [flatCutSpatialDeriv, hp1 p, hp2 p]

theorem flatCutSpatialDeriv_support {c σ H1 L1 : ℝ} {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) (W : HSpace c MeridC)
    (Gr : Chart → Fin 2 → Fin 2 → ℂ) (j : Fin 2) (p : Profile)
    (hp : flatCutSpatialDeriv c χ W Gr j p ≠ 0) :
    σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1 := by
  let v : Profile := if j = 0 then (0, 1, 0) else (0, 0, 1)
  have hdχ_eq : (if j = 0 then pdQ χ else pdEta χ) = fun q => fderiv ℝ χ q v := by
    fin_cases j <;> rfl
  have hdχ : IsNearCutoff c σ H1 L1 (if j = 0 then pdQ χ else pdEta χ) := by
    rw [hdχ_eq]
    exact isNearCutoff_fderiv_apply hχ v
  by_cases h1 : flatStressCutRep c (if j = 0 then pdQ χ else pdEta χ) W p = 0
  · refine flatGradCutRep_support hχ Gr j p fun h2 => hp ?_
    simp [flatCutSpatialDeriv, h1, h2]
  · exact flatStressCutRep_support hdχ W p h1

theorem cellL2Norm_flatCutSpatialDeriv_T0flat_le {ν c σ H1 L1 M γs : ℝ} (χ χ1 : Profile → ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1) (hL1 : 0 ≤ L1) (hγ : 0 < γs)
    (hχ : IsNearCutoff c σ H1 L1 χ) (hm : Measurable χ) {μ : ℂ} (hμM : ‖μ‖ ≤ M)
    (hμγ : γs ≤ μ.re + 1 / 4) (b : HSpace c MeridC)
    {Gr : Chart → Fin 2 → Fin 2 → ℂ} (hGr : ∀ i j, Measurable (fun x => Gr x i j))
    {C_G : ℝ} (hCG : 0 ≤ C_G)
    (hCal : ENNReal.ofReal (Real.sqrt c) * tCalNorm c Gr ≤
      ENNReal.ofReal (C_G * Gamma ν c σ H1 L1 M γs χ χ1 ^ 2 * ‖b‖))
    (j : Fin 2) :
    cellL2Norm c (flatCutSpatialDeriv c χ (T0flat hc ν μ b) Gr j) ≤
      (C_G + 1) * Gamma ν c σ H1 L1 M γs χ χ1 ^ 4 * ‖b‖ := by
  set Gam := Gamma ν c σ H1 L1 M γs χ χ1
  have hM0 : 0 ≤ M := (norm_nonneg μ).trans hμM
  have hG1 : 1 ≤ Gam := one_le_gamma_flat χ χ1 hν hc hσ hσH hL1 hγ hM0
  have hG0 : 0 ≤ Gam := by linarith
  have h1H1_G : 1 + H1 ≤ Gam := by
    unfold Gam Gamma GammaBox
    have : 0 < ν⁻¹ := inv_pos.2 hν
    have : 0 < c⁻¹ := inv_pos.2 hc
    have : 0 < σ⁻¹ := inv_pos.2 hσ
    have : 0 < γs⁻¹ := inv_pos.2 hγ
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hcN_G : cNorm8 χ ≤ Gam := by
    unfold Gam Gamma GammaBox
    have : 0 < ν⁻¹ := inv_pos.2 hν
    have : 0 < c⁻¹ := inv_pos.2 hc
    have : 0 < σ⁻¹ := inv_pos.2 hσ
    have : 0 < γs⁻¹ := inv_pos.2 hγ
    have : 0 < H1 := lt_of_lt_of_le hσ hσH
    linarith [cNorm8_nonneg χ1]
  let v : Profile := if j = 0 then (0, 1, 0) else (0, 0, 1)
  have hv : ‖v‖ ≤ 1 := by
    dsimp only [v]
    fin_cases j <;> simp [Prod.norm_mk]
  have hdχ_eq : (if j = 0 then pdQ χ else pdEta χ) = fun q => fderiv ℝ χ q v := by
    fin_cases j <;> rfl
  have hdχ : IsNearCutoff c σ H1 L1 (if j = 0 then pdQ χ else pdEta χ) := by
    rw [hdχ_eq]
    exact isNearCutoff_fderiv_apply hχ v
  have hm_dχ : Measurable (if j = 0 then pdQ χ else pdEta χ) :=
    hdχ.smooth.continuous.measurable
  set B_Gr : ℝ := C_G * Gam ^ 2 * ‖b‖
  have hB0 : 0 ≤ B_Gr := by dsimp [B_Gr]; positivity
  have hmem1 := memLp_flatStressCutRep hc hσ hσH hdχ hm_dχ (T0flat hc ν μ b)
  have hmem2 := memLp_flatGradCutRep hc hσ hσH hχ hm hGr hB0 hCal j
  have hbd1 : cellL2Norm c (flatStressCutRep c (if j = 0 then pdQ χ else pdEta χ)
      (T0flat hc ν μ b)) ≤ Gam ^ 4 * ‖b‖ := by
    rw [hdχ_eq]
    have hW := norm_T0flat_apply_le χ χ1 hν hc hσ hσH hL1 hγ hμM hμγ b
    have hprod : (1 + H1) * cNorm8 χ * Gam ≤ Gam ^ 3 := by
      calc (1 + H1) * cNorm8 χ * Gam
          ≤ Gam * Gam * Gam := mul_le_mul_of_nonneg_right
            (mul_le_mul h1H1_G hcN_G (cNorm8_nonneg χ) hG0) hG0
        _ = Gam ^ 3 := by ring
    have hG3_le_G4 : Gam ^ 3 ≤ Gam ^ 4 := by
      calc Gam ^ 3 = Gam ^ 3 * 1 := (mul_one _).symm
        _ ≤ Gam ^ 3 * Gam := mul_le_mul_of_nonneg_left hG1 (by positivity)
        _ = Gam ^ 4 := by ring
    calc cellL2Norm c (flatStressCutRep c (fun q => fderiv ℝ χ q v) (T0flat hc ν μ b))
        ≤ (1 + H1) * cNorm8 χ * ‖T0flat hc ν μ b‖ :=
          cellL2Norm_flatStressCutRep_fderiv_le_mul hc hσ hσH hχ hv (T0flat hc ν μ b)
      _ ≤ (1 + H1) * cNorm8 χ * (Gam * ‖b‖) :=
          mul_le_mul_of_nonneg_left hW
            (mul_nonneg (by have := lt_of_lt_of_le hσ hσH; linarith) (cNorm8_nonneg χ))
      _ = ((1 + H1) * cNorm8 χ * Gam) * ‖b‖ := by ring
      _ ≤ Gam ^ 4 * ‖b‖ := mul_le_mul_of_nonneg_right (hprod.trans hG3_le_G4) (norm_nonneg b)
  have hbd2 : cellL2Norm c (flatGradCutRep c χ Gr j) ≤ C_G * Gam ^ 4 * ‖b‖ := by
    have hprod : (1 + H1) * cNorm8 χ * (C_G * Gam ^ 2) ≤ C_G * Gam ^ 4 := by
      calc (1 + H1) * cNorm8 χ * (C_G * Gam ^ 2)
          = C_G * ((1 + H1) * cNorm8 χ) * Gam ^ 2 := by ring
        _ ≤ C_G * (Gam * Gam) * Gam ^ 2 := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
              (mul_le_mul h1H1_G hcN_G (cNorm8_nonneg χ) hG0) hCG) (sq_nonneg Gam)
        _ = C_G * Gam ^ 4 := by ring
    calc cellL2Norm c (flatGradCutRep c χ Gr j)
        ≤ (1 + H1) * cNorm8 χ * B_Gr :=
          cellL2Norm_flatGradCutRep_le_mul hc hσ hσH hχ hm hGr hB0 hCal j
      _ = ((1 + H1) * cNorm8 χ * (C_G * Gam ^ 2)) * ‖b‖ := by dsimp [B_Gr]; ring
      _ ≤ C_G * Gam ^ 4 * ‖b‖ := mul_le_mul_of_nonneg_right hprod (norm_nonneg b)
  calc cellL2Norm c (flatCutSpatialDeriv c χ (T0flat hc ν μ b) Gr j)
      ≤ cellL2Norm c (flatStressCutRep c (if j = 0 then pdQ χ else pdEta χ)
          (T0flat hc ν μ b)) + cellL2Norm c (flatGradCutRep c χ Gr j) :=
        cellL2Norm_add_le hmem1 hmem2
    _ ≤ Gam ^ 4 * ‖b‖ + C_G * Gam ^ 4 * ‖b‖ := add_le_add hbd1 hbd2
    _ = (C_G + 1) * Gam ^ 4 * ‖b‖ := by ring

/-! ### 2. `IsMeridTest` stability under `pdQ`, `pdEta`, and cutoff multiplication -/

/-- Unified spatial profile derivative: `j = 0` is `pdQ`, `j = 1` is `pdEta`. -/
def pdSpatial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (j : Fin 2) (f : Profile → E) : Profile → E :=
  if j = 0 then pdQ f else pdEta f

theorem pdSpatial_eq_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (j : Fin 2) (f : Profile → E) (p : Profile) :
    pdSpatial j f p = fderiv ℝ f p (0, UnforcedLeray.B0579.dir j) := by
  fin_cases j <;> rfl

theorem isMeridTest_pdSpatial {c : ℝ} {φ : Profile → MeridC} (hφ : IsMeridTest c φ) (j : Fin 2) :
    IsMeridTest c (pdSpatial j φ) := by
  obtain ⟨s0, s1, L, hs0, hband⟩ := hφ.band
  have hK : IsClosed (Icc s0 s1 ×ˢ (univ : Set (ℝ × ℝ)) ∩ {p : Profile | |p.2.2| ≤ L}) :=
    (isClosed_Icc.prod isClosed_univ).inter
      (isClosed_le (by fun_prop) continuous_const)
  have hsub : tsupport φ ⊆ Icc s0 s1 ×ˢ (univ : Set (ℝ × ℝ)) ∩ {p : Profile | |p.2.2| ≤ L} := by
    refine closure_minimal (fun p hp => ?_) hK
    obtain ⟨h1, h2⟩ := hband p hp
    exact ⟨⟨h1, trivial⟩, h2⟩
  refine ⟨?_, ?_, ⟨s0, s1, L, hs0, fun p hp => ?_⟩⟩
  · fin_cases j
    · exact UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.isMeridTest_pdQ_aux hφ
    · exact UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.isMeridTest_pdEta_aux hφ
  · intro p
    rw [pdSpatial_eq_fderiv, pdSpatial_eq_fderiv]
    exact UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.pd_periodic_aux hφ.periodic _ p
  · rw [pdSpatial_eq_fderiv] at hp
    have hdf : fderiv ℝ φ p ≠ 0 := fun h0 => hp (by simp [h0])
    have hm := hsub (support_fderiv_subset ℝ hdf)
    exact ⟨hm.1.1, hm.2⟩

theorem isMeridTest_smul_cutoff {c σ H1 L1 : ℝ} (hσ : 0 < σ) {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) {φ : Profile → MeridC} (hφ : IsMeridTest c φ) :
    IsMeridTest c (fun p => χ p • φ p) where
  smooth := hχ.smooth.smul hφ.smooth
  periodic p := by simp only [hχ.periodic p, hφ.periodic p]
  band := ⟨σ, H1, L1, hσ, fun p hp => by
    have hχ0 : χ p ≠ 0 := fun h0 => hp (by simp [h0])
    obtain ⟨hs1, hs2, hη⟩ := hχ.support p hχ0
    exact ⟨⟨hs1, hs2⟩, hη⟩⟩

theorem pdSpatial_smul_cutoff {χ : Profile → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {φ : Profile → MeridC} (hφ : ContDiff ℝ ∞ φ) (j : Fin 2) (p : Profile) :
    pdSpatial j (fun q => χ q • φ q) p =
      pdSpatial j χ p • φ p + χ p • pdSpatial j φ p := by
  rw [pdSpatial_eq_fderiv, pdSpatial_eq_fderiv, pdSpatial_eq_fderiv]
  have hdχ : DifferentiableAt ℝ χ p := (hχ.differentiable (by decide)) p
  have hdφ : DifferentiableAt ℝ φ p := (hφ.differentiable (by decide)) p
  have hsmul := hdχ.hasFDerivAt.smul hdφ.hasFDerivAt
  rw [show (fun q => χ q • φ q) = χ • φ from rfl, hsmul.fderiv]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, smul_apply]
  exact add_comm _ _

theorem memLp_of_isMeridTest_cellMeasure {c : ℝ} (hc : 0 < c) {φ : Profile → MeridC}
    (hφ : IsMeridTest c φ) : MemLp φ 2 (cellMeasure c) := by
  obtain ⟨M, hM⟩ := UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.merid_test_bounded
    c hc φ hφ
  obtain ⟨s0, s1, L, _hs0, hband⟩ := hφ.band
  let K : Set Profile := Icc s0 s1 ×ˢ (Icc 0 c ×ˢ Icc (-L) L)
  have hK_compact : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hK_meas : MeasurableSet K := measurableSet_Icc.prod (measurableSet_Icc.prod measurableSet_Icc)
  have hcell_K : ∀ᵐ p ∂(cellMeasure c), φ p ≠ 0 → p ∈ K := by
    filter_upwards [ae_cell_cellMeasure c] with p hpcell hp0
    obtain ⟨hs, hη⟩ := hband p hp0
    exact ⟨hs, Ioc_subset_Icc_self hpcell.2.1, abs_le.1 hη⟩
  have hM0 : 0 ≤ max M 0 := le_max_right M 0
  refine ⟨hφ.smooth.continuous.measurable.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    ENNReal.toReal_ofNat]
  have hle : ∫⁻ p, ‖φ p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) ≤
      ENNReal.ofReal ((max M 0) ^ 2) * cellMeasure c K := by
    calc ∫⁻ p, ‖φ p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c)
        ≤ ∫⁻ p, K.indicator (fun _ => ENNReal.ofReal ((max M 0) ^ 2)) p ∂(cellMeasure c) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hcell_K] with p hpK
          by_cases hp0 : φ p = 0
          · simp [hp0]
          · rw [indicator_of_mem (hpK hp0), ← ofReal_norm,
              ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]
            exact ENNReal.ofReal_le_ofReal
              (pow_le_pow_left₀ (norm_nonneg _) ((hM p).trans (le_max_left M 0)) 2)
      _ = ENNReal.ofReal ((max M 0) ^ 2) * cellMeasure c K := by
          rw [lintegral_indicator hK_meas, setLIntegral_const]
  have hK_fin : cellMeasure c K < ⊤ :=
    lt_of_le_of_lt (Measure.restrict_le_self.trans le_rfl _) hK_compact.measure_lt_top
  have hprod_fin : ENNReal.ofReal ((max M 0) ^ 2) * cellMeasure c K < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK_fin
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (lt_of_le_of_lt hle hprod_fin).ne

theorem integrable_inner_cellMeasure {c : ℝ} {f g : Profile → MeridC}
    (hf : MemLp f 2 (cellMeasure c)) (hg : MemLp g 2 (cellMeasure c)) :
    Integrable (fun p => inner ℂ (f p) (g p)) (cellMeasure c) :=
  (hf.norm.integrable_mul hg.norm).mono' (hf.1.inner hg.1)
    (Eventually.of_forall fun p => by
      simpa only [Pi.mul_apply] using norm_inner_le_norm (𝕜 := ℂ) (f p) (g p))

/-! ### 3. Slice weak-gradient identity and `(q, η)` integration by parts -/

theorem isCylTest_clm_slice {c : ℝ} {ψ : Profile → MeridC} (hψ : IsMeridTest c ψ)
    (L : MeridC →L[ℝ] ℝ) (s : ℝ) :
    UnforcedLeray.B0579.IsCylTest c (fun y : ℝ × ℝ => L (ψ (s, y))) where
  smooth := L.contDiff.comp (hψ.smooth.comp (contDiff_const.prodMk contDiff_id))
  periodic y := congrArg L (hψ.periodic (s, y))
  band := by
    obtain ⟨s0, s1, R, _hs0, hband⟩ := hψ.band
    refine ⟨R, fun y hy => ?_⟩
    have h0 : ψ (s, y) = 0 := by
      by_contra hne
      have := (hband (s, y) hne).2
      linarith
    simp [h0]

theorem pd_clm_slice {ψ : Profile → MeridC} (hψ : ContDiff ℝ ∞ ψ)
    (L : MeridC →L[ℝ] ℝ) (s : ℝ) (j : Fin 2) (y : ℝ × ℝ) :
    UnforcedLeray.B0579.pd j (fun z : ℝ × ℝ => L (ψ (s, z))) y =
      L (pdSpatial j ψ (s, y)) := by
  have hdψ : Differentiable ℝ ψ := hψ.differentiable (by decide)
  have hdLψ : Differentiable ℝ (fun p : Profile => L (ψ p)) := L.differentiable.comp hdψ
  have h1 : HasFDerivAt (fun z : ℝ × ℝ => L (ψ (s, z)))
      ((fderiv ℝ (fun p : Profile => L (ψ p)) (s, y)).comp
        (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) y :=
    (hdLψ (s, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right s y)
  rw [UnforcedLeray.B0579.pd, h1.fderiv, pdSpatial_eq_fderiv]
  change fderiv ℝ (fun p : Profile => L (ψ p)) (s, y) (0, UnforcedLeray.B0579.dir j) =
    L (fderiv ℝ ψ (s, y) (0, UnforcedLeray.B0579.dir j))
  exact fderiv_clm_comp' L (hdψ (s, y)) (0, UnforcedLeray.B0579.dir j)

theorem slice_ibp_clm {c : ℝ} {f g : ℝ × ℝ → ℂ} {j : Fin 2}
    (hw : HasWeakCellDerivC c j f g) {ψ : Profile → MeridC} (hψ : IsMeridTest c ψ)
    (L : MeridC →L[ℝ] ℝ) (s : ℝ) :
    IntegrableOn (fun y : ℝ × ℝ =>
        star (f y) * (L (pdSpatial j ψ (s, y)) : ℂ) +
        star (g y) * (L (ψ (s, y)) : ℂ)) (UnforcedLeray.B0579.cell c) ∧
      ∫ y in UnforcedLeray.B0579.cell c,
        (star (f y) * (L (pdSpatial j ψ (s, y)) : ℂ) +
          star (g y) * (L (ψ (s, y)) : ℂ)) = 0 := by
  have hcyl := isCylTest_clm_slice hψ L s
  obtain ⟨hI1, hI2⟩ := hw.1 _ hcyl
  have hEq := hw.2 _ hcyl
  have hpd_eq : ∀ y : ℝ × ℝ,
      (UnforcedLeray.B0579.pd j (fun z => L (ψ (s, z))) y : ℂ) =
        (L (pdSpatial j ψ (s, y)) : ℂ) := fun y =>
    congrArg Complex.ofReal (pd_clm_slice hψ.smooth L s j y)
  have hI1' : IntegrableOn (fun y => f y * (L (pdSpatial j ψ (s, y)) : ℂ))
      (UnforcedLeray.B0579.cell c) :=
    hI1.congr_fun (fun y _ => by dsimp only; rw [hpd_eq y]) (UnforcedLeray.B0579.measurableSet_cell c)
  have hsum : IntegrableOn (fun y =>
      f y * (L (pdSpatial j ψ (s, y)) : ℂ) + g y * (L (ψ (s, y)) : ℂ))
      (UnforcedLeray.B0579.cell c) := hI1'.add hI2
  have hsum_zero : ∫ y in UnforcedLeray.B0579.cell c,
      (f y * (L (pdSpatial j ψ (s, y)) : ℂ) + g y * (L (ψ (s, y)) : ℂ)) = 0 := by
    rw [integral_add hI1' hI2]
    have h1 : ∫ y in UnforcedLeray.B0579.cell c, f y * (L (pdSpatial j ψ (s, y)) : ℂ) =
        ∫ y in UnforcedLeray.B0579.cell c,
          f y * (UnforcedLeray.B0579.pd j (fun z => L (ψ (s, z))) y : ℂ) :=
      setIntegral_congr_fun (UnforcedLeray.B0579.measurableSet_cell c) fun y _ => by
        rw [hpd_eq y]
    rw [h1, hEq, neg_add_cancel]
  have hconj_pt : ∀ y : ℝ × ℝ,
      star (f y * (L (pdSpatial j ψ (s, y)) : ℂ) + g y * (L (ψ (s, y)) : ℂ)) =
        star (f y) * (L (pdSpatial j ψ (s, y)) : ℂ) + star (g y) * (L (ψ (s, y)) : ℂ) := by
    intro y
    simp
  have hIconj0 : IntegrableOn (fun y =>
      star (f y * (L (pdSpatial j ψ (s, y)) : ℂ) + g y * (L (ψ (s, y)) : ℂ)))
      (UnforcedLeray.B0579.cell c) :=
    Complex.conjCLE.toContinuousLinearMap.integrable_comp hsum
  have hIconj : IntegrableOn (fun y =>
      star (f y) * (L (pdSpatial j ψ (s, y)) : ℂ) + star (g y) * (L (ψ (s, y)) : ℂ))
      (UnforcedLeray.B0579.cell c) :=
    hIconj0.congr_fun (fun y _ => hconj_pt y) (UnforcedLeray.B0579.measurableSet_cell c)
  refine ⟨hIconj, ?_⟩
  calc ∫ y in UnforcedLeray.B0579.cell c,
          (star (f y) * (L (pdSpatial j ψ (s, y)) : ℂ) + star (g y) * (L (ψ (s, y)) : ℂ))
      = ∫ y in UnforcedLeray.B0579.cell c,
          star (f y * (L (pdSpatial j ψ (s, y)) : ℂ) + g y * (L (ψ (s, y)) : ℂ)) :=
        setIntegral_congr_fun (UnforcedLeray.B0579.measurableSet_cell c) fun y _ =>
          (hconj_pt y).symm
    _ = star (∫ y in UnforcedLeray.B0579.cell c,
          (f y * (L (pdSpatial j ψ (s, y)) : ℂ) + g y * (L (ψ (s, y)) : ℂ))) :=
        integral_conj
    _ = 0 := by rw [hsum_zero, star_zero]

theorem slice_ibp_coord {c : ℝ} {f g : ℝ × ℝ → ℂ} {j : Fin 2}
    (hw : HasWeakCellDerivC c j f g) {ψ : Profile → MeridC} (hψ : IsMeridTest c ψ)
    (s : ℝ) (i : Fin 2) :
    ∫ y in UnforcedLeray.B0579.cell c,
      (star (f y) * pdSpatial j ψ (s, y) i + star (g y) * ψ (s, y) i) = 0 := by
  let L_re : MeridC →L[ℝ] ℝ :=
    Complex.reCLM.comp ((EuclideanSpace.proj i : MeridC →L[ℂ] ℂ).restrictScalars ℝ)
  let L_im : MeridC →L[ℝ] ℝ :=
    Complex.imCLM.comp ((EuclideanSpace.proj i : MeridC →L[ℂ] ℂ).restrictScalars ℝ)
  obtain ⟨hIre, hZre⟩ := slice_ibp_clm hw hψ L_re s
  obtain ⟨hIim, hZim⟩ := slice_ibp_clm hw hψ L_im s
  have hpt : ∀ y : ℝ × ℝ,
      star (f y) * pdSpatial j ψ (s, y) i + star (g y) * ψ (s, y) i =
        (star (f y) * (L_re (pdSpatial j ψ (s, y)) : ℂ) + star (g y) * (L_re (ψ (s, y)) : ℂ)) +
        Complex.I * (star (f y) * (L_im (pdSpatial j ψ (s, y)) : ℂ) +
          star (g y) * (L_im (ψ (s, y)) : ℂ)) := by
    intro y
    have h1 : (L_re (pdSpatial j ψ (s, y)) : ℂ) + Complex.I * (L_im (pdSpatial j ψ (s, y)) : ℂ) =
        pdSpatial j ψ (s, y) i := by
      simp [L_re, L_im, mul_comm Complex.I, Complex.re_add_im]
    have h2 : (L_re (ψ (s, y)) : ℂ) + Complex.I * (L_im (ψ (s, y)) : ℂ) = ψ (s, y) i := by
      simp [L_re, L_im, mul_comm Complex.I, Complex.re_add_im]
    linear_combination -(star (f y)) * h1 - (star (g y)) * h2
  have hfun : (fun y : ℝ × ℝ => star (f y) * pdSpatial j ψ (s, y) i + star (g y) * ψ (s, y) i) =
      fun y =>
        (star (f y) * (L_re (pdSpatial j ψ (s, y)) : ℂ) + star (g y) * (L_re (ψ (s, y)) : ℂ)) +
        Complex.I * (star (f y) * (L_im (pdSpatial j ψ (s, y)) : ℂ) +
          star (g y) * (L_im (ψ (s, y)) : ℂ)) := funext hpt
  rw [hfun, integral_add hIre (hIim.const_mul Complex.I), integral_const_mul, hZre, hZim]
  simp

theorem slice_ibp_merid {c : ℝ} {b : Chart → Fin 2 → ℂ} {Gr : Chart → Fin 2 → Fin 2 → ℂ}
    {s : ℝ} {j : Fin 2}
    (hw : ∀ i j, HasWeakCellDerivC c j (fun y => b (s, y) i) (fun y => Gr (s, y) i j))
    {ψ : Profile → MeridC} (hψ : IsMeridTest c ψ) :
    ∫ y in UnforcedLeray.B0579.cell c,
      ∑ i : Fin 2, (star (b (s, y) i) * pdSpatial j ψ (s, y) i +
        star (Gr (s, y) i j) * ψ (s, y) i) = 0 := by
  let L_re (i : Fin 2) : MeridC →L[ℝ] ℝ :=
    Complex.reCLM.comp ((EuclideanSpace.proj i : MeridC →L[ℂ] ℂ).restrictScalars ℝ)
  let L_im (i : Fin 2) : MeridC →L[ℝ] ℝ :=
    Complex.imCLM.comp ((EuclideanSpace.proj i : MeridC →L[ℂ] ℂ).restrictScalars ℝ)
  have hI : ∀ i : Fin 2, IntegrableOn (fun y : ℝ × ℝ =>
      star (b (s, y) i) * pdSpatial j ψ (s, y) i +
        star (Gr (s, y) i j) * ψ (s, y) i) (UnforcedLeray.B0579.cell c) := by
    intro i
    obtain ⟨hIre, _⟩ := slice_ibp_clm (hw i j) hψ (L_re i) s
    obtain ⟨hIim, _⟩ := slice_ibp_clm (hw i j) hψ (L_im i) s
    refine (hIre.add (hIim.const_mul Complex.I)).congr_fun (fun y _ => ?_)
      (UnforcedLeray.B0579.measurableSet_cell c)
    simp only [Pi.add_apply]
    have h1 : (L_re i (pdSpatial j ψ (s, y)) : ℂ) +
        Complex.I * (L_im i (pdSpatial j ψ (s, y)) : ℂ) = pdSpatial j ψ (s, y) i := by
      simp [L_re, L_im, mul_comm Complex.I, Complex.re_add_im]
    have h2 : (L_re i (ψ (s, y)) : ℂ) + Complex.I * (L_im i (ψ (s, y)) : ℂ) = ψ (s, y) i := by
      simp [L_re, L_im, mul_comm Complex.I, Complex.re_add_im]
    linear_combination (star (b (s, y) i)) * h1 + (star (Gr (s, y) i j)) * h2
  rw [integral_finsetSum _ fun i _ => hI i]
  exact Finset.sum_eq_zero fun i _ => slice_ibp_coord (hw i j) hψ s i

theorem cellPt_cellPtInv_of_mem {c : ℝ} {x : Chart}
    (hx : x ∈ Ioi (0 : ℝ) ×ˢ UnforcedLeray.B0579.cell c) :
    cellPt c (cellPtInv c x) = x := by
  rcases x with ⟨s, q, η⟩
  obtain ⟨_, ⟨hq1, hq2⟩, _⟩ := hx
  change (s, UnforcedLeray.Short.PartIIIb.NearInst.Masked.ctT c (N01.ctInvT c q), η) = (s, q, η)
  congr 2
  unfold UnforcedLeray.Short.PartIIIb.NearInst.Masked.ctT N01.ctInvT
  split_ifs <;> first | rfl | (exfalso; linarith) | ring

theorem qPeriodic_cellPtInv' {c : ℝ} {w : Profile → MeridC} (hw : QPeriodic c w)
    (x : Chart) : w (cellPtInv c x) = w x := by
  rcases x with ⟨s, q, η⟩
  unfold cellPtInv
  by_cases h : 0 < q
  · simp [h]
  · simp only [ite_eq_right_iff.2 (fun h' => False.elim (h h'))]
    exact hw (s, q, η)

/-- Main `(q, η)` integration-by-parts identity for `u = flatStressCutRep c χ W` and
`flatCutSpatialDeriv c χ W Gr j` on `cellMeasure c`. -/
theorem flatCutSpatialDeriv_ibp {c σ H1 L1 : ℝ} (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1)
    {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ) (hm : Measurable χ)
    {W : HSpace c MeridC} {w_rep : Chart → Fin 2 → ℂ} {Gr : Chart → Fin 2 → Fin 2 → ℂ}
    (hw_rep : w_rep =ᵐ[ageμ c (-3 / 2)] velF c W) (hE : IsEnergyFieldAE c w_rep Gr)
    {B_Gr : ℝ} (hB0 : 0 ≤ B_Gr)
    (hCal : ENNReal.ofReal (Real.sqrt c) * tCalNorm c Gr ≤ ENNReal.ofReal B_Gr)
    (j : Fin 2) {φ : Profile → MeridC} (hφ : IsMeridTest c φ) :
    ∫ p, inner ℂ (flatCutSpatialDeriv c χ W Gr j p) (φ p) ∂(cellMeasure c) =
      -∫ p, inner ℂ (flatStressCutRep c χ W p) (pdSpatial j φ p) ∂(cellMeasure c) := by
  let u := flatStressCutRep c χ W
  let dj := flatCutSpatialDeriv c χ W Gr j
  let ψ : Profile → MeridC := fun p => χ p • φ p
  have hψ : IsMeridTest c ψ := isMeridTest_smul_cutoff hσ hχ hφ
  have hpdφ : IsMeridTest c (pdSpatial j φ) := isMeridTest_pdSpatial hφ j
  have hpdψ : IsMeridTest c (pdSpatial j ψ) := isMeridTest_pdSpatial hψ j
  have hmem_u : MemLp u 2 (cellMeasure c) := memLp_flatStressCutRep hc hσ hσH hχ hm W
  have hmem_dj : MemLp dj 2 (cellMeasure c) :=
    memLp_flatCutSpatialDeriv hc hσ hσH hχ hm W hE.gradMeasurable hB0 hCal j
  have hmem_φ : MemLp φ 2 (cellMeasure c) := memLp_of_isMeridTest_cellMeasure hc hφ
  have hmem_pdφ : MemLp (pdSpatial j φ) 2 (cellMeasure c) :=
    memLp_of_isMeridTest_cellMeasure hc hpdφ
  have hInt_dj : Integrable (fun p => inner ℂ (dj p) (φ p)) (cellMeasure c) :=
    integrable_inner_cellMeasure hmem_dj hmem_φ
  have hInt_u : Integrable (fun p => inner ℂ (u p) (pdSpatial j φ p)) (cellMeasure c) :=
    integrable_inner_cellMeasure hmem_u hmem_pdφ
  let K_cell : Profile → ℂ := fun p =>
    inner ℂ (dj p) (φ p) + inner ℂ (u p) (pdSpatial j φ p)
  have hInt_K : Integrable K_cell (cellMeasure c) := hInt_dj.add hInt_u
  -- Rewrite `K_cell p` on `cell c` using the Leibniz rule `pdSpatial j ψ = pdSpatial j χ • φ + χ • pdSpatial j φ`
  have hK_cell_eq : ∀ p ∈ cell c,
      K_cell p = inner ℂ ((W : Profile → MeridC) p) (pdSpatial j ψ p) +
        inner ℂ (flatGradCol c Gr j p) (ψ p) := by
    intro p hpcell
    have hdχ_eq : (if j = 0 then pdQ χ else pdEta χ) p = pdSpatial j χ p := by
      fin_cases j <;> rfl
    have hu_eq : u p = χ p • (W : Profile → MeridC) p := by
      dsimp only [u, flatStressCutRep]
      rw [periodize_of_mem hc _ hpcell]
    have hdj_eq : dj p = pdSpatial j χ p • (W : Profile → MeridC) p +
        χ p • flatGradCol c Gr j p := by
      dsimp only [dj, flatCutSpatialDeriv, flatStressCutRep, flatGradCutRep]
      rw [hdχ_eq, periodize_of_mem hc _ hpcell, periodize_of_mem hc _ hpcell]
    have hleib : pdSpatial j ψ p = pdSpatial j χ p • φ p + χ p • pdSpatial j φ p :=
      pdSpatial_smul_cutoff hχ.smooth hφ.smooth j p
    have hsmul_inner : ∀ (r : ℝ) (x y : MeridC), inner ℂ (r • x) y = inner ℂ x (r • y) := by
      intro r x y
      rw [← Complex.coe_smul r x, ← Complex.coe_smul r y,
        inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    dsimp only [K_cell, ψ]
    rw [hdj_eq, hu_eq, hleib, inner_add_left, inner_add_right,
      hsmul_inner (pdSpatial j χ p), hsmul_inner (χ p), hsmul_inner (χ p)]
    ring
  -- Transport `∫ K_cell ∂(cellMeasure c)` to `S = Ioi 0 ×ˢ B0579.cell c` via `cellPtInv_map hc`
  let S : Set Chart := Ioi (0 : ℝ) ×ˢ UnforcedLeray.B0579.cell c
  have hSm : MeasurableSet S :=
    measurableSet_Ioi.prod (UnforcedLeray.B0579.measurableSet_cell c)
  have hmap : Measure.map (cellPtInv c) (volume.restrict S) = cellMeasure c :=
    N01.cellPtInv_map hc
  have hmp : MeasurePreserving (cellPtInv c) (volume.restrict S) (cellMeasure c) :=
    ⟨measurable_cellPtInv c, hmap⟩
  have hInt_comp : IntegrableOn (K_cell ∘ cellPtInv c) S :=
    (hmp.integrable_comp hInt_K.aestronglyMeasurable).2 hInt_K
  have hVal_map : ∫ p, K_cell p ∂(cellMeasure c) = ∫ x in S, K_cell (cellPtInv c x) := by
    rw [← hmap]
    exact integral_map (measurable_cellPtInv c).aemeasurable
      (by rw [hmap]; exact hInt_K.aestronglyMeasurable)
  -- Identify `K_cell (cellPtInv c x)` with `K_chart x` a.e. on `S`
  let K_chart : Chart → ℂ := fun x =>
    ∑ i : Fin 2, (star (w_rep x i) * pdSpatial j ψ x i + star (Gr x i j) * ψ x i)
  have hac := volCyl_ac_ageμ hc (-3 / 2)
  have hw_ae_S : w_rep =ᵐ[volume.restrict S] velF c (W : Profile → MeridC) :=
    hac.ae_le hw_rep
  have hcellPtInv_mem : ∀ x ∈ S, cellPtInv c x ∈ cell c := by
    rintro ⟨s, q, η⟩ ⟨hs, ⟨hq1, hq2⟩, _⟩
    refine ⟨hs, ?_, trivial⟩
    change N01.ctInvT c q ∈ Ioc 0 c
    unfold N01.ctInvT
    split_ifs with hq0
    · exact ⟨hq0, by linarith⟩
    · exact ⟨by linarith, by linarith⟩
  have hcongr_S : (K_cell ∘ cellPtInv c) =ᵐ[volume.restrict S] K_chart := by
    filter_upwards [ae_restrict_mem hSm, hw_ae_S] with x hx hwx
    simp only [Function.comp_apply]
    rw [hK_cell_eq (cellPtInv c x) (hcellPtInv_mem x hx),
      qPeriodic_cellPtInv' hpdψ.periodic x, qPeriodic_cellPtInv' hψ.periodic x]
    have hgrad_eq : flatGradCol c Gr j (cellPtInv c x) =
        WithLp.toLp 2 (fun i : Fin 2 => Gr x i j) := by
      unfold flatGradCol
      rw [cellPt_cellPtInv_of_mem hx]
    rw [hgrad_eq]
    simp only [K_chart, PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_two]
    have hw0 : (W : Profile → MeridC) (cellPtInv c x) 0 = w_rep x 0 :=
      (congrFun hwx 0).symm
    have hw1 : (W : Profile → MeridC) (cellPtInv c x) 1 = w_rep x 1 :=
      (congrFun hwx 1).symm
    rw [hw0, hw1]
    simp only [Complex.star_def]
    ring
  have hInt_chart : IntegrableOn K_chart S := hInt_comp.congr hcongr_S
  have hVal_chart : ∫ p, K_cell p ∂(cellMeasure c) = ∫ x in S, K_chart x := by
    rw [hVal_map]
    exact integral_congr_ae hcongr_S
  -- Apply Fubini on `S = Ioi 0 ×ˢ B0579.cell c` and `slice_ibp_merid`
  have hμ : (volume : Measure Chart).restrict S =
      (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (UnforcedLeray.B0579.cell c)) := by
    dsimp only [S]
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  have hInt_prod : Integrable K_chart
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (UnforcedLeray.B0579.cell c))) := by
    rw [← hμ]
    exact hInt_chart
  have hK_zero : ∫ p, K_cell p ∂(cellMeasure c) = 0 := by
    rw [hVal_chart, show ∫ x in S, K_chart x = ∫ x, K_chart x ∂(volume.restrict S) from rfl,
      hμ, integral_prod _ hInt_prod]
    have hae_slice : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
        ∫ y in UnforcedLeray.B0579.cell c, K_chart (s, y) = 0 := by
      filter_upwards [ae_restrict_of_ae hE.weakGradAE, ae_restrict_mem measurableSet_Ioi]
        with s hs hs0
      exact slice_ibp_merid (hs hs0) hψ
    rw [integral_congr_ae hae_slice, integral_zero]
  have hadd_zero : (∫ p, inner ℂ (dj p) (φ p) ∂(cellMeasure c)) +
      ∫ p, inner ℂ (u p) (pdSpatial j φ p) ∂(cellMeasure c) = 0 := by
    rw [← integral_add hInt_dj hInt_u]
    exact hK_zero
  exact eq_neg_of_add_eq_zero_left hadd_zero

end UnforcedLeray.Short.PartIIa.N05_2_1Aux
