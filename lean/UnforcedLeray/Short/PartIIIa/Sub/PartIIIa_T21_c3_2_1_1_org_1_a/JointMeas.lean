import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org_1_a.Package
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf4.Force
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_3_1_1.SeedJet
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_3_2
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_1_1
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_1_1_1
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.ComplCoupling.EulerSubBound.Lattice

/-!
# Helper for `PartIII-a:T21/c3/2/1/1/org/1/a`: joint measurability in the age

For a measurable `W`, the map `(r, y) ↦ movDampedComplInt κ P tr (rho t₁ t₂ r) W y` is jointly
measurable (SP 2974-2978: all ingredients are continuous or measurable in the age).  The dual
generator `H₀` is handled through its explicit moving formula: the heat part by the dual
periodization identity (`seedLamPDSharpDecay`) and the Gram-inverse split, whose age derivative is
a right derivative (`measurable_derivWithin_Ici`), and the Euler part by its moving pullback.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit.RelIntA

open UnforcedLeray.Short.IIIa.CompactDuhamelGapSub UnforcedLeray.Short.IIIa.ComplCouplingSub
  UnforcedLeray.Short.IIIa.ComplFreeRateSub.Leaf4Aux

/-- The heat part of the dual generator in explicit moving form (Gram-inverse split). -/
def HeatFormula (κ : PlanarFrameKernels) (ν r : ℝ) : Prop :=
  ∀ (i : Fin 2) (y : ℝ × ℝ), movLamDualHeat κ ν r i y =
    ∑ j : Fin 2, ((perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))⁻¹ i j *
        ComplCouplingHeat.movLam0DualHeat κ ν r j y +
      (((clockA ν r ^ 2 : ℝ)) : ℂ) *
        derivWithin (fun s => (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)))⁻¹ i j)
          (Ici r) r *
        perLam0 κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j y)

theorem heatFormula_of (κ : PlanarFrameKernels) (hκ : IsSeedKernels κ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ {ν r : ℝ}, 0 < ν → 0 ≤ r →
      D ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) → HeatFormula κ ν r := by
  obtain ⟨hCD, C, _hC0, h0, h1, h2⟩ :=
    ComplCouplingHeat.seedLamP_jet2_bounds_of κ (seedLamPJet2Decay_all κ) hκ
  obtain ⟨C_g, D_g, _hCg, hDg, hG⟩ :=
    ComplCouplingHeat.hasDerivWithinAt_perGram_inv_clockA κ hCD h1
  refine ⟨D_g, hDg, fun {ν r} hν hr hd i y => ?_⟩
  obtain ⟨G_inv', hG_der, -⟩ := hG hν hr hd i
  have ht := fun j => ComplCouplingHeat.translate_jet2_bounds (h0 j) (h1 j) (h2 j)
  have h := ComplCouplingHeat.movLamDualHeat_split_of κ hν hr i hCD (fun j => (ht j).1)
    (fun j => (ht j).2.1) (fun j => (ht j).2.2) hG_der y
  rw [h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [(hG_der j).derivWithin (uniqueDiffWithinAt_Ici r)]

theorem le_cellLen_of {ν r D b : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hr : 0 ≤ r) (hD : 0 ≤ D)
    (hb : D ^ 2 ≤ b) (hbr : b ≤ clockTheta ν r) :
    D ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) := by
  have hθ : 0 < clockTheta ν r := theta_pos hν hr
  have ha0 : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le hr)
  have hd0 : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν r) :=
    div_pos (Real.rpow_pos_of_pos hν _) (Real.sqrt_pos.2 ha0)
  have h := inv_cellLen_sq_eq_nu_cube_div_theta hν hr
  set d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r) with hd_def
  have hν3 : ν ^ 3 ≤ 1 := pow_le_one₀ hν.le hν1
  have hd2 : clockTheta ν r ≤ d ^ 2 := by
    have hd2pos : 0 < d ^ 2 := by positivity
    have h' : clockTheta ν r = ν ^ 3 * d ^ 2 := by
      field_simp at h
      linarith
    rw [h']
    nlinarith
  nlinarith

/-! ### Joint measurability of the ingredients -/

theorem measurable_dRho_fst {ν t₁ t₂ : ℝ} (hν : 0 < ν) (ht : 0 ≤ t₁) :
    Measurable (fun a : ℝ × (ℝ × ℝ) => dRho ν t₁ t₂ a.1) :=
  ((continuous_dRho hν ht).comp continuous_fst).measurable

theorem measurable_pair_sub {ν t₁ t₂ : ℝ} (hν : 0 < ν) (ht : 0 ≤ t₁) :
    Measurable (fun q : (ℝ × (ℝ × ℝ)) × (ℝ × ℝ) =>
      ((dRho ν t₁ t₂ q.1.1, q.1.2 - q.2) : ℝ × (ℝ × ℝ))) := by
  have hD : Measurable (fun a : ℝ × (ℝ × ℝ) => dRho ν t₁ t₂ a.1) :=
    measurable_dRho_fst hν ht
  have h2 : Measurable (fun q : (ℝ × (ℝ × ℝ)) × (ℝ × ℝ) => q.1.2 - q.2) := by fun_prop
  exact (hD.comp measurable_fst).prodMk h2

theorem measurable_kerD_pair {ν t₁ t₂ : ℝ} (hν : 0 < ν) (ht : 0 ≤ t₁) (k : Fin 2) :
    Measurable (fun q : (ℝ × (ℝ × ℝ)) × (ℝ × ℝ) =>
      kerD (dRho ν t₁ t₂ q.1.1) (q.1.2 - q.2) k) := by
  have := (measurable_kerD_joint k).comp (measurable_pair_sub (t₂ := t₂) hν ht)
  exact this

theorem measurable_kerVelCx_integrand {ν t₁ t₂ : ℝ} (hν : 0 < ν) (ht : 0 ≤ t₁)
    {W : ℝ × ℝ → ℂ} (hW : Measurable W) (k : Fin 2) :
    Measurable (fun q : (ℝ × (ℝ × ℝ)) × (ℝ × ℝ) =>
      W q.2 * ((kerD (dRho ν t₁ t₂ q.1.1) (q.1.2 - q.2) k : ℝ) : ℂ)) := by
  have h3 := measurable_kerD_pair (t₂ := t₂) hν ht k
  have h4 : Measurable (fun q : (ℝ × (ℝ × ℝ)) × (ℝ × ℝ) =>
      ((kerD (dRho ν t₁ t₂ q.1.1) (q.1.2 - q.2) k : ℝ) : ℂ)) := Complex.measurable_ofReal.comp h3
  have h5 : Measurable (fun q : (ℝ × (ℝ × ℝ)) × (ℝ × ℝ) => W q.2) := hW.comp measurable_snd
  exact h5.mul h4

theorem measurable_kerVelCx_joint {ν t₁ t₂ : ℝ} (hν : 0 < ν) (ht : 0 ≤ t₁)
    {W : ℝ × ℝ → ℂ} (hW : Measurable W) (k : Fin 2) :
    Measurable (fun p : ℝ × (ℝ × ℝ) => kerVelCx (dRho ν t₁ t₂ p.1) W p.2 k) := by
  have hD : Measurable (fun a : ℝ × (ℝ × ℝ) => dRho ν t₁ t₂ a.1) := measurable_dRho_fst hν ht
  exact measurable_setIntegral_cell (fun a : ℝ × (ℝ × ℝ) => dRho ν t₁ t₂ a.1) hD
    (fun q : (ℝ × (ℝ × ℝ)) × (ℝ × ℝ) =>
      W q.2 * ((kerD (dRho ν t₁ t₂ q.1.1) (q.1.2 - q.2) k : ℝ) : ℂ))
    (measurable_kerVelCx_integrand hν ht hW k)

theorem measurable_movLInt_joint {ν t₁ t₂ : ℝ} (hν : 0 < ν) (ht : 0 ≤ t₁)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) {W : ℝ × ℝ → ℂ} (hW : Measurable W) :
    Measurable (fun p : ℝ × (ℝ × ℝ) => movLInt tr (rho t₁ t₂ p.1) W p.2) := by
  have h0 := measurable_kerVelCx_joint (t₂ := t₂) hν ht hW 0
  have h1 := measurable_kerVelCx_joint (t₂ := t₂) hν ht hW 1
  have g0 := Complex.measurable_ofReal.comp (measurable_movingTrainGradE (t₂ := t₂) tr ht 0)
  have g1 := Complex.measurable_ofReal.comp (measurable_movingTrainGradE (t₂ := t₂) tr ht 1)
  exact ((h0.mul g0).add (h1.mul g1)).neg

theorem measurable_pdCx_perLam_joint {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ)
    {ν t₁ t₂ : ℝ} (hν : 0 < ν) (ht : 0 ≤ t₁) (hts : t₁ ≤ t₂)
    (hd1 : ∀ r ∈ Icc t₁ t₂, 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
    (hdet : ∀ r ∈ Icc t₁ t₂, (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))).det ≠ 0)
    (i k : Fin 2) :
    Measurable (fun p : ℝ × (ℝ × ℝ) => pdCx k (perLam κ (dRho ν t₁ t₂ p.1) i) p.2) := by
  obtain ⟨hCD, C, hC0, h0, h1, -⟩ :=
    ComplCouplingHeat.seedLamP_jet2_bounds_of κ (seedLamPJet2Decay_all κ) hκ
  have hL : ∀ j, Differentiable ℝ (κ.lamP j) := fun j => (hCD j).differentiable (by norm_num)
  have h1' : ∀ (j : Fin 2) (z : ℝ × ℝ),
      ‖fderiv ℝ (κ.lamP j) z‖ ≤ C * ((1 + |z.1| + |z.2|)⁻¹) ^ 2 := by
    intro j z
    have h := h1 j z
    have hn : 0 ≤ ‖fderiv ℝ (κ.lamP j) z‖ := norm_nonneg _
    have hz : 0 ≤ ‖z‖ := norm_nonneg _
    nlinarith
  have hdir : ‖B0579.dir k‖ ≤ 1 := by
    fin_cases k <;> simp [B0579.dir]
  have hcont : ∀ j, Continuous (pdCx k (κ.lamP j)) := fun j => by
    unfold pdCx
    exact ((hCD j).continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdec : ∀ (j : Fin 2) (z : ℝ × ℝ), ‖pdCx k (κ.lamP j) z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)) := by
    intro j z
    unfold pdCx
    calc ‖fderiv ℝ (κ.lamP j) z (B0579.dir k)‖
        ≤ ‖fderiv ℝ (κ.lamP j) z‖ * ‖B0579.dir k‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖fderiv ℝ (κ.lamP j) z‖ * 1 := mul_le_mul_of_nonneg_left hdir (norm_nonneg _)
      _ ≤ C * ((1 + |z.1| + |z.2|)⁻¹) ^ 2 := by rw [mul_one]; exact h1' j z
      _ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (EulerSubCore.inv_sq_le_rpow _ _) hC0
  have hps : ∀ j, Measurable (fun p : ℝ × (ℝ × ℝ) =>
      perSum (dRho ν t₁ t₂ p.1) (pdCx k (κ.lamP j)) p.2) :=
    fun j => measurable_perSum_joint (hcont j) hC0 (hdec j) hν ht hts hd1
  have heq : (fun p : ℝ × (ℝ × ℝ) => pdCx k (perLam κ (dRho ν t₁ t₂ p.1) i) p.2) =
      fun p => ∑ j : Fin 2, (perGram κ (dRho ν t₁ t₂ p.1))⁻¹ i j *
        perSum (dRho ν t₁ t₂ p.1) (pdCx k (κ.lamP j)) p.2 := by
    funext p
    have hd0 : dRho ν t₁ t₂ p.1 ≠ 0 := by
      have := hd1 _ (rho_mem hts p.1)
      exact (lt_of_lt_of_le zero_lt_one this).ne'
    have hdiff : ∀ j, DifferentiableAt ℝ (perLam0 κ (dRho ν t₁ t₂ p.1) j) p.2 := fun j =>
      (CutFTCGradPerSum.hasFDerivAt_perSum_of_inv_sq_decay (hL j) hd0 (h0 j) (h1' j)
        p.2).differentiableAt
    rw [CutFTCAux.pdCx_perLam_eq κ _ i k p.2 (hdiff 0) (hdiff 1)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show perLam0 κ (dRho ν t₁ t₂ p.1) j = perSum (dRho ν t₁ t₂ p.1) (κ.lamP j) from rfl,
      CutFTCGradPerSum.pdCx_perSum_eq_perSum_pdCx (hL j) hd0 (h0 j) (h1' j) k p.2]
  rw [heq]
  refine Finset.measurable_sum _ fun j _ => ?_
  have hG : Measurable (fun p : ℝ × (ℝ × ℝ) => (perGram κ (dRho ν t₁ t₂ p.1))⁻¹ i j) :=
    (measurable_Ginv hν ht hts hd1 hdet i j).comp measurable_fst
  exact hG.mul (hps j)

theorem measurable_kerAdjPart_joint {κ : PlanarFrameKernels}
    {ν t₁ t₂ : ℝ} (hν : 0 < ν) (ht : 0 ≤ t₁) (hts : t₁ ≤ t₂)
    (hd1 : ∀ r ∈ Icc t₁ t₂, 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
    (hdet : ∀ r ∈ Icc t₁ t₂, (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))).det ≠ 0)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (i : Fin 2) :
    Measurable (fun p : ℝ × (ℝ × ℝ) => kerAdj (dRho ν t₁ t₂ p.1)
      (fun k w => perLam κ (dRho ν t₁ t₂ p.1) i w *
        (B0579.pd k (movingTrainE tr (rho t₁ t₂ p.1)) w : ℂ)) p.2) := by
  have hr0 : ∀ r, 0 ≤ rho t₁ t₂ r := fun r => ht.trans (le_max_left _ _)
  have heq : (fun p : ℝ × (ℝ × ℝ) => kerAdj (dRho ν t₁ t₂ p.1)
      (fun k w => perLam κ (dRho ν t₁ t₂ p.1) i w *
        (B0579.pd k (movingTrainE tr (rho t₁ t₂ p.1)) w : ℂ)) p.2) =
      fun p => ∫ w in B0579.cell (dRho ν t₁ t₂ p.1), ∑ k : Fin 2,
        perLam κ (dRho ν t₁ t₂ p.1) i w * ((movingTrainGradE tr (rho t₁ t₂ p.1) w k : ℝ) : ℂ) *
          ((kerD (dRho ν t₁ t₂ p.1) (w - p.2) k : ℝ) : ℂ) := by
    funext p
    unfold kerAdj
    congr 1
    funext w
    simp only [DirectEulerSub.pd_movingTrainE_eq_movingTrainGradE tr hν (hr0 p.1)]
  rw [heq]
  have hD := measurable_dRho_fst (t₂ := t₂) hν ht
  refine measurable_setIntegral_cell (fun a : ℝ × (ℝ × ℝ) => dRho ν t₁ t₂ a.1) hD
    (fun q : (ℝ × (ℝ × ℝ)) × (ℝ × ℝ) => ∑ k : Fin 2,
      perLam κ (dRho ν t₁ t₂ q.1.1) i q.2 * ((movingTrainGradE tr (rho t₁ t₂ q.1.1) q.2 k : ℝ) : ℂ) *
        ((kerD (dRho ν t₁ t₂ q.1.1) (q.2 - q.1.2) k : ℝ) : ℂ)) ?_
  refine Finset.measurable_sum _ fun k _ => ?_
  have hpr : Measurable (fun q : (ℝ × (ℝ × ℝ)) × (ℝ × ℝ) => (q.1.1, q.2)) := by fun_prop
  have hPL := (measurable_perLam_joint hν ht hts hd1 hdet i).comp hpr
  have hG := (Complex.measurable_ofReal.comp (measurable_movingTrainGradE (t₂ := t₂) tr ht k)).comp
    hpr
  have hK := Complex.measurable_ofReal.comp ((measurable_kerD_joint k).comp
    ((hD.comp measurable_fst).prodMk (by fun_prop :
      Measurable (fun q : (ℝ × (ℝ × ℝ)) × (ℝ × ℝ) => q.2 - q.1.2))))
  exact (hPL.mul hG).mul hK

theorem measurable_movLamDual_joint {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ)
    {ν t₁ t₂ : ℝ} (hν : 0 < ν) (ht : 0 ≤ t₁) (hts : t₁ ≤ t₂)
    (hd1 : ∀ r ∈ Icc t₁ t₂, 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
    (hdet : ∀ r ∈ Icc t₁ t₂, (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))).det ≠ 0)
    (hform : ∀ r ∈ Icc t₁ t₂, HeatFormula κ ν r)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (i : Fin 2) :
    Measurable (fun p : ℝ × (ℝ × ℝ) => movLamDual κ tr (rho t₁ t₂ p.1) i p.2) := by
  obtain ⟨Ψ, C_d, hCd, hΨc, hΨb, hΨeq⟩ := seedLamPDSharpDecay κ hκ
  have hr0 : ∀ r, 0 ≤ rho t₁ t₂ r := fun r => ht.trans (le_max_left _ _)
  have hrm : ∀ r, rho t₁ t₂ r ∈ Icc t₁ t₂ := rho_mem hts
  have hrhoM : Measurable (fun p : ℝ × (ℝ × ℝ) => rho t₁ t₂ p.1) :=
    ((continuous_rho t₁ t₂).comp continuous_fst).measurable
  -- heat part
  have hheat : Measurable (fun p : ℝ × (ℝ × ℝ) => movLamDualHeat κ ν (rho t₁ t₂ p.1) i p.2) := by
    have heq : (fun p : ℝ × (ℝ × ℝ) => movLamDualHeat κ ν (rho t₁ t₂ p.1) i p.2) =
        fun p => ∑ j : Fin 2, ((perGram κ (dRho ν t₁ t₂ p.1))⁻¹ i j *
            (((clockTheta ν (rho t₁ t₂ p.1) : ℝ) : ℂ)⁻¹ * perSum (dRho ν t₁ t₂ p.1) (Ψ j) p.2) +
          (((clockA ν (rho t₁ t₂ p.1) ^ 2 : ℝ)) : ℂ) *
            derivWithin (fun s => (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)))⁻¹ i j)
              (Ici (rho t₁ t₂ p.1)) (rho t₁ t₂ p.1) *
            perLam0 κ (dRho ν t₁ t₂ p.1) j p.2) := by
      funext p
      rw [hform _ (hrm p.1) i p.2]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hΨeq hν (hr0 p.1) (hd1 _ (hrm p.1)) j p.2]
    rw [heq]
    refine Finset.measurable_sum _ fun j _ => ?_
    have hG : Measurable (fun p : ℝ × (ℝ × ℝ) => (perGram κ (dRho ν t₁ t₂ p.1))⁻¹ i j) :=
      (measurable_Ginv hν ht hts hd1 hdet i j).comp measurable_fst
    have hθ : Measurable (fun p : ℝ × (ℝ × ℝ) => ((clockTheta ν (rho t₁ t₂ p.1) : ℝ) : ℂ)⁻¹) := by
      have : Measurable (fun p : ℝ × (ℝ × ℝ) => clockTheta ν (rho t₁ t₂ p.1)) := by
        unfold clockTheta clockA
        exact (measurable_const.mul (measurable_const.add (measurable_const.mul hrhoM))).inv
      exact (Complex.measurable_ofReal.comp this).inv
    have hPS := measurable_perSum_joint (hΨc j) hCd
      (fun z => (hΨb j z).trans (mul_le_mul_of_nonneg_left (EulerSubCore.inv_sq_le_rpow _ _) hCd))
      hν ht hts hd1
    have ha2 : Measurable (fun p : ℝ × (ℝ × ℝ) => (((clockA ν (rho t₁ t₂ p.1) ^ 2 : ℝ)) : ℂ)) := by
      unfold clockA
      exact Complex.measurable_ofReal.comp ((measurable_const.add (measurable_const.mul hrhoM)).pow_const 2)
    have hder : Measurable (fun p : ℝ × (ℝ × ℝ) =>
        derivWithin (fun s => (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)))⁻¹ i j)
          (Ici (rho t₁ t₂ p.1)) (rho t₁ t₂ p.1)) :=
      (measurable_derivWithin_Ici
        (fun s => (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)))⁻¹ i j)).comp hrhoM
    have hL0 := measurable_perLam0_joint (κ := κ) hν ht hts hd1 j
    exact (hG.mul (hθ.mul hPS)).add ((ha2.mul hder).mul hL0)
  -- Euler part
  have heul : Measurable (fun p : ℝ × (ℝ × ℝ) =>
      (((clockA ν (rho t₁ t₂ p.1)) ^ (2 : ℝ) : ℝ) : ℂ) *
        movingPhi ν (fun r' => physLamDualEuler κ tr r' i) (rho t₁ t₂ p.1) p.2) := by
    have heq : (fun p : ℝ × (ℝ × ℝ) => (((clockA ν (rho t₁ t₂ p.1)) ^ (2 : ℝ) : ℝ) : ℂ) *
        movingPhi ν (fun r' => physLamDualEuler κ tr r' i) (rho t₁ t₂ p.1) p.2) =
        fun p => (((movingTrainV tr (rho t₁ t₂ p.1) p.2 0 : ℝ) : ℂ) *
            pdCx 0 (perLam κ (dRho ν t₁ t₂ p.1) i) p.2 +
          ((movingTrainV tr (rho t₁ t₂ p.1) p.2 1 : ℝ) : ℂ) *
            pdCx 1 (perLam κ (dRho ν t₁ t₂ p.1) i) p.2) -
          kerAdj (dRho ν t₁ t₂ p.1) (fun k w => perLam κ (dRho ν t₁ t₂ p.1) i w *
            (B0579.pd k (movingTrainE tr (rho t₁ t₂ p.1)) w : ℂ)) p.2 := by
      funext p
      rw [ComplCouplingEuler.movPullback_physLamDualEuler_eq κ tr hν (hr0 p.1) i p.2]
      rfl
    rw [heq]
    have hV0 := Complex.measurable_ofReal.comp (measurable_movingTrainV (t₂ := t₂) tr ht 0)
    have hV1 := Complex.measurable_ofReal.comp (measurable_movingTrainV (t₂ := t₂) tr ht 1)
    exact ((hV0.mul (measurable_pdCx_perLam_joint hκ hν ht hts hd1 hdet i 0)).add
      (hV1.mul (measurable_pdCx_perLam_joint hκ hν ht hts hd1 hdet i 1))).sub
      (measurable_kerAdjPart_joint hν ht hts hd1 hdet tr i)
  have heq : (fun p : ℝ × (ℝ × ℝ) => movLamDual κ tr (rho t₁ t₂ p.1) i p.2) =
      fun p => movLamDualHeat κ ν (rho t₁ t₂ p.1) i p.2 +
        (((clockA ν (rho t₁ t₂ p.1)) ^ (2 : ℝ) : ℝ) : ℂ) *
          movingPhi ν (fun r' => physLamDualEuler κ tr r' i) (rho t₁ t₂ p.1) p.2 :=
    funext fun p => movLamDual_eq_heat_add_euler κ tr _ i p.2
  rw [heq]
  exact hheat.add heul

end UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit.RelIntA
