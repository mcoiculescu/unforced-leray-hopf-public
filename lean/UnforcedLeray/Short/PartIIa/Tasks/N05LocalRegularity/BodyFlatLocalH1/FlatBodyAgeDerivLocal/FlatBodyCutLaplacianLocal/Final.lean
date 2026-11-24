import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.BodyFlatLocalH1.FlatBodyAgeDerivLocal.FlatBodyCutLaplacianLocal.Assemble

/-!
# `PartII-a:N05/2/2/1`: `FlatBodyCutLaplacianLocal` from the cylinder heat estimate

Source: `the November 2 reference manuscript`, lines 1794-1799.
`flatBodyCutLaplacianLocal_of` : `CylHeatMaxRegL → FlatBodyCutLaplacianLocal`, with `k_L = 6`,
`C_L = 4 C₀ (8 + 6 M₀)`. The localized term is `S_lap = s χ L̃`, `L = ν(∂_q² + ∂_η²)w` assembled
from the weak second derivatives of the cylinder estimate, `L̃` its periodic extension.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal ContDiff InnerProductSpace ComplexConjugate

namespace UnforcedLeray.Short.PartIIa.FBCLL

open UnforcedLeray.B0220 (HSpace measureH Profile cellMeasure cell periodize QPeriodic
  periodize_of_mem)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIa (IsMeridTest pdS pdQ pdEta IsNearCutoff IsLargerCutoff Gamma
  GammaBox cNorm8 cNorm8_nonneg T0flat PepsC dsFromS cellL2Norm FlatBodyCutLaplacianLocal
  flatStressCutRep)
open UnforcedLeray.Short.PartIIa.N05_2_2Aux (flatCutAgeDriftTerm flatCutAgeForceTerm)
open UnforcedLeray.Short.IIb (Coord cpd cdir qShift)

theorem continuous_vecOf (i : Fin 2) {h : Profile → ℝ} (hh : Continuous h) :
    Continuous (vecOf i h) :=
  hh.smul continuous_const

theorem inner_eVec_norm (i : Fin 2) : ‖eVec i‖ = 1 := by
  rw [eVec, EuclideanSpace.norm_single, norm_one]

theorem gamma_parts {ν c σ H1 L1 M γs : ℝ} (χ χ1 : Profile → ℝ) (hν : 0 < ν) (hc : 0 < c)
    (hσ : 0 < σ) (hσH : σ ≤ H1) (hL1 : 0 ≤ L1) (hγ : 0 < γs) (hM : 0 ≤ M) :
    1 ≤ Gamma ν c σ H1 L1 M γs χ χ1 ∧ σ⁻¹ ≤ Gamma ν c σ H1 L1 M γs χ χ1 ∧
      1 + H1 ≤ Gamma ν c σ H1 L1 M γs χ χ1 ∧ M ≤ Gamma ν c σ H1 L1 M γs χ χ1 ∧
      cNorm8 χ ≤ Gamma ν c σ H1 L1 M γs χ χ1 := by
  have hνi : 0 < ν⁻¹ := inv_pos.2 hν
  have hci : 0 < c⁻¹ := inv_pos.2 hc
  have hσi : 0 < σ⁻¹ := inv_pos.2 hσ
  have hγi : 0 < γs⁻¹ := inv_pos.2 hγ
  have h1 := cNorm8_nonneg χ
  have h2 := cNorm8_nonneg χ1
  unfold Gamma GammaBox
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem final_bound {Γ H1 σ M0 C0 Bχ ng nV nb nμ : ℝ} (hΓ1 : 1 ≤ Γ) (hσ : 0 < σ)
    (hσΓ : σ⁻¹ ≤ Γ) (hH : 0 < H1) (hHΓ : 1 + H1 ≤ Γ) (hM0 : 0 ≤ M0) (hC0 : 0 ≤ C0)
    (hBχ0 : 0 ≤ Bχ) (hBχ : Bχ ≤ Γ) (hng0 : 0 ≤ ng) (hng : ng ≤ nb) (hnV0 : 0 ≤ nV)
    (hnV : nV ≤ Γ * nb) (hnμ0 : 0 ≤ nμ) (hnμ : nμ ≤ Γ) (hnb : 0 ≤ nb) :
    H1 * Bχ * (4 * (C0 * (2 / σ * (1 + 2 * H1) * ng + nμ * (2 / σ * (1 + 2 * H1) * nV) +
      3 * M0 / σ * (1 + 2 * H1) * nV))) ≤ 4 * C0 * (8 + 6 * M0) * Γ ^ 6 * nb := by
  have hΓ0 : 0 < Γ := by linarith
  have h2σ0 : 0 ≤ 2 / σ := by positivity
  have h3σ0 : 0 ≤ 3 * M0 / σ := by positivity
  have h2σ : 2 / σ ≤ 2 * Γ := by rw [div_eq_mul_inv]; linarith
  have h3σ : 3 * M0 / σ ≤ 3 * M0 * Γ := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hσΓ (by positivity)
  have h12H0 : 0 ≤ 1 + 2 * H1 := by linarith
  have h12H : 1 + 2 * H1 ≤ 2 * Γ := by linarith
  have hH1Γ : H1 ≤ Γ := by linarith
  have t1 : 2 / σ * (1 + 2 * H1) * ng ≤ 2 * Γ * (2 * Γ) * nb :=
    mul_le_mul (mul_le_mul h2σ h12H h12H0 (by linarith)) hng hng0 (by positivity)
  have t2 : nμ * (2 / σ * (1 + 2 * H1) * nV) ≤ Γ * (2 * Γ * (2 * Γ) * (Γ * nb)) :=
    mul_le_mul hnμ (mul_le_mul (mul_le_mul h2σ h12H h12H0 (by linarith)) hnV hnV0
      (by positivity)) (by positivity) hΓ0.le
  have t3 : 3 * M0 / σ * (1 + 2 * H1) * nV ≤ 3 * M0 * Γ * (2 * Γ) * (Γ * nb) :=
    mul_le_mul (mul_le_mul h3σ h12H h12H0 (by positivity)) hnV hnV0 (by positivity)
  have hΓ2 : Γ ^ 2 ≤ Γ ^ 4 := pow_le_pow_right₀ hΓ1 (by norm_num)
  have hΓ3 : Γ ^ 3 ≤ Γ ^ 4 := pow_le_pow_right₀ hΓ1 (by norm_num)
  have hKf : 2 / σ * (1 + 2 * H1) * ng + nμ * (2 / σ * (1 + 2 * H1) * nV) +
      3 * M0 / σ * (1 + 2 * H1) * nV ≤ (8 + 6 * M0) * Γ ^ 4 * nb := by
    have e : 2 * Γ * (2 * Γ) * nb + Γ * (2 * Γ * (2 * Γ) * (Γ * nb)) +
        3 * M0 * Γ * (2 * Γ) * (Γ * nb) =
        4 * Γ ^ 2 * nb + 4 * Γ ^ 4 * nb + 6 * M0 * Γ ^ 3 * nb := by ring
    have e2 : 4 * Γ ^ 2 * nb + 4 * Γ ^ 4 * nb + 6 * M0 * Γ ^ 3 * nb ≤
        (8 + 6 * M0) * Γ ^ 4 * nb := by
      have a1 : 4 * Γ ^ 2 * nb ≤ 4 * Γ ^ 4 * nb :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΓ2 (by norm_num)) hnb
      have a2 : 6 * M0 * Γ ^ 3 * nb ≤ 6 * M0 * Γ ^ 4 * nb :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΓ3 (by positivity)) hnb
      nlinarith
    linarith
  have hK0 : 0 ≤ 2 / σ * (1 + 2 * H1) * ng + nμ * (2 / σ * (1 + 2 * H1) * nV) +
      3 * M0 / σ * (1 + 2 * H1) * nV := by positivity
  calc H1 * Bχ * (4 * (C0 * (2 / σ * (1 + 2 * H1) * ng + nμ * (2 / σ * (1 + 2 * H1) * nV) +
      3 * M0 / σ * (1 + 2 * H1) * nV)))
      ≤ Γ * Γ * (4 * (C0 * ((8 + 6 * M0) * Γ ^ 4 * nb))) := by
        apply mul_le_mul (mul_le_mul hH1Γ hBχ hBχ0 hΓ0.le) _ (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hKf hC0) (by norm_num)
    _ = 4 * C0 * (8 + 6 * M0) * Γ ^ 6 * nb := by ring

theorem flatBodyCutLaplacianLocal_of (hC : CylHeatMaxRegL) : FlatBodyCutLaplacianLocal := by
  obtain ⟨C0, hC0pos, hC0⟩ := hC 2 (by norm_num)
  have hC0' : CylBound2 C0 := hC0
  obtain ⟨M0, hM0n, hM0⟩ := st_deriv_bound
  refine ⟨6, 4 * C0 * (8 + 6 * M0), by positivity, ?_⟩
  intro ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ hχ _hχ1 hm μ hμM hμγ b
  have hμ : 0 < μ.re + 1 / 4 := lt_of_lt_of_le hγ hμγ
  have hH : 0 < H1 := lt_of_lt_of_le hσ hσH
  set g : HSpace c MeridC := PepsC 0 c b with hgdef
  set V : HSpace c MeridC := UnforcedLeray.B0225.R0 hc ν μ g with hVdef
  have hTV : T0flat hc ν μ b = V := rfl
  rw [hTV]
  set Kf : ℝ := 2 / σ * (1 + 2 * H1) * ‖g‖ + ‖μ‖ * (2 / σ * (1 + 2 * H1) * ‖V‖) +
    3 * M0 / σ * (1 + 2 * H1) * ‖V‖ with hKfdef
  have hKf0 : 0 ≤ Kf := by positivity
  have hdata := fun i => cyl_data hC0pos hC0' hM0n hM0 hν hc hσ hσH hμ g i
  choose D hDpm hDw hDfin hDcell using hdata
  -- the assembled `ν Δ_{q,η} w`
  set LapN : Profile → MeridC := fun x =>
    ((ν : ℂ) * (D 0 0 x + D 0 1 x)) • eVec 0 + ((ν : ℂ) * (D 1 0 x + D 1 1 x)) • eVec 1
    with hLapNdef
  have hLapN_apply : ∀ x (i : Fin 2), LapN x i = (ν : ℂ) * (D i 0 x + D i 1 x) := by
    intro x i
    fin_cases i <;> simp [hLapNdef, eVec, EuclideanSpace.single_apply]
  have hLapNm : AEStronglyMeasurable LapN volume :=
    ((((hDpm 0 0).2.add (hDpm 0 1).2).const_mul (ν : ℂ)).smul_const (eVec 0)).add
      ((((hDpm 1 0).2.add (hDpm 1 1).2).const_mul (ν : ℂ)).smul_const (eVec 1))
  set S_lap : Profile → MeridC := fun p => (p.1 * χ p) • periodize c LapN p with hSdef
  have hS_cell : ∀ p ∈ cell c, S_lap p = (p.1 * χ p) • LapN p := fun p hp => by
    simp only [hSdef, periodize_of_mem hc _ hp]
  -- the box test `ψ = χ φ` will be handled below; first the norm of `S_lap`
  have habsχ : ∀ p, |p.1 * χ p| ≤ H1 * cNorm8 χ := by
    intro p
    by_cases h0 : χ p = 0
    · rw [h0, mul_zero, abs_zero]
      exact mul_nonneg hH.le (cNorm8_nonneg χ)
    · obtain ⟨a1, a2, -⟩ := hχ.support p h0
      rw [abs_mul, abs_of_pos (lt_of_lt_of_le hσ a1)]
      exact mul_le_mul a2 (UnforcedLeray.Short.PartIIa.N05_4Aux.abs_le_cNorm8_of_nearCutoff hc hχ p)
        (abs_nonneg _) hH.le
  set T : Profile → ℝ := fun p => ‖(ν : ℂ) * D 0 0 p‖ + ‖(ν : ℂ) * D 0 1 p‖ +
    ‖(ν : ℂ) * D 1 0 p‖ + ‖(ν : ℂ) * D 1 1 p‖ with hTdef
  have hLapN_norm : ∀ p, ‖LapN p‖ ≤ T p := by
    intro p
    calc ‖LapN p‖ ≤ ‖((ν : ℂ) * (D 0 0 p + D 0 1 p)) • eVec 0‖ +
          ‖((ν : ℂ) * (D 1 0 p + D 1 1 p)) • eVec 1‖ := norm_add_le _ _
      _ = ‖(ν : ℂ) * D 0 0 p + (ν : ℂ) * D 0 1 p‖ + ‖(ν : ℂ) * D 1 0 p + (ν : ℂ) * D 1 1 p‖ := by
          rw [norm_smul, norm_smul, inner_eVec_norm, inner_eVec_norm, mul_one, mul_one, mul_add,
            mul_add]
      _ ≤ T p := by
          simp only [hTdef]
          linarith [norm_add_le ((ν : ℂ) * D 0 0 p) ((ν : ℂ) * D 0 1 p),
            norm_add_le ((ν : ℂ) * D 1 0 p) ((ν : ℂ) * D 1 1 p)]
  have hmc : ∀ i j, AEStronglyMeasurable (fun x => (ν : ℂ) * D i j x) (cellMeasure c) :=
    fun i j => ((hDpm i j).2.const_mul _).mono_measure Measure.restrict_le_self
  have hT : eLpNorm T 2 (cellMeasure c) ≤ ENNReal.ofReal (4 * (C0 * Kf)) := by
    have e : ∀ i j, eLpNorm (fun p => ‖(ν : ℂ) * D i j p‖) 2 (cellMeasure c) ≤
        ENNReal.ofReal (C0 * Kf) := fun i j => by
      rw [eLpNorm_norm]
      exact hDcell i j
    calc eLpNorm T 2 (cellMeasure c)
        ≤ eLpNorm (fun p => ‖(ν : ℂ) * D 0 0 p‖ + ‖(ν : ℂ) * D 0 1 p‖ +
            ‖(ν : ℂ) * D 1 0 p‖) 2 (cellMeasure c) +
          eLpNorm (fun p => ‖(ν : ℂ) * D 1 1 p‖) 2 (cellMeasure c) :=
          eLpNorm_add_le ((((hmc 0 0).norm).add (hmc 0 1).norm).add (hmc 1 0).norm)
            (hmc 1 1).norm (by norm_num)
      _ ≤ (eLpNorm (fun p => ‖(ν : ℂ) * D 0 0 p‖ + ‖(ν : ℂ) * D 0 1 p‖) 2 (cellMeasure c) +
            eLpNorm (fun p => ‖(ν : ℂ) * D 1 0 p‖) 2 (cellMeasure c)) +
          eLpNorm (fun p => ‖(ν : ℂ) * D 1 1 p‖) 2 (cellMeasure c) := by
          gcongr
          exact eLpNorm_add_le (((hmc 0 0).norm).add (hmc 0 1).norm) (hmc 1 0).norm (by norm_num)
      _ ≤ ((eLpNorm (fun p => ‖(ν : ℂ) * D 0 0 p‖) 2 (cellMeasure c) +
            eLpNorm (fun p => ‖(ν : ℂ) * D 0 1 p‖) 2 (cellMeasure c)) +
            eLpNorm (fun p => ‖(ν : ℂ) * D 1 0 p‖) 2 (cellMeasure c)) +
          eLpNorm (fun p => ‖(ν : ℂ) * D 1 1 p‖) 2 (cellMeasure c) := by
          gcongr
          exact eLpNorm_add_le (hmc 0 0).norm (hmc 0 1).norm (by norm_num)
      _ ≤ ((ENNReal.ofReal (C0 * Kf) + ENNReal.ofReal (C0 * Kf)) + ENNReal.ofReal (C0 * Kf)) +
          ENNReal.ofReal (C0 * Kf) := by
          gcongr <;> exact e _ _
      _ = ENNReal.ofReal (4 * (C0 * Kf)) := by
          have h0 : 0 ≤ C0 * Kf := mul_nonneg hC0pos.le hKf0
          rw [← ENNReal.ofReal_add h0 h0, ← ENNReal.ofReal_add (by positivity) h0,
            ← ENNReal.ofReal_add (by positivity) h0]
          congr 1
          ring
  have hS_ae : S_lap =ᵐ[cellMeasure c] fun p => (p.1 * χ p) • LapN p := by
    filter_upwards [ae_mem_cell c] with p hp
    exact hS_cell p hp
  have hSm : AEStronglyMeasurable (fun p => (p.1 * χ p) • LapN p) (cellMeasure c) :=
    ((measurable_fst.mul hm).aestronglyMeasurable.smul hLapNm).mono_measure
      Measure.restrict_le_self
  have hS_eL : eLpNorm S_lap 2 (cellMeasure c) ≤
      ENNReal.ofReal (H1 * cNorm8 χ * (4 * (C0 * Kf))) := by
    rw [eLpNorm_congr_ae hS_ae]
    have hle : ∀ᵐ p ∂(cellMeasure c), ‖(p.1 * χ p) • LapN p‖ ≤ (H1 * cNorm8 χ) * ‖T p‖ := by
      refine Eventually.of_forall fun p => ?_
      have hTn : 0 ≤ T p := by simp only [hTdef]; positivity
      rw [norm_smul, Real.norm_eq_abs, Real.norm_of_nonneg hTn]
      exact mul_le_mul (habsχ p) (hLapN_norm p) (norm_nonneg _)
        (mul_nonneg hH.le (cNorm8_nonneg χ))
    calc eLpNorm (fun p => (p.1 * χ p) • LapN p) 2 (cellMeasure c)
        ≤ ENNReal.ofReal (H1 * cNorm8 χ) * eLpNorm T 2 (cellMeasure c) :=
          eLpNorm_le_mul_eLpNorm_of_ae_le_mul hle 2
      _ ≤ ENNReal.ofReal (H1 * cNorm8 χ) * ENNReal.ofReal (4 * (C0 * Kf)) := by gcongr
      _ = ENNReal.ofReal (H1 * cNorm8 χ * (4 * (C0 * Kf))) :=
          (ENNReal.ofReal_mul (mul_nonneg hH.le (cNorm8_nonneg χ))).symm
  have hSmem : MemLp S_lap 2 (cellMeasure c) :=
    ⟨hSm.congr hS_ae.symm, lt_of_le_of_lt hS_eL ENNReal.ofReal_lt_top⟩
  refine ⟨S_lap, ?_, ?_, hSmem, ?_, ?_⟩
  · intro p
    simp only [hSdef]
    rw [hχ.periodic p, UnforcedLeray.B0220.qPeriodic_periodize hc LapN p]
  · intro p hp
    refine hχ.support p fun h0 => hp ?_
    simp [hSdef, h0]
  · intro φ hφ
    set ψ : Profile → MeridC := fun q => χ q • φ q with hψdef
    have hψp : ∀ p, ψ p = χ p • φ p := fun p => rfl
    have hψband : ∀ p, ψ p ≠ 0 → p.1 ∈ Icc σ H1 ∧ |p.2.2| ≤ L1 := by
      intro p hp
      have h0 : χ p ≠ 0 := fun h => hp (by rw [hψp, h, zero_smul])
      obtain ⟨a1, a2, a3⟩ := hχ.support p h0
      exact ⟨⟨a1, a2⟩, a3⟩
    have hψ : IsMeridTest c ψ :=
      ⟨hχ.smooth.smul hφ.smooth, fun p => by simp only [hψdef, hχ.periodic p, hφ.periodic p],
        ⟨σ, H1, L1, hσ, hψband⟩⟩
    -- the scalar relations for `LapN = ν Δ w`
    have hrelN : ∀ (i : Fin 2) (a : Profile → ℝ), ContDiff ℝ ∞ a → QPeriodic c a →
        (∀ p, a p ≠ 0 → p.1 ∈ Icc σ H1 ∧ |p.2.2| ≤ L1) →
        Integrable (fun x => (a x : ℂ) * LapN x i) (cellMeasure c) ∧
          Integrable (fun x => (lapR a x : ℂ) * ((ν : ℝ) • (V : Profile → MeridC) x) i)
            (cellMeasure c) ∧
          ∫ x, (a x : ℂ) * LapN x i ∂(cellMeasure c) =
            ∫ x, (lapR a x : ℂ) * ((ν : ℝ) • (V : Profile → MeridC) x) i ∂(cellMeasure c) := by
      intro i a has hper hband
      obtain ⟨hi0, he0⟩ := cell_rel hc hσ hσH V i 0 (hDpm i 0).1 (hDpm i 0).2 (hDfin i 0)
        (hDw i 0) has hper hband
      obtain ⟨hi1, he1⟩ := cell_rel hc hσ hσH V i 1 (hDpm i 1).1 (hDpm i 1).2 (hDfin i 1)
        (hDw i 1) has hper hband
      have hOneK : ∀ s ∈ Icc σ H1, |(fun _ : ℝ => (1 : ℝ)) s| ≤ 1 := fun s _ => by simp
      have hint2 : ∀ j : Fin 3, Integrable (fun x => ((cpd j (fun y => cpd j a y) x : ℝ) : ℂ) *
          (V : Profile → MeridC) x i) (cellMeasure c) := by
        intro j
        have hc2 : Continuous (fun x => cpd j (fun y => cpd j a y) x) :=
          (cpd_contDiff (cpd_contDiff has j) j).continuous
        have hb2 : ∀ p, cpd j (fun y => cpd j a y) p ≠ 0 → p.1 ∈ Icc σ H1 ∧ |p.2.2| ≤ L1 :=
          band_fderiv (band_fderiv hband _) _
        have := integrable_inner_band (c := c) V
          (continuous_vecOf i hc2)
          (fun p hp => hb2 p fun h0 => hp (by simp [vecOf, h0])) measurable_const hOneK
        refine this.congr (Eventually.of_forall fun p => ?_)
        simp only [inner_vecOf, one_smul]
      have hlapR : ∀ x, ((lapR a x : ℝ) : ℂ) * ((ν : ℝ) • (V : Profile → MeridC) x) i =
          (ν : ℂ) * (((cpd 1 (fun y => cpd 1 a y) x : ℝ) : ℂ) * (V : Profile → MeridC) x i +
            ((cpd 2 (fun y => cpd 2 a y) x : ℝ) : ℂ) * (V : Profile → MeridC) x i) := by
        intro x
        rw [smul_apply_real, show lapR a x = cpd 1 (fun y => cpd 1 a y) x +
          cpd 2 (fun y => cpd 2 a y) x from rfl]
        push_cast
        ring
      have he0' : ∫ x, (a x : ℂ) * D i 0 x ∂(cellMeasure c) =
          ∫ x, ((cpd 1 (fun y => cpd 1 a y) x : ℝ) : ℂ) * (V : Profile → MeridC) x i
            ∂(cellMeasure c) := he0
      have he1' : ∫ x, (a x : ℂ) * D i 1 x ∂(cellMeasure c) =
          ∫ x, ((cpd 2 (fun y => cpd 2 a y) x : ℝ) : ℂ) * (V : Profile → MeridC) x i
            ∂(cellMeasure c) := he1
      refine ⟨?_, ?_, ?_⟩
      · refine ((hi0.add hi1).const_mul (ν : ℂ)).congr (Eventually.of_forall fun x => ?_)
        simp only [Pi.add_apply, hLapN_apply]
        ring
      · refine (((hint2 1).add (hint2 2)).const_mul (ν : ℂ)).congr
          (Eventually.of_forall fun x => ?_)
        simp only [Pi.add_apply]
        rw [hlapR]
      · have hL : ∫ x, (a x : ℂ) * LapN x i ∂(cellMeasure c) = (ν : ℂ) *
            ((∫ x, (a x : ℂ) * D i 0 x ∂(cellMeasure c)) +
              ∫ x, (a x : ℂ) * D i 1 x ∂(cellMeasure c)) := by
          rw [← integral_add hi0 hi1, ← integral_const_mul]
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          simp only [hLapN_apply]
          ring
        have hR : ∫ x, (lapR a x : ℂ) * ((ν : ℝ) • (V : Profile → MeridC) x) i ∂(cellMeasure c) =
            (ν : ℂ) * ((∫ x, ((cpd 1 (fun y => cpd 1 a y) x : ℝ) : ℂ) * (V : Profile → MeridC) x i
              ∂(cellMeasure c)) + ∫ x, ((cpd 2 (fun y => cpd 2 a y) x : ℝ) : ℂ) *
                (V : Profile → MeridC) x i ∂(cellMeasure c)) := by
          rw [← integral_add (hint2 1) (hint2 2), ← integral_const_mul]
          exact integral_congr_ae (Eventually.of_forall fun x => hlapR x)
        rw [hL, hR, he0', he1']
    have hcell := cell_rel_inner (Lp := LapN) (Vf := fun x => (ν : ℝ) • (V : Profile → MeridC) x)
      hrelN hψ.smooth hψ.periodic hψband
    have hw := weak_cell hc hν hμ g hψ
    rw [← hVdef] at hw
    -- integrability of the pairings
    have hOneK : ∀ s ∈ Icc σ H1, |(fun _ : ℝ => (1 : ℝ)) s| ≤ 1 := fun s _ => by simp
    have hInvK : ∀ s ∈ Icc σ H1, |s⁻¹| ≤ σ⁻¹ := by
      intro s hs
      have hs' : 0 < s := lt_of_lt_of_le hσ hs.1
      rw [abs_inv, abs_of_pos hs']
      exact inv_anti₀ hσ hs.1
    have hbS : ∀ p, pdS ψ p ≠ 0 → p.1 ∈ Icc σ H1 ∧ |p.2.2| ≤ L1 := fun p hp =>
      band_fderiv hψband _ p hp
    have hbL : ∀ p, lapQE ψ p ≠ 0 → p.1 ∈ Icc σ H1 ∧ |p.2.2| ≤ L1 := by
      intro p hp
      by_cases hQ : pdQ (pdQ ψ) p = 0
      · have hE : pdEta (pdEta ψ) p ≠ 0 := fun hE => hp (by simp [lapQE, hQ, hE])
        exact band_fderiv (band_fderiv hψband _) _ p hE
      · exact band_fderiv (band_fderiv hψband _) _ p hQ
    have hcS : Continuous (pdS ψ) := (contDiff_pdS hψ.smooth).continuous
    have hcL : Continuous (lapQE ψ) :=
      ((contDiff_pdQ (contDiff_pdQ hψ.smooth)).add
        (contDiff_pdEta (contDiff_pdEta hψ.smooth))).continuous
    have hIA : Integrable (fun p => inner ℂ (pdS ψ p) ((V : Profile → MeridC) p))
        (cellMeasure c) :=
      (integrable_inner_band V hcS hbS measurable_const hOneK).congr
        (Eventually.of_forall fun p => by simp only [one_smul])
    have hID : Integrable (fun p => inner ℂ (lapQE ψ p) ((V : Profile → MeridC) p))
        (cellMeasure c) :=
      (integrable_inner_band V hcL hbL measurable_const hOneK).congr
        (Eventually.of_forall fun p => by simp only [one_smul])
    have hIB : Integrable (fun p => inner ℂ (ψ p) ((p.1⁻¹ : ℝ) • (V : Profile → MeridC) p))
        (cellMeasure c) :=
      integrable_inner_band V hψ.smooth.continuous hψband measurable_inv hInvK
    have hIC : Integrable (fun p => inner ℂ (ψ p) ((p.1⁻¹ : ℝ) • (g : Profile → MeridC) p))
        (cellMeasure c) :=
      integrable_inner_band g hψ.smooth.continuous hψband measurable_inv hInvK
    have hsplitw : ∫ p, inner ℂ (pdS ψ p + ν • lapQE ψ p) ((V : Profile → MeridC) p)
        ∂(cellMeasure c) = (∫ p, inner ℂ (pdS ψ p) ((V : Profile → MeridC) p) ∂(cellMeasure c)) +
          (ν : ℂ) * ∫ p, inner ℂ (lapQE ψ p) ((V : Profile → MeridC) p) ∂(cellMeasure c) := by
      rw [← integral_const_mul, ← integral_add hIA (hID.const_mul _)]
      refine integral_congr_ae (Eventually.of_forall fun p => ?_)
      simp only [inner_add_left, inner_real_smul_left]
    rw [hsplitw] at hw
    have hLHS : ∫ p, inner ℂ (dsFromS S_lap p) (φ p) ∂(cellMeasure c) =
        conj ((ν : ℂ) * ∫ p, inner ℂ (lapQE ψ p) ((V : Profile → MeridC) p) ∂(cellMeasure c)) := by
      have e : ∀ᵐ p ∂(cellMeasure c),
          inner ℂ (dsFromS S_lap p) (φ p) = conj (inner ℂ (ψ p) (LapN p)) := by
        filter_upwards [ae_mem_cell c] with p hp
        have hs : 0 < p.1 := hp.1
        have hk : p.1⁻¹ * (p.1 * χ p) = χ p := by field_simp
        rw [dsFromS, hS_cell p hp, smul_smul, hk, hψp, inner_real_smul_left,
          inner_real_smul_left, map_mul, Complex.conj_ofReal, inner_conj_symm]
      rw [integral_congr_ae e, integral_conj, hcell]
      congr 1
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun p => ?_)
      simp only [inner_real_smul_right]
    have hRHS : -∫ p, (inner ℂ ((V : Profile → MeridC) p) (pdS ψ p) +
        inner ℂ (dsFromS (fun q => flatCutAgeDriftTerm c χ μ V q + flatCutAgeForceTerm c χ b q) p)
          (φ p)) ∂(cellMeasure c) =
        -conj ((∫ p, inner ℂ (pdS ψ p) ((V : Profile → MeridC) p) ∂(cellMeasure c)) -
          μ * (∫ p, inner ℂ (ψ p) ((p.1⁻¹ : ℝ) • (V : Profile → MeridC) p) ∂(cellMeasure c)) +
            ∫ p, inner ℂ (ψ p) ((p.1⁻¹ : ℝ) • (g : Profile → MeridC) p) ∂(cellMeasure c)) := by
      have hIAB : Integrable (fun p => inner ℂ (pdS ψ p) ((V : Profile → MeridC) p) -
          μ * inner ℂ (ψ p) ((p.1⁻¹ : ℝ) • (V : Profile → MeridC) p)) (cellMeasure c) :=
        hIA.sub (hIB.const_mul μ)
      rw [← integral_const_mul, ← integral_sub hIA (hIB.const_mul μ), ← integral_add hIAB hIC,
        ← integral_conj]
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [ae_mem_cell c] with p hp
      simp only [dsFromS, flatCutAgeDriftTerm, flatCutAgeForceTerm, flatStressCutRep,
        periodize_of_mem hc _ hp, hψp]
      simp only [map_add, map_sub, map_mul, map_neg, inner_conj_symm, inner_add_left,
        inner_smul_left, inner_real_smul_left, inner_real_smul_right, Complex.conj_ofReal,
        smul_add]
      ring
    rw [hLHS, hRHS]
    have key : (∫ p, inner ℂ (pdS ψ p) ((V : Profile → MeridC) p) ∂(cellMeasure c)) -
        μ * (∫ p, inner ℂ (ψ p) ((p.1⁻¹ : ℝ) • (V : Profile → MeridC) p) ∂(cellMeasure c)) +
          ∫ p, inner ℂ (ψ p) ((p.1⁻¹ : ℝ) • (g : Profile → MeridC) p) ∂(cellMeasure c) =
        -((ν : ℂ) * ∫ p, inner ℂ (lapQE ψ p) ((V : Profile → MeridC) p) ∂(cellMeasure c)) := by
      linear_combination (-1 : ℂ) * hw
    rw [key, map_neg, neg_neg]
  · have hX := cellL2Norm_le_of_eLpNorm hSmem
      (mul_nonneg (mul_nonneg hH.le (cNorm8_nonneg χ)) (by positivity)) hS_eL
    refine hX.trans ?_
    have hM0' : 0 ≤ M := (norm_nonneg μ).trans hμM
    obtain ⟨hΓ1, hσΓ, hHΓ, hMΓ, hχΓ⟩ := gamma_parts χ χ1 hν hc hσ hσH hL1 hγ hM0'
    exact final_bound hΓ1 hσ hσΓ hH hHΓ hM0n hC0pos.le (cNorm8_nonneg χ) hχΓ (norm_nonneg _)
      (UnforcedLeray.Short.PartIIa.N05_2Aux.norm_PepsC0_apply_le c b) (norm_nonneg _)
      (UnforcedLeray.Short.PartIIa.N05_2Aux.norm_T0flat_apply_le χ χ1 hν hc hσ hσH hL1 hγ hμM hμγ b)
      (norm_nonneg _) (hμM.trans hMΓ) (norm_nonneg _)

end UnforcedLeray.Short.PartIIa.FBCLL
