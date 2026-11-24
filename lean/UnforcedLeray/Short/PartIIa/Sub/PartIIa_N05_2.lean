import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_4
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnWeakC

/-!
# `Sub/PartII-a_N05_2`: Decomposition of `BodyFlatLocalH1` (`PartII-a:N05/2`)

Source of record: `the November 2 reference manuscript`,
lines 1794-1799 (together with lines 1684-1689).

## Structure of this file

1. **Unconditional energy-class and weak flat equation for general body sources (`N05_2Aux.flat_body_energy_and_weak_all`)**:
   Using the accepted `N01` leaves (`N01.smoothForceDense`, `N01.smoothForceFields`,
   `smoothForceGradBound`, `N01.energyClosure`, and `N01.weakAllForces` from
   `Sub/N01/BodyColumnEnergyC.lean` and `Sub/N01/BodyColumnWeakC.lean`), we prove that for *every*
   `b : HSpace c MeridC`, `w = T0flat hc ν μ b = R0 hc ν μ (PepsC 0 c b)` has an energy-class
   representative `(w_rep, Gr)` solving the weak flat equation
   `(∂_s + μ / s - ν Δ_{q,η}) w_rep = (PepsC 0 c b) / s` against every divergence-free flat test `Φ`,
   together with the `H`-norm bound `‖T0flat hc ν μ b‖ ≤ Gamma ν c σ H1 L1 M γs χ χ1 * ‖b‖`
   and the concrete box-supported periodic representative bound
   `cellL2Norm c (flatStressCutRep c χ (T0flat hc ν μ b)) ≤ Gamma ν c σ H1 L1 M γs χ χ1 ^ 3 * ‖b‖`.
2. **Coordinate-derivative conversion `∂_s = s⁻¹ S` on the observation box (`N05_2Aux.memLp_dsFromS_flat`,
   `N05_2Aux.cellL2Norm_dsFromS_flat_le`, `N05_2Aux.cellH1Norm_flat_of_dsFromS_le`)**:
   Converts a box-supported weak `S = s ∂_s` derivative `Su` into `ds = dsFromS Su` in
   `L²(cellMeasure c)` with `cellL2Norm c (dsFromS Su) ≤ Gamma * cellL2Norm c Su`.
3. **Conditional assembly (`bodyFlatLocalH1_of`)**:
   Combines the local first-order energy bound leaf `FlatBodyFirstOrderLocal` (`PartII-a:N05/2/1`,
   controlling `u`, `dq`, `deta` in `L²(cellMeasure c)` from the flat energy inequality) and the
   local age-derivative maximal-regularity leaf `FlatBodyAgeDerivLocal` (`PartII-a:N05/2/2`,
   controlling `Su = S(χ w)` on `[σ, H1]` using the larger cutoff `χ1` and `B0423.freeStress11`)
   to establish `BodyFlatLocalH1` (composed by `PartII-a:N05/2`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.Axi
open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226
open UnforcedLeray.Short.PartIIIb.Concrete (Chart)
open UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst (IsEnergyFieldAE forcedIntegrand)
open UnforcedLeray.Short.PartIIIb.NearInst.Delta (velF)
open UnforcedLeray.Short.IIIa (IsFlatTest)

namespace N05_2Aux

/-! ### 1. Norm bounds and unconditional energy/weak solution for general `b : HSpace c MeridC` -/

theorem one_le_gamma_flat {ν c σ H1 L1 M γs : ℝ} (χ χ1 : Profile → ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1) (hL1 : 0 ≤ L1) (hγ : 0 < γs)
    (hM : 0 ≤ M) : 1 ≤ Gamma ν c σ H1 L1 M γs χ χ1 := by
  unfold Gamma GammaBox
  have : 0 < ν⁻¹ := inv_pos.2 hν
  have : 0 < c⁻¹ := inv_pos.2 hc
  have : 0 < σ⁻¹ := inv_pos.2 hσ
  have : 0 < γs⁻¹ := inv_pos.2 hγ
  linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]

/-- The flat Leray projection `PepsC 0 c` is contractive on `HSpace c MeridC`. -/
theorem norm_PepsC0_apply_le (c : ℝ) (b : HSpace c MeridC) :
    ‖PepsC 0 c b‖ ≤ ‖b‖ := by
  set p := PepsC 0 c b
  have hp : p ∈ solenoidalHC 0 c := Submodule.starProjection_apply_mem (solenoidalHC 0 c) b
  have hbp : b - p ∈ (solenoidalHC 0 c)ᗮ :=
    Submodule.sub_starProjection_mem_orthogonal (K := solenoidalHC 0 c) b
  have horth : inner ℂ p (b - p) = 0 :=
    (Submodule.mem_orthogonal (solenoidalHC 0 c) (b - p)).1 hbp p hp
  have hinner : inner ℂ p p = inner ℂ p b := by
    have hsub : inner ℂ p (b - p) = inner ℂ p b - inner ℂ p p := inner_sub_right p b p
    linear_combination -hsub.symm.trans horth
  have hsq : ‖p‖ ^ 2 ≤ ‖p‖ * ‖b‖ := by
    calc ‖p‖ ^ 2 = RCLike.re (inner ℂ p p) := (inner_self_eq_norm_sq p).symm
      _ = RCLike.re (inner ℂ p b) := by rw [hinner]
      _ ≤ ‖inner ℂ p b‖ := RCLike.re_le_norm _
      _ ≤ ‖p‖ * ‖b‖ := norm_inner_le_norm p b
  nlinarith [norm_nonneg p, norm_nonneg b]

/-- Bound `‖T0flat hc ν μ b‖ ≤ Gamma ν c σ H1 L1 M γs χ χ1 * ‖b‖` from `B0225.norm_R0_le`. -/
theorem norm_T0flat_apply_le {ν c σ H1 L1 M γs : ℝ} (χ χ1 : Profile → ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1) (hL1 : 0 ≤ L1) (hγ : 0 < γs)
    {μ : ℂ} (hμM : ‖μ‖ ≤ M) (hμγ : γs ≤ μ.re + 1 / 4) (b : HSpace c MeridC) :
    ‖T0flat hc ν μ b‖ ≤ Gamma ν c σ H1 L1 M γs χ χ1 * ‖b‖ := by
  have hM0 : 0 ≤ M := (norm_nonneg μ).trans hμM
  have hμ : 0 < μ.re + 1 / 4 := lt_of_lt_of_le hγ hμγ
  have hR0 := UnforcedLeray.B0225.norm_R0_le (E := MeridC) hc ν hμ
  have hinv : (μ.re + 1 / 4)⁻¹ ≤ Gamma ν c σ H1 L1 M γs χ χ1 := by
    have h1 : (μ.re + 1 / 4)⁻¹ ≤ γs⁻¹ := inv_anti₀ hγ hμγ
    have h2 : γs⁻¹ ≤ Gamma ν c σ H1 L1 M γs χ χ1 := by
      unfold Gamma GammaBox
      have : 0 < ν⁻¹ := inv_pos.2 hν
      have : 0 < c⁻¹ := inv_pos.2 hc
      have : 0 < σ⁻¹ := inv_pos.2 hσ
      linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
    exact h1.trans h2
  calc ‖T0flat hc ν μ b‖
      = ‖UnforcedLeray.B0225.R0 hc ν μ (PepsC 0 c b)‖ := rfl
    _ ≤ ‖UnforcedLeray.B0225.R0 (E := MeridC) hc ν μ‖ * ‖PepsC 0 c b‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ (μ.re + 1 / 4)⁻¹ * ‖b‖ :=
        mul_le_mul hR0 (norm_PepsC0_apply_le c b) (norm_nonneg _) (inv_nonneg.2 hμ.le)
    _ ≤ Gamma ν c σ H1 L1 M γs χ χ1 * ‖b‖ :=
        mul_le_mul_of_nonneg_right hinv (norm_nonneg b)

/-- Unconditional `Gamma^3` bound on `cellL2Norm c (flatStressCutRep c χ (T0flat hc ν μ b))`. -/
theorem cellL2Norm_flatStressCutRep_T0flat_le {ν c σ H1 L1 M γs : ℝ} (χ χ1 : Profile → ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1) (hL1 : 0 ≤ L1) (hγ : 0 < γs)
    (hχ : IsNearCutoff c σ H1 L1 χ) (hm : Measurable χ) {μ : ℂ} (hμM : ‖μ‖ ≤ M)
    (hμγ : γs ≤ μ.re + 1 / 4) (b : HSpace c MeridC) :
    cellL2Norm c (flatStressCutRep c χ (T0flat hc ν μ b)) ≤
      Gamma ν c σ H1 L1 M γs χ χ1 ^ 3 * ‖b‖ := by
  set G := Gamma ν c σ H1 L1 M γs χ χ1
  have hM0 : 0 ≤ M := (norm_nonneg μ).trans hμM
  have hνi : 0 < ν⁻¹ := inv_pos.2 hν
  have hci : 0 < c⁻¹ := inv_pos.2 hc
  have hσi : 0 < σ⁻¹ := inv_pos.2 hσ
  have hγi : 0 < γs⁻¹ := inv_pos.2 hγ
  have hG0 : 0 ≤ G := by
    unfold G Gamma GammaBox
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have h1H1_G : 1 + H1 ≤ G := by
    unfold G Gamma GammaBox
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hcN_G : cNorm8 χ ≤ G := by
    unfold G Gamma GammaBox
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hL2 := N05_4Aux.cellL2Norm_flatStressCutRep_le_mul hc hσ hσH hχ hm (T0flat hc ν μ b)
  have hT0 := norm_T0flat_apply_le χ χ1 hν hc hσ hσH hL1 hγ hμM hμγ b
  have hH1_pos : 0 < H1 := lt_of_lt_of_le hσ hσH
  calc cellL2Norm c (flatStressCutRep c χ (T0flat hc ν μ b))
      ≤ (1 + H1) * cNorm8 χ * ‖T0flat hc ν μ b‖ := hL2
    _ ≤ (1 + H1) * cNorm8 χ * (G * ‖b‖) :=
        mul_le_mul_of_nonneg_left hT0 (mul_nonneg (by linarith) (cNorm8_nonneg χ))
    _ = (1 + H1) * cNorm8 χ * G * ‖b‖ := by ring
    _ ≤ G * G * G * ‖b‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg b)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul h1H1_G hcN_G (cNorm8_nonneg χ) hG0) hG0
    _ = G ^ 3 * ‖b‖ := by ring

/-- For every `b : HSpace c MeridC` (without requiring `b` to be a smooth tensor divergence),
`w = T0flat hc ν μ b` admits an energy-class representative `(w_rep, Gr)` solving the weak flat
equation `(∂_s + μ / s - ν Δ_{q,η}) w_rep = (PepsC 0 c b) / s` against every flat test `Φ`. -/
theorem flat_body_energy_and_weak_all (c ν : ℝ) (hc : 0 < c) (hν : 0 < ν) (μ : ℂ)
    (hμ : 0 < μ.re + 1 / 4) (b : HSpace c MeridC) :
    ∃ (w_rep : Chart → Fin 2 → ℂ) (Gr : Chart → Fin 2 → Fin 2 → ℂ),
      w_rep =ᵐ[ageμ c (-3 / 2)] velF c (T0flat hc ν μ b) ∧
      IsEnergyFieldAE c w_rep Gr ∧
      ∀ Φ, IsFlatTest c Φ →
        IntegrableOn (forcedIntegrand ν μ (fun _ _ _ => 0)
            (fun x i => velF c (PepsC 0 c b : Profile → MeridC) x i / (x.1 : ℂ)) w_rep Φ)
          (Ioi (0 : ℝ) ×ˢ B0579.cell c) ∧
        ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
          forcedIntegrand ν μ (fun _ _ _ => 0)
            (fun x i => velF c (PepsC 0 c b : Profile → MeridC) x i / (x.1 : ℂ)) w_rep Φ p = 0 := by
  set g : HSpace c MeridC := PepsC 0 c b
  have hgs : g ∈ solenoidalHC 0 c := Submodule.starProjection_apply_mem _ _
  have hD := N01.smoothForceDense c hc g hgs
  have hex : ∀ k : ℕ, ∃ y ∈ N01.SmoothForceSet c, dist g y < 1 / ((k : ℝ) + 1) := fun k =>
    Metric.mem_closure_iff.1 hD _ (by positivity)
  choose gk hgk hdist using hex
  have hlim : Tendsto gk atTop (𝓝 g) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun _ => dist_nonneg) (fun k => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [dist_comm]; exact (hdist k).le
  have hfld := fun k => smoothForceFields c ν hc hν μ hμ (gk k) (hgk k)
  choose bk Gk hbk hEk using hfld
  obtain ⟨C, hC⟩ := smoothForceGradBound c ν hc hν μ hμ
  have hCauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k ≥ N, ∀ l ≥ N,
      ∫⁻ p, ENNReal.ofReal (UnforcedLeray.Short.IIIa.tnorm2
        (fun i j => Gk k p i j - Gk l p i j) ^ 2) ∂(ageμ c (-1 / 2)) < ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (4 * (|C| + 1) / ε)
    refine ⟨N, fun k hk l hl => ?_⟩
    refine lt_of_le_of_lt
      (hC (gk k) (hgk k) (gk l) (hgk l) _ _ _ _ (hbk k) (hEk k) (hbk l) (hEk l))
      ((ENNReal.ofReal_lt_ofReal_iff hε).2 ?_)
    have hk1 : 1 / ((k : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (N : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have hl1 : 1 / ((l : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (N : ℝ) ≤ l := by exact_mod_cast hl
      linarith
    have hnorm : ‖gk k - gk l‖ ≤ 2 / ((N : ℝ) + 1) := by
      have htri : ‖gk k - gk l‖ ≤ dist g (gk k) + dist g (gk l) := by
        calc ‖gk k - gk l‖ = dist (gk k) (gk l) := (dist_eq_norm _ _).symm
          _ ≤ dist (gk k) g + dist g (gk l) := dist_triangle _ _ _
          _ = dist g (gk k) + dist g (gk l) := by rw [dist_comm (gk k) g]
      have hsum : dist g (gk k) + dist g (gk l) ≤ 2 / ((N : ℝ) + 1) := by
        have e2 : 2 / ((N : ℝ) + 1) = 1 / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 1) := by ring
        linarith [hdist k, hdist l]
      linarith
    have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hq : ‖gk k - gk l‖ ^ 2 ≤ 4 / ((N : ℝ) + 1) := by
      have h0 : 0 ≤ ‖gk k - gk l‖ := norm_nonneg _
      have hle : ‖gk k - gk l‖ ^ 2 ≤ (2 / ((N : ℝ) + 1)) ^ 2 := pow_le_pow_left₀ h0 hnorm 2
      have hN1' : (1 : ℝ) ≤ (N : ℝ) + 1 := by
        have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        linarith
      calc ‖gk k - gk l‖ ^ 2 ≤ (2 / ((N : ℝ) + 1)) ^ 2 := hle
        _ = 4 / ((N : ℝ) + 1) ^ 2 := by field_simp; norm_num
        _ ≤ 4 / ((N : ℝ) + 1) := by
          apply div_le_div_of_nonneg_left (by norm_num) hN1
          nlinarith
    have hsq : 0 ≤ ‖gk k - gk l‖ ^ 2 := by positivity
    have hcN : ε * ((N : ℝ) + 1) > 4 * (|C| + 1) := by
      have := (div_lt_iff₀ hε).1 hN
      nlinarith
    calc C * ‖gk k - gk l‖ ^ 2 ≤ |C| * ‖gk k - gk l‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (le_abs_self C) hsq
      _ ≤ |C| * (4 / ((N : ℝ) + 1)) := mul_le_mul_of_nonneg_left hq (abs_nonneg C)
      _ < ε := by
          rw [← mul_div_assoc, div_lt_iff₀ hN1]
          nlinarith [abs_nonneg C]
  obtain ⟨w_rep, Gr, hw_rep, hE⟩ :=
    N01.energyClosure c ν hc hν μ hμ g gk hlim bk Gk (fun k => ⟨hbk k, hEk k⟩) hCauchy
  refine ⟨w_rep, Gr, hw_rep, hE, fun Φ hΦ => ?_⟩
  exact N01.weakAllForces c ν hc hν μ hμ g hgs w_rep Gr hw_rep hE Φ hΦ

/-! ### 2. Coordinate-derivative conversion `∂_s = s⁻¹ S` on the observation box -/

private lemma sqrt_rpow_sq_flat (x : ℝ) (hx : 0 ≤ x) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hx]

private lemma sq_rpow_half_flat (y : ℝ) (hy : 0 ≤ y) : (y ^ 2) ^ (1 / 2 : ℝ) = y := by
  rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hy]

/-- `dsFromS Su` belongs to `L²(cellMeasure c)` when `Su` is supported in `σ ≤ s` (`σ > 0`). -/
theorem memLp_dsFromS_flat {c σ H1 L1 : ℝ} (hσ : 0 < σ) {Su : Profile → MeridC}
    (hsupp : ∀ p : Profile, Su p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1)
    (hSu : MemLp Su 2 (cellMeasure c)) :
    MemLp (dsFromS Su) 2 (cellMeasure c) := by
  have hm : AEStronglyMeasurable (dsFromS Su) (cellMeasure c) :=
    measurable_fst.inv.aestronglyMeasurable.smul hSu.1
  refine hSu.of_le_mul (c := σ⁻¹) hm (Eventually.of_forall fun p => ?_)
  by_cases h0 : Su p = 0
  · simp [dsFromS, h0]
  · have hpσ : σ ≤ p.1 := (hsupp p h0).1
    have hp0 : 0 < p.1 := lt_of_lt_of_le hσ hpσ
    rw [dsFromS, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hp0.le)]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hσ hpσ) (norm_nonneg _)

/-- Bound `cellL2Norm c (dsFromS Su) ≤ Gamma * cellL2Norm c Su` on the observation box. -/
theorem cellL2Norm_dsFromS_flat_le {ν c σ H1 L1 M γs : ℝ} (χ χ1 : Profile → ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1) (hL1 : 0 ≤ L1) (hγ : 0 < γs)
    (hM : 0 ≤ M) {Su : Profile → MeridC}
    (hsupp : ∀ p : Profile, Su p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1)
    (hSu : MemLp Su 2 (cellMeasure c)) :
    cellL2Norm c (dsFromS Su) ≤ Gamma ν c σ H1 L1 M γs χ χ1 * cellL2Norm c Su := by
  set G := Gamma ν c σ H1 L1 M γs χ χ1
  have hG1 : 1 ≤ G := one_le_gamma_flat χ χ1 hν hc hσ hσH hL1 hγ hM
  have hG0 : 0 ≤ G := by linarith
  have hds : MemLp (dsFromS Su) 2 (cellMeasure c) := memLp_dsFromS_flat hσ hsupp hSu
  have hpt : ∀ p : Profile, ‖dsFromS Su p‖ ≤ G * ‖Su p‖ := fun p => by
    by_cases h0 : Su p = 0
    · simp [dsFromS, h0]
    · exact norm_dsFromS_le χ χ1 hν hc hσ hσH hL1 hγ hM Su (hsupp p h0).1
  have hint : ∫ p, ‖dsFromS Su p‖ ^ 2 ∂(cellMeasure c) ≤
      (G * cellL2Norm c Su) ^ 2 := by
    have h1 : ∫ p, ‖dsFromS Su p‖ ^ 2 ∂(cellMeasure c) ≤
        ∫ p, G ^ 2 * ‖Su p‖ ^ 2 ∂(cellMeasure c) := by
      refine integral_mono hds.norm.integrable_sq (hSu.norm.integrable_sq.const_mul (G ^ 2))
        (fun p => ?_)
      calc ‖dsFromS Su p‖ ^ 2 ≤ (G * ‖Su p‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hpt p) 2
        _ = G ^ 2 * ‖Su p‖ ^ 2 := by ring
    have hA : 0 ≤ ∫ p, ‖Su p‖ ^ 2 ∂(cellMeasure c) := integral_nonneg fun _ => sq_nonneg _
    calc ∫ p, ‖dsFromS Su p‖ ^ 2 ∂(cellMeasure c)
        ≤ ∫ p, G ^ 2 * ‖Su p‖ ^ 2 ∂(cellMeasure c) := h1
      _ = G ^ 2 * ∫ p, ‖Su p‖ ^ 2 ∂(cellMeasure c) := integral_const_mul _ _
      _ = G ^ 2 * (cellL2Norm c Su) ^ 2 := by rw [cellL2Norm, sqrt_rpow_sq_flat _ hA]
      _ = (G * cellL2Norm c Su) ^ 2 := by ring
  unfold cellL2Norm
  calc (∫ p, ‖dsFromS Su p‖ ^ 2 ∂(cellMeasure c)) ^ (1 / 2 : ℝ)
      ≤ ((G * cellL2Norm c Su) ^ 2) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (integral_nonneg fun _ => sq_nonneg _) hint (by norm_num)
    _ = G * cellL2Norm c Su := sq_rpow_half_flat _ (mul_nonneg hG0 (cellL2Norm_nonneg c Su))

/-- Bound `cellH1Norm c u (dsFromS Su) dq deta` by `Gamma` times the `cellL2Norm` sum of
`(u, Su, dq, deta)`. -/
theorem cellH1Norm_flat_of_dsFromS_le {ν c σ H1 L1 M γs : ℝ} (χ χ1 : Profile → ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1) (hL1 : 0 ≤ L1) (hγ : 0 < γs)
    (hM : 0 ≤ M) (u Su dq deta : Profile → MeridC)
    (hsuppS : ∀ p : Profile, Su p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1)
    (hSu : MemLp Su 2 (cellMeasure c)) :
    cellH1Norm c u (dsFromS Su) dq deta ≤
      Gamma ν c σ H1 L1 M γs χ χ1 *
        (cellL2Norm c u + cellL2Norm c Su + cellL2Norm c dq + cellL2Norm c deta) := by
  set G := Gamma ν c σ H1 L1 M γs χ χ1
  have hG1 : 1 ≤ G := one_le_gamma_flat χ χ1 hν hc hσ hσH hL1 hγ hM
  have hds := cellL2Norm_dsFromS_flat_le χ χ1 hν hc hσ hσH hL1 hγ hM hsuppS hSu
  have hu0 := cellL2Norm_nonneg c u
  have hq0 := cellL2Norm_nonneg c dq
  have he0 := cellL2Norm_nonneg c deta
  unfold cellH1Norm
  nlinarith

end N05_2Aux

open N05_2Aux

/-! ### 3. Leaf obligations for `BodyFlatLocalH1` -/

/-- **Leaf 1 (`PartII-a:N05/2/1`) — local `(q, η)` first-order energy bound for `χ T_0 b`**
(source `the November 2 reference manuscript`,
lines 1684-1689, 1794-1799): from the flat energy inequality
`(Re μ + 1/4) ‖w‖_H^2 + ν ‖∇_{q,η} w‖_{L²(s^{-1/2})}^2 ≤ (Re μ + 1/4)⁻¹ ‖P_0 b‖_H^2`
(`N05_2Aux.flat_body_energy_and_weak_all`) for `w = T0flat hc ν μ b`, localising by `χ`
(`IsNearCutoff c σ H1 L1 χ`) on the compact age band `[σ, H1]` produces box-supported `c`-periodic
representatives `u, dq, deta : Profile → MeridC` in `L²(cellMeasure c)` satisfying the `(q, η)`
integration-by-parts identities and
`cellL2Norm c u + cellL2Norm c dq + cellL2Norm c deta ≤ C * Gamma^k * ‖b‖`. -/
def FlatBodyFirstOrderLocal : Prop :=
  ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ (ν c σ H1 L1 M γs : ℝ) (χ χ1 : Profile → ℝ), 0 < ν → ∀ (hc : 0 < c),
      0 < σ → σ ≤ H1 → 0 ≤ L1 → 0 < γs →
      IsNearCutoff c σ H1 L1 χ → IsLargerCutoff c χ χ1 →
      ∀ (hm : Measurable χ) (B : ℝ) (hB : ∀ p, |χ p| ≤ B),
      ∀ μ : ℂ, ‖μ‖ ≤ M → γs ≤ μ.re + 1 / 4 →
        ∀ b : HSpace c MeridC,
          ∃ u dq deta : Profile → MeridC,
            ((mulChi (measureH c) χ hm hB (T0flat hc ν μ b) : HSpace c MeridC) : Profile → MeridC)
              =ᵐ[measureH c] u ∧
            QPeriodic c u ∧ QPeriodic c dq ∧ QPeriodic c deta ∧
            (∀ p : Profile, u p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1) ∧
            (∀ p : Profile, dq p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1) ∧
            (∀ p : Profile, deta p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1) ∧
            MemLp u 2 (cellMeasure c) ∧ MemLp dq 2 (cellMeasure c) ∧ MemLp deta 2 (cellMeasure c) ∧
            (∀ φ : Profile → MeridC, IsMeridTest c φ →
              ∫ p, inner ℂ (dq p) (φ p) ∂(cellMeasure c) =
                -∫ p, inner ℂ (u p) (pdQ φ p) ∂(cellMeasure c)) ∧
            (∀ φ : Profile → MeridC, IsMeridTest c φ →
              ∫ p, inner ℂ (deta p) (φ p) ∂(cellMeasure c) =
                -∫ p, inner ℂ (u p) (pdEta φ p) ∂(cellMeasure c)) ∧
            cellL2Norm c u + cellL2Norm c dq + cellL2Norm c deta ≤
              C * Gamma ν c σ H1 L1 M γs χ χ1 ^ k * ‖b‖

/-- **Leaf 2 (`PartII-a:N05/2/2`) — local age-derivative bound for `χ T_0 b` via heat maximal
regularity** (source `the November 2 reference manuscript`,
lines 1794-1799): cutting off the flat heat equation
`(∂_s + μ / s - ν Δ_{q,η}) w = P_0 b / s` (`N05_2Aux.flat_body_energy_and_weak_all`) with the
larger cutoff `χ1` (`IsLargerCutoff c χ χ1`) on the compact age band `[σ, H1]` and applying the
Fourier heat estimate (`B0423.freeStress11`) controls `ν s Δ_{q,η} w` and hence `S w = s ∂_s w` on
`tsupport χ`, yielding a box-supported `c`-periodic weak `S = s ∂_s` derivative `Su` of `u` in
`L²(cellMeasure c)` such that `dsFromS Su` satisfies `ibp_s` against every `IsMeridTest c φ` and
`cellL2Norm c Su ≤ C * Gamma^k * ‖b‖`. -/
def FlatBodyAgeDerivLocal : Prop :=
  ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ (ν c σ H1 L1 M γs : ℝ) (χ χ1 : Profile → ℝ), 0 < ν → ∀ (hc : 0 < c),
      0 < σ → σ ≤ H1 → 0 ≤ L1 → 0 < γs →
      IsNearCutoff c σ H1 L1 χ → IsLargerCutoff c χ χ1 →
      ∀ (hm : Measurable χ) (B : ℝ) (hB : ∀ p, |χ p| ≤ B),
      ∀ μ : ℂ, ‖μ‖ ≤ M → γs ≤ μ.re + 1 / 4 →
        ∀ (b : HSpace c MeridC) (u : Profile → MeridC),
          ((mulChi (measureH c) χ hm hB (T0flat hc ν μ b) : HSpace c MeridC) : Profile → MeridC)
            =ᵐ[measureH c] u →
          QPeriodic c u →
          (∀ p : Profile, u p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1) →
          MemLp u 2 (cellMeasure c) →
          ∃ Su : Profile → MeridC,
            QPeriodic c Su ∧
            (∀ p : Profile, Su p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1) ∧
            MemLp Su 2 (cellMeasure c) ∧
            (∀ φ : Profile → MeridC, IsMeridTest c φ →
              ∫ p, inner ℂ (dsFromS Su p) (φ p) ∂(cellMeasure c) =
                -∫ p, inner ℂ (u p) (pdS φ p) ∂(cellMeasure c)) ∧
            cellL2Norm c Su ≤ C * Gamma ν c σ H1 L1 M γs χ χ1 ^ k * ‖b‖

/-! ### 4. Conditional assembly of `BodyFlatLocalH1` -/

/-- **Conditional assembly of `BodyFlatLocalH1` (`PartII-a:N05/2`)** from
`FlatBodyFirstOrderLocal`, `FlatBodyAgeDerivLocal`, and the coordinate-derivative conversion
`∂_s = s⁻¹ S` (`dsFromS`). -/
theorem bodyFlatLocalH1_of (hFirst : FlatBodyFirstOrderLocal) (hAge : FlatBodyAgeDerivLocal) :
    BodyFlatLocalH1 := by
  obtain ⟨k₁, C₁, hC₁, h1⟩ := hFirst
  obtain ⟨k₂, C₂, hC₂, h2⟩ := hAge
  set K := max k₁ k₂
  refine ⟨K + 1, C₁ + C₂, by positivity, ?_⟩
  intro ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ hχ hχ1 hm B hB μ hμM hμγ b
  have hM0 : 0 ≤ M := (norm_nonneg μ).trans hμM
  obtain ⟨u, dq, deta, hae, hpu, hpq, hpe, hsu, hsq, hse, hmu, hmq, hme, hibpq, hibpe, hbd1⟩ :=
    h1 ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ hχ hχ1 hm B hB μ hμM hμγ b
  obtain ⟨Su, hpS, hsS, hmS, hibps, hbd2⟩ :=
    h2 ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ hχ hχ1 hm B hB μ hμM hμγ b u hae hpu hsu hmu
  refine ⟨u, dsFromS Su, dq, deta,
    { ae_eq := hae
      periodic_u := hpu
      periodic_ds := fun p => by simp [dsFromS, hpS p]
      periodic_dq := hpq
      periodic_deta := hpe
      support_u := hsu
      support_ds := fun p hp => hsS p fun h0 => hp (by simp [dsFromS, h0])
      support_dq := hsq
      support_deta := hse
      memLp_u := hmu
      memLp_ds := memLp_dsFromS_flat hσ hsS hmS
      memLp_dq := hmq
      memLp_deta := hme
      ibp_s := hibps
      ibp_q := hibpq
      ibp_eta := hibpe }, ?_⟩
  set G := Gamma ν c σ H1 L1 M γs χ χ1
  have hG1 : 1 ≤ G := one_le_gamma_flat χ χ1 hν hc hσ hσH hL1 hγ hM0
  have hG0 : 0 ≤ G := by linarith
  have hGK₁ : G ^ k₁ ≤ G ^ K := pow_le_pow_right₀ hG1 (le_max_left k₁ k₂)
  have hGK₂ : G ^ k₂ ≤ G ^ K := pow_le_pow_right₀ hG1 (le_max_right k₁ k₂)
  have hbd1' : cellL2Norm c u + cellL2Norm c dq + cellL2Norm c deta ≤ C₁ * G ^ K * ‖b‖ := by
    calc cellL2Norm c u + cellL2Norm c dq + cellL2Norm c deta
        ≤ C₁ * G ^ k₁ * ‖b‖ := hbd1
      _ ≤ C₁ * G ^ K * ‖b‖ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hGK₁ hC₁) (norm_nonneg b)
  have hbd2' : cellL2Norm c Su ≤ C₂ * G ^ K * ‖b‖ := by
    calc cellL2Norm c Su ≤ C₂ * G ^ k₂ * ‖b‖ := hbd2
      _ ≤ C₂ * G ^ K * ‖b‖ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hGK₂ hC₂) (norm_nonneg b)
  have hsum : cellL2Norm c u + cellL2Norm c Su + cellL2Norm c dq + cellL2Norm c deta ≤
      (C₁ + C₂) * G ^ K * ‖b‖ := by linarith
  calc cellH1Norm c u (dsFromS Su) dq deta
      ≤ G * (cellL2Norm c u + cellL2Norm c Su + cellL2Norm c dq + cellL2Norm c deta) :=
        cellH1Norm_flat_of_dsFromS_le χ χ1 hν hc hσ hσH hL1 hγ hM0 u Su dq deta hsS hmS
    _ ≤ G * ((C₁ + C₂) * G ^ K * ‖b‖) := mul_le_mul_of_nonneg_left hsum hG0
    _ = (C₁ + C₂) * G ^ (K + 1) * ‖b‖ := by ring

end UnforcedLeray.Short.PartIIa
