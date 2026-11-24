import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F9
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F5
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T16_2
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradBound
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.FlatColumnReal
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Velocity
import UnforcedLeray.Short.PartIIb.Tasks.StrongLateCoeff.RawProfileLate
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanDecay
import UnforcedLeray.Short.PartI.Tasks.TrainVorticityTail
import UnforcedLeray.Short.PartI.Tasks.TrainStreamTails
import UnforcedLeray.Short.PartI.Tasks.TrainFluctuationDecayProof
import UnforcedLeray.Short.PartI.Tasks.TrainTransverseTailsProof
import UnforcedLeray.Short.PartI.Tasks.TrainFixedBandProof

/-!
# Part II-b, task `PartII-b:F9/1`: Free convective interaction bound (`FlatFreeInteractionStep`)

Source of record: `the November 2 reference manuscript` (SP), lines 2329–2334.

For `F ∈ H_p` and `b_0 = T_0 F` (`InFlatClass p.c bgp b0`, `IsFlatResponse p.ν 0 F b0`),
we bound the free convective interaction
`s B_v b_0 = flatK p.train b0 b0q b0η` in `H_p`:
* on `(0, p.H]` (`p.H = Σ / ν`):
  `‖s B_v b_0‖_{H_p(0, H)} ≤ C ν^{-k} (ν^{-1/2} H^{1/2} + H) ‖F‖_{H_p}`;
* on `(p.H, ∞)`:
  `‖s B_v b_0‖_{H_p(H, ∞)} ≤ C ν^{-k} H^{-1/2} (ν^{-1/2} + 1) ‖F‖_{H_p}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Real
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete
open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0186
open UnforcedLeray.B0188 UnforcedLeray.B0190
open UnforcedLeray.Short.PartI
open UnforcedLeray.Short.PartIIa UnforcedLeray.Short.PartIIa.Jet

namespace FreeInteractionAux

/-! ### 1. Unconditional band and tail bounds for the train velocity and its spatial gradient -/

/-- Unconditional proof of `RawVelJets` from the Part I train tail and fixed-band tasks. -/
theorem rawVelJets_uncond : RawVelJets := by
  have hFD0 : OverlapFluctuationDecay := overlap_fluctuation_decay overlap_highnorm_uniform
  have hOv : TrainOverlap :=
    trainOverlap_proof hFD0 (overlap_mean_decay overlap_highnorm_uniform hFD0 overlap_mean_primitive)
  have hVort : TrainVorticityGaussianTail := train_vorticity_gaussian_tail hOv
  have hTails : TrainStreamVelocityPressureTails := train_stream_velocity_pressure_tails hOv hVort
  have hFD : TrainFluctuationDecay := trainFluctuationDecay_proof hTails hFD0 hOv
  have hT : TrainTransverseTails := trainTransverseTails_proof hVort hTails
  have hF : TrainFixedBand := trainFixedBand_proof hTails hFD
  exact rawVelJets_of (rawVelTailJets_of hT)
    (rawVelBandJets_of trainVelSmooth_proof vcSmooth_proof vcJetSup_proof (fixedBandJets_of hF))

/-- On the slow-age band `0 < x.1 ≤ p.H = Sig / p.ν`, the train velocity and its first chart
derivatives `∂_q v, ∂_η v` are bounded by `C_b * (p.ν ^ k_b)⁻¹`. -/
theorem trainVel_band_bound (Sig : ℝ) (hSig : 0 < Sig) (dm dp : ℝ) (hdm : 0 < dm) :
    ∃ (C_b : ℝ) (k_b : ℕ) (ν_b : ℝ), 0 < C_b ∧ 0 < ν_b ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν_b → p.ageCut = Sig →
        ∀ x : Coord, 0 < x.1 → x.1 ≤ p.H →
          ‖p.train.v x.1 x.2‖ ≤ C_b * (p.ν ^ k_b)⁻¹ ∧
          ‖Axi.dQ (fun m : Coord => p.train.v m.1 m.2) x‖ ≤ C_b * (p.ν ^ k_b)⁻¹ ∧
          ‖Axi.dEta (fun m : Coord => p.train.v m.1 m.2) x‖ ≤ C_b * (p.ν ^ k_b)⁻¹ := by
  obtain ⟨C, N, ν₀, hC, hν₀, HJ⟩ := rawVelJets_uncond Sig hSig dm dp hdm
  have hBridge : TrainChartBridge := trainChartBridge_of trainVelSmooth_proof
  refine ⟨C, N, ν₀, hC, hν₀, fun p d hreg hν hS x hx0 hxH => ?_⟩
  obtain ⟨b0, -, b2, b3⟩ := hBridge p d dm dp hreg x hx0
  have hJ := HJ p d hreg hν hS x hx0 hxH
  have n0 := norm_nonneg (ageJet 0 0 p.train.v x.1 x.2)
  have n1 := norm_nonneg (ageJet 1 0 p.train.v x.1 x.2)
  have n2 := norm_nonneg (ageJet 0 1 p.train.v x.1 x.2)
  have n3 := norm_nonneg (ageJet 2 0 p.train.v x.1 x.2)
  refine ⟨?_, ?_, ?_⟩
  · change ‖trainProf p x‖ ≤ _
    linarith
  · change ‖Axi.dQ (trainProf p) x‖ ≤ _
    linarith
  · change ‖Axi.dEta (trainProf p) x‖ ≤ _
    linarith

/-- On `0 < x.1`, the train velocity agrees with `merProfile 0 (trainProfile p.train.ψ)`
(since `ringEps 0 = 0⁻¹ = 0`). -/
theorem trainVel_eq_merProfile_zero {p : Params} {d dm dp : ℝ} (hb : BgRegime p d dm dp)
    {x : Coord} (hx : 0 < x.1) :
    p.train.v x.1 x.2 = merProfile 0 (trainProfile p.train.ψ) x := by
  set x' : ProfilePoint := (x.2.1, (x.2.2, x.1))
  have hd : DifferentiableAt ℝ (trainProfile p.train.ψ) x' :=
    (rawDiff_trainProfile_contDiffAt hb (show 0 < x'.2.2 from hx)).differentiableAt (by simp)
  have hV1 := streamV1_trainProfile p.train (show 0 ≤ x'.2.2 from hx.le) hd
  have hV2 := streamV2_trainProfile p.train (show 0 ≤ x'.2.2 from hx.le) hd
  have hR0 : ringEps 0 = 0 := by simp [ringEps]
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, merProfile, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      Axi.m0_zero, Axi.m1_zero, mul_one, mul_zero, add_zero]
    exact hV1.symm
  · simp only [Fin.mk_one, merProfile, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      Axi.m0_one, Axi.m1_one, mul_one, mul_zero, zero_add, axialProfile, hR0, zero_mul, add_zero]
    exact hV2.symm

/-- On the late region `1 ≤ x.1`, the train velocity is bounded by `C_t * (p.ν ^ k_t)⁻¹ * x.1 ^ (-1)`
and its spatial derivatives `∂_q v, ∂_η v` are bounded by `C_t * (p.ν ^ k_t)⁻¹ * x.1 ^ (-3/2)`. -/
theorem trainVel_tail_bound :
    ∃ (C_t : ℝ) (k_t : ℕ) (ν_t : ℝ), 0 < C_t ∧ 0 < ν_t ∧
      ∀ (p : Params) (d dm dp : ℝ), BgRegime p d dm dp → p.ν ≤ ν_t →
        ∀ x : Coord, 1 ≤ x.1 →
          ‖p.train.v x.1 x.2‖ ≤ C_t * (p.ν ^ k_t)⁻¹ * x.1 ^ (-1 : ℝ) ∧
          ‖Axi.dQ (fun m : Coord => p.train.v m.1 m.2) x‖ ≤
            C_t * (p.ν ^ k_t)⁻¹ * x.1 ^ (-(3 / 2 : ℝ)) ∧
          ‖Axi.dEta (fun m : Coord => p.train.v m.1 m.2) x‖ ≤
            C_t * (p.ν ^ k_t)⁻¹ * x.1 ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨_, w1, w32⟩ := ww_rawFam
  obtain ⟨C₁, k₁, ν₁, hC₁, hν₁, H1⟩ := ww_bound_bg w1
  obtain ⟨C₃₂, k₃₂, ν₃₂, hC₃₂, hν₃₂, H32⟩ := ww_bound_bg w32
  set B : ℝ := max C₁ C₃₂
  set k : ℕ := max k₁ k₃₂
  set ν₀ : ℝ := min (min ν₁ ν₃₂) 1
  have hB : 0 < B := lt_max_of_lt_left hC₁
  have hν₀ : 0 < ν₀ := lt_min (lt_min hν₁ hν₃₂) one_pos
  refine ⟨B, k, ν₀, hB, hν₀, fun p d dm dp hb hν x hx1 => ?_⟩
  have hx : 0 < x.1 := lt_of_lt_of_le zero_lt_one hx1
  have hνpos : 0 < p.ν := p.ν_pos
  have hνle1 : p.ν ≤ 1 := hν.trans (min_le_right _ _)
  have hν1 : p.ν ≤ ν₁ := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν32 : p.ν ≤ ν₃₂ := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hopen : {y : Coord | 0 < y.1} ∈ 𝓝 x :=
    (isOpen_lt continuous_const continuous_fst).mem_nhds hx
  have hL : (fun m : Coord => p.train.v m.1 m.2) =ᶠ[𝓝 x]
      merProfile 0 (trainProfile p.train.ψ) := by
    filter_upwards [hopen] with y hy
    exact trainVel_eq_merProfile_zero hb hy
  have hfderiv : fderiv ℝ (fun m : Coord => p.train.v m.1 m.2) x =
      fderiv ℝ (merProfile 0 (trainProfile p.train.ψ)) x := hL.fderiv_eq
  set x' : ProfilePoint := toProfile x
  have hs1 : 1 ≤ x'.2.2 := hx1
  have hC : ContDiffAt ℝ ∞ (trainProfile p.train.ψ) x' :=
    rawDiff_trainProfile_contDiffAt hb (show 0 < x'.2.2 from hx)
  have hR0 : ringEps 0 = 0 := by simp [ringEps]
  set ψ := trainProfile p.train.ψ
  have g1_def : rawFam1 p.ν p.c p.train x' =
      |streamV1 ψ x'| + |streamV2 ψ x'| + |partialEta (B0185.ageDefect ψ) x'| +
        |ageShift 1 (streamV1 ψ) x'| + |ageShift 1 (streamV2 ψ) x'| +
        |partialQ (B0185.ageDefect ψ) x'| := rfl
  have g32_def : rawFam32 p.ν p.c p.train x' =
      |partialEta (streamV1 ψ) x'| + |partialEta (streamV2 ψ) x'| +
        |partialQ (streamV1 ψ) x'| + |partialQ (streamV2 ψ) x'| +
        |ageShift 1 (B0185.ageDefect ψ) x'| := rfl
  have a3 := abs_nonneg (partialEta (B0185.ageDefect ψ) x')
  have a4 := abs_nonneg (ageShift 1 (streamV1 ψ) x')
  have a5 := abs_nonneg (ageShift 1 (streamV2 ψ) x')
  have a6 := abs_nonneg (partialQ (B0185.ageDefect ψ) x')
  have b1 := abs_nonneg (partialEta (streamV1 ψ) x')
  have b2 := abs_nonneg (partialEta (streamV2 ψ) x')
  have b3 := abs_nonneg (partialQ (streamV1 ψ) x')
  have b4 := abs_nonneg (partialQ (streamV2 ψ) x')
  have b5 := abs_nonneg (ageShift 1 (B0185.ageDefect ψ) x')
  have hb1 : rawFam1 p.ν p.c p.train x' ≤ B * (p.ν ^ k)⁻¹ * x.1 ^ (-1 : ℝ) := by
    refine (H1 p d dm dp hb hν1 x' hs1).trans ?_
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hx.le _)
    exact mul_le_mul (le_max_left _ _) (inv_pow_mono hνpos hνle1 (le_max_left _ _))
      (by positivity) hB.le
  have hb32 : rawFam32 p.ν p.c p.train x' ≤ B * (p.ν ^ k)⁻¹ * x.1 ^ (-(3 / 2 : ℝ)) := by
    refine (H32 p d dm dp hb hν32 x' hs1).trans ?_
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hx.le _)
    exact mul_le_mul (le_max_right _ _) (inv_pow_mono hνpos hνle1 (le_max_right _ _))
      (by positivity) hB.le
  refine ⟨?_, ?_, ?_⟩
  · rw [trainVel_eq_merProfile_zero hb hx]
    have h1 := norm_merid_pair_le (streamV1 ψ x') (axialProfile 0 ψ x')
    have h2 : axialProfile 0 ψ x' = streamV2 ψ x' := by
      simp [axialProfile, hR0]
    have hle1 : |streamV1 ψ x'| + |streamV2 ψ x'| ≤ rawFam1 p.ν p.c p.train x' := by
      rw [g1_def]; linarith
    change ‖streamV1 ψ x' • Axi.m0 + axialProfile 0 ψ x' • Axi.m1‖ ≤ _
    exact (h1.trans (by rw [h2])).trans (hle1.trans hb1)
  · have hdQ : Axi.dQ (fun m : Coord => p.train.v m.1 m.2) x =
        Axi.dQ (merProfile 0 ψ) x := by
      unfold Axi.dQ
      rw [hfderiv]
    rw [hdQ, dQ_merProfile hC, hR0, zero_mul, add_zero]
    have h1 := norm_merid_pair_le (partialQ (streamV1 ψ) x') (partialQ (streamV2 ψ) x')
    have hle32 : |partialQ (streamV1 ψ) x'| + |partialQ (streamV2 ψ) x'| ≤
        rawFam32 p.ν p.c p.train x' := by
      rw [g32_def]; linarith
    exact h1.trans (hle32.trans hb32)
  · have hdEta : Axi.dEta (fun m : Coord => p.train.v m.1 m.2) x =
        Axi.dEta (merProfile 0 ψ) x := by
      unfold Axi.dEta
      rw [hfderiv]
    rw [hdEta, dEta_merProfile hC, hR0, zero_mul, add_zero]
    have h1 := norm_merid_pair_le (partialEta (streamV1 ψ) x') (partialEta (streamV2 ψ) x')
    have hle32 : |partialEta (streamV1 ψ) x'| + |partialEta (streamV2 ψ) x'| ≤
        rawFam32 p.ν p.c p.train x' := by
      rw [g32_def]; linarith
    exact h1.trans (hle32.trans hb32)

/-! ### 2. Pointwise and restricted `eLpNorm` bounds for `flatK` -/

/-- On `0 < x.1`, `flatK` can be written in terms of the meridional chart derivatives `Axi.dQ` and
`Axi.dEta` of `(s, z) ↦ tr.v s z`. -/
theorem flatK_eq_on_pos {ν c : ℝ} (tr : B0140.TrainSol ν c) (b0 b0q b0η : CProf)
    {x : Coord} (hx : 0 < x.1) :
    flatK tr b0 b0q b0η x =
      x.1 • ((tr.v x.1 x.2 0 : ℂ) • b0q x + (tr.v x.1 x.2 1 : ℂ) • b0η x +
        b0 x 0 • liftM (Axi.dQ (fun m : Coord => tr.v m.1 m.2) x) +
        b0 x 1 • liftM (Axi.dEta (fun m : Coord => tr.v m.1 m.2) x)) := by
  have hdiff : DifferentiableAt ℝ (fun m : Coord => tr.v m.1 m.2) x :=
    ((tr.isTrain.smooth_v.mono fun y (hy : 0 < y.1) => ⟨hy.le, trivial⟩).differentiableOn
      (by simp)).differentiableAt ((isOpen_lt continuous_const continuous_fst).mem_nhds hx)
  have hQ : ∀ j : Fin 2, fderiv ℝ (fun z : ℝ × ℝ => tr.v x.1 z j) x.2 (1, 0) =
      Axi.dQ (fun m : Coord => tr.v m.1 m.2) x j := fun j =>
    flatPartial_comp_eq (fun m : Coord => tr.v m.1 m.2) x hdiff j (1, 0)
  have hE : ∀ j : Fin 2, fderiv ℝ (fun z : ℝ × ℝ => tr.v x.1 z j) x.2 (0, 1) =
      Axi.dEta (fun m : Coord => tr.v m.1 m.2) x j := fun j =>
    flatPartial_comp_eq (fun m : Coord => tr.v m.1 m.2) x hdiff j (0, 1)
  ext j
  simp only [flatK, liftM, PiLp.add_apply, PiLp.smul_apply, PiLp.toLp_apply,
    Complex.real_smul, smul_eq_mul]
  rw [hQ j, hE j]

/-- Norm of `sqrtS g x` for `0 ≤ x.1`. -/
theorem norm_sqrtS_of_nonneg (g : CProf) {x : Coord} (hx : 0 ≤ x.1) :
    ‖sqrtS g x‖ = Real.sqrt x.1 * ‖g x‖ := by
  unfold sqrtS
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg x.1)]

/-- Pointwise bound on `‖flatK tr b0 b0q b0η x‖` in terms of `‖sqrtS b0q x‖`, `‖sqrtS b0η x‖`,
and `‖b0 x‖` when `0 < x.1`. -/
theorem norm_flatK_le_of_vel_grad {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (b0 b0q b0η : CProf) {x : Coord} (hx : 0 < x.1) {V D : ℝ} (_hV0 : 0 ≤ V) (_hD0 : 0 ≤ D)
    (hV : ‖tr.v x.1 x.2‖ ≤ V)
    (hQ : ‖Axi.dQ (fun m : Coord => tr.v m.1 m.2) x‖ ≤ D)
    (hE : ‖Axi.dEta (fun m : Coord => tr.v m.1 m.2) x‖ ≤ D) :
    ‖flatK tr b0 b0q b0η x‖ ≤
      (V * Real.sqrt x.1) * ‖sqrtS b0q x‖ +
        (V * Real.sqrt x.1) * ‖sqrtS b0η x‖ +
        (2 * D * x.1) * ‖b0 x‖ := by
  have hs0 : 0 ≤ x.1 := hx.le
  have hv0 : |tr.v x.1 x.2 0| ≤ V := by
    have h := PiLp.norm_apply_le (tr.v x.1 x.2) 0
    rw [Real.norm_eq_abs] at h
    exact h.trans hV
  have hv1 : |tr.v x.1 x.2 1| ≤ V := by
    have h := PiLp.norm_apply_le (tr.v x.1 x.2) 1
    rw [Real.norm_eq_abs] at h
    exact h.trans hV
  have hb0 : ‖b0 x 0‖ ≤ ‖b0 x‖ := PiLp.norm_apply_le (b0 x) 0
  have hb1 : ‖b0 x 1‖ ≤ ‖b0 x‖ := PiLp.norm_apply_le (b0 x) 1
  have ht1 : ‖(tr.v x.1 x.2 0 : ℂ) • b0q x‖ ≤ V * ‖b0q x‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hv0 (norm_nonneg _)
  have ht2 : ‖(tr.v x.1 x.2 1 : ℂ) • b0η x‖ ≤ V * ‖b0η x‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hv1 (norm_nonneg _)
  have ht3 : ‖b0 x 0 • liftM (Axi.dQ (fun m : Coord => tr.v m.1 m.2) x)‖ ≤ ‖b0 x‖ * D := by
    rw [norm_smul, liftM_norm]
    exact mul_le_mul hb0 hQ (norm_nonneg _) (norm_nonneg _)
  have ht4 : ‖b0 x 1 • liftM (Axi.dEta (fun m : Coord => tr.v m.1 m.2) x)‖ ≤ ‖b0 x‖ * D := by
    rw [norm_smul, liftM_norm]
    exact mul_le_mul hb1 hE (norm_nonneg _) (norm_nonneg _)
  have hsum : ‖(tr.v x.1 x.2 0 : ℂ) • b0q x + (tr.v x.1 x.2 1 : ℂ) • b0η x +
      b0 x 0 • liftM (Axi.dQ (fun m : Coord => tr.v m.1 m.2) x) +
      b0 x 1 • liftM (Axi.dEta (fun m : Coord => tr.v m.1 m.2) x)‖ ≤
      V * ‖b0q x‖ + V * ‖b0η x‖ + ‖b0 x‖ * D + ‖b0 x‖ * D := by
    calc _ ≤ ‖(tr.v x.1 x.2 0 : ℂ) • b0q x + (tr.v x.1 x.2 1 : ℂ) • b0η x +
              b0 x 0 • liftM (Axi.dQ (fun m : Coord => tr.v m.1 m.2) x)‖ +
            ‖b0 x 1 • liftM (Axi.dEta (fun m : Coord => tr.v m.1 m.2) x)‖ := norm_add_le _ _
      _ ≤ ‖(tr.v x.1 x.2 0 : ℂ) • b0q x + (tr.v x.1 x.2 1 : ℂ) • b0η x‖ +
            ‖b0 x 0 • liftM (Axi.dQ (fun m : Coord => tr.v m.1 m.2) x)‖ +
            ‖b0 x 1 • liftM (Axi.dEta (fun m : Coord => tr.v m.1 m.2) x)‖ :=
          add_le_add (norm_add_le _ _) le_rfl
      _ ≤ ‖(tr.v x.1 x.2 0 : ℂ) • b0q x‖ + ‖(tr.v x.1 x.2 1 : ℂ) • b0η x‖ +
            ‖b0 x 0 • liftM (Axi.dQ (fun m : Coord => tr.v m.1 m.2) x)‖ +
            ‖b0 x 1 • liftM (Axi.dEta (fun m : Coord => tr.v m.1 m.2) x)‖ :=
          add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
      _ ≤ V * ‖b0q x‖ + V * ‖b0η x‖ + ‖b0 x‖ * D + ‖b0 x‖ * D := by linarith
  have hsq : Real.sqrt x.1 * Real.sqrt x.1 = x.1 := Real.mul_self_sqrt hs0
  rw [flatK_eq_on_pos tr b0 b0q b0η hx, norm_smul, Real.norm_of_nonneg hs0]
  calc x.1 * ‖(tr.v x.1 x.2 0 : ℂ) • b0q x + (tr.v x.1 x.2 1 : ℂ) • b0η x +
        b0 x 0 • liftM (Axi.dQ (fun m : Coord => tr.v m.1 m.2) x) +
        b0 x 1 • liftM (Axi.dEta (fun m : Coord => tr.v m.1 m.2) x)‖
      ≤ x.1 * (V * ‖b0q x‖ + V * ‖b0η x‖ + ‖b0 x‖ * D + ‖b0 x‖ * D) :=
        mul_le_mul_of_nonneg_left hsum hs0
    _ = (V * Real.sqrt x.1) * (Real.sqrt x.1 * ‖b0q x‖) +
          (V * Real.sqrt x.1) * (Real.sqrt x.1 * ‖b0η x‖) +
          (2 * D * x.1) * ‖b0 x‖ := by
        calc x.1 * (V * ‖b0q x‖ + V * ‖b0η x‖ + ‖b0 x‖ * D + ‖b0 x‖ * D)
            = (Real.sqrt x.1 * Real.sqrt x.1) * V * ‖b0q x‖ +
                (Real.sqrt x.1 * Real.sqrt x.1) * V * ‖b0η x‖ +
                (2 * D * x.1) * ‖b0 x‖ := by
              rw [hsq]; ring
          _ = _ := by ring
    _ = (V * Real.sqrt x.1) * ‖sqrtS b0q x‖ +
          (V * Real.sqrt x.1) * ‖sqrtS b0η x‖ +
          (2 * D * x.1) * ‖b0 x‖ := by
        rw [norm_sqrtS_of_nonneg b0q hs0, norm_sqrtS_of_nonneg b0η hs0]

/-- Restricted `eLpNorm` bound for `flatK` on a measurable set `S` where
`‖flatK x‖ ≤ A₁ ‖sqrtS b0q x‖ + A₁ ‖sqrtS b0η x‖ + A₂ ‖b0 x‖` for `0 < x.1`. -/
theorem eLpNorm_restrict_flatK_le {ν c : ℝ} (hc : 0 < c) (tr : B0140.TrainSol ν c)
    (b0 b0q b0η : CProf) (hb0 : InHr c bgp b0) (hq : InHr c bgp (sqrtS b0q))
    (hη : InHr c bgp (sqrtS b0η)) (S : Set Coord) (hS : MeasurableSet S)
    {A₁ A₂ : ℝ} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (hpt : ∀ x ∈ S, 0 < x.1 →
      ‖flatK tr b0 b0q b0η x‖ ≤
        A₁ * ‖sqrtS b0q x‖ + A₁ * ‖sqrtS b0η x‖ + A₂ * ‖b0 x‖) :
    eLpNorm (flatK tr b0 b0q b0η) (ENNReal.ofReal bgp) ((hMeas c bgp).restrict S) ≤
      ENNReal.ofReal A₁ * (hNorm c bgp (sqrtS b0q) + hNorm c bgp (sqrtS b0η)) +
        ENNReal.ofReal A₂ * hNorm c bgp b0 := by
  have hp1 : 1 ≤ ENNReal.ofReal bgp := by
    rw [ENNReal.one_le_ofReal]
    norm_num [bgp]
  have hae_pos : ∀ᵐ x ∂(hMeas c bgp), 0 < x.1 :=
    (Axi.ae_ageμ_mem hc (bgp / 2 - 5 / 2)).mono fun x hx => hx.1
  let fq : Coord → ℝ := fun x => A₁ • ‖sqrtS b0q x‖
  let fη : Coord → ℝ := fun x => A₁ • ‖sqrtS b0η x‖
  let fb : Coord → ℝ := fun x => A₂ • ‖b0 x‖
  have hfq_m : AEStronglyMeasurable fq (hMeas c bgp) := hq.meas.norm.const_smul A₁
  have hfη_m : AEStronglyMeasurable fη (hMeas c bgp) := hη.meas.norm.const_smul A₁
  have hfb_m : AEStronglyMeasurable fb (hMeas c bgp) := hb0.meas.norm.const_smul A₂
  have hae_res : ∀ᵐ x ∂((hMeas c bgp).restrict S),
      ‖flatK tr b0 b0q b0η x‖ ≤ ‖(fq + fη + fb) x‖ := by
    filter_upwards [ae_restrict_mem hS, ae_restrict_of_ae hae_pos] with x hxS hx0
    have hnn : 0 ≤ (fq + fη + fb) x := by
      change 0 ≤ A₁ * ‖sqrtS b0q x‖ + A₁ * ‖sqrtS b0η x‖ + A₂ * ‖b0 x‖
      positivity
    rw [Real.norm_of_nonneg hnn]
    exact hpt x hxS hx0
  have hmono1 : eLpNorm (flatK tr b0 b0q b0η) (ENNReal.ofReal bgp) ((hMeas c bgp).restrict S) ≤
      eLpNorm (fq + fη + fb) (ENNReal.ofReal bgp) (hMeas c bgp) :=
    (eLpNorm_mono_ae hae_res).trans (eLpNorm_mono_measure _ Measure.restrict_le_self)
  have hadd1 : eLpNorm (fq + fη + fb) (ENNReal.ofReal bgp) (hMeas c bgp) ≤
      eLpNorm (fq + fη) (ENNReal.ofReal bgp) (hMeas c bgp) +
        eLpNorm fb (ENNReal.ofReal bgp) (hMeas c bgp) :=
    eLpNorm_add_le (hfq_m.add hfη_m) hfb_m hp1
  have hadd2 : eLpNorm (fq + fη) (ENNReal.ofReal bgp) (hMeas c bgp) ≤
      eLpNorm fq (ENNReal.ofReal bgp) (hMeas c bgp) +
        eLpNorm fη (ENNReal.ofReal bgp) (hMeas c bgp) :=
    eLpNorm_add_le hfq_m hfη_m hp1
  have hsmul_q : eLpNorm fq (ENNReal.ofReal bgp) (hMeas c bgp) =
      ENNReal.ofReal A₁ * hNorm c bgp (sqrtS b0q) := by
    change eLpNorm (A₁ • fun x => ‖sqrtS b0q x‖) (ENNReal.ofReal bgp) (hMeas c bgp) = _
    rw [eLpNorm_const_smul, eLpNorm_norm, Real.enorm_eq_ofReal hA₁]
    rfl
  have hsmul_η : eLpNorm fη (ENNReal.ofReal bgp) (hMeas c bgp) =
      ENNReal.ofReal A₁ * hNorm c bgp (sqrtS b0η) := by
    change eLpNorm (A₁ • fun x => ‖sqrtS b0η x‖) (ENNReal.ofReal bgp) (hMeas c bgp) = _
    rw [eLpNorm_const_smul, eLpNorm_norm, Real.enorm_eq_ofReal hA₁]
    rfl
  have hsmul_b : eLpNorm fb (ENNReal.ofReal bgp) (hMeas c bgp) =
      ENNReal.ofReal A₂ * hNorm c bgp b0 := by
    change eLpNorm (A₂ • fun x => ‖b0 x‖) (ENNReal.ofReal bgp) (hMeas c bgp) = _
    rw [eLpNorm_const_smul, eLpNorm_norm, Real.enorm_eq_ofReal hA₂]
    rfl
  calc eLpNorm (flatK tr b0 b0q b0η) (ENNReal.ofReal bgp) ((hMeas c bgp).restrict S)
      ≤ eLpNorm (fq + fη) (ENNReal.ofReal bgp) (hMeas c bgp) +
          eLpNorm fb (ENNReal.ofReal bgp) (hMeas c bgp) := hmono1.trans hadd1
    _ ≤ (eLpNorm fq (ENNReal.ofReal bgp) (hMeas c bgp) +
          eLpNorm fη (ENNReal.ofReal bgp) (hMeas c bgp)) +
          eLpNorm fb (ENNReal.ofReal bgp) (hMeas c bgp) := add_le_add hadd2 le_rfl
    _ = ENNReal.ofReal A₁ * (hNorm c bgp (sqrtS b0q) + hNorm c bgp (sqrtS b0η)) +
          ENNReal.ofReal A₂ * hNorm c bgp b0 := by
        rw [hsmul_q, hsmul_η, hsmul_b, mul_add]

/-! ### 3. Measurability and positive-age periodicity of `flatK` -/

/-- `liftM : Axi.Merid → CMerid` is continuous. -/
theorem continuous_liftM : Continuous liftM := by
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℂ)).comp
    (continuous_pi fun j => Complex.continuous_ofReal.comp (EuclideanSpace.proj j).continuous)

/-- Under `InHr c bgp b0`, `InHr c bgp (sqrtS b0q)`, and `InHr c bgp (sqrtS b0η)`,
`flatK tr b0 b0q b0η` is `AEStronglyMeasurable` with respect to `hMeas c bgp`. -/
theorem aestronglyMeasurable_flatK {ν c : ℝ} (hc : 0 < c) (tr : B0140.TrainSol ν c)
    (b0 b0q b0η : CProf) (hb0 : InHr c bgp b0) (hq : InHr c bgp (sqrtS b0q))
    (hη : InHr c bgp (sqrtS b0η)) :
    AEStronglyMeasurable (flatK tr b0 b0q b0η) (hMeas c bgp) := by
  set U : Set Coord := {x : Coord | 0 < x.1}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_fst
  have hv_cd : ContDiffOn ℝ ∞ (fun m : Coord => tr.v m.1 m.2) U :=
    tr.isTrain.smooth_v.mono fun x (hx : 0 < x.1) => ⟨hx.le, trivial⟩
  have hdQ_cd : ContDiffOn ℝ ∞ (Axi.dQ (fun m : Coord => tr.v m.1 m.2)) U :=
    (hv_cd.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply contDiffOn_const
  have hdE_cd : ContDiffOn ℝ ∞ (Axi.dEta (fun m : Coord => tr.v m.1 m.2)) U :=
    (hv_cd.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply contDiffOn_const
  have hind_ae : ∀ {E : Type} [Zero E] (f : Coord → E), U.indicator f =ᵐ[hMeas c bgp] f := fun f => by
    filter_upwards [Axi.ae_ageμ_mem hc (bgp / 2 - 5 / 2)] with x hx
    exact Set.indicator_of_mem (show x ∈ U from hx.1) f
  have hv0_cont : ContinuousOn (fun x : Coord => (tr.v x.1 x.2 0 : ℂ)) U :=
    Complex.continuous_ofReal.comp_continuousOn
      ((EuclideanSpace.proj 0).continuous.comp_continuousOn hv_cd.continuousOn)
  have hv1_cont : ContinuousOn (fun x : Coord => (tr.v x.1 x.2 1 : ℂ)) U :=
    Complex.continuous_ofReal.comp_continuousOn
      ((EuclideanSpace.proj 1).continuous.comp_continuousOn hv_cd.continuousOn)
  have hdQ_cont : ContinuousOn
      (fun x : Coord => liftM (Axi.dQ (fun m : Coord => tr.v m.1 m.2) x)) U :=
    continuous_liftM.comp_continuousOn hdQ_cd.continuousOn
  have hdE_cont : ContinuousOn
      (fun x : Coord => liftM (Axi.dEta (fun m : Coord => tr.v m.1 m.2) x)) U :=
    continuous_liftM.comp_continuousOn hdE_cd.continuousOn
  have hv0_m : AEStronglyMeasurable (fun x : Coord => (tr.v x.1 x.2 0 : ℂ)) (hMeas c bgp) :=
    ((aestronglyMeasurable_indicator_iff hU.measurableSet).mpr
      (hv0_cont.aestronglyMeasurable hU.measurableSet)).congr (hind_ae _)
  have hv1_m : AEStronglyMeasurable (fun x : Coord => (tr.v x.1 x.2 1 : ℂ)) (hMeas c bgp) :=
    ((aestronglyMeasurable_indicator_iff hU.measurableSet).mpr
      (hv1_cont.aestronglyMeasurable hU.measurableSet)).congr (hind_ae _)
  have hdQ_m : AEStronglyMeasurable
      (fun x : Coord => liftM (Axi.dQ (fun m : Coord => tr.v m.1 m.2) x)) (hMeas c bgp) :=
    ((aestronglyMeasurable_indicator_iff hU.measurableSet).mpr
      (hdQ_cont.aestronglyMeasurable hU.measurableSet)).congr (hind_ae _)
  have hdE_m : AEStronglyMeasurable
      (fun x : Coord => liftM (Axi.dEta (fun m : Coord => tr.v m.1 m.2) x)) (hMeas c bgp) :=
    ((aestronglyMeasurable_indicator_iff hU.measurableSet).mpr
      (hdE_cont.aestronglyMeasurable hU.measurableSet)).congr (hind_ae _)
  have hinv_m : AEStronglyMeasurable (fun x : Coord => ((Real.sqrt x.1)⁻¹ : ℂ)) (hMeas c bgp) := by
    have hm : Measurable (fun x : Coord => ((Real.sqrt x.1)⁻¹ : ℂ)) := by fun_prop
    exact hm.aestronglyMeasurable
  have hq_ae : (fun x : Coord => ((Real.sqrt x.1)⁻¹ : ℂ) • sqrtS b0q x) =ᵐ[hMeas c bgp] b0q := by
    filter_upwards [Axi.ae_ageμ_mem hc (bgp / 2 - 5 / 2)] with x hx
    have hs : ((Real.sqrt x.1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hx.1).ne'
    unfold sqrtS
    rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
  have hη_ae : (fun x : Coord => ((Real.sqrt x.1)⁻¹ : ℂ) • sqrtS b0η x) =ᵐ[hMeas c bgp] b0η := by
    filter_upwards [Axi.ae_ageμ_mem hc (bgp / 2 - 5 / 2)] with x hx
    have hs : ((Real.sqrt x.1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hx.1).ne'
    unfold sqrtS
    rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
  have hb0q_m : AEStronglyMeasurable b0q (hMeas c bgp) :=
    (hinv_m.smul hq.meas).congr hq_ae
  have hb0η_m : AEStronglyMeasurable b0η (hMeas c bgp) :=
    (hinv_m.smul hη.meas).congr hη_ae
  have hb0_0_m : AEStronglyMeasurable (fun x : Coord => b0 x 0) (hMeas c bgp) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℂ) 0).comp_aestronglyMeasurable hb0.meas
  have hb0_1_m : AEStronglyMeasurable (fun x : Coord => b0 x 1) (hMeas c bgp) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℂ) 1).comp_aestronglyMeasurable hb0.meas
  have hs_m : AEStronglyMeasurable (fun x : Coord => x.1) (hMeas c bgp) :=
    continuous_fst.aestronglyMeasurable
  have hrhs_m : AEStronglyMeasurable
      (fun x : Coord => x.1 • ((tr.v x.1 x.2 0 : ℂ) • b0q x + (tr.v x.1 x.2 1 : ℂ) • b0η x +
        b0 x 0 • liftM (Axi.dQ (fun m : Coord => tr.v m.1 m.2) x) +
        b0 x 1 • liftM (Axi.dEta (fun m : Coord => tr.v m.1 m.2) x)))
      (hMeas c bgp) :=
    hs_m.smul
      ((((hv0_m.smul hb0q_m).add (hv1_m.smul hb0η_m)).add
        (hb0_0_m.smul hdQ_m)).add (hb0_1_m.smul hdE_m))
  refine hrhs_m.congr ?_
  filter_upwards [Axi.ae_ageμ_mem hc (bgp / 2 - 5 / 2)] with x hx
  exact (flatK_eq_on_pos tr b0 b0q b0η hx.1).symm

/-! ### 4. Periodicity of `flatK` -/

theorem fderiv_train_periodic {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s) (i : Fin 2)
    (z : ℝ × ℝ) :
    fderiv ℝ (fun w => tr.v s w i) (z.1 + c, z.2) = fderiv ℝ (fun w => tr.v s w i) z := by
  set g : ℝ × ℝ → ℝ := fun w => tr.v s w i with hg
  have hper : (fun y => g (y + (c, 0))) = g := by
    funext y
    have e : y + (c, 0) = (y.1 + c, y.2) := by ext <;> simp
    have := tr.isTrain.periodic_v s hs y
    simp only [hg]
    rw [e, this]
  have h := fderiv_comp_add_right (𝕜 := ℝ) (f := g) (c, 0) (x := z)
  rw [hper] at h
  have e : (z.1 + c, z.2) = z + (c, 0) := by ext <;> simp
  rw [e, ← h]

theorem qPeriodic_flatK {ν c : ℝ} (tr : B0140.TrainSol ν c) (b0 b0q b0η : CProf)
    (hb0 : QPeriodic c b0) (hq : QPeriodic c (sqrtS b0q)) (hη : QPeriodic c (sqrtS b0η)) :
    QPeriodic c (flatK tr b0 b0q b0η) := by
  unfold QPeriodic at *
  have hmeas : MeasurableSet {x : Coord | 0 < x.1} := measurableSet_lt measurable_const measurable_fst
  filter_upwards [hb0, hq, hη, ae_restrict_mem hmeas] with x h0 h1 h2 hx
  have hx' : (0 : ℝ) < x.1 := hx
  have hsq : ((Real.sqrt x.1 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hx').ne'
  have hq' : b0q (qShift c x) = b0q x := by
    have : ((Real.sqrt x.1 : ℝ) : ℂ) • b0q (qShift c x) = ((Real.sqrt x.1 : ℝ) : ℂ) • b0q x := by
      simpa [sqrtS, qShift] using h1
    exact smul_right_injective _ hsq this
  have hη' : b0η (qShift c x) = b0η x := by
    have : ((Real.sqrt x.1 : ℝ) : ℂ) • b0η (qShift c x) = ((Real.sqrt x.1 : ℝ) : ℂ) • b0η x := by
      simpa [sqrtS, qShift] using h2
    exact smul_right_injective _ hsq this
  ext i
  have hv : ∀ j : Fin 2, tr.v x.1 (x.2.1 + c, x.2.2) j = tr.v x.1 x.2 j := fun j => by
    have := tr.isTrain.periodic_v x.1 hx'.le x.2
    rw [this]
  have h0'' : b0 (x.1, x.2.1 + c, x.2.2) = b0 x := h0
  have hq'' : b0q (x.1, x.2.1 + c, x.2.2) = b0q x := hq'
  have hη'' : b0η (x.1, x.2.1 + c, x.2.2) = b0η x := hη'
  have hd := fun (j : Fin 2) => fderiv_train_periodic tr hx'.le j x.2
  simp only [flatK, qShift, h0'', hq'', hη'', hv, hd]

/-! ### 5. Finiteness from two pieces and an `ENNReal` bookkeeping lemma -/

theorem eLpNorm_lt_top_of_two {f : Coord → CMerid} {μ : Measure Coord} {p : ℝ} (hp : 1 ≤ p)
    {S T : Set Coord} (hcov : ∀ᵐ x ∂μ, x ∈ S ∪ T)
    (h1 : eLpNorm f (ENNReal.ofReal p) (μ.restrict S) < ⊤)
    (h2 : eLpNorm f (ENNReal.ofReal p) (μ.restrict T) < ⊤) :
    eLpNorm f (ENNReal.ofReal p) μ < ⊤ := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by
    simpa using (lt_of_lt_of_le one_pos hp)
  have hpt : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hpt] at h1 h2 ⊢
  have hle : μ ≤ μ.restrict S + μ.restrict T := by
    calc μ = μ.restrict (S ∪ T) := (Measure.restrict_eq_self_of_ae_mem hcov).symm
      _ ≤ _ := Measure.restrict_union_le _ _
  calc ∫⁻ x, ‖f x‖ₑ ^ (ENNReal.ofReal p).toReal ∂μ
      ≤ ∫⁻ x, ‖f x‖ₑ ^ (ENNReal.ofReal p).toReal ∂(μ.restrict S + μ.restrict T) :=
        lintegral_mono' hle le_rfl
    _ = _ := lintegral_add_measure _ _ _
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨h1, h2⟩

theorem enn_combine {ν Cfl A1 A2 : ℝ} (hν : 0 < ν) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2)
    (hC : 0 ≤ Cfl) {hb hq hη hF : ℝ≥0∞}
    (h : hb + ENNReal.ofReal (Real.sqrt ν) * (hq + hη) ≤ ENNReal.ofReal Cfl * hF) :
    ENNReal.ofReal A1 * (hq + hη) + ENNReal.ofReal A2 * hb ≤
      ENNReal.ofReal (Cfl * (A1 * ν ^ (-1 / 2 : ℝ) + A2)) * hF := by
  have hsq : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hnu : ν ^ (-1 / 2 : ℝ) * Real.sqrt ν = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hν]; norm_num
  have hA1eq : ENNReal.ofReal A1 =
      ENNReal.ofReal (A1 * ν ^ (-1 / 2 : ℝ)) * ENNReal.ofReal (Real.sqrt ν) := by
    rw [← ENNReal.ofReal_mul (by positivity), mul_assoc, hnu, mul_one]
  have h1 : ENNReal.ofReal (Real.sqrt ν) * (hq + hη) ≤ ENNReal.ofReal Cfl * hF :=
    le_trans le_add_self h
  have h2 : hb ≤ ENNReal.ofReal Cfl * hF := le_trans le_self_add h
  calc ENNReal.ofReal A1 * (hq + hη) + ENNReal.ofReal A2 * hb
      = ENNReal.ofReal (A1 * ν ^ (-1 / 2 : ℝ)) * (ENNReal.ofReal (Real.sqrt ν) * (hq + hη)) +
          ENNReal.ofReal A2 * hb := by rw [hA1eq, mul_assoc]
    _ ≤ ENNReal.ofReal (A1 * ν ^ (-1 / 2 : ℝ)) * (ENNReal.ofReal Cfl * hF) +
          ENNReal.ofReal A2 * (ENNReal.ofReal Cfl * hF) := add_le_add (by gcongr) (by gcongr)
    _ = ENNReal.ofReal (Cfl * (A1 * ν ^ (-1 / 2 : ℝ) + A2)) * hF := by
        rw [← add_mul, ← ENNReal.ofReal_add (by positivity) hA2, ← mul_assoc,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring/-! ### 6. Real-number helpers for the two regions -/

theorem rpow_neg_one_mul_sqrt {x : ℝ} (hx : 0 < x) :
    x ^ (-1 : ℝ) * Real.sqrt x = x ^ (-1 / 2 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx]; norm_num

theorem rpow_neg_three_halves_mul {x : ℝ} (hx : 0 < x) :
    x ^ (-(3 / 2) : ℝ) * x = x ^ (-1 / 2 : ℝ) := by
  calc x ^ (-(3 / 2) : ℝ) * x = x ^ (-(3 / 2) : ℝ) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
    _ = x ^ (-(3 / 2) + 1 : ℝ) := (Real.rpow_add hx _ _).symm
    _ = x ^ (-1 / 2 : ℝ) := by norm_num

end FreeInteractionAux

open FreeInteractionAux in
/-- **`PartII-b:F9/1`**: the free interaction bound (SP 2329-2334). -/
theorem flatFreeInteractionStep_proof : FlatFreeInteractionStep := by
  intro Sig lam q hSig hEig dm dp hdm
  obtain ⟨Cfl, hCfl, hFl⟩ := flat_graph_bound_bgp
  obtain ⟨Cb, kb, νb, hCb, hνb, Hb⟩ := trainVel_band_bound Sig hSig dm dp hdm
  obtain ⟨Ct, kt, νt, hCt, hνt, Ht⟩ := trainVel_tail_bound
  refine ⟨2 * Cfl * (Cb + Ct), max kb kt, min (min νb νt) (min Sig 1), by positivity,
    lt_min (lt_min hνb hνt) (lt_min hSig one_pos), ?_⟩
  intro p d hb hν hSigp _hmode F b0 hF hb0 hresp
  have hνpos : 0 < p.ν := p.ν_pos
  have hνb' : p.ν ≤ νb := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hνt' : p.ν ≤ νt := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hνS : p.ν ≤ Sig := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν1 : p.ν ≤ 1 := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hc : 0 < p.c := by rw [hb.c_eq]; positivity
  have hHdef : p.H = Sig / p.ν := by rw [← hSigp]; rfl
  have hH1 : 1 ≤ p.H := by rw [hHdef]; exact (one_le_div hνpos).2 hνS
  have hH0 : 0 < p.H := lt_of_lt_of_le one_pos hH1
  -- weak derivatives
  obtain ⟨Sb, Qb, Eb, _hS, hQ, hE, hbd⟩ := hFl p.ν p.c hνpos hc F b0 hF hb0 hresp
  obtain ⟨Sb', Qb', Eb', _, hQ', hE', _, hq', hη'⟩ := hb0.deriv
  have hv : vQ 0 = vQ0 := by funext x; simp [vQ, vQ0]
  have hd : dQ 0 = dZero := by funext x; simp [dQ, dZero]
  rw [hv, hd] at hQ
  have hQQ : Qb =ᵐ[hMeas p.c bgp] Qb' := hasWeakVec_unique_ae hc hQ hQ'
  have hEE : Eb =ᵐ[hMeas p.c bgp] Eb' := hasWeakVec_unique_ae hc hE hE'
  have hnQ : hNorm p.c bgp (sqrtS Qb) = hNorm p.c bgp (sqrtS Qb') :=
    eLpNorm_congr_ae (sqrtS_congr_ae hQQ)
  have hnE : hNorm p.c bgp (sqrtS Eb) = hNorm p.c bgp (sqrtS Eb') :=
    eLpNorm_congr_ae (sqrtS_congr_ae hEE)
  have hbd' : hNorm p.c bgp b0 + ENNReal.ofReal (Real.sqrt p.ν) *
      (hNorm p.c bgp (sqrtS Qb') + hNorm p.c bgp (sqrtS Eb')) ≤
      ENNReal.ofReal Cfl * hNorm p.c bgp F := by
    rw [← hnQ, ← hnE]
    refine le_trans ?_ hbd
    calc _ ≤ hNorm p.c bgp b0 + ENNReal.ofReal (Real.sqrt p.ν) *
          (hNorm p.c bgp (sqrtS Qb) + hNorm p.c bgp (sqrtS Eb)) + hNorm p.c bgp Sb := le_self_add
      _ = _ := add_right_comm _ _ _
  refine ⟨Qb', Eb', hQ', hE', ?_⟩
  -- constants
  set W : ℝ := ((p.ν ^ (max kb kt)))⁻¹ with hW
  have hWb : ((p.ν ^ kb))⁻¹ ≤ W := by
    rw [hW]
    exact inv_anti₀ (by positivity) (pow_le_pow_of_le_one hνpos.le hν1 (le_max_left _ _))
  have hWt : ((p.ν ^ kt))⁻¹ ≤ W := by
    rw [hW]
    exact inv_anti₀ (by positivity) (pow_le_pow_of_le_one hνpos.le hν1 (le_max_right _ _))
  have hW0 : 0 < W := by rw [hW]; positivity
  have hfin : hNorm p.c bgp F < ⊤ := hF.finite
  -- early region
  have hearly : eLpNorm (flatK p.train b0 Qb' Eb') (ENNReal.ofReal bgp)
      ((hMeas p.c bgp).restrict (Ioc 0 p.H ×ˢ univ)) ≤
      ENNReal.ofReal (2 * Cfl * (Cb + Ct) * W *
        (p.ν ^ (-1 / 2 : ℝ) * Real.sqrt p.H + p.H)) * hNorm p.c bgp F := by
    set V : ℝ := Cb * (p.ν ^ kb)⁻¹ with hVdef
    have hV0 : 0 ≤ V := by positivity
    have h1 := eLpNorm_restrict_flatK_le hc p.train b0 Qb' Eb' hb0.inHr hq' hη'
      (Ioc 0 p.H ×ˢ univ) (measurableSet_Ioc.prod MeasurableSet.univ)
      (A₁ := V * Real.sqrt p.H) (A₂ := 2 * V * p.H) (by positivity) (by positivity)
      (fun x hx hx0 => by
        have hxH : x.1 ≤ p.H := hx.1.2
        have hsx : Real.sqrt x.1 ≤ Real.sqrt p.H := Real.sqrt_le_sqrt hxH
        obtain ⟨h1, h2, h3⟩ := Hb p d hb hνb' hSigp x hx0 hxH
        have := norm_flatK_le_of_vel_grad p.train b0 Qb' Eb' hx0 hV0 hV0 h1 h2 h3
        refine this.trans ?_
        have n1 := norm_nonneg (sqrtS Qb' x)
        have n2 := norm_nonneg (sqrtS Eb' x)
        have n3 := norm_nonneg (b0 x)
        gcongr)
    refine h1.trans ((enn_combine hνpos (by positivity) (by positivity) hCfl.le hbd').trans ?_)
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
    have hP : 0 ≤ p.ν ^ (-1 / 2 : ℝ) * Real.sqrt p.H := by positivity
    have hVW : V ≤ Cb * W := by rw [hVdef]; gcongr
    have e : V * Real.sqrt p.H * p.ν ^ (-1 / 2 : ℝ) = V * (p.ν ^ (-1 / 2 : ℝ) * Real.sqrt p.H) := by
      ring
    rw [e]
    have hCtW : 0 ≤ Ct * W * (p.ν ^ (-1 / 2 : ℝ) * Real.sqrt p.H + p.H) := by positivity
    have hVV : V * (p.ν ^ (-1 / 2 : ℝ) * Real.sqrt p.H) + 2 * V * p.H ≤
        2 * (Cb * W) * (p.ν ^ (-1 / 2 : ℝ) * Real.sqrt p.H + p.H) := by
      nlinarith [mul_nonneg hV0 hP, mul_nonneg hV0 hH0.le, mul_le_mul_of_nonneg_right hVW hP,
        mul_le_mul_of_nonneg_right hVW hH0.le]
    nlinarith [mul_le_mul_of_nonneg_left hVV hCfl.le, mul_nonneg hCfl.le hCtW]
  -- late region
  have hlate : eLpNorm (flatK p.train b0 Qb' Eb') (ENNReal.ofReal bgp)
      ((hMeas p.c bgp).restrict (Ioi p.H ×ˢ univ)) ≤
      ENNReal.ofReal (2 * Cfl * (Cb + Ct) * W * p.H ^ (-1 / 2 : ℝ) *
        (p.ν ^ (-1 / 2 : ℝ) + 1)) * hNorm p.c bgp F := by
    set U : ℝ := Ct * (p.ν ^ kt)⁻¹ with hUdef
    have hU0 : 0 ≤ U := by positivity
    have hHr : 0 ≤ p.H ^ (-1 / 2 : ℝ) := by positivity
    have h1 := eLpNorm_restrict_flatK_le hc p.train b0 Qb' Eb' hb0.inHr hq' hη'
      (Ioi p.H ×ˢ univ) (measurableSet_Ioi.prod MeasurableSet.univ)
      (A₁ := U * p.H ^ (-1 / 2 : ℝ)) (A₂ := 2 * U * p.H ^ (-1 / 2 : ℝ))
      (by positivity) (by positivity)
      (fun x hx hx0 => by
        have hxH : p.H < x.1 := hx.1
        have hx1 : 1 ≤ x.1 := hH1.trans hxH.le
        obtain ⟨h1, h2, h3⟩ := Ht p d dm dp hb hνt' x hx1
        have hV0 : 0 ≤ U * x.1 ^ (-1 : ℝ) := by positivity
        have hD0 : 0 ≤ U * x.1 ^ (-(3 / 2) : ℝ) := by positivity
        have := norm_flatK_le_of_vel_grad p.train b0 Qb' Eb' hx0 hV0 hD0
          (by simpa [hUdef, mul_assoc] using h1) (by simpa [hUdef, mul_assoc] using h2)
          (by simpa [hUdef, mul_assoc] using h3)
        refine this.trans ?_
        have hr : x.1 ^ (-1 / 2 : ℝ) ≤ p.H ^ (-1 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_nonpos hH0 hxH.le (by norm_num)
        have e1 : U * x.1 ^ (-1 : ℝ) * Real.sqrt x.1 = U * x.1 ^ (-1 / 2 : ℝ) := by
          rw [mul_assoc, rpow_neg_one_mul_sqrt hx0]
        have e2 : 2 * (U * x.1 ^ (-(3 / 2) : ℝ)) * x.1 = 2 * U * x.1 ^ (-1 / 2 : ℝ) := by
          rw [← rpow_neg_three_halves_mul hx0]; ring
        rw [e1, e2]
        have n1 := norm_nonneg (sqrtS Qb' x)
        have n2 := norm_nonneg (sqrtS Eb' x)
        have n3 := norm_nonneg (b0 x)
        have g1 : U * x.1 ^ (-1 / 2 : ℝ) ≤ U * p.H ^ (-1 / 2 : ℝ) := by gcongr
        have g2 : 2 * U * x.1 ^ (-1 / 2 : ℝ) ≤ 2 * U * p.H ^ (-1 / 2 : ℝ) := by gcongr
        gcongr)
    refine h1.trans ((enn_combine hνpos (by positivity) (by positivity) hCfl.le hbd').trans ?_)
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
    have hUW : U ≤ Ct * W := by rw [hUdef]; gcongr
    have hP : 0 ≤ p.ν ^ (-1 / 2 : ℝ) := by positivity
    have hUU : U * (p.ν ^ (-1 / 2 : ℝ) + 2) ≤ Ct * W * (p.ν ^ (-1 / 2 : ℝ) + 2) :=
      mul_le_mul_of_nonneg_right hUW (by positivity)
    have hfin2 : 0 ≤ Cb * W * (p.ν ^ (-1 / 2 : ℝ) + 1) := by positivity
    have e : Cfl * (U * p.H ^ (-1 / 2 : ℝ) * p.ν ^ (-1 / 2 : ℝ) + 2 * U * p.H ^ (-1 / 2 : ℝ)) =
        Cfl * p.H ^ (-1 / 2 : ℝ) * (U * (p.ν ^ (-1 / 2 : ℝ) + 2)) := by ring
    rw [e]
    have hCH : 0 ≤ Cfl * p.H ^ (-1 / 2 : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left hUU hCH
    have hle2 : Ct * W * (p.ν ^ (-1 / 2 : ℝ) + 2) ≤
        2 * (Cb + Ct) * W * (p.ν ^ (-1 / 2 : ℝ) + 1) := by
      nlinarith [mul_nonneg hCb.le hW0.le, mul_nonneg (mul_nonneg hCb.le hW0.le) hP,
        mul_nonneg (mul_nonneg hCt.le hW0.le) hP, mul_nonneg hCt.le hW0.le]
    have := mul_le_mul_of_nonneg_left hle2 hCH
    nlinarith [this]
  have hpos : ∀ᵐ x ∂(hMeas p.c bgp), x ∈ (Ioc 0 p.H ×ˢ univ) ∪ (Ioi p.H ×ˢ univ) := by
    filter_upwards [(Axi.ae_ageμ_mem hc (bgp / 2 - 5 / 2))] with x hx
    by_cases h : x.1 ≤ p.H
    · exact Or.inl ⟨⟨hx.1, h⟩, trivial⟩
    · exact Or.inr ⟨not_le.1 h, trivial⟩
  have hlt : ∀ {B : ℝ}, ∀ {S : Set Coord},
      eLpNorm (flatK p.train b0 Qb' Eb') (ENNReal.ofReal bgp) ((hMeas p.c bgp).restrict S) ≤
        ENNReal.ofReal B * hNorm p.c bgp F →
      eLpNorm (flatK p.train b0 Qb' Eb') (ENNReal.ofReal bgp) ((hMeas p.c bgp).restrict S) < ⊤ :=
    fun h => lt_of_le_of_lt h (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)
  refine ⟨⟨qPeriodic_flatK p.train b0 Qb' Eb' hb0.inHr.periodic hq'.periodic hη'.periodic,
    aestronglyMeasurable_flatK hc p.train b0 Qb' Eb' hb0.inHr hq' hη', ?_⟩, ?_, ?_⟩
  · exact eLpNorm_lt_top_of_two (by norm_num [bgp]) hpos (hlt hearly) (hlt hlate)
  · exact hearly
  · exact hlate

end UnforcedLeray.Short.IIb

end
