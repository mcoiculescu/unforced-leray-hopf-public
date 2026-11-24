import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F5_2
import UnforcedLeray.Short.PartI.Sub.PartI_T25_1
import UnforcedLeray.Short.PartI.Tasks.OverlapHighNorm
import UnforcedLeray.Short.PartI.Tasks.OverlapFluctuationDecay
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanPrimitive
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanDecay
import UnforcedLeray.Short.PartI.Tasks.TrainOverlapProof
import UnforcedLeray.Short.PartI.Tasks.TrainVorticityTail
import UnforcedLeray.Short.PartI.Tasks.TrainStreamTails

/-!
# Part II-b, task `PartII-b:F5/2/1`: `TrainWeightedLp22over3`

Source of record: `the November 2 reference manuscript` (SP), lines 2050-2052,
2228-2233, and Part I Lemma `sct:heat` (SP 437-481).

Proves `trainWeightedLp22over3_proof : TrainWeightedLp22over3`: on the slow-age band
`s ∈ (0, Σ / p.ν]` in `BgRegime p d dm dp`,
`trainSliceNorm22_3 p.c m p.train s * ENNReal.ofReal (p.c ^ (4 / 11 : ℝ))` is bounded by
`ENNReal.ofReal (C_tr * (p.ν ^ k_tr)⁻¹)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Real
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec jap jet)
open UnforcedLeray.Short.PartI (ageJet polyPS trainPeriod IsBUCTrain wSupNorm)
open UnforcedLeray.Short.PartI (OverlapFluctuationDecay overlap_fluctuation_decay overlap_highnorm_uniform)
open UnforcedLeray.Short.PartI (TrainOverlap trainOverlap_proof overlap_mean_decay overlap_mean_primitive)
open UnforcedLeray.Short.PartI (TrainStreamVelocityPressureTails train_stream_velocity_pressure_tails)
open UnforcedLeray.Short.PartI (train_vorticity_gaussian_tail)

namespace TrainLp22over3Aux

/-! ### 1. Unconditional Part I weighted `wSupNorm` train bounds -/

private theorem overlapFD_uncond : OverlapFluctuationDecay :=
  overlap_fluctuation_decay overlap_highnorm_uniform

private theorem trainOverlap_uncond : TrainOverlap :=
  trainOverlap_proof overlapFD_uncond
    (overlap_mean_decay overlap_highnorm_uniform overlapFD_uncond overlap_mean_primitive)

private theorem trainStreamVelocityPressureTails_uncond : TrainStreamVelocityPressureTails :=
  train_stream_velocity_pressure_tails trainOverlap_uncond
    (train_vorticity_gaussian_tail trainOverlap_uncond)

private theorem sqrt_jap_mul_norm_le_of_wSupNorm_le {E : Type*} [NormedAddCommGroup E]
    (k : ℕ) {f : Plane → E} {B : ℝ} (hB : 0 ≤ B)
    (h : wSupNorm k f ≤ ENNReal.ofReal B) (z : Plane) :
    Real.sqrt (jap k z) * ‖f z‖ ≤ B := by
  have hz : ENNReal.ofReal (Real.sqrt (jap k z)) * ‖f z‖ₑ ≤ ENNReal.ofReal B :=
    (le_iSup (fun w : Plane => ENNReal.ofReal (Real.sqrt (jap k w)) * ‖f w‖ₑ) z).trans h
  rw [← ofReal_norm, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at hz
  exact (ENNReal.ofReal_le_ofReal_iff hB).1 hz

/-! ### 2. Pointwise control of `trainJetPt` by `ageJet 0 j tr.v` (`j = 0, 1, 2`) -/

private theorem contDiff_train_v_slice {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s) :
    ContDiff ℝ ∞ (tr.v s) := by
  have hslice : ContDiffOn ℝ ∞ (fun z : Plane => tr.v s z) univ :=
    tr.isTrain.smooth_v.comp ((contDiffOn_const (c := s)).prodMk contDiffOn_id)
      (fun z _ => (⟨hs, mem_univ z⟩ : ((s, z) : ℝ × Plane) ∈ Ici 0 ×ˢ univ))
  exact contDiffOn_univ.1 hslice

private theorem abs_tr_v_le_ageJet0 {ν c : ℝ} (tr : B0140.TrainSol ν c) (s : ℝ) (z : Plane)
    (i : Fin 2) : |tr.v s z i| ≤ ‖ageJet 0 0 tr.v s z‖ := by
  have h1 : |tr.v s z i| ≤ ‖tr.v s z‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (tr.v s z) i
  have h0 : ‖ageJet 0 0 tr.v s z‖ = ‖tr.v s z‖ := by
    simp [ageJet, jet, iteratedDeriv_zero, norm_iteratedFDeriv_zero]
  linarith

private theorem abs_trD1_le_ageJet1 {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s)
    {d : Plane} (hd : ‖d‖ ≤ 1) (z : Plane) (i : Fin 2) :
    |trD1 tr d s z i| ≤ ‖ageJet 0 1 tr.v s z‖ := by
  have hu : ContDiff ℝ ∞ (tr.v s) := contDiff_train_v_slice tr hs
  have hdu : Differentiable ℝ (tr.v s) := hu.differentiable (by simp)
  have heq : trD1 tr d s z i = Dv d (tr.v s) z i := by
    unfold trD1
    have h := congrFun (Dv_proj hdu d i) z
    exact h
  rw [heq]
  have h1 : |Dv d (tr.v s) z i| ≤ ‖Dv d (tr.v s) z‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (Dv d (tr.v s) z) i
  have h2 : ‖Dv d (tr.v s) z‖ = ‖iteratedFDeriv ℝ 0 (Dv d (tr.v s)) z‖ :=
    (norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := Dv d (tr.v s)) (x := z)).symm
  have h3 := norm_jet_Dv_le hu d 0 z
  have h4 : ‖iteratedFDeriv ℝ 1 (tr.v s) z‖ = ‖ageJet 0 1 tr.v s z‖ := by
    simp [ageJet, jet, iteratedDeriv_zero]
  nlinarith [norm_nonneg (ageJet 0 1 tr.v s z)]

private theorem abs_trD2_le_ageJet2 {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s)
    {d₁ d₂ : Plane} (hd₁ : ‖d₁‖ ≤ 1) (hd₂ : ‖d₂‖ ≤ 1) (z : Plane) (i : Fin 2) :
    |trD2 tr d₁ d₂ s z i| ≤ ‖ageJet 0 2 tr.v s z‖ := by
  have hu : ContDiff ℝ ∞ (tr.v s) := contDiff_train_v_slice tr hs
  have hdu : Differentiable ℝ (tr.v s) := hu.differentiable (by simp)
  have hu1 : ContDiff ℝ ∞ (Dv d₁ (tr.v s)) := contDiff_Dv hu d₁
  have hdu1 : Differentiable ℝ (Dv d₁ (tr.v s)) := hu1.differentiable (by simp)
  have heq : trD2 tr d₁ d₂ s z i = Dv d₂ (Dv d₁ (tr.v s)) z i := by
    unfold trD2
    have hproj1 : (fun w => fderiv ℝ (fun y => tr.v s y i) w d₁) =
        fun w => Dv d₁ (tr.v s) w i := Dv_proj hdu d₁ i
    rw [hproj1]
    exact congrFun (Dv_proj hdu1 d₂ i) z
  rw [heq]
  have h1 : |Dv d₂ (Dv d₁ (tr.v s)) z i| ≤ ‖Dv d₂ (Dv d₁ (tr.v s)) z‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (Dv d₂ (Dv d₁ (tr.v s)) z) i
  have h2 : ‖Dv d₂ (Dv d₁ (tr.v s)) z‖ = ‖iteratedFDeriv ℝ 0 (Dv d₂ (Dv d₁ (tr.v s))) z‖ :=
    (norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := Dv d₂ (Dv d₁ (tr.v s))) (x := z)).symm
  have h3 := norm_jet_Dv_le hu1 d₂ 0 z
  have h4 := norm_jet_Dv_le hu d₁ 1 z
  have h5 : ‖iteratedFDeriv ℝ 2 (tr.v s) z‖ = ‖ageJet 0 2 tr.v s z‖ := by
    simp [ageJet, jet, iteratedDeriv_zero]
  have h3' : ‖iteratedFDeriv ℝ 0 (Dv d₂ (Dv d₁ (tr.v s))) z‖ ≤
      ‖iteratedFDeriv ℝ 1 (Dv d₁ (tr.v s)) z‖ :=
    h3.trans (mul_le_of_le_one_left (norm_nonneg _) hd₂)
  have h4' : ‖iteratedFDeriv ℝ 1 (Dv d₁ (tr.v s)) z‖ ≤
      ‖iteratedFDeriv ℝ 2 (tr.v s) z‖ :=
    h4.trans (mul_le_of_le_one_left (norm_nonneg _) hd₁)
  linarith

private theorem trainJetPt_le_ageJets {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s)
    (z : Plane) :
    trainJetPt tr s z ≤
      8 * (‖ageJet 0 0 tr.v s z‖ + ‖ageJet 0 1 tr.v s z‖ + ‖ageJet 0 2 tr.v s z‖) := by
  have hd10 : ‖((1 : ℝ), (0 : ℝ))‖ ≤ 1 := by simp [Prod.norm_def]
  have hd01 : ‖((0 : ℝ), (1 : ℝ))‖ ≤ 1 := by simp [Prod.norm_def]
  have hcomp : ∀ i : Fin 2,
      |tr.v s z i| +
        |trD1 tr (1, 0) s z i| + |trD1 tr (0, 1) s z i| +
        |trD2 tr (1, 0) (1, 0) s z i| + |trD2 tr (1, 0) (0, 1) s z i| +
        |trD2 tr (0, 1) (1, 0) s z i| + |trD2 tr (0, 1) (0, 1) s z i| ≤
        4 * (‖ageJet 0 0 tr.v s z‖ + ‖ageJet 0 1 tr.v s z‖ + ‖ageJet 0 2 tr.v s z‖) := by
    intro i
    have a0 := abs_tr_v_le_ageJet0 tr s z i
    have a10 := abs_trD1_le_ageJet1 tr hs hd10 z i
    have a01 := abs_trD1_le_ageJet1 tr hs hd01 z i
    have a1010 := abs_trD2_le_ageJet2 tr hs hd10 hd10 z i
    have a1001 := abs_trD2_le_ageJet2 tr hs hd10 hd01 z i
    have a0110 := abs_trD2_le_ageJet2 tr hs hd01 hd10 z i
    have a0101 := abs_trD2_le_ageJet2 tr hs hd01 hd01 z i
    linarith [norm_nonneg (ageJet 0 0 tr.v s z), norm_nonneg (ageJet 0 1 tr.v s z)]
  unfold trainJetPt
  rw [Fin.sum_univ_two]
  linarith [hcomp 0, hcomp 1]

/-! ### 3. Weight comparison on `B0579.cell c` and `L^{22/3}` integration of `(1 + η²)⁻¹` -/

private theorem jb_rpow_le_on_cell {c m : ℝ} (_hc : 0 ≤ c) (_hm : 0 ≤ m) (M : ℕ)
    (hM : m / 2 ≤ (M : ℝ)) {z : Plane} (hz : z ∈ B0579.cell c) :
    B0579.jb z ^ (m / 2) ≤
      (1 + c ^ 2) ^ M * Real.sqrt (jap (2 * (M + 1)) z) * (1 + z.2 ^ 2)⁻¹ := by
  have hjb1 : 1 ≤ B0579.jb z := by
    unfold B0579.jb
    nlinarith [sq_nonneg z.1, sq_nonneg z.2]
  have hrpow : B0579.jb z ^ (m / 2) ≤ B0579.jb z ^ M := by
    calc B0579.jb z ^ (m / 2)
        ≤ B0579.jb z ^ (M : ℝ) := Real.rpow_le_rpow_of_exponent_le hjb1 hM
      _ = B0579.jb z ^ M := Real.rpow_natCast _ M
  have hq : z.1 ^ 2 ≤ c ^ 2 := by
    have hz1 := hz.1
    nlinarith [hz1.1, hz1.2.le]
  have hjb_cell : B0579.jb z ≤ (1 + c ^ 2) * (1 + z.2 ^ 2) := by
    unfold B0579.jb
    nlinarith [sq_nonneg c, sq_nonneg z.2, mul_nonneg (sq_nonneg c) (sq_nonneg z.2)]
  have hpowM : B0579.jb z ^ M ≤ (1 + c ^ 2) ^ M * (1 + z.2 ^ 2) ^ M := by
    calc B0579.jb z ^ M
        ≤ ((1 + c ^ 2) * (1 + z.2 ^ 2)) ^ M :=
          pow_le_pow_left₀ (by linarith) hjb_cell M
      _ = (1 + c ^ 2) ^ M * (1 + z.2 ^ 2) ^ M := mul_pow _ _ _
  have hjap_eq : Real.sqrt (jap (2 * (M + 1)) z) = (1 + z.2 ^ 2) ^ (M + 1) := by
    have hsq : jap (2 * (M + 1)) z = ((1 + z.2 ^ 2) ^ (M + 1)) ^ 2 := by
      unfold jap
      rw [mul_comm 2 (M + 1), pow_mul]
    rw [hsq, Real.sqrt_sq (by positivity)]
  have h1z_ne : 1 + z.2 ^ 2 ≠ 0 := by positivity
  have hid : (1 + z.2 ^ 2) ^ M =
      Real.sqrt (jap (2 * (M + 1)) z) * (1 + z.2 ^ 2)⁻¹ := by
    rw [hjap_eq, pow_succ (1 + z.2 ^ 2) M, mul_inv_cancel_right₀ h1z_ne]
  calc B0579.jb z ^ (m / 2)
      ≤ B0579.jb z ^ M := hrpow
    _ ≤ (1 + c ^ 2) ^ M * (1 + z.2 ^ 2) ^ M := hpowM
    _ = (1 + c ^ 2) ^ M * Real.sqrt (jap (2 * (M + 1)) z) * (1 + z.2 ^ 2)⁻¹ := by
        rw [hid, mul_assoc]

private theorem eLpNorm_22_3_le_of_inv_one_add_sq {c A : ℝ} (hc : 0 < c) (hA : 0 ≤ A)
    (W : Plane → ℝ) (hW0 : ∀ z : Plane, 0 ≤ W z)
    (hW : ∀ z ∈ B0579.cell c, W z ≤ A * (1 + z.2 ^ 2)⁻¹) :
    eLpNorm W (ENNReal.ofReal (22 / 3)) (volume.restrict (B0579.cell c)) ≤
      ENNReal.ofReal ((c * Real.pi) ^ (3 / 22 : ℝ) * A) := by
  set μ := volume.restrict (B0579.cell c)
  have hμ_eq : μ = UnforcedLeray.Cyl.cellμ c := by
    dsimp [μ]
    rw [cell_eq_cylCell]
    rfl
  have hp0 : ENNReal.ofReal (22 / 3) ≠ 0 := by norm_num
  have hpt : ENNReal.ofReal (22 / 3) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt]
  have hto : (ENNReal.ofReal (22 / 3)).toReal = 22 / 3 :=
    ENNReal.toReal_ofReal (by norm_num)
  have hinv : 1 / (22 / 3 : ℝ) = 3 / 22 := by norm_num
  rw [hto, hinv]
  have h_ae : ∀ᵐ z ∂μ,
      ‖W z‖ₑ ^ (22 / 3 : ℝ) ≤
        ENNReal.ofReal (A ^ (22 / 3 : ℝ) * (1 + z.2 ^ 2)⁻¹) := by
    have hmem : ∀ᵐ z ∂μ, z ∈ B0579.cell c :=
      ae_restrict_mem (by
        rw [cell_eq_cylCell]
        exact measurableSet_Ico.prod MeasurableSet.univ)
    filter_upwards [hmem] with z hz
    have hWz := hW z hz
    have hinv_le1 : (1 + z.2 ^ 2)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg z.2])
    have hx1 : ENNReal.ofReal ((1 + z.2 ^ 2)⁻¹) ≤ 1 :=
      ENNReal.ofReal_le_one.2 hinv_le1
    have hx_pow : ENNReal.ofReal ((1 + z.2 ^ 2)⁻¹) ^ (22 / 3 : ℝ) ≤
        ENNReal.ofReal ((1 + z.2 ^ 2)⁻¹) := by
      have hadd : (22 / 3 : ℝ) = 1 + 19 / 3 := by norm_num
      calc ENNReal.ofReal ((1 + z.2 ^ 2)⁻¹) ^ (22 / 3 : ℝ)
          = ENNReal.ofReal ((1 + z.2 ^ 2)⁻¹) ^ (1 : ℝ) *
              ENNReal.ofReal ((1 + z.2 ^ 2)⁻¹) ^ (19 / 3 : ℝ) := by
            rw [hadd, ENNReal.rpow_add_of_nonneg _ _ zero_le_one (by norm_num)]
        _ ≤ ENNReal.ofReal ((1 + z.2 ^ 2)⁻¹) ^ (1 : ℝ) * 1 :=
            mul_le_mul_right (ENNReal.rpow_le_one hx1 (by norm_num)) _
        _ = ENNReal.ofReal ((1 + z.2 ^ 2)⁻¹) := by rw [ENNReal.rpow_one, mul_one]
    calc ‖W z‖ₑ ^ (22 / 3 : ℝ)
        = ENNReal.ofReal (W z) ^ (22 / 3 : ℝ) := by
          rw [Real.enorm_eq_ofReal (hW0 z)]
      _ ≤ ENNReal.ofReal (A * (1 + z.2 ^ 2)⁻¹) ^ (22 / 3 : ℝ) :=
          ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hWz) (by norm_num)
      _ = ENNReal.ofReal A ^ (22 / 3 : ℝ) *
            ENNReal.ofReal ((1 + z.2 ^ 2)⁻¹) ^ (22 / 3 : ℝ) := by
          rw [ENNReal.ofReal_mul hA, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      _ ≤ ENNReal.ofReal A ^ (22 / 3 : ℝ) * ENNReal.ofReal ((1 + z.2 ^ 2)⁻¹) :=
          mul_le_mul_right hx_pow _
      _ = ENNReal.ofReal (A ^ (22 / 3 : ℝ) * (1 + z.2 ^ 2)⁻¹) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hA (by norm_num),
            ← ENNReal.ofReal_mul (Real.rpow_nonneg hA _)]
  have hmeas : AEMeasurable
      (fun z : Plane => ENNReal.ofReal (A ^ (22 / 3 : ℝ) * (1 + z.2 ^ 2)⁻¹))
      (UnforcedLeray.Cyl.cellμ c) := by
    have hm : Measurable
        (fun z : Plane => ENNReal.ofReal (A ^ (22 / 3 : ℝ) * (1 + z.2 ^ 2)⁻¹)) := by
      fun_prop
    exact hm.aemeasurable
  have hint_le : ∫⁻ z, ‖W z‖ₑ ^ (22 / 3 : ℝ) ∂μ ≤
      ENNReal.ofReal (c * (A ^ (22 / 3 : ℝ) * Real.pi)) := by
    calc ∫⁻ z, ‖W z‖ₑ ^ (22 / 3 : ℝ) ∂μ
        ≤ ∫⁻ z, ENNReal.ofReal (A ^ (22 / 3 : ℝ) * (1 + z.2 ^ 2)⁻¹) ∂μ :=
          lintegral_mono_ae h_ae
      _ = ∫⁻ z, ENNReal.ofReal (A ^ (22 / 3 : ℝ) * (1 + z.2 ^ 2)⁻¹)
            ∂(UnforcedLeray.Cyl.cellμ c) := by rw [hμ_eq]
      _ = ∫⁻ q in Ico (-c / 2) (c / 2),
            ∫⁻ η : ℝ, ENNReal.ofReal (A ^ (22 / 3 : ℝ) * (1 + η ^ 2)⁻¹) :=
          UnforcedLeray.Cyl.lintegral_cell_eq hmeas
      _ = ENNReal.ofReal (c * (A ^ (22 / 3 : ℝ) * Real.pi)) := by
          have hint : ∫⁻ η : ℝ, ENNReal.ofReal (A ^ (22 / 3 : ℝ) * (1 + η ^ 2)⁻¹) =
              ENNReal.ofReal (A ^ (22 / 3 : ℝ) * Real.pi) := by
            rw [← ofReal_integral_eq_lintegral_ofReal
              (integrable_inv_one_add_sq.const_mul (A ^ (22 / 3 : ℝ)))
              (ae_of_all _ fun η => by positivity)]
            rw [integral_const_mul, integral_univ_inv_one_add_sq]
          simp_rw [hint]
          rw [setLIntegral_const, Real.volume_Ico]
          have hlen : c / 2 - -c / 2 = c := by ring
          rw [hlen, mul_comm, ← ENNReal.ofReal_mul hc.le]
  refine (ENNReal.rpow_le_rpow hint_le (by norm_num)).trans ?_
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  have h1 : c * (A ^ (22 / 3 : ℝ) * Real.pi) = (c * Real.pi) * A ^ (22 / 3 : ℝ) := by ring
  rw [h1, Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul hA, show (22 / 3 : ℝ) * (3 / 22 : ℝ) = 1 by norm_num, Real.rpow_one]

/-! ### 4. Polynomial bound on `(1 + c + ν⁻¹) * (1 + s)` and `1 + c²` in `BgRegime` -/

private theorem polyPS_le_on_band {C Sig ν c s : ℝ} (hC : 0 ≤ C) (_hSig : 0 < Sig)
    (hν : 0 < ν) (hν1 : ν ≤ 1) (hc_eq : c = (ν ^ 2)⁻¹) (_hs0 : 0 ≤ s) (hs : s ≤ Sig / ν)
    (N : ℕ) :
    polyPS C N ν c s ≤ C * (3 * (1 + Sig)) ^ N * (ν ^ (3 * N))⁻¹ := by
  have hν_inv1 : 1 ≤ ν⁻¹ := one_le_inv₀ hν |>.2 hν1
  have hc_inv : c = (ν⁻¹) ^ 2 := by rw [hc_eq, inv_pow]
  have h1 : 1 + c + ν⁻¹ ≤ 3 * (ν⁻¹) ^ 2 := by
    rw [hc_inv]
    nlinarith
  have hs_le : s ≤ Sig * ν⁻¹ := by rwa [div_eq_mul_inv] at hs
  have h2 : 1 + s ≤ (1 + Sig) * ν⁻¹ := by
    nlinarith
  have hX : (1 + c + ν⁻¹) * (1 + s) ≤ (3 * (1 + Sig)) * (ν⁻¹) ^ 3 := by
    calc (1 + c + ν⁻¹) * (1 + s)
        ≤ (3 * (ν⁻¹) ^ 2) * ((1 + Sig) * ν⁻¹) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = (3 * (1 + Sig)) * (ν⁻¹) ^ 3 := by ring
  have hpow : ((1 + c + ν⁻¹) * (1 + s)) ^ N ≤
      (3 * (1 + Sig)) ^ N * (ν ^ (3 * N))⁻¹ := by
    have hX0 : 0 ≤ (1 + c + ν⁻¹) * (1 + s) := by
      rw [hc_inv]; positivity
    calc ((1 + c + ν⁻¹) * (1 + s)) ^ N
        ≤ ((3 * (1 + Sig)) * (ν⁻¹) ^ 3) ^ N := pow_le_pow_left₀ hX0 hX N
      _ = (3 * (1 + Sig)) ^ N * ((ν⁻¹) ^ 3) ^ N := mul_pow _ _ _
      _ = (3 * (1 + Sig)) ^ N * (ν ^ (3 * N))⁻¹ := by
          rw [← pow_mul, inv_pow]
  unfold polyPS
  calc C * ((1 + c + ν⁻¹) * (1 + s)) ^ N
      ≤ C * ((3 * (1 + Sig)) ^ N * (ν ^ (3 * N))⁻¹) :=
        mul_le_mul_of_nonneg_left hpow hC
    _ = C * (3 * (1 + Sig)) ^ N * (ν ^ (3 * N))⁻¹ := by ring

private theorem one_add_c_sq_pow_le {ν c : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hc_eq : c = (ν ^ 2)⁻¹) (M : ℕ) :
    (1 + c ^ 2) ^ M ≤ 2 ^ M * (ν ^ (4 * M))⁻¹ := by
  have hν_inv1 : 1 ≤ ν⁻¹ := one_le_inv₀ hν |>.2 hν1
  have hc2 : c ^ 2 = (ν⁻¹) ^ 4 := by
    rw [hc_eq, inv_pow]
    ring
  have h1 : 1 + c ^ 2 ≤ 2 * (ν⁻¹) ^ 4 := by
    rw [hc2]
    have : 1 ≤ (ν⁻¹) ^ 4 := one_le_pow₀ hν_inv1
    linarith
  calc (1 + c ^ 2) ^ M
      ≤ (2 * (ν⁻¹) ^ 4) ^ M := pow_le_pow_left₀ (by positivity) h1 M
    _ = 2 ^ M * ((ν⁻¹) ^ 4) ^ M := mul_pow _ _ _
    _ = 2 ^ M * (ν ^ (4 * M))⁻¹ := by rw [← pow_mul, inv_pow]

private theorem cell_factor_le {ν c : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hc_eq : c = (ν ^ 2)⁻¹) :
    (c * Real.pi) ^ (3 / 22 : ℝ) * c ^ (4 / 11 : ℝ) ≤ 4 * (ν ^ 4)⁻¹ := by
  have hν_inv1 : 1 ≤ ν⁻¹ := one_le_inv₀ hν |>.2 hν1
  have hc1 : 1 ≤ c := by
    rw [hc_eq, ← inv_pow]
    exact one_le_pow₀ hν_inv1
  have h4c1 : 1 ≤ 4 * c := by linarith
  have hpi : c * Real.pi ≤ 4 * c := by
    nlinarith [Real.pi_le_four]
  have hf1 : (c * Real.pi) ^ (3 / 22 : ℝ) ≤ 4 * c := by
    calc (c * Real.pi) ^ (3 / 22 : ℝ)
        ≤ (4 * c) ^ (3 / 22 : ℝ) := Real.rpow_le_rpow (by positivity) hpi (by norm_num)
      _ ≤ (4 * c) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h4c1 (by norm_num)
      _ = 4 * c := Real.rpow_one _
  have hf2 : c ^ (4 / 11 : ℝ) ≤ c := by
    calc c ^ (4 / 11 : ℝ)
        ≤ c ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
      _ = c := Real.rpow_one _
  have hc2 : c * c = (ν ^ 4)⁻¹ := by
    rw [hc_eq, ← mul_inv, ← pow_add]
  calc (c * Real.pi) ^ (3 / 22 : ℝ) * c ^ (4 / 11 : ℝ)
      ≤ (4 * c) * c := mul_le_mul hf1 hf2 (by positivity) (by positivity)
    _ = 4 * (c * c) := by ring
    _ = 4 * (ν ^ 4)⁻¹ := by rw [hc2]

end TrainLp22over3Aux

open TrainLp22over3Aux

/-- **Proof of `TrainWeightedLp22over3` (`PartII-b:F5/2/1`)**. -/
theorem trainWeightedLp22over3_proof : UnforcedLeray.Short.IIb.TrainWeightedLp22over3 := by
  intro m hm Sig hSig dm dp _hdm
  set M : ℕ := Nat.ceil (m / 2)
  have hm0 : 0 ≤ m := by linarith
  have hM : m / 2 ≤ (M : ℝ) := Nat.le_ceil (m / 2)
  have hρ : (1 / 2 : ℝ) < 2 := by norm_num
  obtain ⟨C₀, N₀, ν₀, hC₀, hν₀, hT₀⟩ :=
    trainStreamVelocityPressureTails_uncond.2.2 2 hρ (2 * (M + 1)) 0 0
  obtain ⟨C₁, N₁, ν₁, hC₁, hν₁, hT₁⟩ :=
    trainStreamVelocityPressureTails_uncond.2.2 2 hρ (2 * (M + 1)) 0 1
  obtain ⟨C₂, N₂, ν₂, hC₂, hν₂, hT₂⟩ :=
    trainStreamVelocityPressureTails_uncond.2.2 2 hρ (2 * (M + 1)) 0 2
  set ν_bar : ℝ := min (min (min ν₀ ν₁) ν₂) 1
  have hν_bar_pos : 0 < ν_bar :=
    lt_min (lt_min (lt_min hν₀ hν₁) hν₂) one_pos
  set K₀ : ℝ := C₀ * (3 * (1 + Sig)) ^ N₀
  set K₁ : ℝ := C₁ * (3 * (1 + Sig)) ^ N₁
  set K₂ : ℝ := C₂ * (3 * (1 + Sig)) ^ N₂
  set C_tr : ℝ := 32 * 2 ^ M * (K₀ + K₁ + K₂)
  set k_tr : ℕ := 4 + 4 * M + (3 * N₀ + 3 * N₁ + 3 * N₂)
  have hCtr_pos : 0 < C_tr := by dsimp [C_tr, K₀, K₁, K₂]; positivity
  refine ⟨C_tr, k_tr, ν_bar, hCtr_pos, hν_bar_pos, ?_⟩
  intro p d hreg hν_le s hs
  have hνp : 0 < p.ν := p.ν_pos
  have hν1 : p.ν ≤ 1 := hν_le.trans (min_le_right _ _)
  have hν₀_le : p.ν ≤ ν₀ :=
    hν_le.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hν₁_le : p.ν ≤ ν₁ :=
    hν_le.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hν₂_le : p.ν ≤ ν₂ :=
    hν_le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hs0 : 0 < s := hs.1
  have hs_le : s ≤ Sig / p.ν := hs.2
  have hc_eq : p.c = (p.ν ^ 2)⁻¹ := hreg.c_eq
  have hcp : 0 < p.c := by rw [hc_eq]; positivity
  have hc2 : trainPeriod 2 p.ν = (p.ν ^ 2)⁻¹ := vb_trainPeriod_two hνp
  obtain ⟨tr', hbuc, hv_eq⟩ :=
    vb_transport (hc_eq.trans hc2.symm) p.train hreg.train_buc
  set K_sum : ℝ := (K₀ + K₁ + K₂) * (p.ν ^ (3 * N₀ + 3 * N₁ + 3 * N₂))⁻¹
  have h_jap_jet : ∀ z : Plane,
      Real.sqrt (jap (2 * (M + 1)) z) * trainJetPt p.train s z ≤ 8 * K_sum := by
    intro z
    have h_each : ∀ (j : ℕ) (C_j : ℝ) (N_j : ℕ) (hC_j : 0 < C_j)
        (h_w : wSupNorm (2 * (M + 1)) (ageJet 0 j tr'.v s) ≤
          ENNReal.ofReal (polyPS C_j N_j p.ν (trainPeriod 2 p.ν) s)),
        Real.sqrt (jap (2 * (M + 1)) z) * ‖ageJet 0 j p.train.v s z‖ ≤
          C_j * (3 * (1 + Sig)) ^ N_j * (p.ν ^ (3 * N_j))⁻¹ := by
      intro j C_j N_j hC_j h_w
      have hpoly_nn : 0 ≤ polyPS C_j N_j p.ν (trainPeriod 2 p.ν) s := by
        unfold polyPS
        rw [hc2]
        positivity
      have hpt := sqrt_jap_mul_norm_le_of_wSupNorm_le (2 * (M + 1)) hpoly_nn h_w z
      rw [hv_eq] at hpt
      exact hpt.trans (polyPS_le_on_band hC_j.le hSig hνp hν1 hc2 hs0.le hs_le N_j)
    have hj0 := h_each 0 C₀ N₀ hC₀ ((hT₀ p.ν hνp hν₀_le tr' hbuc s hs0).2.2.1.2)
    have hj1 := h_each 1 C₁ N₁ hC₁ ((hT₁ p.ν hνp hν₁_le tr' hbuc s hs0).2.2.1.2)
    have hj2 := h_each 2 C₂ N₂ hC₂ ((hT₂ p.ν hνp hν₂_le tr' hbuc s hs0).2.2.1.2)
    have hm0' : (p.ν ^ (3 * N₀))⁻¹ ≤ (p.ν ^ (3 * N₀ + 3 * N₁ + 3 * N₂))⁻¹ :=
      vb_inv_pow_mono hνp hν1 (by omega)
    have hm1' : (p.ν ^ (3 * N₁))⁻¹ ≤ (p.ν ^ (3 * N₀ + 3 * N₁ + 3 * N₂))⁻¹ :=
      vb_inv_pow_mono hνp hν1 (by omega)
    have hm2' : (p.ν ^ (3 * N₂))⁻¹ ≤ (p.ν ^ (3 * N₀ + 3 * N₁ + 3 * N₂))⁻¹ :=
      vb_inv_pow_mono hνp hν1 (by omega)
    have hj0' : Real.sqrt (jap (2 * (M + 1)) z) * ‖ageJet 0 0 p.train.v s z‖ ≤
        K₀ * (p.ν ^ (3 * N₀ + 3 * N₁ + 3 * N₂))⁻¹ :=
      hj0.trans (mul_le_mul_of_nonneg_left hm0' (by positivity))
    have hj1' : Real.sqrt (jap (2 * (M + 1)) z) * ‖ageJet 0 1 p.train.v s z‖ ≤
        K₁ * (p.ν ^ (3 * N₀ + 3 * N₁ + 3 * N₂))⁻¹ :=
      hj1.trans (mul_le_mul_of_nonneg_left hm1' (by positivity))
    have hj2' : Real.sqrt (jap (2 * (M + 1)) z) * ‖ageJet 0 2 p.train.v s z‖ ≤
        K₂ * (p.ν ^ (3 * N₀ + 3 * N₁ + 3 * N₂))⁻¹ :=
      hj2.trans (mul_le_mul_of_nonneg_left hm2' (by positivity))
    have hjet := mul_le_mul_of_nonneg_left (trainJetPt_le_ageJets p.train hs0.le z)
      (Real.sqrt_nonneg (jap (2 * (M + 1)) z))
    dsimp [K_sum]
    linarith
  set A : ℝ := 8 * 2 ^ M * (K₀ + K₁ + K₂) *
    (p.ν ^ (4 * M + (3 * N₀ + 3 * N₁ + 3 * N₂)))⁻¹
  have hA_nn : 0 ≤ A := by positivity
  set W : Plane → ℝ := fun z => B0579.jb z ^ (m / 2) * trainJetPt p.train s z
  have hW0 : ∀ z : Plane, 0 ≤ W z := fun z =>
    mul_nonneg (Real.rpow_nonneg (B0579.jb_pos z).le _) (trainJetPt_nonneg p.train s z)
  have hW_cell : ∀ z ∈ B0579.cell p.c, W z ≤ A * (1 + z.2 ^ 2)⁻¹ := by
    intro z hz
    have hjb := jb_rpow_le_on_cell hcp.le hm0 M hM hz
    have h1 := mul_le_mul_of_nonneg_right hjb (trainJetPt_nonneg p.train s z)
    have h2 : (1 + p.c ^ 2) ^ M * Real.sqrt (jap (2 * (M + 1)) z) * (1 + z.2 ^ 2)⁻¹ *
          trainJetPt p.train s z =
        (1 + p.c ^ 2) ^ M * (Real.sqrt (jap (2 * (M + 1)) z) * trainJetPt p.train s z) *
          (1 + z.2 ^ 2)⁻¹ := by ring
    have h3 : (1 + p.c ^ 2) ^ M * (Real.sqrt (jap (2 * (M + 1)) z) * trainJetPt p.train s z) ≤
        A := by
      calc (1 + p.c ^ 2) ^ M * (Real.sqrt (jap (2 * (M + 1)) z) * trainJetPt p.train s z)
          ≤ (2 ^ M * (p.ν ^ (4 * M))⁻¹) * (8 * K_sum) :=
            mul_le_mul (one_add_c_sq_pow_le hνp hν1 hc_eq M) (h_jap_jet z)
              (mul_nonneg (Real.sqrt_nonneg _) (trainJetPt_nonneg p.train s z)) (by positivity)
        _ = A := by
            dsimp [A, K_sum]
            rw [pow_add, mul_inv]
            ring
    calc W z
        ≤ (1 + p.c ^ 2) ^ M * Real.sqrt (jap (2 * (M + 1)) z) * (1 + z.2 ^ 2)⁻¹ *
            trainJetPt p.train s z := h1
      _ = (1 + p.c ^ 2) ^ M * (Real.sqrt (jap (2 * (M + 1)) z) * trainJetPt p.train s z) *
            (1 + z.2 ^ 2)⁻¹ := h2
      _ ≤ A * (1 + z.2 ^ 2)⁻¹ := mul_le_mul_of_nonneg_right h3 (by positivity)
  have h_lp := eLpNorm_22_3_le_of_inv_one_add_sq hcp hA_nn W hW0 hW_cell
  have h_cf := cell_factor_le hνp hν1 hc_eq
  unfold trainSliceNorm22_3
  calc eLpNorm W (ENNReal.ofReal (22 / 3)) (volume.restrict (B0579.cell p.c)) *
        ENNReal.ofReal (p.c ^ (4 / 11 : ℝ))
      ≤ ENNReal.ofReal ((p.c * Real.pi) ^ (3 / 22 : ℝ) * A) *
          ENNReal.ofReal (p.c ^ (4 / 11 : ℝ)) := by gcongr
    _ = ENNReal.ofReal (((p.c * Real.pi) ^ (3 / 22 : ℝ) * p.c ^ (4 / 11 : ℝ)) * A) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        ring_nf
    _ ≤ ENNReal.ofReal ((4 * (p.ν ^ 4)⁻¹) * A) := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_right h_cf hA_nn
    _ = ENNReal.ofReal (C_tr * (p.ν ^ k_tr)⁻¹) := by
        congr 1
        dsimp [C_tr, k_tr, A]
        rw [pow_add, mul_inv]
        ring

end UnforcedLeray.Short.IIb
