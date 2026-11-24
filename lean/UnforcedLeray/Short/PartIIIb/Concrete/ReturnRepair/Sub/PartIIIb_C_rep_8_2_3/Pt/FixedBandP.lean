import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.PtOrg
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.FixedBandJets

/-!
# `PartIII-b:C/rep/8/2/3/2/9`: the pressure-difference band `FixedBandP`

Source of record: `the November 2 reference manuscript` 468-478 (the component
`nabla(p - p_c^p)` of `d` in Part I `sct:fixed-band`, `TrainFixedBand`). The proof is the
`fixedBandJets_of` template with `dv` replaced by `dp = gradS (p - p_c)`; the train is transported
from period `cOf nu` to `trainPeriod 2 nu` (equal by `cOf nu = (nu^2)^{-1}`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cyl (Plane)

/-- Transport of a BUC train along an equality of periods (only the pressure is kept). -/
theorem fbp_transport {ν c c' : ℝ} (h : c = c')
    (tr : UnforcedLeray.B0140.TrainSol ν c)
    (hb : UnforcedLeray.Short.PartI.IsBUCTrain tr) :
    ∃ tr' : UnforcedLeray.B0140.TrainSol ν c',
      UnforcedLeray.Short.PartI.IsBUCTrain tr' ∧ tr'.p = tr.p := by
  subst h
  exact ⟨tr, hb, rfl⟩

/-- **Pressure difference jets** (source 468-478, `sct:fixed-band`, the `nabla(p - p_c^p)` part). -/
theorem fixedBandP_of (hF : UnforcedLeray.Short.PartI.TrainFixedBand) : FixedBandP := by
  intro ℓ m
  obtain ⟨C, N, CS, bS, ν₀, hC, hbS, hν₀, H⟩ := hF 2 (by norm_num) 1 one_pos 0 ℓ m
  refine ⟨C * 3 ^ N, 2 * N, min ν₀ (min 1 (bS / (|CS| + 1))),
    lt_min hν₀ (lt_min one_pos (by positivity)), ?_⟩
  intro ν hν hνle tr htr s hs hsS z
  have hν0 : ν ≤ ν₀ := hνle.trans (min_le_left _ _)
  have hν1 : ν ≤ 1 := hνle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hνb : ν ≤ bS / (|CS| + 1) := hνle.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hcdef : UnforcedLeray.Short.PartI.trainPeriod 2 ν = (ν ^ 2)⁻¹ := by
    unfold UnforcedLeray.Short.PartI.trainPeriod
    rw [Real.rpow_neg hν.le, Real.rpow_two]
  have hc : cOf ν = UnforcedLeray.Short.PartI.trainPeriod 2 ν := by
    unfold cOf
    rw [hcdef]
  obtain ⟨tr', htr', hp⟩ := fbp_transport hc tr htr
  have hpc : UnforcedLeray.Train.pc ν (cOf ν) = UnforcedLeray.Train.pc ν
      (UnforcedLeray.Short.PartI.trainPeriod 2 ν) := by rw [hc]
  rw [hpc, ← hp]
  have h1 := H ν hν hν0 tr' htr' s hs hsS
  simp only at h1
  -- exponential factor
  have hexp : CS / ν - bS * (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2 ≤ 0 := by
    rw [hcdef, inv_pow, sub_nonpos]
    have hA : 0 < |CS| + 1 := by positivity
    have h3 : ν ^ 3 ≤ ν := by
      have : ν ^ 3 = ν * ν ^ 2 := by ring
      rw [this]
      nlinarith [pow_pos hν 2, mul_pos hν hν]
    have : CS * ν ^ 3 ≤ bS := by
      have h4 : |CS| * ν ≤ bS := by
        have := mul_le_mul_of_nonneg_left hνb (abs_nonneg CS)
        have h5 : |CS| * (bS / (|CS| + 1)) ≤ bS := by
          rw [mul_div_assoc', div_le_iff₀ hA]; nlinarith [abs_nonneg CS]
        linarith
      calc CS * ν ^ 3 ≤ |CS| * ν ^ 3 := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        _ ≤ |CS| * ν := mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
        _ ≤ bS := h4
    rw [div_le_iff₀ hν]
    have hν4 : 0 < (ν ^ 2) ^ 2 := by positivity
    have : bS * ((ν ^ 2) ^ 2)⁻¹ * ν = bS / ν ^ 3 := by
      field_simp
    rw [this, le_div_iff₀ (by positivity)]
    linarith
  have hexp1 : Real.exp (CS / ν - bS * (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.2 hexp
  have hP : 0 ≤ UnforcedLeray.Short.PartI.polyP C N ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) := by
    unfold UnforcedLeray.Short.PartI.polyP; rw [hcdef]; have : 0 < ν := hν; positivity
  have hsup : UnforcedLeray.Short.PartI.wSupNorm 0 (UnforcedLeray.Short.PartI.sigmaJet ν ℓ m
      (fun r w => UnforcedLeray.Train.gradS
        (fun w' => tr'.p r w' - UnforcedLeray.Train.pc ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) r w') w) s)
      ≤ ENNReal.ofReal (UnforcedLeray.Short.PartI.polyP C N ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν)) := by
    have hl : UnforcedLeray.Short.PartI.wSupNorm 0 (UnforcedLeray.Short.PartI.sigmaJet ν ℓ m
        (fun r w => UnforcedLeray.Train.gradS
          (fun w' => tr'.p r w' - UnforcedLeray.Train.pc ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) r w') w) s)
        ≤ ENNReal.ofReal (UnforcedLeray.Short.PartI.polyP C N ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
          Real.exp (CS / ν - bS * (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2)) := by
      refine le_trans ?_ h1
      refine le_trans ?_ (Finset.single_le_sum (fun _ _ => bot_le)
        (Finset.mem_range.2 (Nat.lt_succ_self ℓ)))
      refine le_trans ?_ (Finset.single_le_sum (fun _ _ => bot_le)
        (Finset.mem_range.2 (Nat.lt_succ_self m)))
      exact le_add_self
    exact hl.trans (ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right hP hexp1))
  have hpt := UnforcedLeray.Short.PartIIa.pointwise_of_wSupNorm hP hsup z
  have hjap : UnforcedLeray.Train.jap 0 z = 1 := by simp [UnforcedLeray.Train.jap]
  rw [hjap] at hpt
  simp only [Real.sqrt_one, one_mul] at hpt
  rw [UnforcedLeray.Short.IIb.ageJet_eq_smul_sigmaJet hν, norm_smul, norm_pow, Real.norm_eq_abs,
    abs_of_pos hν]
  have hνl : ν ^ ℓ ≤ 1 := pow_le_one₀ hν.le hν1
  have hinv : (1 : ℝ) ≤ (ν ^ 2)⁻¹ := (one_le_inv₀ (by positivity)).2 (pow_le_one₀ hν.le hν1)
  have hinv1 : ν⁻¹ ≤ (ν ^ 2)⁻¹ := by
    exact inv_anti₀ (by positivity) (by nlinarith)
  have hbase : 1 + UnforcedLeray.Short.PartI.trainPeriod 2 ν + ν⁻¹ ≤ 3 * ν⁻¹ ^ 2 := by
    rw [hcdef, inv_pow]; linarith
  have hb0 : 0 ≤ 1 + UnforcedLeray.Short.PartI.trainPeriod 2 ν + ν⁻¹ := by
    rw [hcdef]; have : 0 < ν := hν; positivity
  have hpoly : UnforcedLeray.Short.PartI.polyP C N ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ≤
      C * 3 ^ N * ν⁻¹ ^ (2 * N) := by
    unfold UnforcedLeray.Short.PartI.polyP
    calc C * (1 + UnforcedLeray.Short.PartI.trainPeriod 2 ν + ν⁻¹) ^ N
        ≤ C * (3 * ν⁻¹ ^ 2) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb0 hbase N) hC.le
      _ = C * 3 ^ N * ν⁻¹ ^ (2 * N) := by
          rw [mul_pow, ← pow_mul]; ring
  have hn := norm_nonneg (UnforcedLeray.Short.PartI.sigmaJet ν ℓ m
      (fun r w => UnforcedLeray.Train.gradS
        (fun w' => tr'.p r w' - UnforcedLeray.Train.pc ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) r w') w) s z)
  have hνl' : ν ^ ℓ ≤ 1 := hνl
  calc ν ^ ℓ * ‖UnforcedLeray.Short.PartI.sigmaJet ν ℓ m
        (fun r w => UnforcedLeray.Train.gradS
          (fun w' => tr'.p r w' - UnforcedLeray.Train.pc ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) r w') w) s z‖
      ≤ 1 * UnforcedLeray.Short.PartI.polyP C N ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) :=
        mul_le_mul hνl' hpt hn zero_le_one
    _ ≤ _ := by rw [one_mul]; exact hpoly

end UnforcedLeray.Short.PartIIIb.Concrete
