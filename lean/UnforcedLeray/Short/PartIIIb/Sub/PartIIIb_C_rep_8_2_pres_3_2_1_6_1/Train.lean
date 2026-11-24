import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_1_6_1.Core
import UnforcedLeray.Short.PartI.Tasks.TrainHeatFixed.JointFromAgeJets
import UnforcedLeray.Short.PartI.StatementsTrain

/-!
# The train pressure and its first derivative decay exponentially in the age

Source `the November 2 reference manuscript`
lines 439-446 (`sct:fluctuation`: `‖⟨η⟩^m ∂_s^ℓ D^j p(s)‖_∞ ≤ P e^{-κνs/c²}` at every age `s > 0`,
the pressure `p` itself), 427-435 (joint derivative from the mixed age jets: `JointFromAgeJets`).
With `ρ = 2` (`c = (ν²)⁻¹`), `m = 4`, `(ℓ, j) ∈ {(0,0), (0,1), (1,0)}`: for fixed `ν ≤ ν₀`,
`(1+|η|)^4 (|p| + ‖Dp‖) ≤ A e^{-a s}` for all `s > 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (jap)

theorem lpt_trainPeriod_two {ν : ℝ} (hν : 0 < ν) :
    UnforcedLeray.Short.PartI.trainPeriod 2 ν = (ν ^ 2)⁻¹ := by
  unfold UnforcedLeray.Short.PartI.trainPeriod
  rw [Real.rpow_neg hν.le, Real.rpow_two]

theorem lpt_pointwise_of_wSup {E : Type*} [NormedAddCommGroup E] {m : ℕ} {f : Plane → E} {K : ℝ} (hK : 0 ≤ K)
    (h : UnforcedLeray.Short.PartI.wSupNorm m f ≤ ENNReal.ofReal K) (z : Plane) :
    Real.sqrt (jap m z) * ‖f z‖ ≤ K := by
  have h1 := (le_iSup
    (fun z : Plane => ENNReal.ofReal (Real.sqrt (jap m z)) * ‖f z‖ₑ) z).trans h
  rw [← ofReal_norm, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at h1
  exact (ENNReal.ofReal_le_ofReal_iff hK).1 h1

theorem lpt_weight_le (z : Plane) : (1 + |z.2|) ^ 4 ≤ 4 * Real.sqrt (jap 4 z) := by
  have h : Real.sqrt (jap 4 z) = (1 + z.2 ^ 2) ^ 2 := by
    unfold jap
    rw [show (1 + z.2 ^ 2) ^ 4 = ((1 + z.2 ^ 2) ^ 2) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  rw [h]
  have h1 : (1 + |z.2|) ^ 2 ≤ 2 * (1 + z.2 ^ 2) := by
    nlinarith [sq_abs z.2, sq_nonneg (1 - |z.2|)]
  calc (1 + |z.2|) ^ 4 = ((1 + |z.2|) ^ 2) ^ 2 := by ring
    _ ≤ (2 * (1 + z.2 ^ 2)) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    _ = 4 * (1 + z.2 ^ 2) ^ 2 := by ring

theorem lpt_norm_ageJet_zero (F : ℝ → Plane → ℝ) (t : ℝ) (z : Plane) :
    ‖UnforcedLeray.Short.PartI.ageJet 0 0 F t z‖ = ‖F t z‖ := by
  simp [UnforcedLeray.Short.PartI.ageJet, UnforcedLeray.Train.jet, iteratedDeriv_zero,
    norm_iteratedFDeriv_zero]

/-- One jet `(ℓ, j)` of the pressure with weight `m = 4`, at `ρ = 2`. -/
theorem lpt_jet_bound (hF : UnforcedLeray.Short.PartI.TrainFluctuationDecay) (ℓ j : ℕ) :
    ∃ (C : ℝ) (N : ℕ) (κ ν₀ : ℝ), 0 < C ∧ 0 < κ ∧ 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
      ∀ tr : UnforcedLeray.B0140.TrainSol ν (cOf ν), UnforcedLeray.Short.PartI.IsBUCTrain tr →
        ∀ s : ℝ, 0 < s → ∀ z : Plane,
          (1 + |z.2|) ^ 4 * ‖UnforcedLeray.Short.PartI.ageJet ℓ j tr.p s z‖ ≤
            4 * (UnforcedLeray.Short.PartI.polyP C N ν (cOf ν) *
              Real.exp (-((κ * ν ^ 5) * s))) := by
  obtain ⟨C, N, κ, ν₀, hC, hκ, hν₀, h⟩ := hF 2 (by norm_num) 4 ℓ j
  refine ⟨C, N, κ, ν₀, hC, hκ, hν₀, ?_⟩
  intro ν hν hνa tr hbuc s hs z
  have hh := h ν hν hνa
  rw [lpt_trainPeriod_two hν] at hh
  have hK := (hh tr hbuc s hs).2.2.2
  have hP0 : 0 ≤ UnforcedLeray.Short.PartI.polyP C N ν (ν ^ 2)⁻¹ := by
    unfold UnforcedLeray.Short.PartI.polyP
    have : 0 ≤ 1 + (ν ^ 2)⁻¹ + ν⁻¹ := by positivity
    exact mul_nonneg hC.le (pow_nonneg this N)
  have hK0 : 0 ≤ UnforcedLeray.Short.PartI.polyP C N ν (ν ^ 2)⁻¹ *
      Real.exp (-(κ * ν * s / ((ν ^ 2)⁻¹) ^ 2)) := mul_nonneg hP0 (Real.exp_pos _).le
  have hpt := lpt_pointwise_of_wSup hK0 hK z
  have hexp : κ * ν * s / ((ν ^ 2)⁻¹) ^ 2 = (κ * ν ^ 5) * s := by field_simp
  rw [hexp] at hpt
  rw [show UnforcedLeray.Short.PartI.polyP C N ν (cOf ν) =
    UnforcedLeray.Short.PartI.polyP C N ν (ν ^ 2)⁻¹ from rfl]
  calc (1 + |z.2|) ^ 4 * ‖UnforcedLeray.Short.PartI.ageJet ℓ j tr.p s z‖
      ≤ (4 * Real.sqrt (jap 4 z)) * ‖UnforcedLeray.Short.PartI.ageJet ℓ j tr.p s z‖ :=
        mul_le_mul_of_nonneg_right (lpt_weight_le z) (norm_nonneg _)
    _ = 4 * (Real.sqrt (jap 4 z) * ‖UnforcedLeray.Short.PartI.ageJet ℓ j tr.p s z‖) := by ring
    _ ≤ 4 * (UnforcedLeray.Short.PartI.polyP C N ν (ν ^ 2)⁻¹ *
          Real.exp (-((κ * ν ^ 5) * s))) := by gcongr

/-- **The train pressure and its derivative decay exponentially in the age.** -/
theorem lpt_train_bounds (hF : UnforcedLeray.Short.PartI.TrainFluctuationDecay) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
      ∀ tr : UnforcedLeray.B0140.TrainSol ν (cOf ν), UnforcedLeray.Short.PartI.IsBUCTrain tr →
        ∃ A a : ℝ, 0 ≤ A ∧ 0 < a ∧
          (∀ x : ℝ × (ℝ × ℝ), 0 < x.1 →
            DifferentiableAt ℝ (fun x : ℝ × (ℝ × ℝ) => tr.p x.1 x.2) x) ∧
          (∀ x : ℝ × (ℝ × ℝ), 0 < x.1 →
            (1 + |x.2.2|) ^ 4 * |tr.p x.1 x.2| ≤ A * Real.exp (-(a * x.1))) ∧
          (∀ x : ℝ × (ℝ × ℝ), 0 < x.1 →
            (1 + |x.2.2|) ^ 4 * ‖fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => tr.p x.1 x.2) x‖ ≤
              A * Real.exp (-(a * x.1))) := by
  obtain ⟨C0, N0, κ0, n0, hC0, hκ0, hn0, h0⟩ := lpt_jet_bound hF 0 0
  obtain ⟨C1, N1, κ1, n1, hC1, hκ1, hn1, h1⟩ := lpt_jet_bound hF 0 1
  obtain ⟨C2, N2, κ2, n2, hC2, hκ2, hn2, h2⟩ := lpt_jet_bound hF 1 0
  obtain ⟨K, hK0, hKJ⟩ := UnforcedLeray.Short.PartI.jointFromAgeJets 1
  refine ⟨min n0 (min n1 n2), lt_min hn0 (lt_min hn1 hn2), ?_⟩
  intro ν hν hνa tr hbuc
  have hν0 : ν ≤ n0 := hνa.trans (min_le_left _ _)
  have hν1 : ν ≤ n1 := hνa.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν2 : ν ≤ n2 := hνa.trans ((min_le_right _ _).trans (min_le_right _ _))
  set κ : ℝ := min κ0 (min κ1 κ2) with hκdef
  have hκ : 0 < κ := lt_min hκ0 (lt_min hκ1 hκ2)
  have hκ0' : κ ≤ κ0 := min_le_left _ _
  have hκ1' : κ ≤ κ1 := (min_le_right _ _).trans (min_le_left _ _)
  have hκ2' : κ ≤ κ2 := (min_le_right _ _).trans (min_le_right _ _)
  set P0 := UnforcedLeray.Short.PartI.polyP C0 N0 ν (cOf ν) with hP0
  set P1 := UnforcedLeray.Short.PartI.polyP C1 N1 ν (cOf ν) with hP1
  set P2 := UnforcedLeray.Short.PartI.polyP C2 N2 ν (cOf ν) with hP2
  have hpoly : ∀ (C : ℝ) (N : ℕ), 0 < C → 0 ≤ UnforcedLeray.Short.PartI.polyP C N ν (cOf ν) := by
    intro C N hC
    unfold UnforcedLeray.Short.PartI.polyP cOf
    have : 0 ≤ 1 + (ν ^ 2)⁻¹ + ν⁻¹ := by positivity
    exact mul_nonneg hC.le (pow_nonneg this N)
  have hP0n := hpoly C0 N0 hC0
  have hP1n := hpoly C1 N1 hC1
  have hP2n := hpoly C2 N2 hC2
  have hsm : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => tr.p x.1 x.2) (Ioi 0 ×ˢ univ) :=
    tr.isTrain.smooth_p.mono (prod_mono Ioi_subset_Ici_self (subset_refl _))
  have hexp : ∀ (κi : ℝ), κ ≤ κi → ∀ x : ℝ × (ℝ × ℝ), 0 < x.1 →
      Real.exp (-((κi * ν ^ 5) * x.1)) ≤ Real.exp (-((κ * ν ^ 5) * x.1)) := by
    intro κi hk x hx
    apply Real.exp_le_exp.2
    have : 0 ≤ ν ^ 5 * x.1 := by positivity
    nlinarith
  have hE4 : ∀ x : ℝ × (ℝ × ℝ), 0 ≤ (1 + |x.2.2|) ^ 4 := fun x => by positivity
  have hW0 : ∀ x : ℝ × (ℝ × ℝ), 0 < Real.exp (-((κ * ν ^ 5) * x.1)) := fun x => Real.exp_pos _
  refine ⟨4 * P0 + K * (4 * P1 + 4 * P2), (κ * ν ^ 5), by positivity, by positivity, ?_, ?_, ?_⟩
  · intro x hx
    have hn : (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) ∈ nhds x :=
      prod_mem_nhds (Ioi_mem_nhds hx) Filter.univ_mem
    exact (hsm.contDiffAt hn).differentiableAt (by simp)
  · intro x hx
    have h := h0 ν hν hν0 tr hbuc x.1 hx x.2
    rw [lpt_norm_ageJet_zero] at h
    rw [Real.norm_eq_abs] at h
    have e := hexp κ0 hκ0' x hx
    have hnn : 0 ≤ K * (4 * P1 + 4 * P2) := by positivity
    calc (1 + |x.2.2|) ^ 4 * |tr.p x.1 x.2| ≤ 4 * (P0 * Real.exp (-((κ0 * ν ^ 5) * x.1))) := h
      _ ≤ 4 * (P0 * Real.exp (-((κ * ν ^ 5) * x.1))) := by gcongr
      _ ≤ (4 * P0 + K * (4 * P1 + 4 * P2)) * Real.exp (-((κ * ν ^ 5) * x.1)) := by
          nlinarith [hW0 x, mul_nonneg hnn (hW0 x).le]
      _ = _ := by ring_nf
  · intro x hx
    have ha := h1 ν hν hν1 tr hbuc x.1 hx x.2
    have hb := h2 ν hν hν2 tr hbuc x.1 hx x.2
    have hj := hKJ (fun s z => tr.p s z) hsm x hx
    rw [norm_iteratedFDeriv_one] at hj
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hj
    have e1 := hexp κ1 hκ1' x hx
    have e2 := hexp κ2 hκ2' x hx
    set a1 := ‖UnforcedLeray.Short.PartI.ageJet 0 1 tr.p x.1 x.2‖
    set a2 := ‖UnforcedLeray.Short.PartI.ageJet 1 0 tr.p x.1 x.2‖
    have hE := hE4 x
    have hsum : (1 + |x.2.2|) ^ 4 * (a1 + a2) ≤
        4 * (P1 * Real.exp (-((κ * ν ^ 5) * x.1))) + 4 * (P2 * Real.exp (-((κ * ν ^ 5) * x.1))) := by
      rw [mul_add]
      refine add_le_add (ha.trans ?_) (hb.trans ?_) <;> gcongr
    calc (1 + |x.2.2|) ^ 4 * ‖fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => tr.p x.1 x.2) x‖
        ≤ (1 + |x.2.2|) ^ 4 * (K * (a1 + a2)) := mul_le_mul_of_nonneg_left hj hE
      _ = K * ((1 + |x.2.2|) ^ 4 * (a1 + a2)) := by ring
      _ ≤ K * (4 * (P1 * Real.exp (-((κ * ν ^ 5) * x.1))) +
            4 * (P2 * Real.exp (-((κ * ν ^ 5) * x.1)))) := mul_le_mul_of_nonneg_left hsum hK0
      _ = (K * (4 * P1 + 4 * P2)) * Real.exp (-((κ * ν ^ 5) * x.1)) := by ring
      _ ≤ (4 * P0 + K * (4 * P1 + 4 * P2)) * Real.exp (-((κ * ν ^ 5) * x.1)) := by
          have : 0 ≤ 4 * P0 := by positivity
          nlinarith [hW0 x]

end UnforcedLeray.Short.PartIIIb.Concrete

end
