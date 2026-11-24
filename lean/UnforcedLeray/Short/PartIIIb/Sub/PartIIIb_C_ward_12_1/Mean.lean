import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_1.Fluct
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_1.MeanSlice
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_1.MeanSmooth

/-!
# Weighted derivatives of the mean stream (source 447-459, `p = ⊤`, `N = 0`, `m ≤ 3`)
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cons.C03.Concrete (Params)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Short.PartI (ageJet meanStream polyP IsBUCTrain)

theorem mean_pointwise (hM : UnforcedLeray.Short.PartI.TrainMeanExpansion) (m b l : ℕ)
    (hm : m ≤ 3) :
    ∃ (C : ℝ) (M : ℕ) (nu0 : ℝ), 0 < C ∧ 0 < nu0 ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ nu0 → ∀ c : ℝ, c = (ν ^ 2)⁻¹ →
        ∀ tr : UnforcedLeray.B0140.TrainSol ν c, IsBUCTrain tr →
          ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanStream tr x.1 x.2) (Ioi 0 ×ˢ univ) →
          ∀ s : ℝ, 0 < s → s ≤ ν⁻¹ → ∀ η : ℝ,
            |η| ^ m * |iteratedDeriv b
              (fun e => iteratedDeriv l (fun r => meanStream tr r e) s) η|
              ≤ polyP C M ν c * (1 + ν⁻¹) ^ 3 := by
  obtain ⟨C, M, nu0, hC, hnu0, H⟩ := hM 2 (by norm_num) 0 m b l ⊤ le_top
  refine ⟨C, M, nu0, hC, hnu0, ?_⟩
  intro ν hν hνn c hc tr htr hsm s hs hsν η
  have hc' : c = UnforcedLeray.Short.PartI.trainPeriod 2 ν :=
    hc.trans (fluct_trainPeriod_two_eq_inv hν).symm
  subst hc'
  have hcnn : 0 ≤ UnforcedLeray.Short.PartI.trainPeriod 2 ν := by
    unfold UnforcedLeray.Short.PartI.trainPeriod
    exact Real.rpow_nonneg hν.le _
  obtain ⟨_, _, _, H4⟩ := H ν hν hνn tr htr
  have h := H4 s hs.le
  have hg := contDiff_iteratedDeriv_slice (fun r e => meanStream tr r e) hsm l s hs
  have hd : Continuous (fun η : ℝ => iteratedDeriv b
      (fun e => iteratedDeriv l (fun r => meanStream tr r e) s) η) :=
    hg.continuous_iteratedDeriv b (by exact_mod_cast le_top)
  have hcont : Continuous (fun η : ℝ => η ^ m * iteratedDeriv b
      (fun e => iteratedDeriv l (fun r => meanStream tr r e) s) η) :=
    (continuous_pow m).mul hd
  set f : ℝ → ℝ := fun η : ℝ => η ^ m * iteratedDeriv b
      (fun e => iteratedDeriv l (fun r => meanStream tr r e) s) η with hf
  have hexp : ((m : ℝ) - b - 1) / 2 - l + (⊤ : ℝ≥0∞).toReal⁻¹ / 2 ≤ 1 := by
    simp only [ENNReal.toReal_top, inv_zero, zero_div, add_zero]
    have : (m : ℝ) ≤ 3 := by exact_mod_cast hm
    have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg _
    have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg _
    linarith
  have h1s : (1 : ℝ) ≤ 1 + s := by linarith
  have hpow : (1 + s) ^ (((m : ℝ) - b - 1) / 2 - l + (⊤ : ℝ≥0∞).toReal⁻¹ / 2) ≤
      (1 + ν⁻¹) ^ 3 := by
    calc _ ≤ (1 + s) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1s hexp
      _ = 1 + s := Real.rpow_one _
      _ ≤ 1 + ν⁻¹ := by linarith
      _ ≤ (1 + ν⁻¹) ^ 3 := by
          have : (1 : ℝ) ≤ 1 + ν⁻¹ := by have := inv_nonneg.2 hν.le; linarith
          calc 1 + ν⁻¹ = (1 + ν⁻¹) ^ 1 := (pow_one _).symm
            _ ≤ _ := pow_le_pow_right₀ this (by norm_num)
  have hP : 0 ≤ polyP C M ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) :=
    fluct_polyP_nonneg hC.le hν hcnn
  have hKp : 0 ≤ polyP C M ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
      (1 + s) ^ (((m : ℝ) - b - 1) / 2 - l + (⊤ : ℝ≥0∞).toReal⁻¹ / 2) :=
    mul_nonneg hP (Real.rpow_nonneg (by linarith) _)
  rw [eLpNorm_exponent_top] at h
  have hae : ∀ᵐ y ∂(volume : Measure ℝ), ‖f y‖ₑ ≤ ENNReal.ofReal
      (polyP C M ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
      (1 + s) ^ (((m : ℝ) - b - 1) / 2 - l + (⊤ : ℝ≥0∞).toReal⁻¹ / 2)) :=
    (ae_le_eLpNormEssSup (f := f) (μ := volume)).mono fun y hy => hy.trans h
  have hU : IsOpen {y : ℝ | ENNReal.ofReal
      (polyP C M ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
      (1 + s) ^ (((m : ℝ) - b - 1) / 2 - l + (⊤ : ℝ≥0∞).toReal⁻¹ / 2)) < ‖f y‖ₑ} :=
    isOpen_lt continuous_const (continuous_enorm.comp hcont)
  have hU0 : volume {y : ℝ | ENNReal.ofReal
      (polyP C M ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
      (1 + s) ^ (((m : ℝ) - b - 1) / 2 - l + (⊤ : ℝ≥0∞).toReal⁻¹ / 2)) < ‖f y‖ₑ} = 0 := by
    rw [ae_iff] at hae
    simpa only [not_le] using hae
  have hempty := (hU.measure_eq_zero_iff (μ := volume)).1 hU0
  have hη : ‖f η‖ₑ ≤ ENNReal.ofReal
      (polyP C M ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
      (1 + s) ^ (((m : ℝ) - b - 1) / 2 - l + (⊤ : ℝ≥0∞).toReal⁻¹ / 2)) := by
    by_contra hcon
    have : η ∈ {y : ℝ | ENNReal.ofReal
      (polyP C M ν (UnforcedLeray.Short.PartI.trainPeriod 2 ν) *
      (1 + s) ^ (((m : ℝ) - b - 1) / 2 - l + (⊤ : ℝ≥0∞).toReal⁻¹ / 2)) < ‖f y‖ₑ} :=
      not_le.1 hcon
    rw [hempty] at this
    exact this
  rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_le_ofReal_iff hKp] at hη
  have hfn : ‖f η‖ = |η| ^ m * |iteratedDeriv b
      (fun e => iteratedDeriv l (fun r => meanStream tr r e) s) η| := by
    simp [hf, norm_mul, norm_pow, Real.norm_eq_abs]
  rw [← hfn]
  exact hη.trans (mul_le_mul_of_nonneg_left hpow hP)

theorem mean_pointwise' (hM : UnforcedLeray.Short.PartI.TrainMeanExpansion) (q : ℕ × ℕ × ℕ) :
    ∃ (C : ℝ) (M : ℕ) (nu0 : ℝ), 0 < C ∧ 0 < nu0 ∧ (q.1 ≤ 3 →
      ∀ ν : ℝ, 0 < ν → ν ≤ nu0 → ∀ c : ℝ, c = (ν ^ 2)⁻¹ →
        ∀ tr : UnforcedLeray.B0140.TrainSol ν c, IsBUCTrain tr →
          ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanStream tr x.1 x.2) (Ioi 0 ×ˢ univ) →
          ∀ s : ℝ, 0 < s → s ≤ ν⁻¹ → ∀ η : ℝ,
            |η| ^ q.1 * |iteratedDeriv q.2.1
              (fun e => iteratedDeriv q.2.2 (fun r => meanStream tr r e) s) η|
              ≤ polyP C M ν c * (1 + ν⁻¹) ^ 3) := by
  by_cases hm : q.1 ≤ 3
  · obtain ⟨C, M, nu0, hC, hn, H⟩ := mean_pointwise hM q.1 q.2.1 q.2.2 hm
    exact ⟨C, M, nu0, hC, hn, fun _ => H⟩
  · exact ⟨1, 0, 1, one_pos, one_pos, fun h => absurd h hm⟩

theorem bgMeanWeighted_of (hM : UnforcedLeray.Short.PartI.TrainMeanExpansion) : BgMeanWeighted := by
  intro dm dp hdm
  choose C N nu0 hC hnu0 H using mean_pointwise' hM
  set T : Finset (ℕ × ℕ × ℕ) := Finset.range 4 ×ˢ Finset.range 4 ×ˢ Finset.range 4 with hT
  have hne : T.Nonempty := ⟨(0, 0, 0), by simp [hT]⟩
  refine ⟨T.inf' hne nu0, ?_, ?_⟩
  · rw [Finset.lt_inf'_iff]
    intro q _
    exact hnu0 q
  · intro p d hreg hν
    have hνle : ∀ q ∈ T, p.ν ≤ nu0 q := fun q hq => le_trans hν (Finset.inf'_le _ hq)
    have hsm := bgMeanSmooth p d dm dp hreg
    have hK : ∀ q ∈ T, 0 ≤ polyP (C q) (N q) p.ν p.c * (1 + p.ν⁻¹) ^ 3 := by
      intro q _
      exact mul_nonneg (fluct_polyP_nonneg (hC q).le p.ν_pos p.c_pos.le) (by
        have := inv_nonneg.2 p.ν_pos.le
        positivity)
    refine ⟨8 * ∑ q ∈ T, polyP (C q) (N q) p.ν p.c * (1 + p.ν⁻¹) ^ 3, ?_⟩
    intro b l hbl s hs hsν η
    have hmem : ∀ m : ℕ, m ≤ 3 → (m, b, l) ∈ T := by
      intro m hm
      simp only [hT, Finset.mem_product, Finset.mem_range]
      omega
    have hbd : ∀ m : ℕ, m ≤ 3 → |η| ^ m * |iteratedDeriv b
        (fun e => iteratedDeriv l (fun r => meanStream p.train r e) s) η| ≤
        ∑ q ∈ T, polyP (C q) (N q) p.ν p.c * (1 + p.ν⁻¹) ^ 3 := by
      intro m hm
      have h1 := H (m, b, l) hm p.ν p.ν_pos (hνle _ (hmem m hm)) p.c hreg.c_eq p.train
        hreg.train_buc hsm s hs hsν η
      exact h1.trans (Finset.single_le_sum (f := fun q : ℕ × ℕ × ℕ =>
        polyP (C q) (N q) p.ν p.c * (1 + p.ν⁻¹) ^ 3) hK (hmem m hm))
    have h0 := hbd 0 (by norm_num)
    have h3 := hbd 3 (by norm_num)
    rw [pow_zero, one_mul] at h0
    set F := |iteratedDeriv b (fun e => iteratedDeriv l (fun r => meanStream p.train r e) s) η|
      with hF
    have hF0 : 0 ≤ F := abs_nonneg _
    have hpoly : (1 + |η|) ^ 3 ≤ 4 * (1 + |η| ^ 3) := by
      have ht : 0 ≤ |η| := abs_nonneg _
      nlinarith [mul_nonneg (sq_nonneg (|η| - 1)) ht, sq_nonneg (|η| - 1)]
    calc (1 + |η|) ^ 3 * F ≤ 4 * (1 + |η| ^ 3) * F := mul_le_mul_of_nonneg_right hpoly hF0
      _ = 4 * (F + |η| ^ 3 * F) := by ring
      _ ≤ 8 * ∑ q ∈ T, polyP (C q) (N q) p.ν p.c * (1 + p.ν⁻¹) ^ 3 := by linarith

end UnforcedLeray.Short.PartIIIb.Concrete
