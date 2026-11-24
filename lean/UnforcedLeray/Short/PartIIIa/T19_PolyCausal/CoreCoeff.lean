import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T19
import UnforcedLeray.Short.PartIIIa.Clock.FreeMoving.Rate.FmrTrainClose
import UnforcedLeray.Short.PartIIIa.Clock.Existence.FluxPath.TrainBoundsSmall.Sup

/-!
# Part III-a, task `PartIII-a:T19/1`: polynomial train coefficient bound on the core `(0, H)`

Source of record: `the November 2 reference manuscript` (SP), lines 3466-3476
(polynomial train coefficient bound on the core `0 < s ≤ H = coreEnd ν b` at `m = 9`), 291-303
(`sct:comparison`), 460-467 (`sct:transverse`).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa

open UnforcedLeray.Short.PartI

/-- `‖D^j v(s, x)‖ ≤ ‖D^j(v(s) - V_c^p(s))(x)‖ + ‖D^j V_c^p(s)(x)‖` at positive width. -/
private theorem norm_train_le_diff_add_Vc {ν c s : ℝ} (tr : B0140.TrainSol ν c) (hs : 0 ≤ s)
    (hc : 0 < c) (ha : 0 < Train.width ν s) (j : ℕ) (x : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ j (tr.v s) x‖ ≤
      ‖iteratedFDeriv ℝ j (fun z => tr.v s z - Train.Vc ν c s z) x‖ +
        ‖iteratedFDeriv ℝ j (Train.Vc ν c s) x‖ := by
  have h1 : ContDiffAt ℝ j (tr.v s) x :=
    ((FmrTC.contDiff_train tr hs).of_le (by exact_mod_cast le_top)).contDiffAt
  have h2 : ContDiffAt ℝ j (Train.Vc ν c s) x :=
    ((Spine.vcReg_contDiff_Vc hc ha).of_le (by exact_mod_cast le_top)).contDiffAt
  have e : iteratedFDeriv ℝ j (fun z => tr.v s z - Train.Vc ν c s z) x =
      iteratedFDeriv ℝ j (tr.v s) x - iteratedFDeriv ℝ j (Train.Vc ν c s) x :=
    iteratedFDeriv_sub_apply h1 h2
  rw [e]
  exact norm_le_norm_sub_add _ _

/-- On `ℝ²`, `⟨x⟩^9 ≤ (1 + |x|²)^8`. -/
private theorem bracket_rpow_nine_le_jb_pow_eight (x : B0579.Plane) :
    B0579.bracket x ^ (9 : ℝ) ≤ B0579.jb x ^ 8 := by
  have hjb1 : 1 ≤ B0579.jb x := by
    unfold B0579.jb
    nlinarith [sq_nonneg x.1, sq_nonneg x.2]
  have hbr1 : 1 ≤ B0579.bracket x := by
    unfold B0579.bracket
    exact Real.one_le_sqrt.2 hjb1
  calc B0579.bracket x ^ (9 : ℝ)
      ≤ B0579.bracket x ^ (16 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hbr1 (by norm_num)
    _ = B0579.bracket x ^ (2 * 8 : ℕ) := by
        rw [← Real.rpow_natCast]
        norm_num
    _ = (B0579.bracket x ^ 2) ^ 8 := pow_mul _ 2 8
    _ = B0579.jb x ^ 8 := by
        unfold B0579.bracket
        rw [Real.sq_sqrt (by linarith)]

/-- Polynomial bound on `⟨x⟩^9 ‖D^j(tr.v s) x‖` on the core `0 < s ≤ (νb)⁻¹ / ν` for a single
derivative order `j`. -/
private theorem trainCoreCoeff_order (hC : PartI.TrainComparison) (hT : PartI.TrainTransverseTails)
    {b : ℝ} (hb : 0 < b) (j : ℕ) :
    ∃ (p_j : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀, ∀ tr : B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      PartI.IsBUCTrain tr → ∀ s : ℝ, 0 < s → s ≤ (ν * b)⁻¹ / ν →
        ∀ x ∈ B0579.cell (ν ^ (-2 : ℝ)),
          B0579.bracket x ^ (9 : ℝ) * ‖iteratedFDeriv ℝ j (tr.v s) x‖ ≤ ν ^ (-(p_j : ℝ)) := by
  obtain ⟨Cc, bc, νc, hCc, hbc, hνc, HC⟩ := hC 2 (by norm_num) j
  obtain ⟨bt, C₀, C', hbt, hC₀, hC', Ct, Nt, νt, hCt, hνt, HT⟩ := hT 2 (by norm_num) 0 j
  obtain ⟨Cv, hCv, HV⟩ := FmrTC.Vc_weighted j
  have hbi : 0 < b⁻¹ := inv_pos.2 hb
  have hbti : 0 < bt⁻¹ := inv_pos.2 hbt
  have hDnn : 0 ≤ ((16 : ℕ).factorial : ℝ) * Real.exp 1 := by positivity
  obtain ⟨K, hK4, hKCc, hKbt, hKbti, hKC', hKC₀, hKCt, hKCv, hKb, hKbi, hKD⟩ :
      ∃ K : ℝ, 4 ≤ K ∧ Cc ≤ K ∧ bt ≤ K ∧ bt⁻¹ ≤ K ∧ C' ≤ K ∧ C₀ ≤ K ∧ Ct ≤ K ∧ Cv ≤ K ∧ b ≤ K ∧
        b⁻¹ ≤ K ∧ ((16 : ℕ).factorial : ℝ) * Real.exp 1 ≤ K := by
    generalize ((16 : ℕ).factorial : ℝ) * Real.exp 1 = D at hDnn ⊢
    generalize b⁻¹ = bi at hbi ⊢
    generalize bt⁻¹ = bti at hbti ⊢
    refine ⟨4 + Cc + bt + bti + C' + C₀ + Ct + Cv + b + bi + D,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  have hKpos : 0 < K := by linarith
  refine ⟨7 * Nt + 123, min νc (min νt K⁻¹), lt_min hνc (lt_min hνt (inv_pos.2 hKpos)), ?_⟩
  intro ν hν tr htr s hs hsS x hx
  have hν0 : 0 < ν := hν.1
  have hνc' : ν ≤ νc := hν.2.trans (min_le_left _ _)
  have hνt' : ν ≤ νt := hν.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hνK : ν ≤ K⁻¹ := hν.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = ν⁻¹ := ⟨_, rfl⟩
  have hyK : K ≤ y := by
    rw [hy]
    exact (le_inv_comm₀ hν0 hKpos).1 hνK
  have hy4 : 4 ≤ y := hK4.trans hyK
  have hy0 : 0 < y := by linarith
  have hy1 : 1 ≤ y := by linarith
  have hy2 : 16 ≤ y ^ 2 := by
    calc (16 : ℝ) = 4 ^ 2 := by norm_num
      _ ≤ y ^ 2 := pow_le_pow_left₀ (by norm_num) hy4 2
  have hcy : ν ^ (-2 : ℝ) = y ^ 2 := by
    rw [Real.rpow_neg hν0.le, Real.rpow_two, hy, inv_pow]
  have hc0 : 0 < ν ^ (-2 : ℝ) := by rw [hcy]; positivity
  have hνs : 0 ≤ ν * s := (mul_pos hν0 hs).le
  have ha1 : 1 ≤ Train.width ν s := by unfold Train.width; linarith
  have ha0 : 0 < Train.width ν s := by linarith
  have hνS : ν * ((ν * b)⁻¹ / ν) = y * b⁻¹ := by
    rw [hy]
    field_simp
  have hS : (ν * b)⁻¹ / ν = y ^ 2 * b⁻¹ := by
    rw [hy]
    field_simp
  have hS0 : 0 ≤ (ν * b)⁻¹ / ν := by rw [hS]; positivity
  have hay : Train.width ν s ≤ 1 + y * b⁻¹ := by
    have h1 : ν * s ≤ ν * ((ν * b)⁻¹ / ν) := mul_le_mul_of_nonneg_left hsS hν0.le
    rw [hνS] at h1
    unfold Train.width
    linarith
  have hac : Train.width ν s ≤ (ν ^ (-2 : ℝ)) ^ 2 := by
    rw [hcy]
    have h1 : y * b⁻¹ ≤ y * y := mul_le_mul_of_nonneg_left (hKbi.trans hyK) hy0.le
    have h2 : (y ^ 2) ^ 2 = y ^ 2 * y ^ 2 := by ring
    have h3 : 16 * y ^ 2 ≤ y ^ 2 * y ^ 2 := mul_le_mul_of_nonneg_right hy2 (by positivity)
    rw [h2]
    linarith
  have hjbnn : 0 ≤ B0579.jb x := (B0579.jb_pos x).le
  have hjb := FmrTC.jb_le_of_mem_cell hx hc0
  rw [hcy] at hjb
  have hc2 : 1 + (y ^ 2) ^ 2 ≤ y ^ 5 := by
    have h1 : y ^ 5 = y * (y ^ 2) ^ 2 := by ring
    have h2 : 1 ≤ (y ^ 2) ^ 2 := one_le_pow₀ (by linarith)
    have h3 : 4 * (y ^ 2) ^ 2 ≤ y * (y ^ 2) ^ 2 := mul_le_mul_of_nonneg_right hy4 (by positivity)
    rw [h1]
    linarith
  have hrpow_eq : y ^ (7 * Nt + 123) = ν ^ (-((7 * Nt + 123 : ℕ) : ℝ)) := by
    rw [hy, Real.rpow_neg hν0.le, Real.rpow_natCast, inv_pow]
  rw [← hrpow_eq]
  have hbr_jb := bracket_rpow_nine_le_jb_pow_eight x
  suffices hmain : ‖iteratedFDeriv ℝ j (tr.v s) x‖ * B0579.jb x ^ 8 ≤ y ^ (7 * Nt + 123) by
    calc B0579.bracket x ^ (9 : ℝ) * ‖iteratedFDeriv ℝ j (tr.v s) x‖
        ≤ B0579.jb x ^ 8 * ‖iteratedFDeriv ℝ j (tr.v s) x‖ :=
          mul_le_mul_of_nonneg_right hbr_jb (norm_nonneg _)
      _ = ‖iteratedFDeriv ℝ j (tr.v s) x‖ * B0579.jb x ^ 8 := mul_comm _ _
      _ ≤ y ^ (7 * Nt + 123) := hmain
  by_cases hz : C' / ν + 2 ≤ |x.2|
  · -- (i) Transverse tail `|x.2| ≥ C'/ν + 2`: direct polynomial-times-tail bound from `hT`
    obtain ⟨l, hl⟩ : ∃ l : ℝ, l = |x.2| - (C' / ν + 2) := ⟨_, rfl⟩
    have hl0 : 0 ≤ l := by rw [hl]; linarith
    have hη : |x.2| = C' * y + 2 + l := by
      rw [hl, hy, div_eq_mul_inv]
      ring
    have hz' : C' / ν + 2 + l ≤ |x.2| := by rw [hl]; linarith
    have hTail := HT ((ν * b)⁻¹ / ν) hS0 ν hν0 hνt' tr htr l hl0 s hs hsS x hz'
    obtain ⟨-, hA, -⟩ := hTail
    rw [FmrTC.ageJet_zero_eq] at hA
    have hper : PartI.trainPeriod 2 ν = y ^ 2 := hcy
    have hA' : ‖iteratedFDeriv ℝ j (tr.v s) x‖ ≤
        Ct * ((1 + y ^ 2 + y) * (1 + y ^ 2 * b⁻¹)) ^ Nt *
          (Real.exp (-(bt * l / y ^ 2)) + Real.exp (-(bt * l ^ 2 / (C₀ + y * b⁻¹)))) := by
      have h := hA
      simp only [PartI.polyPS, hper, hνS, ← hy] at h
      rw [hS] at h
      exact h
    have hB0 : (0 : ℝ) * (1 + x.2 ^ 2) ^ 8 ≤ 1 * Train.width ν s ^ 8 := by
      rw [zero_mul, one_mul]
      positivity
    have hbig := FmrTC.tail_num hy4 hb hbt hC₀ hC' hCt (hKbt.trans hyK) (hKbti.trans hyK)
      (hKC₀.trans hyK) (hKC'.trans hyK) (hKCt.trans hyK) hy1 (hKbi.trans hyK)
      (hKD.trans hyK) ha1 hay hl0 hη hA' hB0
    rw [add_zero] at hbig
    have h1 : B0579.jb x ^ 8 ≤ (y ^ 5 * (1 + x.2 ^ 2)) ^ 8 := by
      refine pow_le_pow_left₀ hjbnn (hjb.trans ?_) 8
      exact mul_le_mul_of_nonneg_right hc2 (by positivity)
    calc ‖iteratedFDeriv ℝ j (tr.v s) x‖ * B0579.jb x ^ 8
        ≤ ‖iteratedFDeriv ℝ j (tr.v s) x‖ * (y ^ 5 * (1 + x.2 ^ 2)) ^ 8 :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = y ^ 40 * (‖iteratedFDeriv ℝ j (tr.v s) x‖ * (1 + x.2 ^ 2) ^ 8) := by
          rw [mul_pow, ← pow_mul]
          ring
      _ ≤ y ^ 40 * y ^ (7 * Nt + 68) := mul_le_mul_of_nonneg_left hbig (by positivity)
      _ = y ^ (7 * Nt + 108) := by ring
      _ ≤ y ^ (7 * Nt + 123) := pow_le_pow_right₀ hy1 (by omega)
  · -- (ii) Interior band `|x.2| < C'/ν + 2`: `⟨x⟩` is polynomial and `v = (v - Vc) + Vc`
    have hR : |x.2| < C' * y + 2 := by
      rw [hy, ← div_eq_mul_inv]
      exact not_le.1 hz
    have hRy : C' * y + 2 ≤ y ^ 3 := by
      have h1 : C' * y ≤ y * y := mul_le_mul_of_nonneg_right (hKC'.trans hyK) hy0.le
      have h2 : y ^ 3 = y * y ^ 2 := by ring
      have h3 : 4 * y ^ 2 ≤ y * y ^ 2 := mul_le_mul_of_nonneg_right hy4 (by positivity)
      rw [h2]
      linarith
    have hη2 : 1 + x.2 ^ 2 ≤ y ^ 7 := by
      have h1 : |x.2| ≤ y ^ 3 := hR.le.trans hRy
      have h2 : x.2 ^ 2 ≤ (y ^ 3) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      have h3 : y ^ 7 = y * (y ^ 3) ^ 2 := by ring
      have h4 : 1 ≤ (y ^ 3) ^ 2 := one_le_pow₀ (one_le_pow₀ hy1)
      have h5 : 4 * (y ^ 3) ^ 2 ≤ y * (y ^ 3) ^ 2 := mul_le_mul_of_nonneg_right hy4 (by positivity)
      rw [h3]
      linarith
    have hjb8 : B0579.jb x ^ 8 ≤ y ^ 96 := by
      have h1 : B0579.jb x ≤ y ^ 12 := by
        calc B0579.jb x ≤ (1 + (y ^ 2) ^ 2) * (1 + x.2 ^ 2) := hjb
          _ ≤ y ^ 5 * y ^ 7 := mul_le_mul hc2 hη2 (by positivity) (by positivity)
          _ = y ^ 12 := by ring
      calc B0579.jb x ^ 8 ≤ (y ^ 12) ^ 8 := pow_le_pow_left₀ hjbnn h1 8
        _ = y ^ 96 := by ring
    -- Bound `E = ‖D^j(v - Vc) x‖` by `hC`
    set E : ℝ := ‖iteratedFDeriv ℝ j (fun z => tr.v s z - Train.Vc ν (ν ^ (-2 : ℝ)) s z) x‖
    have hEsup : E ≤ Cc * y * Train.width ν s ^ (-((5 + (j : ℝ)) / 2)) *
        Real.exp (-(bc * (y ^ 2) ^ 2 / Train.width ν s)) := by
      have H1 := (HC ν hν0 hνc' tr htr s hs.le hac).2
      have hXnn : 0 ≤ Cc * ν⁻¹ * Train.width ν s ^ (-((5 + (j : ℝ)) / 2)) *
          Real.exp (-(bc * PartI.trainPeriod 2 ν ^ 2 / Train.width ν s)) := by
        have := Real.rpow_nonneg ha0.le (-((5 + (j : ℝ)) / 2))
        positivity
      have H2 := B0277.norm_le_of_supNormD_le hXnn H1 x
      have hper : PartI.trainPeriod 2 ν = y ^ 2 := hcy
      have hRHS : Cc * ν⁻¹ * Train.width ν s ^ (-((5 + (j : ℝ)) / 2)) *
          Real.exp (-(bc * PartI.trainPeriod 2 ν ^ 2 / Train.width ν s)) =
            Cc * y * Train.width ν s ^ (-((5 + (j : ℝ)) / 2)) *
              Real.exp (-(bc * (y ^ 2) ^ 2 / Train.width ν s)) := by
        rw [hper, ← hy]
      rw [← hRHS]
      exact H2
    have he : -((5 + (j : ℝ)) / 2) ≤ 0 := by
      have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    have hSm : E ≤ y ^ 2 * Real.exp (-(bc * b / 2 * y)) :=
      FmrTC.small_num hy4 hb hbc (hKCc.trans hyK) (hKb.trans hyK) ha1 hay rfl he hEsup
    have hE_le : E ≤ y ^ 2 := by
      have hby_pos : 0 ≤ bc * b / 2 * y := by positivity
      have hexp1 : Real.exp (-(bc * b / 2 * y)) ≤ 1 :=
        Real.exp_le_one_iff.2 (by linarith)
      calc E ≤ y ^ 2 * Real.exp (-(bc * b / 2 * y)) := hSm
        _ ≤ y ^ 2 * 1 := mul_le_mul_of_nonneg_left hexp1 (by positivity)
        _ = y ^ 2 := mul_one _
    -- Bound `‖D^j Vc x‖` by `FmrTC.Vc_weighted`
    have hB := HV ν (ν ^ (-2 : ℝ)) s hc0 ha1 hac x
    have hW1 : 1 ≤ (1 + x.2 ^ 2) ^ 8 := one_le_pow₀ (by nlinarith [sq_nonneg x.2])
    have ha_y3 : Train.width ν s ≤ y ^ 3 := by
      have h1 : y * b⁻¹ ≤ y * y := mul_le_mul_of_nonneg_left (hKbi.trans hyK) hy0.le
      have h2 : y ^ 3 = y * y ^ 2 := by ring
      have h3 : 4 * y ^ 2 ≤ y * y ^ 2 := mul_le_mul_of_nonneg_right hy4 (by positivity)
      have h4 : y * y = y ^ 2 := by ring
      rw [h2]
      linarith
    have hVc_le : ‖iteratedFDeriv ℝ j (Train.Vc ν (ν ^ (-2 : ℝ)) s) x‖ ≤ y ^ 25 := by
      calc ‖iteratedFDeriv ℝ j (Train.Vc ν (ν ^ (-2 : ℝ)) s) x‖
          ≤ ‖iteratedFDeriv ℝ j (Train.Vc ν (ν ^ (-2 : ℝ)) s) x‖ * (1 + x.2 ^ 2) ^ 8 :=
            le_mul_of_one_le_right (norm_nonneg _) hW1
        _ ≤ Cv * Train.width ν s ^ 8 := hB
        _ ≤ y * (y ^ 3) ^ 8 :=
            mul_le_mul (hKCv.trans hyK) (pow_le_pow_left₀ ha0.le ha_y3 8) (by positivity) hy0.le
        _ = y ^ 25 := by ring
    have hv_le : ‖iteratedFDeriv ℝ j (tr.v s) x‖ ≤ y ^ 27 := by
      have htri := norm_train_le_diff_add_Vc tr hs.le hc0 ha0 j x
      have hy2_25 : y ^ 2 ≤ y ^ 25 := pow_le_pow_right₀ hy1 (by omega)
      have h2y25 : 2 * y ^ 25 ≤ y * y ^ 25 :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have hy26_27 : y * y ^ 25 ≤ y ^ 27 := by
        calc y * y ^ 25 = y ^ 26 := by ring
          _ ≤ y ^ 27 := pow_le_pow_right₀ hy1 (by omega)
      linarith
    calc ‖iteratedFDeriv ℝ j (tr.v s) x‖ * B0579.jb x ^ 8
        ≤ y ^ 27 * y ^ 96 := mul_le_mul hv_le hjb8 (by positivity) (by positivity)
      _ = y ^ 123 := by ring
      _ ≤ y ^ (7 * Nt + 123) := pow_le_pow_right₀ hy1 (by omega)

/-- **`TrainCoreCoeffBound`** from `PartI.TrainComparison` and `PartI.TrainTransverseTails`
(SP lines 3466-3476, 291-303, 460-467). -/
theorem trainCoreCoeffBound_of (hC : UnforcedLeray.Short.PartI.TrainComparison)
    (hT : UnforcedLeray.Short.PartI.TrainTransverseTails) : TrainCoreCoeffBound := by
  intro b hb
  have hb0 : 0 < b := by linarith
  obtain ⟨p₀, ν₀, hν₀, H0⟩ := trainCoreCoeff_order hC hT hb0 0
  obtain ⟨p₁, ν₁, hν₁, H1⟩ := trainCoreCoeff_order hC hT hb0 1
  refine ⟨max p₀ p₁, 2, min (min ν₀ ν₁) 1, by norm_num, lt_min (lt_min hν₀ hν₁) one_pos, ?_⟩
  intro ν hν tr htr s hs x hx
  have hν0 : 0 < ν := hν.1
  have hν1 : ν ≤ 1 := hν.2.trans (min_le_right _ _)
  have hν_0 : ν ∈ Ioc 0 ν₀ := ⟨hν0, hν.2.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
  have hν_1 : ν ∈ Ioc 0 ν₁ := ⟨hν0, hν.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
  have hsS : s ≤ (ν * b)⁻¹ / ν := by
    refine hs.2.trans ?_
    unfold coreEnd
    rw [div_eq_mul_inv, mul_comm (ν * b)⁻¹]
    exact mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 hν0.le)
  have h0 := H0 ν hν_0 tr htr s hs.1 hsS x hx
  have h1 := H1 ν hν_1 tr htr s hs.1 hsS x hx
  rw [norm_iteratedFDeriv_zero] at h0
  rw [norm_iteratedFDeriv_one] at h1
  have hp0 : ν ^ (-(p₀ : ℝ)) ≤ ν ^ (-((max p₀ p₁ : ℕ) : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_ge hν0 hν1 ?_
    exact neg_le_neg (by exact_mod_cast le_max_left p₀ p₁)
  have hp1 : ν ^ (-(p₁ : ℝ)) ≤ ν ^ (-((max p₀ p₁ : ℕ) : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_ge hν0 hν1 ?_
    exact neg_le_neg (by exact_mod_cast le_max_right p₀ p₁)
  calc B0579.bracket x ^ (9 : ℝ) * (‖tr.v s x‖ + ‖fderiv ℝ (tr.v s) x‖)
      = B0579.bracket x ^ (9 : ℝ) * ‖tr.v s x‖ +
          B0579.bracket x ^ (9 : ℝ) * ‖fderiv ℝ (tr.v s) x‖ := mul_add _ _ _
    _ ≤ ν ^ (-((max p₀ p₁ : ℕ) : ℝ)) + ν ^ (-((max p₀ p₁ : ℕ) : ℝ)) :=
        add_le_add (h0.trans hp0) (h1.trans hp1)
    _ = 2 * ν ^ (-((max p₀ p₁ : ℕ) : ℝ)) := (two_mul _).symm

/-- Unconditional **`TrainCoreCoeffBound`** (`PartIII-a:T19/1`, SP lines 3466-3476). -/
theorem trainCoreCoeffBound : UnforcedLeray.Short.IIIa.TrainCoreCoeffBound :=
  trainCoreCoeffBound_of trainComparison_proof
    (trainTransverseTails_of_parts overlap_fluctuation_decay overlap_mean_primitive
      overlap_mean_decay train_vorticity_gaussian_tail train_stream_velocity_pressure_tails)

end UnforcedLeray.Short.IIIa
