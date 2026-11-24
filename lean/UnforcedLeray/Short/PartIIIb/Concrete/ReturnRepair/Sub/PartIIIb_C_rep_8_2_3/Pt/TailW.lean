import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.PtOrg

/-!
# `PartIII-b:C/rep/8/2/3/2/7`: the weighted transverse tails `TailW` from Part I `sct:transverse`

Source of record: `the November 2 reference manuscript` 460-467 (Part I
`sct:transverse`, `PartI.TrainTransverseTails`), with `ρ = 2`, so `trainPeriod 2 ν = (ν²)⁻¹ = cOf ν`.
The transport of the train along this equality of periods is by `subst`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cyl (Plane)

/-- Transport of a BUC train along an equality of periods (`v, p, ψ` are kept). -/
theorem tailW_transport {ν c c' : ℝ} (h : c = c')
    (tr : UnforcedLeray.B0140.TrainSol ν c)
    (hb : UnforcedLeray.Short.PartI.IsBUCTrain tr) :
    ∃ tr' : UnforcedLeray.B0140.TrainSol ν c',
      UnforcedLeray.Short.PartI.IsBUCTrain tr' ∧ tr'.v = tr.v ∧ tr'.p = tr.p ∧ tr'.ψ = tr.ψ := by
  subst h
  exact ⟨tr, hb, rfl, rfl, rfl⟩

/-- `trainPeriod 2 ν = (ν²)⁻¹`. -/
theorem tailW_trainPeriod_two {ν : ℝ} (hν : 0 < ν) :
    UnforcedLeray.Short.PartI.trainPeriod 2 ν = (ν ^ 2)⁻¹ := by
  unfold UnforcedLeray.Short.PartI.trainPeriod
  rw [Real.rpow_neg hν.le, Real.rpow_two]

/-- Pure arithmetic in `t ≥ 1`: `C((1+t²+t)(1+t))^N ≤ C 6^N t^{3N}`. -/
theorem tailW_poly_arith (C : ℝ) (N : ℕ) (hC : 0 ≤ C) {t : ℝ} (ht : 1 ≤ t) :
    C * ((1 + t ^ 2 + t) * (1 + t)) ^ N ≤ C * 6 ^ N * t ^ (3 * N) := by
  have ht0 : 0 ≤ t := by linarith
  have hQ0 : 0 ≤ (1 + t ^ 2 + t) * (1 + t) := by nlinarith
  have hQ : (1 + t ^ 2 + t) * (1 + t) ≤ 6 * t ^ 3 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ t - 1) ht0,
      mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ t - 1) ht0) ht0,
      mul_nonneg (by linarith : (0:ℝ) ≤ t - 1) (mul_nonneg ht0 ht0)]
  have hpow := pow_le_pow_left₀ hQ0 hQ N
  have heq : (6 * t ^ 3) ^ N = 6 ^ N * t ^ (3 * N) := by rw [mul_pow, ← pow_mul]
  calc C * ((1 + t ^ 2 + t) * (1 + t)) ^ N ≤ C * (6 * t ^ 3) ^ N :=
        mul_le_mul_of_nonneg_left hpow hC
    _ = C * 6 ^ N * t ^ (3 * N) := by rw [heq]; ring

/-- The polynomial `P_S` at `c = (ν²)⁻¹`, `S = 1/ν`. -/
theorem tailW_poly {ν : ℝ} (C : ℝ) (N : ℕ) (hC : 0 ≤ C) (hν : 0 < ν) (hν1 : ν ≤ 1) :
    UnforcedLeray.Short.PartI.polyPS C N ν (ν ^ 2)⁻¹ (1 / ν) ≤ C * 6 ^ N * ν⁻¹ ^ (3 * N) := by
  have ht : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have e : UnforcedLeray.Short.PartI.polyPS C N ν (ν ^ 2)⁻¹ (1 / ν) =
      C * ((1 + ν⁻¹ ^ 2 + ν⁻¹) * (1 + ν⁻¹)) ^ N := by
    unfold UnforcedLeray.Short.PartI.polyPS
    rw [← inv_pow, one_div]
  rw [e]
  exact tailW_poly_arith C N hC ht

/-- `x⁴ e^{-x} ≤ 24` for `x ≥ 0`. -/
theorem tailW_exp_quartic (y : ℝ) (hy : 0 ≤ y) : y ^ 4 * Real.exp (-y) ≤ 24 := by
  have h := Real.pow_div_factorial_le_exp y hy 4
  have hf : ((4 : ℕ).factorial : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [hf] at h
  have h' : y ^ 4 ≤ Real.exp y * 24 := (div_le_iff₀ (by norm_num : (0:ℝ) < 24)).1 h
  have hexp : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
  have hpos : 0 < Real.exp (-y) := Real.exp_pos _
  calc y ^ 4 * Real.exp (-y) ≤ (Real.exp y * 24) * Real.exp (-y) :=
        mul_le_mul_of_nonneg_right h' hpos.le
    _ = 24 := by rw [mul_assoc, mul_comm (24:ℝ), ← mul_assoc, hexp, one_mul]

/-- `w² e^{-w} ≤ 2` for `w ≥ 0`. -/
theorem tailW_exp_sq (w : ℝ) (hw : 0 ≤ w) : w ^ 2 * Real.exp (-w) ≤ 2 := by
  have h := Real.pow_div_factorial_le_exp w hw 2
  have hf : ((2 : ℕ).factorial : ℝ) = 2 := by norm_num [Nat.factorial]
  rw [hf] at h
  have h' : w ^ 2 ≤ Real.exp w * 2 := (div_le_iff₀ (by norm_num : (0:ℝ) < 2)).1 h
  have hexp : Real.exp w * Real.exp (-w) = 1 := by rw [← Real.exp_add]; simp
  have hpos : 0 < Real.exp (-w) := Real.exp_pos _
  calc w ^ 2 * Real.exp (-w) ≤ (Real.exp w * 2) * Real.exp (-w) :=
        mul_le_mul_of_nonneg_right h' hpos.le
    _ = 2 := by rw [mul_assoc, mul_comm (2:ℝ), ← mul_assoc, hexp, one_mul]

/-- The `E₁` term: `l⁴ e^{-b l/(ν²)⁻¹} ≤ 24 b⁻⁴ ν⁻⁸`. -/
theorem tailW_E1 {b ν l : ℝ} (hb : 0 < b) (hν : 0 < ν) (hl : 0 ≤ l) :
    l ^ 4 * Real.exp (-(b * l / (ν ^ 2)⁻¹)) ≤ 24 * b⁻¹ ^ 4 * ν⁻¹ ^ 8 := by
  have e : b * l / (ν ^ 2)⁻¹ = b * ν ^ 2 * l := by rw [div_inv_eq_mul]; ring
  rw [e]
  have hy : 0 ≤ b * ν ^ 2 * l := by positivity
  have h1 := tailW_exp_quartic _ hy
  have hbpos : 0 < b ^ 4 * ν ^ 8 := by positivity
  have key : l ^ 4 * Real.exp (-(b * ν ^ 2 * l)) * (b ^ 4 * ν ^ 8) ≤ 24 := by
    have e2 : l ^ 4 * Real.exp (-(b * ν ^ 2 * l)) * (b ^ 4 * ν ^ 8) =
        (b * ν ^ 2 * l) ^ 4 * Real.exp (-(b * ν ^ 2 * l)) := by ring
    rw [e2]; exact h1
  have hfin : 24 * b⁻¹ ^ 4 * ν⁻¹ ^ 8 = 24 / (b ^ 4 * ν ^ 8) := by
    field_simp
  rw [hfin, le_div_iff₀ hbpos]
  exact key

/-- The `E₂` term: `l⁴ e^{-b l²/(C₀+1)} ≤ 2((C₀+1)/b)²`. -/
theorem tailW_E2 {b C₀ l : ℝ} (hb : 0 < b) (hC₀ : 0 < C₀) :
    l ^ 4 * Real.exp (-(b * l ^ 2 / (C₀ + 1))) ≤ ((C₀ + 1) / b) ^ 2 * 2 := by
  have hb0 : b ≠ 0 := hb.ne'
  have hC1 : C₀ + 1 ≠ 0 := by linarith
  have hC1p : 0 < C₀ + 1 := by linarith
  have hw0 : 0 ≤ b * l ^ 2 / (C₀ + 1) := div_nonneg (mul_nonneg hb.le (sq_nonneg l)) hC1p.le
  have hl4 : l ^ 4 = ((C₀ + 1) / b) ^ 2 * (b * l ^ 2 / (C₀ + 1)) ^ 2 := by
    field_simp
  rw [hl4, mul_assoc]
  exact mul_le_mul_of_nonneg_left (tailW_exp_sq _ hw0) (by positivity)

/-- The core: `(1+x)⁴ (E₁+E₂) ≤ D t⁸` with `x = C'/ν + 2 + l`, `t = ν⁻¹`. -/
theorem tailW_core {b C₀ C' ν l : ℝ} (hb : 0 < b) (hC₀ : 0 < C₀) (hC' : 0 < C')
    (hν : 0 < ν) (hν1 : ν ≤ 1) (hl : 0 ≤ l) :
    (1 + (C' / ν + 2 + l)) ^ 4 *
        (Real.exp (-(b * l / (ν ^ 2)⁻¹)) + Real.exp (-(b * l ^ 2 / (C₀ + 1)))) ≤
      16 * ((C' + 3) ^ 4 + 12 * b⁻¹ ^ 4 + ((C₀ + 1) / b) ^ 2) * ν⁻¹ ^ 8 := by
  have ht : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have ht0 : 0 ≤ ν⁻¹ := by linarith
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 1 + (C' * ν⁻¹ + 2) := ⟨_, rfl⟩
  have hdiv : C' / ν = C' * ν⁻¹ := div_eq_mul_inv C' ν
  have hx : 1 + (C' / ν + 2 + l) = a + l := by rw [ha, hdiv]; ring
  rw [hx]
  have ha0 : 0 ≤ a := by rw [ha]; nlinarith
  have hl0 : 0 ≤ l := hl
  have ha_le : a ≤ (C' + 3) * ν⁻¹ := by
    rw [ha]; nlinarith
  have ha4 : a ^ 4 ≤ (C' + 3) ^ 4 * ν⁻¹ ^ 4 := by
    calc a ^ 4 ≤ ((C' + 3) * ν⁻¹) ^ 4 := pow_le_pow_left₀ ha0 ha_le 4
      _ = (C' + 3) ^ 4 * ν⁻¹ ^ 4 := by ring
  have ha4t : a ^ 4 ≤ (C' + 3) ^ 4 * ν⁻¹ ^ 8 := by
    have : ν⁻¹ ^ 4 ≤ ν⁻¹ ^ 8 := pow_le_pow_right₀ ht (by norm_num)
    have hC3 : 0 ≤ (C' + 3) ^ 4 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this hC3]
  set E1 := Real.exp (-(b * l / (ν ^ 2)⁻¹)) with hE1
  set E2 := Real.exp (-(b * l ^ 2 / (C₀ + 1))) with hE2
  have hE1le : E1 ≤ 1 := by
    rw [hE1]; apply Real.exp_le_one_iff.2
    have : 0 ≤ b * l / (ν ^ 2)⁻¹ := div_nonneg (mul_nonneg hb.le hl) (inv_nonneg.2 (by positivity))
    linarith
  have hE2le : E2 ≤ 1 := by
    rw [hE2]; apply Real.exp_le_one_iff.2
    have : 0 ≤ b * l ^ 2 / (C₀ + 1) := div_nonneg (mul_nonneg hb.le (sq_nonneg l)) (by linarith)
    linarith
  have hE1nn : 0 ≤ E1 := (Real.exp_pos _).le
  have hE2nn : 0 ≤ E2 := (Real.exp_pos _).le
  have hL1 : l ^ 4 * E1 ≤ 24 * b⁻¹ ^ 4 * ν⁻¹ ^ 8 := tailW_E1 hb hν hl
  have hL2 : l ^ 4 * E2 ≤ ((C₀ + 1) / b) ^ 2 * 2 := tailW_E2 hb hC₀
  have hL2' : ((C₀ + 1) / b) ^ 2 * 2 ≤ ((C₀ + 1) / b) ^ 2 * 2 * ν⁻¹ ^ 8 := by
    have h8 : (1:ℝ) ≤ ν⁻¹ ^ 8 := one_le_pow₀ ht
    have hpos : 0 ≤ ((C₀ + 1) / b) ^ 2 * 2 := by positivity
    nlinarith
  have hadd : (a + l) ^ 4 ≤ 2 ^ (4 - 1) * (a ^ 4 + l ^ 4) := add_pow_le ha0 hl0 4
  have hsum0 : 0 ≤ E1 + E2 := add_nonneg hE1nn hE2nn
  have hstep1 : (a + l) ^ 4 * (E1 + E2) ≤ 2 ^ (4 - 1) * (a ^ 4 + l ^ 4) * (E1 + E2) :=
    mul_le_mul_of_nonneg_right hadd hsum0
  have hAE : a ^ 4 * (E1 + E2) ≤ 2 * ((C' + 3) ^ 4 * ν⁻¹ ^ 8) := by
    have h1 : a ^ 4 * E1 ≤ a ^ 4 := by
      have := mul_le_mul_of_nonneg_left hE1le (by positivity : (0:ℝ) ≤ a ^ 4)
      linarith
    have h2 : a ^ 4 * E2 ≤ a ^ 4 := by
      have := mul_le_mul_of_nonneg_left hE2le (by positivity : (0:ℝ) ≤ a ^ 4)
      linarith
    nlinarith
  have hLE : l ^ 4 * (E1 + E2) ≤ 24 * b⁻¹ ^ 4 * ν⁻¹ ^ 8 + ((C₀ + 1) / b) ^ 2 * 2 * ν⁻¹ ^ 8 := by
    nlinarith
  have hfinal : (a + l) ^ 4 * (E1 + E2) ≤
      16 * ((C' + 3) ^ 4 + 12 * b⁻¹ ^ 4 + ((C₀ + 1) / b) ^ 2) * ν⁻¹ ^ 8 := by
    have e8 : 2 ^ (4 - 1) * (a ^ 4 + l ^ 4) * (E1 + E2) =
        8 * (a ^ 4 * (E1 + E2) + l ^ 4 * (E1 + E2)) := by ring
    rw [e8] at hstep1
    nlinarith
  exact hfinal

/-- **Tail region** (`TrainTransverseTails` with `ρ = 2`): for `|η| ≥ C'/ν + 2`, the weighted jets of
`v, p, ψ` are bounded by `Cν^{-k}` on `0 < s ≤ 1/ν`. -/
theorem tailW_of (hT : UnforcedLeray.Short.PartI.TrainTransverseTails) : TailW := by
  intro ℓ m
  obtain ⟨b, C₀, C', hb, hC₀, hC', C, N, ν₀, hC, hν₀, hT'⟩ := hT 2 (by norm_num) ℓ m
  refine ⟨C', 3 * (C * 6 ^ N) * (16 * ((C' + 3) ^ 4 + 12 * b⁻¹ ^ 4 + ((C₀ + 1) / b) ^ 2)),
    3 * N + 8, min ν₀ 1, hC', lt_min hν₀ one_pos, ?_⟩
  intro ν hν hνle tr htr s hs hsS z hz
  have hν1 : ν ≤ 1 := hνle.trans (min_le_right _ _)
  have hν0 : ν ≤ ν₀ := hνle.trans (min_le_left _ _)
  obtain ⟨tr', htr', hv, hp, hψ⟩ :=
    tailW_transport (c := UnforcedLeray.Short.PartIIIb.Concrete.cOf ν)
      (c' := UnforcedLeray.Short.PartI.trainPeriod 2 ν)
      (by rw [tailW_trainPeriod_two hν]; rfl) tr htr
  obtain ⟨l, hl_def⟩ : ∃ l : ℝ, l = |z.2| - (C' / ν + 2) := ⟨_, rfl⟩
  have hl : 0 ≤ l := by rw [hl_def]; linarith
  have hzl : C' / ν + 2 + l = |z.2| := by rw [hl_def]; ring
  have hS0 : (0:ℝ) ≤ 1 / ν := by positivity
  have H := hT' (1 / ν) hS0 ν hν hν0 tr' htr' l hl s hs hsS z hzl.le
  dsimp only at H
  rw [hv, hp, hψ] at H
  rw [tailW_trainPeriod_two hν] at H
  have hc1 : ν * (1 / ν) = 1 := by field_simp
  rw [hc1] at H
  obtain ⟨Hψ, Hv, _, Hp⟩ := H
  have hP := tailW_poly C N hC.le hν hν1
  have hcore := tailW_core hb hC₀ hC' hν hν1 hl
  have hQ : 0 ≤ C * 6 ^ N * ν⁻¹ ^ (3 * N) :=
    mul_nonneg (mul_nonneg hC.le (by positivity)) (pow_nonneg (inv_nonneg.2 hν.le) _)
  rw [← hzl]
  set P := UnforcedLeray.Short.PartI.polyPS C N ν (ν ^ 2)⁻¹ (1 / ν) with hPdef
  set E := Real.exp (-(b * l / (ν ^ 2)⁻¹)) + Real.exp (-(b * l ^ 2 / (C₀ + 1))) with hEdef
  set Q := C * 6 ^ N * ν⁻¹ ^ (3 * N) with hQdef
  set X := (1 + (C' / ν + 2 + l)) ^ 4 with hXdef
  have hE0 : 0 ≤ E := by rw [hEdef]; positivity
  have hX : 0 ≤ X * E := mul_nonneg (by rw [hXdef]; positivity) hE0
  have hsumle : ‖UnforcedLeray.Short.PartI.ageJet ℓ m tr.v s z‖ + ‖UnforcedLeray.Short.PartI.ageJet ℓ m tr.p s z‖ + ‖UnforcedLeray.Short.PartI.ageJet ℓ m tr.ψ s z‖ ≤ 3 * (P * E) := by linarith
  calc _ ≤ X * (3 * (P * E)) := mul_le_mul_of_nonneg_left hsumle (by rw [hXdef]; positivity)
    _ = 3 * P * (X * E) := by ring
    _ ≤ 3 * Q * (X * E) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP (by norm_num)) hX
    _ ≤ 3 * Q * (16 * ((C' + 3) ^ 4 + 12 * b⁻¹ ^ 4 + ((C₀ + 1) / b) ^ 2) * ν⁻¹ ^ 8) :=
        mul_le_mul_of_nonneg_left hcore (mul_nonneg (by norm_num) hQ)
    _ = 3 * (C * 6 ^ N) * (16 * ((C' + 3) ^ 4 + 12 * b⁻¹ ^ 4 + ((C₀ + 1) / b) ^ 2)) *
          ν⁻¹ ^ (3 * N + 8) := by rw [hQdef]; ring

end UnforcedLeray.Short.PartIIIb.Concrete
