import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.PtWOrg

/-!
# `PartIII-b:C/rep/8/2/3/3/1`: the weighted transverse tails `TailWW` for every weight `w`

Source of record: `the November 2 reference manuscript` 460-467 (Part I
`sct:transverse`, `PartI.TrainTransverseTails`), with `ρ = 2`, so `trainPeriod 2 ν = (ν²)⁻¹ = cOf ν`.
This is the proof of `tailW_of` (weight `(1+|η|)^4`) with the weight `(1+|η|)^w`.  The polynomial
`P_S` is bounded as in `tailW_poly`; the exponential moments are bounded for every `w`:
`y^w e^{-y} ≤ w!` (`Real.pow_div_factorial_le_exp`), with `y = bν²l` for the first term and
`l² ≥ 2l - 1` (so `e^{-βl²} ≤ e^β e^{-2βl}`) for the second.  The exponent of `ν⁻¹` is `3N + 2w`.
Helper declarations carry a name ending in `W`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cyl (Plane)

/-- Transport of a BUC train along an equality of periods (`v, p, ψ` are kept). -/
theorem tailWW_transportW {ν c c' : ℝ} (h : c = c')
    (tr : UnforcedLeray.B0140.TrainSol ν c)
    (hb : UnforcedLeray.Short.PartI.IsBUCTrain tr) :
    ∃ tr' : UnforcedLeray.B0140.TrainSol ν c',
      UnforcedLeray.Short.PartI.IsBUCTrain tr' ∧ tr'.v = tr.v ∧ tr'.p = tr.p ∧ tr'.ψ = tr.ψ := by
  subst h
  exact ⟨tr, hb, rfl, rfl, rfl⟩

/-- `trainPeriod 2 ν = (ν²)⁻¹`. -/
theorem tailWW_trainPeriodW {ν : ℝ} (hν : 0 < ν) :
    UnforcedLeray.Short.PartI.trainPeriod 2 ν = (ν ^ 2)⁻¹ := by
  unfold UnforcedLeray.Short.PartI.trainPeriod
  rw [Real.rpow_neg hν.le, Real.rpow_two]

/-- Pure arithmetic in `t ≥ 1`: `C((1+t²+t)(1+t))^N ≤ C 6^N t^{3N}`. -/
theorem tailWW_poly_arithW (C : ℝ) (N : ℕ) (hC : 0 ≤ C) {t : ℝ} (ht : 1 ≤ t) :
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
theorem tailWW_polyW {ν : ℝ} (C : ℝ) (N : ℕ) (hC : 0 ≤ C) (hν : 0 < ν) (hν1 : ν ≤ 1) :
    UnforcedLeray.Short.PartI.polyPS C N ν (ν ^ 2)⁻¹ (1 / ν) ≤ C * 6 ^ N * ν⁻¹ ^ (3 * N) := by
  have ht : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have e : UnforcedLeray.Short.PartI.polyPS C N ν (ν ^ 2)⁻¹ (1 / ν) =
      C * ((1 + ν⁻¹ ^ 2 + ν⁻¹) * (1 + ν⁻¹)) ^ N := by
    unfold UnforcedLeray.Short.PartI.polyPS
    rw [← inv_pow, one_div]
  rw [e]
  exact tailWW_poly_arithW C N hC ht

/-- `y^w e^{-y} ≤ w!` for `y ≥ 0`. -/
theorem tailWW_powExpW (w : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    y ^ w * Real.exp (-y) ≤ (w.factorial : ℝ) := by
  have h := Real.pow_div_factorial_le_exp y hy w
  have hf : (0 : ℝ) < (w.factorial : ℝ) := Nat.cast_pos.2 (Nat.factorial_pos w)
  have h' : y ^ w ≤ Real.exp y * (w.factorial : ℝ) := (div_le_iff₀ hf).1 h
  have hexp : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
  have hpos : 0 < Real.exp (-y) := Real.exp_pos _
  calc y ^ w * Real.exp (-y) ≤ (Real.exp y * (w.factorial : ℝ)) * Real.exp (-y) :=
        mul_le_mul_of_nonneg_right h' hpos.le
    _ = (Real.exp y * Real.exp (-y)) * (w.factorial : ℝ) := by ring
    _ = (w.factorial : ℝ) := by rw [hexp, one_mul]

/-- The `E₁` term: `l^w e^{-b l/(ν²)⁻¹} ≤ w! (b^w)⁻¹ ν⁻¹^{2w}`. -/
theorem tailWW_E1W {b ν l : ℝ} (w : ℕ) (hb : 0 < b) (hν : 0 < ν) (hl : 0 ≤ l) :
    l ^ w * Real.exp (-(b * l / (ν ^ 2)⁻¹)) ≤ (w.factorial : ℝ) * (b ^ w)⁻¹ * ν⁻¹ ^ (2 * w) := by
  have e : b * l / (ν ^ 2)⁻¹ = b * ν ^ 2 * l := by rw [div_inv_eq_mul]; ring
  rw [e]
  have hy : 0 ≤ b * ν ^ 2 * l := by positivity
  have h1 := tailWW_powExpW w hy
  have hP : 0 < b ^ w * ν ^ (2 * w) := by positivity
  have hyw : (b * ν ^ 2 * l) ^ w = (b ^ w * ν ^ (2 * w)) * l ^ w := by
    rw [mul_pow, mul_pow, pow_mul]
  have hT : (w.factorial : ℝ) * (b ^ w)⁻¹ * ν⁻¹ ^ (2 * w) =
      (w.factorial : ℝ) / (b ^ w * ν ^ (2 * w)) := by
    rw [inv_pow]; field_simp
  rw [hT, le_div_iff₀ hP]
  have key : l ^ w * Real.exp (-(b * ν ^ 2 * l)) * (b ^ w * ν ^ (2 * w)) =
      (b * ν ^ 2 * l) ^ w * Real.exp (-(b * ν ^ 2 * l)) := by rw [hyw]; ring
  rw [key]
  exact h1

/-- The `E₂` term: `l^w e^{-β l²} ≤ e^β w! (2β)^{-w}` for `β > 0`. -/
theorem tailWW_E2W {β l : ℝ} (w : ℕ) (hβ : 0 < β) (hl : 0 ≤ l) :
    l ^ w * Real.exp (-(β * l ^ 2)) ≤ Real.exp β * (w.factorial : ℝ) * ((2 * β) ^ w)⁻¹ := by
  have hq : -(β * l ^ 2) ≤ β + -(2 * β * l) := by
    nlinarith [mul_nonneg hβ.le (sq_nonneg (l - 1))]
  have hexp : Real.exp (-(β * l ^ 2)) ≤ Real.exp β * Real.exp (-(2 * β * l)) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 hq
  have hpow : l ^ w * Real.exp (-(2 * β * l)) ≤ (w.factorial : ℝ) * ((2 * β) ^ w)⁻¹ := by
    have h := tailWW_powExpW w (y := 2 * β * l) (by positivity)
    have hP : 0 < (2 * β) ^ w := by positivity
    have hyw : (2 * β * l) ^ w = (2 * β) ^ w * l ^ w := by rw [mul_pow]
    rw [← div_eq_mul_inv, le_div_iff₀ hP]
    have key : l ^ w * Real.exp (-(2 * β * l)) * (2 * β) ^ w =
        (2 * β * l) ^ w * Real.exp (-(2 * β * l)) := by rw [hyw]; ring
    rw [key]
    exact h
  calc l ^ w * Real.exp (-(β * l ^ 2)) ≤ l ^ w * (Real.exp β * Real.exp (-(2 * β * l))) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = Real.exp β * (l ^ w * Real.exp (-(2 * β * l))) := by ring
    _ ≤ Real.exp β * ((w.factorial : ℝ) * ((2 * β) ^ w)⁻¹) :=
        mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
    _ = Real.exp β * (w.factorial : ℝ) * ((2 * β) ^ w)⁻¹ := by ring

/-- The core: `(1+x)^w (E₁+E₂) ≤ D ν⁻¹^{2w}` with `x = C'/ν + 2 + l`, `t = ν⁻¹`. -/
theorem tailWW_coreW {b C₀ C' ν l : ℝ} (w : ℕ) (hb : 0 < b) (hC₀ : 0 < C₀) (hC' : 0 < C')
    (hν : 0 < ν) (hν1 : ν ≤ 1) (hl : 0 ≤ l) :
    (1 + (C' / ν + 2 + l)) ^ w *
        (Real.exp (-(b * l / (ν ^ 2)⁻¹)) + Real.exp (-(b * l ^ 2 / (C₀ + 1)))) ≤
      (2 : ℝ) ^ (w - 1) * (2 * (C' + 3) ^ w + (w.factorial : ℝ) * (b ^ w)⁻¹ +
        Real.exp (b / (C₀ + 1)) * (w.factorial : ℝ) * ((2 * (b / (C₀ + 1))) ^ w)⁻¹) *
          ν⁻¹ ^ (2 * w) := by
  have ht : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have ht0 : 0 ≤ ν⁻¹ := by linarith
  have hβ : 0 < b / (C₀ + 1) := div_pos hb (by linarith)
  have e2 : b * l ^ 2 / (C₀ + 1) = b / (C₀ + 1) * l ^ 2 := by ring
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 1 + (C' * ν⁻¹ + 2) := ⟨_, rfl⟩
  have hdiv : C' / ν = C' * ν⁻¹ := div_eq_mul_inv C' ν
  have hx : 1 + (C' / ν + 2 + l) = a + l := by rw [ha, hdiv]; ring
  rw [hx]
  have ha0 : 0 ≤ a := by rw [ha]; nlinarith
  have ha_le : a ≤ (C' + 3) * ν⁻¹ := by rw [ha]; nlinarith
  have hC3 : 0 ≤ (C' + 3) ^ w := by positivity
  have haw : a ^ w ≤ (C' + 3) ^ w * ν⁻¹ ^ (2 * w) := by
    have h1 : a ^ w ≤ ((C' + 3) * ν⁻¹) ^ w := pow_le_pow_left₀ ha0 ha_le w
    have h3 : ν⁻¹ ^ w ≤ ν⁻¹ ^ (2 * w) := pow_le_pow_right₀ ht (by omega)
    calc a ^ w ≤ ((C' + 3) * ν⁻¹) ^ w := h1
      _ = (C' + 3) ^ w * ν⁻¹ ^ w := mul_pow _ _ _
      _ ≤ (C' + 3) ^ w * ν⁻¹ ^ (2 * w) := mul_le_mul_of_nonneg_left h3 hC3
  have hE1le : Real.exp (-(b * l / (ν ^ 2)⁻¹)) ≤ 1 := by
    apply Real.exp_le_one_iff.2
    have : 0 ≤ b * l / (ν ^ 2)⁻¹ := div_nonneg (mul_nonneg hb.le hl) (inv_nonneg.2 (by positivity))
    linarith
  have hE2le : Real.exp (-(b * l ^ 2 / (C₀ + 1))) ≤ 1 := by
    apply Real.exp_le_one_iff.2
    have : 0 ≤ b * l ^ 2 / (C₀ + 1) := div_nonneg (mul_nonneg hb.le (sq_nonneg l)) (by linarith)
    linarith
  have hE1nn : 0 ≤ Real.exp (-(b * l / (ν ^ 2)⁻¹)) := (Real.exp_pos _).le
  have hE2nn : 0 ≤ Real.exp (-(b * l ^ 2 / (C₀ + 1))) := (Real.exp_pos _).le
  have hL1 : l ^ w * Real.exp (-(b * l / (ν ^ 2)⁻¹)) ≤
      (w.factorial : ℝ) * (b ^ w)⁻¹ * ν⁻¹ ^ (2 * w) := tailWW_E1W w hb hν hl
  have hK2nn : 0 ≤ Real.exp (b / (C₀ + 1)) * (w.factorial : ℝ) * ((2 * (b / (C₀ + 1))) ^ w)⁻¹ := by
    positivity
  have hK2X : Real.exp (b / (C₀ + 1)) * (w.factorial : ℝ) * ((2 * (b / (C₀ + 1))) ^ w)⁻¹ ≤
      Real.exp (b / (C₀ + 1)) * (w.factorial : ℝ) * ((2 * (b / (C₀ + 1))) ^ w)⁻¹ *
        ν⁻¹ ^ (2 * w) :=
    le_mul_of_one_le_right hK2nn (one_le_pow₀ ht)
  have hL2 : l ^ w * Real.exp (-(b * l ^ 2 / (C₀ + 1))) ≤
      Real.exp (b / (C₀ + 1)) * (w.factorial : ℝ) * ((2 * (b / (C₀ + 1))) ^ w)⁻¹ := by
    rw [e2]; exact tailWW_E2W w hβ hl
  have hLsum : l ^ w * (Real.exp (-(b * l / (ν ^ 2)⁻¹)) + Real.exp (-(b * l ^ 2 / (C₀ + 1)))) ≤
      ((w.factorial : ℝ) * (b ^ w)⁻¹ + Real.exp (b / (C₀ + 1)) * (w.factorial : ℝ) *
        ((2 * (b / (C₀ + 1))) ^ w)⁻¹) * ν⁻¹ ^ (2 * w) := by
    calc l ^ w * (Real.exp (-(b * l / (ν ^ 2)⁻¹)) + Real.exp (-(b * l ^ 2 / (C₀ + 1))))
        = l ^ w * Real.exp (-(b * l / (ν ^ 2)⁻¹)) +
            l ^ w * Real.exp (-(b * l ^ 2 / (C₀ + 1))) := by ring
      _ ≤ (w.factorial : ℝ) * (b ^ w)⁻¹ * ν⁻¹ ^ (2 * w) +
            Real.exp (b / (C₀ + 1)) * (w.factorial : ℝ) * ((2 * (b / (C₀ + 1))) ^ w)⁻¹ *
              ν⁻¹ ^ (2 * w) :=
          add_le_add hL1 (hL2.trans hK2X)
      _ = ((w.factorial : ℝ) * (b ^ w)⁻¹ + Real.exp (b / (C₀ + 1)) * (w.factorial : ℝ) *
            ((2 * (b / (C₀ + 1))) ^ w)⁻¹) * ν⁻¹ ^ (2 * w) := by ring
  have hadd : (a + l) ^ w ≤ 2 ^ (w - 1) * (a ^ w + l ^ w) := add_pow_le ha0 hl w
  have hsum0 : 0 ≤ Real.exp (-(b * l / (ν ^ 2)⁻¹)) + Real.exp (-(b * l ^ 2 / (C₀ + 1))) :=
    add_nonneg hE1nn hE2nn
  have hA1 : a ^ w * Real.exp (-(b * l / (ν ^ 2)⁻¹)) ≤ a ^ w :=
    mul_le_of_le_one_right (by positivity) hE1le
  have hA2 : a ^ w * Real.exp (-(b * l ^ 2 / (C₀ + 1))) ≤ a ^ w :=
    mul_le_of_le_one_right (by positivity) hE2le
  have hAB : a ^ w ≤ (C' + 3) ^ w * ν⁻¹ ^ (2 * w) := haw
  have hAE : a ^ w * (Real.exp (-(b * l / (ν ^ 2)⁻¹)) + Real.exp (-(b * l ^ 2 / (C₀ + 1)))) ≤
      2 * ((C' + 3) ^ w * ν⁻¹ ^ (2 * w)) := by
    rw [mul_add]; linarith
  have hmid : a ^ w * (Real.exp (-(b * l / (ν ^ 2)⁻¹)) + Real.exp (-(b * l ^ 2 / (C₀ + 1)))) +
      l ^ w * (Real.exp (-(b * l / (ν ^ 2)⁻¹)) + Real.exp (-(b * l ^ 2 / (C₀ + 1)))) ≤
      (2 * (C' + 3) ^ w + (w.factorial : ℝ) * (b ^ w)⁻¹ + Real.exp (b / (C₀ + 1)) *
        (w.factorial : ℝ) * ((2 * (b / (C₀ + 1))) ^ w)⁻¹) * ν⁻¹ ^ (2 * w) := by
    calc _ ≤ 2 * ((C' + 3) ^ w * ν⁻¹ ^ (2 * w)) + ((w.factorial : ℝ) * (b ^ w)⁻¹ +
            Real.exp (b / (C₀ + 1)) * (w.factorial : ℝ) * ((2 * (b / (C₀ + 1))) ^ w)⁻¹) *
              ν⁻¹ ^ (2 * w) := add_le_add hAE hLsum
      _ = _ := by ring
  calc (a + l) ^ w * (Real.exp (-(b * l / (ν ^ 2)⁻¹)) + Real.exp (-(b * l ^ 2 / (C₀ + 1)))) ≤
        2 ^ (w - 1) * (a ^ w + l ^ w) *
          (Real.exp (-(b * l / (ν ^ 2)⁻¹)) + Real.exp (-(b * l ^ 2 / (C₀ + 1)))) :=
        mul_le_mul_of_nonneg_right hadd hsum0
    _ = 2 ^ (w - 1) * (a ^ w * (Real.exp (-(b * l / (ν ^ 2)⁻¹)) + Real.exp (-(b * l ^ 2 / (C₀ + 1)))) +
          l ^ w * (Real.exp (-(b * l / (ν ^ 2)⁻¹)) + Real.exp (-(b * l ^ 2 / (C₀ + 1))))) := by ring
    _ ≤ 2 ^ (w - 1) * ((2 * (C' + 3) ^ w + (w.factorial : ℝ) * (b ^ w)⁻¹ +
          Real.exp (b / (C₀ + 1)) * (w.factorial : ℝ) * ((2 * (b / (C₀ + 1))) ^ w)⁻¹) *
            ν⁻¹ ^ (2 * w)) := mul_le_mul_of_nonneg_left hmid (by positivity)
    _ = _ := by ring

/-- **Weighted tails, every weight** (`TailWW`; Part I `sct:transverse`, source 460-467).  The proof of
`tailW_of` with the weight `(1+|η|)^w`; the exponent of `ν⁻¹` is `3N + 2w`. -/
theorem tailWW_of (hT : UnforcedLeray.Short.PartI.TrainTransverseTails) : TailWW := by
  intro w ℓ m
  obtain ⟨b, C₀, C', hb, hC₀, hC', C, N, ν₀, hC, hν₀, hT'⟩ := hT 2 (by norm_num) ℓ m
  refine ⟨C', 3 * (C * 6 ^ N) * ((2 : ℝ) ^ (w - 1) * (2 * (C' + 3) ^ w +
    (w.factorial : ℝ) * (b ^ w)⁻¹ + Real.exp (b / (C₀ + 1)) * (w.factorial : ℝ) *
      ((2 * (b / (C₀ + 1))) ^ w)⁻¹)), 3 * N + 2 * w, min ν₀ 1, hC', lt_min hν₀ one_pos, ?_⟩
  intro ν hν hνle tr htr s hs hsS z hz
  have hν1 : ν ≤ 1 := hνle.trans (min_le_right _ _)
  have hν0 : ν ≤ ν₀ := hνle.trans (min_le_left _ _)
  obtain ⟨tr', htr', hv, hp, hψ⟩ :=
    tailWW_transportW (c := UnforcedLeray.Short.PartIIIb.Concrete.cOf ν)
      (c' := UnforcedLeray.Short.PartI.trainPeriod 2 ν)
      (by rw [tailWW_trainPeriodW hν]; rfl) tr htr
  obtain ⟨l, hl_def⟩ : ∃ l : ℝ, l = |z.2| - (C' / ν + 2) := ⟨_, rfl⟩
  have hl : 0 ≤ l := by rw [hl_def]; linarith
  have hzl : C' / ν + 2 + l = |z.2| := by rw [hl_def]; ring
  have hS0 : (0:ℝ) ≤ 1 / ν := by positivity
  have H := hT' (1 / ν) hS0 ν hν hν0 tr' htr' l hl s hs hsS z hzl.le
  dsimp only at H
  rw [hv, hp, hψ] at H
  rw [tailWW_trainPeriodW hν] at H
  have hc1 : ν * (1 / ν) = 1 := by field_simp
  rw [hc1] at H
  obtain ⟨Hψ, Hv, _, Hp⟩ := H
  have hP := tailWW_polyW C N hC.le hν hν1
  have hcore := tailWW_coreW w hb hC₀ hC' hν hν1 hl
  have hQ : 0 ≤ C * 6 ^ N * ν⁻¹ ^ (3 * N) :=
    mul_nonneg (mul_nonneg hC.le (by positivity)) (pow_nonneg (inv_nonneg.2 hν.le) _)
  rw [← hzl]
  set P := UnforcedLeray.Short.PartI.polyPS C N ν (ν ^ 2)⁻¹ (1 / ν) with hPdef
  set E := Real.exp (-(b * l / (ν ^ 2)⁻¹)) + Real.exp (-(b * l ^ 2 / (C₀ + 1))) with hEdef
  set Q := C * 6 ^ N * ν⁻¹ ^ (3 * N) with hQdef
  set X := (1 + (C' / ν + 2 + l)) ^ w with hXdef
  have hE0 : 0 ≤ E := by rw [hEdef]; positivity
  have hX : 0 ≤ X * E := mul_nonneg (by rw [hXdef]; positivity) hE0
  have hsumle : ‖UnforcedLeray.Short.PartI.ageJet ℓ m tr.v s z‖ +
      ‖UnforcedLeray.Short.PartI.ageJet ℓ m tr.p s z‖ +
      ‖UnforcedLeray.Short.PartI.ageJet ℓ m tr.ψ s z‖ ≤ 3 * (P * E) := by linarith
  calc _ ≤ X * (3 * (P * E)) := mul_le_mul_of_nonneg_left hsumle (by rw [hXdef]; positivity)
    _ = 3 * P * (X * E) := by ring
    _ ≤ 3 * Q * (X * E) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP (by norm_num)) hX
    _ ≤ 3 * Q * ((2 : ℝ) ^ (w - 1) * (2 * (C' + 3) ^ w +
          (w.factorial : ℝ) * (b ^ w)⁻¹ + Real.exp (b / (C₀ + 1)) * (w.factorial : ℝ) *
            ((2 * (b / (C₀ + 1))) ^ w)⁻¹) * ν⁻¹ ^ (2 * w)) :=
        mul_le_mul_of_nonneg_left hcore (mul_nonneg (by norm_num) hQ)
    _ = 3 * (C * 6 ^ N) * ((2 : ℝ) ^ (w - 1) * (2 * (C' + 3) ^ w +
          (w.factorial : ℝ) * (b ^ w)⁻¹ + Real.exp (b / (C₀ + 1)) * (w.factorial : ℝ) *
            ((2 * (b / (C₀ + 1))) ^ w)⁻¹)) * ν⁻¹ ^ (3 * N + 2 * w) := by
        rw [hQdef]; ring

end UnforcedLeray.Short.PartIIIb.Concrete
