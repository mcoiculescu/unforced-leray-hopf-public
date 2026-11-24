import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Cross.Pair

/-!
# `PartIII-b:C/asrc/ra/8/2/org` : the separated pair bound

Source `the November 2 reference manuscript`
5029-5031 (the Gaussian factor of the cross-center cells), 4371 (`δ_base`).  For `k ≠ j`,
`x_j - x_k = ((k-j)c, 0)`, so `(q-jc)² + (q-kc)² ≥ (k-j)²c²/2 ≥ c²/2` for every `q` (in particular
on the centred cell `|q| ≤ c/2` of `Cyl.avgμ c`).  Split
`(|x_j|²+|x_k|²)/(4a) = |x_j|²/(16a) + |x_k|²/(16a) + |x_j|²/(8a) + |x_k|²/(8a) + (|x_j|²+|x_k|²)/(16a)`:
the first two absorb the polynomial (`(1+S)³e^{-S/(16a)} ≤ 943300`, `a ≤ 2.1`), the next two give
the lattice weights `e^{-(q-jc)²/(8a)}`, and the last gives `e^{-c²/(32a)} e^{-η²/(8a)}
≤ e^{-c²/135} e^{-η²/34}`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `(1+S)³ e^{-S/(16a)} ≤ 943300` for `S ≥ 0`, `1 ≤ a ≤ 2.1`. -/
theorem rc_poly_absorb (S a : ℝ) (hS : 0 ≤ S) (ha1 : 1 ≤ a) (ha2 : a ≤ 21 / 10) :
    (1 + S) ^ 3 * Real.exp (-S / (16 * a)) ≤ 943300 := by
  have ha0 : 0 < 16 * a := by linarith
  set t := S / (16 * a) with htdef
  have ht0 : 0 ≤ t := div_nonneg hS ha0.le
  have hSt : S ≤ 34 * t := by
    have e : S = 16 * a * t := by rw [htdef]; field_simp
    rw [e]
    nlinarith
  have h3 : t ^ 3 / 6 ≤ Real.exp t := by
    have := Real.pow_div_factorial_le_exp (x := t) ht0 3
    simpa [Nat.factorial] using this
  have h1 : 1 ≤ Real.exp t := Real.one_le_exp ht0
  have hpoly : (1 + S) ^ 3 ≤ 4 * (1 + S ^ 3) := by
    nlinarith [mul_nonneg (sq_nonneg (1 - S)) (by linarith : (0 : ℝ) ≤ 1 + S)]
  have hS3 : S ^ 3 ≤ (34 * t) ^ 3 := pow_le_pow_left₀ hS hSt 3
  have hbig : (1 + S) ^ 3 ≤ 943300 * Real.exp t := by nlinarith
  have hneg : -S / (16 * a) = -t := by rw [htdef, neg_div]
  rw [hneg]
  have hpos : 0 < Real.exp (-t) := Real.exp_pos _
  calc (1 + S) ^ 3 * Real.exp (-t) ≤ 943300 * Real.exp t * Real.exp (-t) :=
        mul_le_mul_of_nonneg_right hbig hpos.le
    _ = 943300 := by rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

theorem rcPairSeparated : RcPairSeparated := by
  obtain ⟨C0, hC0, hP⟩ := rcPairPointwise
  refine ⟨C0 * 943300 ^ 2, by positivity, ?_⟩
  intro ν s B j k x hν hν1 hs hsT hkj
  have ha1 : 1 ≤ ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  have ha2 : ageA ν s ≤ 21 / 10 := by
    unfold ageA
    have : ν * s ≤ 11 / 10 := by rw [le_div_iff₀ hν] at hsT; linarith
    linarith
  set a := ageA ν s with hadef
  have ha0 : 0 < a := by linarith
  set c := cOf ν with hcdef
  set uj := x.1 - j * c with hujdef
  set uk := x.1 - k * c with hukdef
  set Sj := sq2 (xj ν j x) with hSjdef
  set Sk := sq2 (xj ν k x) with hSkdef
  have hSj : Sj = uj ^ 2 + x.2 ^ 2 := rfl
  have hSk : Sk = uk ^ 2 + x.2 ^ 2 := rfl
  have hSj0 : 0 ≤ Sj := by rw [hSj]; positivity
  have hSk0 : 0 ≤ Sk := by rw [hSk]; positivity
  set F := frob B with hFdef
  have hF0 : 0 ≤ F := Real.sqrt_nonneg _
  -- separation of the centers
  have hkj1 : (1 : ℝ) ≤ ((k : ℝ) - j) ^ 2 := by
    have h : (1 : ℤ) ≤ |k - j| := Int.one_le_abs (sub_ne_zero.mpr hkj)
    have h' : (1 : ℝ) ≤ |(k : ℝ) - j| := by exact_mod_cast h
    nlinarith [sq_abs ((k : ℝ) - j), abs_nonneg ((k : ℝ) - j)]
  have hsep : c ^ 2 / 2 ≤ uj ^ 2 + uk ^ 2 := by
    have e : uj - uk = ((k : ℝ) - j) * c := by rw [hujdef, hukdef]; ring
    have h2 : c ^ 2 ≤ (uj - uk) ^ 2 := by
      rw [e, mul_pow]
      nlinarith [sq_nonneg c]
    nlinarith [sq_nonneg (uj + uk)]
  -- the exponent split
  have hsplit : Real.exp (-(Sj + Sk) / (4 * a)) =
      Real.exp (-Sj / (16 * a)) * Real.exp (-Sk / (16 * a)) *
        (Real.exp (-Sj / (8 * a)) * Real.exp (-Sk / (8 * a))) *
          Real.exp (-(Sj + Sk) / (16 * a)) := by
    simp only [← Real.exp_add]
    congr 1
    field_simp
    ring
  have hwj : Real.exp (-Sj / (8 * a)) ≤ rcW ν s j x := by
    unfold rcW
    apply Real.exp_le_exp.mpr
    rw [hSj]
    apply div_le_div_of_nonneg_right _ (by linarith)
    nlinarith [sq_nonneg x.2]
  have hwk : Real.exp (-Sk / (8 * a)) ≤ rcW ν s k x := by
    unfold rcW
    apply Real.exp_le_exp.mpr
    rw [hSk]
    apply div_le_div_of_nonneg_right _ (by linarith)
    nlinarith [sq_nonneg x.2]
  have hce : Real.exp (-(Sj + Sk) / (16 * a)) ≤
      Real.exp (-(c ^ 2) / 135) * Real.exp (-(x.2 ^ 2) / 34) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have key : (c ^ 2 / 135 + x.2 ^ 2 / 34) * (16 * a) ≤ Sj + Sk := by
      rw [hSj, hSk]
      have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
      have he2 : 0 ≤ x.2 ^ 2 := sq_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left ha2 hc2, mul_le_mul_of_nonneg_left ha2 he2]
    have h16 : 0 < 16 * a := by linarith
    have : c ^ 2 / 135 + x.2 ^ 2 / 34 ≤ (Sj + Sk) / (16 * a) := by
      rw [le_div_iff₀ h16]; exact key
    have e1 : -(Sj + Sk) / (16 * a) = -((Sj + Sk) / (16 * a)) := by ring
    have e2 : -(c ^ 2) / 135 + -(x.2 ^ 2) / 34 = -(c ^ 2 / 135 + x.2 ^ 2 / 34) := by ring
    rw [e1, e2]
    linarith
  have hpj := rc_poly_absorb Sj a hSj0 ha1 ha2
  have hpk := rc_poly_absorb Sk a hSk0 ha1 ha2
  have hP' := hP ν s B j k x hν hν1 hs hsT
  rw [hsplit] at hP'
  -- nonnegativity
  have hA0 : 0 ≤ (1 + Sj) ^ 3 * Real.exp (-Sj / (16 * a)) := by positivity
  have hB0 : 0 ≤ (1 + Sk) ^ 3 * Real.exp (-Sk / (16 * a)) := by positivity
  have hW0 : 0 ≤ Real.exp (-Sj / (8 * a)) * Real.exp (-Sk / (8 * a)) := by positivity
  have hT0 : 0 ≤ Real.exp (-(Sj + Sk) / (16 * a)) := (Real.exp_pos _).le
  have hrw0 : 0 ≤ rcW ν s k x := (Real.exp_pos _).le
  have hAB : (1 + Sj) ^ 3 * Real.exp (-Sj / (16 * a)) *
      ((1 + Sk) ^ 3 * Real.exp (-Sk / (16 * a))) ≤ 943300 * 943300 :=
    mul_le_mul hpj hpk hB0 (by norm_num)
  have hWW : Real.exp (-Sj / (8 * a)) * Real.exp (-Sk / (8 * a)) ≤ rcW ν s j x * rcW ν s k x :=
    mul_le_mul hwj hwk (Real.exp_pos _).le ((Real.exp_pos _).le.trans hwj)
  have hX : (1 + Sj) ^ 3 * Real.exp (-Sj / (16 * a)) *
      ((1 + Sk) ^ 3 * Real.exp (-Sk / (16 * a))) *
      (Real.exp (-Sj / (8 * a)) * Real.exp (-Sk / (8 * a))) *
      Real.exp (-(Sj + Sk) / (16 * a)) ≤
      943300 * 943300 * (rcW ν s j x * rcW ν s k x) *
        (Real.exp (-(c ^ 2) / 135) * Real.exp (-(x.2 ^ 2) / 34)) := by
    have hrw0j : 0 ≤ rcW ν s j x := (Real.exp_pos _).le
    apply mul_le_mul (mul_le_mul hAB hWW hW0 (by norm_num)) hce hT0
      (mul_nonneg (by norm_num) (mul_nonneg hrw0j hrw0))
  have hCF : 0 ≤ C0 * F := mul_nonneg hC0 hF0
  calc ‖rcPair ν s B j k x‖
      ≤ C0 * F * ((1 + Sj) ^ 3 * (1 + Sk) ^ 3) *
          (Real.exp (-Sj / (16 * a)) * Real.exp (-Sk / (16 * a)) *
            (Real.exp (-Sj / (8 * a)) * Real.exp (-Sk / (8 * a))) *
              Real.exp (-(Sj + Sk) / (16 * a))) := hP'
    _ = C0 * F * ((1 + Sj) ^ 3 * Real.exp (-Sj / (16 * a)) *
          ((1 + Sk) ^ 3 * Real.exp (-Sk / (16 * a))) *
          (Real.exp (-Sj / (8 * a)) * Real.exp (-Sk / (8 * a))) *
          Real.exp (-(Sj + Sk) / (16 * a))) := by ring
    _ ≤ C0 * F * (943300 * 943300 * (rcW ν s j x * rcW ν s k x) *
          (Real.exp (-(c ^ 2) / 135) * Real.exp (-(x.2 ^ 2) / 34))) :=
        mul_le_mul_of_nonneg_left hX hCF
    _ = C0 * 943300 ^ 2 * F * Real.exp (-(c ^ 2) / 135) * Real.exp (-(x.2 ^ 2) / 34) *
          (rcW ν s j x * rcW ν s k x) := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
