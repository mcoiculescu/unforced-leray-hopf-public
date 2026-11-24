import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c2_2_7

/-!
# Part III-a, task `PartIII-a:T21/c2/2/7/2`: `FmrVelCompSup`

Source of record: `the November 2 reference manuscript` lines 291-303
(`sct:comparison`) and line 2955.  `sct:comparison` (`TrainComparison`, at `ρ = 2`, `j = 0`) gives
the sup-norm bound `‖v - V_c‖_∞ ≤ C ν⁻¹ a^{-5/2} e^{-b₀ c²/a}`.  On `θ(s) ≥ b` one has
`a ≤ 1/(νb)`, hence `c²/a ≥ b ν⁻³`, and the exponential is at most `ε ν /(4C)` once `ν` is small.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Short.IIb
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- Pointwise bound `|f₀| + |f₁| ≤ 2M` from the order-zero sup-norm bound `‖f‖_∞ ≤ M`. -/
theorem fmrVelCompSup_pointwise {f : B0579.Plane → UnforcedLeray.Cyl.Vec2} {M : ℝ}
    (hM : 0 ≤ M) (h : B0277.supNormD 0 f ≤ ENNReal.ofReal M) (x : B0579.Plane) :
    |f x 0| + |f x 1| ≤ 2 * M := by
  have h1 : ‖iteratedFDeriv ℝ 0 f x‖ ≤ M := B0277.norm_le_of_supNormD_le hM h x
  rw [norm_iteratedFDeriv_zero] at h1
  have e0 : |f x 0| ≤ ‖f x‖ := by
    have := PiLp.norm_apply_le (f x) 0
    simpa [Real.norm_eq_abs] using this
  have e1 : |f x 1| ≤ ‖f x‖ := by
    have := PiLp.norm_apply_le (f x) 1
    simpa [Real.norm_eq_abs] using this
  linarith

/-- Exponential smallness on `θ ≥ b`. With `c = ν⁻²`, `a = 1+νs`, `a ≤ c²` and
`exp(-bb c²/a) ≤ ε ν /(4C)`. -/
theorem fmrVelCompSup_exp {ν s b bb C ε : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hνb : ν ≤ b)
    (hb : 0 < b) (hbb : 0 < bb) (hC : 0 < C) (hε : 0 < ε)
    (hνK : ν ≤ ε * (bb * b) / (4 * C))
    (hθ : b ≤ 1 / (ν * (1 + ν * s))) (hs : 0 ≤ s) :
    (1 + ν * s) ≤ (ν ^ (-2 : ℝ)) ^ 2 ∧
      Real.exp (-(bb * (ν ^ (-2 : ℝ)) ^ 2 / (1 + ν * s))) ≤ ε * ν / (4 * C) := by
  have ha : 0 < 1 + ν * s := by have := mul_nonneg hν.le hs; linarith
  have hc : ν ^ (-2 : ℝ) * ν ^ 2 = 1 := by
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hν.le, Real.rpow_natCast]
    field_simp
  -- `c² ν⁴ = 1`
  have hc2 : (ν ^ (-2 : ℝ)) ^ 2 * ν ^ 4 = 1 := by
    have : (ν ^ (-2 : ℝ)) ^ 2 * ν ^ 4 = (ν ^ (-2 : ℝ) * ν ^ 2) ^ 2 := by ring
    rw [this, hc]; norm_num
  have hc2pos : 0 < (ν ^ (-2 : ℝ)) ^ 2 := by
    have : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
    positivity
  -- `ν a b ≤ 1` from `θ ≥ b`
  have hθ' : b * (ν * (1 + ν * s)) ≤ 1 := by
    rwa [le_div_iff₀ (mul_pos hν ha)] at hθ
  -- `a ≤ c²`
  have hW : (1 + ν * s) ≤ (ν ^ (-2 : ℝ)) ^ 2 := by
    -- a ≤ 1/(ν b) ≤ 1/ν⁴ since ν³ ≤ ν ≤ b
    have h3 : ν ^ 3 ≤ b := by
      have : ν ^ 3 ≤ ν := by
        have h2 : ν ^ 2 ≤ 1 := by nlinarith
        nlinarith
      linarith
    have key : (1 + ν * s) * ν ^ 4 ≤ 1 := by
      have h6 : (1 + ν * s) * ν * ν ^ 3 ≤ (1 + ν * s) * ν * b :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      have h7 : (1 + ν * s) * ν ^ 4 = (1 + ν * s) * ν * ν ^ 3 := by ring
      have h8 : (1 + ν * s) * ν * b = ν * (1 + ν * s) * b := by ring
      have h9 : ν * (1 + ν * s) * b ≤ 1 := by
        have : b * (ν * (1 + ν * s)) = ν * (1 + ν * s) * b := by ring
        linarith [hθ']
      linarith
    -- from a ν⁴ ≤ 1 = c² ν⁴ we get a ≤ c²
    have : (1 + ν * s) * ν ^ 4 ≤ (ν ^ (-2 : ℝ)) ^ 2 * ν ^ 4 := by rw [hc2]; exact key
    exact le_of_mul_le_mul_right this (pow_pos hν 4)
  refine ⟨hW, ?_⟩
  -- set `K = bb b`, `y = K/ν³`, `E = exp(-bb c²/a)`
  set K : ℝ := bb * b with hKdef
  have hKpos : 0 < K := mul_pos hbb hb
  have hν3 : 0 < ν ^ 3 := pow_pos hν 3
  have hlow : K / ν ^ 3 ≤ bb * (ν ^ (-2 : ℝ)) ^ 2 / (1 + ν * s) := by
    rw [div_le_div_iff₀ hν3 ha]
    -- K a ν ≤ bb  ⇒  K a ≤ bb c² ν³
    have hKa : K * (1 + ν * s) * ν ≤ bb := by
      have : K * (1 + ν * s) * ν = bb * (b * (ν * (1 + ν * s))) := by rw [hKdef]; ring
      rw [this]
      nlinarith
    have hmul : (bb * (ν ^ (-2 : ℝ)) ^ 2 * ν ^ 3) * ν = bb := by
      have : (bb * (ν ^ (-2 : ℝ)) ^ 2 * ν ^ 3) * ν = bb * ((ν ^ (-2 : ℝ)) ^ 2 * ν ^ 4) := by ring
      rw [this, hc2, mul_one]
    have : K * (1 + ν * s) * ν ≤ (bb * (ν ^ (-2 : ℝ)) ^ 2 * ν ^ 3) * ν := by
      rw [hmul]; exact hKa
    have hνpos : 0 < ν := hν
    have := le_of_mul_le_mul_right this hνpos
    -- goal: K * (1 + ν s) ≤ bb c² * ν³
    linarith [this]
  set y : ℝ := K / ν ^ 3 with hydef
  set E : ℝ := Real.exp (-(bb * (ν ^ (-2 : ℝ)) ^ 2 / (1 + ν * s))) with hEdef
  have hE_le : E ≤ Real.exp (-y) := by
    rw [hEdef]
    exact Real.exp_le_exp.mpr (by linarith [hlow])
  have hEnn : 0 ≤ E := (Real.exp_pos _).le
  -- `exp(-y)(1+y) ≤ 1`
  have hEy : Real.exp (-y) * (1 + y) ≤ 1 := by
    have h1 : 1 + y ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
    have h2 : Real.exp (-y) * (1 + y) ≤ Real.exp (-y) * Real.exp y :=
      mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h2
    exact h2
  have hEy' : E * (ν ^ 3 + K) ≤ ν ^ 3 := by
    have hE' : Real.exp (-y) * (1 + y) ≤ 1 := hEy
    have hEE : E ≤ Real.exp (-y) := hE_le
    have h1 : E * (1 + y) ≤ 1 := le_trans (mul_le_mul_of_nonneg_right hEE (by positivity)) hE'
    have h2 : (E * (1 + y)) * ν ^ 3 ≤ 1 * ν ^ 3 :=
      mul_le_mul_of_nonneg_right h1 hν3.le
    have h3 : (E * (1 + y)) * ν ^ 3 = E * (ν ^ 3 + K) := by
      rw [hydef]; field_simp
    linarith [h2, h3]
  -- `4 C ν² ≤ ε K`
  have h4C : 4 * C * ν ≤ ε * K := by
    have := (le_div_iff₀ (by linarith : (0:ℝ) < 4 * C)).mp hνK
    rw [hKdef]; linarith
  have hq : 4 * C * ν ^ 2 ≤ ε * K := by
    have : ν ^ 2 ≤ ν := by nlinarith
    nlinarith
  -- `E · K ≤ ν³`
  have hEK : E * K ≤ ν ^ 3 := by nlinarith [mul_nonneg hEnn hν3.le]
  rw [le_div_iff₀ (by positivity : (0:ℝ) < 4 * C)]
  -- goal: E * (4 C) ≤ ε ν.  Multiply by K > 0.
  have : (E * (4 * C)) * K ≤ (ε * ν) * K := by
    have h1 : (E * (4 * C)) * K = 4 * C * (E * K) := by ring
    have h2 : 4 * C * (E * K) ≤ 4 * C * ν ^ 3 :=
      mul_le_mul_of_nonneg_left hEK (by linarith)
    have h3 : 4 * C * ν ^ 3 = ν * (4 * C * ν ^ 2) := by ring
    have h4 : ν * (4 * C * ν ^ 2) ≤ ν * (ε * K) :=
      mul_le_mul_of_nonneg_left hq hν.le
    have h5 : ν * (ε * K) = (ε * ν) * K := by ring
    linarith [h1, h2, h3, h4, h5]
  exact le_of_mul_le_mul_right this hKpos

/-- **`FmrVelCompSup`** (SP 291-303, 2955): the comparison `TrainComparison` (at `ρ = 2`, `j = 0`)
gives the pointwise bound on the cell-free plane, on `θ(s) ≥ b`. -/
theorem fmrVelCompSup : FmrVelCompSup := by
  intro hTC b hb ε hε
  obtain ⟨C, bb, ν₀, hC, hbb, hν₀, H⟩ := hTC 2 (by norm_num) 0
  have hK : 0 < ε * (bb * b) / (4 * C) := by
    apply div_pos (mul_pos hε (mul_pos hbb hb)); linarith
  refine ⟨min ν₀ (min 1 (min b (ε * (bb * b) / (4 * C)))),
    lt_min hν₀ (lt_min one_pos (lt_min hb hK)), ?_⟩
  intro ν hν tr htr s hs hθ x
  have hν0 : ν ≤ ν₀ := hν.2.trans (min_le_left _ _)
  have hν1 : ν ≤ 1 := hν.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hνb : ν ≤ b :=
    hν.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hνK : ν ≤ ε * (bb * b) / (4 * C) :=
    hν.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hθ' : b ≤ 1 / (ν * (1 + ν * s)) := by
    simpa [clockTheta, clockA, one_div] using hθ
  obtain ⟨hW, hE⟩ := fmrVelCompSup_exp hν.1 hν1 hνb hb hbb hC hε hνK hθ' hs
  have H0 := (H ν hν.1 hν0 tr htr s hs hW).2
  unfold UnforcedLeray.Short.PartI.trainPeriod UnforcedLeray.Train.width at H0
  simp only [Nat.cast_zero, add_zero] at H0
  have hνs : 0 ≤ ν * s := mul_nonneg hν.1.le hs
  have ha : 0 ≤ 1 + ν * s := by linarith
  have hνne : ν ≠ 0 := hν.1.ne'
  have hCne : C ≠ 0 := hC.ne'
  set E : ℝ := Real.exp (-(bb * (ν ^ (-2 : ℝ)) ^ 2 / (1 + ν * s))) with hEdef
  set X : ℝ := C * ν⁻¹ * (1 + ν * s) ^ (-(5 / 2 : ℝ)) * E with hX
  have hXnn : 0 ≤ X := by
    rw [hX]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC.le (inv_nonneg.mpr hν.1.le))
      (Real.rpow_nonneg ha _)) (Real.exp_pos _).le
  have hp := fmrVelCompSup_pointwise (f := fun z => tr.v s z - UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) s z)
    hXnn H0 x
  simp only [PiLp.sub_apply] at hp
  unfold clockA
  have hpow : (1 + ν * s) ^ (-(5 / 2 : ℝ)) ≤ (1 + ν * s) ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hPnn : 0 ≤ (1 + ν * s) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg ha _
  have step1 : (1 + ν * s) ^ (-(5 / 2 : ℝ)) * E ≤
      (1 + ν * s) ^ (-(3 / 2 : ℝ)) * (ε * ν / (4 * C)) :=
    mul_le_mul hpow hE (Real.exp_pos _).le hPnn
  have hK2 : 0 ≤ 2 * C * ν⁻¹ := by
    have := inv_nonneg.mpr hν.1.le
    positivity
  have step2 := mul_le_mul_of_nonneg_left step1 hK2
  have eq : 2 * C * ν⁻¹ * ((1 + ν * s) ^ (-(3 / 2 : ℝ)) * (ε * ν / (4 * C))) =
      ε / 2 * (1 + ν * s) ^ (-(3 / 2 : ℝ)) := by
    field_simp
    ring
  have hX2 : 2 * X = 2 * C * ν⁻¹ * ((1 + ν * s) ^ (-(5 / 2 : ℝ)) * E) := by
    rw [hX]; ring
  linarith [hp, hX2, step2, eq]

end UnforcedLeray.Short.IIIa
