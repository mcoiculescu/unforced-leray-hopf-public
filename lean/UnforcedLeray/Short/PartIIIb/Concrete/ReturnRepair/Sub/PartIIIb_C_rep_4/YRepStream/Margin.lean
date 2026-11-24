import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateEarly
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.EpsForm

/-!
# `PartIII-b:C/rep/4/4/1/org` (c): the repair-source margins and the two repair leaves

Source `the November 2 reference manuscript` 5318-5341 (gains, table, factors),
5362-5372 (margins), 5607 (`ω_b = kbd₀`), 5617 (`δ_G = P_νe^{-(19γ/66-ω_b-3m₀/2)/ν}`), 5936-5940
(`ε_n = C_*ν_n^re^{-(γ/3)/ν_n}`), 5118 (`|N_ν| = e^{γ/ν}ν^{-Re κ}`).

All proved:

* `yr_retEps_rpow_le`: `ε^p ≤ P_νe^{-p(γ/3)/ν}` for every real `p` (`d₀ = γ/3`; with `p = -k₀b`
  this is `S^{k₀} ≤ P_νe^{k₀bd₀/ν}`); `yr_gaugeN_pe`: `|N_ν| ≤ ν^{-⌈Re κ⌉}e^{γ/ν}`.
* The repair-source margins (before `ω_b`): late output, thin receiver
  `(63/22)d₀ - γ + 4γ/9 = 79γ/198` (loss `m₀`), repair receiver `(79/22)d₀ - γ + 4γ/9 = 127γ/198`
  (loss `3m₀/2`); early source `(63/22)d₀ - 3γ/5 = 39γ/110` (loss `m₀`) and
  `(79/22)d₀ - 3γ/5 = 197γ/330` (loss `3m₀/2`) (5364-5365); all at least `19γ/66` (5617).
* `ageTransRep_of`: `TransRepOpTable → AgeTransRep` (both transitions, late-output bound,
  5339-5341).
* `ageLateEarlyRep_of`: `NearYoungOld` and the four entries `→ AgeLateEarlyRep`.
* `AgeRepVel` (the repair half of `SeqData.AgeErrorAt`, on `ageVel = S_far + Y`) and
  `ageRepVel_of`: `AgeLateEarlyRep → AgeTransRep → AgeRepVel` (`ageVel_split`).
-/

set_option autoImplicit false

noncomputable section

open Filter Set
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. Polynomial-exponential sizes -/

/-- `0 ≤ f ≤ B ν^{-J} e^{a/ν}`. -/
def YrPE (f ν a B : ℝ) (J : ℕ) : Prop := 0 ≤ f ∧ f ≤ B * ν⁻¹ ^ J * Real.exp (a / ν)

theorem YrPE.mul {f₁ f₂ ν a₁ a₂ B₁ B₂ : ℝ} {J₁ J₂ : ℕ} (h₁ : YrPE f₁ ν a₁ B₁ J₁)
    (h₂ : YrPE f₂ ν a₂ B₂ J₂) : YrPE (f₁ * f₂) ν (a₁ + a₂) (B₁ * B₂) (J₁ + J₂) := by
  refine ⟨mul_nonneg h₁.1 h₂.1, ?_⟩
  calc f₁ * f₂ ≤ (B₁ * ν⁻¹ ^ J₁ * Real.exp (a₁ / ν)) * (B₂ * ν⁻¹ ^ J₂ * Real.exp (a₂ / ν)) :=
        mul_le_mul h₁.2 h₂.2 h₂.1 (h₁.1.trans h₁.2)
    _ = B₁ * B₂ * ν⁻¹ ^ (J₁ + J₂) * Real.exp ((a₁ + a₂) / ν) := by
        rw [pow_add, add_div, Real.exp_add]; ring

theorem YrPE.mono {f ν a a' B : ℝ} {J J' : ℕ} (h : YrPE f ν a B J) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (ha : a ≤ a') (hJ : J ≤ J') : YrPE f ν a' B J' := by
  refine ⟨h.1, h.2.trans ?_⟩
  have hX : 0 < ν⁻¹ ^ J * Real.exp (a / ν) :=
    mul_pos (pow_pos (inv_pos.2 hν) J) (Real.exp_pos _)
  have hB : 0 ≤ B := by
    by_contra hneg
    have hneg' : B < 0 := lt_of_not_ge hneg
    have : B * ν⁻¹ ^ J * Real.exp (a / ν) < 0 := by
      rw [mul_assoc]; exact mul_neg_of_neg_of_pos hneg' hX
    linarith [h.1, h.2]
  have hp : ν⁻¹ ^ J ≤ ν⁻¹ ^ J' := pow_le_pow_right₀ ((one_le_inv₀ hν).2 hν1) hJ
  have he : Real.exp (a / ν) ≤ Real.exp (a' / ν) :=
    Real.exp_le_exp.2 (div_le_div_of_nonneg_right ha hν.le)
  exact mul_le_mul (mul_le_mul_of_nonneg_left hp hB) he (Real.exp_pos _).le
    (mul_nonneg hB (pow_nonneg (inv_nonneg.2 hν.le) _))

theorem YrPE.add {f₁ f₂ ν a B₁ B₂ : ℝ} {J : ℕ} (h₁ : YrPE f₁ ν a B₁ J) (h₂ : YrPE f₂ ν a B₂ J) :
    YrPE (f₁ + f₂) ν a (B₁ + B₂) J := by
  refine ⟨add_nonneg h₁.1 h₂.1, ?_⟩
  calc f₁ + f₂ ≤ B₁ * ν⁻¹ ^ J * Real.exp (a / ν) + B₂ * ν⁻¹ ^ J * Real.exp (a / ν) :=
        add_le_add h₁.2 h₂.2
    _ = (B₁ + B₂) * ν⁻¹ ^ J * Real.exp (a / ν) := by ring

theorem yrPE_exp (ν a : ℝ) : YrPE (Real.exp (a / ν)) ν a 1 0 :=
  ⟨(Real.exp_pos _).le, by simp⟩

/-- One entry: `x ≤ Cν^{-k}Fy` with `F` of size `e^{a/ν}`, `a ≤ a'`, gives
`x ≤ |C|Bν^{-(k+J)}e^{a'/ν}y`. -/
theorem yr_entry {x C F ν a a' B y : ℝ} {k J : ℕ} (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hF : YrPE F ν a B J) (ha : a ≤ a') (hy : 0 ≤ y) (hx : x ≤ C * ν⁻¹ ^ k * F * y) :
    x ≤ (|C| * B) * ν⁻¹ ^ (k + J) * Real.exp (a' / ν) * y := by
  have hF' := hF.mono hν hν1 ha le_rfl
  have hP : 0 ≤ ν⁻¹ ^ k := pow_nonneg (inv_nonneg.2 hν.le) k
  have hX : 0 ≤ ν⁻¹ ^ k * F * y := mul_nonneg (mul_nonneg hP hF.1) hy
  calc x ≤ C * ν⁻¹ ^ k * F * y := hx
    _ = C * (ν⁻¹ ^ k * F * y) := by ring
    _ ≤ |C| * (ν⁻¹ ^ k * F * y) := mul_le_mul_of_nonneg_right (le_abs_self C) hX
    _ = |C| * ν⁻¹ ^ k * F * y := by ring
    _ ≤ |C| * ν⁻¹ ^ k * (B * ν⁻¹ ^ J * Real.exp (a' / ν)) * y :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hF'.2 (mul_nonneg (abs_nonneg C) hP)) hy
    _ = (|C| * B) * ν⁻¹ ^ (k + J) * Real.exp (a' / ν) * y := by rw [pow_add]; ring

/-- Raise the viscosity degree (`ν ≤ 1`). -/
theorem yr_term {x B E y ν : ℝ} {j J : ℕ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hy : 0 ≤ y) (hj : j ≤ J) (hx : x ≤ B * ν⁻¹ ^ j * E * y) : x ≤ B * ν⁻¹ ^ J * E * y := by
  have hp : ν⁻¹ ^ j ≤ ν⁻¹ ^ J := pow_le_pow_right₀ ((one_le_inv₀ hν).2 hν1) hj
  exact hx.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp hB) hE) hy)

/-- `‖T‖_Z ≤ ‖(T₁,0)‖_Z + ‖(0,T₂)‖_Z`: the thin and the scaled repair receivers (source
5322-5325, "in the split stress norm"). -/
theorem yr_norm_le_thin_add_rep {c mZ ρb γ ν : ℝ} (x : StrG c mZ ρb γ ν) :
    ‖x‖ ≤ ‖thinPart x‖ + ‖repPart x‖ := by
  conv_lhs => rw [← thinPart_add_repPart x]
  exact norm_add_le _ _

/-! ## 2. The phase-locked amplitude and the gauge -/

/-- **`ε^p ≤ P_ν e^{-p(γ/3)/ν}`** for every real `p` (source 5936-5940: `ε_n = C_*ν_n^r
e^{-(γ/3)/ν_n}`; with `p = -kb` this is `S^k ≤ P_ν e^{kbd₀/ν}`, 5607). -/
theorem yr_retEps_rpow_le {Pl : PlanarData} {σ₀ : ℝ} (h : Pl.signedCoeff σ₀ ≠ 0) (p : ℝ) :
    ∃ (C : ℝ) (j : ℕ), 0 ≤ C ∧ ∀ n : ℕ, retNu Pl σ₀ n ≤ 1 →
      YrPE (retEps Pl σ₀ n ^ p) (retNu Pl σ₀ n) (-(p * (gRate Pl / 3))) C j := by
  set c : ℝ := (2 * ‖Pl.signedCoeff σ₀‖) ^ (-(1 / 3 : ℝ)) with hc
  set r : ℝ := (Pl.kappa.re - 5 - 2 * σ₀) / 3 with hr
  have hc0 : 0 < c := Real.rpow_pos_of_pos (mul_pos two_pos (norm_pos_iff.2 h)) _
  refine ⟨c ^ p, ⌈-(r * p)⌉₊, (Real.rpow_pos_of_pos hc0 _).le, fun n hν1 =>
    ⟨Real.rpow_nonneg (retEps_pos h n).le _, ?_⟩⟩
  have hν := retNu_pos Pl σ₀ n
  have hν' : 1 ≤ (retNu Pl σ₀ n)⁻¹ := (one_le_inv₀ hν).2 hν1
  have hp : 0 ≤ retNu Pl σ₀ n ^ r := Real.rpow_nonneg hν.le _
  rw [retEps_eq_form h n]
  have e1 : (c * retNu Pl σ₀ n ^ r * Real.exp (-(Pl.eigenvalue.re / 3) / retNu Pl σ₀ n)) ^ p =
      c ^ p * (retNu Pl σ₀ n)⁻¹ ^ (-(r * p)) *
        Real.exp (-(p * (gRate Pl / 3)) / retNu Pl σ₀ n) := by
    rw [Real.mul_rpow (mul_nonneg hc0.le hp) (Real.exp_pos _).le, Real.mul_rpow hc0.le hp,
      ← Real.exp_mul, ← Real.rpow_mul hν.le, Real.inv_rpow hν.le, ← Real.rpow_neg hν.le, neg_neg]
    have e3 : -(Pl.eigenvalue.re / 3) / retNu Pl σ₀ n * p =
        -(p * (gRate Pl / 3)) / retNu Pl σ₀ n := by
      unfold gRate; ring
    rw [e3]
  rw [e1]
  have hle : (retNu Pl σ₀ n)⁻¹ ^ (-(r * p)) ≤ (retNu Pl σ₀ n)⁻¹ ^ ⌈-(r * p)⌉₊ := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hν' (Nat.le_ceil _)
  have hE := (Real.exp_pos (-(p * (gRate Pl / 3)) / retNu Pl σ₀ n)).le
  have hC := (Real.rpow_pos_of_pos hc0 p).le
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hC) hE

/-- **`|N_ν| = e^{γ/ν}ν^{-Re κ}`** (source 5118). -/
theorem yr_gaugeN_eq (Pl : PlanarData) (L : ReturnLevel) :
    gaugeN Pl L = Real.exp (gRate Pl / L.ν) * L.ν ^ (-Pl.kappa.re) := by
  unfold gaugeN Nnu
  rw [norm_mul, Complex.norm_exp, Complex.norm_cpow_eq_rpow_re_of_pos L.ν_pos,
    Complex.div_ofReal_re, Complex.neg_re]

theorem yr_gaugeN_pe (Pl : PlanarData) (L : ReturnLevel) (hν1 : L.ν ≤ 1) :
    YrPE (gaugeN Pl L) L.ν (gRate Pl) 1 ⌈Pl.kappa.re⌉₊ := by
  have hν := L.ν_pos
  refine ⟨norm_nonneg _, ?_⟩
  rw [yr_gaugeN_eq]
  have h1 : 1 ≤ L.ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hpow : L.ν ^ (-Pl.kappa.re) ≤ L.ν⁻¹ ^ ⌈Pl.kappa.re⌉₊ := by
    rw [← Real.rpow_natCast, Real.rpow_neg hν.le, ← Real.inv_rpow hν.le]
    exact Real.rpow_le_rpow_of_exponent_le h1 (Nat.le_ceil _)
  calc Real.exp (gRate Pl / L.ν) * L.ν ^ (-Pl.kappa.re)
      ≤ Real.exp (gRate Pl / L.ν) * L.ν⁻¹ ^ ⌈Pl.kappa.re⌉₊ :=
        mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
    _ = 1 * L.ν⁻¹ ^ ⌈Pl.kappa.re⌉₊ * Real.exp (gRate Pl / L.ν) := by ring

/-! ## 3. The entries in the target form -/

namespace SeqData

variable (D : SeqData) {dm dp : ℝ}

/-- The target exponent `-(19γ/66 - ω_b - 3m₀/2)` with `ω_b = kk·b·γ/3` (source 5607, 5617). -/
def yrTgt (kk : ℕ) : ℝ :=
  -(19 * gRate D.Pl / 66 - (kk : ℝ) * D.K.b * (gRate D.Pl / 3) - 3 * D.K.m0 / 2)

theorem yr_kb_le (hst : D.RepairStanding dm dp) {j kk : ℕ} (hj : j ≤ kk) :
    (j : ℝ) * D.K.b * (gRate D.Pl / 3) ≤ (kk : ℝ) * D.K.b * (gRate D.Pl / 3) := by
  have hjr : (j : ℝ) ≤ (kk : ℝ) := by exact_mod_cast hj
  have hbg : 0 ≤ D.K.b * (gRate D.Pl / 3) := by
    have := hst.b_pos; have := hst.gamma_pos; positivity
  nlinarith

theorem yr_nu_le_one (hst : D.RepairStanding dm dp) :
    ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n ≤ 1 :=
  (retNu_tendsto D.σ₀ hst.omega_ne).eventually (ge_mem_nhds one_pos)

/-- Entry (late, repair → thin) in the target form, margin `79γ/198 - m₀` (source 5364). -/
theorem yrEntry_lateThin (hst : D.RepairStanding dm dp) {k₀ kk : ℕ} (hk : k₀ ≤ kk)
    (h : D.LateRepThinAt hst.chiY k₀) :
    ∃ (B : ℝ) (J : ℕ), 0 ≤ B ∧ ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∀ w : LVel D.Pl (D.level n),
        ‖thinPart (multOp D.Pl D.K (D.level n)
            (lateOutOp D.Pl D.K (D.level n) (D.mu n z) hst.chiY
              (repPart (multOp D.Pl D.K (D.level n) w))))‖ ≤
          B * (D.level n).ν⁻¹ ^ J * Real.exp (D.yrTgt kk / (D.level n).ν) * ‖w‖ := by
  obtain ⟨C, j, e⟩ := h
  have q := D.yr_kb_le hst hk
  have hγ := hst.gamma_pos
  have hm := hst.m0_pos
  obtain ⟨S, s, hS, PS⟩ := yr_retEps_rpow_le D.coeff_ne (-((k₀ : ℝ) * D.K.b))
  obtain ⟨E, t, hE, PE⟩ := yr_retEps_rpow_le D.coeff_ne (63 / 22)
  refine ⟨|C| * (S * E * 1 * 1 * 1), j + (s + t + 0 + ⌈D.Pl.kappa.re⌉₊ + 0),
    mul_nonneg (abs_nonneg _) (by simpa using mul_nonneg hS hE), ?_⟩
  filter_upwards [e, D.yr_nu_le_one hst] with n m hν z hz w
  have hνp : 0 < (D.level n).ν := (D.level n).ν_pos
  have hν' : (D.level n).ν ≤ 1 := hν
  have F1 : YrPE ((D.level n).ε ^ (-((k₀ : ℝ) * D.K.b))) (D.level n).ν
      (-(-((k₀ : ℝ) * D.K.b) * (gRate D.Pl / 3))) S s := PS n hν
  have F2 : YrPE ((D.level n).ε ^ (63 / 22 : ℝ)) (D.level n).ν
      (-(63 / 22 * (gRate D.Pl / 3))) E t := PE n hν
  have F := (((F1.mul F2).mul (yrPE_exp (D.level n).ν D.K.m0)).mul
    (yr_gaugeN_pe D.Pl (D.level n) hν')).mul (yrPE_exp (D.level n).ν (-(4 * gRate D.Pl / 9)))
  refine yr_entry hνp hν' F ?_ (norm_nonneg w) ((m z hz w).trans_eq (by ring))
  unfold yrTgt
  linarith

/-- Entry (late, repair → repair) in the target form, margin `127γ/198 - 3m₀/2` (table 5329). -/
theorem yrEntry_lateRep (hst : D.RepairStanding dm dp) {k₀ kk : ℕ} (hk : k₀ ≤ kk)
    (h : D.LateRepRepAt hst.chiY k₀) :
    ∃ (B : ℝ) (J : ℕ), 0 ≤ B ∧ ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∀ w : LVel D.Pl (D.level n),
        ‖repPart (multOp D.Pl D.K (D.level n)
            (lateOutOp D.Pl D.K (D.level n) (D.mu n z) hst.chiY
              (repPart (multOp D.Pl D.K (D.level n) w))))‖ ≤
          B * (D.level n).ν⁻¹ ^ J * Real.exp (D.yrTgt kk / (D.level n).ν) * ‖w‖ := by
  obtain ⟨C, j, e⟩ := h
  have q := D.yr_kb_le hst hk
  have hγ := hst.gamma_pos
  have hm := hst.m0_pos
  obtain ⟨S, s, hS, PS⟩ := yr_retEps_rpow_le D.coeff_ne (-((k₀ : ℝ) * D.K.b))
  obtain ⟨E, t, hE, PE⟩ := yr_retEps_rpow_le D.coeff_ne (79 / 22)
  refine ⟨|C| * (S * E * 1 * 1 * 1), j + (s + t + 0 + ⌈D.Pl.kappa.re⌉₊ + 0),
    mul_nonneg (abs_nonneg _) (by simpa using mul_nonneg hS hE), ?_⟩
  filter_upwards [e, D.yr_nu_le_one hst] with n m hν z hz w
  have hνp : 0 < (D.level n).ν := (D.level n).ν_pos
  have hν' : (D.level n).ν ≤ 1 := hν
  have F1 : YrPE ((D.level n).ε ^ (-((k₀ : ℝ) * D.K.b))) (D.level n).ν
      (-(-((k₀ : ℝ) * D.K.b) * (gRate D.Pl / 3))) S s := PS n hν
  have F2 : YrPE ((D.level n).ε ^ (79 / 22 : ℝ)) (D.level n).ν
      (-(79 / 22 * (gRate D.Pl / 3))) E t := PE n hν
  have F := (((F1.mul F2).mul (yrPE_exp (D.level n).ν (3 * D.K.m0 / 2))).mul
    (yr_gaugeN_pe D.Pl (D.level n) hν')).mul (yrPE_exp (D.level n).ν (-(4 * gRate D.Pl / 9)))
  refine yr_entry hνp hν' F ?_ (norm_nonneg w) ((m z hz w).trans_eq (by ring))
  unfold yrTgt
  linarith

/-- Entry (early, repair → thin) in the target form, margin `39γ/110 - m₀` (source 5365). -/
theorem yrEntry_earlyThin (hst : D.RepairStanding dm dp) {k₀ kk : ℕ} (hk : k₀ ≤ kk)
    (h : D.EarlyRepThinAt hst.chiY k₀) :
    ∃ (B : ℝ) (J : ℕ), 0 ≤ B ∧ ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∀ w : LVel D.Pl (D.level n),
        ‖thinPart (multOp D.Pl D.K (D.level n)
            (earlySrcOp D.Pl D.K (D.level n) (D.mu n z) hst.chiY
              (repPart (multOp D.Pl D.K (D.level n) w))))‖ ≤
          B * (D.level n).ν⁻¹ ^ J * Real.exp (D.yrTgt kk / (D.level n).ν) * ‖w‖ := by
  obtain ⟨C, j, e⟩ := h
  have q := D.yr_kb_le hst hk
  have hγ := hst.gamma_pos
  have hm := hst.m0_pos
  obtain ⟨S, s, hS, PS⟩ := yr_retEps_rpow_le D.coeff_ne (-((k₀ : ℝ) * D.K.b))
  obtain ⟨E, t, hE, PE⟩ := yr_retEps_rpow_le D.coeff_ne (63 / 22)
  refine ⟨|C| * (S * E * 1 * 1), j + (s + t + 0 + 0),
    mul_nonneg (abs_nonneg _) (by simpa using mul_nonneg hS hE), ?_⟩
  filter_upwards [e, D.yr_nu_le_one hst] with n m hν z hz w
  have hνp : 0 < (D.level n).ν := (D.level n).ν_pos
  have hν' : (D.level n).ν ≤ 1 := hν
  have F1 : YrPE ((D.level n).ε ^ (-((k₀ : ℝ) * D.K.b))) (D.level n).ν
      (-(-((k₀ : ℝ) * D.K.b) * (gRate D.Pl / 3))) S s := PS n hν
  have F2 : YrPE ((D.level n).ε ^ (63 / 22 : ℝ)) (D.level n).ν
      (-(63 / 22 * (gRate D.Pl / 3))) E t := PE n hν
  have F := ((F1.mul F2).mul (yrPE_exp (D.level n).ν D.K.m0)).mul
    (yrPE_exp (D.level n).ν (3 * gRate D.Pl / 5))
  refine yr_entry hνp hν' F ?_ (norm_nonneg w) ((m z hz w).trans_eq (by ring))
  unfold yrTgt
  linarith

/-- Entry (early, repair → repair) in the target form, margin `197γ/330 - 3m₀/2` (table 5329). -/
theorem yrEntry_earlyRep (hst : D.RepairStanding dm dp) {k₀ kk : ℕ} (hk : k₀ ≤ kk)
    (h : D.EarlyRepRepAt hst.chiY k₀) :
    ∃ (B : ℝ) (J : ℕ), 0 ≤ B ∧ ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∀ w : LVel D.Pl (D.level n),
        ‖repPart (multOp D.Pl D.K (D.level n)
            (earlySrcOp D.Pl D.K (D.level n) (D.mu n z) hst.chiY
              (repPart (multOp D.Pl D.K (D.level n) w))))‖ ≤
          B * (D.level n).ν⁻¹ ^ J * Real.exp (D.yrTgt kk / (D.level n).ν) * ‖w‖ := by
  obtain ⟨C, j, e⟩ := h
  have q := D.yr_kb_le hst hk
  have hγ := hst.gamma_pos
  have hm := hst.m0_pos
  obtain ⟨S, s, hS, PS⟩ := yr_retEps_rpow_le D.coeff_ne (-((k₀ : ℝ) * D.K.b))
  obtain ⟨E, t, hE, PE⟩ := yr_retEps_rpow_le D.coeff_ne (79 / 22)
  refine ⟨|C| * (S * E * 1 * 1), j + (s + t + 0 + 0),
    mul_nonneg (abs_nonneg _) (by simpa using mul_nonneg hS hE), ?_⟩
  filter_upwards [e, D.yr_nu_le_one hst] with n m hν z hz w
  have hνp : 0 < (D.level n).ν := (D.level n).ν_pos
  have hν' : (D.level n).ν ≤ 1 := hν
  have F1 : YrPE ((D.level n).ε ^ (-((k₀ : ℝ) * D.K.b))) (D.level n).ν
      (-(-((k₀ : ℝ) * D.K.b) * (gRate D.Pl / 3))) S s := PS n hν
  have F2 : YrPE ((D.level n).ε ^ (79 / 22 : ℝ)) (D.level n).ν
      (-(79 / 22 * (gRate D.Pl / 3))) E t := PE n hν
  have F := ((F1.mul F2).mul (yrPE_exp (D.level n).ν (3 * D.K.m0 / 2))).mul
    (yrPE_exp (D.level n).ν (3 * gRate D.Pl / 5))
  refine yr_entry hνp hν' F ?_ (norm_nonneg w) ((m z hz w).trans_eq (by ring))
  unfold yrTgt
  linarith

end SeqData

/-! ## 4. The two repair leaves -/

/-- **Both transitions on repair sources** (source 5339-5341: "both transition terms have the
late-output bound"; margins 5364-5365 and 127γ/198, 5617): the table row gives `AgeTransRep`
with `k₀ = k₁`. -/
theorem ageTransRep_of {Pl : PlanarData} {σ₀ mZ dm dp : ℝ} (h : TransRepOpTable Pl σ₀ mZ dm dp) :
    AgeTransRep Pl σ₀ mZ dm dp := by
  obtain ⟨k₁, H⟩ := h
  refine ⟨k₁, fun D hPl hσ hmZ hst => ?_⟩
  obtain ⟨C, j, e⟩ := H D hPl hσ hmZ hst
  have hγ := hst.gamma_pos
  have hm := hst.m0_pos
  obtain ⟨S, s, hS, PS⟩ := yr_retEps_rpow_le D.coeff_ne (-((k₁ : ℝ) * D.K.b))
  obtain ⟨E₁, t₁, hE₁, PE₁⟩ := yr_retEps_rpow_le D.coeff_ne (63 / 22)
  obtain ⟨E₂, t₂, hE₂, PE₂⟩ := yr_retEps_rpow_le D.coeff_ne (79 / 22)
  refine ⟨|C| * (S * 1 * (E₁ * 1 + E₂ * 1) * 1),
    j + (s + ⌈D.Pl.kappa.re⌉₊ + (t₁ + t₂) + 0), ?_⟩
  filter_upwards [e, D.yr_nu_le_one hst] with n m hν z hz w
  have hνp : 0 < (D.level n).ν := (D.level n).ν_pos
  have hν' : (D.level n).ν ≤ 1 := hν
  have F1 : YrPE ((D.level n).ε ^ (-((k₁ : ℝ) * D.K.b))) (D.level n).ν
      (-(-((k₁ : ℝ) * D.K.b) * (gRate D.Pl / 3))) S s := PS n hν
  have G1 : YrPE ((D.level n).ε ^ (63 / 22 : ℝ) * Real.exp (D.K.m0 / (D.level n).ν))
      (D.level n).ν (-(63 / 22 * (gRate D.Pl / 3)) + D.K.m0) (E₁ * 1) (t₁ + 0) :=
    (PE₁ n hν).mul (yrPE_exp (D.level n).ν D.K.m0)
  have G2 : YrPE ((D.level n).ε ^ (79 / 22 : ℝ) * Real.exp (3 * D.K.m0 / 2 / (D.level n).ν))
      (D.level n).ν (-(79 / 22 * (gRate D.Pl / 3)) + 3 * D.K.m0 / 2) (E₂ * 1) (t₂ + 0) :=
    (PE₂ n hν).mul (yrPE_exp (D.level n).ν (3 * D.K.m0 / 2))
  have G1' := G1.mono (a' := -(63 / 22 * (gRate D.Pl / 3)) + 3 * D.K.m0 / 2) (J' := t₁ + t₂)
    hνp hν' (by linarith) (by omega)
  have G2' := G2.mono (a' := -(63 / 22 * (gRate D.Pl / 3)) + 3 * D.K.m0 / 2) (J' := t₁ + t₂)
    hνp hν' (by linarith) (by omega)
  have F := ((F1.mul (yr_gaugeN_pe D.Pl (D.level n) hν')).mul (G1'.add G2')).mul
    (yrPE_exp (D.level n).ν (-(4 * gRate D.Pl / 9)))
  have hb := yr_entry hνp hν' F
    (a' := D.yrTgt k₁) (by unfold SeqData.yrTgt; linarith) (norm_nonneg w)
    ((m z hz w).trans_eq (by ring))
  exact hb

/-- **The late-output and early-source regions on repair sources** (source 5303-5308, the
repair-source row of the table 5328-5329, margins 5364-5365, 5617): `NearYoungOld` and the four
entries give `AgeLateEarlyRep` with `k₀` the largest of the four S-degrees. -/
theorem ageLateEarlyRep_of {Pl : PlanarData} {σ₀ mZ dm dp : ℝ} (h0 : NearYoungOld dm dp)
    (h1 : LateRepThin Pl σ₀ mZ dm dp) (h2 : LateRepRep Pl σ₀ mZ dm dp)
    (h3 : EarlyRepThin Pl σ₀ mZ dm dp) (h4 : EarlyRepRep Pl σ₀ mZ dm dp) :
    AgeLateEarlyRep Pl σ₀ mZ dm dp := by
  obtain ⟨k1, H1⟩ := h1
  obtain ⟨k2, H2⟩ := h2
  obtain ⟨k3, H3⟩ := h3
  obtain ⟨k4, H4⟩ := h4
  set kk := max (max k1 k2) (max k3 k4) with hkk
  refine ⟨kk, fun D hPl hσ hmZ hst => ?_⟩
  obtain ⟨B1, J1, hB1, a1⟩ := D.yrEntry_lateThin hst
    (le_trans (le_max_left k1 k2) (le_max_left _ _)) (H1 D hPl hσ hmZ hst)
  obtain ⟨B2, J2, hB2, a2⟩ := D.yrEntry_lateRep hst
    (le_trans (le_max_right k1 k2) (le_max_left _ _)) (H2 D hPl hσ hmZ hst)
  obtain ⟨B3, J3, hB3, a3⟩ := D.yrEntry_earlyThin hst
    (le_trans (le_max_left k3 k4) (le_max_right _ _)) (H3 D hPl hσ hmZ hst)
  obtain ⟨B4, J4, hB4, a4⟩ := D.yrEntry_earlyRep hst
    (le_trans (le_max_right k3 k4) (le_max_right _ _)) (H4 D hPl hσ hmZ hst)
  refine ⟨B1 + B2 + B3 + B4, max (max J1 J2) (max J3 J4), ?_⟩
  filter_upwards [a1, a2, a3, a4, D.yr_nu_le_one hst, h0 D hst] with n b1 b2 b3 b4 hν hN z hz w
  have hνp : 0 < (D.level n).ν := (D.level n).ν_pos
  have hν' : (D.level n).ν ≤ 1 := hν
  have hE0 : 0 ≤ Real.exp (D.yrTgt kk / (D.level n).ν) := (Real.exp_pos _).le
  have l1 := yr_term (J := max (max J1 J2) (max J3 J4)) hνp hν' hB1 hE0 (norm_nonneg w)
    (le_trans (le_max_left J1 J2) (le_max_left _ _)) (b1 z hz w)
  have l2 := yr_term (J := max (max J1 J2) (max J3 J4)) hνp hν' hB2 hE0 (norm_nonneg w)
    (le_trans (le_max_right J1 J2) (le_max_left _ _)) (b2 z hz w)
  have l3 := yr_term (J := max (max J1 J2) (max J3 J4)) hνp hν' hB3 hE0 (norm_nonneg w)
    (le_trans (le_max_left J3 J4) (le_max_right _ _)) (b3 z hz w)
  have l4 := yr_term (J := max (max J1 J2) (max J3 J4)) hνp hν' hB4 hE0 (norm_nonneg w)
    (le_trans (le_max_right J3 J4) (le_max_right _ _)) (b4 z hz w)
  have hsplit : multOp D.Pl D.K (D.level n)
      (lateEarlyOp D.Pl D.K (D.level n) (D.mu n z) hst.chiY
        (repPart (multOp D.Pl D.K (D.level n) w))) =
        multOp D.Pl D.K (D.level n)
          (lateOutOp D.Pl D.K (D.level n) (D.mu n z) hst.chiY
            (repPart (multOp D.Pl D.K (D.level n) w))) +
        multOp D.Pl D.K (D.level n)
          (earlySrcOp D.Pl D.K (D.level n) (D.mu n z) hst.chiY
            (repPart (multOp D.Pl D.K (D.level n) w))) := by
    rw [lateEarlyOp_eq_of D.Pl D.K (D.level n) (D.mu n z) hst.chiY (hN z hz), map_add]
  have hT : Real.exp (-(19 * gRate D.Pl / 66 - (kk : ℝ) * D.K.b * (gRate D.Pl / 3) -
      3 * D.K.m0 / 2) / (D.level n).ν) = Real.exp (D.yrTgt kk / (D.level n).ν) := rfl
  rw [hsplit, hT]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add (yr_norm_le_thin_add_rep _) (yr_norm_le_thin_add_rep _)
    _ ≤ _ := add_le_add (add_le_add l1 l2) (add_le_add l3 l4)
    _ = _ := by ring

/-! ## 5. The repair half of `repair:age-error` on `ageVel = S_far + Y` -/

namespace SeqData

/-- **The repair half of `SeqData.AgeErrorAt`** (source 5366-5372, 5617, 5622-5623: "the repair
source bounds use `G(w)`"): `‖g⁻¹M_U(S_far + Y)(0,(M_Uw)₂)‖_Z ≤ P_νe^{-(19γ/66-ω_b-3m₀/2)/ν}G(w)`. -/
def AgeRepVelAt (D : SeqData) (ωb : ℝ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ∀ w : LVel D.Pl (D.level n),
      ‖multOp D.Pl D.K (D.level n)
          (ageVel D.Pl D.K (D.level n) (D.mu n z) (repPart (multOp D.Pl D.K (D.level n) w)))‖ ≤
        C * (D.level n).ν⁻¹ ^ k *
          Real.exp (-(19 * gRate D.Pl / 66 - ωb - 3 * D.K.m0 / 2) / (D.level n).ν) * ‖w‖

end SeqData

/-- The repair half of `repair:age-error`, with the S-degree `k₀` chosen before `b`
(`ω_b = k₀bγ/3`, 5607). -/
def AgeRepVel (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∃ k₀ : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ → D.RepairStanding dm dp →
    D.AgeRepVelAt ((k₀ : ℝ) * D.K.b * (gRate D.Pl / 3))

/-- Enlarge `ω_b` and replace the constant by its absolute value. -/
theorem yr_lift {v x C P a c ωb ωb' ν : ℝ} (hν : 0 < ν) (hP : 0 ≤ P) (hx : 0 ≤ x)
    (hω : ωb ≤ ωb') (h : v ≤ C * P * Real.exp (-(a - ωb - c) / ν) * x) :
    v ≤ |C| * P * Real.exp (-(a - ωb' - c) / ν) * x := by
  have hE : Real.exp (-(a - ωb - c) / ν) ≤ Real.exp (-(a - ωb' - c) / ν) :=
    Real.exp_le_exp.2 (div_le_div_of_nonneg_right (by linarith) hν.le)
  refine h.trans ?_
  have h1 : C * P * Real.exp (-(a - ωb - c) / ν) * x ≤
      |C| * P * Real.exp (-(a - ωb - c) / ν) * x :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self C) hP) (Real.exp_pos _).le) hx
  exact h1.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hE (mul_nonneg (abs_nonneg C) hP)) hx)

/-- **The repair half of `repair:age-error`** (source 5687-5689: `S_far + Y` consists exactly of
the early-source and late-output regions and the two stream transitions): the two repair leaves
give the bound on `ageVel`, by `ageVel = lateEarlyOp + transOp` (`Org/YThinTrans.lean`). -/
theorem ageRepVel_of {Pl : PlanarData} {σ₀ mZ dm dp : ℝ} (h1 : AgeLateEarlyRep Pl σ₀ mZ dm dp)
    (h2 : AgeTransRep Pl σ₀ mZ dm dp) : AgeRepVel Pl σ₀ mZ dm dp := by
  obtain ⟨k1, H1⟩ := h1
  obtain ⟨k2, H2⟩ := h2
  refine ⟨max k1 k2, fun D hPl hσ hmZ hst => ?_⟩
  obtain ⟨C1, j1, e1⟩ := H1 D hPl hσ hmZ hst
  obtain ⟨C2, j2, e2⟩ := H2 D hPl hσ hmZ hst
  have m1 := D.yr_kb_le hst (le_max_left k1 k2)
  have m2 := D.yr_kb_le hst (le_max_right k1 k2)
  refine ⟨|C1| + |C2|, max j1 j2, ?_⟩
  filter_upwards [e1, e2, D.yr_nu_le_one hst] with n b1 b2 hν z hz w
  have hνp : 0 < (D.level n).ν := (D.level n).ν_pos
  have hν' : (D.level n).ν ≤ 1 := hν
  have hP : ∀ j : ℕ, 0 ≤ (D.level n).ν⁻¹ ^ j := fun j => by positivity
  have hE0 : 0 ≤ Real.exp (-(19 * gRate D.Pl / 66 -
      ((max k1 k2 : ℕ) : ℝ) * D.K.b * (gRate D.Pl / 3) - 3 * D.K.m0 / 2) / (D.level n).ν) :=
    (Real.exp_pos _).le
  have l1 := yr_term (J := max j1 j2) hνp hν' (abs_nonneg C1) hE0 (norm_nonneg w)
    (le_max_left j1 j2) (yr_lift hνp (hP j1) (norm_nonneg w) m1 (b1 z hz w))
  have l2 := yr_term (J := max j1 j2) hνp hν' (abs_nonneg C2) hE0 (norm_nonneg w)
    (le_max_right j1 j2) (yr_lift hνp (hP j2) (norm_nonneg w) m2 (b2 z hz w))
  have hsplit : multOp D.Pl D.K (D.level n)
      (ageVel D.Pl D.K (D.level n) (D.mu n z) (repPart (multOp D.Pl D.K (D.level n) w))) =
        multOp D.Pl D.K (D.level n)
          (lateEarlyOp D.Pl D.K (D.level n) (D.mu n z) hst.chiY
            (repPart (multOp D.Pl D.K (D.level n) w))) +
        multOp D.Pl D.K (D.level n)
          (transOp D.Pl D.K (D.level n) (D.mu n z) hst.chiY
            (repPart (multOp D.Pl D.K (D.level n) w))) := by
    rw [ageVel_split D.Pl D.K (D.level n) (D.mu n z) hst.chiY, ContinuousLinearMap.add_apply,
      map_add]
  rw [hsplit]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add l1 l2
    _ = _ := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
