import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThinProps
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.EpsForm

/-!
# `PartIII-b:C/rep/4/1/org` (c): the bridge from the thin-source row to the corrected leaf

Source `the November 2 reference manuscript` 5317-5372, 5607, 5936-5940.

`ageLateEarlyThin_of`: the four entries of the thin-source row (`FarThinProps.lean`) bound
`ftLEOp = (1-χ_y)F_far + χ_yF_far(1-χ_o)` on thin sources (`ft_combine`, `FtLEThinAt`) with
`ω_b = k₀bγ/3`, `k₀` the largest of the four S-degrees; with `χ_yS_Nχ_o = 0`
(`NearYoungOldZero`) and `lateEarlyOp = ftLEOp - χ_yS_Nχ_o` (`lateEarlyOp_eq`) this is the leaf
`AgeLateEarlyThin`.  Ingredients (proved):

* `ft_retEps_rpow_le`: `ε^p ≤ P_ν e^{-p(γ/3)/ν}` for every real `p` on the phase-locked sequence
  `ε = C_*ν^r e^{-(γ/3)/ν}` (5936-5940, `retEps_eq_form`); with `p = -k₀b` this is
  `S^{k₀} ≤ P_ν e^{k₀bd₀/ν}`, `d₀ = γ/3` (5607);
* `ft_gaugeN_eq`: `|N_ν| = e^{γ/ν}ν^{-Re κ}` (5118);
* the margins 5357-5365: late `γ/9`, `37γ/198 - m₀/2`; early `γ/15`, `47γ/330 - m₀/2`, all at least
  `γ/15 - 3m₀/2`;
* the receiver split `‖x‖ ≤ ‖x₁‖ + ‖x₂‖` (`ft_norm_le_thin_add_rep`).
-/

set_option autoImplicit false

noncomputable section

open Filter Set
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. Polynomial-exponential sizes -/

/-- `0 ≤ f ≤ B ν^{-J} e^{a/ν}`. -/
def FtPE (f ν a B : ℝ) (J : ℕ) : Prop := 0 ≤ f ∧ f ≤ B * ν⁻¹ ^ J * Real.exp (a / ν)

theorem FtPE.mul {f₁ f₂ ν a₁ a₂ B₁ B₂ : ℝ} {J₁ J₂ : ℕ} (h₁ : FtPE f₁ ν a₁ B₁ J₁)
    (h₂ : FtPE f₂ ν a₂ B₂ J₂) : FtPE (f₁ * f₂) ν (a₁ + a₂) (B₁ * B₂) (J₁ + J₂) := by
  refine ⟨mul_nonneg h₁.1 h₂.1, ?_⟩
  calc f₁ * f₂ ≤ (B₁ * ν⁻¹ ^ J₁ * Real.exp (a₁ / ν)) * (B₂ * ν⁻¹ ^ J₂ * Real.exp (a₂ / ν)) :=
        mul_le_mul h₁.2 h₂.2 h₂.1 (h₁.1.trans h₁.2)
    _ = B₁ * B₂ * ν⁻¹ ^ (J₁ + J₂) * Real.exp ((a₁ + a₂) / ν) := by
        rw [pow_add, add_div, Real.exp_add]; ring

theorem FtPE.mono {f ν a a' B : ℝ} {J J' : ℕ} (h : FtPE f ν a B J) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (ha : a ≤ a') (hJ : J ≤ J') : FtPE f ν a' B J' := by
  refine ⟨h.1, h.2.trans ?_⟩
  have hX : 0 < ν⁻¹ ^ J * Real.exp (a / ν) :=
    mul_pos (pow_pos (inv_pos.2 hν) J) (Real.exp_pos _)
  have hB : 0 ≤ B := by
    by_contra hneg
    push Not at hneg
    have : B * ν⁻¹ ^ J * Real.exp (a / ν) < 0 := by
      rw [mul_assoc]; exact mul_neg_of_neg_of_pos hneg hX
    linarith [h.1, h.2]
  have hp : ν⁻¹ ^ J ≤ ν⁻¹ ^ J' := pow_le_pow_right₀ ((one_le_inv₀ hν).2 hν1) hJ
  have he : Real.exp (a / ν) ≤ Real.exp (a' / ν) :=
    Real.exp_le_exp.2 (div_le_div_of_nonneg_right ha hν.le)
  exact mul_le_mul (mul_le_mul_of_nonneg_left hp hB) he (Real.exp_pos _).le
    (mul_nonneg hB (pow_nonneg (inv_nonneg.2 hν.le) _))

theorem ftPE_exp (ν a : ℝ) : FtPE (Real.exp (a / ν)) ν a 1 0 :=
  ⟨(Real.exp_pos _).le, by simp⟩

/-- One entry: `x ≤ Cν^{-k}Fy` with `F` of size `e^{a/ν}`, `a ≤ a'`, gives
`x ≤ |C|Bν^{-(k+J)}e^{a'/ν}y`. -/
theorem ft_entry {x C F ν a a' B y : ℝ} {k J : ℕ} (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hF : FtPE F ν a B J) (ha : a ≤ a') (hy : 0 ≤ y) (hx : x ≤ C * ν⁻¹ ^ k * F * y) :
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
theorem ft_term {x B E y ν : ℝ} {j J : ℕ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hy : 0 ≤ y) (hj : j ≤ J) (hx : x ≤ B * ν⁻¹ ^ j * E * y) : x ≤ B * ν⁻¹ ^ J * E * y := by
  have hp : ν⁻¹ ^ j ≤ ν⁻¹ ^ J := pow_le_pow_right₀ ((one_le_inv₀ hν).2 hν1) hj
  exact hx.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp hB) hE) hy)

/-! ## 2. The phase-locked amplitude and the gauge -/

/-- **`ε^p ≤ P_ν e^{-p(γ/3)/ν}`** for every real `p` (source 5936-5940: `ε_n = C_*ν_n^r
e^{-(γ/3)/ν_n}`; with `p = -k b` this is `S^k ≤ P_ν e^{kbd₀/ν}`, 5607). -/
theorem ft_retEps_rpow_le {Pl : PlanarData} {σ₀ : ℝ} (h : Pl.signedCoeff σ₀ ≠ 0) (p : ℝ) :
    ∃ (C : ℝ) (j : ℕ), 0 ≤ C ∧ ∀ n : ℕ, retNu Pl σ₀ n ≤ 1 →
      FtPE (retEps Pl σ₀ n ^ p) (retNu Pl σ₀ n) (-(p * (gRate Pl / 3))) C j := by
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
theorem ft_gaugeN_eq (Pl : PlanarData) (L : ReturnLevel) :
    gaugeN Pl L = Real.exp (gRate Pl / L.ν) * L.ν ^ (-Pl.kappa.re) := by
  unfold gaugeN Nnu
  rw [norm_mul, Complex.norm_exp, Complex.norm_cpow_eq_rpow_re_of_pos L.ν_pos,
    Complex.div_ofReal_re, Complex.neg_re]

theorem ft_gaugeN_pe (Pl : PlanarData) (L : ReturnLevel) (hν1 : L.ν ≤ 1) :
    FtPE (gaugeN Pl L) L.ν (gRate Pl) 1 ⌈Pl.kappa.re⌉₊ := by
  have hν := L.ν_pos
  refine ⟨norm_nonneg _, ?_⟩
  rw [ft_gaugeN_eq]
  have h1 : 1 ≤ L.ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hpow : L.ν ^ (-Pl.kappa.re) ≤ L.ν⁻¹ ^ ⌈Pl.kappa.re⌉₊ := by
    rw [← Real.rpow_natCast, Real.rpow_neg hν.le, ← Real.inv_rpow hν.le]
    exact Real.rpow_le_rpow_of_exponent_le h1 (Nat.le_ceil _)
  calc Real.exp (gRate Pl / L.ν) * L.ν ^ (-Pl.kappa.re)
      ≤ Real.exp (gRate Pl / L.ν) * L.ν⁻¹ ^ ⌈Pl.kappa.re⌉₊ :=
        mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
    _ = 1 * L.ν⁻¹ ^ ⌈Pl.kappa.re⌉₊ * Real.exp (gRate Pl / L.ν) := by ring

/-! ## 3. The bridge -/

namespace SeqData

variable (D : SeqData) {dm dp : ℝ}

/-- The target exponent `-(γ/15 - ω_b - 3m₀/2)` with `ω_b = kk·b·γ/3` (source 5368-5372, 5607). -/
def ftTgt (kk : ℕ) : ℝ := -(gRate D.Pl / 15 - (kk : ℝ) * D.K.b * (gRate D.Pl / 3) - 3 * D.K.m0 / 2)

theorem ft_kb_le (hst : D.RepairStanding dm dp) {j kk : ℕ} (hj : j ≤ kk) :
    (j : ℝ) * D.K.b * (gRate D.Pl / 3) ≤ (kk : ℝ) * D.K.b * (gRate D.Pl / 3) := by
  have hjr : (j : ℝ) ≤ (kk : ℝ) := by exact_mod_cast hj
  have hbg : 0 ≤ D.K.b * (gRate D.Pl / 3) := by
    have := hst.b_pos; have := hst.gamma_pos; positivity
  nlinarith

theorem ft_nu_le_one (hst : D.RepairStanding dm dp) :
    ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n ≤ 1 :=
  (retNu_tendsto D.σ₀ hst.omega_ne).eventually (ge_mem_nhds one_pos)

/-- Entry (late, thin → thin) in the target form, margin `γ/9` (source 5357-5359). -/
theorem ftEntry_lateThin (hst : D.RepairStanding dm dp) {k₀ kk : ℕ} (hk : k₀ ≤ kk)
    (h : D.FarLateThinThinAt hst.chiY k₀) :
    ∃ (B : ℝ) (J : ℕ), 0 ≤ B ∧ ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∀ T : LStr D.Pl D.K (D.level n),
        ‖thinPart (multOp D.Pl D.K (D.level n)
            (ftLateOp D.Pl D.K (D.level n) (D.mu n z) hst.chiY (thinPart T)))‖ ≤
          B * (D.level n).ν⁻¹ ^ J * Real.exp (D.ftTgt kk / (D.level n).ν) * ‖T‖ := by
  obtain ⟨C, j, e⟩ := h
  have q := D.ft_kb_le hst hk
  have hγ := hst.gamma_pos
  have hm := hst.m0_pos
  obtain ⟨S, s, hS, PS⟩ := ft_retEps_rpow_le D.coeff_ne (-((k₀ : ℝ) * D.K.b))
  obtain ⟨E, t, hE, PE⟩ := ft_retEps_rpow_le D.coeff_ne 2
  refine ⟨|C| * (S * E * 1 * 1), j + (s + t + ⌈D.Pl.kappa.re⌉₊ + 0),
    mul_nonneg (abs_nonneg _) (by simpa using mul_nonneg hS hE), ?_⟩
  filter_upwards [e, D.ft_nu_le_one hst] with n m hν z hz T
  have hνp : 0 < (D.level n).ν := (D.level n).ν_pos
  have hν' : (D.level n).ν ≤ 1 := hν
  have F1 : FtPE ((D.level n).ε ^ (-((k₀ : ℝ) * D.K.b))) (D.level n).ν
      (-(-((k₀ : ℝ) * D.K.b) * (gRate D.Pl / 3))) S s := PS n hν
  have F2 : FtPE ((D.level n).ε ^ (2 : ℝ)) (D.level n).ν (-(2 * (gRate D.Pl / 3))) E t :=
    PE n hν
  have F := ((F1.mul F2).mul (ft_gaugeN_pe D.Pl (D.level n) hν')).mul
    (ftPE_exp (D.level n).ν (-(4 * gRate D.Pl / 9)))
  refine ft_entry hνp hν' F ?_ (norm_nonneg T) ((m z hz T).trans_eq (by ring))
  unfold ftTgt
  linarith

/-- Entry (late, thin → repair) in the target form, margin `37γ/198 - m₀/2` (source 5360-5361). -/
theorem ftEntry_lateRep (hst : D.RepairStanding dm dp) {k₀ kk : ℕ} (hk : k₀ ≤ kk)
    (h : D.FarLateThinRepAt hst.chiY k₀) :
    ∃ (B : ℝ) (J : ℕ), 0 ≤ B ∧ ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∀ T : LStr D.Pl D.K (D.level n),
        ‖repPart (multOp D.Pl D.K (D.level n)
            (ftLateOp D.Pl D.K (D.level n) (D.mu n z) hst.chiY (thinPart T)))‖ ≤
          B * (D.level n).ν⁻¹ ^ J * Real.exp (D.ftTgt kk / (D.level n).ν) * ‖T‖ := by
  obtain ⟨C, j, e⟩ := h
  have q := D.ft_kb_le hst hk
  have hγ := hst.gamma_pos
  have hm := hst.m0_pos
  obtain ⟨S, s, hS, PS⟩ := ft_retEps_rpow_le D.coeff_ne (-((k₀ : ℝ) * D.K.b))
  obtain ⟨E, t, hE, PE⟩ := ft_retEps_rpow_le D.coeff_ne (49 / 22)
  refine ⟨|C| * (S * E * 1 * 1 * 1), j + (s + t + 0 + ⌈D.Pl.kappa.re⌉₊ + 0),
    mul_nonneg (abs_nonneg _) (by simpa using mul_nonneg hS hE), ?_⟩
  filter_upwards [e, D.ft_nu_le_one hst] with n m hν z hz T
  have hνp : 0 < (D.level n).ν := (D.level n).ν_pos
  have hν' : (D.level n).ν ≤ 1 := hν
  have F1 : FtPE ((D.level n).ε ^ (-((k₀ : ℝ) * D.K.b))) (D.level n).ν
      (-(-((k₀ : ℝ) * D.K.b) * (gRate D.Pl / 3))) S s := PS n hν
  have F2 : FtPE ((D.level n).ε ^ (49 / 22 : ℝ)) (D.level n).ν
      (-(49 / 22 * (gRate D.Pl / 3))) E t := PE n hν
  have F := (((F1.mul F2).mul (ftPE_exp (D.level n).ν (D.K.m0 / 2))).mul
    (ft_gaugeN_pe D.Pl (D.level n) hν')).mul (ftPE_exp (D.level n).ν (-(4 * gRate D.Pl / 9)))
  refine ft_entry hνp hν' F ?_ (norm_nonneg T) ((m z hz T).trans_eq (by ring))
  unfold ftTgt
  linarith

/-- Entry (early, thin → thin) in the target form, margin `γ/15` (source 5357-5359). -/
theorem ftEntry_earlyThin (hst : D.RepairStanding dm dp) {k₀ kk : ℕ} (hk : k₀ ≤ kk)
    (h : D.FarEarlyThinThinAt hst.chiY k₀) :
    ∃ (B : ℝ) (J : ℕ), 0 ≤ B ∧ ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∀ T : LStr D.Pl D.K (D.level n),
        ‖thinPart (multOp D.Pl D.K (D.level n)
            (ftEarlyOp D.Pl D.K (D.level n) (D.mu n z) hst.chiY (thinPart T)))‖ ≤
          B * (D.level n).ν⁻¹ ^ J * Real.exp (D.ftTgt kk / (D.level n).ν) * ‖T‖ := by
  obtain ⟨C, j, e⟩ := h
  have q := D.ft_kb_le hst hk
  have hγ := hst.gamma_pos
  have hm := hst.m0_pos
  obtain ⟨S, s, hS, PS⟩ := ft_retEps_rpow_le D.coeff_ne (-((k₀ : ℝ) * D.K.b))
  obtain ⟨E, t, hE, PE⟩ := ft_retEps_rpow_le D.coeff_ne 2
  refine ⟨|C| * (S * E * 1), j + (s + t + 0),
    mul_nonneg (abs_nonneg _) (by simpa using mul_nonneg hS hE), ?_⟩
  filter_upwards [e, D.ft_nu_le_one hst] with n m hν z hz T
  have hνp : 0 < (D.level n).ν := (D.level n).ν_pos
  have hν' : (D.level n).ν ≤ 1 := hν
  have F1 : FtPE ((D.level n).ε ^ (-((k₀ : ℝ) * D.K.b))) (D.level n).ν
      (-(-((k₀ : ℝ) * D.K.b) * (gRate D.Pl / 3))) S s := PS n hν
  have F2 : FtPE ((D.level n).ε ^ (2 : ℝ)) (D.level n).ν (-(2 * (gRate D.Pl / 3))) E t :=
    PE n hν
  have F := (F1.mul F2).mul (ftPE_exp (D.level n).ν (3 * gRate D.Pl / 5))
  refine ft_entry hνp hν' F ?_ (norm_nonneg T) ((m z hz T).trans_eq (by ring))
  unfold ftTgt
  linarith

/-- Entry (early, thin → repair) in the target form, margin `47γ/330 - m₀/2` (source 5360-5361). -/
theorem ftEntry_earlyRep (hst : D.RepairStanding dm dp) {k₀ kk : ℕ} (hk : k₀ ≤ kk)
    (h : D.FarEarlyThinRepAt hst.chiY k₀) :
    ∃ (B : ℝ) (J : ℕ), 0 ≤ B ∧ ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∀ T : LStr D.Pl D.K (D.level n),
        ‖repPart (multOp D.Pl D.K (D.level n)
            (ftEarlyOp D.Pl D.K (D.level n) (D.mu n z) hst.chiY (thinPart T)))‖ ≤
          B * (D.level n).ν⁻¹ ^ J * Real.exp (D.ftTgt kk / (D.level n).ν) * ‖T‖ := by
  obtain ⟨C, j, e⟩ := h
  have q := D.ft_kb_le hst hk
  have hγ := hst.gamma_pos
  have hm := hst.m0_pos
  obtain ⟨S, s, hS, PS⟩ := ft_retEps_rpow_le D.coeff_ne (-((k₀ : ℝ) * D.K.b))
  obtain ⟨E, t, hE, PE⟩ := ft_retEps_rpow_le D.coeff_ne (49 / 22)
  refine ⟨|C| * (S * E * 1 * 1), j + (s + t + 0 + 0),
    mul_nonneg (abs_nonneg _) (by simpa using mul_nonneg hS hE), ?_⟩
  filter_upwards [e, D.ft_nu_le_one hst] with n m hν z hz T
  have hνp : 0 < (D.level n).ν := (D.level n).ν_pos
  have hν' : (D.level n).ν ≤ 1 := hν
  have F1 : FtPE ((D.level n).ε ^ (-((k₀ : ℝ) * D.K.b))) (D.level n).ν
      (-(-((k₀ : ℝ) * D.K.b) * (gRate D.Pl / 3))) S s := PS n hν
  have F2 : FtPE ((D.level n).ε ^ (49 / 22 : ℝ)) (D.level n).ν
      (-(49 / 22 * (gRate D.Pl / 3))) E t := PE n hν
  have F := ((F1.mul F2).mul (ftPE_exp (D.level n).ν (D.K.m0 / 2))).mul
    (ftPE_exp (D.level n).ν (3 * gRate D.Pl / 5))
  refine ft_entry hνp hν' F ?_ (norm_nonneg T) ((m z hz T).trans_eq (by ring))
  unfold ftTgt
  linarith

/-- Four receiver/region bounds in the target form give the bound for `M_U ftLE (T₁,0)`. -/
theorem ft_combine (hst : D.RepairStanding dm dp) (kk : ℕ) {B1 B2 B3 B4 : ℝ} {J1 J2 J3 J4 : ℕ}
    (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2) (hB3 : 0 ≤ B3) (hB4 : 0 ≤ B4)
    (a1 : ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ T : LStr D.Pl D.K (D.level n),
        ‖thinPart (multOp D.Pl D.K (D.level n)
            (ftLateOp D.Pl D.K (D.level n) (D.mu n z) hst.chiY (thinPart T)))‖ ≤
          B1 * (D.level n).ν⁻¹ ^ J1 * Real.exp (D.ftTgt kk / (D.level n).ν) * ‖T‖)
    (a2 : ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ T : LStr D.Pl D.K (D.level n),
        ‖repPart (multOp D.Pl D.K (D.level n)
            (ftLateOp D.Pl D.K (D.level n) (D.mu n z) hst.chiY (thinPart T)))‖ ≤
          B2 * (D.level n).ν⁻¹ ^ J2 * Real.exp (D.ftTgt kk / (D.level n).ν) * ‖T‖)
    (a3 : ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ T : LStr D.Pl D.K (D.level n),
        ‖thinPart (multOp D.Pl D.K (D.level n)
            (ftEarlyOp D.Pl D.K (D.level n) (D.mu n z) hst.chiY (thinPart T)))‖ ≤
          B3 * (D.level n).ν⁻¹ ^ J3 * Real.exp (D.ftTgt kk / (D.level n).ν) * ‖T‖)
    (a4 : ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ T : LStr D.Pl D.K (D.level n),
        ‖repPart (multOp D.Pl D.K (D.level n)
            (ftEarlyOp D.Pl D.K (D.level n) (D.mu n z) hst.chiY (thinPart T)))‖ ≤
          B4 * (D.level n).ν⁻¹ ^ J4 * Real.exp (D.ftTgt kk / (D.level n).ν) * ‖T‖) :
    D.FtLEThinAt hst.chiY ((kk : ℝ) * D.K.b * (gRate D.Pl / 3)) := by
  refine ⟨B1 + B2 + B3 + B4, max (max J1 J2) (max J3 J4), ?_⟩
  filter_upwards [a1, a2, a3, a4, D.ft_nu_le_one hst] with n b1 b2 b3 b4 hν z hz T
  have hνp : 0 < (D.level n).ν := (D.level n).ν_pos
  have hν' : (D.level n).ν ≤ 1 := hν
  have hE0 : 0 ≤ Real.exp (D.ftTgt kk / (D.level n).ν) := (Real.exp_pos _).le
  have l1 := ft_term (J := max (max J1 J2) (max J3 J4)) hνp hν' hB1 hE0 (norm_nonneg T)
    (le_trans (le_max_left J1 J2) (le_max_left _ _)) (b1 z hz T)
  have l2 := ft_term (J := max (max J1 J2) (max J3 J4)) hνp hν' hB2 hE0 (norm_nonneg T)
    (le_trans (le_max_right J1 J2) (le_max_left _ _)) (b2 z hz T)
  have l3 := ft_term (J := max (max J1 J2) (max J3 J4)) hνp hν' hB3 hE0 (norm_nonneg T)
    (le_trans (le_max_left J3 J4) (le_max_right _ _)) (b3 z hz T)
  have l4 := ft_term (J := max (max J1 J2) (max J3 J4)) hνp hν' hB4 hE0 (norm_nonneg T)
    (le_trans (le_max_right J3 J4) (le_max_right _ _)) (b4 z hz T)
  have hsplit : multOp D.Pl D.K (D.level n)
      (ftLEOp D.Pl D.K (D.level n) (D.mu n z) hst.chiY (thinPart T)) =
        multOp D.Pl D.K (D.level n)
          (ftLateOp D.Pl D.K (D.level n) (D.mu n z) hst.chiY (thinPart T)) +
        multOp D.Pl D.K (D.level n)
          (ftEarlyOp D.Pl D.K (D.level n) (D.mu n z) hst.chiY (thinPart T)) := by
    simp only [ftLEOp, add_apply, map_add]
  have hT : Real.exp (-(gRate D.Pl / 15 - (kk : ℝ) * D.K.b * (gRate D.Pl / 3) -
      3 * D.K.m0 / 2) / (D.level n).ν) = Real.exp (D.ftTgt kk / (D.level n).ν) := rfl
  rw [hsplit, hT]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add (ft_norm_le_thin_add_rep _) (ft_norm_le_thin_add_rep _)
    _ ≤ _ := add_le_add (add_le_add l1 l2) (add_le_add l3 l4)
    _ = _ := by ring

/-- `lateEarlyOp = ftLEOp` once the near operator vanishes on the young-old rectangle. -/
theorem ageLateEarlyThinAt_of (hst : D.RepairStanding dm dp) (h0 : NearYoungOldZero dm dp)
    {ωb : ℝ} (h : D.FtLEThinAt hst.chiY ωb) : D.AgeLateEarlyThinAt hst.chiY ωb := by
  obtain ⟨C, k, e⟩ := h
  refine ⟨C, k, ?_⟩
  filter_upwards [e, h0 D hst] with n hn h0n z hz T
  rw [lateEarlyOp_eq, h0n z hz, sub_zero]
  exact hn z hz T

end SeqData

/-- **Bridge** (source 5303-5372, 5607): the four entries of the thin-source row and
`χ_yS_Nχ_o = 0` give the thin far leaf `AgeLateEarlyThin` (late output and early source on thin
sources), with `k₀` the largest of the four S-degrees. -/
theorem ageLateEarlyThin_of (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) (h0 : NearYoungOldZero dm dp)
    (h1 : FarLateThinThin Pl σ₀ mZ dm dp) (h2 : FarLateThinRep Pl σ₀ mZ dm dp)
    (h3 : FarEarlyThinThin Pl σ₀ mZ dm dp) (h4 : FarEarlyThinRep Pl σ₀ mZ dm dp) :
    AgeLateEarlyThin Pl σ₀ mZ dm dp := by
  obtain ⟨k1, H1⟩ := h1
  obtain ⟨k2, H2⟩ := h2
  obtain ⟨k3, H3⟩ := h3
  obtain ⟨k4, H4⟩ := h4
  refine ⟨max (max k1 k2) (max k3 k4), fun D hPl hσ hmZ hst => ?_⟩
  obtain ⟨B1, J1, hB1, a1⟩ := D.ftEntry_lateThin hst
    (le_trans (le_max_left k1 k2) (le_max_left _ _)) (H1 D hPl hσ hmZ hst)
  obtain ⟨B2, J2, hB2, a2⟩ := D.ftEntry_lateRep hst
    (le_trans (le_max_right k1 k2) (le_max_left _ _)) (H2 D hPl hσ hmZ hst)
  obtain ⟨B3, J3, hB3, a3⟩ := D.ftEntry_earlyThin hst
    (le_trans (le_max_left k3 k4) (le_max_right _ _)) (H3 D hPl hσ hmZ hst)
  obtain ⟨B4, J4, hB4, a4⟩ := D.ftEntry_earlyRep hst
    (le_trans (le_max_right k3 k4) (le_max_right _ _)) (H4 D hPl hσ hmZ hst)
  exact D.ageLateEarlyThinAt_of hst h0 (D.ft_combine hst _ hB1 hB2 hB3 hB4 a1 a2 a3 a4)

end UnforcedLeray.Short.PartIIIb.Concrete
