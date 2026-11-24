import UnforcedLeray.Short.PartIIIa.Sub.T21_c2_2
import UnforcedLeray.Short.PartI.StatementsTrain
import UnforcedLeray.Short.Spine.Proofs.EstVcRegularity
import UnforcedLeray.Units.B0169
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Part III-a, `PartIII-a:T21/c2/2/1/org`: `FmrTrainClose` from the Part I train estimates

Source of record: `the November 2 reference manuscript` (SP), lines 2085-2090 (the
train comparison "in any fixed finite weighted derivative budget" on `s ≤ Σ/ν`), 291-303
(`sct:comparison`, one order at a time, unweighted), 463-467 (`sct:transverse`, the transverse tails
with `P_{S_*}` polynomial in `1 + S_*`), 541-543 ("`sct:comparison`, interpolated with the
just-proved doubled weights, proves fixed-band comparison for velocity and vorticity").

`FmrTrainClose` asks, for `b > 0` and `ν` small, on `0 ≤ s ≤ (νb)⁻¹/ν` (so `a = 1 + νs ≲ (νb)⁻¹`
and `c²/a ≳ b ν⁻³`, `c = ν⁻²`), that `‖D^j(v - V_c^p)‖ ⟨x⟩⁸ ≤ 1` on the centered cell for `j ≤ 4`.

The unweighted comparison `Spine.TrainPreError` (`j ≤ 3`) and `PartI.TrainComparison` carry no
weight, so they cannot give this alone: the weight is the source's interpolation (SP 541-543).  With
`E = ‖D^j(v - V_c^p)(x)‖`, `J = ⟨x⟩⁸`:
`(E J)² = E · (E J²) ≤ ‖D^j(v - V_c^p)‖_∞ · ‖⟨x⟩¹⁶ D^j(v - V_c^p)‖_{L^∞(cell)}`.
The first factor is `≤ ν⁻¹·C e^{-b_j c²/a}` by `PartI.TrainComparison` (`ρ = 2`, each `j`, not only
`j ≤ 3`).  The second is polynomial in `ν⁻¹`:
* for `|η| ≥ C'/ν + 2 + l`, `‖D^j v‖ ≤ P_{S_*}{e^{-bl/c} + e^{-bl²/(C₀+νS_*)}}` by
  `PartI.TrainTransverseTails` (`ℓ = 0`) at `S_* = (νb)⁻¹/ν`, and `‖D^j V_c^p‖ ⟨η⟩¹⁶ ≤ C a⁸` by
  `Train.Vc_bounds` (the fixed weight in units of `√a`, SP 338);
* on `|η| < C'/ν + 2` the weight is itself polynomial (`|q| ≤ c/2` on the cell), and the
  comparison alone closes.
At `s = 0` the difference vanishes (`v(0) = V_c^p(0)`, the datum, SP 261-265).

`fmrTrainClose_of (hC : PartI.TrainComparison) (hT : PartI.TrainTransverseTails) : FmrTrainClose`
is the theorem; it is unconditional once the Part I tasks `PartI:T10`, `PartI:T24` are proved.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa

namespace FmrTC

/-! ### Real-variable calculus -/

/-- Absorption of a power by the exponential, with an explicit threshold. -/
theorem pow_mul_exp_neg_le_one {β y : ℝ} (hβ : 0 < β) (hy : 0 < y) (M : ℕ)
    (hY : ((M + 1).factorial : ℝ) / β ^ (M + 1) ≤ y) :
    y ^ M * Real.exp (-(β * y)) ≤ 1 := by
  have hexp := Real.pow_div_factorial_le_exp (x := β * y) (by positivity) (M + 1)
  have hβ' : 0 < β ^ (M + 1) := pow_pos hβ _
  have hf : (0 : ℝ) < ((M + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have h1 : ((M + 1).factorial : ℝ) ≤ y * β ^ (M + 1) := (div_le_iff₀ hβ').1 hY
  have h2 : y ^ M ≤ (β * y) ^ (M + 1) / ((M + 1).factorial : ℝ) := by
    rw [le_div_iff₀ hf, mul_pow, pow_succ y M]
    calc y ^ M * ((M + 1).factorial : ℝ) ≤ y ^ M * (y * β ^ (M + 1)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = β ^ (M + 1) * (y ^ M * y) := by ring
  have h3 : y ^ M ≤ Real.exp (β * y) := h2.trans hexp
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
  exact h3

/-- `(1+u)^n e^{-u} ≤ n! e` for `u ≥ 0`. -/
theorem one_add_pow_mul_exp_neg_le {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    (1 + u) ^ n * Real.exp (-u) ≤ (n.factorial : ℝ) * Real.exp 1 := by
  have h := Real.pow_div_factorial_le_exp (x := 1 + u) (by linarith) n
  have hf : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  rw [div_le_iff₀ hf, Real.exp_add] at h
  have he : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  calc (1 + u) ^ n * Real.exp (-u)
      ≤ (Real.exp 1 * Real.exp u * (n.factorial : ℝ)) * Real.exp (-u) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = (n.factorial : ℝ) * Real.exp 1 * (Real.exp u * Real.exp (-u)) := by ring
    _ = (n.factorial : ℝ) * Real.exp 1 := by rw [he, mul_one]

/-- The Gaussian tail is dominated by the exponential tail at rate `bt/c`:
`bt l²/W ≥ bt l/c - bt W/(4c²)`. -/
theorem exp_gauss_le {bt c W : ℝ} (l : ℝ) (hbt : 0 ≤ bt) (hc : 0 < c) (hW : 0 < W) :
    Real.exp (-(bt * l ^ 2 / W)) ≤
      Real.exp (-(bt * l / c)) * Real.exp (bt * W / (4 * c ^ 2)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have key : l ^ 2 / W - l / c + W / (4 * c ^ 2) = (2 * c * l - W) ^ 2 / (4 * c ^ 2 * W) := by
    field_simp
    ring
  have h : 0 ≤ bt * (l ^ 2 / W - l / c + W / (4 * c ^ 2)) := by
    rw [key]
    positivity
  have e : bt * (l ^ 2 / W - l / c + W / (4 * c ^ 2)) =
      bt * l ^ 2 / W - bt * l / c + bt * W / (4 * c ^ 2) := by ring
  linarith

/-- The polynomial weight at distance `R + l` is absorbed by `e^{-bt l/c}`. -/
theorem weight_mul_exp_le {bt c R l η : ℝ} (hbt : 0 < bt) (hc : 0 < c) (hR : 0 ≤ R) (hl : 0 ≤ l)
    (hη : |η| = R + l) :
    (1 + η ^ 2) ^ 8 * Real.exp (-(bt * l / c)) ≤
      (1 + R + c / bt) ^ 16 * (((16 : ℕ).factorial : ℝ) * Real.exp 1) := by
  set u : ℝ := bt * l / c with hu
  have hu0 : 0 ≤ u := by positivity
  have hl' : l = c / bt * u := by
    rw [hu]
    field_simp
  have hcb : 0 ≤ c / bt := by positivity
  have h1 : 1 + |η| ≤ (1 + R + c / bt) * (1 + u) := by
    have e : (1 + R + c / bt) * (1 + u) = 1 + (R + c / bt * u) + (c / bt + (1 + R) * u) := by ring
    have h0 : 0 ≤ (1 + R) * u := mul_nonneg (by linarith) hu0
    rw [e, hη, ← hl']
    linarith
  have h2 : 1 + η ^ 2 ≤ (1 + |η|) ^ 2 := by
    have h3 := abs_nonneg η
    have h4 : |η| ^ 2 = η ^ 2 := sq_abs η
    have e : (1 + |η|) ^ 2 = 1 + 2 * |η| + |η| ^ 2 := by ring
    rw [e, h4]
    linarith
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = 1 + R + c / bt := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  rw [← hX] at h1 ⊢
  have h3 : (1 + η ^ 2) ^ 8 ≤ (X * (1 + u)) ^ 16 := by
    have h4 : 1 + η ^ 2 ≤ (X * (1 + u)) ^ 2 :=
      h2.trans (pow_le_pow_left₀ (by positivity) h1 2)
    calc (1 + η ^ 2) ^ 8 ≤ ((X * (1 + u)) ^ 2) ^ 8 :=
          pow_le_pow_left₀ (by positivity) h4 8
      _ = (X * (1 + u)) ^ 16 := by rw [← pow_mul]
  have h5 := one_add_pow_mul_exp_neg_le hu0 16
  calc (1 + η ^ 2) ^ 8 * Real.exp (-u)
      ≤ (X * (1 + u)) ^ 16 * Real.exp (-u) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    _ = X ^ 16 * ((1 + u) ^ 16 * Real.exp (-u)) := by rw [mul_pow, mul_assoc]
    _ ≤ X ^ 16 * (((16 : ℕ).factorial : ℝ) * Real.exp 1) :=
        mul_le_mul_of_nonneg_left h5 (by positivity)

/-- The interpolation of SP 541-543: `E ≤ Sm`, `E J² ≤ Bg`, `Sm Bg ≤ 1` give `E J ≤ 1`. -/
theorem interp_le_one {E J Sm Bg : ℝ} (hE : 0 ≤ E) (hJ : 0 ≤ J) (h1 : E ≤ Sm) (h2 : E * J ^ 2 ≤ Bg)
    (h3 : Sm * Bg ≤ 1) : E * J ≤ 1 := by
  have h0 : 0 ≤ E * J ^ 2 := by positivity
  have h4 : (E * J) ^ 2 ≤ 1 := by
    calc (E * J) ^ 2 = E * (E * J ^ 2) := by ring
      _ ≤ Sm * Bg := mul_le_mul h1 h2 h0 (hE.trans h1)
      _ ≤ 1 := h3
  have h5 : 0 ≤ E * J := by positivity
  exact (pow_le_one_iff_of_nonneg h5 (by norm_num)).1 h4

/-- The comparison factor in the regime `a ≲ y/b`, `c = y²`, `y = ν⁻¹`. -/
theorem small_num {y b bc Cc a e β E : ℝ} (hy : 4 ≤ y) (hb : 0 < b) (hbc : 0 < bc)
    (hCc : Cc ≤ y) (hby : b ≤ y) (ha1 : 1 ≤ a) (hay : a ≤ 1 + y * b⁻¹) (hβ : β = bc * b / 2)
    (he : e ≤ 0) (hE : E ≤ Cc * y * a ^ e * Real.exp (-(bc * (y ^ 2) ^ 2 / a))) :
    E ≤ y ^ 2 * Real.exp (-(β * y)) := by
  have hy0 : 0 < y := by linarith
  have hapos : 0 < a := by linarith
  have hae : a ^ e ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ha1 he
  have hae0 : 0 ≤ a ^ e := Real.rpow_nonneg hapos.le _
  have h1 : 1 ≤ y * b⁻¹ := by
    rw [← div_eq_mul_inv, one_le_div hb]
    exact hby
  have ha2 : a ≤ 2 * (y * b⁻¹) := by linarith
  have hexp : β * y ≤ bc * (y ^ 2) ^ 2 / a := by
    rw [le_div_iff₀ hapos, hβ]
    have h2 : b / 2 * y * a ≤ y ^ 2 := by
      calc b / 2 * y * a ≤ b / 2 * y * (2 * (y * b⁻¹)) :=
            mul_le_mul_of_nonneg_left ha2 (by positivity)
        _ = y ^ 2 := by field_simp
    have h3 : y ^ 2 ≤ (y ^ 2) ^ 2 := by
      have h1' : 1 ≤ y ^ 2 := one_le_pow₀ (by linarith)
      calc y ^ 2 = y ^ 2 * 1 := (mul_one _).symm
        _ ≤ y ^ 2 * y ^ 2 := mul_le_mul_of_nonneg_left h1' (by positivity)
        _ = (y ^ 2) ^ 2 := by ring
    calc bc * b / 2 * y * a = bc * (b / 2 * y * a) := by ring
      _ ≤ bc * (y ^ 2) ^ 2 := mul_le_mul_of_nonneg_left (h2.trans h3) hbc.le
  have hee : Real.exp (-(bc * (y ^ 2) ^ 2 / a)) ≤ Real.exp (-(β * y)) :=
    Real.exp_le_exp.2 (by linarith)
  have hexp0 : 0 ≤ Real.exp (-(bc * (y ^ 2) ^ 2 / a)) := (Real.exp_pos _).le
  have hCy : Cc * y ≤ y * y := mul_le_mul_of_nonneg_right hCc hy0.le
  calc E ≤ Cc * y * a ^ e * Real.exp (-(bc * (y ^ 2) ^ 2 / a)) := hE
    _ ≤ y * y * 1 * Real.exp (-(β * y)) := by
        refine mul_le_mul (mul_le_mul hCy hae hae0 (by positivity)) hee hexp0 (by positivity)
    _ = y ^ 2 * Real.exp (-(β * y)) := by ring

/-- The doubled-weight factor on the transverse tail, in powers of `y = ν⁻¹`. -/
theorem tail_num {y b bt C₀ C' Ct Cv a A B η l : ℝ} {Nt : ℕ} (hy : 4 ≤ y) (hb : 0 < b)
    (hbt : 0 < bt) (hC₀ : 0 < C₀) (hC' : 0 < C') (hCt : 0 < Ct)
    (hbty : bt ≤ y) (hbtiy : bt⁻¹ ≤ y) (hC₀y : C₀ ≤ y) (hC'y : C' ≤ y) (hCty : Ct ≤ y) (hCvy : Cv ≤ y)
    (hbiy : b⁻¹ ≤ y) (hDy : ((16 : ℕ).factorial : ℝ) * Real.exp 1 ≤ y)
    (ha1 : 1 ≤ a) (hay : a ≤ 1 + y * b⁻¹) (hl : 0 ≤ l) (hη : |η| = C' * y + 2 + l)
    (hA : A ≤ Ct * ((1 + y ^ 2 + y) * (1 + y ^ 2 * b⁻¹)) ^ Nt *
      (Real.exp (-(bt * l / y ^ 2)) + Real.exp (-(bt * l ^ 2 / (C₀ + y * b⁻¹)))))
    (hB : B * (1 + η ^ 2) ^ 8 ≤ Cv * a ^ 8) :
    (A + B) * (1 + η ^ 2) ^ 8 ≤ y ^ (7 * Nt + 68) := by
  have hy0 : 0 < y := by linarith
  have hy1 : 1 ≤ y := by linarith
  have hbi : 0 < b⁻¹ := inv_pos.2 hb
  have hbti : 0 < bt⁻¹ := inv_pos.2 hbt
  have hy2 : 16 ≤ y ^ 2 := by
    calc (16 : ℝ) = 4 ^ 2 := by norm_num
      _ ≤ y ^ 2 := pow_le_pow_left₀ (by norm_num) hy 2
  have hy3' : 64 ≤ y ^ 3 := by
    calc (64 : ℝ) = 4 ^ 3 := by norm_num
      _ ≤ y ^ 3 := pow_le_pow_left₀ (by norm_num) hy 3
  have hyy : y * y = y ^ 2 := by ring
  have hyy2 : y ≤ y ^ 2 := by
    rw [← hyy]
    exact le_mul_of_one_le_right hy0.le hy1
  have h4y2 : 4 * y ^ 2 ≤ y ^ 3 := by
    have e : y ^ 3 = y * y ^ 2 := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hy (by positivity)
  have h4y3 : 4 * y ^ 3 ≤ y ^ 4 := by
    have e : y ^ 4 = y * y ^ 3 := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hy (by positivity)
  have hc0 : 0 < y ^ 2 := by positivity
  set R : ℝ := C' * y + 2 with hR
  have hR0 : 0 ≤ R := by positivity
  have hRy : R ≤ y ^ 3 := by
    have : C' * y ≤ y * y := mul_le_mul_of_nonneg_right hC'y hy0.le
    rw [hR]
    linarith
  have hη' : |η| = R + l := by rw [hR, hη]
  set W8 : ℝ := (1 + η ^ 2) ^ 8 with hW8
  have hW80 : 0 ≤ W8 := by positivity
  set e1 : ℝ := Real.exp (-(bt * l / y ^ 2)) with he1
  have he10 : 0 < e1 := Real.exp_pos _
  -- the weight against the exponential
  have hw : W8 * e1 ≤ (y ^ 4) ^ 16 * y := by
    have h1 := weight_mul_exp_le (c := y ^ 2) hbt hc0 hR0 hl hη'
    have h2 : 1 + R + y ^ 2 / bt ≤ y ^ 4 := by
      have h3 : y ^ 2 / bt ≤ y ^ 3 := by
        have e : y ^ 3 = y ^ 2 * y := by ring
        rw [div_eq_mul_inv, e]
        exact mul_le_mul_of_nonneg_left hbtiy (by positivity)
      linarith
    have h4 : 0 ≤ 1 + R + y ^ 2 / bt := by positivity
    calc W8 * e1 ≤ (1 + R + y ^ 2 / bt) ^ 16 * (((16 : ℕ).factorial : ℝ) * Real.exp 1) := h1
      _ ≤ (y ^ 4) ^ 16 * y :=
        mul_le_mul (pow_le_pow_left₀ h4 h2 16) hDy (by positivity) (by positivity)
  -- the Gaussian tail
  set W : ℝ := C₀ + y * b⁻¹ with hW
  have hW0 : 0 < W := by positivity
  have hbW : bt * W / (4 * (y ^ 2) ^ 2) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have h1 : W ≤ y + y * y := by
      rw [hW]
      exact add_le_add hC₀y (mul_le_mul_of_nonneg_left hbiy hy0.le)
    have h2 : bt * W ≤ y * (y + y * y) := mul_le_mul hbty h1 hW0.le hy0.le
    have h3 : (y ^ 2) ^ 2 = y ^ 2 * y ^ 2 := by ring
    have h4 : y * (y + y * y) = y ^ 2 + y ^ 3 := by ring
    have h5 : y ^ 2 ≤ y ^ 2 * y ^ 2 := le_mul_of_one_le_right hc0.le (by linarith)
    have h6 : y ^ 3 ≤ y ^ 2 * y ^ 2 := by
      have e : y ^ 2 * y ^ 2 = y * y ^ 3 := by ring
      rw [e]
      exact le_mul_of_one_le_left (by positivity) hy1
    rw [h3]
    rw [h4] at h2
    linarith
  have he2 : Real.exp (-(bt * l ^ 2 / W)) ≤ e1 * Real.exp 1 :=
    (exp_gauss_le l hbt.le hc0 hW0).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hbW) he10.le)
  -- the polynomial
  have hP : Ct * ((1 + y ^ 2 + y) * (1 + y ^ 2 * b⁻¹)) ^ Nt ≤ y ^ (7 * Nt + 1) := by
    have h1 : 1 + y ^ 2 + y ≤ y ^ 3 := by linarith
    have h2 : y ^ 2 * b⁻¹ ≤ y ^ 3 := by
      have e : y ^ 3 = y ^ 2 * y := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_left hbiy (by positivity)
    have h3 : 1 + y ^ 2 * b⁻¹ ≤ y ^ 4 := by linarith
    have h4 : (1 + y ^ 2 + y) * (1 + y ^ 2 * b⁻¹) ≤ y ^ 3 * y ^ 4 :=
      mul_le_mul h1 h3 (by positivity) (by positivity)
    have h5 : ((1 + y ^ 2 + y) * (1 + y ^ 2 * b⁻¹)) ^ Nt ≤ (y ^ 3 * y ^ 4) ^ Nt :=
      pow_le_pow_left₀ (by positivity) h4 Nt
    calc Ct * ((1 + y ^ 2 + y) * (1 + y ^ 2 * b⁻¹)) ^ Nt ≤ y * (y ^ 3 * y ^ 4) ^ Nt :=
          mul_le_mul hCty h5 (by positivity) hy0.le
      _ = y ^ (7 * Nt + 1) := by
          rw [← pow_add, ← pow_mul]
          ring
  set P : ℝ := Ct * ((1 + y ^ 2 + y) * (1 + y ^ 2 * b⁻¹)) ^ Nt with hPdef
  have hP0 : 0 ≤ P := by positivity
  have hexp1 : 1 + Real.exp 1 ≤ y := by
    have := Real.exp_one_lt_three
    linarith
  -- the velocity term
  have hAW : A * W8 ≤ y ^ (7 * Nt + 67) := by
    have h1 : A ≤ P * (e1 * (1 + Real.exp 1)) := by
      refine hA.trans (mul_le_mul_of_nonneg_left ?_ hP0)
      linarith
    calc A * W8 ≤ P * (e1 * (1 + Real.exp 1)) * W8 := mul_le_mul_of_nonneg_right h1 hW80
      _ = P * (1 + Real.exp 1) * (W8 * e1) := by ring
      _ ≤ y ^ (7 * Nt + 1) * y * ((y ^ 4) ^ 16 * y) := by
          refine mul_le_mul (mul_le_mul hP hexp1 (by positivity) (by positivity)) hw
            (by positivity) (by positivity)
      _ = y ^ (7 * Nt + 67) := by ring
  -- the vortex term
  have hBW : B * W8 ≤ y ^ (7 * Nt + 67) := by
    have h1 : a ≤ y ^ 3 := by
      have : y * b⁻¹ ≤ y * y := mul_le_mul_of_nonneg_left hbiy hy0.le
      linarith
    have h2 : a ^ 8 ≤ (y ^ 3) ^ 8 := pow_le_pow_left₀ (by linarith) h1 8
    calc B * W8 ≤ Cv * a ^ 8 := hB
      _ ≤ y * (y ^ 3) ^ 8 := mul_le_mul hCvy h2 (by positivity) hy0.le
      _ = y ^ 25 := by ring
      _ ≤ y ^ (7 * Nt + 67) := pow_le_pow_right₀ hy1 (by omega)
  have hpos : 0 ≤ y ^ (7 * Nt + 67) := by positivity
  calc (A + B) * W8 = A * W8 + B * W8 := by ring
    _ ≤ y ^ (7 * Nt + 67) + y ^ (7 * Nt + 67) := add_le_add hAW hBW
    _ ≤ y * y ^ (7 * Nt + 67) := by
        have := mul_le_mul_of_nonneg_right (by linarith : (2 : ℝ) ≤ y) hpos
        linarith
    _ = y ^ (7 * Nt + 68) := by ring

/-- On the cell, `⟨x⟩² ≤ (1 + c²)(1 + η²)`. -/
theorem jb_le_of_mem_cell {c : ℝ} {x : B0579.Plane} (hx : x ∈ B0579.cell c) (hc : 0 < c) :
    B0579.jb x ≤ (1 + c ^ 2) * (1 + x.2 ^ 2) := by
  have h1 := hx.1
  have hq : x.1 ^ 2 ≤ c ^ 2 := by
    have h2 : -(c / 2) ≤ x.1 := h1.1
    have h3 : x.1 < c / 2 := h1.2
    exact sq_le_sq' (by linarith) (by linarith)
  have h4 : 0 ≤ c ^ 2 * x.2 ^ 2 := by positivity
  have e : (1 + c ^ 2) * (1 + x.2 ^ 2) = 1 + c ^ 2 + x.2 ^ 2 + c ^ 2 * x.2 ^ 2 := by ring
  unfold B0579.jb
  rw [e]
  linarith

/-! ### The periodized vortex with the doubled weight -/

/-- `Train.Vc_bounds` (SP 327-338, the fixed weight in units of `√a`) with the unit weight:
`‖D^j V_c^p(z)‖ ⟨η⟩¹⁶ ≤ C a⁸`. -/
theorem Vc_weighted (j : ℕ) :
    ∃ Cv : ℝ, 0 ≤ Cv ∧ ∀ ν c s : ℝ, 0 < c → 1 ≤ Train.width ν s → Train.width ν s ≤ c ^ 2 →
      ∀ z : ℝ × ℝ, ‖iteratedFDeriv ℝ j (Train.Vc ν c s) z‖ * (1 + z.2 ^ 2) ^ 8 ≤
        Cv * Train.width ν s ^ 8 := by
  obtain ⟨C, b, hC, hb, h⟩ := Train.Vc_bounds j 8
  refine ⟨2 ^ (j + 1) * C, by positivity, fun ν c s hc ha1 hac z => ?_⟩
  have ha0 : (0 : ℝ) < Train.width ν s := lt_of_lt_of_le one_pos ha1
  have hsm : ContDiff ℝ ∞ (Train.Vc ν c s) := Spine.vcReg_contDiff_Vc hc ha0
  obtain ⟨h1, -, -⟩ := h ν c s hc ha1 hac
  set a : ℝ := Train.width ν s with ha
  set P : ℝ := (1 + z.2 ^ 2) ^ 8 with hP
  have hPpos : 0 < P := by positivity
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hrp : a ^ (-(3 + (j : ℝ)) / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos ha1 (by linarith)
  have hweight : P ≤ a ^ 8 * (1 + z.2 ^ 2 / a) ^ 8 := by
    rw [← mul_pow, hP]
    refine pow_le_pow_left₀ (by positivity) ?_ 8
    have : a * (1 + z.2 ^ 2 / a) = a + z.2 ^ 2 := by field_simp
    rw [this]
    linarith
  have hk : ∀ k : Fin 2, ‖iteratedFDeriv ℝ j (fun x => Train.Vc ν c s x k) z‖ ≤
      2 ^ j * (C * a ^ 8 / P) := by
    intro k
    have hfk : ContDiff ℝ ∞ (fun x => Train.Vc ν c s x k) :=
      (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hsm
    refine Spine.norm_iteratedFDeriv_le_of_derivWord hfk j z ?_
    intro w hw
    have hw' := h1 w hw k z
    rw [le_div_iff₀ hPpos]
    have hD := abs_nonneg (B0151.derivWord w (fun x => Train.Vc ν c s x k) z)
    calc |B0151.derivWord w (fun x => Train.Vc ν c s x k) z| * P
        ≤ |B0151.derivWord w (fun x => Train.Vc ν c s x k) z| * (a ^ 8 * (1 + z.2 ^ 2 / a) ^ 8) :=
          mul_le_mul_of_nonneg_left hweight hD
      _ = a ^ 8 * ((1 + z.2 ^ 2 / a) ^ 8 *
            |B0151.derivWord w (fun x => Train.Vc ν c s x k) z|) := by ring
      _ ≤ a ^ 8 * (C * a ^ (-(3 + (j : ℝ)) / 2)) :=
          mul_le_mul_of_nonneg_left hw' (by positivity)
      _ ≤ a ^ 8 * (C * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrp hC) (by positivity)
      _ = C * a ^ 8 := by ring
  have hsum := Spine.norm_iteratedFDeriv_euclid2_le hsm j z
  have h2 := add_le_add (hk 0) (hk 1)
  calc ‖iteratedFDeriv ℝ j (Train.Vc ν c s) z‖ * P
      ≤ (2 ^ j * (C * a ^ 8 / P) + 2 ^ j * (C * a ^ 8 / P)) * P :=
        mul_le_mul_of_nonneg_right (hsum.trans h2) hPpos.le
    _ = 2 ^ (j + 1) * C * a ^ 8 := by
        field_simp
        ring

/-! ### Train facts -/

theorem ageJet_zero_eq (j : ℕ) (F : ℝ → ℝ × ℝ → Train.Vec) (s : ℝ) :
    PartI.ageJet 0 j F s = iteratedFDeriv ℝ j (F s) := by
  funext z
  simp only [PartI.ageJet, Train.jet, iteratedDeriv_zero]

theorem contDiff_train {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s) :
    ContDiff ℝ ∞ (tr.v s) := by
  have h := tr.isTrain.smooth_v.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (s := Set.univ) (fun z _ => ⟨Set.mem_Ici.2 hs, Set.mem_univ z⟩)
  exact contDiffOn_univ.1 h

/-- `‖D^j(v - V_c^p)‖ ≤ ‖D^j v‖ + ‖D^j V_c^p‖` at positive width. -/
theorem norm_diff_le {ν c s : ℝ} (tr : B0140.TrainSol ν c) (hs : 0 ≤ s) (hc : 0 < c)
    (ha : 0 < Train.width ν s) (j : ℕ) (x : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ j (fun z => tr.v s z - Train.Vc ν c s z) x‖ ≤
      ‖iteratedFDeriv ℝ j (tr.v s) x‖ + ‖iteratedFDeriv ℝ j (Train.Vc ν c s) x‖ := by
  have h1 : ContDiffAt ℝ j (tr.v s) x :=
    ((contDiff_train tr hs).of_le (by exact_mod_cast le_top)).contDiffAt
  have h2 : ContDiffAt ℝ j (Train.Vc ν c s) x :=
    ((Spine.vcReg_contDiff_Vc hc ha).of_le (by exact_mod_cast le_top)).contDiffAt
  have e : iteratedFDeriv ℝ j (fun z => tr.v s z - Train.Vc ν c s z) x =
      iteratedFDeriv ℝ j (tr.v s) x - iteratedFDeriv ℝ j (Train.Vc ν c s) x :=
    iteratedFDeriv_sub_apply h1 h2
  rw [e]
  exact norm_sub_le _ _

/-- At age `0` the train is the periodized vortex (`v(0) = V_c^p(0)`, the datum, SP 261-265). -/
theorem trainDiff_zero {ν c : ℝ} (tr : B0140.TrainSol ν c) :
    (fun z => tr.v 0 z - Train.Vc ν c 0 z) = fun _ => 0 := by
  funext z
  rw [tr.isTrain.initial, B0169.trainDatum_eq_datum, Train.Vc_zero, sub_self]

/-! ### One order at a time -/

/-- **The weighted comparison at order `j`** on `0 < s ≤ (νb)⁻¹/ν`, for `ν` small. -/
theorem trainClose_order (hC : PartI.TrainComparison) (hT : PartI.TrainTransverseTails)
    {b : ℝ} (hb : 0 < b) (j : ℕ) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀, ∀ tr : B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      PartI.IsBUCTrain tr → ∀ s : ℝ, 0 < s → s ≤ (ν * b)⁻¹ / ν →
        ∀ x ∈ B0579.cell (ν ^ (-2 : ℝ)),
          ‖iteratedFDeriv ℝ j (fun z => tr.v s z - Train.Vc ν (ν ^ (-2 : ℝ)) s z) x‖ *
            B0579.jb x ^ 4 ≤ 1 := by
  obtain ⟨Cc, bc, νc, hCc, hbc, hνc, HC⟩ := hC 2 (by norm_num) j
  obtain ⟨bt, C₀, C', hbt, hC₀, hC', Ct, Nt, νt, hCt, hνt, HT⟩ := hT 2 (by norm_num) 0 j
  obtain ⟨Cv, hCv, HV⟩ := Vc_weighted j
  have hβ : 0 < bc * b / 2 := by positivity
  have hbi : 0 < b⁻¹ := inv_pos.2 hb
  have hbti : 0 < bt⁻¹ := inv_pos.2 hbt
  have hDnn : 0 ≤ ((16 : ℕ).factorial : ℝ) * Real.exp 1 := by positivity
  have hFnn : 0 ≤ (((7 * Nt + 110 + 1).factorial : ℕ) : ℝ) / (bc * b / 2) ^ (7 * Nt + 110 + 1) := by
    positivity
  obtain ⟨K, hK4, hKCc, hKbt, hKbti, hKC', hKC₀, hKCt, hKCv, hKb, hKbi, hKD, hKF⟩ :
      ∃ K : ℝ, 4 ≤ K ∧ Cc ≤ K ∧ bt ≤ K ∧ bt⁻¹ ≤ K ∧ C' ≤ K ∧ C₀ ≤ K ∧ Ct ≤ K ∧ Cv ≤ K ∧ b ≤ K ∧
        b⁻¹ ≤ K ∧ ((16 : ℕ).factorial : ℝ) * Real.exp 1 ≤ K ∧
        (((7 * Nt + 110 + 1).factorial : ℕ) : ℝ) / (bc * b / 2) ^ (7 * Nt + 110 + 1) ≤ K := by
    generalize ((16 : ℕ).factorial : ℝ) * Real.exp 1 = D at hDnn ⊢
    generalize (((7 * Nt + 110 + 1).factorial : ℕ) : ℝ) / (bc * b / 2) ^ (7 * Nt + 110 + 1) = F
      at hFnn ⊢
    generalize b⁻¹ = bi at hbi ⊢
    generalize bt⁻¹ = bti at hbti ⊢
    refine ⟨4 + Cc + bt + bti + C' + C₀ + Ct + Cv + b + bi + D + F,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  have hKpos : 0 < K := by linarith
  refine ⟨min νc (min νt K⁻¹), lt_min hνc (lt_min hνt (inv_pos.2 hKpos)), ?_⟩
  intro ν hν tr htr s hs hsS x hx
  have hν0 : 0 < ν := hν.1
  have hνc' : ν ≤ νc := hν.2.trans (min_le_left _ _)
  have hνt' : ν ≤ νt := hν.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hνK : ν ≤ K⁻¹ := hν.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  -- `y = ν⁻¹` and its relatives
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
    have h4 : y * y = y ^ 2 := by ring
    have h5 : 0 < y ^ 2 := by positivity
    rw [h2]
    linarith
  -- the comparison
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E =
      ‖iteratedFDeriv ℝ j (fun z => tr.v s z - Train.Vc ν (ν ^ (-2 : ℝ)) s z) x‖ := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by rw [hEdef]; positivity
  rw [← hEdef]
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
    rw [hEdef, ← hRHS]
    exact H2
  set β : ℝ := bc * b / 2 with hβdef
  have hSm : E ≤ y ^ 2 * Real.exp (-(β * y)) := by
    have he : -((5 + (j : ℝ)) / 2) ≤ 0 := by
      have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    exact small_num hy4 hb hbc (hKCc.trans hyK) (hKb.trans hyK) ha1 hay hβdef he hEsup
  -- the absorption of all powers of `y`
  have hab : y ^ 2 * Real.exp (-(β * y)) * y ^ (7 * Nt + 108) ≤ 1 := by
    have h1 := pow_mul_exp_neg_le_one hβ hy0 (7 * Nt + 110) (hKF.trans hyK)
    calc y ^ 2 * Real.exp (-(β * y)) * y ^ (7 * Nt + 108)
        = y ^ (7 * Nt + 110) * Real.exp (-(β * y)) := by ring
      _ ≤ 1 := h1
  have hjbnn : 0 ≤ B0579.jb x := (B0579.jb_pos x).le
  have hjb := jb_le_of_mem_cell hx hc0
  rw [hcy] at hjb
  have hc2 : 1 + (y ^ 2) ^ 2 ≤ y ^ 5 := by
    have h1 : y ^ 5 = y * (y ^ 2) ^ 2 := by ring
    have h2 : 1 ≤ (y ^ 2) ^ 2 := one_le_pow₀ (by linarith)
    have h3 : 4 * (y ^ 2) ^ 2 ≤ y * (y ^ 2) ^ 2 := mul_le_mul_of_nonneg_right hy4 (by positivity)
    rw [h1]
    linarith
  by_cases hz : C' / ν + 2 ≤ |x.2|
  · -- the transverse tail: interpolate with the doubled weight
    obtain ⟨l, hl⟩ : ∃ l : ℝ, l = |x.2| - (C' / ν + 2) := ⟨_, rfl⟩
    have hl0 : 0 ≤ l := by rw [hl]; linarith
    have hη : |x.2| = C' * y + 2 + l := by
      rw [hl, hy, div_eq_mul_inv]
      ring
    have hz' : C' / ν + 2 + l ≤ |x.2| := by rw [hl]; linarith
    have hTail := HT ((ν * b)⁻¹ / ν) hS0 ν hν0 hνt' tr htr l hl0 s hs hsS x hz'
    obtain ⟨-, hA, -⟩ := hTail
    rw [ageJet_zero_eq] at hA
    have hper : PartI.trainPeriod 2 ν = y ^ 2 := hcy
    have hA' : ‖iteratedFDeriv ℝ j (tr.v s) x‖ ≤
        Ct * ((1 + y ^ 2 + y) * (1 + y ^ 2 * b⁻¹)) ^ Nt *
          (Real.exp (-(bt * l / y ^ 2)) + Real.exp (-(bt * l ^ 2 / (C₀ + y * b⁻¹)))) := by
      have h := hA
      simp only [PartI.polyPS, hper, hνS, ← hy] at h
      rw [hS] at h
      exact h
    have hB := HV ν (ν ^ (-2 : ℝ)) s hc0 ha1 hac x
    have hbig := tail_num hy4 hb hbt hC₀ hC' hCt (hKbt.trans hyK) (hKbti.trans hyK)
      (hKC₀.trans hyK) (hKC'.trans hyK) (hKCt.trans hyK) (hKCv.trans hyK) (hKbi.trans hyK)
      (hKD.trans hyK) ha1 hay hl0 hη hA' hB
    have hEle : E ≤ ‖iteratedFDeriv ℝ j (tr.v s) x‖ + ‖iteratedFDeriv ℝ j (Train.Vc ν (ν ^ (-2 : ℝ)) s) x‖ := by
      rw [hEdef]
      exact norm_diff_le tr hs.le hc0 ha0 j x
    have hEW : E * (1 + x.2 ^ 2) ^ 8 ≤ y ^ (7 * Nt + 68) :=
      (mul_le_mul_of_nonneg_right hEle (by positivity)).trans hbig
    have hJ : E * (B0579.jb x ^ 4) ^ 2 ≤ y ^ (7 * Nt + 108) := by
      have h1 : B0579.jb x ^ 8 ≤ ((y ^ 5) * (1 + x.2 ^ 2)) ^ 8 := by
        refine pow_le_pow_left₀ hjbnn (hjb.trans ?_) 8
        exact mul_le_mul_of_nonneg_right hc2 (by positivity)
      calc E * (B0579.jb x ^ 4) ^ 2 = E * B0579.jb x ^ 8 := by rw [← pow_mul]
        _ ≤ E * ((y ^ 5) * (1 + x.2 ^ 2)) ^ 8 := mul_le_mul_of_nonneg_left h1 hE0
        _ = y ^ 40 * (E * (1 + x.2 ^ 2) ^ 8) := by
            rw [mul_pow, ← pow_mul]
            ring
        _ ≤ y ^ 40 * y ^ (7 * Nt + 68) := mul_le_mul_of_nonneg_left hEW (by positivity)
        _ = y ^ (7 * Nt + 108) := by ring
    exact interp_le_one hE0 (by positivity) hSm hJ hab
  · -- `|η| < C'/ν + 2`: the weight is polynomial, the comparison alone closes
    have hR : |x.2| < C' * y + 2 := by
      rw [hy, ← div_eq_mul_inv]
      exact not_le.1 hz
    have hRy : C' * y + 2 ≤ y ^ 3 := by
      have h1 : C' * y ≤ y * y := mul_le_mul_of_nonneg_right (hKC'.trans hyK) hy0.le
      have h2 : y ^ 3 = y * y ^ 2 := by ring
      have h3 : 4 * y ^ 2 ≤ y * y ^ 2 := mul_le_mul_of_nonneg_right hy4 (by positivity)
      have h4 : y * y = y ^ 2 := by ring
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
    have hJ : B0579.jb x ^ 4 ≤ y ^ (7 * Nt + 108) := by
      have h1 : B0579.jb x ≤ y ^ 12 := by
        calc B0579.jb x ≤ (1 + (y ^ 2) ^ 2) * (1 + x.2 ^ 2) := hjb
          _ ≤ y ^ 5 * y ^ 7 := mul_le_mul hc2 hη2 (by positivity) (by positivity)
          _ = y ^ 12 := by ring
      calc B0579.jb x ^ 4 ≤ (y ^ 12) ^ 4 := pow_le_pow_left₀ hjbnn h1 4
        _ = y ^ 48 := by ring
        _ ≤ y ^ (7 * Nt + 108) := pow_le_pow_right₀ hy1 (by omega)
    calc E * B0579.jb x ^ 4 ≤ y ^ 2 * Real.exp (-(β * y)) * y ^ (7 * Nt + 108) :=
          mul_le_mul hSm hJ (by positivity) (by positivity)
      _ ≤ 1 := hab

end FmrTC

/-- **`FmrTrainClose`** from the Part I train estimates (SP 2085-2090, 291-303, 463-467, 541-543):
`sct:comparison` interpolated with the doubled weights given by `sct:transverse`. -/
theorem fmrTrainClose_of (hC : UnforcedLeray.Short.PartI.TrainComparison)
    (hT : UnforcedLeray.Short.PartI.TrainTransverseTails) : FmrTrainClose := by
  intro b hb
  have key : ∀ n : ℕ, ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ j ≤ n, ∀ ν ∈ Ioc 0 ν₀,
      ∀ tr : B0140.TrainSol ν (ν ^ (-2 : ℝ)), PartI.IsBUCTrain tr →
        ∀ s : ℝ, 0 < s → s ≤ (ν * b)⁻¹ / ν → ∀ x ∈ B0579.cell (ν ^ (-2 : ℝ)),
          ‖iteratedFDeriv ℝ j (fun z => tr.v s z - Train.Vc ν (ν ^ (-2 : ℝ)) s z) x‖ *
            B0579.jb x ^ 4 ≤ 1 := by
    intro n
    induction n with
    | zero =>
        obtain ⟨ν₀, hν₀, H⟩ := FmrTC.trainClose_order hC hT hb 0
        exact ⟨ν₀, hν₀, fun j hj => by
          obtain rfl : j = 0 := by omega
          exact H⟩
    | succ n ih =>
        obtain ⟨ν₁, hν₁, H1⟩ := ih
        obtain ⟨ν₂, hν₂, H2⟩ := FmrTC.trainClose_order hC hT hb (n + 1)
        refine ⟨min ν₁ ν₂, lt_min hν₁ hν₂, fun j hj ν hν => ?_⟩
        rcases Nat.lt_or_ge j (n + 1) with h | h
        · exact H1 j (by omega) ν ⟨hν.1, hν.2.trans (min_le_left _ _)⟩
        · obtain rfl : j = n + 1 := by omega
          exact H2 ν ⟨hν.1, hν.2.trans (min_le_right _ _)⟩
  obtain ⟨ν₀, hν₀, H⟩ := key 4
  refine ⟨ν₀, hν₀, fun ν hν tr htr s hs0 hs x hx j hj => ?_⟩
  rcases hs0.eq_or_lt with rfl | hs0'
  · rw [FmrTC.trainDiff_zero tr, iteratedFDeriv_fun_zero]
    simp
  · exact H j hj ν hν tr htr s hs0' hs x hx

end UnforcedLeray.Short.IIIa
