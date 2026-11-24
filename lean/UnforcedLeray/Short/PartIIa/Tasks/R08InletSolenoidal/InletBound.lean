import UnforcedLeray.Short.PartIIa.Sub.R08
import UnforcedLeray.Units.B0140
import UnforcedLeray.Units.B0141.Datum

/-!
# Part II-a, task `PartII-a:R08`: the inlet bound `InletBound`

Source of record: `the November 2 reference manuscript`, lines 1330-1336 ("Each
derivative costs `C/r`; all powers of `|x|/r` are absorbed by the Gaussian decay in `η = Rz/r`").

This file proves the Prop `InletBound` of `Sub/R08.lean` for every `c > 0` and `R ≥ 2`.

Method. Let `S₀(q) = ∑ₙ e^{-(q-nc)²/4}` and `S₁(q) = ∑ₙ (q-nc) e^{-(q-nc)²/4}`
(`inletSum0`, `inletSum1`). Both are bounded in `q` for every `c > 0`
(`B0141.norm_periodize_le_bound`). The datum factorizes as
`trainStream c (q, η) = -2 e^{-η²/4} S₀(q)` (`trainStream_split`), and its `q`-derivative is
`e^{-η²/4} S₁(q)` (`hasDerivAt_inletSum0`, from `B0140.hasDerivAt_trainStream_q` at `η = 0`).
Off the axis, with `r = ϱ y`, `z = y₂`, `q = R log(r/R)`, `η = Rz/r`, `E = e^{-η²/4}`:
`∂_z 𝒫 = R η E S₀` and `∂_r 𝒫 = -2E S₀ - η²E S₀ + R E S₁`, where `𝒫 = inletStream c R`.
Hence `inletRaw = -(1/r) ∂_z𝒫 e_r + (1/r) ∂_r𝒫 e_z` has norm at most `(1/r) E B(η)` with
`B(η) = R|η|M₀ + 2M₀ + η²M₀ + RM₁`. Since `‖y‖ ≤ r(1 + |η|/R)` and `E(1+|η|)³ ≤ 64`, one gets
`‖inletRaw y‖ ‖y‖ ≤ 64 (R+2)(M₀+M₁)` off the axis. At axis points `x ≠ 0` the bound follows by
continuity of the extension along `x + t e₀`, `t ↓ 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIa

/-! ### 1. Lattice sums of the Gaussian datum -/

/-- The lattice sum `S₀(q) = ∑ₙ e^{-(q-nc)²/4}`. -/
def inletSum0 (c q : ℝ) : ℝ := ∑' n : ℤ, Real.exp (-((q - (n : ℝ) * c) ^ 2) / 4)

/-- The weighted lattice sum `S₁(q) = ∑ₙ (q-nc) e^{-(q-nc)²/4}`. -/
def inletSum1 (c q : ℝ) : ℝ :=
  ∑' n : ℤ, (q - (n : ℝ) * c) * Real.exp (-((q - (n : ℝ) * c) ^ 2) / 4)

/-- The Gaussian datum of `StatementsRing.lean` is the `B0140` train stream. -/
theorem trainDatum_eq_trainStream' (c q η : ℝ) :
    trainDatum c q η = UnforcedLeray.B0140.trainStream c (q, η) := by
  simp only [trainDatum, UnforcedLeray.B0140.trainStream_apply, tsum_mul_left, neg_div]

/-- Factorization of the datum stream: `ψ(q, η) = -2 e^{-η²/4} S₀(q)`. -/
theorem trainStream_split (c q η : ℝ) :
    UnforcedLeray.B0140.trainStream c (q, η) =
      -2 * Real.exp (-(η ^ 2) / 4) * inletSum0 c q := by
  rw [UnforcedLeray.B0140.trainStream_apply, inletSum0]
  have key : ∀ n : ℤ, Real.exp (-(((q - (n : ℝ) * c) ^ 2 + η ^ 2)) / 4) =
      Real.exp (-(η ^ 2) / 4) * Real.exp (-((q - (n : ℝ) * c) ^ 2) / 4) := by
    intro n
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [key]
  rw [tsum_mul_left]
  ring

/-- The second velocity component of a Gaussian: `v₀(x, η)₂ = e^{-η²/4} x e^{-x²/4}`. -/
theorem velocity_snd_split (x η : ℝ) :
    (UnforcedLeray.GaussianVortex.velocity (x, η)).2 =
      Real.exp (-(η ^ 2) / 4) * (x * Real.exp (-(x ^ 2) / 4)) := by
  rw [UnforcedLeray.B0140.velocity_apply]
  simp only [Prod.smul_mk, smul_eq_mul]
  rw [show -(x ^ 2 + η ^ 2) / 4 = -(η ^ 2) / 4 + -(x ^ 2) / 4 by ring, Real.exp_add]
  ring

/-- The second component of the train velocity: `(P_c v₀)₂(q, η) = e^{-η²/4} S₁(q)`. -/
theorem trainVelocity_snd_split {c : ℝ} (hc : c ≠ 0) (q η : ℝ) :
    (UnforcedLeray.B0140.trainVelocity c (q, η)).2 =
      Real.exp (-(η ^ 2) / 4) * inletSum1 c q := by
  have e : (UnforcedLeray.B0140.trainVelocity c (q, η)).2 =
      ∑' n : ℤ, (UnforcedLeray.GaussianVortex.velocity (q - (n : ℝ) * c, η)).2 :=
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).hasSum
      (UnforcedLeray.B0140.hasSum_trainVelocity hc (q, η))).tsum_eq.symm
  rw [e, inletSum1]
  simp only [velocity_snd_split]
  rw [tsum_mul_left]

/-- The `q`-derivative of `S₀` is `-S₁/2` (termwise differentiation is done by `B0140`). -/
theorem hasDerivAt_inletSum0 {c : ℝ} (hc : c ≠ 0) (q : ℝ) :
    HasDerivAt (inletSum0 c) (-(1 / 2 : ℝ) * inletSum1 c q) q := by
  have h : HasDerivAt (fun t => UnforcedLeray.B0140.trainStream c (t, 0))
      (UnforcedLeray.B0140.trainVelocity c (q, 0)).2 q :=
    UnforcedLeray.B0140.hasDerivAt_trainStream_q hc (q, 0)
  have h2 : HasDerivAt (fun t => -(1 / 2 : ℝ) * UnforcedLeray.B0140.trainStream c (t, 0))
      (-(1 / 2 : ℝ) * (UnforcedLeray.B0140.trainVelocity c (q, 0)).2) q := h.const_mul _
  have hfun : (fun t => -(1 / 2 : ℝ) * UnforcedLeray.B0140.trainStream c (t, 0)) =
      inletSum0 c := by
    funext t
    rw [trainStream_split]
    have h0 : Real.exp (-((0 : ℝ) ^ 2) / 4) = 1 := by simp
    rw [h0]
    ring
  have hval : (UnforcedLeray.B0140.trainVelocity c (q, 0)).2 = inletSum1 c q := by
    rw [trainVelocity_snd_split hc q 0]
    have h0 : Real.exp (-((0 : ℝ) ^ 2) / 4) = 1 := by simp
    rw [h0, one_mul]
  rw [hfun, hval] at h2
  exact h2

/-! ### 2. Uniform bounds on the lattice sums (any `c > 0`) -/

/-- Majorant for `e^{-x²/4}` with the decay `(1+|x|)^{-2}` required by the periodization bound. -/
theorem inletMaj0 (z : ℝ × ℝ) :
    ‖Real.exp (-(z.1 ^ 2) / 4)‖ ≤ 8 * (1 + |z.1|) ^ (-(2 : ℝ)) := by
  have hx : (0 : ℝ) < 1 + |z.1| := by positivity
  have hE : 0 < Real.exp (z.1 ^ 2 / 4) := Real.exp_pos _
  have hexp : Real.exp (-(z.1 ^ 2) / 4) = (Real.exp (z.1 ^ 2 / 4))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  have hpow : (1 + |z.1|) ^ (-(2 : ℝ)) = ((1 + |z.1|) ^ 2)⁻¹ := by
    rw [Real.rpow_neg hx.le, Real.rpow_two]
  have hkey : (1 + |z.1|) ^ 2 ≤ Real.exp (z.1 ^ 2 / 4) * 8 := by
    have h1 := Real.add_one_le_exp (z.1 ^ 2 / 4)
    have h2 := sq_abs z.1
    nlinarith [sq_nonneg (|z.1| - 1), abs_nonneg z.1]
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hexp, hpow]
  simp only [inv_eq_one_div, mul_one_div]
  rw [div_le_div_iff₀ hE (by positivity)]
  linarith [hkey]

/-- Majorant for `x e^{-x²/4}` with the decay `(1+|x|)^{-2}`. -/
theorem inletMaj1 (z : ℝ × ℝ) :
    ‖z.1 * Real.exp (-(z.1 ^ 2) / 4)‖ ≤ 16 * (1 + |z.1|) ^ (-(2 : ℝ)) := by
  have hx : (0 : ℝ) < 1 + |z.1| := by positivity
  have hE : 0 < Real.exp (z.1 ^ 2 / 4) := Real.exp_pos _
  have hexp : Real.exp (-(z.1 ^ 2) / 4) = (Real.exp (z.1 ^ 2 / 4))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  have hpow : (1 + |z.1|) ^ (-(2 : ℝ)) = ((1 + |z.1|) ^ 2)⁻¹ := by
    rw [Real.rpow_neg hx.le, Real.rpow_two]
  have hq := Real.quadratic_le_exp_of_nonneg (x := z.1 ^ 2 / 4) (by positivity)
  have hkey : |z.1| * (1 + |z.1|) ^ 2 ≤ Real.exp (z.1 ^ 2 / 4) * 16 := by
    have h2 := sq_abs z.1
    nlinarith [sq_nonneg (|z.1| ^ 2 - |z.1|), sq_nonneg (|z.1| - 1 / 3), abs_nonneg z.1]
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), hexp, hpow]
  simp only [inv_eq_one_div, mul_one_div]
  rw [div_le_div_iff₀ hE (by positivity)]
  linarith [hkey]

/-- `S₀` is bounded in `q`, uniformly, for every `c > 0`. -/
theorem inletSum0_bound {c : ℝ} (hc : 0 < c) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ q : ℝ, |inletSum0 c q| ≤ M := by
  obtain ⟨M, hM⟩ := UnforcedLeray.B0141.norm_periodize_le_bound
    (F := ℝ) (g := fun w : ℝ × ℝ => Real.exp (-(w.1 ^ 2) / 4)) (C := 8) inletMaj0 hc
  refine ⟨max M 0, le_max_right _ _, fun q => ?_⟩
  have h := hM (q, 0)
  have e : UnforcedLeray.Gaussian.periodize c
      (fun w : ℝ × ℝ => Real.exp (-(w.1 ^ 2) / 4)) (q, 0) = inletSum0 c q := rfl
  rw [e, Real.norm_eq_abs] at h
  exact h.trans (le_max_left _ _)

/-- `S₁` is bounded in `q`, uniformly, for every `c > 0`. -/
theorem inletSum1_bound {c : ℝ} (hc : 0 < c) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ q : ℝ, |inletSum1 c q| ≤ M := by
  obtain ⟨M, hM⟩ := UnforcedLeray.B0141.norm_periodize_le_bound
    (F := ℝ) (g := fun w : ℝ × ℝ => w.1 * Real.exp (-(w.1 ^ 2) / 4)) (C := 16) inletMaj1 hc
  refine ⟨max M 0, le_max_right _ _, fun q => ?_⟩
  have h := hM (q, 0)
  have e : UnforcedLeray.Gaussian.periodize c
      (fun w : ℝ × ℝ => w.1 * Real.exp (-(w.1 ^ 2) / 4)) (q, 0) = inletSum1 c q := rfl
  rw [e, Real.norm_eq_abs] at h
  exact h.trans (le_max_left _ _)

/-! ### 3. The inlet stream and its derivatives -/

/-- The `t = 0` stream formula `𝒫(r, z) = r ψ(R log(r/R), Rz/r)` of `StatementsRing.lean`, with
the factorization of `trainStream_split`. -/
theorem inletStream_eq (c R r z : ℝ) :
    inletStream c R r z =
      r * (-2 * Real.exp (-((R * z / r) ^ 2) / 4) * inletSum0 c (R * Real.log (r / R))) := by
  unfold inletStream
  rw [trainDatum_eq_trainStream', trainStream_split]

/-- The `z`-derivative of the inlet stream: `∂_z 𝒫 = R η E S₀` with `η = Rz/r`, `E = e^{-η²/4}`. -/
theorem hasDerivAt_inletStream_z (c R r z : ℝ) (hc : c ≠ 0) (hr : r ≠ 0) :
    HasDerivAt (fun z' => inletStream c R r z')
      (R * (R * z / r) *
        (Real.exp (-((R * z / r) ^ 2) / 4) * inletSum0 c (R * Real.log (r / R)))) z := by
  have hl : HasDerivAt (fun z' : ℝ => R * z' / r) (R / r) z := by
    have h := ((hasDerivAt_id' z).const_mul R).div_const r
    refine h.congr_deriv ?_
    ring
  have hsq : HasDerivAt (fun z' : ℝ => (R * z' / r) ^ 2) (2 * (R * z / r) * (R / r)) z := by
    have h := hl.pow 2
    refine h.congr_deriv ?_
    norm_num
  have hE : HasDerivAt (fun z' : ℝ => Real.exp (-((R * z' / r) ^ 2) / 4))
      (Real.exp (-((R * z / r) ^ 2) / 4) * (-(2 * (R * z / r) * (R / r)) / 4)) z :=
    ((hsq.neg).div_const 4).exp
  have hB : HasDerivAt (fun z' : ℝ => -2 * Real.exp (-((R * z' / r) ^ 2) / 4) *
      inletSum0 c (R * Real.log (r / R)))
      (-2 * (Real.exp (-((R * z / r) ^ 2) / 4) * (-(2 * (R * z / r) * (R / r)) / 4)) *
        inletSum0 c (R * Real.log (r / R))) z :=
    (hE.const_mul (-2)).mul_const (inletSum0 c (R * Real.log (r / R)))
  have h := hB.const_mul r
  have hfun : (fun z' => inletStream c R r z') = fun z' : ℝ =>
      r * (-2 * Real.exp (-((R * z' / r) ^ 2) / 4) * inletSum0 c (R * Real.log (r / R))) :=
    funext fun z' => inletStream_eq c R r z'
  rw [hfun]
  refine h.congr_deriv ?_
  field_simp
  ring

/-- The `r`-derivative of the inlet stream:
`∂_r 𝒫 = -2E S₀ - η²E S₀ + R E S₁`, `η = Rz/r`, `E = e^{-η²/4}`. -/
theorem hasDerivAt_inletStream_r (c R z r : ℝ) (hc : c ≠ 0) (hr : r ≠ 0) (hR : R ≠ 0) :
    HasDerivAt (fun r' => inletStream c R r' z)
      (-2 * Real.exp (-((R * z / r) ^ 2) / 4) * inletSum0 c (R * Real.log (r / R))
        - (R * z / r) ^ 2 * Real.exp (-((R * z / r) ^ 2) / 4) * inletSum0 c (R * Real.log (r / R))
        + R * Real.exp (-((R * z / r) ^ 2) / 4) * inletSum1 c (R * Real.log (r / R))) r := by
  have hA : HasDerivAt (fun r' : ℝ => r') 1 r := hasDerivAt_id' r
  have hk : HasDerivAt (fun y : ℝ => R * z / y) (-(R * z) / r ^ 2) r := by
    have h := (hasDerivAt_const r (R * z)).div (hasDerivAt_id' r) hr
    refine h.congr_deriv ?_
    ring
  have hsq : HasDerivAt (fun y : ℝ => (R * z / y) ^ 2) (2 * (R * z / r) * (-(R * z) / r ^ 2)) r := by
    have h := hk.pow 2
    refine h.congr_deriv ?_
    norm_num
  have hE : HasDerivAt (fun y : ℝ => Real.exp (-((R * z / y) ^ 2) / 4))
      (Real.exp (-((R * z / r) ^ 2) / 4) * (-(2 * (R * z / r) * (-(R * z) / r ^ 2)) / 4)) r :=
    ((hsq.neg).div_const 4).exp
  have hB : HasDerivAt (fun y : ℝ => -2 * Real.exp (-((R * z / y) ^ 2) / 4))
      (-2 * (Real.exp (-((R * z / r) ^ 2) / 4) * (-(2 * (R * z / r) * (-(R * z) / r ^ 2)) / 4)))
      r :=
    hE.const_mul (-2)
  have hlog : HasDerivAt (fun y : ℝ => Real.log (y / R)) ((1 / R) / (r / R)) r :=
    ((hasDerivAt_id' r).div_const R).log (div_ne_zero hr hR)
  have hC0 := HasDerivAt.comp r (hasDerivAt_inletSum0 hc (R * Real.log (r / R)))
    (hlog.const_mul R)
  have hC : HasDerivAt (fun y : ℝ => inletSum0 c (R * Real.log (y / R)))
      (-(1 / 2 : ℝ) * inletSum1 c (R * Real.log (r / R)) * (R * ((1 / R) / (r / R)))) r :=
    hC0
  have hP := hA.mul (hB.mul hC)
  have hfun : (fun r' => inletStream c R r' z) = fun r' : ℝ =>
      r' * (-2 * Real.exp (-((R * z / r') ^ 2) / 4) * inletSum0 c (R * Real.log (r' / R))) :=
    funext fun r' => inletStream_eq c R r' z
  rw [hfun]
  refine hP.congr_deriv ?_
  simp only [Pi.mul_apply, Pi.neg_apply]
  field_simp
  ring

/-! ### 4. Elementary inequalities -/

/-- `(1+|η|)³ ≤ 64 (1 + η²/4 + (η²/4)²/2)`. -/
theorem inletCube_poly (η : ℝ) :
    (1 + |η|) ^ 3 ≤ 64 * (1 + η ^ 2 / 4 + (η ^ 2 / 4) ^ 2 / 2) := by
  have hu := abs_nonneg η
  have h2 : η ^ 2 = |η| ^ 2 := (sq_abs η).symm
  rw [h2]
  nlinarith [sq_nonneg (|η| ^ 2 - |η| / 4), sq_nonneg (|η| - 1 / 10), hu]

/-- `e^{-η²/4} (1+|η|)³ ≤ 64`. -/
theorem inletGauss_cube (η : ℝ) : Real.exp (-(η ^ 2) / 4) * (1 + |η|) ^ 3 ≤ 64 := by
  have hq := Real.quadratic_le_exp_of_nonneg (x := η ^ 2 / 4) (by positivity)
  have hexp : Real.exp (-(η ^ 2) / 4) = (Real.exp (η ^ 2 / 4))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  have hpos := Real.exp_pos (η ^ 2 / 4)
  rw [hexp, inv_mul_le_iff₀ hpos]
  have hp := inletCube_poly η
  nlinarith [hp, hq]

/-- The polynomial factor `B(η) = R|η|M₀ + 2M₀ + η²M₀ + RM₁` is nonnegative. -/
theorem inletPoly_nonneg {R η M0 M1 : ℝ} (hR : 0 ≤ R) (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1) :
    0 ≤ R * |η| * M0 + 2 * M0 + η ^ 2 * M0 + R * M1 := by
  have h1 := mul_nonneg (mul_nonneg hR (abs_nonneg η)) hM0
  have h2 := mul_nonneg (sq_nonneg η) hM0
  have h3 := mul_nonneg hR hM1
  linarith

/-- The numerical bound `E B(η) (1 + |η|/R) ≤ 64 (R+2)(M₀+M₁)`. -/
theorem inletFinal_numeric {R η M0 M1 : ℝ} (hR : 2 ≤ R) (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1) :
    Real.exp (-(η ^ 2) / 4) * (R * |η| * M0 + 2 * M0 + η ^ 2 * M0 + R * M1) * (1 + |η| / R)
      ≤ 64 * ((R + 2) * (M0 + M1)) := by
  have hR0 : (0 : ℝ) < R := by linarith
  have hu : 0 ≤ |η| := abs_nonneg η
  have hA0 : 0 ≤ (R + 2) * (M0 + M1) := mul_nonneg (by linarith) (by linarith)
  have hRM0 : 0 ≤ R * M0 := mul_nonneg hR0.le hM0
  have hRM1 : 0 ≤ R * M1 := mul_nonneg hR0.le hM1
  have hAM0 : 0 ≤ (R + 2) * (M0 + M1) - M0 := by nlinarith
  have h2AR : 0 ≤ 2 * ((R + 2) * (M0 + M1)) - R * M0 := by nlinarith
  have hB : R * |η| * M0 + 2 * M0 + η ^ 2 * M0 + R * M1 ≤
      (R + 2) * (M0 + M1) * (1 + |η|) ^ 2 := by
    have hs : η ^ 2 = |η| ^ 2 := (sq_abs η).symm
    rw [hs]
    nlinarith [mul_nonneg (sq_nonneg |η|) hAM0, mul_nonneg hu h2AR, hRM0, hRM1]
  have hB0 : 0 ≤ R * |η| * M0 + 2 * M0 + η ^ 2 * M0 + R * M1 :=
    inletPoly_nonneg hR0.le hM0 hM1
  have hR' : 1 + |η| / R ≤ 1 + |η| := by
    have : |η| / R ≤ |η| := div_le_self hu (by linarith)
    linarith
  have hR0' : 0 ≤ 1 + |η| / R := by
    have := div_nonneg hu hR0.le
    linarith
  have h1 : (R * |η| * M0 + 2 * M0 + η ^ 2 * M0 + R * M1) * (1 + |η| / R) ≤
      (R + 2) * (M0 + M1) * (1 + |η|) ^ 3 := by
    calc (R * |η| * M0 + 2 * M0 + η ^ 2 * M0 + R * M1) * (1 + |η| / R)
        ≤ ((R + 2) * (M0 + M1) * (1 + |η|) ^ 2) * (1 + |η|) :=
          mul_le_mul hB hR' hR0' (mul_nonneg hA0 (sq_nonneg _))
      _ = (R + 2) * (M0 + M1) * (1 + |η|) ^ 3 := by ring
  have hEb := inletGauss_cube η
  calc Real.exp (-(η ^ 2) / 4) * (R * |η| * M0 + 2 * M0 + η ^ 2 * M0 + R * M1) * (1 + |η| / R)
      = Real.exp (-(η ^ 2) / 4) *
          ((R * |η| * M0 + 2 * M0 + η ^ 2 * M0 + R * M1) * (1 + |η| / R)) := by ring
    _ ≤ Real.exp (-(η ^ 2) / 4) * ((R + 2) * (M0 + M1) * (1 + |η|) ^ 3) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = (R + 2) * (M0 + M1) * (Real.exp (-(η ^ 2) / 4) * (1 + |η|) ^ 3) := by ring
    _ ≤ (R + 2) * (M0 + M1) * 64 := mul_le_mul_of_nonneg_left hEb hA0
    _ = 64 * ((R + 2) * (M0 + M1)) := by ring

/-- The absolute value of the two inlet components, in terms of the lattice sums. -/
theorem inletPair_bound {R r z E S0 S1 M0 M1 : ℝ} (hR : 0 < R) (hr : 0 < r) (hE : 0 ≤ E)
    (hS0 : |S0| ≤ M0) (hS1 : |S1| ≤ M1) :
    |-(1 / r) * (R * (R * z / r) * (E * S0))| +
        |(1 / r) * (-2 * E * S0 - (R * z / r) ^ 2 * E * S0 + R * E * S1)|
      ≤ (1 / r) * (E * (R * |R * z / r| * M0 + 2 * M0 + (R * z / r) ^ 2 * M0 + R * M1)) := by
  set η := R * z / r with hη
  have hr1 : (0 : ℝ) < 1 / r := one_div_pos.2 hr
  have hα : |-(1 / r) * (R * η * (E * S0))| ≤ (1 / r) * (E * (R * |η| * M0)) := by
    rw [abs_mul, abs_neg, abs_of_pos hr1, abs_mul, abs_mul, abs_mul, abs_of_pos hR,
      abs_of_nonneg hE]
    refine mul_le_mul_of_nonneg_left ?_ hr1.le
    have h1 : E * |S0| ≤ E * M0 := mul_le_mul_of_nonneg_left hS0 hE
    have h2 : 0 ≤ R * |η| := mul_nonneg hR.le (abs_nonneg η)
    calc R * |η| * (E * |S0|) ≤ R * |η| * (E * M0) := mul_le_mul_of_nonneg_left h1 h2
      _ = E * (R * |η| * M0) := by ring
  have hβ : |(1 / r) * (-2 * E * S0 - η ^ 2 * E * S0 + R * E * S1)| ≤
      (1 / r) * (E * (2 * M0 + η ^ 2 * M0 + R * M1)) := by
    rw [abs_mul, abs_of_pos hr1]
    refine mul_le_mul_of_nonneg_left ?_ hr1.le
    have hT : -2 * E * S0 - η ^ 2 * E * S0 + R * E * S1 =
        E * (-(2 + η ^ 2) * S0 + R * S1) := by ring
    rw [hT, abs_mul, abs_of_nonneg hE]
    refine mul_le_mul_of_nonneg_left ?_ hE
    have h3 := abs_add_le (-(2 + η ^ 2) * S0) (R * S1)
    have h4 : |-(2 + η ^ 2) * S0| = (2 + η ^ 2) * |S0| := by
      rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 + η ^ 2)]
    have h5 : |R * S1| = R * |S1| := by rw [abs_mul, abs_of_pos hR]
    rw [h4, h5] at h3
    have h6 : (2 + η ^ 2) * |S0| ≤ 2 * M0 + η ^ 2 * M0 := by
      calc (2 + η ^ 2) * |S0| ≤ (2 + η ^ 2) * M0 :=
            mul_le_mul_of_nonneg_left hS0 (by positivity)
        _ = 2 * M0 + η ^ 2 * M0 := by ring
    have h7 : R * |S1| ≤ R * M1 := mul_le_mul_of_nonneg_left hS1 hR.le
    linarith
  calc |-(1 / r) * (R * η * (E * S0))| +
          |(1 / r) * (-2 * E * S0 - η ^ 2 * E * S0 + R * E * S1)|
      ≤ (1 / r) * (E * (R * |η| * M0)) + (1 / r) * (E * (2 * M0 + η ^ 2 * M0 + R * M1)) :=
        add_le_add hα hβ
    _ = (1 / r) * (E * (R * |η| * M0 + 2 * M0 + η ^ 2 * M0 + R * M1)) := by ring

/-- The norm of the inlet vector in terms of the two partial derivatives. -/
theorem norm_inletRaw_le (c R : ℝ) (y : Space) (hy : y ∉ Axi.axis) :
    ‖inletRaw c R y‖ ≤
      |-(1 / Axi.ϱ y) * deriv (fun z => inletStream c R (Axi.ϱ y) z) (y 2)| +
        |(1 / Axi.ϱ y) * deriv (fun r => inletStream c R r (y 2)) (Axi.ϱ y)| := by
  have he3 : ‖Axi.e3‖ = 1 := by simp [Axi.e3, coordinateVector]
  unfold inletRaw
  refine (norm_add_le _ _).trans ?_
  simp only [norm_smul, Axi.norm_eR hy, he3, Real.norm_eq_abs, mul_one, le_refl]

/-! ### 5. The off-axis bound -/

/-- Off the axis, `‖inletRaw c R y‖ ‖y‖ ≤ 64 (R+2)(M₀+M₁)`. -/
theorem inletRaw_off_axis {c R : ℝ} (hc : 0 < c) (hR : 2 ≤ R) {M0 M1 : ℝ} (hM0 : 0 ≤ M0)
    (hM1 : 0 ≤ M1) (h0 : ∀ q : ℝ, |inletSum0 c q| ≤ M0)
    (h1 : ∀ q : ℝ, |inletSum1 c q| ≤ M1) (y : Space) (hy : y ∉ Axi.axis) :
    ‖inletRaw c R y‖ * ‖y‖ ≤ 64 * ((R + 2) * (M0 + M1)) := by
  have hr : 0 < Axi.ϱ y := Axi.ϱ_pos hy
  have hR0 : (0 : ℝ) < R := by linarith
  have hcne : c ≠ 0 := hc.ne'
  have hrne : Axi.ϱ y ≠ 0 := hr.ne'
  have hRne : R ≠ 0 := hR0.ne'
  have hn := norm_inletRaw_le c R y hy
  rw [(hasDerivAt_inletStream_z c R (Axi.ϱ y) (y 2) hcne hrne).deriv,
    (hasDerivAt_inletStream_r c R (y 2) (Axi.ϱ y) hcne hrne hRne).deriv] at hn
  have hE0 : 0 ≤ Real.exp (-((R * y 2 / Axi.ϱ y) ^ 2) / 4) := (Real.exp_pos _).le
  have hab := inletPair_bound (R := R) (r := Axi.ϱ y) (z := y 2) hR0 hr hE0
    (h0 (R * Real.log (Axi.ϱ y / R))) (h1 (R * Real.log (Axi.ϱ y / R)))
  -- `‖y‖ ≤ r (1 + |η|/R)`
  have hη : R * y 2 / Axi.ϱ y * Axi.ϱ y = R * y 2 := div_mul_cancel₀ _ hrne
  have hA : |R * y 2| = |R * y 2 / Axi.ϱ y| * Axi.ϱ y := by
    conv_lhs => rw [← hη]
    rw [abs_mul, abs_of_pos hr]
  have hB : R * |y 2| = |R * y 2 / Axi.ϱ y| * Axi.ϱ y := by
    rw [← hA, abs_mul, abs_of_pos hR0]
  have hyz : |y 2| = |R * y 2 / Axi.ϱ y| * Axi.ϱ y / R := by
    rw [eq_div_iff hR0.ne']
    linear_combination hB
  have hsq := Axi.norm_sq_eq_ϱ_sq_add y
  have hsq2 : (y 2) ^ 2 = |y 2| ^ 2 := (sq_abs (y 2)).symm
  have hyle : ‖y‖ ≤ Axi.ϱ y + |y 2| := by
    nlinarith [abs_nonneg (y 2), norm_nonneg y, mul_nonneg hr.le (abs_nonneg (y 2)),
      add_nonneg (add_nonneg (norm_nonneg y) hr.le) (abs_nonneg (y 2))]
  have hcalc : Axi.ϱ y * (1 + |R * y 2 / Axi.ϱ y| / R) = Axi.ϱ y + |y 2| := by
    rw [hyz]
    ring
  have hy_le : ‖y‖ ≤ Axi.ϱ y * (1 + |R * y 2 / Axi.ϱ y| / R) := by
    rw [hcalc]
    exact hyle
  have hnonneg : 0 ≤ (1 / Axi.ϱ y) * (Real.exp (-((R * y 2 / Axi.ϱ y) ^ 2) / 4) *
      (R * |R * y 2 / Axi.ϱ y| * M0 + 2 * M0 + (R * y 2 / Axi.ϱ y) ^ 2 * M0 + R * M1)) :=
    mul_nonneg (one_div_pos.2 hr).le
      (mul_nonneg hE0 (inletPoly_nonneg hR0.le hM0 hM1))
  calc ‖inletRaw c R y‖ * ‖y‖
      ≤ ((1 / Axi.ϱ y) * (Real.exp (-((R * y 2 / Axi.ϱ y) ^ 2) / 4) *
          (R * |R * y 2 / Axi.ϱ y| * M0 + 2 * M0 + (R * y 2 / Axi.ϱ y) ^ 2 * M0 + R * M1))) *
          (Axi.ϱ y * (1 + |R * y 2 / Axi.ϱ y| / R)) :=
        mul_le_mul (hn.trans hab) hy_le (norm_nonneg _) hnonneg
    _ = Real.exp (-((R * y 2 / Axi.ϱ y) ^ 2) / 4) *
          (R * |R * y 2 / Axi.ϱ y| * M0 + 2 * M0 + (R * y 2 / Axi.ϱ y) ^ 2 * M0 + R * M1) *
          (1 + |R * y 2 / Axi.ϱ y| / R) := by
        field_simp
    _ ≤ 64 * ((R + 2) * (M0 + M1)) := inletFinal_numeric hR hM0 hM1

/-! ### 6. The inlet bound -/

/-- **Task `PartII-a:R08`, inlet bound.** Every extension `a` of `inletRaw c R`, continuous on
`{x ≠ 0}`, satisfies `‖a x‖ ≤ C / ‖x‖` for `x ≠ 0`. -/
theorem inletBound_proof : UnforcedLeray.Short.PartIIa.InletBound := by
  unfold UnforcedLeray.Short.PartIIa.InletBound
  intro c R hc hR a ha hao
  obtain ⟨M0, hM0, h0⟩ := inletSum0_bound hc
  obtain ⟨M1, hM1, h1⟩ := inletSum1_bound hc
  have hoff : ∀ y : Space, y ∉ Axi.axis → ‖a y‖ ≤ 64 * ((R + 2) * (M0 + M1)) / ‖y‖ := by
    intro y hy
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact hy (by simp [Axi.axis])
    rw [hao y hy, le_div_iff₀ (norm_pos_iff.2 hy0)]
    exact inletRaw_off_axis hc hR hM0 hM1 h0 h1 y hy
  refine ⟨64 * ((R + 2) * (M0 + M1)), fun x hx => ?_⟩
  by_cases hax : x ∈ Axi.axis
  · obtain ⟨hx0, hx1⟩ : x 0 = 0 ∧ x 1 = 0 := hax
    obtain ⟨p, hp⟩ : ∃ p : ℝ → Space, p = fun t => x + t • coordinateVector 0 := ⟨_, rfl⟩
    have hp0 : ∀ t : ℝ, p t 0 = t := by
      intro t
      rw [hp]
      simp [coordinateVector, hx0]
    have hpc : Continuous p := by
      rw [hp]
      fun_prop
    have hpx : p 0 = x := by
      rw [hp]
      simp
    have hlim1 : Tendsto p (𝓝[>] (0 : ℝ)) (𝓝 x) := by
      have := (hpc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      rwa [hpx] at this
    have hlim2 : Tendsto p (𝓝[>] (0 : ℝ)) (𝓝[{y : Space | y ≠ 0}] x) := by
      refine tendsto_nhdsWithin_iff.2 ⟨hlim1, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with t ht
      show p t ≠ 0
      intro hzero
      have h1' := hp0 t
      rw [hzero] at h1'
      simp at h1'
      have ht' : 0 < t := ht
      linarith
    have hA : Tendsto (fun t => a (p t)) (𝓝[>] (0 : ℝ)) (𝓝 (a x)) :=
      (ha x hx).tendsto.comp hlim2
    have hden : Tendsto (fun t => 64 * ((R + 2) * (M0 + M1)) / ‖p t‖) (𝓝[>] (0 : ℝ))
        (𝓝 (64 * ((R + 2) * (M0 + M1)) / ‖x‖)) :=
      tendsto_const_nhds.div hlim1.norm (norm_ne_zero_iff.2 hx)
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
        ‖a (p t)‖ ≤ 64 * ((R + 2) * (M0 + M1)) / ‖p t‖ := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      apply hoff
      intro hmem
      obtain ⟨hm0, _⟩ : p t 0 = 0 ∧ p t 1 = 0 := hmem
      have h2 := hp0 t
      have ht' : 0 < t := ht
      linarith
    exact le_of_tendsto_of_tendsto hA.norm hden hev
  · exact hoff x hax

end UnforcedLeray.Short.PartIIa
