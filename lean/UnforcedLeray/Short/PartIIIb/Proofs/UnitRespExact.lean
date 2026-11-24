import UnforcedLeray.Short.PartIIIb.Tasks

/-!
# Proof of `T_unitRespExact` (source: `the November 2 reference manuscript`, lines 5962-5970)

Write `C = 𝒞(σ₀)`, `N = N_ν = e^{λ/ν} ν^{-κ}` and `φ = Im λ / ν - Im κ · log ν`.

* Polar form: `C = ‖C‖ e^{i arg C}` and `N = ‖N‖ e^{iφ}`.
* The phase lock `φ + arg C = 2π m` gives `C N = ‖C‖ ‖N‖`, a positive real number.
* Hence `Re(𝒞(μ) N) = Re(𝒞(μ)/C) · ‖C‖ ‖N‖`.
* The amplitude identity `ε³ ‖N‖ ν^{5+2μ} = e^{-z}/(2‖C‖)` (the content of `T_astarExact`,
  proved inline below) turns `2 ε³ ν^{5+2μ} · ‖C‖ ‖N‖ · Re(𝒞(μ)/C)` into `e^{-z} Re(𝒞(μ)/C)`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb

/-- A product of two polar factorisations whose phases add to a multiple of `2π` is real and
equal to the product of the moduli. -/
theorem unitRespExact_polar (C N : ℂ) (r n a b : ℝ) (m : ℤ)
    (hC : C = (r : ℂ) * Complex.exp ((a : ℂ) * Complex.I))
    (hN : N = (n : ℂ) * Complex.exp ((b : ℂ) * Complex.I))
    (hab : b + a = 2 * Real.pi * m) :
    C * N = ((r * n : ℝ) : ℂ) := by
  have hexp : Complex.exp ((a : ℂ) * Complex.I) * Complex.exp ((b : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add]
    have h1 : ((b + a : ℝ) : ℂ) = ((2 * Real.pi * m : ℝ) : ℂ) := by rw [hab]
    push_cast at h1
    have h2 : (a : ℂ) * Complex.I + (b : ℂ) * Complex.I
        = (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      linear_combination h1 * Complex.I
    rw [h2, Complex.exp_int_mul_two_pi_mul_I]
  rw [hC, hN]
  push_cast
  linear_combination ((r : ℂ) * (n : ℂ)) * hexp

/-- The amplitude identity `ε³ ‖N_ν‖ ν^{5+2μ} = e^{-z}/(2‖𝒞(σ₀)‖)` (lines 5955-5957, the
statement of `T_astarExact`, at `μ = μ_n(z)`), for `0 < ν < 1`. -/
theorem unitRespExact_astar (lam κ C : ℂ) (σ₀ ν z : ℝ) (hν0 : 0 < ν) (hν1 : ν < 1) :
    epsCube lam.re κ σ₀ C ν * ‖Nnu lam κ ν‖ * ν ^ (5 + 2 * muWin σ₀ ν z)
      = Real.exp (-z) / (2 * ‖C‖) := by
  have hlog : Real.log ν < 0 := Real.log_neg hν0 hν1
  have hLne : Real.log ν ≠ 0 := ne_of_lt hlog
  have hL : |Real.log ν| = -Real.log ν := abs_of_neg hlog
  have hN : ‖Nnu lam κ ν‖ = Real.exp (lam.re / ν) * ν ^ (-κ.re) := by
    unfold Nnu
    rw [norm_mul, Complex.norm_exp, Complex.norm_cpow_eq_rpow_re_of_pos hν0,
      Complex.div_ofReal_re, Complex.neg_re]
  have hexp : Real.exp (-lam.re / ν) * Real.exp (lam.re / ν) = 1 := by
    rw [← Real.exp_add]
    have h0 : -lam.re / ν + lam.re / ν = 0 := by ring
    rw [h0, Real.exp_zero]
  have hpow : ν ^ (κ.re - 5 - 2 * σ₀) * ν ^ (-κ.re)
      * ν ^ (5 + 2 * (σ₀ + z / (2 * |Real.log ν|))) = Real.exp (-z) := by
    rw [← Real.rpow_add hν0, ← Real.rpow_add hν0, Real.rpow_def_of_pos hν0, hL]
    congr 1
    have hsum : (κ.re - 5 - 2 * σ₀) + -κ.re + (5 + 2 * (σ₀ + z / (2 * -Real.log ν)))
        = z / (-Real.log ν) := by ring
    have hmul : Real.log ν * (z / (-Real.log ν)) = -z := by
      rw [mul_div_assoc', div_eq_iff (neg_ne_zero.mpr hLne)]
      ring
    rw [hsum, hmul]
  unfold epsCube muWin
  rw [hN]
  have key : Real.exp (-lam.re / ν) * ν ^ (κ.re - 5 - 2 * σ₀) / (2 * ‖C‖) *
      (Real.exp (lam.re / ν) * ν ^ (-κ.re)) *
      ν ^ (5 + 2 * (σ₀ + z / (2 * |Real.log ν|))) =
      (Real.exp (-lam.re / ν) * Real.exp (lam.re / ν)) *
      (ν ^ (κ.re - 5 - 2 * σ₀) * ν ^ (-κ.re) *
      ν ^ (5 + 2 * (σ₀ + z / (2 * |Real.log ν|)))) / (2 * ‖C‖) := by
    ring
  rw [key, hexp, hpow, one_mul]

theorem unitRespExact : UnforcedLeray.Short.PartIIIb.T_unitRespExact := by
  unfold UnforcedLeray.Short.PartIIIb.T_unitRespExact
  intro lam κ ell J σ₀ ν z hν0 hν1 hC hm
  obtain ⟨m, hm⟩ := hm
  have hν0ne : (ν : ℂ) ≠ 0 := by exact_mod_cast hν0.ne'
  -- Step 1: N_ν is the exponential of an explicit complex number.
  have hNexp : Nnu lam κ ν
      = Complex.exp (lam / (ν : ℂ) + ((Real.log ν : ℝ) : ℂ) * (-κ)) := by
    unfold Nnu
    rw [Complex.exp_add, Complex.cpow_def_of_ne_zero hν0ne, ← Complex.ofReal_log hν0.le]
  -- Step 2: the imaginary part of that exponent is the phase φ.
  have hwim : (lam / (ν : ℂ) + ((Real.log ν : ℝ) : ℂ) * (-κ)).im
      = lam.im / ν - κ.im * Real.log ν := by
    simp [Complex.mul_im]
    ring
  -- Step 3: polar form N_ν = ‖N_ν‖ e^{iφ}.
  have hnorm : ‖Nnu lam κ ν‖
      = Real.exp (lam / (ν : ℂ) + ((Real.log ν : ℝ) : ℂ) * (-κ)).re := by
    rw [hNexp, Complex.norm_exp]
  have hNpolar : Nnu lam κ ν
      = ((‖Nnu lam κ ν‖ : ℝ) : ℂ)
        * Complex.exp (((lam.im / ν - κ.im * Real.log ν : ℝ) : ℂ) * Complex.I) := by
    rw [hnorm, hNexp, Complex.ofReal_exp, ← Complex.exp_add, ← hwim]
    congr 1
    exact (Complex.re_add_im _).symm
  -- Step 4: polar form of 𝒞(σ₀), and the phase lock gives C N = ‖C‖ ‖N‖ (real).
  have hCpolar : mellinC lam ell J (σ₀ : ℂ)
      = ((‖mellinC lam ell J (σ₀ : ℂ)‖ : ℝ) : ℂ)
        * Complex.exp (((Complex.arg (mellinC lam ell J (σ₀ : ℂ)) : ℝ) : ℂ) * Complex.I) :=
    (Complex.norm_mul_exp_arg_mul_I _).symm
  have hCN : mellinC lam ell J (σ₀ : ℂ) * Nnu lam κ ν
      = ((‖mellinC lam ell J (σ₀ : ℂ)‖ * ‖Nnu lam κ ν‖ : ℝ) : ℂ) :=
    unitRespExact_polar (mellinC lam ell J (σ₀ : ℂ)) (Nnu lam κ ν)
      ‖mellinC lam ell J (σ₀ : ℂ)‖ ‖Nnu lam κ ν‖
      (Complex.arg (mellinC lam ell J (σ₀ : ℂ))) (lam.im / ν - κ.im * Real.log ν) m
      hCpolar hNpolar hm
  -- Step 5: Re(𝒞(μ) N) = Re(𝒞(μ)/𝒞(σ₀)) · ‖C‖ ‖N‖.
  have hre : (mellinC lam ell J ((muWin σ₀ ν z : ℝ) : ℂ) * Nnu lam κ ν).re
      = (mellinC lam ell J ((muWin σ₀ ν z : ℝ) : ℂ) / mellinC lam ell J (σ₀ : ℂ)).re
        * (‖mellinC lam ell J (σ₀ : ℂ)‖ * ‖Nnu lam κ ν‖) := by
    have hsplit : mellinC lam ell J ((muWin σ₀ ν z : ℝ) : ℂ) * Nnu lam κ ν
        = (mellinC lam ell J ((muWin σ₀ ν z : ℝ) : ℂ) / mellinC lam ell J (σ₀ : ℂ))
          * (mellinC lam ell J (σ₀ : ℂ) * Nnu lam κ ν) := by
      field_simp
    rw [hsplit, hCN, Complex.re_mul_ofReal]
  -- Step 6: the amplitude identity and the final cancellation.
  have hA := unitRespExact_astar lam κ (mellinC lam ell J (σ₀ : ℂ)) σ₀ ν z hν0 hν1
  have hC0 : ‖mellinC lam ell J (σ₀ : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr hC
  unfold unitResp
  rw [hre]
  have e1 : 2 * epsCube lam.re κ σ₀ (mellinC lam ell J (σ₀ : ℂ)) ν
      * ν ^ (5 + 2 * muWin σ₀ ν z)
      * ((mellinC lam ell J ((muWin σ₀ ν z : ℝ) : ℂ) / mellinC lam ell J (σ₀ : ℂ)).re
        * (‖mellinC lam ell J (σ₀ : ℂ)‖ * ‖Nnu lam κ ν‖))
      = 2 * ‖mellinC lam ell J (σ₀ : ℂ)‖
        * (epsCube lam.re κ σ₀ (mellinC lam ell J (σ₀ : ℂ)) ν * ‖Nnu lam κ ν‖
          * ν ^ (5 + 2 * muWin σ₀ ν z))
        * (mellinC lam ell J ((muWin σ₀ ν z : ℝ) : ℂ) / mellinC lam ell J (σ₀ : ℂ)).re := by
    ring
  have h2 : 2 * ‖mellinC lam ell J (σ₀ : ℂ)‖ * (Real.exp (-z) / (2 * ‖mellinC lam ell J (σ₀ : ℂ)‖))
      = Real.exp (-z) := by
    field_simp
  rw [e1, hA, h2]

end UnforcedLeray.Short.PartIIIb
