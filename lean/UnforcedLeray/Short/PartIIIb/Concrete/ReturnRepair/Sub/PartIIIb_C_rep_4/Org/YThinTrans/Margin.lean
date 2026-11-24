import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.EpsForm

/-!
# `PartIII-b:C/rep/4/2/org`: the margin of the thin stream transitions

Source `the November 2 reference manuscript` 5116-5121 (`eps = C_* nu^r e^{-d0/nu}`,
`d0 = gamma/3`), 5357-5365 (margins), 5607 (`omega_b = k b d0`).

The table row `TransThinOpTable` (`YThinTrans.lean`) carries the factor `Scut^k1 |N_nu| (eps^2 +
eps^{49/22} e^{m0/(2nu)}) e^{-4gamma/(9nu)}`.  With `Scut = eps^{-b}`, `eps = C_* nu^r e^{-gamma/(3nu)}`
and `|N_nu| = e^{gamma/nu} nu^{-Re kappa}` this is `nu^{poly} e^{E/nu}` with
`E = k1 b gamma/3 - gamma/9 + ...`, and the leaf `AgeTransThinAt` asks for the exponent
`k0 b gamma/3 - gamma/15 + 3 m0/2` with `k0 = k1`.  The two exponents are checked by `ring`/`linarith`:

* eps^2 term: `E - T = -2 gamma/45 - 3 m0/2 <= 0`;
* eps^{49/22} term: `E - T = -119 gamma/990 - m0 <= 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-- Power of a product `(A nu^r e^{e/nu})^p`, real `p`. -/
theorem am_form_rpow {A ν r e p : ℝ} (hA : 0 < A) (hν : 0 < ν) :
    (A * ν ^ r * Real.exp (e / ν)) ^ p = A ^ p * ν ^ (r * p) * Real.exp (e * p / ν) := by
  rw [Real.mul_rpow (mul_pos hA (Real.rpow_pos_of_pos hν r)).le (Real.exp_pos _).le,
    Real.mul_rpow hA.le (Real.rpow_pos_of_pos hν r).le, ← Real.rpow_mul hν.le, ← Real.exp_mul,
    show e / ν * p = e * p / ν by ring]

/-- One monomial term `c nu^a e^{e/nu}` is bounded by `c nu^{-j} e^{T/nu}` when `e <= T`,
`-a <= j` and `nu <= 1` (`nu^a <= nu^{-j}`). -/
theorem am_term {ν a e T c : ℝ} (j : ℕ) (hc : 0 ≤ c) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hj : -a ≤ (j : ℝ)) (he : e ≤ T) :
    c * ν ^ a * Real.exp (e / ν) ≤ c * ν⁻¹ ^ j * Real.exp (T / ν) := by
  have h1 : ν ^ a ≤ ν⁻¹ ^ j := by
    calc ν ^ a ≤ ν ^ (-(j : ℝ)) := Real.rpow_le_rpow_of_exponent_ge hν hν1 (by linarith)
      _ = ν⁻¹ ^ j := by rw [Real.rpow_neg hν.le, Real.rpow_natCast, inv_pow]
  have h2 : Real.exp (e / ν) ≤ Real.exp (T / ν) :=
    Real.exp_le_exp.2 (div_le_div_of_nonneg_right he hν.le)
  have h3 : c * ν ^ a ≤ c * ν⁻¹ ^ j := mul_le_mul_of_nonneg_left h1 hc
  calc c * ν ^ a * Real.exp (e / ν) ≤ c * ν⁻¹ ^ j * Real.exp (e / ν) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    _ ≤ c * ν⁻¹ ^ j * Real.exp (T / ν) :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg hc (pow_nonneg (inv_nonneg.2 hν.le) j))

/-- The gauge `|N_nu| = e^{gamma/nu} nu^{-Re kappa}` (`Estimates.gaugeN`, `Scalar.Nnu`). -/
theorem am_gaugeN (Pl : PlanarData) (L : ReturnLevel) :
    gaugeN Pl L = Real.exp (Pl.eigenvalue.re / L.ν) * L.ν ^ (-Pl.kappa.re) := by
  unfold gaugeN Nnu
  rw [norm_mul, Complex.norm_exp, Complex.norm_cpow_eq_rpow_re_of_pos L.ν_pos,
    Complex.div_ofReal_re, Complex.neg_re]

/-- **The exponent algebra of the margin** (source 5116-5121, 5357-5365): with
`eps = A nu^r e^{-(gamma/3)/nu}`, the thin-receiver and repair-receiver terms of
`(eps^{-b})^{k1} |N_nu| (eps^2 + eps^{49/22} e^{m0/(2nu)}) e^{-4gamma/(9nu)}` are bounded by one
`Q nu^{-j} e^{T/nu}` with `T = -(gamma/15 - k1 b gamma/3 - 3 m0/2)`, uniformly for `0 < nu <= 1`. -/
theorem am_core (A r κ γ m0 b : ℝ) (k1 : ℕ) (hA : 0 < A) (hγ : 0 < γ) (hm : 0 < m0) :
    ∃ (Q : ℝ) (j : ℕ), ∀ ν ε : ℝ, 0 < ν → ν ≤ 1 → ε = A * ν ^ r * Real.exp (-(γ / 3) / ν) →
      (ε ^ (-b)) ^ k1 * (Real.exp (γ / ν) * ν ^ (-κ)) *
          (ε ^ (2 : ℝ) + ε ^ (49 / 22 : ℝ) * Real.exp (m0 / (2 * ν))) * Real.exp (-(4 * γ / 9) / ν)
        ≤ Q * ν⁻¹ ^ j * Real.exp (-(γ / 15 - (k1 : ℝ) * b * (γ / 3) - 3 * m0 / 2) / ν) := by
  refine ⟨A ^ (-b * (k1 : ℝ)) * A ^ (2 : ℝ) + A ^ (-b * (k1 : ℝ)) * A ^ (49 / 22 : ℝ),
    ⌈-(r * (-b * (k1 : ℝ)) + -κ + r * 2)⌉₊ + ⌈-(r * (-b * (k1 : ℝ)) + -κ + r * (49 / 22))⌉₊, ?_⟩
  intro ν ε hν hν1 hε
  have hε0 : 0 < ε := by
    rw [hε]; exact mul_pos (mul_pos hA (Real.rpow_pos_of_pos hν r)) (Real.exp_pos _)
  have h1 : (ε ^ (-b)) ^ k1 = A ^ (-b * (k1 : ℝ)) * ν ^ (r * (-b * (k1 : ℝ))) *
      Real.exp (-(γ / 3) * (-b * (k1 : ℝ)) / ν) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε0.le, hε, am_form_rpow hA hν]
  have h2 : ε ^ (2 : ℝ) = A ^ (2 : ℝ) * ν ^ (r * 2) * Real.exp (-(γ / 3) * 2 / ν) := by
    rw [hε, am_form_rpow hA hν]
  have h3 : ε ^ (49 / 22 : ℝ) = A ^ (49 / 22 : ℝ) * ν ^ (r * (49 / 22)) *
      Real.exp (-(γ / 3) * (49 / 22) / ν) := by
    rw [hε, am_form_rpow hA hν]
  have hm2 : Real.exp (m0 / (2 * ν)) = Real.exp (m0 / 2 / ν) := by
    congr 1; ring
  have hsplit :
      (ε ^ (-b)) ^ k1 * (Real.exp (γ / ν) * ν ^ (-κ)) *
          (ε ^ (2 : ℝ) + ε ^ (49 / 22 : ℝ) * Real.exp (m0 / (2 * ν))) * Real.exp (-(4 * γ / 9) / ν)
        = (A ^ (-b * (k1 : ℝ)) * A ^ (2 : ℝ)) * ν ^ (r * (-b * (k1 : ℝ)) + -κ + r * 2) *
            Real.exp ((-(γ / 3) * (-b * (k1 : ℝ)) + γ + -(γ / 3) * 2 + -(4 * γ / 9)) / ν)
        + (A ^ (-b * (k1 : ℝ)) * A ^ (49 / 22 : ℝ)) *
            ν ^ (r * (-b * (k1 : ℝ)) + -κ + r * (49 / 22)) *
            Real.exp ((-(γ / 3) * (-b * (k1 : ℝ)) + γ + -(γ / 3) * (49 / 22) + m0 / 2
              + -(4 * γ / 9)) / ν) := by
    rw [h1, h2, h3, hm2]
    simp only [Real.rpow_add hν, add_div, Real.exp_add]
    ring
  have hc1 : 0 ≤ A ^ (-b * (k1 : ℝ)) * A ^ (2 : ℝ) :=
    mul_nonneg (Real.rpow_nonneg hA.le _) (Real.rpow_nonneg hA.le _)
  have hc2 : 0 ≤ A ^ (-b * (k1 : ℝ)) * A ^ (49 / 22 : ℝ) :=
    mul_nonneg (Real.rpow_nonneg hA.le _) (Real.rpow_nonneg hA.le _)
  have eA : (-(γ / 3) * (-b * (k1 : ℝ)) + γ + -(γ / 3) * 2 + -(4 * γ / 9)) ≤
      -(γ / 15 - (k1 : ℝ) * b * (γ / 3) - 3 * m0 / 2) := by
    have h : -(γ / 15 - (k1 : ℝ) * b * (γ / 3) - 3 * m0 / 2) -
        (-(γ / 3) * (-b * (k1 : ℝ)) + γ + -(γ / 3) * 2 + -(4 * γ / 9)) = 2 * γ / 45 + 3 * m0 / 2 := by
      ring
    linarith
  have eB : (-(γ / 3) * (-b * (k1 : ℝ)) + γ + -(γ / 3) * (49 / 22) + m0 / 2 + -(4 * γ / 9)) ≤
      -(γ / 15 - (k1 : ℝ) * b * (γ / 3) - 3 * m0 / 2) := by
    have h : -(γ / 15 - (k1 : ℝ) * b * (γ / 3) - 3 * m0 / 2) -
        (-(γ / 3) * (-b * (k1 : ℝ)) + γ + -(γ / 3) * (49 / 22) + m0 / 2 + -(4 * γ / 9)) =
          119 * γ / 990 + m0 := by
      ring
    linarith
  have hjA : -(r * (-b * (k1 : ℝ)) + -κ + r * 2) ≤
      ((⌈-(r * (-b * (k1 : ℝ)) + -κ + r * 2)⌉₊ + ⌈-(r * (-b * (k1 : ℝ)) + -κ + r * (49 / 22))⌉₊ : ℕ) : ℝ) := by
    push_cast
    linarith [Nat.le_ceil (-(r * (-b * (k1 : ℝ)) + -κ + r * 2)),
      (Nat.cast_nonneg ⌈-(r * (-b * (k1 : ℝ)) + -κ + r * (49 / 22))⌉₊ : (0 : ℝ) ≤ _)]
  have hjB : -(r * (-b * (k1 : ℝ)) + -κ + r * (49 / 22)) ≤
      ((⌈-(r * (-b * (k1 : ℝ)) + -κ + r * 2)⌉₊ + ⌈-(r * (-b * (k1 : ℝ)) + -κ + r * (49 / 22))⌉₊ : ℕ) : ℝ) := by
    push_cast
    linarith [Nat.le_ceil (-(r * (-b * (k1 : ℝ)) + -κ + r * (49 / 22))),
      (Nat.cast_nonneg ⌈-(r * (-b * (k1 : ℝ)) + -κ + r * 2)⌉₊ : (0 : ℝ) ≤ _)]
  have bA := am_term (c := A ^ (-b * (k1 : ℝ)) * A ^ (2 : ℝ)) _ hc1 hν hν1 hjA eA
  have bB := am_term (c := A ^ (-b * (k1 : ℝ)) * A ^ (49 / 22 : ℝ)) _ hc2 hν hν1 hjB eB
  rw [hsplit]
  calc _ ≤ _ := add_le_add bA bB
    _ = _ := by ring

/-- **The thin stream-transition leaf from the table row** (source 5357-5365, 5607): the
`S`-degree `k0 = k1` of the table row gives `omega_b = k0 b gamma/3`. Pure arithmetic on
`TransThinOpTable`, `eps = retEps` in closed form (`retEps_eq_form`), `Scut = eps^{-b}`,
`|N_nu| = e^{gamma/nu} nu^{-Re kappa}` (`am_gaugeN`). -/
theorem ageTransThin_of_table {Pl : PlanarData} {σ₀ mZ dm dp : ℝ}
    (h : TransThinOpTable Pl σ₀ mZ dm dp) : AgeTransThin Pl σ₀ mZ dm dp := by
  obtain ⟨k₁, H⟩ := h
  refine ⟨k₁, fun D hPl hσ hmZ hst => ?_⟩
  obtain ⟨C, k, HC⟩ := H D hPl hσ hmZ hst
  have hν : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n < 1 :=
    (tendsto_order.1 (retNu_tendsto D.σ₀ hst.omega_ne)).2 1 one_pos
  have hA : 0 < (2 * ‖D.Pl.signedCoeff D.σ₀‖) ^ (-(1 / 3 : ℝ)) :=
    Real.rpow_pos_of_pos (mul_pos two_pos (norm_pos_iff.2 D.coeff_ne)) _
  obtain ⟨Q, j, hQ⟩ := am_core ((2 * ‖D.Pl.signedCoeff D.σ₀‖) ^ (-(1 / 3 : ℝ)))
    ((D.Pl.kappa.re - 5 - 2 * D.σ₀) / 3) D.Pl.kappa.re (gRate D.Pl) D.K.m0 D.K.b k₁ hA
    hst.gamma_pos hst.m0_pos
  unfold SeqData.AgeTransThinAt
  refine ⟨|C| * Q, k + j, ?_⟩
  filter_upwards [HC, hν] with n hn hn1
  intro z hz T
  have hb := hn z hz T
  have hν0 : 0 < (D.level n).ν := (D.level n).ν_pos
  have hεform : (D.level n).ε = (2 * ‖D.Pl.signedCoeff D.σ₀‖) ^ (-(1 / 3 : ℝ)) *
      (D.level n).ν ^ ((D.Pl.kappa.re - 5 - 2 * D.σ₀) / 3) *
      Real.exp (-(gRate D.Pl / 3) / (D.level n).ν) :=
    retEps_eq_form D.coeff_ne n
  have hcore := hQ (D.level n).ν (D.level n).ε hν0 hn1.le hεform
  have hG : gaugeN D.Pl (D.level n) =
      Real.exp (gRate D.Pl / (D.level n).ν) * (D.level n).ν ^ (-D.Pl.kappa.re) :=
    am_gaugeN D.Pl (D.level n)
  have hS : (D.level n).Scut D.K = (D.level n).ε ^ (-D.K.b) := rfl
  have hbound' : ‖multOp D.Pl D.K (D.level n) (transOp D.Pl D.K (D.level n) (D.mu n z) hst.chiY (thinPart T))‖
      ≤ C * (D.level n).ν⁻¹ ^ k *
          (((D.level n).ε ^ (-D.K.b)) ^ k₁ * (Real.exp (gRate D.Pl / (D.level n).ν) * (D.level n).ν ^ (-D.Pl.kappa.re)) *
            ((D.level n).ε ^ (2 : ℝ) + (D.level n).ε ^ (49 / 22 : ℝ) *
              Real.exp (D.K.m0 / (2 * (D.level n).ν))) *
            Real.exp (-(4 * gRate D.Pl / 9) / (D.level n).ν)) * ‖T‖ := by
    refine hb.trans (le_of_eq ?_)
    rw [hG, hS]
    ring
  have hP : 0 ≤ (D.level n).ν⁻¹ ^ k := pow_nonneg (inv_nonneg.2 hν0.le) k
  have hX0 : 0 ≤ ((D.level n).ε ^ (-D.K.b)) ^ k₁ *
      (Real.exp (gRate D.Pl / (D.level n).ν) * (D.level n).ν ^ (-D.Pl.kappa.re)) *
      ((D.level n).ε ^ (2 : ℝ) + (D.level n).ε ^ (49 / 22 : ℝ) *
        Real.exp (D.K.m0 / (2 * (D.level n).ν))) *
      Real.exp (-(4 * gRate D.Pl / 9) / (D.level n).ν) := by
    have hε0 := (D.level n).ε_pos
    have hνr : 0 ≤ (D.level n).ν ^ (-D.Pl.kappa.re) := Real.rpow_nonneg hν0.le _
    refine mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (Real.rpow_nonneg hε0.le _) k₁)
      (mul_nonneg (Real.exp_pos _).le hνr)) (add_nonneg (Real.rpow_nonneg hε0.le _)
      (mul_nonneg (Real.rpow_nonneg hε0.le _) (Real.exp_pos _).le))) (Real.exp_pos _).le
  have hXY := hcore
  calc _ ≤ _ := hbound'
    _ ≤ |C| * (D.level n).ν⁻¹ ^ k *
          (((D.level n).ε ^ (-D.K.b)) ^ k₁ * (Real.exp (gRate D.Pl / (D.level n).ν) * (D.level n).ν ^ (-D.Pl.kappa.re)) *
            ((D.level n).ε ^ (2 : ℝ) + (D.level n).ε ^ (49 / 22 : ℝ) *
              Real.exp (D.K.m0 / (2 * (D.level n).ν))) *
            Real.exp (-(4 * gRate D.Pl / 9) / (D.level n).ν)) * ‖T‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_abs_self C) hP) hX0) (norm_nonneg T)
    _ ≤ |C| * (D.level n).ν⁻¹ ^ k * (Q * (D.level n).ν⁻¹ ^ j *
          Real.exp (-(gRate D.Pl / 15 - (k₁ : ℝ) * D.K.b * (gRate D.Pl / 3) - 3 * D.K.m0 / 2) / (D.level n).ν)) * ‖T‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hXY (mul_nonneg (abs_nonneg C) hP))
            (norm_nonneg T)
    _ = |C| * Q * (D.level n).ν⁻¹ ^ (k + j) *
          Real.exp (-(gRate D.Pl / 15 - (k₁ : ℝ) * D.K.b * (gRate D.Pl / 3) - 3 * D.K.m0 / 2) / (D.level n).ν) * ‖T‖ := by
          rw [pow_add]; ring

end UnforcedLeray.Short.PartIIIb.Concrete
