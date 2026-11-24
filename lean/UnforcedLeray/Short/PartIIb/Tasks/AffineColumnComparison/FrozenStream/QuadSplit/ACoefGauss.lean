import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.QuadSplit.GaussMulPoly

/-!
# Part II-b, task `PartII-b:G4/2/2/1/4`: `ACoefGauss`

Source of record: `the November 2 reference manuscript`, lines 2349-2352.

Route: `aCoef λ = (2ik) · G` with `G = (λ + 2iΩ)⁻¹`, `2ik = P e^{-r²/4}` (`P` a polynomial),
`G' = G² · (i r e^{-r²/4})`.  Derivatives of `P e^{-r²/4}` are again of this form (Gaussian
bounded); derivatives of `G` are polynomially bounded by induction on the order (Leibniz).  The
conclusion follows from `gaussMulPoly`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Blueprint

namespace ACoefHelp

/-- `E r = e^{-r²/4}` as a complex number. -/
def E (r : ℝ) : ℂ := ((Real.exp (-(r ^ 2) / 4) : ℝ) : ℂ)

/-- `P(r) e^{-r²/4}` for a complex polynomial `P`. -/
def PE (P : Polynomial ℂ) (r : ℝ) : ℂ := P.eval (r : ℂ) * E r

lemma E_hasDerivAt (r : ℝ) : HasDerivAt E (((-r / 2 : ℝ) : ℂ) * E r) r := by
  have h1 : HasDerivAt (fun x : ℝ => -(x ^ 2) / 4) (-(2 * r) / 4) r := by
    have := ((hasDerivAt_pow 2 r).neg).div_const 4
    exact this.congr_deriv (by push_cast; ring)
  have h : HasDerivAt (fun x : ℝ => Real.exp (-(x ^ 2) / 4))
      (Real.exp (-(r ^ 2) / 4) * (-(2 * r) / 4)) r := h1.exp
  have h2 := h.ofReal_comp
  exact h2.congr_deriv (by simp only [E]; push_cast; ring)

lemma E_smooth : ContDiff ℝ ∞ E := by
  unfold E
  exact Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (by fun_prop))

lemma polyEval_hasDerivAt (P : Polynomial ℂ) (r : ℝ) :
    HasDerivAt (fun x : ℝ => P.eval (x : ℂ)) ((Polynomial.derivative P).eval (r : ℂ)) r :=
  (P.hasDerivAt (r : ℂ)).comp_ofReal

lemma polyEval_smooth (P : Polynomial ℂ) : ContDiff ℝ ∞ (fun x : ℝ => P.eval (x : ℂ)) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simpa using hp.add hq
  | monomial n a =>
    simp only [Polynomial.eval_monomial]
    exact contDiff_const.mul (Complex.ofRealCLM.contDiff.pow n)

lemma PE_smooth (P : Polynomial ℂ) : ContDiff ℝ ∞ (PE P) :=
  (polyEval_smooth P).mul E_smooth

lemma deriv_PE (P : Polynomial ℂ) :
    deriv (PE P) = PE (Polynomial.derivative P - Polynomial.C (1 / 2) * Polynomial.X * P) := by
  funext r
  have h := (polyEval_hasDerivAt P r).mul (E_hasDerivAt r)
  have h' : HasDerivAt (PE P) _ r := h
  rw [h'.deriv]
  simp only [PE, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  push_cast
  ring

lemma iter_PE : ∀ (j : ℕ) (P : Polynomial ℂ), ∃ Q : Polynomial ℂ,
    iteratedDeriv j (PE P) = PE Q := by
  intro j
  induction j with
  | zero => intro P; exact ⟨P, by simp⟩
  | succ j ih =>
    intro P
    obtain ⟨Q, hQ⟩ := ih (Polynomial.derivative P - Polynomial.C (1 / 2) * Polynomial.X * P)
    refine ⟨Q, ?_⟩
    rw [iteratedDeriv_succ', deriv_PE, hQ]

/-- absorption `r^N e^{-κ r²} ≤ A e^{-(κ/2) r²}` on `[1,∞)`. -/
lemma absorb (N : ℕ) (κ : ℝ) (hκ : 0 < κ) : ∃ A : ℝ, ∀ r : ℝ, 1 ≤ r →
    r ^ N * Real.exp (-(κ * r ^ 2)) ≤ A * Real.exp (-((κ / 2) * r ^ 2)) := by
  refine ⟨(2 / κ) ^ N * (N.factorial : ℝ), fun r hr => ?_⟩
  have hr0 : (0 : ℝ) ≤ r := by linarith
  have hx0 : 0 ≤ (κ / 2) * r ^ 2 := mul_nonneg (by linarith) (sq_nonneg r)
  set x := (κ / 2) * r ^ 2 with hx_def
  have hkey : Real.exp (-(κ * r ^ 2)) = Real.exp (-x) * Real.exp (-x) := by
    rw [← Real.exp_add]
    congr 1
    rw [hx_def]
    ring
  have hrN : r ^ N ≤ (2 / κ) ^ N * x ^ N := by
    have h1 : r ^ N ≤ (r ^ 2) ^ N := by
      calc r ^ N ≤ r ^ (2 * N) := pow_le_pow_right₀ hr (by omega)
        _ = (r ^ 2) ^ N := by rw [pow_mul]
    have h2 : r ^ 2 = (2 / κ) * x := by
      rw [hx_def]
      field_simp
    rw [h2, mul_pow] at h1
    exact h1
  have hfac : x ^ N ≤ (N.factorial : ℝ) * Real.exp x := by
    have h := Real.pow_div_factorial_le_exp x hx0 N
    rw [div_le_iff₀ (by positivity)] at h
    linarith [mul_comm (Real.exp x) (N.factorial : ℝ)]
  have hprod : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    simp
  have hmain : r ^ N * Real.exp (-x) ≤ (2 / κ) ^ N * (N.factorial : ℝ) := by
    calc r ^ N * Real.exp (-x) ≤ ((2 / κ) ^ N * x ^ N) * Real.exp (-x) :=
          mul_le_mul_of_nonneg_right hrN (Real.exp_pos _).le
      _ ≤ ((2 / κ) ^ N * ((N.factorial : ℝ) * Real.exp x)) * Real.exp (-x) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hfac
              (pow_nonneg (div_nonneg (by norm_num) hκ.le) N)) (Real.exp_pos _).le
      _ = (2 / κ) ^ N * (N.factorial : ℝ) := by
          linear_combination ((2 / κ) ^ N * (N.factorial : ℝ)) * hprod
  calc r ^ N * Real.exp (-(κ * r ^ 2)) = (r ^ N * Real.exp (-x)) * Real.exp (-x) := by
        rw [hkey]
        ring
    _ ≤ ((2 / κ) ^ N * (N.factorial : ℝ)) * Real.exp (-x) :=
        mul_le_mul_of_nonneg_right hmain (Real.exp_pos _).le

/-- polynomial bound on `[1,∞)` -/
lemma poly_bound (P : Polynomial ℂ) : ∃ C : ℝ, ∀ r : ℝ, 1 ≤ r →
    ‖P.eval (r : ℂ)‖ ≤ C * r ^ P.natDegree := by
  refine ⟨∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖, fun r hr => ?_⟩
  have hr0 : (0 : ℝ) ≤ r := by linarith
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  have hi' : i ≤ P.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr hi') (norm_nonneg _)

lemma gaussAt_PE (P : Polynomial ℂ) (j : ℕ) : GaussAt (PE P) j := by
  obtain ⟨Q, hQ⟩ := iter_PE j P
  obtain ⟨C, hC⟩ := poly_bound Q
  obtain ⟨A, hA⟩ := absorb Q.natDegree (1 / 4) (by norm_num)
  refine ⟨|C| * A, 1 / 8, by norm_num, fun r hr => ?_⟩
  rw [hQ]
  have hr0 : (0 : ℝ) ≤ r := by linarith
  have hE : ‖E r‖ = Real.exp (-(1 / 4 * r ^ 2)) := by
    unfold E
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    congr 1
    ring
  have h1 : ‖Q.eval (r : ℂ)‖ ≤ |C| * r ^ Q.natDegree :=
    (hC r hr).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hr0 _))
  have h2 := hA r hr
  have hA0 : 0 ≤ A := by
    have hp : 0 ≤ r ^ Q.natDegree * Real.exp (-(1 / 4 * r ^ 2)) :=
      mul_nonneg (pow_nonneg hr0 _) (Real.exp_pos _).le
    by_contra hneg
    push_neg at hneg
    have : A * Real.exp (-(1 / 4 / 2 * r ^ 2)) < 0 :=
      mul_neg_of_neg_of_pos hneg (Real.exp_pos _)
    linarith
  calc ‖PE Q r‖ = ‖Q.eval (r : ℂ)‖ * ‖E r‖ := by unfold PE; rw [norm_mul]
    _ ≤ (|C| * r ^ Q.natDegree) * Real.exp (-(1 / 4 * r ^ 2)) := by
        rw [hE]; exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = |C| * (r ^ Q.natDegree * Real.exp (-(1 / 4 * r ^ 2))) := by ring
    _ ≤ |C| * (A * Real.exp (-(1 / 4 / 2 * r ^ 2))) :=
        mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    _ = |C| * A * Real.exp (-(1 / 8 * r ^ 2)) := by
        have : (1 : ℝ) / 4 / 2 = 1 / 8 := by norm_num
        rw [this]; ring

lemma polyAt_of_gaussAt {f : ℝ → ℂ} {j : ℕ} (h : GaussAt f j) : PolyAt f j := by
  obtain ⟨C, κ, hκ, hb⟩ := h
  refine ⟨|C|, 0, fun r hr => ?_⟩
  have hexp : Real.exp (-(κ * r ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ κ * r ^ 2 := mul_nonneg hκ.le (sq_nonneg r)
    linarith
  calc ‖iteratedDeriv j f r‖ ≤ C * Real.exp (-(κ * r ^ 2)) := hb r hr
    _ ≤ |C| * Real.exp (-(κ * r ^ 2)) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
    _ ≤ |C| * 1 := mul_le_mul_of_nonneg_left hexp (abs_nonneg _)
    _ = |C| * r ^ 0 := by simp

/-- Leibniz bound on `(0,∞)`. -/
lemma leib (f g : ℝ → ℂ) (j : ℕ) (r : ℝ) (hr : 0 < r) (hf : ContDiffOn ℝ ∞ f (Ioi 0))
    (hg : ContDiffOn ℝ ∞ g (Ioi 0)) :
    ‖iteratedDeriv j (fun s => f s * g s) r‖ ≤
      ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        (‖iteratedDeriv i f r‖ * ‖iteratedDeriv (j - i) g r‖) := by
  have hx : r ∈ Ioi (0 : ℝ) := hr
  have hfw : ContDiffWithinAt ℝ j f (Ioi 0) r := (hf r hx).of_le (by exact_mod_cast le_top)
  have hgw : ContDiffWithinAt ℝ j g (Ioi 0) r := (hg r hx).of_le (by exact_mod_cast le_top)
  have hL : iteratedDerivWithin j (f * g) (Ioi 0) r = ∑ i ∈ Finset.range (j + 1),
      (j.choose i : ℂ) * iteratedDerivWithin i f (Ioi 0) r *
        iteratedDerivWithin (j - i) g (Ioi 0) r :=
    iteratedDerivWithin_mul hx isOpen_Ioi.uniqueDiffOn hfw hgw
  have hfi : ∀ i : ℕ, iteratedDerivWithin i f (Ioi 0) r = iteratedDeriv i f r :=
    fun i => iteratedDerivWithin_of_isOpen (n := i) isOpen_Ioi hx
  have hgi : ∀ i : ℕ, iteratedDerivWithin i g (Ioi 0) r = iteratedDeriv i g r :=
    fun i => iteratedDerivWithin_of_isOpen (n := i) isOpen_Ioi hx
  have hfgi : ∀ i : ℕ, iteratedDerivWithin i (f * g) (Ioi 0) r = iteratedDeriv i (f * g) r :=
    fun i => iteratedDerivWithin_of_isOpen (n := i) isOpen_Ioi hx
  simp only [hfi, hgi, hfgi] at hL
  show ‖iteratedDeriv j (f * g) r‖ ≤ _
  rw [hL]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, norm_mul, Complex.norm_natCast]
  exact le_of_eq (by ring)

lemma unifP (g : ℝ → ℂ) (n : ℕ) (h : ∀ i < n, PolyAt g i) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ i < n, ∀ r : ℝ, 1 ≤ r →
      ‖iteratedDeriv i g r‖ ≤ C * r ^ N := by
  induction n with
  | zero => exact ⟨0, 0, le_refl _, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨C, N, hC0, hb⟩ := ih (fun i hi => h i (by omega))
    obtain ⟨Cn, Nn, hbn⟩ := h n (by omega)
    refine ⟨|C| + |Cn|, max N Nn, add_nonneg (abs_nonneg _) (abs_nonneg _), fun i hi r hr => ?_⟩
    have hr0 : (0 : ℝ) ≤ r := by linarith
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
    · calc ‖iteratedDeriv i g r‖ ≤ C * r ^ N := hb i hi' r hr
        _ ≤ (|C| + |Cn|) * r ^ (max N Nn) := by
          calc C * r ^ N ≤ (|C| + |Cn|) * r ^ N :=
                mul_le_mul_of_nonneg_right (by linarith [le_abs_self C, abs_nonneg Cn])
                  (pow_nonneg hr0 _)
            _ ≤ (|C| + |Cn|) * r ^ (max N Nn) :=
                mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr (le_max_left _ _))
                  (add_nonneg (abs_nonneg _) (abs_nonneg _))
    · calc ‖iteratedDeriv i g r‖ ≤ Cn * r ^ Nn := hbn r hr
        _ ≤ (|C| + |Cn|) * r ^ (max N Nn) := by
          calc Cn * r ^ Nn ≤ (|C| + |Cn|) * r ^ Nn :=
                mul_le_mul_of_nonneg_right (by linarith [le_abs_self Cn, abs_nonneg C])
                  (pow_nonneg hr0 _)
            _ ≤ (|C| + |Cn|) * r ^ (max N Nn) :=
                mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr (le_max_right _ _))
                  (add_nonneg (abs_nonneg _) (abs_nonneg _))

/-- Leibniz for polynomially bounded derivatives. -/
lemma polyMulPoly (f g : ℝ → ℂ) (n : ℕ) (hf : ContDiffOn ℝ ∞ f (Ioi 0))
    (hg : ContDiffOn ℝ ∞ g (Ioi 0)) (hF : ∀ j < n, PolyAt f j) (hG : ∀ j < n, PolyAt g j) :
    ∀ j < n, PolyAt (fun r => f r * g r) j := by
  intro j hj
  obtain ⟨C1, N1, hC1, hb1⟩ := unifP f n hF
  obtain ⟨C2, N2, hC2, hb2⟩ := unifP g n hG
  refine ⟨∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (C1 * C2), N1 + N2, fun r hr => ?_⟩
  have hr0 : (0 : ℝ) ≤ r := by linarith
  have hrpos : (0 : ℝ) < r := by linarith
  refine (leib f g j r hrpos hf hg).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i < j + 1 := Finset.mem_range.mp hi
  have h1 := hb1 i (by omega) r hr
  have h2 := hb2 (j - i) (by omega) r hr
  have hc : (0 : ℝ) ≤ (j.choose i : ℝ) := Nat.cast_nonneg _
  calc (j.choose i : ℝ) * (‖iteratedDeriv i f r‖ * ‖iteratedDeriv (j - i) g r‖)
      ≤ (j.choose i : ℝ) * ((C1 * r ^ N1) * (C2 * r ^ N2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (norm_nonneg _)
          (mul_nonneg hC1 (pow_nonneg hr0 _))) hc
    _ = ((j.choose i : ℝ) * (C1 * C2)) * r ^ (N1 + N2) := by rw [pow_add]; ring

/-! ### The factor `G = (λ + 2iΩ)⁻¹` -/

def Gf (lam : ℂ) (r : ℝ) : ℂ := (lam + 2 * Complex.I * E r)⁻¹

lemma E_im (r : ℝ) : (E r).im = 0 := by
  unfold E
  exact Complex.ofReal_im _

lemma den_re (lam : ℂ) (r : ℝ) : (lam + 2 * Complex.I * E r).re = lam.re := by
  simp [E_im]

lemma den_ne (lam : ℂ) (h : 0 < lam.re) (r : ℝ) : lam + 2 * Complex.I * E r ≠ 0 := by
  intro h0
  have := congrArg Complex.re h0
  rw [den_re] at this
  simp at this
  linarith

lemma Gf_smooth (lam : ℂ) (h : 0 < lam.re) : ContDiff ℝ ∞ (Gf lam) := by
  unfold Gf
  exact (contDiff_const.add (contDiff_const.mul E_smooth)).inv (den_ne lam h)

lemma Gf_deriv (lam : ℂ) (h : 0 < lam.re) :
    deriv (Gf lam) =
      fun r => (Gf lam r * Gf lam r) * PE (Polynomial.C Complex.I * Polynomial.X) r := by
  funext r
  have hd : HasDerivAt (fun x : ℝ => lam + 2 * Complex.I * E x)
      (2 * Complex.I * (((-r / 2 : ℝ) : ℂ) * E r)) r := by
    have := (hasDerivAt_const r lam).add ((hasDerivAt_const r (2 * Complex.I)).mul (E_hasDerivAt r))
    exact this.congr_deriv (by ring)
  have h3 := hd.inv (den_ne lam h r)
  have h4 : HasDerivAt (fun x => (lam + 2 * Complex.I * E x)⁻¹) _ r := h3
  show deriv (fun x => (lam + 2 * Complex.I * E x)⁻¹) r = _
  rw [h4.deriv]
  have hne := den_ne lam h r
  simp only [Gf, PE, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  push_cast
  field_simp

lemma Gf_bound (lam : ℂ) (h : 0 < lam.re) (r : ℝ) : ‖Gf lam r‖ ≤ 1 / lam.re := by
  unfold Gf
  rw [norm_inv]
  have hre : lam.re ≤ ‖lam + 2 * Complex.I * E r‖ := by
    have := Complex.abs_re_le_norm (lam + 2 * Complex.I * E r)
    rw [den_re] at this
    exact (le_abs_self _).trans this
  rw [one_div]
  exact inv_anti₀ h hre

lemma polyAt_Gf (lam : ℂ) (h : 0 < lam.re) : ∀ n : ℕ, ∀ j < n, PolyAt (Gf lam) j := by
  have hHp : ∀ j, PolyAt (PE (Polynomial.C Complex.I * Polynomial.X)) j :=
    fun j => polyAt_of_gaussAt (gaussAt_PE _ j)
  have hGs : ContDiffOn ℝ ∞ (Gf lam) (Ioi 0) := (Gf_smooth lam h).contDiffOn
  have hHs : ContDiffOn ℝ ∞ (PE (Polynomial.C Complex.I * Polynomial.X)) (Ioi 0) :=
    (PE_smooth _).contDiffOn
  intro n
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
    · exact ih j hj'
    · cases j with
      | zero =>
        refine ⟨1 / lam.re, 0, fun r hr => ?_⟩
        simpa using Gf_bound lam h r
      | succ m =>
        have hGG : ∀ i < m + 1, PolyAt (fun r => Gf lam r * Gf lam r) i :=
          polyMulPoly _ _ (m + 1) hGs hGs (fun i hi => ih i hi) (fun i hi => ih i hi)
        have hGGs : ContDiffOn ℝ ∞ (fun r => Gf lam r * Gf lam r) (Ioi 0) := hGs.mul hGs
        have := polyMulPoly _ _ (m + 1) hGGs hHs hGG (fun i _ => hHp i) m (by omega)
        unfold PolyAt at this ⊢
        rw [iteratedDeriv_succ', Gf_deriv lam h]
        exact this

end ACoefHelp

open ACoefHelp in
theorem aCoefGauss : UnforcedLeray.Short.IIb.ACoefGauss := by
  intro lam hlam
  let F : Polynomial ℂ :=
    Polynomial.C (2 * Complex.I) * (Polynomial.C (1 / 4) * Polynomial.X ^ 2 - Polynomial.C 2)
  have heq : aCoef lam = fun r => PE F r * Gf lam r := by
    funext r
    simp only [aCoef, PE, Gf, F, E, Planar.strainK, Planar.vortexOmega, div_eq_mul_inv,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X]
    push_cast
    ring
  have hFs : ContDiffOn ℝ ∞ (PE F) (Ioi 0) := (PE_smooth F).contDiffOn
  have hGs : ContDiffOn ℝ ∞ (Gf lam) (Ioi 0) := (Gf_smooth lam hlam).contDiffOn
  rw [heq]
  refine ⟨hFs.mul hGs, fun j => ?_⟩
  exact gaussMulPoly (PE F) (Gf lam) (j + 1) hFs hGs (fun i _ => gaussAt_PE F i)
    (fun i hi => polyAt_Gf lam hlam (j + 1) i hi) j (by omega)

end UnforcedLeray.Short.IIb
