import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_6_1_3_1_org_1_org_1_1_2_1_3

/-!
# Leaf 1: weighted heat-kernel jet bound

Source `the November 2 reference manuscript`
455-458 and proof 527-535 (scaling of `G_{nu s}`).

The proof uses the explicit scaling form of the heat kernel. Writing `g(r) = (sqrt r)^{-1}` and
`x = e g(r)`, every `r`-derivative of `heatKernel1 (nu r) e` is `g^(2l+1) P_l(x) exp(-x^2/(4 nu))`
for a polynomial `P_l`, and every `e`-derivative of `P(e w) exp(-(e w)^2/(4 nu))` is again of the
same shape. A polynomial times the Gaussian is bounded, and `(1+|eta|) <= sqrt s (1+|x|)` for `s >= 1`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Polynomial Real

namespace UnforcedLeray.Short.PartIIIb.Concrete.HDWRSub.L1

/-- Scaling form of the heat kernel, `(4 pi nu r)^{-1/2} = c g(r)`. -/
theorem heat_form {ν r e : ℝ} (hν : 0 < ν) (hr : 0 < r) :
    UnforcedLeray.Short.PartI.heatKernel1 (ν * r) e =
      (Real.sqrt (4 * π * ν))⁻¹ * (Real.sqrt r)⁻¹ *
        Real.exp (-((e * (Real.sqrt r)⁻¹) ^ 2) / (4 * ν)) := by
  unfold UnforcedLeray.Short.PartI.heatKernel1
  have h4 : 4 * π * (ν * r) = (4 * π * ν) * r := by ring
  have hs : (Real.sqrt r) ^ 2 = r := Real.sq_sqrt hr.le
  have hν0 : ν ≠ 0 := hν.ne'
  have hr0 : r ≠ 0 := hr.ne'
  have he : -(e ^ 2) / (4 * (ν * r)) = -((e * (Real.sqrt r)⁻¹) ^ 2) / (4 * ν) := by
    rw [mul_pow, inv_pow, hs]
    field_simp
  rw [h4, Real.sqrt_mul (by positivity), mul_inv, he]

/-- Closed form of one `r`-derivative step. -/
theorem hasDerivAt_closed (ν : ℝ) (m : ℕ) (P : Polynomial ℝ) (e r : ℝ) (hr : 0 < r) :
    HasDerivAt (fun r' : ℝ => ((Real.sqrt r')⁻¹) ^ (m + 1) * P.eval (e * (Real.sqrt r')⁻¹) *
        Real.exp (-((e * (Real.sqrt r')⁻¹) ^ 2) / (4 * ν)))
      (((Real.sqrt r)⁻¹) ^ (m + 3) *
        (C (-(((m : ℝ) + 1) / 2)) * P - C (1 / 2 : ℝ) * X * P.derivative +
          C (1 / (4 * ν)) * X ^ 2 * P).eval (e * (Real.sqrt r)⁻¹) *
        Real.exp (-((e * (Real.sqrt r)⁻¹) ^ 2) / (4 * ν))) r := by
  have hsq : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  have hg : HasDerivAt (fun r' : ℝ => (Real.sqrt r')⁻¹) (-((Real.sqrt r)⁻¹) ^ 3 / 2) r := by
    have h := (Real.hasDerivAt_sqrt hr.ne').inv hsq.ne'
    refine h.congr_deriv ?_
    field_simp
    <;> ring
  have hx : HasDerivAt (fun r' : ℝ => e * (Real.sqrt r')⁻¹)
      (e * (-((Real.sqrt r)⁻¹) ^ 3 / 2)) r := hg.const_mul e
  have hP : HasDerivAt (fun r' : ℝ => P.eval (e * (Real.sqrt r')⁻¹))
      (P.derivative.eval (e * (Real.sqrt r)⁻¹) * (e * (-((Real.sqrt r)⁻¹) ^ 3 / 2))) r :=
    HasDerivAt.comp (x := r) (h := fun r' : ℝ => e * (Real.sqrt r')⁻¹)
      (h₂ := fun y : ℝ => P.eval y) (P.hasDerivAt (e * (Real.sqrt r)⁻¹)) hx
  have hin : HasDerivAt (fun r' : ℝ => -((e * (Real.sqrt r')⁻¹) ^ 2) / (4 * ν))
      (-(2 * (e * (Real.sqrt r)⁻¹) * (e * (-((Real.sqrt r)⁻¹) ^ 3 / 2))) / (4 * ν)) r := by
    have h := ((hx.pow 2).neg).div_const (4 * ν)
    refine h.congr_deriv ?_
    norm_num
  have hE := hin.exp
  have hn := hg.pow (m + 1)
  have htot := (hn.mul hP).mul hE
  refine htot.congr_deriv ?_
  simp only [Pi.pow_apply, Pi.mul_apply, eval_add, eval_sub, eval_mul, eval_C, eval_X,
    eval_pow, Nat.add_sub_cancel]
  push_cast
  ring

/-- Derivative in `e` of a Gaussian-polynomial product. -/
theorem hasDerivAt_e (ν : ℝ) (P : Polynomial ℝ) (K w e : ℝ) :
    HasDerivAt (fun e' : ℝ => K * P.eval (e' * w) * Real.exp (-((e' * w) ^ 2) / (4 * ν)))
      (K * w * (P.derivative - C (1 / (2 * ν)) * X * P).eval (e * w) *
        Real.exp (-((e * w) ^ 2) / (4 * ν))) e := by
  have hx : HasDerivAt (fun e' : ℝ => e' * w) w e := hasDerivAt_mul_const w
  have hP : HasDerivAt (fun e' : ℝ => P.eval (e' * w)) (P.derivative.eval (e * w) * w) e :=
    HasDerivAt.comp (x := e) (h := fun e' : ℝ => e' * w)
      (h₂ := fun y : ℝ => P.eval y) (P.hasDerivAt (e * w)) hx
  have hin : HasDerivAt (fun e' : ℝ => -((e' * w) ^ 2) / (4 * ν))
      (-(2 * (e * w) * w) / (4 * ν)) e := by
    have h := ((hx.pow 2).neg).div_const (4 * ν)
    refine h.congr_deriv ?_
    norm_num
  have hE := hin.exp
  have htot := (hP.const_mul K).mul hE
  refine htot.congr_deriv ?_
  simp only [Pi.mul_apply, eval_sub, eval_mul, eval_C, eval_X]
  field_simp
  ring

/-- Iterated `e`-derivatives of `P(e w) exp(-(e w)^2/(4 nu))` keep the same shape. -/
theorem iter_e (ν : ℝ) (hν : 0 < ν) (b : ℕ) : ∀ P : Polynomial ℝ, ∃ Q : Polynomial ℝ,
    ∀ K w η : ℝ,
      iteratedDeriv b (fun e => K * P.eval (e * w) * Real.exp (-((e * w) ^ 2) / (4 * ν))) η =
        K * w ^ b * Q.eval (η * w) * Real.exp (-((η * w) ^ 2) / (4 * ν)) := by
  induction b with
  | zero => intro P; exact ⟨P, fun K w η => by simp⟩
  | succ b ih =>
    intro P
    obtain ⟨Q, hQ⟩ := ih (P.derivative - C (1 / (2 * ν)) * X * P)
    refine ⟨Q, fun K w η => ?_⟩
    have hd : deriv (fun e' : ℝ => K * P.eval (e' * w) * Real.exp (-((e' * w) ^ 2) / (4 * ν)))
        = fun e' : ℝ => K * w * (P.derivative - C (1 / (2 * ν)) * X * P).eval (e' * w) *
            Real.exp (-((e' * w) ^ 2) / (4 * ν)) :=
      funext fun e' => (hasDerivAt_e ν P K w e').deriv
    rw [iteratedDeriv_succ', hd, hQ (K * w) w η]
    ring

/-- Bounded-ness of a continuous function tending to zero at infinity. -/
theorem bdd_of_tendsto_cocompact {h : ℝ → ℝ} (hc : Continuous h)
    (ht : Tendsto h (cocompact ℝ) (𝓝 0)) : ∃ D : ℝ, ∀ x, h x ≤ D := by
  have hev : ∀ᶠ x in cocompact ℝ, h x ∈ Iio (1 : ℝ) :=
    ht.eventually (Iio_mem_nhds (by norm_num))
  obtain ⟨t, htc, hsub⟩ := Filter.mem_cocompact.mp hev
  obtain ⟨C0, hC0⟩ := htc.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C0 1, fun x => ?_⟩
  by_cases hx : x ∈ t
  · have h1 := hC0 x hx
    rw [Real.norm_eq_abs] at h1
    exact le_trans (le_trans (le_abs_self _) h1) (le_max_left _ _)
  · have h1 : h x < 1 := hsub hx
    exact le_trans h1.le (le_max_right _ _)

/-- A polynomial times the Gaussian is bounded, with the polynomial weight `(1+|x|)^m`. -/
theorem gauss_poly_bound {ν : ℝ} (hν : 0 < ν) (Q : Polynomial ℝ) (m : ℕ) :
    ∃ D : ℝ, ∀ x : ℝ, (1 + |x|) ^ m * |Q.eval x| * Real.exp (-(x ^ 2) / (4 * ν)) ≤ D := by
  obtain ⟨A, hA_def⟩ : ∃ A : ℝ, A = ∑ i ∈ Finset.range (Q.natDegree + 1), |Q.coeff i| :=
    ⟨_, rfl⟩
  have hA : 0 ≤ A := by
    rw [hA_def]
    exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hpoly : ∀ x : ℝ, |Q.eval x| ≤ A * (1 + |x|) ^ Q.natDegree := by
    intro x
    rw [Polynomial.eval_eq_sum_range]
    calc |∑ i ∈ Finset.range (Q.natDegree + 1), Q.coeff i * x ^ i|
        ≤ ∑ i ∈ Finset.range (Q.natDegree + 1), |Q.coeff i * x ^ i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range (Q.natDegree + 1), |Q.coeff i| * (1 + |x|) ^ Q.natDegree := by
          apply Finset.sum_le_sum
          intro i hi
          have hi' : i ≤ Q.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          rw [abs_mul, abs_pow]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          calc |x| ^ i ≤ (1 + |x|) ^ i :=
                pow_le_pow_left₀ (abs_nonneg _) (by linarith [abs_nonneg x]) i
            _ ≤ (1 + |x|) ^ Q.natDegree :=
                pow_le_pow_right₀ (by linarith [abs_nonneg x]) hi'
      _ = A * (1 + |x|) ^ Q.natDegree := by rw [hA_def, Finset.sum_mul]
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = m + Q.natDegree := ⟨_, rfl⟩
  obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = 1 / (4 * ν) := ⟨_, rfl⟩
  have ha : 0 < a := by rw [ha_def]; positivity
  obtain ⟨h, hh⟩ : ∃ h : ℝ → ℝ, h = fun x : ℝ =>
      A * 2 ^ (M - 1) * (|x| ^ (0 : ℝ) * Real.exp (-a * x ^ 2) +
        |x| ^ (M : ℝ) * Real.exp (-a * x ^ 2)) := ⟨_, rfl⟩
  have hfb : ∀ x : ℝ, (1 + |x|) ^ m * |Q.eval x| * Real.exp (-(x ^ 2) / (4 * ν)) ≤ h x := by
    intro x
    have hE : Real.exp (-(x ^ 2) / (4 * ν)) = Real.exp (-a * x ^ 2) := by
      congr 1
      rw [ha_def]
      ring
    have hE0 : 0 ≤ Real.exp (-a * x ^ 2) := (Real.exp_pos _).le
    have h1 : (1 + |x|) ^ m * |Q.eval x| ≤ (1 + |x|) ^ m * (A * (1 + |x|) ^ Q.natDegree) :=
      mul_le_mul_of_nonneg_left (hpoly x) (by positivity)
    have h2 : (1 + |x|) ^ M ≤ 2 ^ (M - 1) * (1 ^ M + |x| ^ M) :=
      add_pow_le zero_le_one (abs_nonneg x) M
    rw [hE, hh]
    calc (1 + |x|) ^ m * |Q.eval x| * Real.exp (-a * x ^ 2)
        ≤ (1 + |x|) ^ m * (A * (1 + |x|) ^ Q.natDegree) * Real.exp (-a * x ^ 2) :=
          mul_le_mul_of_nonneg_right h1 hE0
      _ = A * (1 + |x|) ^ M * Real.exp (-a * x ^ 2) := by rw [hM]; ring
      _ ≤ A * (2 ^ (M - 1) * (1 ^ M + |x| ^ M)) * Real.exp (-a * x ^ 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hA) hE0
      _ = A * 2 ^ (M - 1) * (|x| ^ (0 : ℝ) * Real.exp (-a * x ^ 2) +
          |x| ^ (M : ℝ) * Real.exp (-a * x ^ 2)) := by
          simp only [Real.rpow_zero, Real.rpow_natCast, one_pow]
          ring
  have hc : Continuous h := by
    rw [hh]
    apply Continuous.mul continuous_const
    apply Continuous.add
    · exact (continuous_abs.rpow_const (fun _ => Or.inr (by norm_num))).mul (by fun_prop)
    · exact (continuous_abs.rpow_const (fun _ => Or.inr (by positivity))).mul (by fun_prop)
  have ht : Tendsto h (cocompact ℝ) (𝓝 0) := by
    have t0 := tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact ha (0 : ℝ)
    have tM := tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact ha (M : ℝ)
    have := (t0.add tM).const_mul (A * 2 ^ (M - 1))
    rw [hh]
    simpa using this
  obtain ⟨D, hD⟩ := bdd_of_tendsto_cocompact hc ht
  exact ⟨D, fun x => le_trans (hfb x) (hD x)⟩

/-- Exponent identity `u^m * (u^{-1})^N = s^{(m-N)/2}` for `u = sqrt s`. -/
theorem key_pow (s : ℝ) (hs : 0 < s) (m N : ℕ) :
    (Real.sqrt s) ^ m * ((Real.sqrt s)⁻¹) ^ N = s ^ (((m : ℝ) - (N : ℝ)) / 2) := by
  have ht : 0 < s ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hs _
  rw [Real.sqrt_eq_rpow, show ((m : ℝ) - (N : ℝ)) / 2 = (1 / 2 : ℝ) * ((m : ℝ) - (N : ℝ)) by ring,
    Real.rpow_mul hs.le, Real.rpow_sub ht, Real.rpow_natCast, Real.rpow_natCast, inv_pow]
  ring

/-- The `r`-derivatives of `heatKernel1 (nu r) e`, in closed form. -/
theorem heat_r_form {ν : ℝ} (hν : 0 < ν) (ℓ : ℕ) : ∃ P : Polynomial ℝ, ∀ e r : ℝ, 0 < r →
    iteratedDeriv ℓ (fun r' => UnforcedLeray.Short.PartI.heatKernel1 (ν * r') e) r =
      ((Real.sqrt r)⁻¹) ^ (2 * ℓ + 1) * P.eval (e * (Real.sqrt r)⁻¹) *
        Real.exp (-((e * (Real.sqrt r)⁻¹) ^ 2) / (4 * ν)) := by
  induction ℓ with
  | zero =>
    refine ⟨C (Real.sqrt (4 * π * ν))⁻¹, fun e r hr => ?_⟩
    rw [iteratedDeriv_zero, heat_form hν hr, eval_C]
    ring
  | succ ℓ ih =>
    obtain ⟨P, hP⟩ := ih
    refine ⟨C (-((((2 * ℓ : ℕ) : ℝ) + 1) / 2)) * P - C (1 / 2 : ℝ) * X * P.derivative +
      C (1 / (4 * ν)) * X ^ 2 * P, fun e r hr => ?_⟩
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv ℓ (fun r' => UnforcedLeray.Short.PartI.heatKernel1 (ν * r') e)
        =ᶠ[𝓝 r] (fun r' : ℝ => ((Real.sqrt r')⁻¹) ^ (2 * ℓ + 1) * P.eval (e * (Real.sqrt r')⁻¹) *
          Real.exp (-((e * (Real.sqrt r')⁻¹) ^ 2) / (4 * ν))) := by
      filter_upwards [Ioi_mem_nhds hr] with r' hr'
      exact hP e r' hr'
    rw [hev.deriv_eq, (hasDerivAt_closed ν (2 * ℓ) P e r hr).deriv]
    rw [show 2 * (ℓ + 1) + 1 = 2 * ℓ + 3 by ring]

end UnforcedLeray.Short.PartIIIb.Concrete.HDWRSub.L1

open UnforcedLeray.Short.PartIIIb.Concrete.HDWRSub L1 in
/-- **Leaf 1: weighted heat-kernel jet bound** (SP 535-537). -/
theorem heatKernelWeightedBound :
    UnforcedLeray.Short.PartIIIb.Concrete.HDWRSub.HeatKernelWeightedBound := by
  unfold UnforcedLeray.Short.PartIIIb.Concrete.HDWRSub.HeatKernelWeightedBound
  intro ν hν m b ℓ
  obtain ⟨P, hP⟩ := heat_r_form hν ℓ
  obtain ⟨Q, hQ⟩ := iter_e ν hν b P
  obtain ⟨D, hD⟩ := gauss_poly_bound hν Q m
  refine ⟨D, fun s hs η => ?_⟩
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs
  have hu1 : 1 ≤ Real.sqrt s := by
    have := Real.sqrt_le_sqrt hs
    simpa using this
  have hfun : (fun e => iteratedDeriv ℓ (fun r => UnforcedLeray.Short.PartI.heatKernel1 (ν * r) e) s)
      = fun e => ((Real.sqrt s)⁻¹) ^ (2 * ℓ + 1) * P.eval (e * (Real.sqrt s)⁻¹) *
          Real.exp (-((e * (Real.sqrt s)⁻¹) ^ 2) / (4 * ν)) :=
    funext fun e => hP e s hs0
  simp only [UnforcedLeray.Short.PartIIIb.Concrete.HDWRSub.jet]
  rw [hfun, hQ]
  have hexp : ((m : ℝ) - ((2 * ℓ + 1 + b : ℕ) : ℝ)) / 2 = (((m : ℝ) - b) - 1) / 2 - ℓ := by
    push_cast
    ring
  have hupos0 : 0 < Real.sqrt s := by linarith
  generalize hu : Real.sqrt s = u at hupos0 hu1 ⊢
  have hpos : 0 < u⁻¹ := inv_pos.mpr hupos0
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = η * u⁻¹ := ⟨_, rfl⟩
  have hη : η = x * u := by
    rw [hx]
    field_simp
  rw [← hx]
  have hineq : 1 + |η| ≤ u * (1 + |x|) := by
    rw [hη, abs_mul, abs_of_pos hupos0]
    nlinarith [abs_nonneg x]
  have hE0 : 0 < Real.exp (-(x ^ 2) / (4 * ν)) := Real.exp_pos _
  have hnorm : ‖u⁻¹ ^ (2 * ℓ + 1) * u⁻¹ ^ b * Q.eval x * Real.exp (-(x ^ 2) / (4 * ν))‖
      = u⁻¹ ^ (2 * ℓ + 1 + b) * |Q.eval x| * Real.exp (-(x ^ 2) / (4 * ν)) := by
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos (pow_pos hpos (2 * ℓ + 1)),
      abs_of_pos (pow_pos hpos b), abs_of_pos hE0, pow_add]
    ring
  have hmain : (1 + |η|) ^ m *
      ‖u⁻¹ ^ (2 * ℓ + 1) * u⁻¹ ^ b * Q.eval x * Real.exp (-(x ^ 2) / (4 * ν))‖
      ≤ u ^ m * u⁻¹ ^ (2 * ℓ + 1 + b) * D := by
    rw [hnorm]
    have hw0 : 0 ≤ u⁻¹ ^ (2 * ℓ + 1 + b) * |Q.eval x| * Real.exp (-(x ^ 2) / (4 * ν)) :=
      mul_nonneg (mul_nonneg (pow_nonneg hpos.le _) (abs_nonneg _)) hE0.le
    calc (1 + |η|) ^ m * (u⁻¹ ^ (2 * ℓ + 1 + b) * |Q.eval x| * Real.exp (-(x ^ 2) / (4 * ν)))
        ≤ (u * (1 + |x|)) ^ m *
            (u⁻¹ ^ (2 * ℓ + 1 + b) * |Q.eval x| * Real.exp (-(x ^ 2) / (4 * ν))) :=
          mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (by positivity) hineq m) hw0
      _ = u ^ m * u⁻¹ ^ (2 * ℓ + 1 + b) *
            ((1 + |x|) ^ m * |Q.eval x| * Real.exp (-(x ^ 2) / (4 * ν))) := by
          rw [mul_pow]
          ring
      _ ≤ u ^ m * u⁻¹ ^ (2 * ℓ + 1 + b) * D :=
          mul_le_mul_of_nonneg_left (hD x)
            (mul_nonneg (pow_nonneg hupos0.le _) (pow_nonneg hpos.le _))
  have hkey : u ^ m * u⁻¹ ^ (2 * ℓ + 1 + b) = s ^ ((((m : ℝ) - b) - 1) / 2 - ℓ) := by
    rw [← hu, ← hexp]
    exact key_pow s hs0 m (2 * ℓ + 1 + b)
  calc (1 + |η|) ^ m *
        ‖u⁻¹ ^ (2 * ℓ + 1) * u⁻¹ ^ b * Q.eval x * Real.exp (-(x ^ 2) / (4 * ν))‖
      ≤ u ^ m * u⁻¹ ^ (2 * ℓ + 1 + b) * D := hmain
    _ = D * s ^ ((((m : ℝ) - b) - 1) / 2 - ℓ) := by
          rw [← hkey]
          ring
