import UnforcedLeray.Short.PartIIa.Sub.R02
import UnforcedLeray.Units.B0191

/-!


Source of record: `the November 2 reference manuscript`, lines 1255-1257 and
1268-1272 (heat kernel profile calculus).  Unit `B0191` supplies the self-similarity and the
`K`-homogeneity of the heat derivatives; this file adds the Hermite-type form of the heat
derivatives, the uniform weighted bound, and the profile-level derivative identities.

Plan.
* `lhPoly`: `∂_η^j G_t(η) = (√(4πt))⁻¹ (√t)^{-j} Q_j(η/√t) e^{-η²/(4t)}` for a polynomial `Q_j`.
* `lhPolyGauss`, `lhExpPow`: `(1+u²)^m |Q(u)| e^{-u²/4}` is bounded.
* `lhBound1D`: for `0 < ν ≤ 1` and `s ≥ 1`, `(1+η²/s)^m |∂_η^j G_{νs}(η)| ≤ C (νs)^{-(j+1)/2}`.
* `lhP`: the profile function `(q,(η,s)) ↦ ∂_η^j G_{νs}(η)`, differentiable on `s > 0`, with
  `∂_η` and `∂_s` read off from `B0191.hasDerivAt_heatDeriv_eta` and `hasDerivAt_heatDeriv_age`.
* `lateHeatProfile`: the three clauses of `LateHeatProfile`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0184
open UnforcedLeray.Short.PartI (heatKernel1)

/-! ### Part 1: heat derivatives are Gaussians times polynomials -/

/-- `∂_η^j G_t = (√(4πt))⁻¹ (√t)^{-j} Q_j(η/√t) e^{-η²/(4t)}` for some polynomial `Q_j`. -/
theorem lhPoly (j : ℕ) :
    ∃ Q : Polynomial ℝ, ∀ t : ℝ, 0 < t → ∀ η : ℝ,
      iteratedDeriv j (heatKernel1 t) η =
        (Real.sqrt (4 * Real.pi * t))⁻¹ * (Real.sqrt t)⁻¹ ^ j * Q.eval (η / Real.sqrt t) *
          Real.exp (-(η ^ 2) / (4 * t)) := by
  induction j with
  | zero =>
    refine ⟨1, fun t _ η => ?_⟩
    rw [iteratedDeriv_zero]
    simp [heatKernel1]
  | succ j ih =>
    obtain ⟨Q, hQ⟩ := ih
    refine ⟨Q.derivative - Polynomial.C (1 / 2 : ℝ) * Polynomial.X * Q, fun t ht η => ?_⟩
    obtain ⟨s0, hs0, rfl⟩ : ∃ s0 : ℝ, 0 < s0 ∧ t = s0 ^ 2 :=
      ⟨Real.sqrt t, Real.sqrt_pos.2 ht, (Real.sq_sqrt ht.le).symm⟩
    have hs0' : s0 ≠ 0 := hs0.ne'
    have hfun : iteratedDeriv j (heatKernel1 (s0 ^ 2)) = fun y : ℝ =>
        (Real.sqrt (4 * Real.pi * s0 ^ 2))⁻¹ * (Real.sqrt (s0 ^ 2))⁻¹ ^ j *
          Q.eval (y / Real.sqrt (s0 ^ 2)) * Real.exp (-(y ^ 2) / (4 * s0 ^ 2)) :=
      funext (hQ (s0 ^ 2) ht)
    rw [Real.sqrt_sq hs0.le] at hfun ⊢
    rw [iteratedDeriv_succ, hfun]
    have hQ0 : HasDerivAt (fun u : ℝ => Q.eval u) (Q.derivative.eval (η / s0)) (η / s0) :=
      Q.hasDerivAt (η / s0)
    have hc : HasDerivAt ((fun u : ℝ => Q.eval u) ∘ (fun x : ℝ => x / s0))
        (Q.derivative.eval (η / s0) * (1 / s0)) η :=
      HasDerivAt.comp η hQ0 ((hasDerivAt_id' η).div_const s0)
    have hQ' : HasDerivAt (fun y : ℝ => Q.eval (y / s0))
        (Q.derivative.eval (η / s0) * (1 / s0)) η := hc
    have hE : HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2) / (4 * s0 ^ 2)))
        (Real.exp (-(η ^ 2) / (4 * s0 ^ 2)) * (-(2 * η) / (4 * s0 ^ 2))) η := by
      have h := (((hasDerivAt_pow 2 η).neg).div_const (4 * s0 ^ 2)).exp
      refine h.congr_deriv ?_
      norm_num
    refine ((hQ'.const_mul ((Real.sqrt (4 * Real.pi * s0 ^ 2))⁻¹ * s0⁻¹ ^ j)).mul hE).deriv.trans ?_
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    ring

/-- `(√t)⁻¹ ^ n = t ^ (-(n/2))` for `t > 0`. -/
theorem lhInvSqrtPow (t : ℝ) (ht : 0 < t) (n : ℕ) :
    (Real.sqrt t)⁻¹ ^ n = t ^ (-((n : ℝ) / 2)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg ht.le, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
  congr 1
  ring

/-- `exp` beats polynomials: `(1+u²)^N e^{-u²/4} ≤ (4N)^N` for `N ≥ 1`. -/
theorem lhExpPow (N : ℕ) (hN : 1 ≤ N) (u : ℝ) :
    (1 + u ^ 2) ^ N * Real.exp (-(u ^ 2 / 4)) ≤ (4 * (N : ℝ)) ^ N := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  have hv : 0 ≤ u ^ 2 := sq_nonneg u
  have hw0 : 0 ≤ u ^ 2 / (4 * N) := by positivity
  have hexp : Real.exp (u ^ 2 / 4) = Real.exp (u ^ 2 / (4 * N)) ^ N := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  have h1 : 1 + u ^ 2 / (4 * N) ≤ Real.exp (u ^ 2 / (4 * N)) := by
    linarith [Real.add_one_le_exp (u ^ 2 / (4 * N))]
  have h2 : (1 + u ^ 2 / (4 * N)) ^ N ≤ Real.exp (u ^ 2 / (4 * N)) ^ N :=
    pow_le_pow_left₀ (by linarith) h1 N
  have h3 : 1 + u ^ 2 ≤ 4 * (N : ℝ) * (1 + u ^ 2 / (4 * N)) := by
    have e : 4 * (N : ℝ) * (1 + u ^ 2 / (4 * N)) = 4 * N + u ^ 2 := by
      field_simp
    rw [e]
    linarith
  have h4 : (1 + u ^ 2) ^ N ≤ (4 * (N : ℝ)) ^ N * (1 + u ^ 2 / (4 * N)) ^ N := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) h3 N
  have hpos : 0 < Real.exp (u ^ 2 / 4) := Real.exp_pos _
  rw [Real.exp_neg, mul_inv_le_iff₀ hpos, hexp]
  calc (1 + u ^ 2) ^ N ≤ (4 * (N : ℝ)) ^ N * (1 + u ^ 2 / (4 * N)) ^ N := h4
    _ ≤ (4 * (N : ℝ)) ^ N * Real.exp (u ^ 2 / (4 * N)) ^ N :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

/-- A polynomial times `(1+u²)^m e^{-u²/4}` is bounded on `ℝ`. -/
theorem lhPolyGauss (Q : Polynomial ℝ) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : ℝ, (1 + u ^ 2) ^ m * |Q.eval u| * Real.exp (-(u ^ 2 / 4)) ≤ B := by
  set A : ℝ := ∑ i ∈ Finset.range (Q.natDegree + 1), |Q.coeff i| with hA_def
  have hA0 : 0 ≤ A := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  refine ⟨A * (4 * ((m + Q.natDegree + 1 : ℕ) : ℝ)) ^ (m + Q.natDegree + 1),
    mul_nonneg hA0 (by positivity), fun u => ?_⟩
  have habs : |u| ≤ 1 + u ^ 2 := by
    nlinarith [sq_abs u, sq_nonneg (|u| - 1 / 2), abs_nonneg u]
  have hQb : |Q.eval u| ≤ A * (1 + u ^ 2) ^ Q.natDegree := by
    rw [Polynomial.eval_eq_sum_range, hA_def, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    have hiM : i ≤ Q.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [abs_mul, abs_pow]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    calc |u| ^ i ≤ (1 + u ^ 2) ^ i := pow_le_pow_left₀ (abs_nonneg u) habs i
      _ ≤ (1 + u ^ 2) ^ Q.natDegree := pow_le_pow_right₀ (by linarith [sq_nonneg u]) hiM
  have hN1 : 1 ≤ m + Q.natDegree + 1 := by omega
  have hE := lhExpPow (m + Q.natDegree + 1) hN1 u
  have hpowle : (1 + u ^ 2) ^ (m + Q.natDegree) ≤ (1 + u ^ 2) ^ (m + Q.natDegree + 1) :=
    pow_le_pow_right₀ (by linarith [sq_nonneg u]) (Nat.le_succ _)
  have hexp0 : 0 ≤ Real.exp (-(u ^ 2 / 4)) := (Real.exp_pos _).le
  calc (1 + u ^ 2) ^ m * |Q.eval u| * Real.exp (-(u ^ 2 / 4))
      ≤ (1 + u ^ 2) ^ m * (A * (1 + u ^ 2) ^ Q.natDegree) * Real.exp (-(u ^ 2 / 4)) := by
        apply mul_le_mul_of_nonneg_right _ hexp0
        exact mul_le_mul_of_nonneg_left hQb (by positivity)
    _ = A * ((1 + u ^ 2) ^ (m + Q.natDegree) * Real.exp (-(u ^ 2 / 4))) := by ring
    _ ≤ A * ((1 + u ^ 2) ^ (m + Q.natDegree + 1) * Real.exp (-(u ^ 2 / 4))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpowle hexp0) hA0
    _ ≤ A * (4 * ((m + Q.natDegree + 1 : ℕ) : ℝ)) ^ (m + Q.natDegree + 1) :=
        mul_le_mul_of_nonneg_left hE hA0

/-- **Weighted one-dimensional bound.** For `m, j`, a number `C ≥ 0` with
`(1+η²/s)^m |∂_η^j G_{νs}(η)| ≤ C (νs)^{-(j+1)/2}` for `0 < ν ≤ 1`, `s ≥ 1`, all `η`. -/
theorem lhBound1D (m j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ s : ℝ, 1 ≤ s →
    ∀ η : ℝ, (1 + η ^ 2 / s) ^ m * |iteratedDeriv j (heatKernel1 (ν * s)) η| ≤
      C * (ν * s) ^ (-(((j : ℝ) + 1) / 2)) := by
  obtain ⟨Q, hQ⟩ := lhPoly j
  obtain ⟨B, hB0, hB⟩ := lhPolyGauss Q m
  refine ⟨(Real.sqrt (4 * Real.pi))⁻¹ * B, mul_nonneg (by positivity) hB0, ?_⟩
  intro ν hν hν1 s hs η
  have hs0 : 0 < s := by linarith
  have ht : 0 < ν * s := mul_pos hν hs0
  have hνne : ν ≠ 0 := hν.ne'
  have hsne : s ≠ 0 := hs0.ne'
  have hu2 : (η / Real.sqrt (ν * s)) ^ 2 = η ^ 2 / (ν * s) := by
    rw [div_pow, Real.sq_sqrt ht.le]
  have hrel : η ^ 2 / s = ν * (η / Real.sqrt (ν * s)) ^ 2 := by
    rw [hu2]
    field_simp
  have hbase : 1 + η ^ 2 / s ≤ 1 + (η / Real.sqrt (ν * s)) ^ 2 := by
    rw [hrel]
    nlinarith [mul_nonneg (sub_nonneg.2 hν1) (sq_nonneg (η / Real.sqrt (ν * s)))]
  have hbase0 : 0 ≤ 1 + η ^ 2 / s := by
    have := div_nonneg (sq_nonneg η) hs0.le
    linarith
  have hpow : (1 + η ^ 2 / s) ^ m ≤ (1 + (η / Real.sqrt (ν * s)) ^ 2) ^ m :=
    pow_le_pow_left₀ hbase0 hbase m
  rw [hQ (ν * s) ht η]
  have hgauss : -(η ^ 2) / (4 * (ν * s)) = -((η / Real.sqrt (ν * s)) ^ 2 / 4) := by
    rw [hu2]
    ring
  rw [hgauss]
  have hc0 : 0 ≤ (Real.sqrt (4 * Real.pi * (ν * s)))⁻¹ * (Real.sqrt (ν * s))⁻¹ ^ j := by
    positivity
  have hE : 0 < Real.exp (-((η / Real.sqrt (ν * s)) ^ 2 / 4)) := Real.exp_pos _
  have habs : |(Real.sqrt (4 * Real.pi * (ν * s)))⁻¹ * (Real.sqrt (ν * s))⁻¹ ^ j *
      Q.eval (η / Real.sqrt (ν * s)) * Real.exp (-((η / Real.sqrt (ν * s)) ^ 2 / 4))| =
      (Real.sqrt (4 * Real.pi * (ν * s)))⁻¹ * (Real.sqrt (ν * s))⁻¹ ^ j *
        |Q.eval (η / Real.sqrt (ν * s))| * Real.exp (-((η / Real.sqrt (ν * s)) ^ 2 / 4)) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hc0, abs_of_pos hE]
  rw [habs]
  have h4pi : (0 : ℝ) ≤ 4 * Real.pi := by positivity
  have hc1 : (Real.sqrt (4 * Real.pi * (ν * s)))⁻¹ * (Real.sqrt (ν * s))⁻¹ ^ j =
      (Real.sqrt (4 * Real.pi))⁻¹ * (Real.sqrt (ν * s))⁻¹ ^ (j + 1) := by
    rw [Real.sqrt_mul h4pi]
    ring
  have hpowj : (Real.sqrt (ν * s))⁻¹ ^ (j + 1) = (ν * s) ^ (-(((j : ℝ) + 1) / 2)) := by
    have h := lhInvSqrtPow (ν * s) ht (j + 1)
    push_cast at h
    exact h
  rw [hc1, hpowj]
  have hBu := hB (η / Real.sqrt (ν * s))
  calc _ ≤ (1 + (η / Real.sqrt (ν * s)) ^ 2) ^ m *
        ((Real.sqrt (4 * Real.pi))⁻¹ * (ν * s) ^ (-(((j : ℝ) + 1) / 2)) *
          |Q.eval (η / Real.sqrt (ν * s))| *
          Real.exp (-((η / Real.sqrt (ν * s)) ^ 2 / 4))) :=
        mul_le_mul_of_nonneg_right hpow (by
          have hP : 0 ≤ (ν * s) ^ (-(((j : ℝ) + 1) / 2)) := Real.rpow_nonneg ht.le _
          have hA : 0 ≤ (Real.sqrt (4 * Real.pi))⁻¹ := by positivity
          have hE' : 0 ≤ Real.exp (-((η / Real.sqrt (ν * s)) ^ 2 / 4)) := hE.le
          exact mul_nonneg (mul_nonneg (mul_nonneg hA hP) (abs_nonneg _)) hE')
    _ = (Real.sqrt (4 * Real.pi))⁻¹ * (ν * s) ^ (-(((j : ℝ) + 1) / 2)) *
          ((1 + (η / Real.sqrt (ν * s)) ^ 2) ^ m * |Q.eval (η / Real.sqrt (ν * s))| *
            Real.exp (-((η / Real.sqrt (ν * s)) ^ 2 / 4))) := by ring
    _ ≤ (Real.sqrt (4 * Real.pi))⁻¹ * (ν * s) ^ (-(((j : ℝ) + 1) / 2)) * B :=
        mul_le_mul_of_nonneg_left hBu (mul_nonneg (by positivity)
          (Real.rpow_nonneg ht.le _))
    _ = (Real.sqrt (4 * Real.pi))⁻¹ * B * (ν * s) ^ (-(((j : ℝ) + 1) / 2)) := by ring

/-! ### Part 2: the profile function and its derivatives -/

/-- The profile `(q, (η, s)) ↦ ∂_η^j G_{νs}(η)`. -/
def lhP (ν : ℝ) (j : ℕ) : ProfilePoint → ℝ :=
  fun x => UnforcedLeray.B0191.heatDeriv ν j x.2.1 x.2.2

/-- The heat kernel `G_{νs}` of `B0191` is the one-variable `heatKernel1` at `t = νs`. -/
theorem lhHeatKernelEq (ν : ℝ) (j : ℕ) (η s : ℝ) :
    UnforcedLeray.B0191.heatDeriv ν j η s = iteratedDeriv j (heatKernel1 (ν * s)) η := by
  have hk : UnforcedLeray.B0191.heatKernel ν s = heatKernel1 (ν * s) := by
    funext y
    simp only [UnforcedLeray.B0191.heatKernel, heatKernel1, mul_assoc]
  unfold UnforcedLeray.B0191.heatDeriv
  rw [hk]

theorem lhP_eq (ν : ℝ) (j : ℕ) (x : ProfilePoint) :
    lhP ν j x = iteratedDeriv j (heatKernel1 (ν * x.2.2)) x.2.1 :=
  lhHeatKernelEq ν j x.2.1 x.2.2

theorem lhProfileEq (ν : ℝ) : heatProfile ν = lhP ν 0 := by
  funext x
  simp only [lhP, heatProfile, lhHeatKernelEq, iteratedDeriv_zero]

theorem lhMemNhds {y : ProfilePoint} (hy : 0 < y.2.2) : {z : ProfilePoint | 0 < z.2.2} ∈ 𝓝 y := by
  have hopen : IsOpen {z : ProfilePoint | 0 < z.2.2} := isOpen_lt continuous_const (by fun_prop)
  exact hopen.mem_nhds hy

/-- Near `y` with `s > 0`, `lhP ν j` agrees with the explicit self-similar form. -/
theorem lhEventuallyEq (ν : ℝ) (j : ℕ) {y : ProfilePoint} (hy : 0 < y.2.2) :
    lhP ν j =ᶠ[𝓝 y] fun z : ProfilePoint =>
      (Real.sqrt z.2.2)⁻¹ ^ (j + 1) *
        UnforcedLeray.B0191.profileDeriv ν j ((Real.sqrt z.2.2)⁻¹ * z.2.1) := by
  refine Filter.eventuallyEq_of_mem (lhMemNhds hy) ?_
  intro z hz
  have hz' : 0 < z.2.2 := hz
  exact UnforcedLeray.B0191.heatDeriv_selfSimilar ν j z.2.1 hz'

theorem lhDiff (ν : ℝ) (j : ℕ) {y : ProfilePoint} (hy : 0 < y.2.2) :
    DifferentiableAt ℝ (lhP ν j) y := by
  refine (Filter.EventuallyEq.differentiableAt_iff (lhEventuallyEq ν j hy)).2 ?_
  have h1 : DifferentiableAt ℝ (fun z : ProfilePoint => z.2.2) y := by fun_prop
  have h2 : DifferentiableAt ℝ (fun z : ProfilePoint => z.2.1) y := by fun_prop
  have hsq : DifferentiableAt ℝ (fun z : ProfilePoint => Real.sqrt z.2.2) y :=
    h1.sqrt hy.ne'
  have hinv : DifferentiableAt ℝ (fun z : ProfilePoint => (Real.sqrt z.2.2)⁻¹) y :=
    hsq.inv (Real.sqrt_pos.2 hy).ne'
  have hpow : DifferentiableAt ℝ (fun z : ProfilePoint => (Real.sqrt z.2.2)⁻¹ ^ (j + 1)) y :=
    hinv.pow (j + 1)
  have hin : DifferentiableAt ℝ (fun z : ProfilePoint => (Real.sqrt z.2.2)⁻¹ * z.2.1) y :=
    hinv.mul h2
  have hg : DifferentiableAt ℝ (UnforcedLeray.B0191.profileDeriv ν j)
      ((Real.sqrt y.2.2)⁻¹ * y.2.1) :=
    (UnforcedLeray.B0191.hasDerivAt_profileDeriv ν j _).differentiableAt
  have hpd : DifferentiableAt ℝ (fun z : ProfilePoint =>
      UnforcedLeray.B0191.profileDeriv ν j ((Real.sqrt z.2.2)⁻¹ * z.2.1)) y :=
    hg.comp y hin
  exact hpow.mul hpd

/-- Directional derivative along a line gives the Fréchet derivative. -/
theorem lhFderivLine {f : ProfilePoint → ℝ} {x v : ProfilePoint} {d : ℝ}
    (hf : DifferentiableAt ℝ f x) (h : HasDerivAt (fun t : ℝ => f (x + t • v)) d 0) :
    fderiv ℝ f x v = d := by
  have hg : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).smul_const v).const_add x
  have hc := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hf.hasFDerivAt hg (by simp)
  exact hc.unique h

theorem lhPartialEta (ν : ℝ) (j : ℕ) {y : ProfilePoint} (hy : 0 < y.2.2) :
    partialEta (lhP ν j) y = lhP ν (j + 1) y := by
  unfold partialEta
  apply lhFderivLine (lhDiff ν j hy)
  have hline : (fun t : ℝ => lhP ν j (y + t • eηDir)) =
      fun t : ℝ => UnforcedLeray.B0191.heatDeriv ν j (y.2.1 + t) y.2.2 := by
    funext t
    simp [lhP, eηDir]
  rw [hline]
  have h0 := UnforcedLeray.B0191.hasDerivAt_heatDeriv_eta ν j y.2.1 y.2.2
  have h3 : HasDerivAt (fun η' : ℝ => UnforcedLeray.B0191.heatDeriv ν j η' y.2.2)
      (UnforcedLeray.B0191.heatDeriv ν (j + 1) y.2.1 y.2.2) (y.2.1 + 0) := by
    rw [add_zero]
    exact h0
  exact HasDerivAt.comp_const_add y.2.1 0 h3

theorem lhPartialAge (ν : ℝ) (j : ℕ) {y : ProfilePoint} (hy : 0 < y.2.2) :
    partialAge (lhP ν j) y =
      -(((j : ℝ) + 1) * lhP ν j y + y.2.1 * lhP ν (j + 1) y) / (2 * y.2.2) := by
  unfold partialAge
  apply lhFderivLine (lhDiff ν j hy)
  have hline : (fun t : ℝ => lhP ν j (y + t • esDir)) =
      fun t : ℝ => UnforcedLeray.B0191.heatDeriv ν j y.2.1 (y.2.2 + t) := by
    funext t
    simp [lhP, esDir]
  rw [hline]
  have h0 := UnforcedLeray.B0191.hasDerivAt_heatDeriv_age ν j y.2.1 hy
  have h3 : HasDerivAt (fun s' : ℝ => UnforcedLeray.B0191.heatDeriv ν j y.2.1 s')
      (-(((j : ℝ) + 1) * UnforcedLeray.B0191.heatDeriv ν j y.2.1 y.2.2 +
        y.2.1 * UnforcedLeray.B0191.heatDeriv ν (j + 1) y.2.1 y.2.2) / (2 * y.2.2))
      (y.2.2 + 0) := by
    rw [add_zero]
    exact h0
  exact HasDerivAt.comp_const_add y.2.2 0 h3

theorem lhPartialEtaCongr {f g : ProfilePoint → ℝ} {y : ProfilePoint}
    (h : f =ᶠ[𝓝 y] g) : partialEta f y = partialEta g y := by
  unfold partialEta
  rw [h.fderiv_eq]

theorem lhPartialAgeCongr {f g : ProfilePoint → ℝ} {y : ProfilePoint}
    (h : f =ᶠ[𝓝 y] g) : partialAge f y = partialAge g y := by
  unfold partialAge
  rw [h.fderiv_eq]

/-- On `s > 0` the iterated `η`-derivative of the profile is `lhP ν j`. -/
theorem lhIter (ν : ℝ) (j : ℕ) : ∀ y : ProfilePoint, 0 < y.2.2 →
    (partialEta^[j] (heatProfile ν)) y = lhP ν j y := by
  induction j with
  | zero =>
    intro y _
    rw [Function.iterate_zero_apply, lhProfileEq]
  | succ j ih =>
    intro y hy
    rw [Function.iterate_succ_apply']
    have hEq : partialEta^[j] (heatProfile ν) =ᶠ[𝓝 y] lhP ν j :=
      Filter.eventuallyEq_of_mem (lhMemNhds hy) (by
        intro z hz
        have hz' : 0 < z.2.2 := hz
        exact ih z hz')
    rw [lhPartialEtaCongr hEq]
    exact lhPartialEta ν j hy

/-! ### Part 3: the three clauses -/

/-- **Heat-kernel profile calculus** (`LateHeatProfile`, source lines 1255-1257, 1268-1272). -/
theorem lateHeatProfile : LateHeatProfile := by
  refine ⟨?_, ?_, ?_⟩
  · intro ν _ j x hx
    have hEq : partialEta^[j] (heatProfile ν) =ᶠ[𝓝 x] lhP ν j :=
      Filter.eventuallyEq_of_mem (lhMemNhds hx) (by
        intro z hz
        have hz' : 0 < z.2.2 := hz
        exact lhIter ν j z hz')
    have hx0 : x.2.2 ≠ 0 := hx.ne'
    unfold ageOperator
    rw [lhPartialEtaCongr hEq, lhPartialAgeCongr hEq, lhPartialEta ν j hx,
      lhPartialAge ν j hx, lhIter ν j x hx]
    field_simp
    ring
  · intro m j
    obtain ⟨C, hC0, hC⟩ := lhBound1D m j
    refine ⟨C, hC0, ?_⟩
    intro ν hν hν1 x hx
    have hx0 : 0 < x.2.2 := lt_of_lt_of_le one_pos hx
    rw [lhIter ν j x hx0, lhP_eq]
    exact hC ν hν hν1 x.2.2 hx x.2.1
  · intro ν _ j x hx
    rw [lhIter ν j x hx, lhP_eq]

end UnforcedLeray.Short.PartIIa
