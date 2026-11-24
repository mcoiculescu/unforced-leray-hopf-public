import UnforcedLeray.Short.PartI.Sub.T02_4

/-!


Source of record: `the November 2 reference manuscript`, lines 276-288 (the barrier
computation for the vorticity comparison). The target is `SechSupersolution` of
`Short/PartI/Sub/T02_4.lean`.

Route. Write `B = A e^{Ks} sech(aη)`, `Φ = ε e^{Ks} cosh(aη)` and `F = B + Φ` (the helper `ssF`).
Then `∂_s F = K F`, `∂_q F = 0`, `∂_η F = a (sinh(aη)/cosh(aη)) (Φ - B)`, and
`∂_η² F = a² B (1 - 2 sech²) + a² Φ`. The operator is therefore
`K F + b_η ∂_η F - ν ∂_η² F`. Since `|b_η| ≤ β`, `|sinh/cosh| ≤ 1`, `B, Φ ≥ 0`, `1 - 2 sech² ≤ 1`
and `ν ≥ 0`, this is at least `(K - β a - ν a²) F`.

Helper names carry the prefix `ss`. The derivatives are computed with `HasDerivAt` in the forms
`sech = (cosh)⁻¹` and `(cosh)⁻¹ * (cosh)⁻¹`, and the identities `cosh · sech = 1`,
`sinh² = cosh² - 1` close the second-derivative algebra by `linear_combination`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

/-- The barrier sum `B + Φ` as a function of `(s, w)`. -/
def ssF (A K a ε : ℝ) (s : ℝ) (w : Plane) : ℝ :=
  sechBarrier A K a s w + coshBarrier ε K a s w

/-- The map `η ↦ a η` has derivative `a`. -/
theorem ss_lin (a y : ℝ) : HasDerivAt (fun η : ℝ => a * η) a y :=
  ((hasDerivAt_id (x := y)).const_mul a).congr_deriv (mul_one a)

/-- `η ↦ cosh(aη)` has derivative `sinh(ay) a`. -/
theorem ss_cosh_lin (a y : ℝ) :
    HasDerivAt (fun η : ℝ => Real.cosh (a * η)) (Real.sinh (a * y) * a) y :=
  (ss_lin a y).cosh

/-- `η ↦ sinh(aη)` has derivative `cosh(ay) a`. -/
theorem ss_sinh_lin (a y : ℝ) :
    HasDerivAt (fun η : ℝ => Real.sinh (a * η)) (Real.cosh (a * y) * a) y :=
  (ss_lin a y).sinh

/-- First `η`-derivative of the slice `P sech(aη) + Q cosh(aη)`. -/
theorem ss_slice_d1 (P Q a y : ℝ) :
    HasDerivAt (fun η : ℝ => P * (Real.cosh (a * η))⁻¹ + Q * Real.cosh (a * η))
      (P * (-(Real.sinh (a * y) * a) * ((Real.cosh (a * y))⁻¹ * (Real.cosh (a * y))⁻¹))
        + Q * (Real.sinh (a * y) * a)) y := by
  have hc := ss_cosh_lin a y
  have hw : HasDerivAt (fun η : ℝ => (Real.cosh (a * η))⁻¹)
      (-(Real.sinh (a * y) * a) / (Real.cosh (a * y)) ^ 2) y :=
    hc.inv (Real.cosh_pos _).ne'
  exact ((hw.const_mul P).add (hc.const_mul Q)).congr_deriv (by ring)

/-- Second `η`-derivative of the slice `P sech(aη) + Q cosh(aη)`. -/
theorem ss_slice_d2 (P Q a y : ℝ)
    (hw1 : Real.cosh (a * y) * (Real.cosh (a * y))⁻¹ = 1)
    (ht : Real.sinh (a * y) ^ 2 = Real.cosh (a * y) ^ 2 - 1) :
    HasDerivAt
      (fun η : ℝ => P * (-(Real.sinh (a * η) * a) * ((Real.cosh (a * η))⁻¹ * (Real.cosh (a * η))⁻¹))
        + Q * (Real.sinh (a * η) * a))
      (P * (a ^ 2 * (Real.cosh (a * y))⁻¹ * (1 - 2 * ((Real.cosh (a * y))⁻¹ * (Real.cosh (a * y))⁻¹)))
        + Q * (Real.cosh (a * y) * a * a)) y := by
  have hc := ss_cosh_lin a y
  have hs := ss_sinh_lin a y
  have hw : HasDerivAt (fun η : ℝ => (Real.cosh (a * η))⁻¹)
      (-(Real.sinh (a * y) * a) / (Real.cosh (a * y)) ^ 2) y :=
    hc.inv (Real.cosh_pos _).ne'
  have hnum : HasDerivAt (fun η : ℝ => -(Real.sinh (a * η) * a)) (-(Real.cosh (a * y) * a * a)) y :=
    (hs.mul_const a).neg
  have hf := (hnum.mul (hw.mul hw)).const_mul P
  have hg := (hs.mul_const a).const_mul Q
  exact (hf.add hg).congr_deriv (by
    simp only [Pi.mul_apply]
    linear_combination
      (P * a ^ 2 * (Real.cosh (a * y))⁻¹ * (2 * (Real.cosh (a * y) * (Real.cosh (a * y))⁻¹) + 1)) * hw1
        + (P * (2 * a ^ 2 * ((Real.cosh (a * y))⁻¹) ^ 3)) * ht)

/-- `|x i| ≤ ‖x‖` for a vector of the plane. -/
theorem ss_abs_apply_le (x : Vec) (i : Fin 2) : |x i| ≤ ‖x‖ := by
  have h := PiLp.norm_apply_le x i
  rwa [Real.norm_eq_abs] at h

/-- The real inequality behind the barrier: with `X = P w + Q u`, `w = u⁻¹`, `t² = u² - 1`,
`|b₁| ≤ β` and `ν ≥ 0`, the transport term is at least `-β a X` and the diffusion term at most
`ν a² X`. -/
theorem ss_alg (β ν a K P Q u t w b0 b1 : ℝ) (hν : 0 ≤ ν) (ha : 0 < a) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hu : 0 < u) (hw1 : u * w = 1) (ht : t ^ 2 = u ^ 2 - 1) (hb1 : |b1| ≤ β) :
    (K - β * a - ν * a ^ 2) * (P * w + Q * u) ≤
      K * (P * w + Q * u) + (b0 * 0 + b1 * (P * (-(t * a) * (w * w)) + Q * (t * a))) -
        ν * (0 + (P * (a ^ 2 * w * (1 - 2 * (w * w))) + Q * (u * a * a))) := by
  have hw0 : 0 < w := by nlinarith
  have hτ : |t| ≤ u := by nlinarith [sq_abs t, abs_nonneg t]
  have htw : |t * w| ≤ 1 := by
    rw [abs_mul, abs_of_pos hw0]
    have h := mul_le_mul_of_nonneg_right hτ hw0.le
    linarith
  have hpE : P * (-(t * a) * (w * w)) + Q * (t * a) = a * (t * w) * (Q * u - P * w) := by
    linear_combination (-(Q * t * a)) * hw1
  have hX0 : 0 ≤ Q * u := mul_nonneg hQ hu.le
  have hX1 : 0 ≤ P * w := mul_nonneg hP hw0.le
  have hdiff : |Q * u - P * w| ≤ Q * u + P * w := abs_le.mpr ⟨by linarith, by linarith⟩
  have hpEabs : |P * (-(t * a) * (w * w)) + Q * (t * a)| ≤ a * (P * w + Q * u) := by
    rw [hpE, abs_mul, abs_mul, abs_of_pos ha]
    have h1 : |t * w| * |Q * u - P * w| ≤ 1 * (Q * u + P * w) :=
      mul_le_mul htw hdiff (abs_nonneg _) zero_le_one
    have h2 := mul_le_mul_of_nonneg_left h1 ha.le
    linarith
  have hb0 : 0 ≤ β := le_trans (abs_nonneg b1) hb1
  have hlow : -(β * (a * (P * w + Q * u))) ≤ b1 * (P * (-(t * a) * (w * w)) + Q * (t * a)) := by
    have h1 : |b1 * (P * (-(t * a) * (w * w)) + Q * (t * a))| ≤ β * (a * (P * w + Q * u)) := by
      rw [abs_mul]
      exact mul_le_mul hb1 hpEabs (abs_nonneg _) hb0
    exact (abs_le.mp h1).1
  have hpEE : P * (a ^ 2 * w * (1 - 2 * (w * w))) + Q * (u * a * a) ≤ a ^ 2 * (P * w + Q * u) := by
    have h3 : 0 ≤ P * a ^ 2 * (w * w * w) :=
      mul_nonneg (mul_nonneg hP (sq_nonneg a)) (mul_nonneg (mul_nonneg hw0.le hw0.le) hw0.le)
    nlinarith
  have h4 := mul_le_mul_of_nonneg_left hpEE hν
  linarith

/-- **The `sech` / `cosh` barriers are supersolutions.** -/
theorem sechSupersolution : SechSupersolution := by
  unfold SechSupersolution
  intro ν β A ε K a b s z hν ha hA hε hb
  have hb1 : |b s z 1| ≤ β := le_trans (ss_abs_apply_le (b s z) 1) hb
  obtain ⟨q, η⟩ := z
  have hu : 0 < Real.cosh (a * η) := Real.cosh_pos _
  have hw1 : Real.cosh (a * η) * (Real.cosh (a * η))⁻¹ = 1 := mul_inv_cancel₀ hu.ne'
  have ht : Real.sinh (a * η) ^ 2 = Real.cosh (a * η) ^ 2 - 1 := by
    have h := Real.cosh_sq (x := a * η)
    linarith
  have hP : 0 ≤ A * Real.exp (K * s) := mul_nonneg hA (Real.exp_pos _).le
  have hQ : 0 ≤ ε * Real.exp (K * s) := mul_nonneg hε (Real.exp_pos _).le
  have hX : ssF A K a ε s (q, η)
      = A * Real.exp (K * s) * (Real.cosh (a * η))⁻¹
        + ε * Real.exp (K * s) * Real.cosh (a * η) := rfl
  -- time derivative
  have hexp : HasDerivAt (fun t' : ℝ => Real.exp (K * t')) (Real.exp (K * s) * K) s :=
    (ss_lin K s).exp
  have hd : HasDerivAt (fun t' : ℝ => ssF A K a ε t' (q, η))
      (A * (Real.exp (K * s) * K) * (Real.cosh (a * η))⁻¹
        + ε * (Real.exp (K * s) * K) * Real.cosh (a * η)) s :=
    ((hexp.const_mul A).mul_const (Real.cosh (a * η))⁻¹).add
      ((hexp.const_mul ε).mul_const (Real.cosh (a * η)))
  have hdt : deriv (fun t' : ℝ => ssF A K a ε t' (q, η)) s
      = K * (A * Real.exp (K * s) * (Real.cosh (a * η))⁻¹
        + ε * Real.exp (K * s) * Real.cosh (a * η)) := by
    rw [hd.deriv]
    ring
  -- q-derivatives vanish
  have hQ0 : ∀ w : Plane, Cyl.partialQ (ssF A K a ε s) w = 0 := by
    intro w
    show deriv (fun q' : ℝ => ssF A K a ε s (q', w.2)) w.1 = 0
    rw [show (fun q' : ℝ => ssF A K a ε s (q', w.2)) = fun _ => ssF A K a ε s (0, w.2) from rfl,
      deriv_const]
  have hQQ : ∀ η' : ℝ, Cyl.partialQ (Cyl.partialQ (ssF A K a ε s)) (q, η') = 0 := by
    intro η'
    show deriv (fun q' : ℝ => Cyl.partialQ (ssF A K a ε s) (q', η')) q = 0
    rw [show (fun q' : ℝ => Cyl.partialQ (ssF A K a ε s) (q', η')) = fun _ => (0 : ℝ) from
      funext (fun q' => hQ0 (q', η')), deriv_const]
  -- first η-derivative
  have hE1 : ∀ η' : ℝ, Cyl.partialEta (ssF A K a ε s) (q, η') =
      A * Real.exp (K * s)
          * (-(Real.sinh (a * η') * a) * ((Real.cosh (a * η'))⁻¹ * (Real.cosh (a * η'))⁻¹))
        + ε * Real.exp (K * s) * (Real.sinh (a * η') * a) := by
    intro η'
    show deriv (fun η'' : ℝ => ssF A K a ε s (q, η'')) η' = _
    exact (ss_slice_d1 (A * Real.exp (K * s)) (ε * Real.exp (K * s)) a η').deriv
  -- second η-derivative
  have hEE : Cyl.partialEta (Cyl.partialEta (ssF A K a ε s)) (q, η) =
      A * Real.exp (K * s)
          * (a ^ 2 * (Real.cosh (a * η))⁻¹ * (1 - 2 * ((Real.cosh (a * η))⁻¹ * (Real.cosh (a * η))⁻¹)))
        + ε * Real.exp (K * s) * (Real.cosh (a * η) * a * a) := by
    show deriv (fun η'' : ℝ => Cyl.partialEta (ssF A K a ε s) (q, η'')) η = _
    rw [funext hE1]
    exact (ss_slice_d2 (A * Real.exp (K * s)) (ε * Real.exp (K * s)) a η hw1 ht).deriv
  -- assemble the operator
  show (K - β * a - ν * a ^ 2) * ssF A K a ε s (q, η)
    ≤ vorticityOp ν b (ssF A K a ε) s (q, η)
  unfold vorticityOp
  unfold Train.lapS
  rw [hdt, hQ0 (q, η), hQQ η, hE1 η, hEE, hX]
  have key := ss_alg β ν a K (A * Real.exp (K * s)) (ε * Real.exp (K * s)) (Real.cosh (a * η))
    (Real.sinh (a * η)) (Real.cosh (a * η))⁻¹ (b s (q, η) 0) (b s (q, η) 1)
    hν ha hP hQ hu hw1 ht hb1
  linarith [key]

end UnforcedLeray.Short.PartI
