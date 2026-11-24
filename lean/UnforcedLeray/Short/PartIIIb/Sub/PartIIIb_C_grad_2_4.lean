import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.PsipADiff.XPart

/-!
# `PartIII-b:C/grad/2/4`: the mixed derivative `∂_x ∂_s ψ^p_A` exists at `s > 0`

Source `the November 2 reference manuscript` lines 4973-4980 (`ψ^p_A = Σ_j Φ(x_j)`,
sums and their derivatives converge by Gaussian decay), 4741-4745 (`A` is `C^6`), 5081-5084.

Reduction: by `PAMXSDerivTsum`, `∂_s ψ^p_A(s, y) = Σ_n sV(x_n(y))` (the lattice sum of the explicit
`s`-derivative `sV` of `Φ_{A^y(s)}`); each term `sV` is smooth in `y` with a Gaussian-weighted bound
on its `y`-derivative (`PAMXSVBound`), which is summable over the lattice on a unit ball
(`PAMXBallMajor`); hence the sum is differentiable in `y` (`hasFDerivAt_tsum_of_isPreconnected`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Sub 1 (source 4973-4980, same argument as `psipASDiff`): the `s`-derivative of `ψ^p_A` is the
lattice sum of the explicit derivative `sV` of the profile `Φ_{A^y(s)}`. -/
def PAMXSDerivTsum (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν : ℝ), 0 < ν → ∀ (A : ℝ → Mat3), IsAffElem as A →
    ∀ s : ℝ, 0 < s → ∀ y : ℝ × ℝ,
      deriv (fun s' => psipA ν χf A s' y) s =
        ∑' n : ℤ, sV ν (xj ν n y) (Ay ν χf A s) (deriv (Ay ν χf A) s) s

/-- Sub 2 (source 4973-4980; `sV` is a polynomial in `y` times a Gaussian): `y ↦ sV ν y Mt D t`
is differentiable, and its `y`-derivative has a Gaussian-weighted polynomial bound, with constant
depending only on `ν` and the entry bounds `K1, K2` of `Mt, D`, uniformly in `t` with
`1 ≤ ageA ν t`. -/
def PAMXSVBound : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (K1 K2 : ℝ), 0 ≤ K1 → 0 ≤ K2 → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (Mt D : Mat3) (t : ℝ), 1 ≤ ageA ν t → (∀ i j, |Mt i j| ≤ K1) → (∀ i j, |D i j| ≤ K2) →
      ∀ y : ℝ × ℝ, DifferentiableAt ℝ (fun w => sV ν w Mt D t) y ∧
        ∀ v : ℝ × ℝ, ‖fderiv ℝ (fun w => sV ν w Mt D t) y v‖ ≤
          C * ‖v‖ * ((1 + ‖y‖) ^ 5 * Real.exp (-(sq2 y) / (4 * ageA ν t)))

/-- Sub 3 (generalises `ball_geom` of `XPart.lean` from exponent 3 to 5): a summable lattice
majorant of `(1+|x_j(z)|)^5 e^{-|x_j(z)|²/(4a)}` on the unit ball around `x`. -/
def PAMXBallMajor : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (s : ℝ), 1 ≤ ageA ν s → ∀ x : ℝ × ℝ, ∀ C : ℝ, 0 ≤ C →
    ∃ u : ℤ → ℝ, Summable u ∧ ∀ (j : ℤ) (z : ℝ × ℝ), ‖z - x‖ < 1 →
      C * ((1 + ‖xj ν j z‖) ^ 5 * Real.exp (-(sq2 (xj ν j z)) / (4 * ageA ν s))) ≤ u j

theorem xj_hasFDerivAt (ν : ℝ) (n : ℤ) (z : ℝ × ℝ) :
    HasFDerivAt (fun w : ℝ × ℝ => xj ν n w) (ContinuousLinearMap.id ℝ (ℝ × ℝ)) z := by
  have e : (fun w : ℝ × ℝ => xj ν n w) = fun w => w - ((n : ℝ) * cOf ν, 0) := by
    funext w; ext <;> simp [xj]
  rw [e]
  exact (hasFDerivAt_id z).sub_const _

theorem psipAMixedX_of (as : ℝ) (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf)
    (h1 : PAMXSDerivTsum as χf) (h2 : PAMXSVBound) (h3 : PAMXBallMajor) :
    PsipAMixedX as χf := by
  intro ν hν A hA s hs x
  have ha1 : 1 ≤ ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  have hs0 : 0 < s := hs
  have hfun : (fun y => deriv (fun s' => psipA ν χf A s' y) s) =
      fun y => ∑' n : ℤ, sV ν (xj ν n y) (Ay ν χf A s) (deriv (Ay ν χf A) s) s :=
    funext fun y => h1 hχ ν hν A hA s hs y
  rw [hfun]
  set Mt := Ay ν χf A s with hMt
  set D := deriv (Ay ν χf A) s with hD
  have hMb : ∀ i j, |Mt i j| ≤ ‖Mt‖ := fun i j => sp_entry_le _ i j
  have hDb : ∀ i j, |D i j| ≤ ‖D‖ := fun i j => sp_entry_le _ i j
  obtain ⟨C, hC0, hC⟩ := h2 ν hν ‖Mt‖ ‖D‖ (norm_nonneg _) (norm_nonneg _)
  obtain ⟨u, hu, hub⟩ := h3 ν hν s ha1 x C hC0
  have hc0 : 0 ≤ 10 * ν * ‖Mt‖ + 8 * ‖D‖ := by positivity
  obtain ⟨u', hu', hub'⟩ := h3 ν hν s ha1 x _ hc0
  have hu0 : ∀ n, 0 ≤ u n := fun n =>
    le_trans (by positivity) (hub n x (by simp))
  have hF : ∀ (n : ℤ) (z : ℝ × ℝ), z ∈ Metric.ball x 1 →
      HasFDerivAt (fun w => sV ν (xj ν n w) Mt D s)
        ((fderiv ℝ (fun w => sV ν w Mt D s) (xj ν n z)).comp
          (ContinuousLinearMap.id ℝ (ℝ × ℝ))) z := by
    intro n z _
    have hd := (hC Mt D s ha1 hMb hDb (xj ν n z)).1
    exact hd.hasFDerivAt.comp z (xj_hasFDerivAt ν n z)
  have hbound : ∀ (n : ℤ) (z : ℝ × ℝ), z ∈ Metric.ball x 1 →
      ‖(fderiv ℝ (fun w => sV ν w Mt D s) (xj ν n z)).comp
          (ContinuousLinearMap.id ℝ (ℝ × ℝ))‖ ≤ u n := by
    intro n z hz
    apply ContinuousLinearMap.opNorm_le_bound _ (hu0 n)
    intro v
    have h1' := (hC Mt D s ha1 hMb hDb (xj ν n z)).2 v
    have h2' := hub n z (mem_ball_iff_norm.mp hz)
    have hv := norm_nonneg v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
    calc ‖(fderiv ℝ (fun w => sV ν w Mt D s) (xj ν n z)) v‖
        ≤ C * ‖v‖ * ((1 + ‖xj ν n z‖) ^ 5 *
            Real.exp (-(sq2 (xj ν n z)) / (4 * ageA ν s))) := h1'
      _ = ‖v‖ * (C * ((1 + ‖xj ν n z‖) ^ 5 *
            Real.exp (-(sq2 (xj ν n z)) / (4 * ageA ν s)))) := by ring
      _ ≤ ‖v‖ * u n := mul_le_mul_of_nonneg_left h2' hv
      _ = u n * ‖v‖ := by ring
  have hf0 : Summable (fun n : ℤ => sV ν (xj ν n x) Mt D s) := by
    refine Summable.of_norm_bounded hu' (fun n => ?_)
    rw [Real.norm_eq_abs]
    have b1 := sV_bound ν hν (xj ν n x) ‖Mt‖ ‖D‖ Mt D s hs0 hMb hDb
    have b2 := hub' n x (by simp)
    have hR1 : (1:ℝ) ≤ 1 + ‖xj ν n x‖ := by linarith [norm_nonneg (xj ν n x)]
    have hE : 0 ≤ Real.exp (-(sq2 (xj ν n x)) / (4 * ageA ν s)) := (Real.exp_pos _).le
    have hp : (1 + ‖xj ν n x‖) ^ 4 ≤ (1 + ‖xj ν n x‖) ^ 5 :=
      pow_le_pow_right₀ hR1 (by norm_num)
    refine b1.trans (le_trans ?_ b2)
    have := mul_le_mul_of_nonneg_right hp hE
    calc (10 * ν * ‖Mt‖ + 8 * ‖D‖) * (1 + ‖xj ν n x‖) ^ 4 *
          Real.exp (-(sq2 (xj ν n x)) / (4 * ageA ν s))
        = (10 * ν * ‖Mt‖ + 8 * ‖D‖) * ((1 + ‖xj ν n x‖) ^ 4 *
          Real.exp (-(sq2 (xj ν n x)) / (4 * ageA ν s))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this hc0
  have key := hasFDerivAt_tsum_of_isPreconnected
    (f := fun n (w : ℝ × ℝ) => sV ν (xj ν n w) Mt D s)
    (f' := fun n z => (fderiv ℝ (fun w => sV ν w Mt D s) (xj ν n z)).comp
          (ContinuousLinearMap.id ℝ (ℝ × ℝ)))
    (u := u) hu Metric.isOpen_ball (convex_ball x 1).isPreconnected hF hbound
    (Metric.mem_ball_self one_pos) hf0 (Metric.mem_ball_self one_pos)
  exact key.differentiableAt

end UnforcedLeray.Short.PartIIIb.Concrete
