import UnforcedLeray.Units.B0147.Profile

/-!
# B0147 helper: Gaussian lattice sums uniform in the period

Blueprint unit **B0147** (`eq:st18-t00145`, `paper/main.tex` lines 2217–2234), helper file;
infrastructure `INF27`/`INF29` ("Gaussian lattice sum bounds uniform in `c ≥ 2`").

In rescaled variables the period is `L = c/√a`, and the hypothesis `a ≤ c²` of tex line 2217
is `L ≥ 1`. For `β > 0` and `L ≥ 1`:

* on one cell `0 ≤ t ≤ L`, `∑ₙ e^{-β(t-nL)²} ≤ e^{-βt²} + e^{-β(t-L)²} + e^{-βL²/2} Θ(β/8)`
  (`lattice1D_cell`), where `Θ(γ) = ∑ₙ e^{-γn²}`;
* everywhere, `∑ₙ e^{-β(t-nL)²} ≤ 2 + Θ(β/8)` (`lattice1D_sup`).

These give the pointwise bounds for lattice sums of Gaussian-bounded profiles
(`latticeSum_abs_le`, `latticeSum_sup`, `latticeSum_cell`), their continuity, and the
termwise derivatives of lattice sums of `GP` profiles along any derivative word
(`GP.derivWord_lattice`).
-/

set_option autoImplicit false

noncomputable section

open Filter
open scoped Topology

namespace UnforcedLeray.B0147

open UnforcedLeray.GaussianVortex
open UnforcedLeray.B0146 (XDecay latticeSum shift radiusSq_nonneg summable_exp_shift
  exp_shift_local)
open UnforcedLeray.B0151 (derivWord)

/-- `Θ(γ) = ∑ₙ e^{-γ n²}`. -/
def theta (γ : ℝ) : ℝ := ∑' n : ℤ, Real.exp (-(γ * (n : ℝ) ^ 2))

theorem summable_theta {γ : ℝ} (hγ : 0 < γ) :
    Summable (fun n : ℤ => Real.exp (-(γ * (n : ℝ) ^ 2))) := by
  refine (summable_exp_shift hγ one_ne_zero 0).congr fun n => ?_
  congr 2
  ring

theorem theta_nonneg (γ : ℝ) : 0 ≤ theta γ := tsum_nonneg fun _ => (Real.exp_pos _).le

/-- The quadratic lower bound behind the cell estimate: away from the two nearest lattice
points the distance is at least `L/√2` plus a summable margin. -/
theorem far_sq_ge {L t : ℝ} (hL : 1 ≤ L) (ht0 : 0 ≤ t) (htL : t ≤ L) {n : ℤ} (h0 : n ≠ 0)
    (h1 : n ≠ 1) : L ^ 2 / 2 + (n : ℝ) ^ 2 / 8 ≤ (t - n * L) ^ 2 := by
  have hL0 : 0 ≤ L := by linarith
  rcases lt_or_gt_of_ne h0 with hn | hn
  · have hn' : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
    have hA : -(n : ℝ) * L ≤ t - n * L := by linarith
    have hA0 : 0 ≤ -(n : ℝ) * L := by nlinarith
    have hsq : (-(n : ℝ) * L) ^ 2 ≤ (t - n * L) ^ 2 := pow_le_pow_left₀ hA0 hA 2
    have hL2 : 1 ≤ L ^ 2 := by nlinarith
    have hn2 : 1 ≤ (n : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hL2 (sq_nonneg (n : ℝ))]
  · have hn' : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
    have hA : ((n : ℝ) - 1) * L ≤ n * L - t := by nlinarith
    have hA0 : 0 ≤ ((n : ℝ) - 1) * L := by nlinarith
    have hsq : (((n : ℝ) - 1) * L) ^ 2 ≤ (n * L - t) ^ 2 := pow_le_pow_left₀ hA0 hA 2
    have hL2 : 1 ≤ L ^ 2 := by nlinarith
    have hq : 1 / 2 + (n : ℝ) ^ 2 / 8 ≤ ((n : ℝ) - 1) ^ 2 := by nlinarith
    have e1 : (((n : ℝ) - 1) * L) ^ 2 = ((n : ℝ) - 1) ^ 2 * L ^ 2 := by ring
    have e2 : (n * L - t) ^ 2 = (t - n * L) ^ 2 := by ring
    nlinarith [mul_le_mul_of_nonneg_right hq (by positivity : (0 : ℝ) ≤ L ^ 2),
      mul_le_mul_of_nonneg_left hL2 (sq_nonneg (n : ℝ))]

/-- Termwise domination on one cell. -/
theorem exp_term_le {β L t : ℝ} (hβ : 0 < β) (hL : 1 ≤ L) (ht0 : 0 ≤ t) (htL : t ≤ L)
    (n : ℤ) :
    Real.exp (-(β * (t - n * L) ^ 2)) ≤
      ((if n = 0 then Real.exp (-(β * t ^ 2)) else 0) +
        (if n = 1 then Real.exp (-(β * (t - L) ^ 2)) else 0)) +
        Real.exp (-(β * L ^ 2 / 2)) * Real.exp (-(β / 8 * (n : ℝ) ^ 2)) := by
  have hE := (mul_pos (Real.exp_pos (-(β * L ^ 2 / 2)))
    (Real.exp_pos (-(β / 8 * (n : ℝ) ^ 2)))).le
  by_cases h0 : n = 0
  · subst h0
    simp only [if_true, Int.cast_zero, zero_mul, sub_zero, (by decide : (0 : ℤ) ≠ 1),
      if_false, add_zero]
    linarith
  by_cases h1 : n = 1
  · subst h1
    simp only [if_true, Int.cast_one, one_mul, (by decide : (1 : ℤ) ≠ 0), if_false, zero_add]
    linarith
  simp only [h0, h1, if_false, add_zero, zero_add]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have key := far_sq_ge hL ht0 htL h0 h1
  nlinarith

/-- **Cell bound for the one-dimensional Gaussian lattice sum**, uniform for `L ≥ 1`. -/
theorem lattice1D_cell {β L t : ℝ} (hβ : 0 < β) (hL : 1 ≤ L) (ht0 : 0 ≤ t) (htL : t ≤ L) :
    ∑' n : ℤ, Real.exp (-(β * (t - n * L) ^ 2)) ≤
      Real.exp (-(β * t ^ 2)) + Real.exp (-(β * (t - L) ^ 2)) +
        Real.exp (-(β * L ^ 2 / 2)) * theta (β / 8) := by
  have hL0 : L ≠ 0 := by positivity
  have h1 := (summable_exp_shift hβ hL0 t).hasSum
  have h2 := ((hasSum_ite_eq (0 : ℤ) (Real.exp (-(β * t ^ 2)))).add
    (hasSum_ite_eq (1 : ℤ) (Real.exp (-(β * (t - L) ^ 2))))).add
    ((summable_theta (by positivity : 0 < β / 8)).hasSum.mul_left
      (Real.exp (-(β * L ^ 2 / 2))))
  exact hasSum_le (exp_term_le hβ hL ht0 htL) h1 h2

/-- **Uniform bound for the one-dimensional Gaussian lattice sum** for every `t` and `L ≥ 1`. -/
theorem lattice1D_sup {β L : ℝ} (hβ : 0 < β) (hL : 1 ≤ L) (t : ℝ) :
    ∑' n : ℤ, Real.exp (-(β * (t - n * L) ^ 2)) ≤ 2 + theta (β / 8) := by
  have hLp : 0 < L := by linarith
  set k : ℤ := ⌊t / L⌋
  set t₀ : ℝ := t - k * L
  have hk1 : (k : ℝ) ≤ t / L := Int.floor_le _
  have hk2 : t / L < k + 1 := Int.lt_floor_add_one _
  have ht0 : 0 ≤ t₀ := by
    have : (k : ℝ) * L ≤ t := by rwa [le_div_iff₀ hLp] at hk1
    simp only [t₀]; linarith
  have htL : t₀ ≤ L := by
    have : t < (k + 1) * L := by rwa [div_lt_iff₀ hLp] at hk2
    simp only [t₀]; nlinarith
  have hre : ∑' n : ℤ, Real.exp (-(β * (t - n * L) ^ 2)) =
      ∑' m : ℤ, Real.exp (-(β * (t₀ - m * L) ^ 2)) := by
    rw [← (Equiv.addRight k).tsum_eq]
    congr 1
    funext m
    simp only [Equiv.coe_addRight, Int.cast_add, t₀]
    congr 2
    ring
  rw [hre]
  refine (lattice1D_cell hβ hL ht0 htL).trans ?_
  have e1 : Real.exp (-(β * t₀ ^ 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have e2 : Real.exp (-(β * (t₀ - L) ^ 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have e3 : Real.exp (-(β * L ^ 2 / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have := theta_nonneg (β / 8)
  nlinarith

/-! ### Lattice sums of Gaussian-bounded profiles -/

section Bounds

variable {K β L : ℝ} {g : Plane → ℝ}

theorem shift_bound (hg : GBound K β g) (n : ℤ) (y : Plane) :
    |g (shift L n y)| ≤
      K * Real.exp (-(β * y.2 ^ 2)) * Real.exp (-(β * (y.1 - n * L) ^ 2)) := by
  refine (hg _).trans (le_of_eq ?_)
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  simp only [shift, radiusSq]
  ring

/-- `|∑ₙ g(y - nLe₁)| ≤ K e^{-βy₂²} ∑ₙ e^{-β(y₁-nL)²}`. -/
theorem latticeSum_abs_le (hK : 0 ≤ K) (hβ : 0 < β) (hL : L ≠ 0) (hg : GBound K β g)
    (y : Plane) :
    |latticeSum L g y| ≤
      K * Real.exp (-(β * y.2 ^ 2)) * ∑' n : ℤ, Real.exp (-(β * (y.1 - n * L) ^ 2)) := by
  have hs := (hg.xdecay hK hβ).summable_norm hL y
  have hsum := summable_exp_shift hβ hL y.1
  rw [← tsum_mul_left]
  refine (norm_tsum_le_tsum_norm hs).trans ?_
  exact hs.tsum_le_tsum (fun n => shift_bound hg n y) (hsum.mul_left _)

/-- Uniform bound on the lattice sum, for every period `L ≥ 1`. -/
theorem latticeSum_sup (hK : 0 ≤ K) (hβ : 0 < β) (hL : 1 ≤ L) (hg : GBound K β g)
    (y : Plane) : |latticeSum L g y| ≤ K * (2 + theta (β / 8)) := by
  refine (latticeSum_abs_le hK hβ (by positivity) hg y).trans ?_
  have e : Real.exp (-(β * y.2 ^ 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have h1 := lattice1D_sup hβ hL y.1
  have h0 : 0 ≤ ∑' n : ℤ, Real.exp (-(β * (y.1 - n * L) ^ 2)) :=
    tsum_nonneg fun _ => (Real.exp_pos _).le
  calc K * Real.exp (-(β * y.2 ^ 2)) * ∑' n : ℤ, Real.exp (-(β * (y.1 - n * L) ^ 2))
      ≤ K * 1 * (2 + theta (β / 8)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left e hK) h1 h0 (by positivity)
    _ = K * (2 + theta (β / 8)) := by ring

/-- Bound on one cell `0 ≤ y₁ ≤ L`, keeping the two nearest Gaussians. -/
theorem latticeSum_cell (hK : 0 ≤ K) (hβ : 0 < β) (hL : 1 ≤ L) (hg : GBound K β g)
    (y : Plane) (h0 : 0 ≤ y.1) (h1 : y.1 ≤ L) :
    |latticeSum L g y| ≤ K * Real.exp (-(β * y.2 ^ 2)) *
      (Real.exp (-(β * y.1 ^ 2)) + Real.exp (-(β * (y.1 - L) ^ 2)) +
        Real.exp (-(β * L ^ 2 / 2)) * theta (β / 8)) :=
  (latticeSum_abs_le hK hβ (by positivity) hg y).trans
    (mul_le_mul_of_nonneg_left (lattice1D_cell hβ hL h0 h1) (by positivity))

/-- Continuity of the lattice sum of a continuous Gaussian-bounded profile. -/
theorem latticeSum_continuous (hc : Continuous g) (hK : 0 ≤ K) (hβ : 0 < β) (hL : L ≠ 0)
    (hg : GBound K β g) : Continuous (latticeSum L g) := by
  rw [continuous_iff_continuousAt]
  intro z
  let s : Set Plane := {y | |y.1 - z.1| < 1}
  have hs : IsOpen s := isOpen_lt (by fun_prop) continuous_const
  have hz : z ∈ s := by simp [s]
  have hcont : ContinuousOn (fun y => ∑' n : ℤ, g (shift L n y)) s := by
    refine continuousOn_tsum (u := fun n : ℤ =>
        K * (Real.exp β * Real.exp (-(β / 2 * (z.1 - n * L) ^ 2))))
      (fun n => (hc.comp (by unfold shift; fun_prop)).continuousOn)
      ((summable_exp_shift (half_pos hβ) hL z.1).mul_left _ |>.mul_left _) ?_
    intro n y hy
    rw [Real.norm_eq_abs]
    have h1 := shift_bound (L := L) hg n y
    have e : Real.exp (-(β * y.2 ^ 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have h2 := exp_shift_local (d := n * L) hβ hy
    calc |g (shift L n y)|
        ≤ K * Real.exp (-(β * y.2 ^ 2)) * Real.exp (-(β * (y.1 - n * L) ^ 2)) := h1
      _ ≤ K * 1 * (Real.exp β * Real.exp (-(β / 2 * (z.1 - n * L) ^ 2))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left e hK) h2 (Real.exp_pos _).le (by positivity)
      _ = K * (Real.exp β * Real.exp (-(β / 2 * (z.1 - n * L) ^ 2))) := by ring
  exact hcont.continuousAt (hs.mem_nhds hz)

end Bounds

/-! ### Derivatives of lattice sums of `GP` profiles -/

theorem GP.gbound_pos {f : Plane → ℝ} (hf : GP f) :
    ∃ K β : ℝ, 0 ≤ K ∧ 0 < β ∧ GBound K β f := hf.bound

theorem GP.latticeSum_continuous {f : Plane → ℝ} (hf : GP f) {L : ℝ} (hL : L ≠ 0) :
    Continuous (latticeSum L f) := by
  obtain ⟨K, β, hK, hβ, hb⟩ := hf.bound
  exact B0147.latticeSum_continuous hf.continuous hK hβ hL hb

theorem GP.hasDerivAt_lattice_x {f g : Plane → ℝ} (hf : GP f) (hg : GP g)
    (hd : ∀ y : Plane, HasDerivAt (fun t => f (t, y.2)) (g y) y.1) {L : ℝ} (hL : L ≠ 0)
    (z : Plane) :
    HasDerivAt (fun t => latticeSum L f (t, z.2)) (latticeSum L g z) z.1 :=
  B0146.hasDerivAt_latticeSum_x hL hd hf.xdecay hg.xdecay z

theorem GP.hasDerivAt_lattice_y {f g : Plane → ℝ} (hf : GP f) (hg : GP g)
    (hd : ∀ y : Plane, HasDerivAt (fun t => f (y.1, t)) (g y) y.2) {L : ℝ} (hL : L ≠ 0)
    (z : Plane) :
    HasDerivAt (fun t => latticeSum L f (z.1, t)) (latticeSum L g z) z.2 :=
  B0146.hasDerivAt_latticeSum_y hL hd hf.xdecay hg.xdecay z

/-- The lattice sum of a `GP` profile has genuine partial derivatives everywhere. -/
theorem GP.lattice_hasPartial {f : Plane → ℝ} (hf : GP f) {L : ℝ} (hL : L ≠ 0) (z : Plane) :
    B0146.HasPartialX (latticeSum L f) z ∧ B0146.HasPartialY (latticeSum L f) z := by
  obtain ⟨gx, hgx, hdx⟩ := hf.derivX
  obtain ⟨gy, hgy, hdy⟩ := hf.derivY
  exact ⟨B0146.hasPartialX_of (hf.hasDerivAt_lattice_x hgx hdx hL z),
    B0146.hasPartialY_of (hf.hasDerivAt_lattice_y hgy hdy hL z)⟩

/-- **Termwise differentiation along any word**: every iterated classical partial derivative of
the lattice sum of a `GP` profile is the lattice sum of a `GP` profile, independent of the
period. -/
theorem GP.derivWord_lattice {f : Plane → ℝ} (hf : GP f) (w : List Bool) :
    ∃ g : Plane → ℝ, GP g ∧ ∀ L : ℝ, L ≠ 0 → derivWord w (latticeSum L f) = latticeSum L g := by
  induction w with
  | nil => exact ⟨f, hf, fun L _ => rfl⟩
  | cons b w ih =>
    obtain ⟨g, hg, hw⟩ := ih
    cases b
    · obtain ⟨g', hg', hd⟩ := hg.derivY
      refine ⟨g', hg', fun L hL => ?_⟩
      show partialY (derivWord w (latticeSum L f)) = _
      rw [hw L hL]
      exact B0146.partialY_latticeSum hL hd hg.xdecay hg'.xdecay
    · obtain ⟨g', hg', hd⟩ := hg.derivX
      refine ⟨g', hg', fun L hL => ?_⟩
      show partialX (derivWord w (latticeSum L f)) = _
      rw [hw L hL]
      exact B0146.partialX_latticeSum hL hd hg.xdecay hg'.xdecay

end UnforcedLeray.B0147
