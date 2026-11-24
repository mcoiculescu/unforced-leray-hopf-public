import UnforcedLeray.Short.PartI.Sub.T02_3_8

/-!
# Part I, task `PartI:T02/3/8/AffineZero`: a `C²` function with zero second derivative that decays is zero

Target: `CylPoisAffineZero` (`Short/PartI/Sub/T02_3_8.lean`, Leaf M4).
Source of record: `the November 2 reference manuscript`, lines 276-288 (the mean part
`P + avg(v_η²)` is affine in `η` and decays, hence vanishes).

Proof.  Since `F` is `C²`, `deriv F` is differentiable with zero derivative, hence constant `a`, and
then `F η = a η + F 0`.  The limit of `F` along `atTop` (a part of `cocompact ℝ`) forces `a = 0`,
because the increments `F (η + 1) - F η = a` tend to `0`; then `F` is constant with limit `0`.
-/

open Filter Topology

namespace UnforcedLeray.Short.PartI

/-- An affine function `x ↦ a x + c` that tends to `0` along `atTop` is identically `0`. -/
theorem cpAZ_affine_zero_of_atTop (F : ℝ → ℝ) (a c : ℝ) (hF : ∀ x, F x = a * x + c)
    (hlim : Tendsto F atTop (𝓝 0)) : ∀ x, F x = 0 := by
  -- the increments `F (x + 1) - F x` tend to `0 - 0`, and they are the constant `a`
  have h1 : Tendsto (fun x : ℝ => F (x + 1)) atTop (𝓝 0) :=
    hlim.comp (tendsto_atTop_add_const_right _ 1 tendsto_id)
  have hg : Tendsto (fun x : ℝ => F (x + 1) - F x) atTop (𝓝 (0 - 0)) := h1.sub hlim
  have hdiff : ∀ x : ℝ, F (x + 1) - F x = a := fun x => by
    linear_combination hF (x + 1) - hF x
  have hg2 : Tendsto (fun _ : ℝ => a) atTop (𝓝 (0 - 0)) := (tendsto_congr hdiff).mp hg
  have ha0 : a = 0 := by
    have h := tendsto_nhds_unique (tendsto_const_nhds (x := a) (f := atTop)) hg2
    linarith
  -- now `F` is the constant `c`, and its limit `0` is `c`
  have hFc : ∀ x : ℝ, F x = c := fun x => by
    rw [hF x, ha0, zero_mul, zero_add]
  have hc0 : c = 0 := by
    have h1' : Tendsto (fun _ : ℝ => c) atTop (𝓝 0) := (tendsto_congr hFc).mp hlim
    exact tendsto_nhds_unique (tendsto_const_nhds (x := c) (f := atTop)) h1'
  intro x
  rw [hFc x, hc0]

/-- **Leaf M4 is true.** A `C²` function on `ℝ` with vanishing second derivative that tends to `0`
at infinity is identically zero. -/
theorem cylPoisAffineZero : CylPoisAffineZero := by
  unfold CylPoisAffineZero
  intro F hF2 h2 hlim η
  have hF : Differentiable ℝ F := hF2.differentiable (by norm_num)
  have hdF : Differentiable ℝ (deriv F) := hF2.differentiable_deriv_two
  -- `deriv F` is constant
  have hder : ∀ x : ℝ, deriv F x = deriv F 0 := fun x => is_const_of_deriv_eq_zero hdF h2 x 0
  -- `F x - a x` has zero derivative, with `a = deriv F 0`, hence `F x = a x + F 0`
  have hGd : ∀ y : ℝ, HasDerivAt (fun z : ℝ => F z - deriv F 0 * z) (deriv F y - deriv F 0) y := by
    intro y
    have h1 : HasDerivAt F (deriv F y) y := (hF y).hasDerivAt
    have h2' : HasDerivAt (fun z : ℝ => deriv F 0 * z) (deriv F 0 * 1) y :=
      (hasDerivAt_id' y).const_mul (deriv F 0)
    have h3 := h1.sub h2'
    rwa [mul_one] at h3
  have hGdiff : Differentiable ℝ (fun z : ℝ => F z - deriv F 0 * z) :=
    fun y => (hGd y).differentiableAt
  have hG' : ∀ y : ℝ, deriv (fun z : ℝ => F z - deriv F 0 * z) y = 0 := by
    intro y
    rw [(hGd y).deriv, hder y, sub_self]
  have hform : ∀ x : ℝ, F x = deriv F 0 * x + F 0 := by
    intro x
    have h := is_const_of_deriv_eq_zero hGdiff hG' x 0
    simp only [mul_zero, sub_zero] at h
    linarith
  have hFtop : Tendsto F atTop (𝓝 0) := hlim.mono_left atTop_le_cocompact
  exact cpAZ_affine_zero_of_atTop F (deriv F 0) (F 0) hform hFtop η

end UnforcedLeray.Short.PartI
