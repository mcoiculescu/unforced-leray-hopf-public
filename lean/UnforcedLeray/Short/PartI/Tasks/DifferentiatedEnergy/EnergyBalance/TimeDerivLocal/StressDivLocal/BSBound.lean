import UnforcedLeray.Lib.Cylinder.Basic
import UnforcedLeray.Units.B0147.Bilinear
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance.TimeDerivLocal.StressDivLocal.Lattice

/-!
# Part I, task `PartI:T08/4/1/1/5/2` (`qcJet_BS_bound_loc`)

Source: `the November 2 reference manuscript`, lines 326-335 and 2217-2234.

Local-in-period version of `UnforcedLeray.B0147.BS.bound`: for every class member `H` of `BS`
and every `L₀ > 0`, there are constants with `|H L y| ≤ C e^{-γ y₂²}` for all `L ≥ L₀`.

Pair case: `bil L f g = (∑ f)(∑ g) - ∑ fg`. Each lattice sum is bounded by
`K e^{-β y₂²} · S(L,y₁)` with `S` the one-dimensional lattice sum, and `S` is bounded uniformly
for `L ≥ L₀` by `qcJet_lattice1D_sup_loc`. The product `fg` is Gaussian with rate `2β`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

noncomputable section

/-- The pointwise product of two functions with a common Gaussian bound `K e^{-β|y|²}` has
Gaussian bound `K² e^{-2β|y|²}`. -/
theorem gbound_mul_self {K β : ℝ} {f g : UnforcedLeray.Cyl.Plane → ℝ} (hK : 0 ≤ K)
    (hf : UnforcedLeray.B0147.GBound K β f) (hg : UnforcedLeray.B0147.GBound K β g) :
    UnforcedLeray.B0147.GBound (K * K) (2 * β) (fun x => f x * g x) := by
  intro y
  have e : Real.exp (-(β * UnforcedLeray.GaussianVortex.radiusSq y)) *
      Real.exp (-(β * UnforcedLeray.GaussianVortex.radiusSq y)) =
      Real.exp (-((2 * β) * UnforcedLeray.GaussianVortex.radiusSq y)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc |f y * g y| = |f y| * |g y| := abs_mul _ _
    _ ≤ (K * Real.exp (-(β * UnforcedLeray.GaussianVortex.radiusSq y))) *
          (K * Real.exp (-(β * UnforcedLeray.GaussianVortex.radiusSq y))) :=
        mul_le_mul (hf y) (hg y) (abs_nonneg _) (mul_nonneg hK (Real.exp_pos _).le)
    _ = K * K * (Real.exp (-(β * UnforcedLeray.GaussianVortex.radiusSq y)) *
          Real.exp (-(β * UnforcedLeray.GaussianVortex.radiusSq y))) := by ring
    _ = K * K * Real.exp (-((2 * β) * UnforcedLeray.GaussianVortex.radiusSq y)) := by rw [e]

theorem qcJet_BS_bound_loc {H : ℝ → UnforcedLeray.Cyl.Plane → ℝ} (hH : UnforcedLeray.B0147.BS H)
    {L₀ : ℝ} (hL₀ : 0 < L₀) : ∃ C γ : ℝ, 0 ≤ C ∧ 0 < γ ∧ ∀ L : ℝ, L₀ ≤ L →
      ∀ y : UnforcedLeray.Cyl.Plane, |H L y| ≤ C * Real.exp (-(γ * y.2 ^ 2)) := by
  induction hH with
  | @pair f g hf hg =>
    obtain ⟨K, β, hK, hβ, hfb, hgb⟩ := hf.bound₂ hg
    obtain ⟨M₁, hM₁⟩ := qcJet_lattice1D_sup_loc hβ hL₀
    obtain ⟨M₂, hM₂⟩ := qcJet_lattice1D_sup_loc (mul_pos two_pos hβ) hL₀
    have hfg := gbound_mul_self hK hfb hgb
    have hm₁0 : 0 ≤ max M₁ 0 := le_max_right _ _
    have hm₂0 : 0 ≤ max M₂ 0 := le_max_right _ _
    have hS₁ : ∀ L : ℝ, L₀ ≤ L → ∀ t : ℝ,
        ∑' n : ℤ, Real.exp (-(β * (t - n * L) ^ 2)) ≤ max M₁ 0 :=
      fun L hL t => (hM₁ L hL t).trans (le_max_left _ _)
    have hS₂ : ∀ L : ℝ, L₀ ≤ L → ∀ t : ℝ,
        ∑' n : ℤ, Real.exp (-((2 * β) * (t - n * L) ^ 2)) ≤ max M₂ 0 :=
      fun L hL t => (hM₂ L hL t).trans (le_max_left _ _)
    refine ⟨K * K * (max M₁ 0 * max M₁ 0 + max M₂ 0), 2 * β,
      mul_nonneg (mul_nonneg hK hK) (add_nonneg (mul_nonneg hm₁0 hm₁0) hm₂0),
      mul_pos two_pos hβ, fun L hL y => ?_⟩
    show |UnforcedLeray.B0147.bil L f g y| ≤ _
    have hL0 : 0 < L := lt_of_lt_of_le hL₀ hL
    have hLne : L ≠ 0 := hL0.ne'
    rw [UnforcedLeray.B0147.bil_eq hf.xdecay hg.xdecay hLne y]
    have hA := UnforcedLeray.B0147.latticeSum_abs_le hK hβ hLne hfb y
    have hB := UnforcedLeray.B0147.latticeSum_abs_le hK hβ hLne hgb y
    have hD := UnforcedLeray.B0147.latticeSum_abs_le (mul_nonneg hK hK) (mul_pos two_pos hβ)
      hLne hfg y
    have s1 := hS₁ L hL y.1
    have s2 := hS₂ L hL y.1
    have s1n : 0 ≤ ∑' n : ℤ, Real.exp (-(β * (y.1 - n * L) ^ 2)) :=
      tsum_nonneg fun _ => (Real.exp_pos _).le
    have s2n : 0 ≤ ∑' n : ℤ, Real.exp (-((2 * β) * (y.1 - n * L) ^ 2)) :=
      tsum_nonneg fun _ => (Real.exp_pos _).le
    have he : Real.exp (-(β * y.2 ^ 2)) * Real.exp (-(β * y.2 ^ 2)) =
        Real.exp (-((2 * β) * y.2 ^ 2)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hEnn : 0 ≤ Real.exp (-((2 * β) * y.2 ^ 2)) := (Real.exp_pos _).le
    -- product of the two lattice sums
    have hAB : |UnforcedLeray.B0146.latticeSum L f y *
        UnforcedLeray.B0146.latticeSum L g y| ≤
        K * K * Real.exp (-((2 * β) * y.2 ^ 2)) * (max M₁ 0 * max M₁ 0) := by
      rw [abs_mul]
      calc |UnforcedLeray.B0146.latticeSum L f y| * |UnforcedLeray.B0146.latticeSum L g y|
          ≤ (K * Real.exp (-(β * y.2 ^ 2)) * ∑' n : ℤ, Real.exp (-(β * (y.1 - n * L) ^ 2))) *
            (K * Real.exp (-(β * y.2 ^ 2)) * ∑' n : ℤ, Real.exp (-(β * (y.1 - n * L) ^ 2))) :=
            mul_le_mul hA hB (abs_nonneg _)
              (mul_nonneg (mul_nonneg hK (Real.exp_pos _).le) s1n)
        _ = K * K * (Real.exp (-(β * y.2 ^ 2)) * Real.exp (-(β * y.2 ^ 2))) *
            ((∑' n : ℤ, Real.exp (-(β * (y.1 - n * L) ^ 2))) *
              (∑' n : ℤ, Real.exp (-(β * (y.1 - n * L) ^ 2)))) := by ring
        _ = K * K * Real.exp (-((2 * β) * y.2 ^ 2)) *
            ((∑' n : ℤ, Real.exp (-(β * (y.1 - n * L) ^ 2))) *
              (∑' n : ℤ, Real.exp (-(β * (y.1 - n * L) ^ 2)))) := by rw [he]
        _ ≤ K * K * Real.exp (-((2 * β) * y.2 ^ 2)) * (max M₁ 0 * max M₁ 0) :=
            mul_le_mul_of_nonneg_left (mul_le_mul s1 s1 s1n hm₁0)
              (mul_nonneg (mul_nonneg hK hK) hEnn)
    -- the cross term
    have hDb : |UnforcedLeray.B0146.latticeSum L (fun x => f x * g x) y| ≤
        K * K * Real.exp (-((2 * β) * y.2 ^ 2)) * max M₂ 0 := by
      calc |UnforcedLeray.B0146.latticeSum L (fun x => f x * g x) y|
          ≤ K * K * Real.exp (-((2 * β) * y.2 ^ 2)) *
              ∑' n : ℤ, Real.exp (-((2 * β) * (y.1 - n * L) ^ 2)) := hD
        _ ≤ K * K * Real.exp (-((2 * β) * y.2 ^ 2)) * max M₂ 0 :=
            mul_le_mul_of_nonneg_left s2 (mul_nonneg (mul_nonneg hK hK) hEnn)
    calc |UnforcedLeray.B0146.latticeSum L f y * UnforcedLeray.B0146.latticeSum L g y -
          UnforcedLeray.B0146.latticeSum L (fun x => f x * g x) y|
        ≤ |UnforcedLeray.B0146.latticeSum L f y * UnforcedLeray.B0146.latticeSum L g y| +
          |UnforcedLeray.B0146.latticeSum L (fun x => f x * g x) y| := abs_sub _ _
      _ ≤ K * K * Real.exp (-((2 * β) * y.2 ^ 2)) * (max M₁ 0 * max M₁ 0) +
          K * K * Real.exp (-((2 * β) * y.2 ^ 2)) * max M₂ 0 := add_le_add hAB hDb
      _ = K * K * (max M₁ 0 * max M₁ 0 + max M₂ 0) * Real.exp (-((2 * β) * y.2 ^ 2)) := by ring
  | @add H₁ H₂ _ _ ih₁ ih₂ =>
    obtain ⟨C₁, γ₁, hC₁, hγ₁, h₁⟩ := ih₁
    obtain ⟨C₂, γ₂, hC₂, hγ₂, h₂⟩ := ih₂
    refine ⟨C₁ + C₂, min γ₁ γ₂, add_nonneg hC₁ hC₂, lt_min hγ₁ hγ₂, fun L hL y => ?_⟩
    have m1 : Real.exp (-(γ₁ * y.2 ^ 2)) ≤ Real.exp (-(min γ₁ γ₂ * y.2 ^ 2)) :=
      Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)))
    have m2 : Real.exp (-(γ₂ * y.2 ^ 2)) ≤ Real.exp (-(min γ₁ γ₂ * y.2 ^ 2)) :=
      Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)))
    have a1 := h₁ L hL y
    have a2 := h₂ L hL y
    calc |(H₁ L y + H₂ L y)| ≤ |H₁ L y| + |H₂ L y| := abs_add_le _ _
      _ ≤ C₁ * Real.exp (-(min γ₁ γ₂ * y.2 ^ 2)) + C₂ * Real.exp (-(min γ₁ γ₂ * y.2 ^ 2)) :=
          add_le_add (a1.trans (mul_le_mul_of_nonneg_left m1 hC₁))
            (a2.trans (mul_le_mul_of_nonneg_left m2 hC₂))
      _ = (C₁ + C₂) * Real.exp (-(min γ₁ γ₂ * y.2 ^ 2)) := by ring

end

end UnforcedLeray.Short.PartI
