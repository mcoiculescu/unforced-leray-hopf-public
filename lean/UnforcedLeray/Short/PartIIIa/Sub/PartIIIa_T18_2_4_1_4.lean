import UnforcedLeray.Short.PartIIIa.Sub.T18_2_4_1

/-!
# Part III-a, task `PartIII-a:T18/2/4/1/4` (decomposition): Gaussian decay of the Duhamel solution

Target (`Sub/T18_2_4_1.lean`): `DuhamelDecay`. Source of record:
`the November 2 reference manuscript`,
lines 3427-3440 (Gaussian decay of the heat Duhamel solution, locally uniformly in `s`).

Plan. (1) `DuhDecGaussTail`: the one-dimensional Gaussian tail. (2) `DuhDecFactor`: the planar heat
kernel is the product of two one-dimensional kernels. (3) `DuhDecValue`: the value bound
`‖w(s,x)‖ ≤ C e^{-κ η²}` for `s ≤ s₂` (uses (1), (2), the cutoff `0 < r ≤ s₂ - a` and the
`η`-support of `h`). (4) `DuhDecDirNice`: the `x`-directional derivative of a nice source is nice.
(5) `DuhDecFderivComm`: `∂_e w = duhamelHeat` of `∂_e h` (differentiation under the integral).
(6) `duhDec_opNorm_le`: `‖L‖ ≤ ‖L(1,0)‖ + ‖L(0,1)‖` (proved here). The wiring `duhamelDecay_of`
combines (3)-(6) (proved here).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The `x`-directional derivative of the source: `(∂_e h)(s, x) = D_x h(s, x) e`. -/
def duhDecDirDeriv (e : ℝ × ℝ) (h : ℝ × (ℝ × ℝ) → ℂ) : ℝ × (ℝ × ℝ) → ℂ :=
  fun p => fderiv ℝ (fun y => h (p.1, y)) p.2 e

/-- **Leaf 1** (SP 3427-3440): the one-dimensional Gaussian tail
`∫_{|t| ≥ A} G_θ(t) dt ≤ 2 e^{-A²/(8θ)}` for `θ > 0`, `A ≥ 0`
(`G_θ = B0191.heatKernel 1 θ`; Mathlib `integral_gaussian`, `Real.exp_neg`, or
`Lib/Gaussian/Kernel.lean`). -/
def DuhDecGaussTail : Prop :=
  ∀ θ A : ℝ, 0 < θ → 0 ≤ A →
    ∫ t in {t : ℝ | A ≤ |t|}, UnforcedLeray.B0191.heatKernel 1 θ t ≤ 2 * Real.exp (-A ^ 2 / (8 * θ))

/-- **Leaf 2** (SP 3427-3440): the planar heat kernel factorises,
`B0284.heatKernel2 θ z = B0191.heatKernel 1 θ z.1 * B0191.heatKernel 1 θ z.2` for `θ > 0`
(`Units/B0191.lean:37`, `Units/B0284/Defs.lean`). -/
def DuhDecFactor : Prop :=
  ∀ θ : ℝ, 0 < θ → ∀ z : ℝ × ℝ,
    UnforcedLeray.B0284.heatKernel2 θ z =
      UnforcedLeray.B0191.heatKernel 1 θ z.1 * UnforcedLeray.B0191.heatKernel 1 θ z.2

/-- **Leaf 3** (SP 3427-3440): value half of the decay. For `s ≤ a` the solution vanishes; for
`a < s ≤ s₂` only `0 < r ≤ s₂ - a` contributes; for `|η| ≥ 2R` the support of `h` forces
`|z₂| ≥ |η|/2`, and Leaves 1, 2 plus `∫ G = 1` give `‖w‖ ≤ H T · 2 e^{-η²/(32 ν T)}`
(`H = sup‖h‖`, `T = s₂ - a`); for `|η| < 2R` use `‖w‖ ≤ H T`. -/
def DuhDecValue : Prop :=
  ∀ (c ν : ℝ) (h : ℝ × (ℝ × ℝ) → ℂ), 0 < c → 0 < ν → NiceScalar c h → ∀ s₂ : ℝ,
    ∃ C κ : ℝ, 0 < κ ∧ ∀ (s : ℝ) (x : ℝ × ℝ), s ≤ s₂ →
      ‖duhamelHeat ν h s x‖ ≤ C * Real.exp (-κ * x.2 ^ 2)

/-- **Leaf 4** (SP 3427-3440): the `x`-directional derivative of a nice source is a nice source
(smooth, `c`-periodic in `q`, same vanishing in `s` for the same `a, B`, and for `|η| > R`
because the slice vanishes on the open set `{|η| > R}`). -/
def DuhDecDirNice : Prop :=
  ∀ (c : ℝ) (e : ℝ × ℝ) (h : ℝ × (ℝ × ℝ) → ℂ), NiceScalar c h → NiceScalar c (duhDecDirDeriv e h)

/-- **Leaf 5** (SP 3427-3440): the `x`-derivative of the Duhamel solution is the Duhamel solution
of the differentiated source (differentiation under the integral sign, as in `duhamelSmooth`):
`D_x w(s,·)(x) e = duhamelHeat ν (∂_e h) s x`. -/
def DuhDecFderivComm : Prop :=
  ∀ (c ν : ℝ) (h : ℝ × (ℝ × ℝ) → ℂ), 0 < c → 0 < ν → NiceScalar c h → ∀ (s : ℝ) (x e : ℝ × ℝ),
    fderiv ℝ (fun y => duhamelHeat ν h s y) x e = duhamelHeat ν (duhDecDirDeriv e h) s x

/-- Operator norm on `ℝ × ℝ` (sup norm) is bounded by the two coordinate values. -/
theorem duhDec_opNorm_le (L : ℝ × ℝ →L[ℝ] ℂ) : ‖L‖ ≤ ‖L (1, 0)‖ + ‖L (0, 1)‖ := by
  refine L.opNorm_le_bound (by positivity) fun v => ?_
  have hv : L v = v.1 • L (1, 0) + v.2 • L (0, 1) := by
    have e : v = v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
    calc L v = L (v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ))) := congrArg L e
      _ = _ := by rw [map_add, map_smul, map_smul]
  have h1 : ‖v.1‖ ≤ ‖v‖ := by simpa using norm_fst_le v
  have h2 : ‖v.2‖ ≤ ‖v‖ := by simpa using norm_snd_le v
  calc ‖L v‖ ≤ ‖v.1 • L (1, 0)‖ + ‖v.2 • L (0, 1)‖ := hv ▸ norm_add_le _ _
    _ = ‖v.1‖ * ‖L (1, 0)‖ + ‖v.2‖ * ‖L (0, 1)‖ := by rw [norm_smul, norm_smul]
    _ ≤ ‖v‖ * ‖L (1, 0)‖ + ‖v‖ * ‖L (0, 1)‖ := by gcongr
    _ = (‖L (1, 0)‖ + ‖L (0, 1)‖) * ‖v‖ := by ring

/-- `DuhamelDecay` from the leaves. -/
theorem duhamelDecay_of (hV : DuhDecValue) (hN : DuhDecDirNice) (hC : DuhDecFderivComm) :
    DuhamelDecay := by
  intro c ν h hc hν hn s₂
  obtain ⟨C0, κ0, hκ0, h0⟩ := hV c ν h hc hν hn s₂
  obtain ⟨C1, κ1, hκ1, h1⟩ := hV c ν _ hc hν (hN c (1, 0) h hn) s₂
  obtain ⟨C2, κ2, hκ2, h2⟩ := hV c ν _ hc hν (hN c (0, 1) h hn) s₂
  refine ⟨|C0| + |C1| + |C2|, min κ0 (min κ1 κ2), lt_min hκ0 (lt_min hκ1 hκ2), ?_⟩
  intro s x hs
  have ht : 0 ≤ x.2 ^ 2 := sq_nonneg _
  have key : ∀ {C κ : ℝ} {L : ℝ}, min κ0 (min κ1 κ2) ≤ κ → 0 ≤ C → L ≤ C * Real.exp (-κ * x.2 ^ 2) →
      L ≤ C * Real.exp (-(min κ0 (min κ1 κ2)) * x.2 ^ 2) := by
    intro C κ L hκ hC hL
    refine hL.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC)
    nlinarith
  have e0 : ‖duhamelHeat ν h s x‖ ≤ |C0| * Real.exp (-(min κ0 (min κ1 κ2)) * x.2 ^ 2) :=
    key (min_le_left _ _) (abs_nonneg _)
      ((h0 s x hs).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_nonneg _)))
  have e1 : ‖duhamelHeat ν (duhDecDirDeriv (1, 0) h) s x‖ ≤
      |C1| * Real.exp (-(min κ0 (min κ1 κ2)) * x.2 ^ 2) :=
    key ((min_le_right _ _).trans (min_le_left _ _)) (abs_nonneg _)
      ((h1 s x hs).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_nonneg _)))
  have e2 : ‖duhamelHeat ν (duhDecDirDeriv (0, 1) h) s x‖ ≤
      |C2| * Real.exp (-(min κ0 (min κ1 κ2)) * x.2 ^ 2) :=
    key ((min_le_right _ _).trans (min_le_right _ _)) (abs_nonneg _)
      ((h2 s x hs).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_nonneg _)))
  have hg := duhDec_opNorm_le (fderiv ℝ (fun y => duhamelHeat ν h s y) x)
  rw [hC c ν h hc hν hn s x (1, 0), hC c ν h hc hν hn s x (0, 1)] at hg
  show ‖duhamelHeat ν h s x‖ + ‖fderiv ℝ (fun y => duhamelHeat ν h s y) x‖ ≤ _
  nlinarith [e0, e1, e2, hg]

end UnforcedLeray.Short.IIIa
