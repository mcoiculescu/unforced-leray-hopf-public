import UnforcedLeray.Short.PartIIb.StatementsMixed

/-!
# Legacy helper for `PartII-b:T22/1`: the `jb`-weighted decay class forces periodic data to vanish

**Status: historical.** This file records why the first version of `CylSmoothDecay` /
`IsRegularCylFlow` in `Sub/T22.lean` (decay weight `jb^N`, `jb = 1 + q² + η²`) was wrong. Since
`ORG:cyl-weight` those structures use the weight `(1 + η²)^N`; the old classes live on here, as
`Legacy.CylSmoothDecay`, `Legacy.IsRegularCylFlow`, `Legacy.CylClassicalExists`, only to keep the
refutation compiling and auditable. Nothing outside the refutation (`Sub/T22_1.lean`) uses them.

`Legacy.CylSmoothDecay c g` asks `g` to be `c`-periodic in `q` and to satisfy
`(|g| + |∂_q g| + |∂_η g| + |lapP g|) · jb^N ≤ C` for every `N`.
A `c`-periodic function cannot decay in `q`: at a fixed point `x` the translates
`(x.1 + n c, x.2)` carry the same value while `jb` tends to infinity, so `g ≡ 0` when `c ≠ 0`.
`Legacy.IsRegularCylFlow` contains the same decay clause uniformly in the age, so every slice
vanishes. Consequently `Legacy.CylClassicalExists` forces every test datum to be zero.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb

namespace Legacy

/-- The first version of `CylSmoothDecay` (decay weight `jb^N`; refuted below). -/
structure CylSmoothDecay (c : ℝ) (g : B0579.Plane → ℝ) : Prop where
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g
  periodic : ∀ x : B0579.Plane, g (x.1 + c, x.2) = g x
  decay : ∀ N : ℝ, ∃ C : ℝ, ∀ x : B0579.Plane,
    (|g x| + |B0579.pd 0 g x| + |B0579.pd 1 g x| + |lapP g x|) * B0579.jb x ^ N ≤ C

/-- The first version of `IsRegularCylFlow` (decay weight `jb^N`). -/
structure IsRegularCylFlow (c ν : ℝ) (v : ℝ → B0579.Plane → UnforcedLeray.Train.Vec) (s T : ℝ)
    (ω : ℝ → B0579.Plane → ℝ) : Prop where
  smooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × B0579.Plane => ω z.1 z.2) (Icc s T ×ˢ univ)
  slice : ∀ σ ∈ Icc s T, CylSmoothDecay c (ω σ)
  decay : ∀ N : ℝ, ∃ C : ℝ, ∀ σ ∈ Icc s T, ∀ x : B0579.Plane,
    (|ω σ x| + |B0579.pd 0 (ω σ) x| + |B0579.pd 1 (ω σ) x| + |lapP (ω σ) x|) * B0579.jb x ^ N ≤ C
  pde : ∀ σ ∈ Icc s T, ∀ x : B0579.Plane,
    HasDerivWithinAt (fun r => ω r x)
      (ν * lapP (ω σ) x - (v σ x 0 * B0579.pd 0 (ω σ) x + v σ x 1 * B0579.pd 1 (ω σ) x))
      (Icc s T) σ

/-- The first version of `CylClassicalExists` (against the `jb`-weighted classes). -/
def CylClassicalExists : Prop :=
  ∀ (Sg : ℝ), 0 < Sg → ∀ (ν c δ : ℝ), 0 < ν → 0 < c → 0 ≤ δ → ∀ tr : B0140.TrainSol ν c,
    TrainClose tr Sg δ → ∀ s : ℝ, 0 ≤ s → s ≤ Sg / ν → ∀ f : B0579.Plane → ℝ,
      B0579.IsCylTest c f →
        ∃ ω : ℝ → B0579.Plane → ℝ, IsRegularCylFlow c ν tr.v s (Sg / ν) ω ∧ ω s = f

theorem cylSmoothDecay_shift {c : ℝ} {g : B0579.Plane → ℝ} (hg : CylSmoothDecay c g)
    (x : B0579.Plane) (n : ℕ) : g (x.1 + (n : ℝ) * c, x.2) = g x := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := hg.periodic (x.1 + (n : ℝ) * c, x.2)
    have e : (x.1 + ((n + 1 : ℕ) : ℝ) * c, x.2)
        = ((x.1 + (n : ℝ) * c, x.2).1 + c, (x.1 + (n : ℝ) * c, x.2).2) := by
      ext <;> simp <;> ring
    rw [e, h, ih]

theorem cylSmoothDecay_eq_zero {c : ℝ} (hc : c ≠ 0) {g : B0579.Plane → ℝ}
    (hg : CylSmoothDecay c g) : g = 0 := by
  funext x
  show g x = 0
  obtain ⟨C, hC⟩ := hg.decay 1
  have hx : (|g x| + |B0579.pd 0 g x| + |B0579.pd 1 g x| + |lapP g x|) * B0579.jb x ≤ C := by
    have := hC x
    rwa [Real.rpow_one] at this
  have hC0 : 0 ≤ C := le_trans (mul_nonneg (by positivity) (B0579.jb_pos x).le) hx
  by_contra hne
  have ha : 0 < |g x| := abs_pos.mpr hne
  have hne' : |g x| ≠ 0 := ha.ne'
  have hcpos : 0 < |c| := abs_pos.mpr hc
  obtain ⟨n, hn⟩ := exists_nat_gt ((|x.1| + (C / |g x| + 1)) / |c|)
  have hnc : |x.1| + (C / |g x| + 1) < (n : ℝ) * |c| := (div_lt_iff₀ hcpos).mp hn
  have h3 : |(n : ℝ) * c| = (n : ℝ) * |c| := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
  have h2 : |(n : ℝ) * c| ≤ |x.1 + (n : ℝ) * c| + |x.1| := by
    have h := abs_add_le (x.1 + (n : ℝ) * c) (-x.1)
    rwa [show x.1 + (n : ℝ) * c + -x.1 = (n : ℝ) * c by ring, abs_neg] at h
  have hdiv : 0 ≤ C / |g x| := div_nonneg hC0 ha.le
  have hbig : C / |g x| + 1 < |x.1 + (n : ℝ) * c| := by linarith
  have hM1 : 1 ≤ |x.1 + (n : ℝ) * c| := by linarith
  have hjb : |x.1 + (n : ℝ) * c| ≤ B0579.jb (x.1 + (n : ℝ) * c, x.2) := by
    simp only [B0579.jb]
    nlinarith [mul_nonneg (abs_nonneg (x.1 + (n : ℝ) * c)) (sub_nonneg.mpr hM1),
      sq_abs (x.1 + (n : ℝ) * c), sq_nonneg x.2]
  have hsh := cylSmoothDecay_shift hg x n
  have key := hC (x.1 + (n : ℝ) * c, x.2)
  rw [Real.rpow_one, hsh] at key
  have hgy : |g x| * B0579.jb (x.1 + (n : ℝ) * c, x.2) ≤ C := by
    have h6 := mul_le_mul_of_nonneg_right
      (show |g x| ≤ |g x| + |B0579.pd 0 g (x.1 + (n : ℝ) * c, x.2)|
          + |B0579.pd 1 g (x.1 + (n : ℝ) * c, x.2)| + |lapP g (x.1 + (n : ℝ) * c, x.2)| by
        linarith [abs_nonneg (B0579.pd 0 g (x.1 + (n : ℝ) * c, x.2)),
          abs_nonneg (B0579.pd 1 g (x.1 + (n : ℝ) * c, x.2)),
          abs_nonneg (lapP g (x.1 + (n : ℝ) * c, x.2))])
      (B0579.jb_pos (x.1 + (n : ℝ) * c, x.2)).le
    linarith
  have hM : |g x| * (C / |g x| + 1) = C + |g x| := by
    field_simp
  have h4 : |g x| * (C / |g x| + 1) < |g x| * |x.1 + (n : ℝ) * c| :=
    mul_lt_mul_of_pos_left hbig ha
  have h5 : |g x| * |x.1 + (n : ℝ) * c| ≤ |g x| * B0579.jb (x.1 + (n : ℝ) * c, x.2) :=
    mul_le_mul_of_nonneg_left hjb ha.le
  linarith

theorem regularCylFlow_eq_zero {c ν : ℝ} (hc : c ≠ 0)
    {v : ℝ → B0579.Plane → UnforcedLeray.Train.Vec} {s T : ℝ}
    {ω : ℝ → B0579.Plane → ℝ} (h : IsRegularCylFlow c ν v s T ω)
    {σ : ℝ} (hσ : σ ∈ Icc s T) : ω σ = 0 :=
  cylSmoothDecay_eq_zero hc (h.slice σ hσ)

/-- Any solution provided by `CylClassicalExists` for a train with `TrainClose` is zero at the
initial age, so the datum must vanish. -/
theorem classicalExists_forces_zero (hEx : CylClassicalExists) {Sg ν c δ : ℝ} (hSg : 0 < Sg)
    (hν : 0 < ν) (hc : 0 < c) (hδ : 0 ≤ δ) (tr : B0140.TrainSol ν c) (htr : TrainClose tr Sg δ)
    (f : B0579.Plane → ℝ) (hf : B0579.IsCylTest c f) : f = 0 := by
  obtain ⟨ω, hω, hωs⟩ :=
    hEx Sg hSg ν c δ hν hc hδ tr htr 0 le_rfl (div_nonneg hSg.le hν.le) f hf
  rw [← hωs]
  exact regularCylFlow_eq_zero hc.ne' hω ⟨le_rfl, div_nonneg hSg.le hν.le⟩

end Legacy

end UnforcedLeray.Short.IIb
