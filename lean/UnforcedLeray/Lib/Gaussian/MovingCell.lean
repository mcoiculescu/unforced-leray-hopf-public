import UnforcedLeray.Lib.Gaussian.HeatDilationFlow

/-!
# Periodization on moving cells (INF22 G7, item 5; unit B0333)


target G7 item 5 and §2.10 row B0333 (tex 6317–6330). In the rescaled variable `y = x/√a` the
cell width is `d(z)` with `d_z/d = -ϑ_OU/2`, and periodization satisfies the exact identities

`ϑ D(P_d q) - ∂_z(P_d q) = ϑ P_d Dq`,  `ϑ D^#(P_d g) + ∂_z(P_d g) = ϑ P_d D^# g`,

with `D = Δ + ½y·∇ + 2` (tex 722) and `D^# = Δ - ½y·∇ + 1` (tex 6315, B0332), for
`z`-independent smooth decaying `q`, `g` (tex 6328–6329).

Main results:
* `hasDerivAt_periodize_period`: the derivative of `p ↦ P_p q(y)` in the period is
  `-∑_n n ∂_1 q(y - npe₁)` (dominated termwise differentiation on `p/2 < p' < 2p`);
* `fderiv_periodize_apply_self`: `y·∇(P_p q)(y) = P_p(y·∇q)(y) + p ∑_n n ∂_1 q(y - npe₁)`
  (the `y·∇` acting on translates, blueprint infrastructure of B0333);
* `movingCell_identity`, `movingCell_identity_dual` (**B0333**): the two displayed identities at
  a point `z₀` where `d(z₀) > 0` and `d'(z₀) = -(ϑ/2) d(z₀)`.

Hypotheses: `q` is `C²` with translate bounds `C(1+|y₁|)^{-s}`, `s > 1`, on `q`,
`(1+‖y‖)‖Dq(y)‖` and `‖D²q‖` (as in `HeatDilationFlow.lean`).
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.Gaussian

open Real Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The dual operator `D^# = Δ - ½ y·∇ + 1` of tex 6315 (B0332). -/
def dualGen (g : ℝ × ℝ → E) (y : ℝ × ℝ) : E :=
  Cyl.laplacian g y - (1 / 2 : ℝ) • fderiv ℝ g y y + g y

/-- The period-shift sum `∑_n n ∂_1 q(y - npe₁)`. -/
def periodShift (q : ℝ × ℝ → E) (p : ℝ) (y : ℝ × ℝ) : E :=
  ∑' n : ℤ, (n : ℝ) • fderiv ℝ q (y.1 - n * p, y.2) ((1 : ℝ), (0 : ℝ))

/-- `‖Dq(z)‖ ≤ C(1+|z₁|)^{-s}` from the weighted bound. -/
theorem norm_fderiv_le_of_weighted {q : ℝ × ℝ → E} {C s : ℝ}
    (h1 : ∀ z, (1 + ‖z‖) * ‖fderiv ℝ q z‖ ≤ C * (1 + |z.1|) ^ (-s)) (z : ℝ × ℝ) :
    ‖fderiv ℝ q z‖ ≤ C * (1 + |z.1|) ^ (-s) := by
  refine le_trans ?_ (h1 z)
  have := norm_nonneg (fderiv ℝ q z)
  have := norm_nonneg z
  nlinarith

/-- `‖Dq(z) z‖ ≤ C(1+|z₁|)^{-s}` from the weighted bound. -/
theorem norm_fderiv_apply_self_le {q : ℝ × ℝ → E} {C s : ℝ}
    (h1 : ∀ z, (1 + ‖z‖) * ‖fderiv ℝ q z‖ ≤ C * (1 + |z.1|) ^ (-s)) (z : ℝ × ℝ) :
    ‖fderiv ℝ q z z‖ ≤ C * (1 + |z.1|) ^ (-s) := by
  refine ((fderiv ℝ q z).le_opNorm z).trans ?_
  refine le_trans ?_ (h1 z)
  have := norm_nonneg (fderiv ℝ q z)
  have := norm_nonneg z
  nlinarith

/-- The domination of the period-shift terms: for `p/2 ≤ p'`,
`|n| ‖∂_1 q(y₁ - np', y₂)‖ ≤ K (1+|n|)^{-s}` with `K` independent of `n` and `p'`. -/
theorem norm_shift_term_le {q : ℝ × ℝ → E} {C s p p' : ℝ} (hs : 0 ≤ s) (hp : 0 < p)
    (hp' : p / 2 ≤ p') (h0C : 0 ≤ C)
    (h1 : ∀ z, (1 + ‖z‖) * ‖fderiv ℝ q z‖ ≤ C * (1 + |z.1|) ^ (-s)) (y : ℝ × ℝ) (n : ℤ) :
    ‖(n : ℝ) • fderiv ℝ q (y.1 - n * p', y.2) ((1 : ℝ), (0 : ℝ))‖ ≤
      (2 / p * (1 + |y.1|) * C * (1 + |y.1|) ^ s * (min 1 (p / 2)) ^ (-s)) *
        (1 + |(n : ℝ)|) ^ (-s) := by
  set w : ℝ × ℝ := (y.1 - n * p', y.2) with hw
  have hp'0 : 0 < p' := by linarith
  have he : ‖((1 : ℝ), (0 : ℝ))‖ = 1 := by simp
  -- `|n| ≤ (2/p)(1+|y₁|)(1+‖w‖)`
  have hn : |(n : ℝ)| ≤ 2 / p * ((1 + |y.1|) * (1 + ‖w‖)) := by
    have h1 : |(n : ℝ)| * (p / 2) ≤ |(n : ℝ) * p'| := by
      rw [abs_mul, abs_of_pos hp'0]
      exact mul_le_mul_of_nonneg_left hp' (abs_nonneg _)
    have h2 : |(n : ℝ) * p'| ≤ |y.1| + |w.1| := by
      have : (n : ℝ) * p' = y.1 - w.1 := by rw [hw]; ring
      rw [this]; exact abs_sub _ _
    have h3 : |w.1| ≤ ‖w‖ := by
      rw [← Real.norm_eq_abs]; exact norm_fst_le w
    have h4 : |y.1| + |w.1| ≤ (1 + |y.1|) * (1 + ‖w‖) := by
      have := abs_nonneg y.1
      have := norm_nonneg w
      nlinarith
    have h5 : |(n : ℝ)| * (p / 2) ≤ (1 + |y.1|) * (1 + ‖w‖) := by linarith
    calc |(n : ℝ)| = (|(n : ℝ)| * (p / 2)) * (2 / p) := by field_simp
      _ ≤ ((1 + |y.1|) * (1 + ‖w‖)) * (2 / p) :=
          mul_le_mul_of_nonneg_right h5 (by positivity)
      _ = 2 / p * ((1 + |y.1|) * (1 + ‖w‖)) := by ring
  -- Peetre and the lattice bound
  have hpe : (1 + |w.1|) ^ (-s) ≤ (1 + |y.1|) ^ s * (1 + |p' * (n : ℝ)|) ^ (-s) := by
    have h := one_add_abs_rpow_neg_le hs w.1 (-y.1)
    rw [abs_neg, show w.1 + -y.1 = -(p' * n) by rw [hw]; ring, abs_neg] at h
    exact h
  have hlat : (1 + |p' * (n : ℝ)|) ^ (-s) ≤ (min 1 (p / 2)) ^ (-s) * (1 + |(n : ℝ)|) ^ (-s) :=
    one_add_abs_mul_rpow_neg_le hs (by linarith) hp' _
  have hD := h1 w
  have hys : 0 ≤ (1 + |y.1|) ^ s := by positivity
  calc ‖(n : ℝ) • fderiv ℝ q w ((1 : ℝ), (0 : ℝ))‖
      ≤ |(n : ℝ)| * ‖fderiv ℝ q w‖ := by
        rw [norm_smul, Real.norm_eq_abs]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        simpa [he] using (fderiv ℝ q w).le_opNorm ((1 : ℝ), (0 : ℝ))
    _ ≤ (2 / p * ((1 + |y.1|) * (1 + ‖w‖))) * ‖fderiv ℝ q w‖ :=
        mul_le_mul_of_nonneg_right hn (norm_nonneg _)
    _ = 2 / p * (1 + |y.1|) * ((1 + ‖w‖) * ‖fderiv ℝ q w‖) := by ring
    _ ≤ 2 / p * (1 + |y.1|) * (C * (1 + |w.1|) ^ (-s)) :=
        mul_le_mul_of_nonneg_left hD (by positivity)
    _ ≤ 2 / p * (1 + |y.1|) * (C * ((1 + |y.1|) ^ s *
          ((min 1 (p / 2)) ^ (-s) * (1 + |(n : ℝ)|) ^ (-s)))) := by
        gcongr
        exact hpe.trans (mul_le_mul_of_nonneg_left hlat hys)
    _ = _ := by ring

section Complete

variable [CompleteSpace E]

/-- Summability of the period-shift terms. -/
theorem summable_shift_term {q : ℝ × ℝ → E} {C s p : ℝ} (hs : 1 < s) (hp : 0 < p)
    (h0C : 0 ≤ C) (h1 : ∀ z, (1 + ‖z‖) * ‖fderiv ℝ q z‖ ≤ C * (1 + |z.1|) ^ (-s))
    (y : ℝ × ℝ) :
    Summable fun n : ℤ => (n : ℝ) • fderiv ℝ q (y.1 - n * p, y.2) ((1 : ℝ), (0 : ℝ)) :=
  Summable.of_norm_bounded ((summable_one_add_abs_int_rpow hs).mul_left _)
    fun n => norm_shift_term_le (by linarith) hp (by linarith) h0C h1 y n

/-- **B0333, period derivative.** For `p > 0`, `∂_p P_p q(y) = -∑_n n ∂_1 q(y - npe₁)`. -/
theorem hasDerivAt_periodize_period {q : ℝ × ℝ → E} (hq : Differentiable ℝ q) {C s p : ℝ}
    (hs : 1 < s) (hp : 0 < p) (h0 : ∀ z, ‖q z‖ ≤ C * (1 + |z.1|) ^ (-s))
    (h1 : ∀ z, (1 + ‖z‖) * ‖fderiv ℝ q z‖ ≤ C * (1 + |z.1|) ^ (-s)) (y : ℝ × ℝ) :
    HasDerivAt (fun p' => periodize p' q y) (-periodShift q p y) p := by
  have hs0 : 0 ≤ s := by linarith
  have hC := nonneg_of_translate_bound h0
  set K : ℝ := 2 / p * (1 + |y.1|) * C * (1 + |y.1|) ^ s * (min 1 (p / 2)) ^ (-s) with hK
  have hu : Summable fun n : ℤ => K * (1 + |(n : ℝ)|) ^ (-s) :=
    (summable_one_add_abs_int_rpow hs).mul_left K
  have hpt : p ∈ Ioo (p / 2) (2 * p) := ⟨by linarith, by linarith⟩
  have hderiv : ∀ (n : ℤ) (p' : ℝ), p' ∈ Ioo (p / 2) (2 * p) →
      HasDerivAt (fun p'' => q (y.1 - n * p'', y.2))
        (-((n : ℝ) • fderiv ℝ q (y.1 - n * p', y.2) ((1 : ℝ), (0 : ℝ)))) p' := by
    intro n p' _
    have hin : HasDerivAt (fun p'' : ℝ => ((y.1 - n * p'', y.2) : ℝ × ℝ))
        ((-((n : ℝ) * 1), (0 : ℝ))) p' :=
      (((hasDerivAt_id p').const_mul (n : ℝ)).const_sub y.1).prodMk (hasDerivAt_const p' y.2)
    have h := (hq (y.1 - n * p', y.2)).hasFDerivAt.comp_hasDerivAt p' hin
    refine HasDerivAt.congr_deriv h ?_
    have : ((-((n : ℝ) * 1), (0 : ℝ)) : ℝ × ℝ) = (-(n : ℝ)) • ((1 : ℝ), (0 : ℝ)) := by
      ext <;> simp
    rw [this, ContinuousLinearMap.map_smul, neg_smul]
  have key := hasDerivAt_tsum_of_isPreconnected
    (g := fun (n : ℤ) p'' => q (y.1 - n * p'', y.2))
    (g' := fun (n : ℤ) p' => -((n : ℝ) • fderiv ℝ q (y.1 - n * p', y.2) ((1 : ℝ), (0 : ℝ))))
    hu isOpen_Ioo isPreconnected_Ioo hderiv
    (fun n p' hp' => by
      rw [norm_neg]
      exact norm_shift_term_le hs0 hp hp'.1.le hC h1 y n)
    hpt (summable_periodize hs hp.ne' h0 y) hpt
  unfold periodize periodShift
  rw [← tsum_neg]
  exact key

/-- **B0333, `y·∇` on translates.** `y·∇(P_p q)(y) = P_p(y·∇q)(y) + p ∑_n n ∂_1 q(y - npe₁)`. -/
theorem fderiv_periodize_apply_self {q : ℝ × ℝ → E} (hq : Differentiable ℝ q) {C s p : ℝ}
    (hs : 1 < s) (hp : 0 < p) (h0 : ∀ z, ‖q z‖ ≤ C * (1 + |z.1|) ^ (-s))
    (h1 : ∀ z, (1 + ‖z‖) * ‖fderiv ℝ q z‖ ≤ C * (1 + |z.1|) ^ (-s)) (y : ℝ × ℝ) :
    fderiv ℝ (periodize p q) y y =
      periodize p (fun w => fderiv ℝ q w w) y + p • periodShift q p y := by
  have hC := nonneg_of_translate_bound h0
  have h1' := norm_fderiv_le_of_weighted h1
  have hfun : periodize p q = fun y => ∑' n : ℤ, q (y - shiftVec p n) :=
    funext (periodize_eq p q)
  have hF := hasFDerivAt_tsum_translates hq hs hp.ne' h0 h1' y
  rw [hfun, hF.fderiv]
  simp_rw [fderiv_comp_sub]
  have hsumD : Summable fun n : ℤ => fderiv ℝ q (y - shiftVec p n) :=
    Summable.of_norm_bounded ((summable_translate hs hp.ne' y.1).mul_left C)
      fun n => by rw [sub_shiftVec]; exact h1' _
  have hev : (∑' n : ℤ, fderiv ℝ q (y - shiftVec p n)) y =
      ∑' n : ℤ, fderiv ℝ q (y - shiftVec p n) y :=
    (hsumD.hasSum.mapL (ContinuousLinearMap.apply ℝ E y)).tsum_eq.symm
  rw [hev]
  have hsplit : ∀ n : ℤ, fderiv ℝ q (y - shiftVec p n) y =
      fderiv ℝ q (y.1 - n * p, y.2) (y.1 - n * p, y.2) +
        p • ((n : ℝ) • fderiv ℝ q (y.1 - n * p, y.2) ((1 : ℝ), (0 : ℝ))) := by
    intro n
    rw [sub_shiftVec, smul_smul, ← ContinuousLinearMap.map_smul, ← ContinuousLinearMap.map_add]
    congr 1
    ext <;> simp; ring
  simp_rw [hsplit]
  have hA : Summable fun n : ℤ => fderiv ℝ q (y.1 - n * p, y.2) (y.1 - n * p, y.2) :=
    summable_periodize hs hp.ne' (norm_fderiv_apply_self_le h1) y
  have hB := summable_shift_term hs hp hC h1 y
  rw [hA.tsum_add (hB.const_smul p), tsum_const_smul'']
  rfl

/-- The three pieces of `P_p` applied to `Δq`, `y·∇q`, `q`. -/
theorem periodize_three {q : ℝ × ℝ → E} (hq : ContDiff ℝ 2 q) {C s p : ℝ} (hs : 1 < s)
    (hp : 0 < p) (h0 : ∀ z, ‖q z‖ ≤ C * (1 + |z.1|) ^ (-s))
    (h1 : ∀ z, (1 + ‖z‖) * ‖fderiv ℝ q z‖ ≤ C * (1 + |z.1|) ^ (-s))
    (h2 : ∀ z, ‖iteratedFDeriv ℝ 2 q z‖ ≤ C * (1 + |z.1|) ^ (-s)) (α β γ : ℝ) (y : ℝ × ℝ) :
    periodize p (fun w => α • Cyl.laplacian q w + β • fderiv ℝ q w w + γ • q w) y =
      α • periodize p (Cyl.laplacian q) y + β • periodize p (fun w => fderiv ℝ q w w) y +
        γ • periodize p q y := by
  have hL : Summable fun n : ℤ => Cyl.laplacian q (y.1 - n * p, y.2) :=
    summable_periodize hs hp.ne' (norm_laplacian_le_translate hq h2) y
  have hA : Summable fun n : ℤ => fderiv ℝ q (y.1 - n * p, y.2) (y.1 - n * p, y.2) :=
    summable_periodize hs hp.ne' (norm_fderiv_apply_self_le h1) y
  have hQ : Summable fun n : ℤ => q (y.1 - n * p, y.2) := summable_periodize hs hp.ne' h0 y
  unfold periodize
  exact (((hL.hasSum.const_smul α).add (hA.hasSum.const_smul β)).add
    (hQ.hasSum.const_smul γ)).tsum_eq

omit [CompleteSpace E] in
/-- The translate bounds of order `≤ 2` in the form used by `laplacian_periodize`. -/
theorem iteratedFDeriv_bounds_of {q : ℝ × ℝ → E} {C s : ℝ}
    (h0 : ∀ z, ‖q z‖ ≤ C * (1 + |z.1|) ^ (-s))
    (h1 : ∀ z, (1 + ‖z‖) * ‖fderiv ℝ q z‖ ≤ C * (1 + |z.1|) ^ (-s))
    (h2 : ∀ z, ‖iteratedFDeriv ℝ 2 q z‖ ≤ C * (1 + |z.1|) ^ (-s)) :
    ∀ k : ℕ, (k : ℕ∞) ≤ 2 → ∃ C' : ℝ, ∀ z,
      ‖iteratedFDeriv ℝ k q z‖ ≤ C' * (1 + |z.1|) ^ (-s) := by
  intro k hk
  refine ⟨C, fun z => ?_⟩
  have hk' : k ≤ 2 := by exact_mod_cast hk
  interval_cases k
  · rw [norm_iteratedFDeriv_zero]; exact h0 z
  · rw [norm_iteratedFDeriv_one]; exact norm_fderiv_le_of_weighted h1 z
  · exact h2 z

/-- **B0333 (tex 6319–6329), direct identity.** Let `d` be the cell width, `d(z₀) > 0`, with
`d'(z₀) = -(ϑ/2) d(z₀)`. For `C²` `q` with the translate bounds above,
`ϑ D(P_d q)(y) - ∂_z(P_{d(z)} q)(y)|_{z₀} = ϑ P_d(Dq)(y)`, `D = Δ + ½y·∇ + 2`. -/
theorem movingCell_identity {q : ℝ × ℝ → E} (hq : ContDiff ℝ 2 q) {C s : ℝ} (hs : 1 < s)
    (h0 : ∀ z, ‖q z‖ ≤ C * (1 + |z.1|) ^ (-s))
    (h1 : ∀ z, (1 + ‖z‖) * ‖fderiv ℝ q z‖ ≤ C * (1 + |z.1|) ^ (-s))
    (h2 : ∀ z, ‖iteratedFDeriv ℝ 2 q z‖ ≤ C * (1 + |z.1|) ^ (-s))
    {d : ℝ → ℝ} {z₀ ϑ : ℝ} (hd0 : 0 < d z₀) (hd : HasDerivAt d (-(ϑ / 2) * d z₀) z₀)
    (y : ℝ × ℝ) :
    ϑ • dilationGen (periodize (d z₀) q) y - deriv (fun z => periodize (d z) q y) z₀ =
      ϑ • periodize (d z₀) (dilationGen q) y := by
  have hqd : Differentiable ℝ q := hq.differentiable (by norm_num)
  have hder : HasDerivAt (fun z => periodize (d z) q y)
      ((-(ϑ / 2) * d z₀) • -periodShift q (d z₀) y) z₀ :=
    (hasDerivAt_periodize_period hqd hs hd0 h0 h1 y).scomp z₀ hd
  rw [hder.deriv, dilationGen_eq,
    laplacian_periodize hq hs hd0.ne' (iteratedFDeriv_bounds_of h0 h1 h2),
    fderiv_periodize_apply_self hqd hs hd0 h0 h1]
  have hgen : periodize (d z₀) (dilationGen q) y =
      periodize (d z₀) (fun w => (1 : ℝ) • Cyl.laplacian q w + (1 / 2 : ℝ) • fderiv ℝ q w w +
        (2 : ℝ) • q w) y := by
    unfold periodize
    congr 1; funext n
    beta_reduce
    rw [dilationGen_eq, one_smul]
  rw [hgen, periodize_three hq hs hd0 h0 h1 h2]
  module

/-- **B0333 (tex 6319–6329), dual identity.** Under the same hypotheses on `g` and `d`,
`ϑ D^#(P_d g)(y) + ∂_z(P_{d(z)} g)(y)|_{z₀} = ϑ P_d(D^# g)(y)`, `D^# = Δ - ½y·∇ + 1`. -/
theorem movingCell_identity_dual {g : ℝ × ℝ → E} (hg : ContDiff ℝ 2 g) {C s : ℝ} (hs : 1 < s)
    (h0 : ∀ z, ‖g z‖ ≤ C * (1 + |z.1|) ^ (-s))
    (h1 : ∀ z, (1 + ‖z‖) * ‖fderiv ℝ g z‖ ≤ C * (1 + |z.1|) ^ (-s))
    (h2 : ∀ z, ‖iteratedFDeriv ℝ 2 g z‖ ≤ C * (1 + |z.1|) ^ (-s))
    {d : ℝ → ℝ} {z₀ ϑ : ℝ} (hd0 : 0 < d z₀) (hd : HasDerivAt d (-(ϑ / 2) * d z₀) z₀)
    (y : ℝ × ℝ) :
    ϑ • dualGen (periodize (d z₀) g) y + deriv (fun z => periodize (d z) g y) z₀ =
      ϑ • periodize (d z₀) (dualGen g) y := by
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hder : HasDerivAt (fun z => periodize (d z) g y)
      ((-(ϑ / 2) * d z₀) • -periodShift g (d z₀) y) z₀ :=
    (hasDerivAt_periodize_period hgd hs hd0 h0 h1 y).scomp z₀ hd
  rw [hder.deriv, dualGen, laplacian_periodize hg hs hd0.ne' (iteratedFDeriv_bounds_of h0 h1 h2),
    fderiv_periodize_apply_self hgd hs hd0 h0 h1]
  have hgen : periodize (d z₀) (dualGen g) y =
      periodize (d z₀) (fun w => (1 : ℝ) • Cyl.laplacian g w + (-(1 / 2) : ℝ) • fderiv ℝ g w w +
        (1 : ℝ) • g w) y := by
    unfold periodize
    congr 1; funext n
    beta_reduce
    rw [dualGen]
    module
  rw [hgen, periodize_three hg hs hd0 h0 h1 h2]
  module

end Complete

end UnforcedLeray.Gaussian
