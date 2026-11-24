import UnforcedLeray.Short.PartI.Sub.T01Class

/-!
# Part I, task `PartI:TC/1`: the one-sided interpolation inequality

Source of record: `the November 2 reference manuscript`, lines 397-404 (the
interpolation inequality used for the BUC train). The Prop `LkOneSided` is defined in
`Sub/T01Class.lean`; this file proves it.

Route (a monotonicity argument; no Taylor formula with remainder is needed). Let `c = f'(x)` and
let `B` bound `|f''|`.

1. `f'` is `B`-Lipschitz: `|f'(t) - f'(x)| ≤ B |t - x|` (mean value inequality for `f'`, whose
   derivative is `f'' = iteratedDeriv 2 f`; `Convex.norm_image_sub_le_of_norm_deriv_le`).
2. For `t ≥ x` the function `G(s) = f(s) - f(x) - (s - x) c - B (s - x)²/2` has derivative
   `f'(s) - c - B(s - x) ≤ 0` on `[x, ∞)`, so it is antitone there, and `G(x) = 0`; hence
   `f(t) - f(x) - (t - x) c ≤ B (t - x)²/2`.
3. Applying 2 to `-f` gives the matching lower bound.
4. With `t = x + h`: `h |c| ≤ |f(x+h)| + |f(x)| + B h²/2 ≤ 2m + B h²/2`; divide by `h > 0`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartI

/-- `f'` is `B`-Lipschitz when its derivative `f'' = deriv (deriv f)` is bounded by `B`. -/
private theorem lkOneSided_deriv_lipschitz {f : ℝ → ℝ} (hH : Differentiable ℝ (deriv f)) {B : ℝ}
    (hB : ∀ t, |deriv (deriv f) t| ≤ B) (x t : ℝ) :
    |deriv f t - deriv f x| ≤ B * |t - x| := by
  have h := convex_univ.norm_image_sub_le_of_norm_deriv_le (f := deriv f) (C := B)
    (fun y _ => hH y) (fun y _ => by rw [Real.norm_eq_abs]; exact hB y) (mem_univ x) (mem_univ t)
  simpa only [Real.norm_eq_abs] using h

/-- One-sided Taylor bound: if `f'(t) - f'(x) ≤ B (t - x)` for `t ≥ x`, then
`f(t) - f(x) - (t - x) f'(x) ≤ B (t - x)² / 2` for `t ≥ x`. -/
private theorem lkOneSided_taylor_upper {f : ℝ → ℝ} (hf : Differentiable ℝ f) {x B : ℝ}
    (hlip : ∀ t, x ≤ t → deriv f t - deriv f x ≤ B * (t - x)) (t : ℝ) (ht : x ≤ t) :
    f t - f x - (t - x) * deriv f x ≤ B * (t - x) ^ 2 / 2 := by
  have hG : ∀ s : ℝ,
      HasDerivAt (fun s => f s - f x - (s - x) * deriv f x - B * (s - x) ^ 2 / 2)
        (deriv f s - deriv f x - B * (s - x)) s := by
    intro s
    have h1 : HasDerivAt f (deriv f s) s := (hf s).hasDerivAt
    have h2 : HasDerivAt (fun y : ℝ => y - x) 1 s := (hasDerivAt_id' (x := s)).sub_const x
    have h3 := ((h1.sub_const (f x)).sub (h2.mul_const (deriv f x))).sub
      (((h2.pow 2).const_mul B).div_const 2)
    refine h3.congr_deriv ?_
    norm_num
    ring
  have hanti : AntitoneOn (fun s => f s - f x - (s - x) * deriv f x - B * (s - x) ^ 2 / 2)
      (Ici x) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici x) ?_ ?_ ?_
    · exact fun s _ => (hG s).continuousAt.continuousWithinAt
    · exact fun s _ => (hG s).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      rw [(hG s).deriv]
      have hs' := hlip s (le_of_lt (Set.mem_Ioi.mp hs))
      linarith
  have key := hanti (Set.mem_Ici.mpr le_rfl) (show t ∈ Ici x from ht) ht
  dsimp only at key
  linarith

/-- **`PartI:TC/1`. One-sided interpolation** (Landau-Kolmogorov type, proved by monotonicity of the
one-sided Taylor remainder): if `f` is `C²` with `|f''| ≤ B` everywhere and `|f(t)| ≤ m` for all
`t ≥ x`, then for every `h > 0`, `|f'(x)| ≤ 2m/h + B h/2`. -/
theorem lkOneSided : LkOneSided := by
  intro f x B m h hf _hB0 _hm0 hh hB2 hm
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hH : Differentiable ℝ (deriv f) := by
    have h1 := hf.differentiable_iteratedDeriv 1 (by norm_num)
    rwa [iteratedDeriv_one] at h1
  have h2 : ∀ t, iteratedDeriv 2 f t = deriv (deriv f) t := by
    intro t
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hB' : ∀ t, |deriv (deriv f) t| ≤ B := fun t => by
    rw [← h2 t]
    exact hB2 t
  -- one-sided Lipschitz bounds on `[x, ∞)`, for `f'` and for `-f'`
  have hup_lip : ∀ t, x ≤ t → deriv f t - deriv f x ≤ B * (t - x) := by
    intro t ht
    have h1 := lkOneSided_deriv_lipschitz hH hB' x t
    rw [abs_of_nonneg (sub_nonneg.2 ht)] at h1
    exact le_trans (le_abs_self _) h1
  have hlo_lip : ∀ t, x ≤ t → deriv (-f) t - deriv (-f) x ≤ B * (t - x) := by
    intro t ht
    rw [deriv.neg, deriv.neg]
    have h1 := lkOneSided_deriv_lipschitz hH hB' x t
    rw [abs_of_nonneg (sub_nonneg.2 ht)] at h1
    have h3 := (abs_le.mp h1).1
    linarith
  -- Taylor bounds at `t = x + h`, upper and (via `-f`) lower
  have hup := lkOneSided_taylor_upper hfd hup_lip (x + h) (by linarith)
  have hlow := lkOneSided_taylor_upper hfd.neg hlo_lip (x + h) (by linarith)
  simp only [Pi.neg_apply, deriv.neg] at hlow
  have e : x + h - x = h := by ring
  rw [e] at hup hlow
  -- `h |f'(x)| ≤ |f(x+h)| + |f(x)| + B h²/2 ≤ 2m + B h²/2`
  have hfx := abs_le.mp (hm x le_rfl)
  have hfxh := abs_le.mp (hm (x + h) (by linarith))
  have key : |h * deriv f x| ≤ 2 * m + B * h ^ 2 / 2 := by
    rw [abs_le]
    constructor
    · linarith
    · linarith
  have hc : |h * deriv f x| = h * |deriv f x| := by
    rw [abs_mul, abs_of_pos hh]
  have hfin : h * |deriv f x| ≤ 2 * m + B * h ^ 2 / 2 := by
    rw [← hc]
    exact key
  have hdiv : |deriv f x| ≤ (2 * m + B * h ^ 2 / 2) / h := by
    rw [le_div_iff₀ hh]
    linarith
  have hh' : h ≠ 0 := ne_of_gt hh
  have hsplit : (2 * m + B * h ^ 2 / 2) / h = 2 * m / h + B * h / 2 := by
    field_simp
  linarith

end UnforcedLeray.Short.PartI
