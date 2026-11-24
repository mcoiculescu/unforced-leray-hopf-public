import UnforcedLeray.Short.PartIIa.Sub.R02_2

/-!
# Part II-a, task `PartII-a:R02/2/3`: slice derivatives are bounded by jets (`SliceJetBound`)

Source of record: `the November 2 reference manuscript`, lines 439-446
(route step (ii)).

Target: `UnforcedLeray.Short.PartIIa.sliceJetBound_of (hD : ProfileDict) : SliceJetBound`.

Write `S = {y | 0 < y.2.2}`. The proof has three parts.

* `sjb_deriv`: the derivative in `s` of `s ↦ D^n g(y + s w)(m)` is `D^{n+1} g(y + s w)(cons w m)`.
* `sjb_eq0`, `sjb_bound`: iterated slice derivatives along a fixed direction `w` are the iterated
  Fréchet derivatives on the same direction list; the bound `|∂_s^a D^n g(y + s w)(m)| ≤ ‖D^{n+a} g‖`
  for unit vectors `m i`, `w` follows from `ContinuousMultilinearMap.le_opNorm`.
* `sjb_calc`: for `g : ℝ × ℝ → ℝ` of class `C^∞`,
  `|∂_η^a ∂_q^b g (q, η)| ≤ ‖D^{a+b} g (q, η)‖`.

`sliceJetBound_of` combines them: `g z := ∂_s^k F(s, z)` is `C^∞` (by `ProfileDict` with `a = b = 0`
and `contDiffOn_iterate`), and `ageJet k (a+b) F s = D^{a+b} g` by definition.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0184 UnforcedLeray.B0190
open UnforcedLeray.Short.PartI (meanStream ageJet)

/-! ### Slice calculus on `ℝ × ℝ` -/

/-- The derivative in the line parameter of `s ↦ D^n g(y + s w)(m)` is `D^{n+1} g(y + s w)(w, m)`. -/
theorem sjb_deriv (g : ℝ × ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (n : ℕ) (m : Fin n → ℝ × ℝ)
    (y w : ℝ × ℝ) (t : ℝ) :
    deriv (fun s : ℝ => iteratedFDeriv ℝ n g (y + s • w) m) t =
      iteratedFDeriv ℝ (n + 1) g (y + t • w) (Fin.cons w m) := by
  have hd : Differentiable ℝ (iteratedFDeriv ℝ n g) :=
    hg.differentiable_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top _)
  have hΦ : ∀ z : ℝ × ℝ, DifferentiableAt ℝ (fun z => iteratedFDeriv ℝ n g z m) z := fun z =>
    (hd z).continuousMultilinear_apply_const m
  have key : ∀ z : ℝ × ℝ, iteratedFDeriv ℝ (n + 1) g z (Fin.cons w m) =
      fderiv ℝ (fun z => iteratedFDeriv ℝ n g z m) z w := by
    intro z
    have h := (hd z).iteratedFDeriv_succ_apply_left' (m := Fin.cons w m)
    simp only [Fin.tail_cons, Fin.cons_zero] at h
    exact h
  have hline : HasDerivAt (fun s : ℝ => y + s • w) w t := by
    simpa using ((hasDerivAt_id t).smul_const w).const_add y
  have hΦt : HasFDerivAt (fun z => iteratedFDeriv ℝ n g z m)
      (fderiv ℝ (fun z => iteratedFDeriv ℝ n g z m) (y + t • w)) (y + t • w) :=
    (hΦ (y + t • w)).hasFDerivAt
  have hcomp : HasDerivAt (fun s : ℝ => iteratedFDeriv ℝ n g (y + s • w) m)
      (fderiv ℝ (fun z => iteratedFDeriv ℝ n g z m) (y + t • w) w) t :=
    HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => y + s • w) (x := t) hΦt hline
  rw [hcomp.deriv, key]

/-- Along a fixed direction `w`, the `a`-th `s`-derivative of `g(y + s w)` is `D^a g(y + t w)(w, …, w)`. -/
theorem sjb_eq0 (g : ℝ × ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (a : ℕ) (y w : ℝ × ℝ) :
    ∀ t : ℝ, iteratedDeriv a (fun s : ℝ => g (y + s • w)) t =
      iteratedFDeriv ℝ a g (y + t • w) (fun _ => w) := by
  induction a with
  | zero =>
    intro t
    simp [iteratedDeriv_zero, iteratedFDeriv_zero_apply]
  | succ a ih =>
    intro t
    rw [iteratedDeriv_succ]
    have hf : iteratedDeriv a (fun s : ℝ => g (y + s • w)) =
        fun s => iteratedFDeriv ℝ a g (y + s • w) (fun _ => w) := funext ih
    rw [hf, sjb_deriv g hg a (fun _ => w) y w t]
    have hc : (Fin.cons w (fun _ : Fin a => w) : Fin (a + 1) → ℝ × ℝ) = fun _ => w := by
      funext i
      induction i using Fin.cases with
      | zero => simp
      | succ j => simp
    rw [hc]

/-- Bound for iterated slice derivatives: for unit vectors `m i` and `‖w‖ ≤ 1`,
`|∂_s^a [D^n g(y + s w)(m)]| ≤ ‖D^{n+a} g(y + t w)‖`. -/
theorem sjb_bound (g : ℝ × ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (a : ℕ) :
    ∀ (n : ℕ) (m : Fin n → ℝ × ℝ) (y w : ℝ × ℝ) (t : ℝ),
      (∀ i, ‖m i‖ ≤ 1) → ‖w‖ ≤ 1 →
      |iteratedDeriv a (fun s : ℝ => iteratedFDeriv ℝ n g (y + s • w) m) t| ≤
        ‖iteratedFDeriv ℝ (n + a) g (y + t • w)‖ := by
  induction a with
  | zero =>
    intro n m y w t hm _
    have h1 := (iteratedFDeriv ℝ n g (y + t • w)).le_opNorm m
    have h2 : ∏ i, ‖m i‖ ≤ 1 :=
      Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => hm i)
    rw [iteratedDeriv_zero, Nat.add_zero, ← Real.norm_eq_abs]
    calc ‖iteratedFDeriv ℝ n g (y + t • w) m‖
        ≤ ‖iteratedFDeriv ℝ n g (y + t • w)‖ * ∏ i, ‖m i‖ := h1
      _ ≤ ‖iteratedFDeriv ℝ n g (y + t • w)‖ * 1 :=
          mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = ‖iteratedFDeriv ℝ n g (y + t • w)‖ := mul_one _
  | succ a ih =>
    intro n m y w t hm hw
    rw [iteratedDeriv_succ']
    have hf : deriv (fun s : ℝ => iteratedFDeriv ℝ n g (y + s • w) m) =
        fun s => iteratedFDeriv ℝ (n + 1) g (y + s • w) (Fin.cons w m) := by
      funext s
      exact sjb_deriv g hg n m y w s
    rw [hf]
    have hcons : ∀ i, ‖(Fin.cons w m : Fin (n + 1) → ℝ × ℝ) i‖ ≤ 1 := by
      intro i
      induction i using Fin.cases with
      | zero => simpa using hw
      | succ j => simpa using hm j
    have h := ih (n + 1) (Fin.cons w m) y w t hcons hw
    rw [show n + (a + 1) = n + 1 + a by omega]
    exact h

/-- The mixed slice derivative `∂_η^a ∂_q^b g` of a `C^∞` function `g` on `ℝ × ℝ` is bounded by
the operator norm of `D^{a+b} g`. -/
theorem sjb_calc (g : ℝ × ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (a b : ℕ) (q η : ℝ) :
    |iteratedDeriv a (fun e : ℝ => iteratedDeriv b (fun q' : ℝ => g (q', e)) q) η| ≤
      ‖iteratedFDeriv ℝ (a + b) g (q, η)‖ := by
  have hx : ∀ t : ℝ, ((q, 0) : ℝ × ℝ) + t • ((0, 1) : ℝ × ℝ) = (q, t) := by
    intro t
    ext <;> simp
  have hin : ∀ e : ℝ, iteratedDeriv b (fun q' : ℝ => g (q', e)) q =
      iteratedFDeriv ℝ b g (q, e) (fun _ => ((1, 0) : ℝ × ℝ)) := by
    intro e
    have h := sjb_eq0 g hg b ((0, e) : ℝ × ℝ) ((1, 0) : ℝ × ℝ) q
    have hx' : ∀ t : ℝ, ((0, e) : ℝ × ℝ) + t • ((1, 0) : ℝ × ℝ) = (t, e) := by
      intro t
      ext <;> simp
    simpa only [hx'] using h
  have hfun : (fun e : ℝ => iteratedDeriv b (fun q' : ℝ => g (q', e)) q) =
      (fun t : ℝ => iteratedFDeriv ℝ b g ((q, 0) + t • ((0, 1) : ℝ × ℝ))
        (fun _ => ((1, 0) : ℝ × ℝ))) := by
    funext e
    rw [hin e, hx e]
  rw [hfun]
  have hb := sjb_bound g hg a b (fun _ => ((1, 0) : ℝ × ℝ)) ((q, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ) η
    (fun _ => by simp [Prod.norm_def]) (by simp [Prod.norm_def])
  rw [hx η, Nat.add_comm b a] at hb
  exact hb

/-! ### The target -/

/-- **Slice derivatives are bounded by jets** (source lines 439-446, step (ii)): from the profile
dictionary `ProfileDict`, the nested slice derivative of a train field is bounded by `ageJet`. -/
theorem sliceJetBound_of (hD : ProfileDict) : SliceJetBound := by
  intro F hF a b k q η s hs
  have hAge : ∀ G : ProfilePoint → ℝ, ContDiffOn ℝ ∞ G {y : ProfilePoint | 0 < y.2.2} →
      ContDiffOn ℝ ∞ (partialAge G) {y : ProfilePoint | 0 < y.2.2} :=
    fun G hG => contDiffOn_fderiv_apply hG esDir
  have hiter : ContDiffOn ℝ ∞ (partialAge^[k] (trainProfile F)) {y : ProfilePoint | 0 < y.2.2} :=
    contDiffOn_iterate partialAge hAge hF k
  have hmap : ContDiff ℝ ∞ (fun z : ℝ × ℝ => ((z.1, (z.2, s)) : ProfilePoint)) :=
    contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const)
  have hc : ContDiff ℝ ∞ ((partialAge^[k] (trainProfile F)) ∘
      fun z : ℝ × ℝ => ((z.1, (z.2, s)) : ProfilePoint)) :=
    hiter.comp_contDiff hmap (fun _ => by simpa using hs)
  have heq : (fun z : ℝ × ℝ => iteratedDeriv k (fun r => F r z) s) =
      (partialAge^[k] (trainProfile F)) ∘ fun z : ℝ × ℝ => ((z.1, (z.2, s)) : ProfilePoint) := by
    funext z
    have h := hD F hF 0 0 k ((z.1, (z.2, s)) : ProfilePoint) hs
    simp only [Function.iterate_zero, id_eq, iteratedDeriv_zero] at h
    exact h.symm
  have hgs : ContDiff ℝ ∞ (fun z : ℝ × ℝ => iteratedDeriv k (fun r => F r z) s) := by
    rw [heq]
    exact hc
  exact sjb_calc (fun z : ℝ × ℝ => iteratedDeriv k (fun r => F r z) s) hgs a b q η

end UnforcedLeray.Short.PartIIa
