import UnforcedLeray.Short.PartI.Sub.T02_1_2

/-!
# Part I, task `PartI:T02/1/2/4`: `BaseDerivative` (conditional)

Source of record: `the November 2 reference manuscript`, lines 261-288
(Gallay-Slijepcevic 2015, Theorem 1.1: the solution is smooth for positive time and the datum is
in `BUC ∩ H^k`; here the first derivative of the mild `H³` solution).

The target is `BaseDerivative` (`Short/PartI/Sub/T02_1_2.lean`): if `u = s + u ⋆ u` in
`C([0,T], H³)` and the seed `s` has a `∂_j`-derivative path `s'`, then `u` has a `∂_j`-derivative
path `u'` and `u' = s' + Λ_u u'`.

## Why the sketch of the TASKS file is replaced


identification `∂_j u = w`) needs an `L²`-valued Duhamel calculus that is not in the library, and

`bilDuhamel`, the product rule `BilDuhamelDerivative` (task `PartI:T02/1/2/3`) and four elementary
leaves.

## The route (all compiled below except the four leaves)

1. `baseDerivative_of`: the *equation* `u' = s' + Λ_u u'` is free once a derivative path `u'` of
   `u` exists: by the product rule `∂_j(u ⋆ u) = u' ⋆ u + u ⋆ u'`, so
   `u = s + u ⋆ u` has the derivative path `s' + (u' ⋆ u + u ⋆ u')`, and derivative paths are
   unique (`HasDerivPath.unique`).  So `BaseDerivative` follows from
   `BilDuhamelDerivative` and `MildDerivPathExists` (only the *existence* of `u'`).
2. `mildDerivPathExists_of`: existence of `u'` by *Picard iteration around `u`* in a weighted
   (Bielecki) norm.  With `R = ‖u‖ + 1` and `λ` large, the Picard map `G(v) = s + v ⋆ v` is a
   contraction of factor `1/2` in the norm `sup_t e^{-λt}‖·(t)‖` on the set
   `{v : ‖v - u‖_∞ ≤ e^{-λT}}` (on which `‖v‖_∞ ≤ R`), whatever the starting point `v₀` in that
   set; the fixed point is `u`.  Start at `v₀` having a derivative path (`DerivDense`: density of
   such paths in `C([0,T], H³)`).  The iterates `v_m` all have derivative paths `v_m'`
   (`BilDuhamelDerivative` and `BilDuhamelAdditive`), `(v_m')` is Cauchy in the sup norm (the
   linearised weighted estimate), and the limit is a derivative path of `u` (`DerivClosed`).

The leaves are `BilWeightedEstimate` (weighted Volterra estimate for `bilDuhamel`),
`BilDuhamelAdditive`, `DerivDense` and `DerivClosed`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB

/-! ### The four open leaves -/

/-- **Leaf W** (weighted Volterra estimate for the polarised Duhamel map; source lines 261-288):
there is `C₀ > 0` (depending on `ν, c` only, not on `T` or `λ`) such that, if `‖a(r)‖ ≤ α e^{λr}`
and `‖b(r)‖ ≤ β'` on `[0,T]`, then `‖(a ⋆ b)(t)‖ ≤ (C₀/√λ) α β' e^{λt}`; and the same with the
weight on the second argument.  Proof: the integrand bound
`‖P₀ e^{ν(t-r)Δ} div F(r)‖ ≤ ‖toVecL‖ heatDivL2Coeff(ν(t-r)) ‖F(r)‖` of
`norm_projectedHeatDuhamelIntegral_le` (`Lib/TrainB/P0GaussianDuhamelGenericBound.lean`) with
`‖tensorH3Bilinear a b‖ ≤ 1536 ‖a‖ ‖b‖` (`norm_tensorH3Bilinear_apply_le`), then
`∫_0^t heatDivL2Coeff(ν θ) e^{-λθ} dθ ≤ (2/√π) ν^{-1/2} √(π/λ)`; so `C₀ = 2·1536‖toVecL‖ν^{-1/2}`
works. -/
def BilWeightedEstimate : Prop :=
  ∀ (ν c : ℝ) (hν : 0 < ν) (hc : 0 < c) (hc1 : 1 ≤ c), ∃ C₀ : ℝ, 0 < C₀ ∧
    (∀ (T : ℝ) (hT : 0 < T) (a b : MPath c T) (lam α β' : ℝ), 0 < lam → 0 ≤ α → 0 ≤ β' →
      (∀ t : Icc (0 : ℝ) T, ‖a t‖ ≤ α * Real.exp (lam * t)) →
      (∀ t : Icc (0 : ℝ) T, ‖b t‖ ≤ β') →
      ∀ t : Icc (0 : ℝ) T,
        ‖(bilDuhamel hc hc1 hν hT.le a b) t‖ ≤ C₀ / Real.sqrt lam * α * β' * Real.exp (lam * t)) ∧
    (∀ (T : ℝ) (hT : 0 < T) (a b : MPath c T) (lam α β' : ℝ), 0 < lam → 0 ≤ α → 0 ≤ β' →
      (∀ t : Icc (0 : ℝ) T, ‖a t‖ ≤ β') →
      (∀ t : Icc (0 : ℝ) T, ‖b t‖ ≤ α * Real.exp (lam * t)) →
      ∀ t : Icc (0 : ℝ) T,
        ‖(bilDuhamel hc hc1 hν hT.le a b) t‖ ≤ C₀ / Real.sqrt lam * α * β' * Real.exp (lam * t))

/-- **Leaf A** (additivity of the polarised Duhamel map in each argument): `bilDuhamel` is the
Bochner integral of `P₀ e^{ν(t-r)Δ} div (a(r) ⊗ b(r))` and `tensorH3Bilinear` is bilinear. -/
def BilDuhamelAdditive : Prop :=
  ∀ (ν c T : ℝ) (hν : 0 < ν) (hc : 0 < c) (hc1 : 1 ≤ c) (hT : 0 < T) (a a' b b' : MPath c T),
    bilDuhamel hc hc1 hν hT.le (a + a') b =
        bilDuhamel hc hc1 hν hT.le a b + bilDuhamel hc hc1 hν hT.le a' b ∧
      bilDuhamel hc hc1 hν hT.le a (b + b') =
        bilDuhamel hc hc1 hν hT.le a b + bilDuhamel hc hc1 hν hT.le a b'

/-- **Leaf D** (density of paths with a derivative path in `C([0,T], H³)`): every path is
uniformly approximated by a path having a `∂_j`-derivative path.  Proof: the elements `x ∈ H³`
with a weak `∂_j`-derivative `x' ∈ H³` are dense in `H³` (`Sob.W.cylinder_dense_smooth`,
`Sob.W.exists_seq_cylSmooth` of `Lib/SobolevC`: smooth compactly supported `x` have the smooth
derivative `∂_j x`); the compact set `u([0,T])` is covered by finitely many `η/2`-balls around
such `x_i`, and `v = Σ φ_i(t) x_i`, `v' = Σ φ_i(t) x_i'` for a continuous partition of unity `φ_i`
subordinate to `{t : ‖u(t) - x_i‖ < η/2}`. -/
def DerivDense : Prop :=
  ∀ (c T : ℝ), 0 < c → 0 < T → ∀ (j : Fin 2) (u : MPath c T) (η : ℝ), 0 < η →
    ∃ v v' : MPath c T, HasDerivPath c T j v v' ∧ ∀ t, ‖u t - v t‖ ≤ η

/-- **Leaf C** (closedness of derivative paths): if `a_m` has the derivative path `a_m'`,
`a_m → x` and `a_m' → d` in `C([0,T], H³)`, then `d` is a derivative path of `x`.  Proof: for
each `t`, `a_m(t) → x(t)` and `a_m'(t) → d(t)` in `H³`, hence in `L²`, and the identity
`∫ a_m ∂_jφ = -∫ a_m' φ` passes to the limit (`Sob.HasWeakDeriv` is the integrated-by-parts
identity against the test functions of `Sob.TestDomain`). -/
def DerivClosed : Prop :=
  ∀ (c T : ℝ) (j : Fin 2) (a a' : ℕ → MPath c T) (x d : MPath c T),
    (∀ m, HasDerivPath c T j (a m) (a' m)) → Tendsto a atTop (𝓝 x) → Tendsto a' atTop (𝓝 d) →
    HasDerivPath c T j x d

/-- **Existence of a derivative path of the mild solution.** -/
def MildDerivPathExists : Prop :=
  ∀ (ν c T : ℝ) (hν : 0 < ν) (hc : 0 < c) (hc1 : 1 ≤ c) (hT : 0 < T) (j : Fin 2)
    (s s' u : MPath c T), u = s + bilDuhamel hc hc1 hν hT.le u u → HasDerivPath c T j s s' →
    ∃ u' : MPath c T, HasDerivPath c T j u u'

/-! ### `BaseDerivative` from the existence of a derivative path -/

/-- **`BaseDerivative` from `BilDuhamelDerivative` and the existence of a derivative path.** -/
theorem baseDerivative_of (hP : BilDuhamelDerivative) (hE : MildDerivPathExists) :
    BaseDerivative := by
  intro ν c T hν hc hc1 hT j s s' u hu hs
  obtain ⟨u', hu'⟩ := hE ν c T hν hc hc1 hT j s s' u hu hs
  refine ⟨u', hu', ?_⟩
  have h1 := hP ν c T hν hc hc1 hT j u u' u u' hu' hu'
  have h2 : HasDerivPath c T j (s + bilDuhamel hc hc1 hν hT.le u u)
      (s' + (bilDuhamel hc hc1 hν hT.le u' u + bilDuhamel hc hc1 hν hT.le u u')) :=
    hs.add h1
  rw [← hu] at h2
  have h3 := hu'.unique h2
  calc u' = s' + (bilDuhamel hc hc1 hν hT.le u' u + bilDuhamel hc hc1 hν hT.le u u') := h3
    _ = s' + linDuhamel hc hc1 hν hT.le u u' := by
      unfold linDuhamel
      rw [add_comm (bilDuhamel hc hc1 hν hT.le u' u)]

/-! ### Existence of a derivative path by Picard iteration around `u` -/

set_option maxHeartbeats 1000000 in
/-- The abstract core: `B` additive in each argument with the product rule and the weighted
estimates, `u = s + B u u`, `s` having a derivative path, gives a derivative path of `u`. -/
theorem picard_core {c T : ℝ} [CompleteSpace (MPath c T)] (j : Fin 2)
    (B : MPath c T → MPath c T → MPath c T)
    (hBadd1 : ∀ a a' b, B (a + a') b = B a b + B a' b)
    (hBadd2 : ∀ a b b', B a (b + b') = B a b + B a b')
    (hBprod : ∀ a a' b b', HasDerivPath c T j a a' → HasDerivPath c T j b b' →
      HasDerivPath c T j (B a b) (B a' b + B a b'))
    (C₀ : ℝ) (hC₀ : 0 < C₀)
    (hWl : ∀ (a b : MPath c T) (lam α β' : ℝ), 0 < lam → 0 ≤ α → 0 ≤ β' →
      (∀ t : Icc (0 : ℝ) T, ‖a t‖ ≤ α * Real.exp (lam * t)) →
      (∀ t : Icc (0 : ℝ) T, ‖b t‖ ≤ β') →
      ∀ t : Icc (0 : ℝ) T, ‖(B a b) t‖ ≤ C₀ / Real.sqrt lam * α * β' * Real.exp (lam * t))
    (hWr : ∀ (a b : MPath c T) (lam α β' : ℝ), 0 < lam → 0 ≤ α → 0 ≤ β' →
      (∀ t : Icc (0 : ℝ) T, ‖a t‖ ≤ β') →
      (∀ t : Icc (0 : ℝ) T, ‖b t‖ ≤ α * Real.exp (lam * t)) →
      ∀ t : Icc (0 : ℝ) T, ‖(B a b) t‖ ≤ C₀ / Real.sqrt lam * α * β' * Real.exp (lam * t))
    (hD : ∀ (u : MPath c T) (η : ℝ), 0 < η →
      ∃ v v' : MPath c T, HasDerivPath c T j v v' ∧ ∀ t, ‖u t - v t‖ ≤ η)
    (hC : ∀ (a a' : ℕ → MPath c T) (x d : MPath c T),
      (∀ m, HasDerivPath c T j (a m) (a' m)) → Tendsto a atTop (𝓝 x) →
      Tendsto a' atTop (𝓝 d) → HasDerivPath c T j x d)
    (s s' u : MPath c T) (hu : u = s + B u u) (hs : HasDerivPath c T j s s') :
    ∃ u' : MPath c T, HasDerivPath c T j u u' := by
  -- constants
  set R : ℝ := ‖u‖ + 1 with hR
  have hR1 : 1 ≤ R := by have := norm_nonneg u; linarith
  have hR0 : 0 < R := by linarith
  set lam : ℝ := (4 * C₀ * R) ^ 2 + 1 with hlam
  have hlam0 : 0 < lam := by positivity
  have hsl0 : 0 < Real.sqrt lam := Real.sqrt_pos.2 hlam0
  have hsq : 4 * C₀ * R ≤ Real.sqrt lam := by
    have h1 : (4 * C₀ * R) ^ 2 ≤ lam := by rw [hlam]; linarith
    calc 4 * C₀ * R = Real.sqrt ((4 * C₀ * R) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt lam := Real.sqrt_le_sqrt h1
  set K : ℝ := C₀ / Real.sqrt lam with hK
  have hK0 : 0 < K := div_pos hC₀ hsl0
  have hKR : 2 * K * R ≤ 1 / 2 := by
    have h1 : K * Real.sqrt lam = C₀ := by rw [hK]; field_simp
    nlinarith [mul_le_mul_of_nonneg_left hsq hK0.le, hR0, hK0]
  set η0 : ℝ := Real.exp (-(lam * T)) with hη0
  have hη0pos : 0 < η0 := Real.exp_pos _
  have hexp1 : ∀ t : Icc (0 : ℝ) T, 1 ≤ Real.exp (lam * t) := fun t =>
    Real.one_le_exp (mul_nonneg hlam0.le t.2.1)
  have hexpT : ∀ t : Icc (0 : ℝ) T, Real.exp (lam * t) * η0 ≤ 1 := by
    intro t
    rw [hη0, ← Real.exp_add]
    apply Real.exp_le_one_iff.2
    have : (t : ℝ) ≤ T := t.2.2
    nlinarith
  have hexpT' : ∀ t : Icc (0 : ℝ) T, Real.exp (lam * t) ≤ Real.exp (lam * T) := fun t =>
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left t.2.2 hlam0.le)
  have hη0T : η0 * Real.exp (lam * T) = 1 := by
    rw [hη0, ← Real.exp_add]; simp
  -- the starting point
  obtain ⟨v0, v0', hv0, hv0u⟩ := hD u η0 hη0pos
  -- the Picard step on pairs
  let step : MPath c T × MPath c T → MPath c T × MPath c T := fun p =>
    (s + B p.1 p.1, s' + (B p.2 p.1 + B p.1 p.2))
  let seq : ℕ → MPath c T × MPath c T := fun m => step^[m] (v0, v0')
  have hseq0 : seq 0 = (v0, v0') := rfl
  have hseqS : ∀ m, seq (m + 1) = step (seq m) := fun m =>
    Function.iterate_succ_apply' step m (v0, v0')
  have hseq1 : ∀ m, (seq (m + 1)).1 = s + B (seq m).1 (seq m).1 := fun m => by rw [hseqS]
  have hseq2 : ∀ m, (seq (m + 1)).2 = s' + (B (seq m).2 (seq m).1 + B (seq m).1 (seq m).2) :=
    fun m => by rw [hseqS]
  -- (F1) derivative paths
  have F1 : ∀ m, HasDerivPath c T j (seq m).1 (seq m).2 := by
    intro m
    induction m with
    | zero => exact hv0
    | succ m ih =>
      rw [hseq1, hseq2]
      exact hs.add (hBprod _ _ _ _ ih ih)

  have hRu : ∀ t : Icc (0 : ℝ) T, ‖u t‖ ≤ R := fun t => by
    have := u.norm_coe_le_norm t
    rw [hR]; linarith
  -- a sup bound from a weighted closeness bound
  have hsupAux : ∀ (n : ℕ) (v : MPath c T),
      (∀ t : Icc (0 : ℝ) T, ‖v t - u t‖ ≤ (1 / 2) ^ n * η0 * Real.exp (lam * t)) →
      ∀ t : Icc (0 : ℝ) T, ‖v t‖ ≤ R := by
    intro n v hv t
    calc ‖v t‖ = ‖u t + (v t - u t)‖ := by rw [add_sub_cancel]
      _ ≤ ‖u t‖ + ‖v t - u t‖ := norm_add_le _ _
      _ ≤ ‖u‖ + 1 * 1 := by
        refine add_le_add (u.norm_coe_le_norm t) ?_
        calc ‖v t - u t‖ ≤ (1 / 2) ^ n * η0 * Real.exp (lam * t) := hv t
          _ = (1 / 2) ^ n * (Real.exp (lam * t) * η0) := by ring
          _ ≤ 1 * 1 := mul_le_mul (pow_le_one₀ (by norm_num) (by norm_num)) (hexpT t)
              (by positivity) zero_le_one
      _ ≤ R := by rw [hR]; linarith
  -- the algebraic identity for one Picard step
  have hdiff : ∀ v e : MPath c T, v = u + e → s + B v v - u = B u e + B e v := by
    intro v e hve
    subst hve
    have h1 : B (u + e) (u + e) = B u u + B u e + B e (u + e) := by
      rw [hBadd1 u e (u + e), hBadd2 u u e]
    rw [h1]
    have h2 : s + (B u u + B u e + B e (u + e)) - u =
        (s + B u u - u) + (B u e + B e (u + e)) := by abel
    rw [h2, ← hu]
    simp
  -- one Picard step contracts the weighted distance to `u`
  have stepClose : ∀ (n : ℕ) (v : MPath c T),
      (∀ t : Icc (0 : ℝ) T, ‖v t - u t‖ ≤ (1 / 2) ^ n * η0 * Real.exp (lam * t)) →
      ∀ t : Icc (0 : ℝ) T,
        ‖(s + B v v) t - u t‖ ≤ (1 / 2) ^ (n + 1) * η0 * Real.exp (lam * t) := by
    intro n v hv t
    have hvR := hsupAux n v hv
    have hfun : s + B v v - u = B u (v - u) + B (v - u) v := hdiff v (v - u) (by abel)
    have e : (s + B v v) t - u t = (B u (v - u)) t + (B (v - u) v) t := by
      have h := congrArg (fun f : MPath c T => f t) hfun
      simpa only [ContinuousMap.sub_apply, ContinuousMap.add_apply] using h
    have hvu : ∀ t : Icc (0 : ℝ) T,
        ‖(v - u) t‖ ≤ (1 / 2) ^ n * η0 * Real.exp (lam * t) := fun t => by
      rw [ContinuousMap.sub_apply]; exact hv t
    have hα : 0 ≤ (1 / 2 : ℝ) ^ n * η0 := by positivity
    have b1 := hWr u (v - u) lam ((1 / 2) ^ n * η0) R hlam0 hα hR0.le hRu hvu t
    have b2 := hWl (v - u) v lam ((1 / 2) ^ n * η0) R hlam0 hα hR0.le hvu hvR t
    have he : 0 ≤ Real.exp (lam * t) := (Real.exp_pos _).le
    have hkey : 2 * K * R * (((1 / 2) ^ n * η0) * Real.exp (lam * t)) ≤
        1 / 2 * (((1 / 2) ^ n * η0) * Real.exp (lam * t)) :=
      mul_le_mul_of_nonneg_right hKR (mul_nonneg hα he)
    rw [e]
    calc ‖(B u (v - u)) t + (B (v - u) v) t‖ ≤ ‖(B u (v - u)) t‖ + ‖(B (v - u) v) t‖ :=
          norm_add_le _ _
      _ ≤ K * ((1 / 2) ^ n * η0) * R * Real.exp (lam * t) +
          K * ((1 / 2) ^ n * η0) * R * Real.exp (lam * t) := add_le_add b1 b2
      _ = 2 * K * R * (((1 / 2) ^ n * η0) * Real.exp (lam * t)) := by ring
      _ ≤ 1 / 2 * (((1 / 2) ^ n * η0) * Real.exp (lam * t)) := hkey
      _ = (1 / 2) ^ (n + 1) * η0 * Real.exp (lam * t) := by ring
  -- (F2) closeness of the iterates to `u` in the weighted envelope
  have F2 : ∀ m : ℕ, ∀ t : Icc (0 : ℝ) T,
      ‖(seq m).1 t - u t‖ ≤ (1 / 2) ^ m * η0 * Real.exp (lam * t) := by
    intro m
    induction m with
    | zero =>
      intro t
      rw [hseq0]
      simp only [pow_zero, one_mul]
      calc ‖v0 t - u t‖ = ‖u t - v0 t‖ := norm_sub_rev _ _
        _ ≤ η0 := hv0u t
        _ = η0 * 1 := (mul_one _).symm
        _ ≤ η0 * Real.exp (lam * t) := mul_le_mul_of_nonneg_left (hexp1 t) hη0pos.le
    | succ m ih =>
      rw [hseq1]
      exact stepClose m _ ih
  -- (F3) sup bound for the iterates
  have F3 : ∀ m : ℕ, ∀ t : Icc (0 : ℝ) T, ‖(seq m).1 t‖ ≤ R := fun m => hsupAux m _ (F2 m)
  -- the derivative iterates: envelope bound
  set Γ : ℝ := max ‖v0'‖ (2 * ‖s'‖) with hΓ
  have hΓ0 : 0 ≤ Γ := le_trans (norm_nonneg _) (le_max_left _ _)
  have hΓs : ‖s'‖ ≤ Γ / 2 := by
    have := le_max_right ‖v0'‖ (2 * ‖s'‖)
    rw [← hΓ] at this
    linarith
  have stepDeriv : ∀ (v v' : MPath c T), (∀ t : Icc (0 : ℝ) T, ‖v t‖ ≤ R) →
      (∀ t : Icc (0 : ℝ) T, ‖v' t‖ ≤ Γ * Real.exp (lam * t)) →
      ∀ t : Icc (0 : ℝ) T, ‖(s' + (B v' v + B v v')) t‖ ≤ Γ * Real.exp (lam * t) := by
    intro v v' hv hv' t
    have b1 := hWl v' v lam Γ R hlam0 hΓ0 hR0.le hv' hv t
    have b2 := hWr v v' lam Γ R hlam0 hΓ0 hR0.le hv hv' t
    have he1 := hexp1 t
    have hkey : 2 * K * R * (Γ * Real.exp (lam * t)) ≤ 1 / 2 * (Γ * Real.exp (lam * t)) :=
      mul_le_mul_of_nonneg_right hKR (mul_nonneg hΓ0 (Real.exp_pos _).le)
    have hs't : ‖s' t‖ ≤ Γ / 2 := (s'.norm_coe_le_norm t).trans hΓs
    calc ‖(s' + (B v' v + B v v')) t‖ = ‖s' t + ((B v' v) t + (B v v') t)‖ := rfl
      _ ≤ ‖s' t‖ + (‖(B v' v) t‖ + ‖(B v v') t‖) :=
          (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
      _ ≤ Γ / 2 + (K * Γ * R * Real.exp (lam * t) + K * Γ * R * Real.exp (lam * t)) :=
          add_le_add hs't (add_le_add b1 b2)
      _ = Γ / 2 + 2 * K * R * (Γ * Real.exp (lam * t)) := by ring
      _ ≤ Γ / 2 * Real.exp (lam * t) + 1 / 2 * (Γ * Real.exp (lam * t)) := by
          refine add_le_add ?_ hkey
          nlinarith
      _ = Γ * Real.exp (lam * t) := by ring
  have F4 : ∀ m : ℕ, ∀ t : Icc (0 : ℝ) T, ‖(seq m).2 t‖ ≤ Γ * Real.exp (lam * t) := by
    intro m
    induction m with
    | zero =>
      intro t
      rw [hseq0]
      calc ‖v0' t‖ ≤ ‖v0'‖ := v0'.norm_coe_le_norm t
        _ ≤ Γ := le_max_left _ _
        _ = Γ * 1 := (mul_one _).symm
        _ ≤ Γ * Real.exp (lam * t) := mul_le_mul_of_nonneg_left (hexp1 t) hΓ0
    | succ m ih =>
      rw [hseq2]
      exact stepDeriv _ _ (F3 m) ih
  -- the differences of the derivative iterates
  set C₁ : ℝ := 2 * K * Γ with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  set D : ℝ := max (2 * Γ) (8 * C₁) with hD'
  have hD0 : 0 ≤ D := le_trans (by positivity) (le_max_left _ _)
  have hD1 : 2 * Γ ≤ D := le_max_left _ _
  have hD2 : 8 * C₁ ≤ D := le_max_right _ _
  have stepDiff : ∀ (n : ℕ) (v v' w w' : MPath c T), (∀ t : Icc (0 : ℝ) T, ‖v t‖ ≤ R) →
      (∀ t : Icc (0 : ℝ) T, ‖w t‖ ≤ R) →
      (∀ t : Icc (0 : ℝ) T, ‖v' t‖ ≤ Γ * Real.exp (lam * t)) →
      (∀ t : Icc (0 : ℝ) T, ‖w' t‖ ≤ Γ * Real.exp (lam * t)) →
      (∀ t : Icc (0 : ℝ) T, ‖(w - v) t‖ ≤ 2 * (1 / 2) ^ n) →
      (∀ t : Icc (0 : ℝ) T, ‖(w' - v') t‖ ≤ D * (3 / 4) ^ n * Real.exp (lam * t)) →
      ∀ t : Icc (0 : ℝ) T,
        ‖(B w' w + B w w' - (B v' v + B v v')) t‖ ≤ D * (3 / 4) ^ (n + 1) * Real.exp (lam * t) := by
    intro n v v' w w' hv hw hv' hw' hδ hd t
    obtain ⟨δ, rfl⟩ : ∃ δ, w = v + δ := ⟨w - v, by abel⟩
    obtain ⟨d, rfl⟩ : ∃ d, w' = v' + d := ⟨w' - v', by abel⟩
    simp only [add_sub_cancel_left] at hδ hd
    have hid : B (v' + d) (v + δ) + B (v + δ) (v' + d) - (B v' v + B v v') =
        B v' δ + B d (v + δ) + B v d + B δ (v' + d) := by
      rw [hBadd1 v' d (v + δ), hBadd2 v' v δ, hBadd1 v δ (v' + d), hBadd2 v v' d]
      abel
    have hα : 0 ≤ D * (3 / 4 : ℝ) ^ n := by positivity
    have hε : 0 ≤ 2 * (1 / 2 : ℝ) ^ n := by positivity
    have t1 := hWl v' δ lam Γ (2 * (1 / 2) ^ n) hlam0 hΓ0 hε hv' hδ t
    have t2 := hWl d (v + δ) lam (D * (3 / 4) ^ n) R hlam0 hα hR0.le hd hw t
    have t3 := hWr v d lam (D * (3 / 4) ^ n) R hlam0 hα hR0.le hv hd t
    have t4 := hWr δ (v' + d) lam Γ (2 * (1 / 2) ^ n) hlam0 hΓ0 hε hδ hw' t
    have he : 0 ≤ Real.exp (lam * t) := (Real.exp_pos _).le
    have hkey : 2 * K * R * ((D * (3 / 4) ^ n) * Real.exp (lam * t)) ≤
        1 / 2 * ((D * (3 / 4) ^ n) * Real.exp (lam * t)) :=
      mul_le_mul_of_nonneg_right hKR (mul_nonneg hα he)
    have hpow : (1 / 2 : ℝ) ^ n ≤ (3 / 4) ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
    have hpow0 : 0 ≤ (3 / 4 : ℝ) ^ n := by positivity
    have hsmall : 4 * K * Γ * (1 / 2 : ℝ) ^ n ≤ D / 4 * (3 / 4) ^ n := by
      have h1 : 4 * K * Γ = 2 * C₁ := by rw [hC₁]; ring
      rw [h1]
      have h2 : 2 * C₁ ≤ D / 4 := by linarith
      calc 2 * C₁ * (1 / 2 : ℝ) ^ n ≤ 2 * C₁ * (3 / 4) ^ n :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
        _ ≤ D / 4 * (3 / 4) ^ n := mul_le_mul_of_nonneg_right h2 hpow0
    rw [hid]
    calc ‖(B v' δ + B d (v + δ) + B v d + B δ (v' + d)) t‖
        = ‖(B v' δ) t + (B d (v + δ)) t + (B v d) t + (B δ (v' + d)) t‖ := rfl
      _ ≤ ‖(B v' δ) t‖ + ‖(B d (v + δ)) t‖ + ‖(B v d) t‖ + ‖(B δ (v' + d)) t‖ := by
          refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
            (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
      _ ≤ K * Γ * (2 * (1 / 2) ^ n) * Real.exp (lam * t) +
          K * (D * (3 / 4) ^ n) * R * Real.exp (lam * t) +
          K * (D * (3 / 4) ^ n) * R * Real.exp (lam * t) +
          K * Γ * (2 * (1 / 2) ^ n) * Real.exp (lam * t) := by
          refine add_le_add (add_le_add (add_le_add t1 t2) t3) t4
      _ = (4 * K * Γ * (1 / 2 : ℝ) ^ n) * Real.exp (lam * t) +
          2 * K * R * ((D * (3 / 4) ^ n) * Real.exp (lam * t)) := by ring
      _ ≤ (D / 4 * (3 / 4) ^ n) * Real.exp (lam * t) +
          1 / 2 * ((D * (3 / 4) ^ n) * Real.exp (lam * t)) := by
          refine add_le_add (mul_le_mul_of_nonneg_right hsmall he) hkey
      _ = D * (3 / 4) ^ (n + 1) * Real.exp (lam * t) - D / 4 * (3 / 4) ^ n * Real.exp (lam * t) +
          (D / 4 * (3 / 4) ^ n) * Real.exp (lam * t) := by ring
      _ = D * (3 / 4) ^ (n + 1) * Real.exp (lam * t) := by ring
  have hstep2 : ∀ m : ℕ, (seq (m + 1 + 1)).2 - (seq (m + 1)).2 =
      (B (seq (m + 1)).2 (seq (m + 1)).1 + B (seq (m + 1)).1 (seq (m + 1)).2) -
        (B (seq m).2 (seq m).1 + B (seq m).1 (seq m).2) := by
    intro m
    have h1 := hseq2 (m + 1)
    have h2 := hseq2 m
    calc (seq (m + 1 + 1)).2 - (seq (m + 1)).2
        = (s' + (B (seq (m + 1)).2 (seq (m + 1)).1 + B (seq (m + 1)).1 (seq (m + 1)).2)) -
          (s' + (B (seq m).2 (seq m).1 + B (seq m).1 (seq m).2)) := by rw [← h1, ← h2]
      _ = _ := add_sub_add_left_eq_sub _ _ _
  have F5 : ∀ m : ℕ, ∀ t : Icc (0 : ℝ) T,
      ‖((seq (m + 1)).2 - (seq m).2) t‖ ≤ D * (3 / 4) ^ m * Real.exp (lam * t) := by
    intro m
    induction m with
    | zero =>
      intro t
      calc ‖((seq (0 + 1)).2 - (seq 0).2) t‖ = ‖(seq (0 + 1)).2 t - (seq 0).2 t‖ := rfl
        _ ≤ ‖(seq (0 + 1)).2 t‖ + ‖(seq 0).2 t‖ := norm_sub_le _ _
        _ ≤ Γ * Real.exp (lam * t) + Γ * Real.exp (lam * t) := add_le_add (F4 _ t) (F4 _ t)
        _ = 2 * Γ * Real.exp (lam * t) := by ring
        _ ≤ D * (3 / 4) ^ 0 * Real.exp (lam * t) := by
          rw [pow_zero, mul_one]
          exact mul_le_mul_of_nonneg_right hD1 (Real.exp_pos _).le
    | succ m ih =>
      intro t
      have hδ : ∀ t : Icc (0 : ℝ) T, ‖((seq (m + 1)).1 - (seq m).1) t‖ ≤ 2 * (1 / 2) ^ m := by
        intro t
        have h1 := F2 (m + 1) t
        have h2 := F2 m t
        have he1 := hexpT t
        have hp : (1 / 2 : ℝ) ^ (m + 1) ≤ (1 / 2) ^ m := by
          apply pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ m)
        calc ‖((seq (m + 1)).1 - (seq m).1) t‖ = ‖((seq (m + 1)).1 t - u t) - ((seq m).1 t - u t)‖ := by
              congr 1; simp only [ContinuousMap.sub_apply]; abel
          _ ≤ ‖(seq (m + 1)).1 t - u t‖ + ‖(seq m).1 t - u t‖ := norm_sub_le _ _
          _ ≤ (1 / 2) ^ (m + 1) * η0 * Real.exp (lam * t) +
              (1 / 2) ^ m * η0 * Real.exp (lam * t) := add_le_add h1 h2
          _ = ((1 / 2) ^ (m + 1) + (1 / 2) ^ m) * (Real.exp (lam * t) * η0) := by ring
          _ ≤ (2 * (1 / 2) ^ m) * 1 := by
              refine mul_le_mul ?_ he1 (by positivity) (by positivity)
              have : (1 / 2 : ℝ) ^ (m + 1) = 1 / 2 * (1 / 2) ^ m := by ring
              rw [this]; nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) m]
          _ = 2 * (1 / 2) ^ m := mul_one _
      have key := stepDiff m (seq m).1 (seq m).2 (seq (m + 1)).1 (seq (m + 1)).2 (F3 m) (F3 (m + 1))
        (F4 m) (F4 (m + 1)) hδ ih t
      rw [← hstep2 m] at key
      exact key
  -- the derivative iterates are Cauchy
  have hdist : ∀ m : ℕ, dist (seq m).2 (seq (m + 1)).2 ≤ (D * Real.exp (lam * T)) * (3 / 4) ^ m := by
    intro m
    rw [dist_eq_norm, norm_sub_rev]
    refine (ContinuousMap.norm_le _ (by positivity)).2 (fun t => ?_)
    calc ‖((seq (m + 1)).2 - (seq m).2) t‖ ≤ D * (3 / 4) ^ m * Real.exp (lam * t) := F5 m t
      _ ≤ D * (3 / 4) ^ m * Real.exp (lam * T) :=
          mul_le_mul_of_nonneg_left (hexpT' t) (by positivity)
      _ = (D * Real.exp (lam * T)) * (3 / 4) ^ m := by ring
  have hcau : CauchySeq (fun m => (seq m).2) :=
    cauchySeq_of_le_geometric (3 / 4) (D * Real.exp (lam * T)) (by norm_num) hdist
  obtain ⟨d, hd⟩ := cauchySeq_tendsto_of_complete hcau
  -- the iterates converge to `u`
  have ht1 : Tendsto (fun m => (seq m).1) atTop (𝓝 u) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun m => norm_nonneg _) (fun m => ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
    refine (ContinuousMap.norm_le _ (by positivity)).2 (fun t => ?_)
    calc ‖((seq m).1 - u) t‖ = ‖(seq m).1 t - u t‖ := rfl
      _ ≤ (1 / 2) ^ m * η0 * Real.exp (lam * t) := F2 m t
      _ ≤ (1 / 2) ^ m * η0 * Real.exp (lam * T) :=
          mul_le_mul_of_nonneg_left (hexpT' t) (by positivity)
      _ = (1 / 2) ^ m := by rw [mul_assoc, hη0T, mul_one]
  exact ⟨d, hC (fun m => (seq m).1) (fun m => (seq m).2) u d F1 ht1 hd⟩

/-- **Existence of a derivative path of the mild solution** from the four leaves and the product
rule. -/
theorem mildDerivPathExists_of (hP : BilDuhamelDerivative) (hA : BilDuhamelAdditive)
    (hW : BilWeightedEstimate) (hD : DerivDense) (hC : DerivClosed) : MildDerivPathExists := by
  intro ν c T hν hc hc1 hT j s s' u hu hs
  obtain ⟨C₀, hC₀, hWl, hWr⟩ := hW ν c hν hc hc1
  exact picard_core j (fun a b => bilDuhamel hc hc1 hν hT.le a b)
    (fun a a' b => (hA ν c T hν hc hc1 hT a a' b b).1)
    (fun a b b' => (hA ν c T hν hc hc1 hT a a b b').2)
    (fun a a' b b' ha hb => hP ν c T hν hc hc1 hT j a a' b b' ha hb)
    C₀ hC₀ (hWl T hT) (hWr T hT)
    (fun u η hη => hD c T hc hT j u η hη)
    (fun a a' x d h1 h2 h3 => hC c T j a a' x d h1 h2 h3)
    s s' u hu hs

/-- **`BaseDerivative` from the product rule and the four leaves.** -/
theorem baseDerivative_of_leaves (hP : BilDuhamelDerivative) (hA : BilDuhamelAdditive)
    (hW : BilWeightedEstimate) (hD : DerivDense) (hC : DerivClosed) : BaseDerivative :=
  baseDerivative_of hP (mildDerivPathExists_of hP hA hW hD hC)

end UnforcedLeray.Short.PartI
