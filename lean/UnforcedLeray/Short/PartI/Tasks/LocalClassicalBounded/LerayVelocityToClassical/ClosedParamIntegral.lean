import UnforcedLeray.Short.PartI.Sub.T02_1_5

/-!
# Part I, task `PartI:T02/1/5`, leaf 1: a parametric integral over a closed parameter set

Source of record: `the November 2 reference manuscript`, lines 261-288 (the smooth
pressure up to `s = 0`).  Target: `ClosedParamIntegralSmooth` (`Short/PartI/Sub/T02_1_5.lean`).

Mathematics.  Let `S` be a closed convex set with unique differentiation in a finite-dimensional
normed space `X`, and let `G : X → ℝ → E` be `C^n` on `S × [0,1]`.  Then `x ↦ ∫₀¹ G x t dt` is `C^n`
on `S`.  The order-`0` case is uniform continuity on compact sets.  The first-order step is
`hasFDerivWithinAt_integral`: the derivative of the integral is the integral of the derivatives,
controlled by the mean value inequality on `S ∩ ball x r` and the uniform continuity of the
derivative on `(S ∩ closedBall x 1) × [0,1]`.  The induction then applies the hypothesis to the
continuous-linear-map-valued integrand.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)

namespace ClosedParamIntegral

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]

/-- Near `x ∈ S`, the function `Φ` is uniformly close to `Φ x` on `[0,1]`. -/
theorem uniform_close {S : Set X} (hS : IsClosed S) {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {Φ : X → ℝ → E}
    (hΦ : ContinuousOn (fun p : X × ℝ => Φ p.1 p.2) (S ×ˢ Icc (0 : ℝ) 1))
    {x : X} (hx : x ∈ S) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ z ∈ S, dist z x < r → ∀ t ∈ Icc (0 : ℝ) 1, dist (Φ z t) (Φ x t) < ε := by
  have hK : IsCompact ((Metric.closedBall x 1 ∩ S) ×ˢ Icc (0 : ℝ) 1) :=
    ((isCompact_closedBall x 1).inter_right hS).prod isCompact_Icc
  have hKsub : (Metric.closedBall x 1 ∩ S) ×ˢ Icc (0 : ℝ) 1 ⊆ S ×ˢ Icc (0 : ℝ) 1 :=
    Set.prod_mono inter_subset_right subset_rfl
  have hcont : ContinuousOn (fun p : X × ℝ => Φ p.1 p.2)
      ((Metric.closedBall x 1 ∩ S) ×ˢ Icc (0 : ℝ) 1) :=
    hΦ.mono hKsub
  obtain ⟨δ, hδ, hδK⟩ :=
    Metric.uniformContinuousOn_iff.mp (hK.uniformContinuousOn_of_continuous hcont) ε hε
  refine ⟨min δ 1, lt_min hδ one_pos, fun z hz hdist t ht => ?_⟩
  have hzK : z ∈ Metric.closedBall x 1 ∩ S :=
    ⟨Metric.mem_closedBall.mpr (hdist.le.trans (min_le_right _ _)), hz⟩
  have hxK : x ∈ Metric.closedBall x 1 ∩ S :=
    ⟨Metric.mem_closedBall_self zero_le_one, hx⟩
  have hdist_eq : dist ((z, t) : X × ℝ) (x, t) = dist z x := by
    rw [Prod.dist_eq]
    simp
  have hdist' : dist ((z, t) : X × ℝ) (x, t) < δ := by
    rw [hdist_eq]
    exact lt_of_lt_of_le hdist (min_le_left _ _)
  exact hδK (z, t) ⟨hzK, ht⟩ (x, t) ⟨hxK, ht⟩ hdist'

/-- The restriction of a continuous function on `S × [0,1]` to a slice `{z} × [0,1]`. -/
theorem slice_continuousOn {S : Set X} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : X → ℝ → E} (hG : ContinuousOn (fun p : X × ℝ => G p.1 p.2) (S ×ˢ Icc (0 : ℝ) 1))
    {z : X} (hz : z ∈ S) : ContinuousOn (fun t : ℝ => G z t) (Icc (0 : ℝ) 1) := by
  have h : ContinuousOn (fun t : ℝ => ((z, t) : X × ℝ)) (Icc (0 : ℝ) 1) :=
    (continuous_const.prodMk continuous_id).continuousOn
  exact hG.comp h (fun t ht => ⟨hz, ht⟩)

/-- Interval integrability of a slice of a continuous function on `S × [0,1]`. -/
theorem slice_intervalIntegrable {S : Set X} {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {G : X → ℝ → E}
    (hG : ContinuousOn (fun p : X × ℝ => G p.1 p.2) (S ×ˢ Icc (0 : ℝ) 1))
    {z : X} (hz : z ∈ S) : IntervalIntegrable (fun t : ℝ => G z t) volume 0 1 :=
  ContinuousOn.intervalIntegrable (by
    rw [uIcc_of_le zero_le_one]
    exact slice_continuousOn hG hz)

/-- Order zero: the integral of a function continuous on `S × [0,1]` is continuous on `S`. -/
theorem continuousOn_integral {S : Set X} (hS : IsClosed S) {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {G : X → ℝ → E}
    (hG : ContinuousOn (fun p : X × ℝ => G p.1 p.2) (S ×ˢ Icc (0 : ℝ) 1)) :
    ContinuousOn (fun w => ∫ t in (0 : ℝ)..1, G w t) S := by
  intro x hx
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨r, hr, hcl⟩ := uniform_close (Φ := G) hS hG hx (half_pos hε)
  refine ⟨r, hr, fun {z} hz hdist => ?_⟩
  have hz' := hcl z hz hdist
  have hsub : ∫ t in (0 : ℝ)..1, (G z t - G x t)
      = (∫ t in (0 : ℝ)..1, G z t) - ∫ t in (0 : ℝ)..1, G x t :=
    intervalIntegral.integral_sub (slice_intervalIntegrable hG hz)
      (slice_intervalIntegrable hG hx)
  show dist (∫ t in (0 : ℝ)..1, G z t) (∫ t in (0 : ℝ)..1, G x t) < ε
  rw [dist_eq_norm, ← hsub]
  have hb : ‖∫ t in (0 : ℝ)..1, (G z t - G x t)‖ ≤ ε / 2 * |(1 : ℝ) - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (fun t ht => by
      rw [uIoc_of_le zero_le_one] at ht
      show ‖G z t - G x t‖ ≤ ε / 2
      rw [← dist_eq_norm]
      exact (hz' t ⟨ht.1.le, ht.2⟩).le)
  rw [sub_zero, abs_one, mul_one] at hb
  linarith

/-- Slice of the derivative: for `z ∈ S`, `t ∈ [0,1]`, the `w`-derivative of `G · t` at `z` is the
restriction of the joint derivative of `G` to the slice. -/
theorem hasFDerivWithinAt_slice {S : Set X} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : X → ℝ → E} (hG : ContDiffOn ℝ 1 (fun p : X × ℝ => G p.1 p.2) (S ×ˢ Icc (0 : ℝ) 1))
    {z : X} (hz : z ∈ S) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasFDerivWithinAt (fun w => G w t)
      ((fderivWithin ℝ (fun p : X × ℝ => G p.1 p.2) (S ×ˢ Icc (0 : ℝ) 1) (z, t)).comp
        (ContinuousLinearMap.inl ℝ X ℝ)) S z := by
  have hFd : DifferentiableWithinAt ℝ (fun p : X × ℝ => G p.1 p.2) (S ×ˢ Icc (0 : ℝ) 1) (z, t) :=
    hG.differentiableOn one_ne_zero (z, t) ⟨hz, ht⟩
  have hinl : HasFDerivWithinAt (fun w : X => (w, t)) (ContinuousLinearMap.inl ℝ X ℝ) S z :=
    (hasFDerivAt_prodMk_left z t).hasFDerivWithinAt
  have hmaps : MapsTo (fun w : X => (w, t)) S (S ×ˢ Icc (0 : ℝ) 1) :=
    fun w hw => ⟨hw, ht⟩
  exact hFd.hasFDerivWithinAt.comp z hinl hmaps

/-- The same slice derivative, as an equation of continuous linear maps. -/
theorem fderivWithin_slice_eq {S : Set X} (hU : UniqueDiffOn ℝ S) {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : X → ℝ → E} (hG : ContDiffOn ℝ 1 (fun p : X × ℝ => G p.1 p.2) (S ×ˢ Icc (0 : ℝ) 1))
    {z : X} (hz : z ∈ S) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    fderivWithin ℝ (fun w => G w t) S z =
      (fderivWithin ℝ (fun p : X × ℝ => G p.1 p.2) (S ×ˢ Icc (0 : ℝ) 1) (z, t)).comp
        (ContinuousLinearMap.inl ℝ X ℝ) :=
  (hasFDerivWithinAt_slice hG hz ht).fderivWithin (hU z hz)

/-- Restriction of a derivative on `X × ℝ` to the slice `X × {t}`, as a continuous linear map. -/
def sliceL (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (X × ℝ →L[ℝ] E) →L[ℝ] (X →L[ℝ] E) :=
  (ContinuousLinearMap.compL ℝ X (X × ℝ) E).flip (ContinuousLinearMap.inl ℝ X ℝ)

theorem sliceL_apply {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : X × ℝ →L[ℝ] E) :
    sliceL E L = L.comp (ContinuousLinearMap.inl ℝ X ℝ) := by
  simp [sliceL]

/-- **First order.** The integral of a `C^1` family on `S × [0,1]` has the integrated
derivative as its derivative within `S`. -/
theorem hasFDerivWithinAt_integral {S : Set X} (hS : IsClosed S) (hconv : Convex ℝ S)
    (hU : UniqueDiffOn ℝ S) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {G : X → ℝ → E}
    (hG : ContDiffOn ℝ 1 (fun p : X × ℝ => G p.1 p.2) (S ×ˢ Icc (0 : ℝ) 1))
    {x : X} (hx : x ∈ S) :
    HasFDerivWithinAt (fun w => ∫ t in (0 : ℝ)..1, G w t)
      (∫ t in (0 : ℝ)..1, fderivWithin ℝ (fun w => G w t) S x) S x := by
  have hU' : UniqueDiffOn ℝ (S ×ˢ Icc (0 : ℝ) 1) := hU.prod (uniqueDiffOn_Icc one_pos)
  have hGc : ContinuousOn (fun p : X × ℝ => G p.1 p.2) (S ×ˢ Icc (0 : ℝ) 1) :=
    hG.continuousOn
  -- the slice derivative is jointly continuous on `S × [0,1]`
  have hDcont : ContinuousOn (fun p : X × ℝ => fderivWithin ℝ (fun w => G w p.2) S p.1)
      (S ×ˢ Icc (0 : ℝ) 1) := by
    have hL : ContinuousOn (fderivWithin ℝ (fun p : X × ℝ => G p.1 p.2) (S ×ˢ Icc (0 : ℝ) 1))
        (S ×ˢ Icc (0 : ℝ) 1) := hG.continuousOn_fderivWithin hU' le_rfl
    have hc : ContinuousOn (fun p : X × ℝ => sliceL (X := X) E
        (fderivWithin ℝ (fun q : X × ℝ => G q.1 q.2) (S ×ˢ Icc (0 : ℝ) 1) p))
        (S ×ˢ Icc (0 : ℝ) 1) :=
      (sliceL (X := X) E).continuous.comp_continuousOn hL
    refine hc.congr ?_
    rintro ⟨z, t⟩ ⟨hz, ht⟩
    dsimp only
    rw [sliceL_apply]
    exact fderivWithin_slice_eq hU hG hz ht
  -- the derivative of each slice
  have hslice : ∀ z ∈ S, ∀ t ∈ Icc (0 : ℝ) 1,
      HasFDerivWithinAt (fun w => G w t) (fderivWithin ℝ (fun w => G w t) S z) S z := by
    intro z hz t ht
    exact (hasFDerivWithinAt_slice hG hz ht).differentiableWithinAt.hasFDerivWithinAt
  -- the integrand of the derivative is integrable in `t`
  have hDt : ContinuousOn (fun t : ℝ => fderivWithin ℝ (fun w => G w t) S x)
      (Icc (0 : ℝ) 1) :=
    slice_continuousOn (G := fun z t => fderivWithin ℝ (fun w => G w t) S z) hDcont hx
  have hDint : IntervalIntegrable (fun t : ℝ => fderivWithin ℝ (fun w => G w t) S x) volume 0 1 :=
    ContinuousOn.intervalIntegrable (by
      rw [uIcc_of_le zero_le_one]
      exact hDt)
  rw [hasFDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨r, hr, hD⟩ :=
    uniform_close (Φ := fun z t => fderivWithin ℝ (fun w => G w t) S z) hS hDcont hx hc
  have hball : ∀ᶠ y in 𝓝 x, y ∈ Metric.ball x r := Metric.ball_mem_nhds x hr
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds hball, self_mem_nhdsWithin]
    with y hyr hyS
  have hyr' : dist y x < r := Metric.mem_ball.mp hyr
  have hGy : IntervalIntegrable (fun t : ℝ => G y t) volume 0 1 :=
    slice_intervalIntegrable hGc hyS
  have hGx : IntervalIntegrable (fun t : ℝ => G x t) volume 0 1 :=
    slice_intervalIntegrable hGc hx
  have hDv : IntervalIntegrable
      (fun t : ℝ => fderivWithin ℝ (fun w => G w t) S x (y - x)) volume 0 1 :=
    ContinuousOn.intervalIntegrable (by
      rw [uIcc_of_le zero_le_one]
      exact hDt.clm_apply continuousOn_const)
  have e2 : (∫ t in (0 : ℝ)..1, fderivWithin ℝ (fun w => G w t) S x) (y - x)
      = ∫ t in (0 : ℝ)..1, fderivWithin ℝ (fun w => G w t) S x (y - x) :=
    ((ContinuousLinearMap.apply ℝ E (y - x)).intervalIntegral_comp_comm hDint).symm
  -- the mean value estimate, for each parameter `t`
  have hmv : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖(G y t - G x t) - fderivWithin ℝ (fun w => G w t) S x (y - x)‖ ≤ c * ‖y - x‖ := by
    intro t ht
    have hf : ∀ z ∈ S ∩ Metric.ball x r,
        HasFDerivWithinAt (fun w => G w t - fderivWithin ℝ (fun w => G w t) S x w)
          (fderivWithin ℝ (fun w => G w t) S z - fderivWithin ℝ (fun w => G w t) S x)
          (S ∩ Metric.ball x r) z := by
      intro z hz
      exact ((hslice z hz.1 t ht).mono inter_subset_left).sub
        (fderivWithin ℝ (fun w => G w t) S x).hasFDerivAt.hasFDerivWithinAt
    have hb : ∀ z ∈ S ∩ Metric.ball x r,
        ‖fderivWithin ℝ (fun w => G w t) S z - fderivWithin ℝ (fun w => G w t) S x‖ ≤ c := by
      intro z hz
      rw [← dist_eq_norm]
      exact (hD z hz.1 (Metric.mem_ball.mp hz.2) t ht).le
    have hs : Convex ℝ (S ∩ Metric.ball x r) := hconv.inter (convex_ball x r)
    have key := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hf hb hs
      ⟨hx, Metric.mem_ball_self hr⟩ ⟨hyS, hyr⟩
    have e : (G y t - G x t) - fderivWithin ℝ (fun w => G w t) S x (y - x)
        = (G y t - fderivWithin ℝ (fun w => G w t) S x y)
          - (G x t - fderivWithin ℝ (fun w => G w t) S x x) := by
      rw [map_sub]
      abel
    rw [e]
    exact key
  -- integrate
  have hsplit : (∫ t in (0 : ℝ)..1, G y t) - (∫ t in (0 : ℝ)..1, G x t)
      - (∫ t in (0 : ℝ)..1, fderivWithin ℝ (fun w => G w t) S x) (y - x)
      = ∫ t in (0 : ℝ)..1, ((G y t - G x t)
          - fderivWithin ℝ (fun w => G w t) S x (y - x)) := by
    rw [e2, intervalIntegral.integral_sub (hGy.sub hGx) hDv,
      intervalIntegral.integral_sub hGy hGx]
  show ‖(∫ t in (0 : ℝ)..1, G y t) - (∫ t in (0 : ℝ)..1, G x t)
      - (∫ t in (0 : ℝ)..1, fderivWithin ℝ (fun w => G w t) S x) (y - x)‖ ≤ c * ‖y - x‖
  rw [hsplit]
  have hb : ‖∫ t in (0 : ℝ)..1, ((G y t - G x t)
      - fderivWithin ℝ (fun w => G w t) S x (y - x))‖ ≤ c * ‖y - x‖ * |(1 : ℝ) - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (fun t ht => by
      rw [uIoc_of_le zero_le_one] at ht
      exact hmv t ⟨ht.1.le, ht.2⟩)
  rw [sub_zero, abs_one, mul_one] at hb
  exact hb

/-- **Induction.** For a closed convex set with unique differentiation and a `C^n` family on
`S × [0,1]`, the parametric integral is `C^n` on `S`. -/
theorem contDiffOn_integral_closed {S : Set X} (hS : IsClosed S) (hconv : Convex ℝ S)
    (hU : UniqueDiffOn ℝ S) (n : ℕ) :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (G : X → ℝ → E),
      ContDiffOn ℝ (n : ℕ∞ω) (fun p : X × ℝ => G p.1 p.2) (S ×ˢ Icc (0 : ℝ) 1) →
      ContDiffOn ℝ (n : ℕ∞ω) (fun w => ∫ t in (0 : ℝ)..1, G w t) S := by
  induction n with
  | zero =>
    intro E _ _ _ G hG
    simp only [Nat.cast_zero, contDiffOn_zero] at hG ⊢
    exact continuousOn_integral hS hG
  | succ n ih =>
    intro E _ _ _ G hG
    push_cast at hG ⊢
    have hU' : UniqueDiffOn ℝ (S ×ˢ Icc (0 : ℝ) 1) := hU.prod (uniqueDiffOn_Icc one_pos)
    obtain ⟨-, -, hLs⟩ := (contDiffOn_succ_iff_fderivWithin hU').mp hG
    have hG1 : ContDiffOn ℝ 1 (fun p : X × ℝ => G p.1 p.2) (S ×ˢ Icc (0 : ℝ) 1) :=
      hG.of_le (by exact_mod_cast Nat.le_add_left 1 n)
    have hH : ∀ w ∈ S, HasFDerivWithinAt (fun v => ∫ t in (0 : ℝ)..1, G v t)
        (∫ t in (0 : ℝ)..1, fderivWithin ℝ (fun v' => G v' t) S w) S w :=
      fun w hw => hasFDerivWithinAt_integral hS hconv hU hG1 hw
    have hHdiff : DifferentiableOn ℝ (fun v => ∫ t in (0 : ℝ)..1, G v t) S :=
      fun w hw => (hH w hw).differentiableWithinAt
    have hfd : ∀ w ∈ S, fderivWithin ℝ (fun v => ∫ t in (0 : ℝ)..1, G v t) S w
        = ∫ t in (0 : ℝ)..1, fderivWithin ℝ (fun v' => G v' t) S w :=
      fun w hw => (hH w hw).fderivWithin (hU w hw)
    have hsl : ContDiff ℝ (n : ℕ∞ω) (sliceL (X := X) E) :=
      ContinuousLinearMap.contDiff (sliceL (X := X) E)
    have hLs' : ContDiffOn ℝ (n : ℕ∞ω) (fun p : X × ℝ => sliceL (X := X) E
        (fderivWithin ℝ (fun q : X × ℝ => G q.1 q.2) (S ×ˢ Icc (0 : ℝ) 1) p))
        (S ×ˢ Icc (0 : ℝ) 1) :=
      hsl.comp_contDiffOn hLs
    have hD : ContDiffOn ℝ (n : ℕ∞ω) (fun p : X × ℝ => fderivWithin ℝ (fun v => G v p.2) S p.1)
        (S ×ˢ Icc (0 : ℝ) 1) :=
      hLs'.congr (fun p hp => by
        show fderivWithin ℝ (fun v => G v p.2) S p.1 = sliceL (X := X) E
          (fderivWithin ℝ (fun q : X × ℝ => G q.1 q.2) (S ×ˢ Icc (0 : ℝ) 1) p)
        rw [sliceL_apply]
        exact fderivWithin_slice_eq hU hG1 hp.1 hp.2)
    have hI := ih (X →L[ℝ] E) (fun z t => fderivWithin ℝ (fun v => G v t) S z) hD
    refine (contDiffOn_succ_iff_fderivWithin hU).mpr
      ⟨hHdiff, fun h => absurd h (by simp), ?_⟩
    exact hI.congr (fun w hw => hfd w hw)

end ClosedParamIntegral

open ClosedParamIntegral in
/-- **Leaf 1 (proved).** A parametric integral over `[0,T] × ℝ²`-type closed parameter set with a
smooth integrand on `S × [0,1]` is smooth on `S`. -/
theorem closedParamIntegralSmooth : ClosedParamIntegralSmooth := by
  intro T hT G hG
  have hS : IsClosed (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) := isClosed_Icc.prod isClosed_univ
  have hconv : Convex ℝ (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
    (convex_Icc 0 T).prod convex_univ
  have hU : UniqueDiffOn ℝ (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
    (uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ
  refine contDiffOn_infty.mpr fun n => ?_
  exact contDiffOn_integral_closed hS hconv hU n ℝ G (hG.of_le (by exact_mod_cast le_top))

end UnforcedLeray.Short.PartI
