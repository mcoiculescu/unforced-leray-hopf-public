import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.Split

/-!
# Part II-a, task `PartII-a:N02/5` (`NearLerayModeSplit`): decomposition into four analytic leaves

Target: `NearLerayModeSplit` (`Sub/N02.lean`). Source of record
`the November 2 reference manuscript`, lines 1738-1740 (zero frequency and nonzero
frequencies are treated separately): `f = f_0 + f_1` with `f_0 = c⁻¹ ∫_0^c f dq` (the `q`-average,
`avgQ`) and `f_1 = f - f_0` (zero `q`-mean); both are smooth band tests, `N(f_0) ≤ N(f)` and
`N(f_1) ≤ 2 N(f)` where `N = nzMomSum` is the moment sum of `nearLerayRhs`, and the approximants of
`F_0 = toLp f_0` and `F_1 = toLp f_1` add because the projections are linear.


`Tasks/N02LerayComparison/ModeSplit.lean` (attempt 2, status partial; audited, recompiled OK): the
`q`-average is `QInvariant`, the remainder is `QMeanZero`, both are band tests once `avgQ c f` is
smooth, band tests are in `L²(measureH c)`, and the Hilbert-space assembly
`nearLerayModeSplit_of` (approximants add; `d = max d₀ d₁`, `C = 3 (C₀ + C₁)`). The analytic

here to the three leaf Props `IntervalParamSmooth`, `AvgQCauchySchwarz`, `AvgSliceMono` (the
conditional theorems are in `Sub/N02_5/Cond.lean`; `AvgSmooth` and `AvgOpS` follow from
`IntervalParamSmooth`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

theorem avgNzMomSum_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℝ)
    (g : Profile → E) : 0 ≤ nzMomSum c g := by
  unfold nzMomSum nzSq
  refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun j _ => Real.rpow_nonneg ?_ _
  exact integral_nonneg fun p => by positivity

/-! ### The `q`-average -/

/-- The `q`-average over the cell `(0, c]`: `avgQ c f (s, q, η) = c⁻¹ ∫_0^c f(s, q', η) dq'`,
independent of `q`. This is the zero-frequency part `f_0` of line 1738. -/
def avgQ (c : ℝ) (f : Profile → MeridC) : Profile → MeridC := fun p =>
  (c⁻¹ : ℝ) • ∫ q in (0 : ℝ)..c, f (p.1, q, p.2.2)

/-- The average is `q`-independent. -/
theorem qInvariant_avgQ (c : ℝ) (f : Profile → MeridC) : QInvariant c (avgQ c f) :=
  fun _ _ _ _ => rfl

/-- Band support of the average: `avgQ c f p ≠ 0` forces `p` into the band of `f`. -/
theorem avgQ_band {c s0 s1 L : ℝ} {f : Profile → MeridC}
    (hb : ∀ p : Profile, f p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) (p : Profile)
    (hp : avgQ c f p ≠ 0) : p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L := by
  by_contra hne
  apply hp
  have hz : ∀ q : ℝ, f (p.1, q, p.2.2) = 0 := fun q => by
    by_contra hq
    exact hne (hb (p.1, q, p.2.2) hq)
  simp [avgQ, hz]

/-- The average of a band test is a band test, provided it is smooth. -/
theorem isMeridTest_avgQ {c : ℝ} {f : Profile → MeridC} (hf : IsMeridTest c f)
    (hsm : ContDiff ℝ ∞ (avgQ c f)) : IsMeridTest c (avgQ c f) := by
  obtain ⟨s0, s1, L, hs0, hb⟩ := hf.band
  exact ⟨hsm, fun _ => rfl, s0, s1, L, hs0, fun p hp => avgQ_band hb p hp⟩

/-- The remainder `f - avgQ c f` is a band test, provided the average is smooth. -/
theorem isMeridTest_sub_avgQ {c : ℝ} {f : Profile → MeridC} (hf : IsMeridTest c f)
    (hA : IsMeridTest c (avgQ c f)) : IsMeridTest c (fun p => f p - avgQ c f p) := by
  obtain ⟨s0, s1, L, hs0, hb⟩ := hf.band
  refine ⟨hf.smooth.sub hA.smooth, fun p => ?_, s0, s1, L, hs0, fun p hp => ?_⟩
  · show f (p.1, p.2.1 + c, p.2.2) - avgQ c f (p.1, p.2.1 + c, p.2.2) = f p - avgQ c f p
    rw [hf.periodic p, hA.periodic p]
  · by_cases h : f p = 0
    · refine avgQ_band (c := c) hb p ?_
      intro h2
      apply hp
      simp [h, h2]
    · exact hb p h

/-- The remainder `f - avgQ c f` has zero `q`-mean over the cell. -/
theorem qMeanZero_sub_avgQ {c : ℝ} (hc : 0 < c) {f : Profile → MeridC} (hf : IsMeridTest c f) :
    QMeanZero c (fun p => f p - avgQ c f p) := by
  intro s η
  have hcont : Continuous fun q : ℝ => f (s, q, η) :=
    Continuous.comp hf.smooth.continuous
      (by fun_prop : Continuous fun q : ℝ => ((s, q, η) : Profile))
  have hconst : ∀ q : ℝ, avgQ c f (s, q, η) = (c⁻¹ : ℝ) • ∫ x in (0 : ℝ)..c, f (s, x, η) :=
    fun _ => rfl
  show ∫ q in (0 : ℝ)..c, (f (s, q, η) - avgQ c f (s, q, η)) = 0
  simp only [hconst]
  rw [intervalIntegral.integral_sub (hcont.intervalIntegrable 0 c) intervalIntegrable_const,
    intervalIntegral.integral_const, sub_zero, smul_smul, mul_inv_cancel₀ hc.ne', one_smul,
    sub_self]

/-! ### `L²` membership of band tests -/

/-- A continuous function supported in the band `s0 ≤ s ≤ s1`, `|η| ≤ L` is in `L²(measureH c)`.
Copied from `Tasks/N02LerayComparison/GradMember.lean` (`memLp_of_band`). -/
theorem avgMemLp_of_band {c s0 s1 L : ℝ} {E : Type*} [NormedAddCommGroup E]
    [SecondCountableTopologyEither Profile E] {f : Profile → E} (hf : Continuous f)
    (hs0 : 0 < s0) (hz : ∀ p : Profile, ¬(p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) → f p = 0) :
    MemLp f 2 (measureH c) := by
  refine memLp_of_continuous_of_ae_vanish hf
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)) (measureH_band_ne_top c hs0 s1 L) ?_ 2
  filter_upwards [ae_cell_measureH c] with p hp hpA
  apply hz p
  intro hb
  exact hpA ⟨hb.1, Ioc_subset_Icc_self hp.2.1, abs_le.1 hb.2⟩

/-- An `IsMeridTest` profile is in `L²(measureH c)`. -/
theorem avgMemLp_of_isMeridTest {c : ℝ} {g : Profile → MeridC} (hg : IsMeridTest c g) :
    MemLp g 2 (measureH c) := by
  obtain ⟨s0, s1, L, hs0, hb⟩ := hg.band
  refine avgMemLp_of_band (c := c) (s0 := s0) (s1 := s1) (L := L) hg.smooth.continuous hs0 ?_
  intro p hp
  by_contra hne
  exact hp (hb p hne)

/-! ### Elementary monotonicity of the constants -/

theorem avgRhs_mono {C : ℝ} (hC : 0 ≤ C) {K : ℝ} (hK : 1 ≤ K) {d d' : ℕ} (hd : d ≤ d')
    (ε : ℝ) {m m' : ℝ} (hm : 0 ≤ m) (hmm : m ≤ m') :
    C * K ^ d * Real.sqrt ε * m ≤ C * K ^ d' * Real.sqrt ε * m' := by
  have hx : 0 ≤ C * Real.sqrt ε := mul_nonneg hC (Real.sqrt_nonneg ε)
  have hK0 : 0 ≤ K ^ d' := pow_nonneg (by linarith) _
  have hpow : K ^ d ≤ K ^ d' := pow_le_pow_right₀ hK hd
  calc C * K ^ d * Real.sqrt ε * m = (C * Real.sqrt ε) * K ^ d * m := by ring
    _ ≤ (C * Real.sqrt ε) * K ^ d' * m' :=
        mul_le_mul (mul_le_mul_of_nonneg_left hpow hx) hmm hm (mul_nonneg hx hK0)
    _ = C * K ^ d' * Real.sqrt ε * m' := by ring


/-!-/

/-- **Leaf `IntervalParamSmooth`: smooth dependence on a parameter of an integral over a compact
interval.** If `H : P × ℝ → V` is `C^∞` then `x ↦ ∫_a^b H(x, q) dq` is `C^∞` and its derivative in the
direction `v` is `∫_a^b D H(x, q) (v, 0) dq`. Proof: induction on the smoothness order `n` (for all
Banach `V` simultaneously); the derivative formula is
`intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le` (the domination of `D H` on a ball
times `[a, b]` comes from continuity on the compact set `closedBall x r ×ˢ uIcc a b`) and the derivative
is again such an integral of the smooth function `(x, q) ↦ (D H (x, q)).comp (inl)`. Used for the
`q`-average (`AvgSmooth`, `AvgOpS`) and for the `q`-Fourier coefficients of a profile. -/
def IntervalParamSmooth : Prop :=
  ∀ (P V : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup V]
    [NormedSpace ℝ V] [CompleteSpace V] (a b : ℝ) (H : P × ℝ → V), ContDiff ℝ ∞ H →
    ContDiff ℝ ∞ (fun x : P => ∫ q in a..b, H (x, q)) ∧
      ∀ x v : P, fderiv ℝ (fun x : P => ∫ q in a..b, H (x, q)) x v =
        ∫ q in a..b, fderiv ℝ H (x, q) (v, 0)

/-- Analytic input 1 (reduced to `IntervalParamSmooth` by `avgSmooth_of`): the `q`-average of a band
test is smooth (differentiation under the `q`-integral over the compact interval `[0, c]`). -/
def AvgSmooth : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ f : Profile → MeridC, IsMeridTest c f → ContDiff ℝ ∞ (avgQ c f)

/-- Analytic input 2: zero-frequency moment comparison `N(f_0) ≤ N(f)` (Jensen in `q` plus Fubini on
`measureH c`; `opS` commutes with the `q`-average). Reduced to `AvgOpS` and `AvgJensen`
(`avgMomentZero_of`). -/
def AvgMomentZero : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ f : Profile → MeridC, IsMeridTest c f →
    nzMomSum c (avgQ c f) ≤ nzMomSum c f

/-- Analytic input 3: nonzero-frequency moment comparison `N(f_1) ≤ 2 N(f)` (pointwise
`‖a - b‖² ≤ 2‖a‖² + 2‖b‖²` and input 2). Reduced to `AvgSmooth` and `AvgMomentZero`
(`avgMomentOne_of`). -/
def AvgMomentOne : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ f : Profile → MeridC, IsMeridTest c f →
    nzMomSum c (fun p => f p - avgQ c f p) ≤ 2 * nzMomSum c f

/-- **`AvgOpS` (reduced to `IntervalParamSmooth` by `avgOpS_of`): `S = s ∂_s` commutes with the
`q`-average.** For a smooth test `f`,
`opS (avgQ c f) = avgQ c (opS f)` as functions on `Profile`: `S` differentiates only in `s`, the
average integrates only in `q`, and `f` is smooth, so `∂_s ∫_0^c f(s, q, η) dq =
∫_0^c ∂_s f(s, q, η) dq` (differentiation under the integral over the compact interval `[0, c]`). -/
def AvgOpS : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ f : Profile → MeridC, IsMeridTest c f →
    opS (avgQ c f) = avgQ c (opS f)

/-- **Leaf `AvgQCauchySchwarz`: Jensen/Cauchy-Schwarz for the `q`-average, pointwise.** For a continuous
`v : ℝ → ℂ²` and `c > 0`: `‖∫_0^c v‖² ≤ c ∫_0^c ‖v‖²` (equivalently `‖c⁻¹ ∫_0^c v‖² ≤ c⁻¹ ∫_0^c ‖v‖²`). -/
def AvgQCauchySchwarz : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ v : ℝ → MeridC, Continuous v →
    ‖∫ q in (0 : ℝ)..c, v q‖ ^ 2 ≤ c * ∫ q in (0 : ℝ)..c, ‖v q‖ ^ 2

/-- **Leaf `AvgSliceMono`: Fubini on `measureH c`, monotone form.** For continuous real `A, B` supported in
a common band `s ∈ [s₀, s₁]`, `|η| ≤ L` with `s₀ > 0`, if `∫_0^c A(s, q, η) dq ≤ ∫_0^c B(s, q, η) dq` for
all `s > 0` and `η`, then `∫ A d(measureH c) ≤ ∫ B d(measureH c)`. Proof: `measureH c` is the
weighted cell measure `s^{-3/2} ds dq dη` on `(0,∞) × (0, c] × ℝ`; `A`, `B` are integrable (continuous,
compactly supported in the band, weight `s^{-3/2} ≤ s₀^{-3/2}` there); integrate the `q`-variable first
(Fubini) and apply the pointwise inequality of the `q`-slices to the nonnegative weight. -/
def AvgSliceMono : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ A B : Profile → ℝ, Continuous A → Continuous B →
    (∃ s0 s1 L : ℝ, 0 < s0 ∧
      ∀ p : Profile, (A p ≠ 0 ∨ B p ≠ 0) → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) →
    (∀ s η : ℝ, 0 < s →
      ∫ q in (0 : ℝ)..c, A (s, q, η) ≤ ∫ q in (0 : ℝ)..c, B (s, q, η)) →
    ∫ p, A p ∂(measureH c) ≤ ∫ p, B p ∂(measureH c)

/-! ### Assembly (fully proved, conditional on the three inputs) -/

/-- **Assembly.** `NearLerayModeSplit` from the three analytic inputs. The approximants of
`F_0 = toLp f_0` and `F_1 = toLp f_1` add (projections are linear), and the constants
`d = max d₀ d₁`, `C = 3 (C₀ + C₁)` absorb the moment bounds. -/
theorem nearLerayModeSplit_of (hsm : AvgSmooth) (hm0 : AvgMomentZero) (hm1 : AvgMomentOne) :
    NearLerayModeSplit := by
  unfold NearLerayModeSplit
  intro hA0 hA1
  obtain ⟨d0, C0, hC0, hA0'⟩ := hA0
  obtain ⟨d1, C1, hC1, hA1'⟩ := hA1
  refine ⟨max d0 d1, 3 * (C0 + C1), by linarith, fun c ε hc hε hε1 f F hf _ hF => ?_⟩
  have hK : (1 : ℝ) ≤ 1 + c + c⁻¹ := by
    have := inv_pos.2 hc
    linarith
  have h0 : IsMeridTest c (avgQ c f) := isMeridTest_avgQ hf (hsm c hc f hf)
  have h1 : IsMeridTest c (fun p => f p - avgQ c f p) := isMeridTest_sub_avgQ hf h0
  obtain ⟨F0, hF0⟩ : ∃ G : HSpace c MeridC, (G : Profile → MeridC) =ᵐ[measureH c] avgQ c f :=
    ⟨(avgMemLp_of_isMeridTest h0).toLp _, (avgMemLp_of_isMeridTest h0).coeFn_toLp⟩
  obtain ⟨F1, hF1⟩ : ∃ G : HSpace c MeridC,
      (G : Profile → MeridC) =ᵐ[measureH c] fun p => f p - avgQ c f p :=
    ⟨(avgMemLp_of_isMeridTest h1).toLp _, (avgMemLp_of_isMeridTest h1).coeFn_toLp⟩
  have hsplit : F = F0 + F1 := by
    apply Lp.ext
    filter_upwards [hF, Lp.coeFn_add F0 F1, hF0, hF1] with p hFp hadd h0p h1p
    rw [hadd, Pi.add_apply, hFp, h0p, h1p]
    simp
  have hT0 : QInvariant c (avgQ c f) := qInvariant_avgQ c f
  have hT1 : QMeanZero c (fun p => f p - avgQ c f p) := qMeanZero_sub_avgQ hc hf
  obtain ⟨⟨g0, hg0, hgb0⟩, ⟨s0', hs0', hsb0⟩⟩ :=
    hA0' c ε hc hε hε1 (avgQ c f) F0 h0 hT0 hF0
  obtain ⟨⟨g1, hg1, hgb1⟩, ⟨s1', hs1', hsb1⟩⟩ :=
    hA1' c ε hc hε hε1 (fun p => f p - avgQ c f p) F1 h1 hT1 hF1
  -- Constants: each piece is bounded by the corresponding moment term of `f`.
  have hX0 : 0 ≤ C0 * (1 + c + c⁻¹) ^ (max d0 d1) * Real.sqrt ε * nzMomSum c f := by
    have hp : 0 ≤ (1 + c + c⁻¹) ^ (max d0 d1) := pow_nonneg (by linarith) _
    exact mul_nonneg (mul_nonneg (mul_nonneg hC0 hp) (Real.sqrt_nonneg ε)) (avgNzMomSum_nonneg c f)
  have hX1 : 0 ≤ C1 * (1 + c + c⁻¹) ^ (max d0 d1) * Real.sqrt ε * nzMomSum c f := by
    have hp : 0 ≤ (1 + c + c⁻¹) ^ (max d0 d1) := pow_nonneg (by linarith) _
    exact mul_nonneg (mul_nonneg (mul_nonneg hC1 hp) (Real.sqrt_nonneg ε)) (avgNzMomSum_nonneg c f)
  have hRhs : nearLerayRhs C0 d0 c ε (avgQ c f)
      + nearLerayRhs C1 d1 c ε (fun p => f p - avgQ c f p)
      ≤ nearLerayRhs (3 * (C0 + C1)) (max d0 d1) c ε f := by
    simp only [nearLerayRhs_eq_nzMomSum]
    have hR0 := avgRhs_mono hC0 hK (le_max_left d0 d1) ε (avgNzMomSum_nonneg c (avgQ c f))
      (hm0 c hc f hf)
    have hR1 := avgRhs_mono hC1 hK (le_max_right d0 d1) ε
      (avgNzMomSum_nonneg c (fun p => f p - avgQ c f p)) (hm1 c hc f hf)
    have hE1 : C1 * (1 + c + c⁻¹) ^ (max d0 d1) * Real.sqrt ε * (2 * nzMomSum c f)
        = 2 * (C1 * (1 + c + c⁻¹) ^ (max d0 d1) * Real.sqrt ε * nzMomSum c f) := by ring
    have hE2 : 3 * (C0 + C1) * (1 + c + c⁻¹) ^ (max d0 d1) * Real.sqrt ε * nzMomSum c f
        = 3 * (C0 * (1 + c + c⁻¹) ^ (max d0 d1) * Real.sqrt ε * nzMomSum c f)
          + 3 * (C1 * (1 + c + c⁻¹) ^ (max d0 d1) * Real.sqrt ε * nzMomSum c f) := by ring
    linarith [hR0, hR1, hE1, hE2, hX0, hX1]
  refine ⟨⟨g0 + g1, Submodule.add_mem _ hg0 hg1, ?_⟩, ⟨s0' + s1', Submodule.add_mem _ hs0' hs1', ?_⟩⟩
  · rw [hsplit, map_add]
    have e : (solenoidalHC 0 c)ᗮ.starProjection F0 + (solenoidalHC 0 c)ᗮ.starProjection F1
        - (g0 + g1) = ((solenoidalHC 0 c)ᗮ.starProjection F0 - g0)
          + ((solenoidalHC 0 c)ᗮ.starProjection F1 - g1) := by abel
    rw [e]
    exact (norm_add_le _ _).trans (by linarith [hgb0, hgb1, hRhs])
  · rw [hsplit, map_add]
    have e : (solenoidalHC 0 c).starProjection F0 + (solenoidalHC 0 c).starProjection F1
        - (s0' + s1') = ((solenoidalHC 0 c).starProjection F0 - s0')
          + ((solenoidalHC 0 c).starProjection F1 - s1') := by abel
    rw [e]
    exact (norm_add_le _ _).trans (by linarith [hsb0, hsb1, hRhs])


end UnforcedLeray.Short.PartIIa
