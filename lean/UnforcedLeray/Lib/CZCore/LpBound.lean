import UnforcedLeray.Lib.CZCore.CZWeak
import UnforcedLeray.Lib.CZCore.Marcinkiewicz
import UnforcedLeray.Lib.CZCore.Norming
import UnforcedLeray.Lib.CZCore.Extension

/-!
# `L^p` bounds of anisotropic Calderón–Zygmund operators (INF01 T12)


target T12; §4.9 ("Marcinkiewicz gives `1 < p < 2`; duality gives `2 < p < ∞`, using the
transpose operator"); decision D4 of `scoping/README.md` §3. This is the abstract form of the
Riesz-transform bound used for the Leray projection (blueprint unit B0414, `paper/main.tex`
lines 7336–7344: "bounded on `L^q` for `1 < q < ∞`", citing Grafakos Cor. 5.2.8) and of the
parabolic estimate eq:free-stress-11 (unit B0423, lines 7447–7477).

* `lp_bound` (**T12**): if `T` and its transpose `T'` (`∫ (T f) g = ∫ f (T' g)` on `L²`) are
  Calderón–Zygmund convolution operators, then for every `1 < p < ∞` there is `C` with
  `‖T f‖_p ≤ C ‖f‖_p` for all `f ∈ L² ∩ L^p`. For `p < 2`: weak `(1,1)` (T10) and Marcinkiewicz
  (T7). For `p = 2`: `‖T‖`. For `p > 2`: the bound for `T'` at the conjugate exponent and the
  norming lemma (T11, `L²` form).
* `extendLp`: the bounded operator on `L^p`, `1 < p < ∞`, obtained by continuity;
  `extendLp_apply`: it agrees with `T` on `L² ∩ L^p`; `extendLp_consistent`: for
  `f ∈ L^p ∩ L^q` the two extensions agree almost everywhere.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff

namespace UnforcedLeray.CZ

set_option autoImplicit false

variable {N : ℕ} {a : Fin N → ℕ+}
  {T T' : Lp ℝ 2 (volume : Measure (Fin N → ℝ)) →L[ℝ] Lp ℝ 2 (volume : Measure (Fin N → ℝ))}
  {K K' : (Fin N → ℝ) → ℝ} {B B' : ℝ≥0}

/-- **Duality step.** If the transpose `T'` is bounded on `L² ∩ L^{p'}` with constant `C'`,
then `T` is bounded on `L² ∩ L^p` with the same constant. -/
theorem eLpNorm_le_of_adjoint_bound {p : ℝ} (hp : 1 < p) {C' : ℝ≥0}
    (hadj : ∀ f g : Lp ℝ 2 (volume : Measure (Fin N → ℝ)), ∫ x, T f x * g x = ∫ x, f x * T' g x)
    (hT'q : ∀ g : Lp ℝ 2 (volume : Measure (Fin N → ℝ)),
      MemLp g (ENNReal.ofReal p.conjExponent) volume →
      eLpNorm (T' g) (ENNReal.ofReal p.conjExponent) volume ≤
        C' * eLpNorm g (ENNReal.ofReal p.conjExponent) volume)
    (f : Lp ℝ 2 (volume : Measure (Fin N → ℝ))) (hf : MemLp f (ENNReal.ofReal p) volume) :
    eLpNorm (T f) (ENNReal.ofReal p) volume ≤ C' * eLpNorm f (ENNReal.ofReal p) volume := by
  have hpq : p.HolderConjugate p.conjExponent := Real.HolderConjugate.conjExponent hp
  have : ENNReal.HolderConjugate (ENNReal.ofReal p) (ENNReal.ofReal p.conjExponent) :=
    hpq.ennrealOfReal
  have hfin : eLpNorm f (ENNReal.ofReal p) volume ≠ ⊤ := hf.2.ne
  have key : ∀ ψ : (Fin N → ℝ) → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      |∫ x, T f x * ψ x| ≤ (C' * (eLpNorm f (ENNReal.ofReal p) volume).toReal) *
        (eLpNorm ψ (ENNReal.ofReal p.conjExponent) volume).toReal := by
    intro ψ hψ hψc
    have hψ2 : MemLp ψ 2 volume := hψ.continuous.memLp_of_hasCompactSupport hψc
    have hψq : MemLp ψ (ENNReal.ofReal p.conjExponent) volume :=
      hψ.continuous.memLp_of_hasCompactSupport hψc
    have hΨq : MemLp (hψ2.toLp ψ) (ENNReal.ofReal p.conjExponent) volume :=
      hψq.ae_eq hψ2.coeFn_toLp.symm
    have h1 : ∫ x, T f x * ψ x = ∫ x, f x * T' (hψ2.toLp ψ) x := by
      rw [← hadj f (hψ2.toLp ψ)]
      exact integral_congr_ae (hψ2.coeFn_toLp.mono fun x hx => by simp only [hx])
    have hfinψ : eLpNorm ψ (ENNReal.ofReal p.conjExponent) volume ≠ ⊤ := hψq.2.ne
    have h2 : ENNReal.ofReal |∫ x, f x * T' (hψ2.toLp ψ) x| ≤
        eLpNorm f (ENNReal.ofReal p) volume *
          (C' * eLpNorm ψ (ENNReal.ofReal p.conjExponent) volume) := by
      refine (ofReal_abs_integral_mul_le (p := ENNReal.ofReal p)
        (q := ENNReal.ofReal p.conjExponent) (Lp.aestronglyMeasurable f)
        (Lp.aestronglyMeasurable (T' (hψ2.toLp ψ)))).trans ?_
      gcongr
      rw [← eLpNorm_congr_ae hψ2.coeFn_toLp]
      exact hT'q _ hΨq
    rw [h1]
    have h3 := (ENNReal.ofReal_le_iff_le_toReal
      (ENNReal.mul_ne_top hfin (ENNReal.mul_ne_top ENNReal.coe_ne_top hfinψ))).1 h2
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal] at h3
    exact h3.trans (le_of_eq (by ring))
  have h := eLpNorm_le_of_forall_test_pairing_of_memLp_two hp (Lp.memLp (T f)) key
  rwa [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal,
    ENNReal.ofReal_toReal hfin] at h

/-- **T12 (INF01 §5, Level 1): `L^p` bound.** If `T` and its transpose `T'` are anisotropic
Calderón–Zygmund convolution operators (`N ≥ 1`), then for every `1 < p < ∞` there is a constant
`C` with `‖T f‖_p ≤ C ‖f‖_p` for every `f ∈ L² ∩ L^p`. -/
theorem lp_bound [NeZero N] (hT : IsCZConvolution a T K B) (hT' : IsCZConvolution a T' K' B')
    (hadj : ∀ f g : Lp ℝ 2 (volume : Measure (Fin N → ℝ)), ∫ x, T f x * g x = ∫ x, f x * T' g x)
    {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ≥0, ∀ f : Lp ℝ 2 (volume : Measure (Fin N → ℝ)), MemLp f (ENNReal.ofReal p) volume →
      eLpNorm (T f) (ENNReal.ofReal p) volume ≤ C * eLpNorm f (ENNReal.ofReal p) volume := by
  rcases lt_trichotomy p 2 with hp2 | rfl | hp2
  · exact ⟨_, marcinkiewicz (weak11_of_isCZConvolution hT) hp hp2⟩
  · refine ⟨‖T‖₊, fun f _ => ?_⟩
    rw [ENNReal.ofReal_ofNat]
    exact eLpNorm_apply_le T f
  · have hpq : p.HolderConjugate p.conjExponent := Real.HolderConjugate.conjExponent hp
    have hq1 : 1 < p.conjExponent := hpq.symm.lt
    have hq2 : p.conjExponent < 2 := by
      rw [Real.conjExponent, div_lt_iff₀ (by linarith)]
      linarith
    exact ⟨_, eLpNorm_le_of_adjoint_bound hp hadj
      (marcinkiewicz (weak11_of_isCZConvolution hT') hq1 hq2)⟩

/-- `lp_bound` with the exponent in `ℝ≥0∞`. -/
theorem lp_bound_ennreal [NeZero N] (hT : IsCZConvolution a T K B)
    (hT' : IsCZConvolution a T' K' B')
    (hadj : ∀ f g : Lp ℝ 2 (volume : Measure (Fin N → ℝ)), ∫ x, T f x * g x = ∫ x, f x * T' g x)
    {p : ℝ≥0∞} (hp1 : 1 < p) (hp : p ≠ ⊤) :
    ∃ C : ℝ≥0, ∀ f : Lp ℝ 2 (volume : Measure (Fin N → ℝ)), MemLp f p volume →
      eLpNorm (T f) p volume ≤ C * eLpNorm f p volume := by
  have h1 : 1 < p.toReal := by
    have := ENNReal.toReal_strict_mono hp hp1
    rwa [ENNReal.toReal_one] at this
  obtain ⟨C, hC⟩ := lp_bound hT hT' hadj h1
  rw [ENNReal.ofReal_toReal hp] at hC
  exact ⟨C, hC⟩

/-- **T12 (INF01 §5, Level 1): the operator on `L^p`**, `1 < p < ∞`, extending `T` from
`L² ∩ L^p` by continuity. -/
def extendLp [NeZero N] (hT : IsCZConvolution a T K B) (hT' : IsCZConvolution a T' K' B')
    (hadj : ∀ f g : Lp ℝ 2 (volume : Measure (Fin N → ℝ)), ∫ x, T f x * g x = ∫ x, f x * T' g x)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ⊤) :
    Lp ℝ p (volume : Measure (Fin N → ℝ)) →L[ℝ] Lp ℝ p (volume : Measure (Fin N → ℝ)) :=
  extendOfBound T p (Classical.choose (lp_bound_ennreal hT hT' hadj hp1 hp))
    (Classical.choose_spec (lp_bound_ennreal hT hT' hadj hp1 hp))

/-- `extendLp` agrees with `T` on `L² ∩ L^p`. -/
theorem extendLp_apply [NeZero N] (hT : IsCZConvolution a T K B)
    (hT' : IsCZConvolution a T' K' B')
    (hadj : ∀ f g : Lp ℝ 2 (volume : Measure (Fin N → ℝ)), ∫ x, T f x * g x = ∫ x, f x * T' g x)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ⊤)
    (f : Lp ℝ 2 (volume : Measure (Fin N → ℝ))) (hfp : MemLp f p volume) :
    ⇑(extendLp hT hT' hadj p hp1 hp (hfp.toLp f)) =ᵐ[volume] ⇑(T f) :=
  extendOfBound_apply T p _ _ hp f hfp

/-- **T12 (INF01 §5, Level 1): consistency.** For `f ∈ L^p ∩ L^q` the extensions at `p` and at
`q` agree almost everywhere. -/
theorem extendLp_consistent [NeZero N] (hT : IsCZConvolution a T K B)
    (hT' : IsCZConvolution a T' K' B')
    (hadj : ∀ f g : Lp ℝ 2 (volume : Measure (Fin N → ℝ)), ∫ x, T f x * g x = ∫ x, f x * T' g x)
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hp1 : 1 < p) (hp : p ≠ ⊤) (hq1 : 1 < q)
    (hq : q ≠ ⊤) {f : (Fin N → ℝ) → ℝ} (hfp : MemLp f p volume) (hfq : MemLp f q volume) :
    ⇑(extendLp hT hT' hadj p hp1 hp (hfp.toLp f)) =ᵐ[volume]
      ⇑(extendLp hT hT' hadj q hq1 hq (hfq.toLp f)) :=
  extendOfBound_consistent T hp hq _ _ hfp hfq

end UnforcedLeray.CZ
