import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFluxLemmas
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFlux.VtvZpSmooth
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFlux.VtvZpVanish
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFlux.VtvThetaFacts
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.DivFreeCutoffDensity.QPrimDeriv

/-!
# Part III-b, task `PartIII-b:C/flatset/col/6/5/8`: the flux remainder `E_R` is a flat test

Target (`VtvFluxLemmas.lean`): `VtvErrFlat`. Source of record:
`the November 2 reference manuscript`, lines 3511-3514 and 3426-3440.

`E_R(s,x) = (F(s) θ'(x₂/R)/R, 0)` with `F = vtvFluxF Φ R₀`. It is smooth (`F` smooth, `θ'` smooth),
independent of `x₁` (periodic), divergence free (`E_η = 0` and `E_q` independent of `q`), and vanishes
for `s ∉ (s₁, s₂)` (`F` vanishes there) or `|x₂| > 2R` (`θ'(t) = 0` for `t ≤ 1` or `t ≥ 2`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (IsFlatTest)

/-- Target: `VtvErrFlat`. The flux remainder is a flat test supported in `[s₁,s₂] × {|η| ≤ 2R}`. -/
theorem vtvErrFlat : VtvErrFlat := by
  intro c Φ s₁ s₂ R₀ hS R hR
  have hΦ : IsFlatTest c Φ := hS.1
  have hs1 : 0 < s₁ := hS.2.1
  have hV := vtvZpVanish c Φ s₁ s₂ R₀ hS
  have hZ := vtvZpSmooth c Φ hΦ R₀
  -- the flux is smooth and vanishes off the age band
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ => (s, ((0:ℝ), R₀ + 1))) := by
    fun_prop
  have hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (vtvFluxF Φ R₀) := hZ.comp hg
  have hFvan : ∀ t, (t < s₁ ∨ s₂ < t) → vtvFluxF Φ R₀ t = 0 := fun t ht =>
    hV.2.1 t (0, R₀ + 1) ht
  -- the cutoff derivative is smooth
  have hθ := vtvThetaFacts.1
  have hDθ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv vtvTheta) :=
    (contDiff_infty_iff_deriv.1 hθ).2
  -- the closed forms of the two components
  have hval0 : ∀ s x, vtvErr Φ R₀ R s x 0 =
      vtvFluxF Φ R₀ s * deriv vtvTheta (x.2 / R) / R := fun s x => if_pos rfl
  have hval1 : ∀ s x, vtvErr Φ R₀ R s x 1 = 0 := fun s x => if_neg (by decide)
  -- smoothness of the components
  have hsm0 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × (ℝ × ℝ) => vtvErr Φ R₀ R p.1 p.2 0) := by
    have hfun : (fun p : ℝ × (ℝ × ℝ) => vtvErr Φ R₀ R p.1 p.2 0) =
        fun p => vtvFluxF Φ R₀ p.1 * deriv vtvTheta (p.2.2 / R) / R :=
      funext (fun p => hval0 p.1 p.2)
    rw [hfun]
    exact (((hF.comp contDiff_fst).mul
      (hDθ.comp ((contDiff_snd.comp contDiff_snd).div_const R))).div_const R)
  have hsm1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × (ℝ × ℝ) => vtvErr Φ R₀ R p.1 p.2 1) := by
    have hfun : (fun p : ℝ × (ℝ × ℝ) => vtvErr Φ R₀ R p.1 p.2 1) = fun _ => (0:ℝ) :=
      funext (fun p => hval1 p.1 p.2)
    rw [hfun]
    exact contDiff_const
  have hsm : ∀ i : Fin 2, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × (ℝ × ℝ) => vtvErr Φ R₀ R p.1 p.2 i) := by
    intro i
    rcases (show i = 0 ∨ i = 1 by fin_cases i <;> simp) with rfl | rfl
    · exact hsm0
    · exact hsm1
  -- the support clause
  have hsupp : ∀ s x i, (s < s₁ ∨ s₂ < s ∨ 2 * R < |x.2|) → vtvErr Φ R₀ R s x i = 0 := by
    intro s x i h
    rcases (show i = 0 ∨ i = 1 by fin_cases i <;> simp) with rfl | rfl
    · rw [hval0]
      rcases h with h | h | h
      · rw [hFvan s (Or.inl h), zero_mul, zero_div]
      · rw [hFvan s (Or.inr h), zero_mul, zero_div]
      · have hder : deriv vtvTheta (x.2 / R) = 0 := by
          rcases lt_or_ge 0 x.2 with h0 | h0
          · rw [abs_of_pos h0] at h
            exact vtvThetaFacts.2.2.2.1 _ (Or.inr ((le_div_iff₀ hR).2 (by linarith)))
          · rw [abs_of_nonpos h0] at h
            exact vtvThetaFacts.2.2.2.1 _ (Or.inl ((div_le_iff₀ hR).2 (by linarith)))
        rw [hder, mul_zero, zero_div]
    · exact hval1 s x
  -- divergence-free
  have hdiv : ∀ s x, B0579.pd 0 (fun y => vtvErr Φ R₀ R s y 0) x +
      B0579.pd 1 (fun y => vtvErr Φ R₀ R s y 1) x = 0 := by
    intro s x
    obtain ⟨q, η⟩ := x
    have hdiffY : Differentiable ℝ (fun y : ℝ × ℝ => vtvErr Φ R₀ R s y 0) :=
      (hsm0.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
    have hsec0 : B0579.pd 0 (fun y => vtvErr Φ R₀ R s y 0) (q, η) = 0 := by
      rw [UnforcedLeray.Short.IIIa.DfcQPrimDerivAux.pd0_eq _ q η (hdiffY (q, η))]
      have hconst : (fun s' : ℝ => vtvErr Φ R₀ R s (s', η) 0) =
          fun _ => vtvFluxF Φ R₀ s * deriv vtvTheta (η / R) / R :=
        funext (fun s' => hval0 s (s', η))
      rw [hconst, deriv_const]
    have hsec1 : B0579.pd 1 (fun y => vtvErr Φ R₀ R s y 1) (q, η) = 0 := by
      have hz : (fun y : ℝ × ℝ => vtvErr Φ R₀ R s y 1) = fun _ => (0:ℝ) :=
        funext (fun y => hval1 s y)
      rw [hz, UnforcedLeray.Short.IIIa.DfcQPrimDerivAux.pd1_eq (fun _ : ℝ × ℝ => (0:ℝ)) q η
        (differentiableAt_const _)]
      simp
    rw [hsec0, hsec1, add_zero]
  refine ⟨⟨hsm, ?_, ⟨s₁, s₂, 2 * R, hs1, hsupp⟩, hdiv⟩, hsupp⟩
  -- periodicity in `q`: the field does not depend on `x₁`
  intro s x i
  rcases (show i = 0 ∨ i = 1 by fin_cases i <;> simp) with rfl | rfl
  · simp only [hval0]
  · simp only [hval1]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
