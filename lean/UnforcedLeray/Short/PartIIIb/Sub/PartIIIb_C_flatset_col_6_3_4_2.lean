import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_4
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod

/-!
# `PartIII-b:C/flatset/col/6/3/4/2` (`vtvFubiniJoint`): decomposition

Source of record: `the November 2 reference manuscript`
(line 4610: the integrated Duhamel identity `Y(s,φ) = ∫₀^s R(r,φ) dr`, with `R(r,φ) = r^μ(⟨g,φ⟩ +
∫flowIntegrand)`).

The joint integrability of `F(s,r) = 1_{r ≤ s} R(r,∂_sη(s))` on `(0,∞)²` is reduced (Tonelli,
`integrable_prod_iff`) to three leaves:

* `VtvFubiniMeas`: joint a.e. measurability of `F`.  Route: express every `ω`-pairing through `b`
  (third clause of `IsBiotSavart`: `⟨ω(r),ψ⟩ = ∫ b(r)·∇^⊥ψ`) and `g`-pairings through `f`
  (curl clause), so that `R(r,ψ)` is a cell integral of a jointly measurable integrand, bilinear in
  smooth `ψ`-derivatives; `ψ = ∂_sη(s)` is jointly continuous in `(s,x)`.
* `VtvFubiniOpBound`: the operator bound.  For a test band `|x.2| ≤ R` and ages `≤ s₂` the linear map
  `φ ↦ (r ↦ R(r,φ)) ∈ L¹(0,s]` is bounded by finitely many `C^k` seminorms of `φ`.  Route: closed
  graph / Banach-Steinhaus on the Fréchet space of band-supported cylinder tests; for each `r > 0`
  `R(r,·)` is continuous (`f ∈ L²` of every age band `[r₀,s₂]×cell`, `b` in `energyLoc`), and
  `L¹`-convergence of `R(·,φ_n)` forces a.e. convergence of a subsequence, identifying the graph; the
  integrability of `r ↦ R(r,φ)` on `(0,s]` for each `φ` is the last clause of `VtvHyps`.
* `VtvDerivBound`: for a stream test `η` the `C^k` seminorms of `∂_sη(s)` are bounded uniformly in
  `s` (`η` is jointly smooth, `c`-periodic in `x.1`, supported in a compact `(s,x.2)`-box); `0 < c` is needed (false for `c = 0`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- **Joint measurability** of `F(s,r) = 1_{r ≤ s} R(r,∂_sη(s))` (source 4610). -/
def VtvFubiniMeas : Prop :=
  ∀ (ν c μ : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (ω g : ℝ → ℝ × ℝ → ℂ)
    (b : Chart → Fin 2 → ℂ) (G : Chart → Fin 2 → Fin 2 → ℂ) (f : Chart → Fin 2 → ℂ),
    VtvHyps ν c μ tr ω g b G f → ∀ η : ℝ → ℝ × ℝ → ℝ, IsStreamTest c η →
      AEStronglyMeasurable (fun p : ℝ × ℝ => if p.2 ≤ p.1 then
          vtvR μ tr ω g b p.2 (fun x => deriv (fun s' => η s' x) p.1) else 0)
        ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))))

/-- **Operator bound** (source 4610): for band `|x.2| ≤ R` and ages `0 < s ≤ s₂` there are `k, C`
such that `∫_{(0,s]} ‖R(r,φ)‖ dr ≤ C M` for every band-supported cylinder test `φ` whose derivatives
of order `≤ k` are bounded by `M`. -/
def VtvFubiniOpBound : Prop :=
  ∀ (ν c μ : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (ω g : ℝ → ℝ × ℝ → ℂ)
    (b : Chart → Fin 2 → ℂ) (G : Chart → Fin 2 → Fin 2 → ℂ) (f : Chart → Fin 2 → ℂ),
    VtvHyps ν c μ tr ω g b G f → ∀ s₂ R : ℝ, ∃ (k : ℕ) (C : ℝ),
      ∀ φ : ℝ × ℝ → ℝ, B0579.IsCylTest c φ → (∀ x : ℝ × ℝ, R < |x.2| → φ x = 0) →
        ∀ M : ℝ, (∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j φ x‖ ≤ M) →
          ∀ s : ℝ, 0 < s → s ≤ s₂ → ∫ r in Ioc 0 s, ‖vtvR μ tr ω g b r φ‖ ≤ C * M

/-- **Uniform seminorm bound of `∂_sη(s)`** for a stream test `η` (jointly smooth, periodic,
compactly supported box). -/
def VtvDerivBound : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (η : ℝ → ℝ × ℝ → ℝ), IsStreamTest c η → ∀ k : ℕ, ∃ M : ℝ, ∀ s : ℝ, ∀ j ≤ k,
    ∀ x : ℝ × ℝ, ‖iteratedFDeriv ℝ j (fun x => deriv (fun s' => η s' x) s) x‖ ≤ M

theorem vtv_deriv_eq_zero {η : ℝ → ℝ × ℝ → ℝ} {s₁ s₂ : ℝ}
    (hband : ∀ s x, (s < s₁ ∨ s₂ < s ∨ False) → η s x = 0) {s : ℝ} (hs : s < s₁ ∨ s₂ < s) :
    (fun x => deriv (fun s' => η s' x) s) = fun _ => 0 := by
  funext x
  have hev : (fun s' => η s' x) =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
    rcases hs with h | h
    · filter_upwards [Iio_mem_nhds h] with t ht
      exact hband t x (Or.inl ht)
    · filter_upwards [Ioi_mem_nhds h] with t ht
      exact hband t x (Or.inr (Or.inl ht))
  rw [hev.deriv_eq]
  exact deriv_const _ 0

theorem vtvR_zero {ν c : ℝ} (μ : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (ω g : ℝ → ℝ × ℝ → ℂ)
    (b : Chart → Fin 2 → ℂ) (r : ℝ) : vtvR μ tr ω g b r (fun _ => 0) = 0 := by
  have hpd : ∀ j, B0579.pd j (fun _ : ℝ × ℝ => (0 : ℝ)) = fun _ => 0 := by
    intro j; funext x; simp [B0579.pd]
  simp [hpd, vtvR, UnforcedLeray.Short.IIIa.flowIntegrand, UnforcedLeray.Short.IIIa.lapP, B0579.pd]

theorem vtvFubiniJoint_of (hD : VtvDerivCyl) (hM : VtvFubiniMeas) (hO : VtvFubiniOpBound)
    (hB : VtvDerivBound) : VtvFubiniJoint := by
  intro ν c μ tr ω g b G f H η hη
  have hη' := hη
  obtain ⟨hsm, hcyl, s₁, s₂, R, hs₁, hband⟩ := hη'
  have hband' : ∀ s x, (s < s₁ ∨ s₂ < s ∨ False) → η s x = 0 := fun s x h => by
    rcases h with h | h | h
    · exact hband s x (Or.inl h)
    · exact hband s x (Or.inr (Or.inl h))
    · exact h.elim
  set φ : ℝ → ℝ × ℝ → ℝ := fun s x => deriv (fun s' => η s' x) s with hφ
  set F : ℝ × ℝ → ℂ := fun p => if p.2 ≤ p.1 then vtvR μ tr ω g b p.2 (φ p.1) else 0 with hF
  have hmeas : AEStronglyMeasurable F
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    hM ν c μ tr ω g b G f H η hη
  have hzero : ∀ s, (s < s₁ ∨ s₂ < s) → φ s = fun _ => 0 := fun s hs =>
    vtv_deriv_eq_zero hband' hs
  have hcylφ : ∀ s, B0579.IsCylTest c (φ s) := fun s => hD c η hη s
  have hbandφ : ∀ s, ∀ x : ℝ × ℝ, R < |x.2| → φ s x = 0 := by
    intro s x hx
    show deriv (fun s' => η s' x) s = 0
    have hz : (fun s' => η s' x) = fun _ => (0 : ℝ) :=
      funext fun s' => hband s' x (Or.inr (Or.inr hx))
    rw [hz]
    exact deriv_const _ 0
  have hInt : ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ → ∀ s : ℝ, 0 < s →
      IntegrableOn (fun r => vtvR μ tr ω g b r ψ) (Ioc 0 s) := by
    intro ψ hψ s hs
    obtain ⟨h1, h2, _⟩ := H.2.2.2.2.2.2.2.1 ψ hψ s hs
    refine (h1.add h2).congr_fun (fun r _ => ?_) measurableSet_Ioc
    simp only [vtvR, mul_add, Pi.add_apply]
  obtain ⟨k, C, hC⟩ := hO ν c μ tr ω g b G f H s₂ R
  obtain ⟨M, hM'⟩ := hB c H.2.1 η hη k
  -- slice identities
  have hslice : ∀ s : ℝ, ∀ r : ℝ, F (s, r) =
      (Iic s).indicator (fun r => vtvR μ tr ω g b r (φ s)) r := by
    intro s r
    simp only [hF, Set.indicator_apply, Set.mem_Iic]
  have hnorm : ∀ s : ℝ, 0 < s → ∫ r in Ioi (0 : ℝ), ‖F (s, r)‖ =
      ∫ r in Ioc 0 s, ‖vtvR μ tr ω g b r (φ s)‖ := by
    intro s hs
    have : (fun r => ‖F (s, r)‖) =
        (Iic s).indicator (fun r => ‖vtvR μ tr ω g b r (φ s)‖) := by
      funext r
      rw [hslice]
      by_cases h : r ∈ Iic s <;> simp [h]
    rw [this, setIntegral_indicator measurableSet_Iic, Set.Ioi_inter_Iic]
  rw [integrable_prod_iff hmeas]
  refine ⟨?_, ?_⟩
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun s hs => ?_)
    have hs0 : (0 : ℝ) < s := hs
    have : (fun r => F (s, r)) = (Iic s).indicator (fun r => vtvR μ tr ω g b r (φ s)) :=
      funext (hslice s)
    rw [this, integrable_indicator_iff measurableSet_Iic, IntegrableOn,
      Measure.restrict_restrict measurableSet_Iic, Set.inter_comm, Set.Ioi_inter_Iic]
    exact hInt _ (hcylφ s) s hs0
  · have hmeas2 : AEStronglyMeasurable (fun s => ∫ r in Ioi (0 : ℝ), ‖F (s, r)‖)
        (volume.restrict (Ioi (0 : ℝ))) :=
      hmeas.norm.integral_prod_right'
    have hK : Integrable ((Icc s₁ s₂).indicator (fun _ => C * M))
        (volume.restrict (Ioi (0 : ℝ))) := by
      rw [integrable_indicator_iff measurableSet_Icc]
      have h1 : IntegrableOn (fun _ : ℝ => C * M) (Icc s₁ s₂) volume :=
        integrableOn_const (by simp) 
      exact h1.mono_measure Measure.restrict_le_self
    refine hK.mono' hmeas2 ((ae_restrict_iff' measurableSet_Ioi).2
      (Filter.Eventually.of_forall fun s hs => ?_))
    have hs0 : (0 : ℝ) < s := hs
    rw [hnorm s hs0, Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    by_cases hin : s ∈ Icc s₁ s₂
    · rw [Set.indicator_of_mem hin]
      exact hC (φ s) (hcylφ s) (hbandφ s) M (fun j hj x => hM' s j hj x) s hs0 hin.2
    · rw [Set.indicator_of_notMem hin]
      have hout : s < s₁ ∨ s₂ < s := by
        by_contra hcon
        push Not at hcon
        exact hin ⟨hcon.1, hcon.2⟩
      rw [hzero s hout]
      simp [vtvR_zero]
end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
