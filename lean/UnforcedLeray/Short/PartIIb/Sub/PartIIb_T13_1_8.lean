import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.FlatGraphOrg

/-!
# `PartII-b:T13/1/8` decomposition: weak derivatives are local

Source: `the November 2 reference manuscript` lines 1928-1933 (window estimates give
the global derivatives of `T_0F`; weak derivatives are local). Three source-level facts: a finite
smooth decomposition of a test into window-supported tests, consistency of local weak derivatives on
overlaps (fundamental lemma), and measurable periodic gluing.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff

/-- Finite decomposition of a test (SP 1928-1933, smooth partition of unity in `s`, e.g. windows
`(a_k, 2a_k)`, `a_k = (3/2)^k`, `k ∈ ℤ`, meeting the compact support of `φ` finitely often): every
`IsCoordTest φ` is a finite sum of `IsCoordTest`s `ψ_k` with `tsupport ψ_k ⊆ winOpen (a_k)`,
and the transposes add up (linearity of the derivative, `v` smooth). -/
def WglDecomp : Prop :=
  ∀ v : Coord → Fin 3 → ℝ, (∀ j, ContDiff ℝ ∞ (fun x => v x j)) → ∀ φ : Coord → ℝ,
    IsCoordTest φ → ∃ (n : ℕ) (a : Fin n → ℝ) (ψ : Fin n → Coord → ℝ),
      (∀ k, 0 < a k ∧ IsCoordTest (ψ k) ∧ tsupport (ψ k) ⊆ winOpen (a k)) ∧
      (∀ x, φ x = ∑ k, ψ k x) ∧
      ∀ x, coordTranspose v dZero φ x = ∑ k, coordTranspose v dZero (ψ k) x

/-- Consistency on overlaps (SP 1928-1933): two local weak derivatives of `b`, on windows
`(a,2a)` and `(a',2a')`, agree a.e. on the intersection (fundamental lemma of the calculus of
variations, `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`, applied on the open
intersection; `g a` is locally integrable there because tests supported in the window have
integrable pairings). -/
def WglConsistency : Prop :=
  ∀ v : Coord → Fin 3 → ℝ, (∀ j, ContDiff ℝ ∞ (fun x => v x j)) → ∀ (b : CProf) (g : ℝ → CProf),
    (∀ a : ℝ, 0 < a → HasWeakVecOn (winOpen a) v dZero b (g a)) →
    ∀ a a' : ℝ, 0 < a → 0 < a' → ∀ᵐ x ∂(volume : Measure Coord),
      x ∈ winOpen a → x ∈ winOpen a' → g a x = g a' x

/-- Measurable periodic gluing (SP 1928-1933): a family `g a`, `a > 0`, of `q`-periodic measurable
profiles that agree a.e. on overlaps of windows is a.e. equal on each window to one `q`-periodic
measurable `Gl` (take `Gl x = g a_{k(x)} x` with `k(x)` the least index with `x.1` in a fixed
closed subinterval of the window `k`, depending only on `x.1`). -/
def WglMeasGlue : Prop :=
  ∀ (c : ℝ) (g : ℝ → CProf),
    (∀ a : ℝ, 0 < a → QPeriodic c (g a) ∧ AEStronglyMeasurable (g a) volume) →
    (∀ a a' : ℝ, 0 < a → 0 < a' → ∀ᵐ x ∂(volume : Measure Coord),
      x ∈ winOpen a → x ∈ winOpen a' → g a x = g a' x) →
    ∃ Gl : CProf, QPeriodic c Gl ∧ AEStronglyMeasurable Gl volume ∧
      ∀ a : ℝ, 0 < a → ∀ᵐ x ∂(volume : Measure Coord), x ∈ winOpen a → Gl x = g a x

theorem weakGlue_of (hD : WglDecomp) (hC : WglConsistency) (hG : WglMeasGlue) : WeakGlue := by
  intro v hv c b g hloc hper
  obtain ⟨Gl, hP, hM, hEq⟩ := hG c g hper (hC v hv b g hloc)
  refine ⟨Gl, ?_, hP, hM, fun a ha => hEq a ha⟩
  intro i
  have key : ∀ φ : Coord → ℝ, IsCoordTest φ →
      Integrable (fun x => b x i * (coordTranspose v dZero φ x : ℂ)) ∧
      Integrable (fun x => Gl x i * (φ x : ℂ)) ∧
      ∫ x, Gl x i * (φ x : ℂ) = ∫ x, b x i * (coordTranspose v dZero φ x : ℂ) := by
    intro φ hφ
    obtain ⟨n, a, ψ, hψ, hsum, hT⟩ := hD v hv φ hφ
    have loc : ∀ k, Integrable (fun x => b x i * (coordTranspose v dZero (ψ k) x : ℂ)) ∧
        Integrable (fun x => Gl x i * (ψ k x : ℂ)) ∧
        ∫ x, Gl x i * (ψ k x : ℂ) = ∫ x, b x i * (coordTranspose v dZero (ψ k) x : ℂ) := by
      intro k
      obtain ⟨ha, hψt, hsub⟩ := hψ k
      obtain ⟨I1, I2, E⟩ := hloc (a k) ha i (ψ k) hψt hsub
      have hae : (fun x => Gl x i * (ψ k x : ℂ)) =ᵐ[volume]
          (fun x => g (a k) x i * (ψ k x : ℂ)) := by
        filter_upwards [hEq (a k) ha] with x hx
        by_cases hxw : x ∈ winOpen (a k)
        · rw [hx hxw]
        · have : ψ k x = 0 := by
            by_contra hne
            exact hxw (hsub (subset_tsupport _ (Function.mem_support.mpr hne)))
          simp [this]
      refine ⟨I1, I2.congr hae.symm, ?_⟩
      rw [integral_congr_ae hae]; exact E
    have e1 : (fun x => Gl x i * (φ x : ℂ)) = fun x => ∑ k, Gl x i * (ψ k x : ℂ) := by
      funext x; rw [hsum x]; push_cast; rw [Finset.mul_sum]
    have e2 : (fun x => b x i * (coordTranspose v dZero φ x : ℂ)) =
        fun x => ∑ k, b x i * (coordTranspose v dZero (ψ k) x : ℂ) := by
      funext x; rw [hT x]; push_cast; rw [Finset.mul_sum]
    refine ⟨?_, ?_, ?_⟩
    · rw [e2]; exact integrable_finset_sum _ (fun k _ => (loc k).1)
    · rw [e1]; exact integrable_finset_sum _ (fun k _ => (loc k).2.1)
    · rw [e1, e2, integral_finset_sum _ (fun k _ => (loc k).2.1),
        integral_finset_sum _ (fun k _ => (loc k).1)]
      exact Finset.sum_congr rfl (fun k _ => (loc k).2.2)
  exact ⟨fun φ hφ => ⟨(key φ hφ).1, (key φ hφ).2.1⟩, fun φ hφ => (key φ hφ).2.2⟩

end UnforcedLeray.Short.IIb
