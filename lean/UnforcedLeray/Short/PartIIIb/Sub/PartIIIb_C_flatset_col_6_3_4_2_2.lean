import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_4_2

/-!
# `PartIII-b:C/flatset/col/6/3/4/2/2` (`vtvFubiniOpBound`): decomposition

Source of record: `the November 2 reference manuscript`
(line 4610: the integrated Duhamel identity `Y(s,φ) = ∫₀^s R(r,φ) dr`).

For the band `|x.2| ≤ R` of cylinder tests (a Fréchet space `E` under the `C^k` seminorms) and
`p(φ) = ∫_{(0,s₂]} ‖R(r,φ)‖ dr`:

* `p` is finite (last clause of `VtvHyps`), a seminorm (`VtvRLinAE` + `VtvPSub`), and lower
  semicontinuous for `C^∞` convergence (`VtvRBoundAE`: for a.e. `r`, `φ ↦ R(r,φ)` is bounded by
  finitely many seminorms; Fatou: `VtvPLsc`).
* `FrechetLscBound`: a finite, lower semicontinuous seminorm on a Fréchet space is bounded by a
  finite number of its seminorms (Baire / Banach-Steinhaus / gliding hump).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- Cylinder tests supported in the band `|x.2| ≤ R`. -/
def BandTest (c R : ℝ) (φ : ℝ × ℝ → ℝ) : Prop :=
  B0579.IsCylTest c φ ∧ ∀ x : ℝ × ℝ, R < |x.2| → φ x = 0

/-- All derivatives of order `≤ k` are bounded by `M`. -/
def CkSmall (k : ℕ) (M : ℝ) (φ : ℝ × ℝ → ℝ) : Prop :=
  ∀ j ≤ k, ∀ x : ℝ × ℝ, ‖iteratedFDeriv ℝ j φ x‖ ≤ M

/-- `φn → φ` in `C^∞` (uniformly, with every derivative). -/
def CkConv (φn : ℕ → ℝ × ℝ → ℝ) (φ : ℝ × ℝ → ℝ) : Prop :=
  ∀ j : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ x : ℝ × ℝ, ‖iteratedFDeriv ℝ j (φn n - φ) x‖ ≤ ε

/-- `p(φ) = ∫_{(0,s]} ‖R(r,φ)‖ dr`. -/
def vtvP {ν c : ℝ} (μ : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (ω g : ℝ → ℝ × ℝ → ℂ)
    (b : Chart → Fin 2 → ℂ) (s : ℝ) (φ : ℝ × ℝ → ℝ) : ℝ :=
  ∫ r in Ioc 0 s, ‖vtvR μ tr ω g b r φ‖

/-- **Finite lower semicontinuous seminorm on the Fréchet space of band tests is bounded by
finitely many `C^k` seminorms.**  (Source 4610 uses this closed-graph / Banach-Steinhaus step.)
Standard proof: Baire on `{p ≤ n}` (sequentially closed, hence closed, balanced, convex, absorbing)
in the Fréchet space `E`, or a gliding-hump construction of `φ = Σ ε_k φ_k` converging in every
`C^j`. -/
def FrechetLscBound : Prop :=
  ∀ (c R : ℝ) (p : (ℝ × ℝ → ℝ) → ℝ),
    (∀ φ, BandTest c R φ → 0 ≤ p φ) →
    (∀ φ ψ, BandTest c R φ → BandTest c R ψ → p (φ + ψ) ≤ p φ + p ψ) →
    (∀ (a : ℝ) φ, BandTest c R φ → p (a • φ) = |a| * p φ) →
    (∀ (φn : ℕ → ℝ × ℝ → ℝ) (φ : ℝ × ℝ → ℝ), (∀ n, BandTest c R (φn n)) → BandTest c R φ →
        CkConv φn φ → ∀ t : ℝ, (∀ᶠ n in atTop, p (φn n) ≤ t) → p φ ≤ t) →
    ∃ (k : ℕ) (C : ℝ), ∀ φ, BandTest c R φ → ∀ M : ℝ, CkSmall k M φ → p φ ≤ C * M

/-- **Linearity of `φ ↦ R(r,φ)` for a.e. `r > 0`** (source 4610).  For a.e. `r`, `f(r,·) ∈ L²(cell)`
(Fubini from clause 6 of `VtvHyps` on the bands `[1/n, n]`), so `⟨g(r),φ⟩ = ∫ f(r)×∇φ` (curl clause)
is linear on cylinder tests; the flow term is linear because `ω(r)·ψ` is integrable on the cell for
every cylinder test `ψ` (last clause) and the pieces `ψ_φ = νΔφ + v·∇φ` and `(b·∇E)φ` are linear in
`φ` (the second is integrable: `b(r) ∈ L²(cell)`, `∇E` bounded, `φ` band supported). -/
def VtvRLinAE : Prop :=
  ∀ (ν c μ : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (ω g : ℝ → ℝ × ℝ → ℂ)
    (b : Chart → Fin 2 → ℂ) (G : Chart → Fin 2 → Fin 2 → ℂ) (f : Chart → Fin 2 → ℂ),
    VtvHyps ν c μ tr ω g b G f →
      ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), ∀ φ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c φ →
        B0579.IsCylTest c ψ → ∀ a : ℝ,
          vtvR μ tr ω g b r (φ + ψ) = vtvR μ tr ω g b r φ + vtvR μ tr ω g b r ψ ∧
          vtvR μ tr ω g b r (a • φ) = (a : ℂ) * vtvR μ tr ω g b r φ

/-- **Pointwise seminorm bound of `R(r,·)` for a.e. `r > 0`** (source 4610): on the band of
height `R`, `‖R(r,φ)‖ ≤ C_r M` whenever the derivatives of `φ` of order `≤ k_r` are bounded by `M`.
Route: for a.e. `r`, `f(r,·) ∈ L²(cell)` so `|⟨g(r),φ⟩| ≤ ‖f(r)‖_{L¹(cell∩band)} ‖∇φ‖_∞`
(curl clause); the flow term equals `∫ b(r)·∇^⊥ψ_φ - ∫(b·∇E)φ` (Biot-Savart clause with the
cylinder test `ψ_φ = νΔφ + v·∇φ`) which is bounded by `‖b(r)‖_{L²(cell∩band)}` times the `C^3`
norm of `φ` times the bounded train derivatives (`IsBUCTrain`, derivatives of `E` are `v`-derivatives). -/
def VtvRBoundAE : Prop :=
  ∀ (ν c μ : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (ω g : ℝ → ℝ × ℝ → ℂ)
    (b : Chart → Fin 2 → ℂ) (G : Chart → Fin 2 → Fin 2 → ℂ) (f : Chart → Fin 2 → ℂ),
    VtvHyps ν c μ tr ω g b G f → ∀ R : ℝ,
      ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), ∃ (k : ℕ) (C : ℝ), ∀ φ, BandTest c R φ →
        ∀ M : ℝ, CkSmall k M φ → ‖vtvR μ tr ω g b r φ‖ ≤ C * M

/-- **`p_s` is a seminorm on cylinder tests** (from `VtvRLinAE` and the integrability of
`r ↦ R(r,φ)` on `(0,s]`, last clause of `VtvHyps`): triangle inequality and homogeneity. -/
def VtvPSub : Prop :=
  ∀ (ν c μ : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (ω g : ℝ → ℝ × ℝ → ℂ)
    (b : Chart → Fin 2 → ℂ) (G : Chart → Fin 2 → Fin 2 → ℂ) (f : Chart → Fin 2 → ℂ),
    VtvHyps ν c μ tr ω g b G f → ∀ s : ℝ, 0 < s → ∀ φ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c φ →
      B0579.IsCylTest c ψ → vtvP μ tr ω g b s (φ + ψ) ≤ vtvP μ tr ω g b s φ + vtvP μ tr ω g b s ψ ∧
        ∀ a : ℝ, vtvP μ tr ω g b s (a • φ) = |a| * vtvP μ tr ω g b s φ

/-- **Lower semicontinuity of `p_s` under `C^∞` convergence** (Fatou): from `VtvRLinAE` and
`VtvRBoundAE`, `R(r,φ_n) → R(r,φ)` for a.e. `r` (`R(r,φ_n) - R(r,φ) = R(r,φ_n - φ)` is bounded by
`C_r ε`), then `lintegral_liminf_le` on `ENNReal.ofReal ‖R(r,φ_n)‖` and finiteness of `p_s(φ)`. -/
def VtvPLsc : Prop :=
  ∀ (ν c μ : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (ω g : ℝ → ℝ × ℝ → ℂ)
    (b : Chart → Fin 2 → ℂ) (G : Chart → Fin 2 → Fin 2 → ℂ) (f : Chart → Fin 2 → ℂ),
    VtvHyps ν c μ tr ω g b G f → ∀ s R : ℝ, 0 < s →
      ∀ (φn : ℕ → ℝ × ℝ → ℝ) (φ : ℝ × ℝ → ℝ), (∀ n, BandTest c R (φn n)) → BandTest c R φ →
        CkConv φn φ → ∀ t : ℝ, (∀ᶠ n in atTop, vtvP μ tr ω g b s (φn n) ≤ t) →
          vtvP μ tr ω g b s φ ≤ t

theorem vtvFubiniOpBound_of (hFr : FrechetLscBound) (hS : VtvPSub) (hL : VtvPLsc) :
    VtvFubiniOpBound := by
  intro ν c μ tr ω g b G f H s₂ R
  by_cases hs : 0 < s₂
  · obtain ⟨k, C, hkC⟩ := hFr c R (vtvP μ tr ω g b s₂)
      (fun φ _ => integral_nonneg fun _ => norm_nonneg _)
      (fun φ ψ hφ hψ => (hS ν c μ tr ω g b G f H s₂ hs φ ψ hφ.1 hψ.1).1)
      (fun a φ hφ => (hS ν c μ tr ω g b G f H s₂ hs φ φ hφ.1 hφ.1).2 a)
      (fun φn φ hn hφ hc t ht => hL ν c μ tr ω g b G f H s₂ R hs φn φ hn hφ hc t ht)
    refine ⟨k, C, ?_⟩
    intro φ hcyl hband M hM s hs0 hss
    have hbd : vtvP μ tr ω g b s₂ φ ≤ C * M := hkC φ ⟨hcyl, hband⟩ M hM
    obtain ⟨h1, h2, _⟩ := H.2.2.2.2.2.2.2.1 φ hcyl s₂ hs
    have hint : IntegrableOn (fun r => vtvR μ tr ω g b r φ) (Ioc 0 s₂) := by
      refine (h1.add h2).congr_fun (fun r _ => ?_) measurableSet_Ioc
      simp only [vtvR, mul_add, Pi.add_apply]
    calc ∫ r in Ioc 0 s, ‖vtvR μ tr ω g b r φ‖
        ≤ ∫ r in Ioc 0 s₂, ‖vtvR μ tr ω g b r φ‖ :=
          setIntegral_mono_set hint.norm
            (Filter.Eventually.of_forall fun _ => norm_nonneg _)
            (Ioc_subset_Ioc_right hss).eventuallyLE
      _ ≤ C * M := hbd
  · exact ⟨0, 0, fun φ _ _ M _ s hs0 hss => absurd (lt_of_lt_of_le hs0 hss) hs⟩

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
