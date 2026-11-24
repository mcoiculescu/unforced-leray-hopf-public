import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F04

/-!
# Part II-a, task `PartII-a:F04/2`: from a global window Laplacian to `HasPhaseOp (νΔ)` (decomposition)

Source of record: `the November 2 reference manuscript`, lines 1470-1480
("periodicity and a partition of unity then give the global distributional equation").

`LaplacianFieldToY` (`Sub/PartIIa_F04.lean`) is proved from five leaves:

* `PeriodicFieldToYq` : a strongly measurable `P`-periodic field, `L^r` on a period, is a jointly
  measurable representative of an element `a ∈ Y_r` (Fubini isometry, as `exists_isRep`);
* `PeriodPartition` : for every period `P > 0` there are finitely many smooth compactly supported
  `η_j`, each supported in a window `(c_j - 1, c_j + 1)`, with `∑_k ∑_j η_j(τ - kP) = 1`;
* `PeriodUnfold` : `∫₀^P G = ∑_j ∫_ℝ η_j G` for a `P`-periodic `G` integrable on a period;
* `WindowTestIdentityF04` : a window Laplacian satisfies the identity against `η(τ) Φ(τ, y)`
  (`ψ = η Φ` in `IsWindowLaplacian`, Fubini);
* `PhasePairSliceIntegrable` : `τ ↦ ∫ Ψ(τ, y) · w(τ)(y) dy` is integrable on a period.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.Short.PartIIa.Rep

/-- A strongly measurable `P`-periodic field of class `L^r` on a period is a representative of an
element of `Y_r` (source lines 1478-1480). -/
def PeriodicFieldToYq : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → ∀ (P : ℝ) [Fact (0 < P)] (Λ : ℝ × Space → CVec3),
    StronglyMeasurable Λ → (∀ᵐ τ : ℝ, (fun y => Λ (τ + P, y)) =ᵐ[volume] fun y => Λ (τ, y)) →
      ∫⁻ τ in Ioc 0 P, ∫⁻ y, ‖Λ (τ, y)‖ₑ ^ r.toReal < ⊤ → ∃ a : Yq P r, IsRep a Λ

/-- `η` is a finite family of window-supported smooth bumps forming a `P`-periodic partition of
unity. -/
def IsPeriodPartition (P : ℝ) {n : ℕ} (c : Fin n → ℝ) (η : Fin n → ℝ → ℝ) : Prop :=
  (∀ j, ContDiff ℝ ∞ (η j) ∧ HasCompactSupport (η j) ∧ tsupport (η j) ⊆ Ioo (c j - 1) (c j + 1)) ∧
    ∀ τ : ℝ, ∑' k : ℤ, ∑ j, η j (τ - k * P) = 1

/-- Existence of a periodic partition of unity subordinate to windows of length `2` (lines
1478-1480). -/
def PeriodPartition : Prop :=
  ∀ P : ℝ, 0 < P → ∃ (n : ℕ) (c : Fin n → ℝ) (η : Fin n → ℝ → ℝ), IsPeriodPartition P c η

/-- Unfolding a period integral with a periodic partition of unity. -/
def PeriodUnfold : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ (n : ℕ) (c : Fin n → ℝ) (η : Fin n → ℝ → ℝ), IsPeriodPartition P c η →
    ∀ G : ℝ → ℂ, Function.Periodic G P → IntegrableOn G (Ioc 0 P) →
      ∫ t in Ioc (0 : ℝ) P, G t = ∑ j, ∫ t, (η j t : ℂ) * G t

/-- The window identity against `η(τ) Φ(τ, y)`: from `IsWindowLaplacian ν τ₀ W Λ` with
`ψ = η Φ` (support in the window, `Δ` acts in `y` only), and Fubini. -/
def WindowTestIdentityF04 : Prop :=
  ∀ (P ν τ₀ : ℝ) (W Λ : ℝ × Space → CVec3), IsWindowLaplacian ν τ₀ W Λ →
    ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ Ioo (τ₀ - 1) (τ₀ + 1) →
      ∀ Φ : ℝ × Space → CVec3, IsPhaseTest P Φ →
        ∫ t, (η t : ℂ) * ∫ y, dotL (nuLapT ν Φ (t, y)) (W (t, y)) =
          ∫ t, (η t : ℂ) * ∫ y, dotL (Φ (t, y)) (Λ (t, y))

/-- Integrability over a period of the slice pairing of a phase test with `w ∈ Y_r`. -/
def PhasePairSliceIntegrable : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)] (P : ℝ) [Fact (0 < P)] (w : Yq P r) (Ψ : ℝ × Space → CVec3),
    IsPhaseTest P Ψ →
      IntegrableOn (fun t : ℝ => ∫ y, dotL (Ψ (t, y)) ((w (t : AddCircle P) : Space → CVec3) y))
        (Ioc 0 P)

/-- Reduction of `LaplacianFieldToY` to the five leaves. -/
theorem laplacianFieldToY_of (h1 : PeriodicFieldToYq) (h3 : PeriodPartition) (h4 : PeriodUnfold)
    (h5 : WindowTestIdentityF04) (h7 : PhasePairSliceIntegrable) : LaplacianFieldToY := by
  intro r _ hr P hP ν w W hW Λ hm hwin hper hfin
  obtain ⟨a, ha⟩ := h1 r hr P Λ hm hper hfin
  refine ⟨a, ?_⟩
  intro Φ hΦ
  obtain ⟨n, c, η, hpart⟩ := h3 P hP.out
  have hΨ : IsPhaseTest P (nuLapT ν Φ) := isPhaseTest_nuLapT hΦ ν
  rw [phasePair_eq_periodIntegral hΨ w, phasePair_eq_periodIntegral hΦ a, zero_add]
  congr 1
  have unfold : ∀ (Ψ' : ℝ × Space → CVec3), IsPhaseTest P Ψ' → ∀ v : Yq P r,
      ∫ t in Ioc (0 : ℝ) P, ∫ y, dotL (Ψ' (t, y)) ((v (t : AddCircle P) : Space → CVec3) y) =
        ∑ j, ∫ t, (η j t : ℂ) *
          ∫ y, dotL (Ψ' (t, y)) ((v (t : AddCircle P) : Space → CVec3) y) := by
    intro Ψ' hΨ' v
    refine h4 P hP.out n c η hpart _ ?_ (h7 r P v Ψ' hΨ')
    intro t
    have e : (((t + P : ℝ)) : AddCircle P) = (t : AddCircle P) := AddCircle.coe_add_period P t
    simp only [e, hΨ'.periodic]
  have conv : ∀ (Ψ' : ℝ × Space → CVec3) (v : Yq P r) (V : ℝ × Space → CVec3), IsRep v V →
      ∀ j, ∫ t, (η j t : ℂ) * ∫ y, dotL (Ψ' (t, y)) ((v (t : AddCircle P) : Space → CVec3) y) =
        ∫ t, (η j t : ℂ) * ∫ y, dotL (Ψ' (t, y)) (V (t, y)) := by
    intro Ψ' v V hV j
    refine integral_congr_ae ?_
    filter_upwards [hV.slice] with t ht
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [ht] with y hy
    rw [hy]
  rw [unfold _ hΨ w, unfold _ hΦ a]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [conv _ w W hW j, conv _ a Λ ha j]
  exact h5 P ν (c j) W Λ (hwin (c j)) (η j) (hpart.1 j).1 (hpart.1 j).2.1 (hpart.1 j).2.2 Φ hΦ

end UnforcedLeray.Short.PartIIa

#print axioms UnforcedLeray.Short.PartIIa.laplacianFieldToY_of
