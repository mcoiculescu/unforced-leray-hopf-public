import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2_3

/-!
# `PartII-b:F2/3/1` (`Sub/PartII-b_F2_3_1.lean`): decomposition of `PlanarFrozenEulerStep`

Source of record: `the November 2 reference manuscript` (SP) lines 841-852,
931-953, 2137-2140, 2145-2171.

Leaves: `PlanarEulerFamily` (the Euler semigroup `E_pl` as the realified `eulerGroupDil (1+σ)`,
its Duhamel identity against `T_pl` and `A_pl`, SP 2121-2123, 931-953),
`PlanarModesInXm` (the real planar direct modes `(2 Re J_a q, -2 Im J_a q)` as a continuous
bounded family `E2 → Xm m`, SP 2167-2171), `PlanarEulerSpectral` (the coordinate functional,
rotation action, commuting projection and uniform complement bound, SP 931-953, 2137-2140,
2145-2171), `PlanarSeedIdentification` (uniqueness of the growing pair, SP 593-602).
Assembly: `planarFrozenEulerStep_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal Matrix

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411

namespace PlanarFrozenF231

/-- Data of the frozen planar Euler semigroup `E` and transport group `T` on `Icc 0 Sig`:
strongly continuous semigroup, isometric transport group acting by `frozenRadialFlow`,
existence of the planar interaction operator, and the mild Duhamel identity. -/
def EulerData (m Sig : ℝ) (E T : ℝ → ℝ → (Xm m →L[ℝ] Xm m)) : Prop :=
  (∀ σ ∈ Icc 0 Sig,
    E σ 0 = ContinuousLinearMap.id ℝ (Xm m) ∧
    (∀ τ₁ τ₂ : ℝ, 0 ≤ τ₁ → 0 ≤ τ₂ → E σ (τ₁ + τ₂) = (E σ τ₁).comp (E σ τ₂)) ∧
    ∀ f : Xm m, ContinuousOn (fun τ => E σ τ f) (Ici 0)) ∧
  (∀ σ ∈ Icc 0 Sig,
    T σ 0 = ContinuousLinearMap.id ℝ (Xm m) ∧
    (∀ τ₁ τ₂ : ℝ, T σ (τ₁ + τ₂) = (T σ τ₁).comp (T σ τ₂)) ∧
    (∀ τ : ℝ, ∀ f : Xm m, ‖T σ τ f‖ = ‖f‖) ∧
    (∀ f : Xm m, Continuous (fun τ => T σ τ f)) ∧
    (∀ τ : ℝ, ∀ f : Xm m,
      (T σ τ f : B0579.Plane → ℝ) =ᵐ[planeMeasure m]
        fun x => f (PartIIbF23Sub.frozenRadialFlow σ τ x))) ∧
  (∀ σ ∈ Icc 0 Sig, ∃ A : Xm m →L[ℝ] Xm m, IsPlanarInteractionOp m σ A) ∧
  (∀ σ ∈ Icc 0 Sig, ∀ A : Xm m →L[ℝ] Xm m, IsPlanarInteractionOp m σ A →
    ∀ τ : ℝ, 0 ≤ τ → ∀ f : Xm m,
      IntervalIntegrable (fun r => T σ (τ - r) (A (E σ r f))) volume 0 τ ∧
      E σ τ f = T σ τ f + ∫ r in (0 : ℝ)..τ, T σ (τ - r) (A (E σ r f)))

/-- **Leaf (a)+(b)**: the frozen planar Euler family exists (`E_pl σ τ` = realification of
`Planar.eulerGroupDil (1+σ) τ` on `Xm m ≅ Planar.L2w m`; Duhamel from `expSec_eq_duhamel`). -/
def PlanarEulerFamily : Prop :=
  ∀ m : ℝ, 8 < m → ∀ Sig : ℝ, 0 < Sig →
    ∃ E T : ℝ → ℝ → (Xm m →L[ℝ] Xm m), EulerData m Sig E T

/-- **Leaf (c1)**: the planar direct modes `(2 Re J_a q, -2 Im J_a q)`, `a = 1+σ`, define a
continuous bounded family `ι : E2 → Xm m` on `Icc 0 Sig` (SP 2167-2171). -/
def PlanarModesInXm : Prop :=
  ∀ m : ℝ, 8 < m → ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
    ∃ (M : ℝ) (ι : ℝ → (E2 →L[ℝ] Xm m)),
      1 ≤ M ∧ ContinuousOn ι (Icc 0 Sig) ∧ (∀ σ ∈ Icc 0 Sig, ‖ι σ‖ ≤ M) ∧
      ∀ σ ∈ Icc 0 Sig, ∀ α : E2,
        (ι σ α : B0579.Plane → ℝ) =ᵐ[planeMeasure m]
          fun x => ∑ i : Fin 2, α i * planarFrozenDirectMode q (1 + σ) i x

/-- **Leaf (c2)**: for the Euler family `E` of `EulerData` and the direct modes `ι`, there is a
continuous bounded coordinate functional `π` with `π ∘ ι = id`, rotation action of `E` on
`ι`, commuting projection `ι ∘ π`, and the complement bound for every `η > 0`
(SP 931-953, 2137-2140, 2145-2171; seed pair, `short-seed-dilation`). -/
def PlanarEulerSpectral : Prop :=
  ∀ m : ℝ, 8 < m → ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ ι : ℝ → (E2 →L[ℝ] Xm m), ContinuousOn ι (Icc 0 Sig) →
    (∀ σ ∈ Icc 0 Sig, ∀ α : E2,
      (ι σ α : B0579.Plane → ℝ) =ᵐ[planeMeasure m]
        fun x => ∑ i : Fin 2, α i * planarFrozenDirectMode q (1 + σ) i x) →
  ∀ E T : ℝ → ℝ → (Xm m →L[ℝ] Xm m), EulerData m Sig E T →
    ∃ (M : ℝ) (π : ℝ → (Xm m →L[ℝ] E2)),
      1 ≤ M ∧ ContinuousOn π (Icc 0 Sig) ∧
      (∀ σ ∈ Icc 0 Sig, (π σ).comp (ι σ) = ContinuousLinearMap.id ℝ E2 ∧ ‖π σ‖ ≤ M) ∧
      (∀ σ ∈ Icc 0 Sig, ∀ τ : ℝ, 0 ≤ τ →
        let θ : ℝ := lam.im * τ / (1 + σ) ^ 2
        let r : ℝ := Real.exp (lam.re * τ / (1 + σ) ^ 2)
        (E σ τ).comp (ι σ) =
          (ι σ).comp
            (LinearMap.toContinuousLinearMap
              (Matrix.toEuclideanLin ![![r * Real.cos θ, -r * Real.sin θ],
                                       ![r * Real.sin θ,  r * Real.cos θ]]))) ∧
      (∀ σ ∈ Icc 0 Sig, ∀ τ : ℝ, 0 ≤ τ →
        (E σ τ).comp ((ι σ).comp (π σ)) = ((ι σ).comp (π σ)).comp (E σ τ)) ∧
      (∀ η : ℝ, 0 < η → ∃ C_η : ℝ, 0 < C_η ∧
        ∀ σ ∈ Icc 0 Sig, ∀ τ : ℝ, 0 ≤ τ →
          ‖(E σ τ).comp (ContinuousLinearMap.id ℝ (Xm m) - (ι σ).comp (π σ))‖ ≤
            C_η * Real.exp (η * τ))

/-- **Leaf (d)**: seed identification (Blueprint G1; SP 593-602): any two growing eigenpairs
have the same eigenvalue and proportional profiles. Also an input of `PartII-b:F2/3/2`. -/
def PlanarSeedIdentification : Prop :=
  ∀ (lam₁ lam₂ : ℂ) (q₁ q₂ : Blueprint.Planar.Profile),
    Blueprint.Planar.IsGrowingEigenpair lam₁ q₁ →
    Blueprint.Planar.IsGrowingEigenpair lam₂ q₂ →
    lam₁ = lam₂ ∧ ∃ c : ℂ, c ≠ 0 ∧
      q₁ =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun r => c * q₂ r

end PlanarFrozenF231

open PlanarFrozenF231 in
/-- Assembly of `PlanarFrozenEulerStep` from the three leaves. -/
theorem planarFrozenEulerStep_of
    (hE : PlanarEulerFamily) (hM : PlanarModesInXm) (hS : PlanarEulerSpectral) :
    PlanarFrozenEulerStep := by
  intro m hm Sig lam q hSig hEig
  obtain ⟨E, T, hD⟩ := hE m hm Sig hSig
  obtain ⟨M₁, ι, hM₁, hιc, hιb, hιae⟩ := hM m hm Sig lam q hSig hEig
  obtain ⟨M₂, π, hM₂, hπc, hπ, hrot, hcomm, hcompl⟩ :=
    hS m hm Sig lam q hSig hEig ι hιc hιae E T hD
  obtain ⟨hsemi, hT, -, hduh⟩ := hD
  refine ⟨max M₁ M₂, ι, π, E, hM₁.trans (le_max_left _ _), ⟨hιc, hπc⟩, ?_, hιae, hsemi,
    hrot, hcomm, hcompl, ⟨T, hT, hduh⟩⟩
  intro σ hσ
  exact ⟨(hπ σ hσ).1, (hιb σ hσ).trans (le_max_left _ _),
    (hπ σ hσ).2.trans (le_max_right _ _)⟩

end UnforcedLeray.Short.IIb
