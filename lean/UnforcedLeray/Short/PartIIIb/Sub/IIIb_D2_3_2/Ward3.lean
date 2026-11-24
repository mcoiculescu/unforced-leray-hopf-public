import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Defs

/-!
# Decomposition of `WardWeakFromPointwise` (source 4260-4282)

Source: `the November 2 reference manuscript`.
The weak form for smooth inputs splits into: the integration by parts `WardIBPLoc` against phase
tests (source 4268-4270; no decay, `Dense/IBPLoc.lean` proves it from the facts of `WardIBP`),
applied to the regularized Ward fields (`Dense/Reg.lean`), the identification `WardLifts` of the
pinned Ward fields with the pointwise fields `wardH`, `wardE` (`IsWardPinned`, source 4161-4174),
and the identification `WardStressLift` of the physical stress of `M(Y+h)` with
`U⊗(Y+h) + (Y+h)⊗U` (`IsExactMultiplier`, source 4147).  The pairings see the raw and the
regularized fields alike (they differ only on the axis: `pairF_congr_offAxis'`,
`stressPair_congr_offAxis`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- The symmetrized product `(a ⊗ b + b ⊗ a)_{ij} = a_ib_j + b_ia_j` (source 4147). -/
def symProd (a b : Space) : Matrix (Fin 3) (Fin 3) ℝ := fun i j => a i * b j + b i * a j

/-- **Integration by parts** (source 4268-4270): `H, Y, E` smooth, `P`-periodic in `τ`, of
Schwartz decay, `U`, `q` smooth and `P`-periodic with polynomial growth, and the classical identity
`D_μH + div(U⊗H + H⊗U) + div(U⊗Y + Y⊗U) - E = ∇q`.  Then for every solenoidal phase test `Φ`,
`⟨D_μᵗΦ, H⟩ = ⟨Φ, E⟩ + ⟨U⊗(Y+H) + (Y+H)⊗U, ∇Φ⟩` (the gradient is killed by `div Φ = 0`,
the divergence gives `stressPair`, periodicity removes the `τ`-boundary term). -/
def WardIBP (ν μ P : ℝ) : Prop :=
  ∀ (U H Y E : ℝ → Space → Space) (q : ℝ → Space → ℝ),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => U x.1 x.2) →
    (∀ τ y, U (τ + P) y = U τ y) →
    (∃ (C : ℝ) (k : ℕ), ∀ τ y, ‖U τ y‖ ≤ C * (1 + ‖y‖) ^ k ∧
      ‖fderiv ℝ (U τ) y‖ ≤ C * (1 + ‖y‖) ^ k) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => q x.1 x.2) →
    (∃ (C : ℝ) (k : ℕ), ∀ τ y, |q τ y| ≤ C * (1 + ‖y‖) ^ k) →
    (∀ F ∈ ({H, Y, E} : Set (ℝ → Space → Space)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => F x.1 x.2) ∧
      IsSchwartzDecay F ∧ ∀ τ y, F (τ + P) y = F τ y) →
    (∀ τ y, physDmu ν μ H τ y + physDivSym (U τ) (H τ) y + physDivSym (U τ) (Y τ) y - E τ y =
      physGrad (q τ) y) →
    ∀ Φ : ℝ × Space → CVec3, IsSolTest P Φ →
      pairF P (fun x => L0T ν Φ x + (μ : ℂ) • Φ x) (fun x => B0412.realC (H x.1 x.2)) =
        pairF P Φ (fun x => B0412.realC (E x.1 x.2)) +
          stressPair P (fun x => symProd (U x.1 x.2) (Y x.1 x.2 + H x.1 x.2)) Φ

/-- **Integration by parts against phase tests** (source 4268-4270), the form used by the weak
equation: `WardIBP` without its decay and growth hypotheses.  A phase test has bounded spatial
support (`IsPhaseTest.bounded_support`), so only the smoothness of `U, q, H, Y, E` and the
periodicity of `H` enter; the Ward fields of the separated kernel decay only like `|y|^{-4}`
(`sep:kernel`, 3604-3610).  Proved as `wardIBPLoc_proved` in `Dense/IBPLoc.lean`. -/
def WardIBPLoc (ν μ P : ℝ) : Prop :=
  ∀ (U H Y E : ℝ → Space → Space) (q : ℝ → Space → ℝ),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => U x.1 x.2) →
    (∀ τ y, U (τ + P) y = U τ y) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => q x.1 x.2) →
    (∀ F ∈ ({H, Y, E} : Set (ℝ → Space → Space)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => F x.1 x.2) ∧
      ∀ τ y, F (τ + P) y = F τ y) →
    (∀ τ y, physDmu ν μ H τ y + physDivSym (U τ) (H τ) y + physDivSym (U τ) (Y τ) y - E τ y =
      physGrad (q τ) y) →
    ∀ Φ : ℝ × Space → CVec3, IsSolTest P Φ →
      pairF P (fun x => L0T ν Φ x + (μ : ℂ) • Φ x) (fun x => B0412.realC (H x.1 x.2)) =
        pairF P Φ (fun x => B0412.realC (E x.1 x.2)) +
          stressPair P (fun x => symProd (U x.1 x.2) (Y x.1 x.2 + H x.1 x.2)) Φ

-- `AxiNoSwirlPt` (pointwise axisymmetry without swirl, source 121-124) is in `Defs.lean`.

section Ward

variable {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff] [NormedSpace ℝ Aff]
  [CompleteSpace Aff]

/-- **Lift identification** (source 4161-4174, 4276-4282): under `IsWardPinned`, if `g₁, g₂`
represent `χ_oT` and `g₁ + g₂` is a `SmoothWardInput`, the lifts of `B.hf T`, `B.Ef T`,
`B.Yf T + B.hf T` are `wardH`, `wardE`, `wardY + wardH` (a.e., since the pinned coefficient
formulas are their own lifts: `liftH`, `liftE`, `liftYH`), so all pairings against `Ψ` agree. -/
def WardLifts (B : ReturnBase c mZ ρb γ ν Aff) (hc : 0 < c) (ε : ℝ) (hε : 0 < ε) (hν : 0 < ν) (μ : ℝ) {χo : ℝ → ℝ}
    (hχo : IsOutwardCutoff χo) (χy : ℝ → ℝ) (U : ℝ → SpatialField) (p : ℝ → Space → ℝ) :
    Prop :=
  IsWardPinned B ε μ hχo χy U p →
    ∀ (T : StrG c mZ ρb γ ν) (g₁ g₂ : Chart → Ten3),
      ((chiOStr c mZ ρb γ ν hχo T).fst : Chart → Ten3) =ᵐ[gainZ1Measure c mZ γ ν] g₁ →
      ((chiOStr c mZ ρb γ ν hχo T).snd : Chart → Ten3) =ᵐ[gainHTMeasure c ρb γ ν] g₂ →
      SmoothWardInput ν μ ε⁻¹ c χy U p (g₁ + g₂) →
        ∀ Ψ : ℝ × Space → CVec3,
          pairF (2 * ε * c) Ψ (velPhys ε⁻¹ c (B.hf T)) =
            pairF (2 * ε * c) Ψ
              (fun x => B0412.realC (wardH ν μ ε⁻¹ c χy U (g₁ + g₂) x.1 x.2)) ∧
          pairF (2 * ε * c) Ψ (velPhys ε⁻¹ c (B.Ef T)) =
            pairF (2 * ε * c) Ψ
              (fun x => B0412.realC (wardE ν μ ε⁻¹ c χy U p (g₁ + g₂) x.1 x.2)) ∧
          velPhys ε⁻¹ c (B.Yf T + B.hf T) =ᵐ[volume]
            fun x => B0412.realC (wardY ν μ ε⁻¹ c χy (g₁ + g₂) x.1 x.2 +
              wardH ν μ ε⁻¹ c χy U (g₁ + g₂) x.1 x.2)

/-- **Stress lift** (source 4147, 4163-4164): under `IsExactMultiplier` the physical stress of
`M(Y + h)` is `U ⊗ (Y+h) + (Y+h) ⊗ U` for `U = V + r_b`, as far as `stressPair` sees it. -/
def WardStressLift (B : ReturnBase c mZ ρb γ ν Aff) (hc : 0 < c) (ε : ℝ) (hε : 0 < ε) (hν : 0 < ν) (μ : ℝ) {χo : ℝ → ℝ}
    (hχo : IsOutwardCutoff χo) (χy : ℝ → ℝ) (V rb : ℝ → SpatialField) (p : ℝ → Space → ℝ) :
    Prop :=
  IsExactMultiplier B ε⁻¹ V rb →
  (∀ τ, AxiNoSwirlPt (fun y => V τ y + rb τ y)) →
  (∀ τ y, V (τ + 2 * ε * c) y + rb (τ + 2 * ε * c) y = V τ y + rb τ y) →
  IsWardPinned B ε μ hχo χy (fun τ y => V τ y + rb τ y) p →
    ∀ (T : StrG c mZ ρb γ ν) (g₁ g₂ : Chart → Ten3),
      ((chiOStr c mZ ρb γ ν hχo T).fst : Chart → Ten3) =ᵐ[gainZ1Measure c mZ γ ν] g₁ →
      ((chiOStr c mZ ρb γ ν hχo T).snd : Chart → Ten3) =ᵐ[gainHTMeasure c ρb γ ν] g₂ →
      SmoothWardInput ν μ ε⁻¹ c χy (fun τ y => V τ y + rb τ y) p (g₁ + g₂) →
        ∀ Φ : ℝ × Space → CVec3, IsSolTest (2 * ε * c) Φ →
          stressPair (2 * ε * c) (strPhys ε⁻¹ c (strSum (B.M (B.Yf T + B.hf T)))) Φ =
            stressPair (2 * ε * c)
              (fun x => symProd (V x.1 x.2 + rb x.1 x.2)
                (wardY ν μ ε⁻¹ c χy (g₁ + g₂) x.1 x.2 + wardH ν μ ε⁻¹ c χy
                  (fun τ y => V τ y + rb τ y) (g₁ + g₂) x.1 x.2)) Φ

theorem wardWeakFromPointwise_of_parts (B : ReturnBase c mZ ρb γ ν Aff) (hc : 0 < c) {ε μ : ℝ}
    (hε : 0 < ε) (hν : 0 < ν)
    {χo χy : ℝ → ℝ} (hχo : IsOutwardCutoff χo) {V rb : ℝ → SpatialField}
    {p : ℝ → Space → ℝ}
    (hibp : WardIBPLoc ν μ (2 * ε * c))
    (hl : WardLifts B hc ε hε hν μ hχo χy (fun τ y => V τ y + rb τ y) p)
    (hs : WardStressLift B hc ε hε hν μ hχo χy V rb p) :
    WardWeakFromPointwise B ε μ hχo χy V rb p := by
  intro h1 hUp hM hax hW T hT Φ hΦ
  obtain ⟨g₁, g₂, hg1, hg2, hin⟩ := hT
  have hP : (2 * c / ε⁻¹ : ℝ) = 2 * ε * c := by rw [div_inv_eq_mul]; ring
  -- the pointwise identity of the regularized displacement, integrated by parts
  have hcl := h1 _ hUp (wardXr ν μ ε⁻¹ c χy (g₁ + g₂)) hin.smoothX hin.solenoidalX
  have hibp' := hibp (fun τ y => V τ y + rb τ y)
    (wardHr ν μ ε⁻¹ c χy (fun τ y => V τ y + rb τ y) (g₁ + g₂))
    (wardYr ν μ ε⁻¹ c χy (g₁ + g₂))
    (wardEr ν μ ε⁻¹ c χy (fun τ y => V τ y + rb τ y) p (g₁ + g₂))
    (fun τ y => ∑ j : Fin 3, wardXr ν μ ε⁻¹ c χy (g₁ + g₂) τ y j * physGrad (p τ) y j)
    hUp.smoothU hUp.periodicU hin.smoothQ ?_ hcl Φ hΦ
  · have hl' := hl hW T g₁ g₂ hg1 hg2 hin
    have hs' := hs hM hax (fun τ y => by have := hUp.periodicU τ y; simpa using this) hW T g₁ g₂
      hg1 hg2 hin Φ hΦ
    -- the raw fields of the pins agree with the regularized ones off the axis
    have eH : ∀ Ψ : ℝ × Space → CVec3,
        pairF (2 * ε * c) Ψ (fun x => B0412.realC
          (wardH ν μ ε⁻¹ c χy (fun τ y => V τ y + rb τ y) (g₁ + g₂) x.1 x.2)) =
        pairF (2 * ε * c) Ψ (fun x => B0412.realC
          (wardHr ν μ ε⁻¹ c χy (fun τ y => V τ y + rb τ y) (g₁ + g₂) x.1 x.2)) :=
      fun Ψ => pairF_congr_offAxis' Ψ _ _ fun τ y hy => by
        simp only [wardHr_eq_of_not_mem ν μ ε⁻¹ c χy (g₁ + g₂) _ τ hy]
    have eE : pairF (2 * ε * c) Φ (fun x => B0412.realC
          (wardE ν μ ε⁻¹ c χy (fun τ y => V τ y + rb τ y) p (g₁ + g₂) x.1 x.2)) =
        pairF (2 * ε * c) Φ (fun x => B0412.realC
          (wardEr ν μ ε⁻¹ c χy (fun τ y => V τ y + rb τ y) p (g₁ + g₂) x.1 x.2)) :=
      pairF_congr_offAxis' Φ _ _ fun τ y hy => by
        simp only [wardEr_eq_of_not_mem ν μ ε⁻¹ c χy (g₁ + g₂) _ p τ hy]
    have eS : stressPair (2 * ε * c)
          (fun x => symProd (V x.1 x.2 + rb x.1 x.2)
            (wardY ν μ ε⁻¹ c χy (g₁ + g₂) x.1 x.2 + wardH ν μ ε⁻¹ c χy
              (fun τ y => V τ y + rb τ y) (g₁ + g₂) x.1 x.2)) Φ =
        stressPair (2 * ε * c)
          (fun x => symProd (V x.1 x.2 + rb x.1 x.2)
            (wardYr ν μ ε⁻¹ c χy (g₁ + g₂) x.1 x.2 + wardHr ν μ ε⁻¹ c χy
              (fun τ y => V τ y + rb τ y) (g₁ + g₂) x.1 x.2)) Φ :=
      stressPair_congr_offAxis _ _ Φ fun τ y hy => by
        simp only [wardYr_eq_of_not_mem ν μ ε⁻¹ c χy (g₁ + g₂) τ hy,
          wardHr_eq_of_not_mem ν μ ε⁻¹ c χy (g₁ + g₂) _ τ hy]
    rw [(hl' _).1, (hl' Φ).2.1, hs', eH, eE, eS]
    exact hibp'
  · intro F hF
    have hF' : F = wardHr ν μ ε⁻¹ c χy (fun τ y => V τ y + rb τ y) (g₁ + g₂) ∨
        F = wardYr ν μ ε⁻¹ c χy (g₁ + g₂) ∨
        F = wardEr ν μ ε⁻¹ c χy (fun τ y => V τ y + rb τ y) p (g₁ + g₂) := by simpa using hF
    rcases hF' with rfl | rfl | rfl
    · exact ⟨hin.smoothH, fun τ y => by rw [← hP]; exact hin.periodicH τ y⟩
    · exact ⟨hin.smoothY, fun τ y => by rw [← hP]; exact hin.periodicY τ y⟩
    · exact ⟨hin.smoothE, fun τ y => by rw [← hP]; exact hin.periodicE τ y⟩

end Ward

end UnforcedLeray.Short.PartIIIb.Concrete
