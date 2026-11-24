import UnforcedLeray.Infra.RealStructure.Basic
import UnforcedLeray.Infra.RealStructure.Riesz
import UnforcedLeray.Infra.RealStructure.Lp
import UnforcedLeray.Infra.RealStructure.RieszProjection

/-!
# Real structures and Riesz projections (umbrella file)

Manuscript `paper/main.tex`, line 361: "Both projections preserve real fields". The
localization works with the period map `𝓜 = E(𝒯, 0)` on the complexification of
`X = H¹_div`; `𝓜` commutes with pointwise complex conjugation, and the Riesz projection `P_-`
over the circle `|ξ| = e^{β𝒯}` and `P_+ = I - P_-` must map real fields to real fields.

The development is split into
* `RealStructure/Basic.lean`: `Conjugation X` (a conjugate-linear isometric involution of a
  complex normed space), real vectors `fixedSubmodule` (closed real subspace,
  `re`/`im` decomposition), conjugation of operators `conjOp`, `CommutesWith`, the resolvent
  identity `CommutesWith.resolvent_apply_conj` and conjugation invariance of the resolvent set
  and the spectrum;
* `RealStructure/Riesz.lean`: conjugation of circle integrals and the Riesz integral
  `rieszIntegral T c r = (2πi)⁻¹ ∮_{C(c,r)} (z - T)⁻¹ dz`, which commutes with `J` for a real
  centre (`CommutesWith.rieszIntegral_commutesWith`);
* `RealStructure/RieszProjection.lean`: the same for `rieszProj`, `contourOp` and
  `rieszOuterInv` of `Infra/RieszProjection/Basic.lean` (`P_-`, `P_+ = 1 - P_-`, `𝓜_+⁻¹`),
  and `J`-invariance of `P_± X`;
* `RealStructure/Lp.lean`: the conjugations of `ℂ`, of invariant subspaces, of `PiLp`
  products and of `L^p` fields, and the identification of real fields
  (`realFieldsEquiv`).

This file adds the operator form of the resolvent identity and the specializations to the
complex velocity fields `L²(μ; ℂ³)` and to the `H¹` graph-norm ambient space
`PiLp 2 (Fin 4 → L²(μ; ℂ³))`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Infra.RealStructure

namespace Conjugation

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {J : Conjugation X}

/-- **Resolvent and conjugation, operator form.** For `T` commuting with `J`,
`(z - T)⁻¹ ∘ J = J ∘ (conj z - T)⁻¹` as continuous conjugate-linear maps, for every `z ∈ ℂ`. -/
theorem CommutesWith.resolvent_comp_toCLM {T : X →L[ℂ] X} (hT : J.CommutesWith T) (z : ℂ) :
    (resolvent T z).comp J.toCLM = J.toCLM.comp (resolvent T (conj z)) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, toCLM_apply]
  exact hT.resolvent_apply_conj z x

/-- The Riesz integral of a `J`-commuting operator over a circle centred at `0` commutes with
`J`, in operator form. -/
theorem CommutesWith.rieszIntegral_comp_toCLM {T : X →L[ℂ] X} (hT : J.CommutesWith T)
    (r : ℝ) : (rieszIntegral T 0 r).comp J.toCLM = J.toCLM.comp (rieszIntegral T 0 r) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, toCLM_apply]
  exact ((hT.rieszIntegral_zero_commutesWith r) x).symm

end Conjugation

/-! ### Complex velocity fields -/

section Velocity

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

/-- Pointwise complex conjugation on complex velocity fields `L²(μ; ℂ³)`. -/
abbrev velocityConj : Conjugation (Lp (EuclideanSpace ℂ (Fin 3)) 2 μ) :=
  Conjugation.lpEuclidean (Fin 3) 2 μ

variable {μ}

theorem coeFn_velocityConj (f : Lp (EuclideanSpace ℂ (Fin 3)) 2 μ) :
    ∀ᵐ a ∂μ, ∀ i, velocityConj μ f a i = conj (f a i) :=
  Conjugation.coeFn_lpEuclidean f

/-- A complex velocity field is real iff its three components are a.e. real. -/
theorem mem_fixedSubmodule_velocityConj_iff (f : Lp (EuclideanSpace ℂ (Fin 3)) 2 μ) :
    f ∈ (velocityConj μ).fixedSubmodule ↔ ∀ᵐ a ∂μ, ∀ i, (f a i).im = 0 :=
  Conjugation.mem_fixedSubmodule_lpEuclidean_iff f

/-- A complex velocity field is real iff it is the complexification of a real-valued
`L²(μ; ℝ³)` field. -/
theorem mem_fixedSubmodule_velocityConj_iff_exists (f : Lp (EuclideanSpace ℂ (Fin 3)) 2 μ) :
    f ∈ (velocityConj μ).fixedSubmodule ↔
      ∃ g : Lp (EuclideanSpace ℝ (Fin 3)) 2 μ, Conjugation.complexifyLp g = f :=
  Conjugation.mem_fixedSubmodule_lpEuclidean_iff_exists f

variable (μ) in
/-- The real velocity fields `L²(μ; ℝ³)` are real-linearly isometric to the real vectors of
`L²(μ; ℂ³)`. -/
abbrev realVelocityEquiv :
    Lp (EuclideanSpace ℝ (Fin 3)) 2 μ ≃ₗᵢ[ℝ] (velocityConj μ).fixedSubmodule :=
  Conjugation.realFieldsEquiv (Fin 3) 2 μ

variable (μ) in
/-- The componentwise conjugation on the complex `H¹` graph-norm ambient space
`PiLp 2 (Fin 4 → L²(μ; ℂ³))` (a field and its three first derivatives). A complex Sobolev space
realized as a conjugation-invariant subspace `V` of it carries the restricted conjugation
`(h1AmbientConj μ).restrict V hV`. -/
abbrev h1AmbientConj :
    Conjugation (PiLp 2 (fun _ : Fin 4 => Lp (EuclideanSpace ℂ (Fin 3)) 2 μ)) :=
  Conjugation.piLp 2 (fun _ => velocityConj μ)

/-- A vector of the `H¹` ambient space is real iff all four of its components are real
velocity fields. -/
theorem mem_fixedSubmodule_h1AmbientConj_iff
    (F : PiLp 2 (fun _ : Fin 4 => Lp (EuclideanSpace ℂ (Fin 3)) 2 μ)) :
    F ∈ (h1AmbientConj μ).fixedSubmodule ↔ ∀ k, F k ∈ (velocityConj μ).fixedSubmodule :=
  Conjugation.mem_fixedSubmodule_piLp_iff 2 _ F

end Velocity

end UnforcedLeray.Infra.RealStructure
