import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_7

/-!
# `SigmaMRot`: the Cartesian source is rotation covariant (task `PartIII-b:C/srcL/7/3`)

Source of record: `the November 2 reference manuscript`, lines 4771-4775
(`Σ_M(x') = Q(φ)(ρ⁻¹E(u))Q(φ)ᵀ` with `u = ρ⁻²`, `ρ = |x'|`).

Mirrors `XmtRefl.sigmaM_sigE`: the radius and the phase-mean argument are invariant under
`rotPl θ` (`rotPl_sq`), the frame satisfies `Q(R_θ x') = R_θ Q(x')` (`hQ`), and the quadratic form
`Q S Qᵀ` is then rotated by `R_θ` on both sides.  No hypothesis on `M`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`SigmaMRot`** (source 4771-4775): `Σ_M(R_θ x') = R_θ Σ_M(x') R_θᵀ`. -/
theorem sigmaMRot : SigmaMRot := by
  intro c ν χo M θ x' a b
  have hr : (rotPl θ x').1 ^ 2 + (rotPl θ x').2 ^ 2 = x'.1 ^ 2 + x'.2 ^ 2 := rotPl_sq θ x'
  have hQ : ∀ a i, rotQ (rotPl θ x') a i = ∑ p, rotMat θ a p * rotQ x' p i := by
    intro a i
    have hρ : Real.sqrt ((rotPl θ x').1 ^ 2 + (rotPl θ x').2 ^ 2) =
        Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) := by
      rw [hr]
    simp only [rotQ]
    rw [hρ]
    fin_cases a <;> fin_cases i <;> simp [rotMat, rotPl, Fin.sum_univ_three] <;> ring
  simp only [sigmaM, hr, hQ]
  simp only [Fin.sum_univ_three]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
