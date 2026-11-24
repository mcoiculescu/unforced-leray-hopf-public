import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3_2

/-!
# Part III-a, `PartIII-a:T18/3/1/3/2/2` (`MollDerivData`): decomposition

Source of record: `the November 2 reference manuscript` (SP) lines 3541-3552 and
3427-3440.

`MollDerivData` asks for a weak derivative `u'` of `u_k = J_k b` (`LMWeakDeriv`) with the
pairing `2 Re ⟨u'(s), u_k(s)⟩ = -(2 Re μ s⁻¹ E_k + 2 ν N_k + 2 R_k)` for a.e. `s > 0`.
Since the pairing identity is only needed a.e. in `s`, `MollDerivData` is the same statement as

* `LMDerivRepAE`: existence of `u'` (the Leray representative
  `-(μ/s) u_k + νΔu_k + J_k 𝒫₀ div F`, obtained by testing `ExtWeakH1` with `J_k φ₀`, SP 3427-3440)
  together with the pairing identity for a.e. `s > 0` (SP 3541-3552). This needs the Leray
  projection on the cylinder, which has no Lean definition: organize task.

Proved here: `mollDerivData_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **Existence of the weak derivative of `u_k = J_k b` with the pairing identity a.e. in `s`**
(SP 3427-3440, 3541-3552): `u' = -(μ/s) u_k + νΔu_k + J_k 𝒫₀ div F`, `ExtWeakH1` tested with
`J_k φ₀` (`selfAdj`, `commute`, `divFree` of `IsLMMollifier`), and
`2 Re⟨u', u_k⟩ = -(2 Re μ s⁻¹ E_k + 2 ν N_k + 2 R_k)` for a.e. `s > 0`, using
`Re⟨Δu_k, u_k⟩ = -‖∇u_k‖²` (`LMSmoothWeakPd`) and `⟨J_k 𝒫₀ div F, u_k⟩ = -⟨F, ∇J_k² b⟩`. -/
def LMDerivRepAE : Prop :=
  ∀ (c ν : ℝ) (μ : ℂ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ),
    FreeSolData c ν μ F b G → ∀ J : ℕ → LMSpField → LMSpField, IsLMMollifier c J →
    ExtWeakH1 c ν μ F b G → ∀ k : ℕ,
      ∃ u' : ℝ → LMSpField, LMWeakDeriv c (LMMollU J b k) u' ∧
        ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
          2 * (LMIp c (u' s) (LMMollU J b k s)).re =
            -(2 * μ.re / s * LMMollE c J b k s + 2 * ν * LMMollN c J b k s +
              2 * LMMollR c J F b k s)

/-- `MollDerivData` is `LMDerivRepAE` (the pairing identity is a.e. in `s`). -/
theorem mollDerivData_of (hA : LMDerivRepAE) : MollDerivData := hA

end UnforcedLeray.Short.IIIa
