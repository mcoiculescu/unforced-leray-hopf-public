import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Linear.Helpers
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.XmtCongr
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.XmtLinear
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.XmtSmooth
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.N0
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.OldMeasureAC

/-!
# Part III-b, task `PartIII-b:C/srcL/14` (`sourceLLinear`)

`𝓛` is linear on the stress space: the thin representative is additive and homogeneous almost
everywhere for the gain measure, hence (absolute continuity of the old measure, `oldMeasureAC`) for
the old measure; `X^mt` is linear on old tensors with finite `N₀` (`xmtLinear`) and depends only on
the a.e. class (`xmtCongr`); the receiver derivative is additive and homogeneous (`fderiv_add`,
`fderiv_const_smul`). Source 4792-4796 of `the November 2 reference manuscript`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `𝓛` is linear on the stress space. -/
theorem sourceLLinear (c mZ ρb γ ν ε μ : ℝ) (χo χy : ℝ → ℝ) :
    SourceLLinear c mZ ρb γ ν ε μ χo χy := by
  intro h hmZ hγ T T' r
  obtain ⟨C, k, hC⟩ := sourceLN0 mZ γ hmZ hγ
  have hf : ∀ S : StrG c mZ ρb γ ν, OldThinFinite c ν (thinRep S) :=
    fun S => (hC c ν ρb h.c_pos h.nu_pos h.nu_le S).1
  have hdiff : ∀ S : StrG c mZ ρb γ ν, ∀ y,
      DifferentiableAt ℝ (Xmt c ν ε μ χo χy (thinRep S)) y := fun S y =>
    ((xmtSmooth c ν ε μ χo χy h (thinRep S) (hf S)).differentiable (by norm_num)).differentiableAt
  have hae_add : thinRep (T + T') =ᵐ[oldMeasure c ν] thinRep T + thinRep T' :=
    (oldMeasureAC c mZ γ ν h.nu_pos).ae_eq (thinRep_add_ae T T')
  have hae_smul : thinRep (r • T) =ᵐ[oldMeasure c ν] r • thinRep T :=
    (oldMeasureAC c mZ γ ν h.nu_pos).ae_eq (thinRep_smul_ae r T)
  have hE_add : Xmt c ν ε μ χo χy (thinRep (T + T')) =
      Xmt c ν ε μ χo χy (thinRep T) + Xmt c ν ε μ χo χy (thinRep T') :=
    (xmtCongr c ν ε μ χo χy h.chiO h.nu_pos _ _ hae_add).trans
      (xmtLinear c ν ε μ χo χy h (thinRep T) (thinRep T') (hf T) (hf T') r).1
  have hE_smul : Xmt c ν ε μ χo χy (thinRep (r • T)) =
      r • Xmt c ν ε μ χo χy (thinRep T) :=
    (xmtCongr c ν ε μ χo χy h.chiO h.nu_pos _ _ hae_smul).trans
      (xmtLinear c ν ε μ χo χy h (thinRep T) (thinRep T') (hf T) (hf T') r).2
  exact ⟨funext fun s => Lpt_add_of (hdiff T) (hdiff T') hE_add s,
    funext fun s => Lpt_smul_of r (hdiff T) hE_smul s⟩

end UnforcedLeray.Short.PartIIIb.Concrete
