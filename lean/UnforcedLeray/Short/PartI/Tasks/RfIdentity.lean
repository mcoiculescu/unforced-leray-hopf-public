import UnforcedLeray.Short.PartI.StatementsCanonical
import UnforcedLeray.Units.B0094

/-!
# Part I, task `PartI:C01`: the identity `Q(D - kappa)Q = D - kappa + R_f` on `X_G`

Source of record: `the November 2 reference manuscript`, lines 1014-1030
(`Q(D-kappa)Q = D-kappa+R_f`, `R_f = -DP - PD + PDP + kappa P`).

Proof. Write `P f = l f • q`, `Q = 1 - P`, `kappa = l (D q)`. Since `q ∈ 𝒟(D)`, the vector
`Q f = f - l f • q` lies in `𝒟(D)` and `D (Q f) = D f - l f • D q`. Then
`Q (D (Q f)) = D (Q f) - l (D (Q f)) • q` with `l (D (Q f)) = l (D f) - l f * kappa`.
Self-adjointness and `l = ⟪qd, ·⟫` give `l (D f) = ⟪D qd, f⟫`. Expanding `seedRf` then
gives the same vector identity on both sides.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ContDiff Topology ComplexConjugate

open UnforcedLeray.Infra.Dunford (rankOneProj)

namespace UnforcedLeray.Short.PartI

/-- **Complementary identity** (source lines 1014-1030): for a seed triple `(lam, q, l)` with
`l = ⟪qd, ·⟫` and `q, qd ∈ 𝒟(D)`, the operator `Q (D - kappa) Q` on `𝒟(D)` equals
`D - kappa + R_f` with `R_f = seedRf l q qd`. -/
theorem seedRf_spec {lam q l} (hI : IsSeedXG lam q l) {qd} (hq : q ∈ B0094.D.domain)
    (hqd : qd ∈ B0094.D.domain) (hl : ∀ f, l f = inner ℂ qd f) (f : B0010.XG)
    (hf : f ∈ B0094.D.domain) :
    ∃ hQf : (1 - rankOneProj l q) f ∈ B0094.D.domain,
      (1 - rankOneProj l q) (B0094.D ⟨(1 - rankOneProj l q) f, hQf⟩)
          - seedKappa l q hq • (1 - rankOneProj l q) f
        = B0094.D ⟨f, hf⟩ - seedKappa l q hq • f + seedRf l q qd hq hqd f := by
  have hQ : ∀ g : B0010.XG, (1 - rankOneProj l q) g = g - l g • q := by
    intro g
    simp [rankOneProj]
  have hQf : (1 - rankOneProj l q) f ∈ B0094.D.domain := by
    rw [hQ f]
    exact Submodule.sub_mem _ hf (Submodule.smul_mem _ _ hq)
  have hkey : l (B0094.D ⟨f, hf⟩) = inner ℂ (B0094.D ⟨qd, hqd⟩) f := by
    rw [hl]
    exact (B0094.D_symm ⟨qd, hqd⟩ ⟨f, hf⟩).symm
  have hDsub : B0094.D ⟨(1 - rankOneProj l q) f, hQf⟩
      = B0094.D ⟨f, hf⟩ - l f • B0094.D ⟨q, hq⟩ := by
    have h1 : (⟨(1 - rankOneProj l q) f, hQf⟩ : B0094.D.domain)
        = (⟨f, hf⟩ : B0094.D.domain) - l f • (⟨q, hq⟩ : B0094.D.domain) := by
      apply Subtype.ext
      simp only [Submodule.coe_sub, Submodule.coe_smul]
      exact hQ f
    rw [h1, LinearPMap.map_sub, LinearPMap.map_smul]
  refine ⟨hQf, ?_⟩
  rw [hDsub]
  simp only [hQ, seedRf, seedKappa, add_apply, sub_apply,
    neg_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, map_sub, map_smul, smul_eq_mul,
    hkey]
  module

end UnforcedLeray.Short.PartI
