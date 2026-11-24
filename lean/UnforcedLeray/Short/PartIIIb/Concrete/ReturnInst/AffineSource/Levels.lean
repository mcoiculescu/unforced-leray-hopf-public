import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymMu
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymNuEps
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.AMuInAff

/-!
# The source-map hypotheses at the concrete levels (source 4753-4757, 4792-4811, 5926-5950)

Source of record: `the November 2 reference manuscript` (73 pages).

Part (e) of `ORG:return-concrete/instance-3/affine-source`.  Along the phase-locked sequence
(`SeqData`, `Concrete/ReturnInst.lean`), for large `n` and `z ∈ [-1, 1]`:

* `SeqData.eventually_mu_mem_Ioo` : `μ_n(z) ∈ (0, 1/4)` (source 5946-5950, from
  `mu_eventually_mem`, task `PartIII-b:C/rinst/3`);
* `SeqData.eventually_lHyp` : the standing hypotheses `LHyp (cOf ν_n) ν_n ε_n μ_n(z) χ_o χ_y` of the
  source maps (source 4753-4757: `c = ν⁻²`, `0 < ν ≤ 1`, `ε > 0`, `μ ∈ K ⋐ (0,1/4)`, the outward
  and stream cutoffs), from `mu_eventually_mem` and `retNu_retEps_eventually_le_one`
  (`PartIII-b:C/rinst/2`);
* `SeqData.eventually_exists_LjOp`, `SeqData.eventually_exists_aMuOp` : the pinned `𝓛` and `a_μ`
  (`exists_LjOp_of`, `exists_aMuOp_of`) at these levels, from the source facts `SourceLLinear`
  (accepted `sourceLLinear`, `PartIII-b:C/srcL/14`), `SourceLBounded` (accepted `sourceLBounded`,
  `PartIII-b:C/srcL/16`), `SourceLInAff` (task `PartIII-b:C/srcL/15`) and the accepted `aMuInAff`
  (`PartIII-b:C/srcL/3`).

`SourceLLinear` and `SourceLBounded` are hypotheses here although their theorems are accepted:
`Concrete/SourceL/Linear.lean` and `Concrete/SourceL/Bounded.lean` import
`Concrete/SourceL/Ambient/SigmaL1/Pointwise.lean`, whose `Concrete.frob_smul` clashes with the
`Concrete.frob_smul` of `Concrete/AffineEnvelope.lean`, now in the closure of
`Concrete/ReturnInst.lean` (through `Concrete/AffineGradPin.lean`).  Once the clash is renamed
the hypotheses are discharged by `sourceLLinear _ _ _ _ _ _ _ _ _` and `sourceLBounded _ _ _ _ _ _`.

The stream cutoff `χ_y` of `ReturnConsts` carries no property; `IsStreamCutoff D.K.χy`
(source 4755-4757) is a hypothesis.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace SeqData

variable (D : SeqData)

/-- `μ_n(z) ∈ (0, 1/4)` for large `n`, uniformly in `z ∈ [-1, 1]` (source 5946-5950). -/
theorem eventually_mu_mem_Ioo (hω : D.Pl.eigenvalue.im ≠ 0) (hσ0 : 0 < D.σ₀)
    (hσ1 : D.σ₀ < 1 / 4) :
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, D.mu n z ∈ Ioo (0 : ℝ) (1 / 4) := by
  filter_upwards [mu_eventually_mem D hω hσ0 hσ1] with n hn z hz
  obtain ⟨h1, h2⟩ := hn z hz
  exact ⟨by linarith, by linarith⟩

/-- **The standing hypotheses of the source maps at the levels** (source 4753-4757 along
5926-5950): for large `n` and `z ∈ [-1,1]`, `LHyp (cOf ν_n) ν_n ε_n μ_n(z) χ_o χ_y`. -/
theorem eventually_lHyp (hω : D.Pl.eigenvalue.im ≠ 0) (hγ : 0 < D.Pl.eigenvalue.re)
    (hσ0 : 0 < D.σ₀) (hσ1 : D.σ₀ < 1 / 4) (hχy : IsStreamCutoff D.K.χy) :
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      LHyp (cOf (retNu D.Pl D.σ₀ n)) (retNu D.Pl D.σ₀ n) (retEps D.Pl D.σ₀ n) (D.mu n z)
        D.K.χo D.K.χy := by
  filter_upwards [eventually_mu_mem_Ioo D hω hσ0 hσ1,
    retNu_retEps_eventually_le_one (σ₀ := D.σ₀) hω hγ D.coeff_ne] with n hμ hνε z hz
  exact ⟨cOf_pos (retNu_pos _ _ _), retNu_pos _ _ _, hνε.1, retEps_pos D.coeff_ne n,
    (hμ z hz).1, (hμ z hz).2, D.K.hχo, hχy⟩

/-- **The pinned `𝓛` at the levels** (source 4792-4803, 4917-4937): for large `n` and
`z ∈ [-1,1]` there is a continuous linear `𝓛 : Str → 𝒜` with `ι(𝓛T) = LjFun … T`, the first
clause of `IsSourceLPinned`.  `SourceLInAff` is the leaf `PartIII-b:C/srcL/15`; `SourceLLinear`,
`SourceLBounded` are the accepted `PartIII-b:C/srcL/14`, `/16` (see the module docstring). -/
theorem eventually_exists_LjOp (hω : D.Pl.eigenvalue.im ≠ 0) (hγ : 0 < D.Pl.eigenvalue.re)
    (hσ0 : 0 < D.σ₀) (hσ1 : D.σ₀ < 1 / 4) (hχy : IsStreamCutoff D.K.χy)
    (hmZ : 3 / 2 < D.K.mZ) (has : 0 < D.K.as)
    (hIn : ∀ (c mZ ρb γ ν ε μ : ℝ), SourceLInAff D.K.as c mZ ρb γ ν ε μ D.K.χo D.K.χy)
    (hLin : ∀ (c mZ ρb γ ν ε μ : ℝ), SourceLLinear c mZ ρb γ ν ε μ D.K.χo D.K.χy)
    (hB : ∀ Kset : Set ℝ, SourceLBounded D.K.as D.K.mZ (gRate D.Pl) Kset D.K.χo D.K.χy) :
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∃ Lj : LStr D.Pl D.K (D.level n) →L[ℝ] AffSp D.K.as, ∀ T, affIota D.K.as (Lj T) =
        LjFun (cOf (D.level n).ν) D.K.mZ ((D.level n).ρb D.Pl D.K) (gRate D.Pl) (D.level n).ν
          (D.level n).ε (D.mu n z) D.K.χo D.K.χy T := by
  filter_upwards [eventually_lHyp D hω hγ hσ0 hσ1 hχy] with n hn z hz
  have hL := hn z hz
  have hK : ({D.mu n z} : Set ℝ) ⊆ Ioo 0 (1 / 4) := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨hL.mu_pos, hL.mu_lt⟩
  exact exists_LjOp_of (Pl := D.Pl) (K := D.K) (L := D.level n) (μ := D.mu n z) hL hmZ hγ has
    hK (hIn _ _ _ _ _ _ _) (hLin _ _ _ _ _ _ _) (hB _)

/-- **The pinned `a_μ` at the levels** (source 4807-4811): for large `n` and `z ∈ [-1,1]`,
`a_{μ_n(z)} ∈ 𝒜` (`aMuInAff`, `PartIII-b:C/srcL/3`), the second clause of `IsSourceLPinned`. -/
theorem eventually_exists_aMuOp (hω : D.Pl.eigenvalue.im ≠ 0) (hσ0 : 0 < D.σ₀)
    (hσ1 : D.σ₀ < 1 / 4) (has : 0 ≤ D.K.as) :
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∃ a : AffSp D.K.as, affIota D.K.as a = aMuFun (D.mu n z) := by
  filter_upwards [eventually_mu_mem_Ioo D hω hσ0 hσ1] with n hn z hz
  exact exists_aMuOp_of (aMuInAff _ _) has (hn z hz).1

end SeqData

end UnforcedLeray.Short.PartIIIb.Concrete
