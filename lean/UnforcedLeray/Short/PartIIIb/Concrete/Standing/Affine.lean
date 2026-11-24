import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Lam
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.AZeroBmatLinear
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.AZeroBmatBound
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.InAff
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Linear
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Bounded
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.HhatCoefLinear
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.FACoefLinear
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.EACoefLinear
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.HhatCoefBound
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.FACoefBound

/-!
# The affine pins of the standing hypotheses (`ORG:C/standing` (a))

Source of record: `the November 2 reference manuscript` (73 pages).

Along the sequence `D` (large `n`, `z ∈ [-1, 1]`, `μ = μ_n(z)`), the fields `lj`, `lam`, `hA`,
`fA`, `eA` of `RegimePins` (`Concrete/ReturnRepair/Estimates.lean`), from accepted statements
only:

* `regimePins_lj_of` : `𝓛 : Str → 𝒜` with `ι(𝓛T) = LjFun … T` (source 4792-4803, 4917-4937), from
  `sourceLInAff`, `sourceLLinear`, `sourceLBounded` (`PartIII-b:C/srcL/15, 14, 16`) through
  `SeqData.eventually_exists_LjOp`;
* `regimePins_lam_of` : the real row `Λ_{μ,ν} : 𝒜 → ℝ` (source 4812-4815), from `aZeroBmatLinear`,
  `aZeroBmatBound` through `SeqData.eventually_exists_LamOp`;
* `seq_affineFieldData`, `regimePins_hA_of`, `regimePins_fA_of`, `regimePins_eA_of` : the affine
  fields `ĥ_A, F_A, E_A` (source 4969-4985), from `affineFieldData_of` with `hhatCoefLinear`,
  `faCoefLinear`, `eaCoefLinear`, `hhatCoefBound`, `faCoefBound` (`PartIII-b:C/inst/11, 9`) and
  `EACoefBound` (`eaCoefBound`, `PartIII-b:C/inst/10`).

`EACoefBound` is a hypothesis: `Concrete/ReturnInst/EACoefBound.lean` and
`Concrete/ReturnInst/FACoefBound.lean` cannot be imported together (the verbatim copy
`EACoefBound/BmatBound.lean` of `FACoefBound/BmatBound.lean`; `ORG:clash-pass` step (1)).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-! ## 1. `𝓛` and `Λ` (source 4792-4815) -/

/-- **The pinned `𝓛` along the sequence** (source 4792-4803, 4917-4937; the field `lj` of
`RegimePins`). -/
theorem regimePins_lj_of (D : SeqData) (hω : D.Pl.eigenvalue.im ≠ 0)
    (hγ : 0 < D.Pl.eigenvalue.re) (hσ0 : 0 < D.σ₀) (hσ1 : D.σ₀ < 1 / 4)
    (hχy : IsStreamCutoff D.K.χy) (hmZ : 3 / 2 < D.K.mZ) (has : 0 < D.K.as) :
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∃ Lj : LStr D.Pl D.K (D.level n) →L[ℝ] AffSp D.K.as, ∀ T, affIota D.K.as (Lj T) =
        LjFun (cOf (D.level n).ν) D.K.mZ ((D.level n).ρb D.Pl D.K) (gRate D.Pl) (D.level n).ν
          (D.level n).ε (D.mu n z) D.K.χo D.K.χy T :=
  D.eventually_exists_LjOp hω hγ hσ0 hσ1 hχy hmZ has
    (fun c mZ ρb γ ν ε μ => sourceLInAff D.K.as c mZ ρb γ ν ε μ D.K.χo D.K.χy)
    (fun c mZ ρb γ ν ε μ => sourceLLinear c mZ ρb γ ν ε μ D.K.χo D.K.χy)
    (fun Kset => sourceLBounded D.K.as D.K.mZ (gRate D.Pl) Kset D.K.χo D.K.χy)

/-- **The real row `Λ_{μ,ν}` along the sequence** (source 4812-4815; the field `lam` of
`RegimePins`). -/
theorem regimePins_lam_of (D : SeqData) (hω : D.Pl.eigenvalue.im ≠ 0) (hσ0 : 0 < D.σ₀)
    (hσ1 : D.σ₀ < 1 / 4) (hχf : IsSourceCutoffC D.K.χf) (has : 0 ≤ D.K.as) :
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∃ l : AffSp D.K.as →L[ℝ] ℝ, ∀ A, l A =
        LamFun D.Pl.eigenvalue D.Pl.kappa D.Pl.strainCoupling (planarJ D.Pl) (D.level n).ε
          (D.level n).ν (D.mu n z) D.K.χf (affIota D.K.as A) :=
  D.eventually_exists_LamOp hω hσ0 hσ1 hχf has (aZeroBmatLinear _ _) (aZeroBmatBound _ _)

/-! ## 2. The affine fields `ĥ_A, F_A, E_A` (source 4969-4985) -/

/-- **The affine field data along the sequence** (source 4969-4985): for large `n` and
`z ∈ [-1, 1]` the three affine coefficient families are `L²` families on `𝒜` through `ι`. -/
theorem seq_affineFieldData (D : SeqData) (hω : D.Pl.eigenvalue.im ≠ 0)
    (hγ : 0 < D.Pl.eigenvalue.re) (hσ0 : 0 < D.σ₀) (hσ1 : D.σ₀ < 1 / 4)
    (hχf : IsSourceCutoffC D.K.χf) (has : 0 ≤ D.K.as) (bE : EACoefBound D.K.as D.K.χf) :
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      AffineFieldData D.K.as (D.level n).ν (D.mu n z) (D.level n).ε (gRate D.Pl) D.K.χf
        (affIota D.K.as) := by
  obtain ⟨Cenv, -, hCenv⟩ := affM_le_norm_of (affMEnvelope D.K.χf hχf)
  have hKs : Icc (D.σ₀ / 2) ((D.σ₀ + 1 / 4) / 2) ⊆ Ioo 0 (1 / 4) :=
    fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  filter_upwards [retNu_retEps_eventually_le_one (σ₀ := D.σ₀) hω hγ D.coeff_ne,
    mu_eventually_mem D hω hσ0 hσ1] with n hνε hμ z hz
  have hν : 0 < (D.level n).ν := (D.level n).ν_pos
  exact affineFieldData_of (affIota_mem D.K.as) hν hνε.1 (D.level n).ε_pos hνε.2 hγ.le
    isCompact_Icc hKs (hμ z hz) _
    (fun A => hCenv D.K.as (D.level n).ν (fun A => affIota D.K.as A) has hν (affIota_mem D.K.as)
      (fun A => (affNorm_affIota D.K.as A).le) A)
    (hhatCoefLinear _ _ hχf) (faCoefLinear _ _ hχf) (eaCoefLinear _ _ hχf)
    (hhatCoefBound _ _ hχf) (faCoefBound _ _ hχf) bE

/-- **`ĥ_A` along the sequence** (source 4976-4980; the field `hA` of `RegimePins`). -/
theorem regimePins_hA_of (D : SeqData) (hω : D.Pl.eigenvalue.im ≠ 0)
    (hγ : 0 < D.Pl.eigenvalue.re) (hσ0 : 0 < D.σ₀) (hσ1 : D.σ₀ < 1 / 4)
    (hχf : IsSourceCutoffC D.K.χf) (has : 0 ≤ D.K.as) (bE : EACoefBound D.K.as D.K.χf) :
    ∀ᶠ n : ℕ in atTop, ∀ _z ∈ Icc (-1 : ℝ) 1,
      ∃ H : AffSp D.K.as →L[ℝ] LVel D.Pl (D.level n), ∀ A,
        (H A : Chart → Merid) =ᵐ[bodyMeasure (cOf (D.level n).ν) (gRate D.Pl) (D.level n).ν]
          hAcoef (D.level n).ν (D.level n).ε D.K.χf (affIota D.K.as A) := by
  filter_upwards [seq_affineFieldData D hω hγ hσ0 hσ1 hχf has bE] with n hn z hz
  exact ⟨(hn z hz).hAL, (hn z hz).hA.toCLM_ae⟩

/-- **`F_A` along the sequence** (source 4981; the field `fA` of `RegimePins`). -/
theorem regimePins_fA_of (D : SeqData) (hω : D.Pl.eigenvalue.im ≠ 0)
    (hγ : 0 < D.Pl.eigenvalue.re) (hσ0 : 0 < D.σ₀) (hσ1 : D.σ₀ < 1 / 4)
    (hχf : IsSourceCutoffC D.K.χf) (has : 0 ≤ D.K.as) (bE : EACoefBound D.K.as D.K.χf) :
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∃ F : AffSp D.K.as →L[ℝ] LSrc (D.level n), ∀ A,
        (F A : Chart → Merid) =ᵐ[srcMeasure (cOf (D.level n).ν)]
          FAcoef (D.level n).ν (D.mu n z) D.K.χf (affIota D.K.as A) := by
  filter_upwards [seq_affineFieldData D hω hγ hσ0 hσ1 hχf has bE] with n hn z hz
  exact ⟨(hn z hz).FAL, (hn z hz).FA.toCLM_ae⟩

/-- **`E_A` along the sequence** (source 4981; the field `eA` of `RegimePins`). -/
theorem regimePins_eA_of (D : SeqData) (hω : D.Pl.eigenvalue.im ≠ 0)
    (hγ : 0 < D.Pl.eigenvalue.re) (hσ0 : 0 < D.σ₀) (hσ1 : D.σ₀ < 1 / 4)
    (hχf : IsSourceCutoffC D.K.χf) (has : 0 ≤ D.K.as) (bE : EACoefBound D.K.as D.K.χf) :
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∃ E : AffSp D.K.as →L[ℝ] LSrc (D.level n), ∀ A,
        (E A : Chart → Merid) =ᵐ[srcMeasure (cOf (D.level n).ν)]
          EAcoef (D.level n).ν (D.mu n z) D.K.χf (affIota D.K.as A) := by
  filter_upwards [seq_affineFieldData D hω hγ hσ0 hσ1 hχf has bE] with n hn z hz
  exact ⟨(hn z hz).EAL, (hn z hz).EA.toCLM_ae⟩

end UnforcedLeray.Short.PartIIIb.Concrete
