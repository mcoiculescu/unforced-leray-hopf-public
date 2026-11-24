import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineFields
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnAffBanach
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Clauses
import UnforcedLeray.Short.PartIIIb.PhaseLocked
import UnforcedLeray.Short.PartIIIb.Concrete.AffineGradPin
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Background.Ball
import UnforcedLeray.Short.PartI.TrainClass

/-!
# The concrete exact return: the pinned base, `ConcreteReturnOps` and `concreteReturnSeq`
(source 5777-5833, 5926-5950)

Source of record: `the November 2 reference manuscript` (73 pages).

## One regime

A regime is a level `L : ReturnLevel` (viscosity `ν`, ring parameter `ε = R⁻¹`, slow age `Σ`,
the actual train at `c = ν⁻²`, the exact split `U = V + r_b` with inlet support `S_in`, the
global pressure of `U`, the flat setting), the fixed choices `K : ReturnConsts` (`m_Z`, the repair
bound `ρ_b = C₀ν^{-k₀}e^{m₀/ν}ε^{3/11}` of source 2706-2713, `a_s`, the far-mask gap `δ` and
output cut `S = ε^{-b}` of 3902-3912, the cutoff profiles `χ̂_o, χ̂_y, χ̂_f` of 4161-4166,
4750-4752, 4955-4956), the planar data `Pl` (`λ, κ, ℓ₊(H₀), 𝒥`; gain rate `γ = Re λ`) and the
Floquet exponent `μ`.  The spaces are those of `Concrete/ReturnOps.lean` at `c = ν⁻²`
(`cOf ν`), `γ = Re λ`, `ρ_b = rhoB`, and `𝒜 = AffSp a_s` (`Concrete/ReturnAffBanach.lean`) with
the inclusion `affIota` (the subtype map).

## The operators

Each primary operator is *the* operator with the source's defining property (`Classical.epsilon`
of the pin; the pins determine the operators, and every statement about an operator takes the
existence of the pinned operator as a hypothesis):

| operator | definition | source |
|---|---|---|
| `nearMU` | split multiplier `M_U u = (v⊗u+u⊗v, v_b⊗u+u⊗v_b)` on `H → Z` (`IsSplitMult`) | 2706, 3877-3878 |
| `multOp` | `M = M_U` on the gain spaces, the near-link transport of `nearMU` (`NearOps.MG`) | 3876-3877, 4147, 5779-5782 |
| `nearOpsAt` | the near operators of the level (`IsActualNear`, with `M_U = nearMU`) | 3866-3914 |
| `SNop` | `S_N` = transport `NearOps.SNG` of the near inverse | 3911-3920, 5785 |
| `bodyReps`, `Rop` | real form `R_ε` of `T_ε = (μ - A_ε)⁻¹P_ε`; `R_μ = bodyG R_ε` | 1675-1677, 4139-4146, 5781 |
| `Sop` | `S_μ = R_μℙ div`, the weak stress inverse (`IsWeakStressInverse`) | 4145, 1556-1572 |
| `wardOps` | the Ward fields `Y[T], h[T], Ẽ_μ[T]` (`IsWardTriple` = `IsWardPinned`) | 4161-4303 |
| `hAOp`, `FAOp`, `EAOp` | `ĥ_A, F_A, E_A` of `Concrete/ReturnAff.lean` (`IsAffinePinned`) | 4969-4985 |
| `rAOp` | `𝔯_A`, the exact unprojected residual (`IsRAOp` = `IsRAPinned`) | 5001-5050 |
| `LjOp`, `aMuOp`, `LamOp`, `KflatOp` | `𝓛`, `a_μ`, `Λ_{μ,ν}`, `𝒦^flat` (`IsSourceLPinned`) | 4792-4815 |

`multOp` does not depend on `μ` (`M_U` is the multiplier of the fixed background), so the graph
`𝓔_ν = {T = Mw}` (`PairSp (multOp …) (γ/8) ν`, source 5640-5658) is the same for all `μ`.

## The base and the operators of the return system

* `baseOf … D h₁ h₂` : the `ReturnBase` with these primary fields and a two-sided inverse `D` of
  `D_N = I + MS_N` (source 5787).  `D_N⁻¹` exists when the near operator `D_N` of the level is a
  unit (`NearSolverC`, source 3943-3951); then the base is `concreteBase … hU` (with
  `D_N⁻¹ = NearOps.DNinvG`) and **`ConcreteReturnOps … hU := (concreteBase … hU).toOps`**.
* `concreteOps` : the return operators of the regime without the invertibility proof:
  `Classical.epsilon` of "`= (baseOf … D h₁ h₂).toOps` for an inverse `D`".  Two-sided inverses
  are unique (`dnInv_unique`), so `concreteOps = ConcreteReturnOps … hU` whenever `D_N` is a unit
  (`concreteOps_eq`).  This is the field `ops` of the sequence.

## The sequence (source 5926-5950)

`SeqData` : the planar reference `(Pl, σ₀)` with `𝒞(σ₀) ≠ 0`, the fixed choices, the slow age,
and at every level the actual train, the exact split, the pressure and the flat setting (the
source fixes one exact background per level and holds it fixed while `σ` varies, 5933-5936; the
Part III output quantifies over every such background, `Spine/PartIII.lean`).
`ν_n = retNu = lockedNu(Im λ, Im κ, arg 𝒞(σ₀))` is the phase-locked sequence (5928-5934, the
witness of `PhaseLocked.phaseLockedSequence`; it is the Spine's `nuSeq`), `ε_n = retEps` with
`ε_n³ = e^{-γ/ν_n}ν_n^{Re κ-5-2σ₀}/(2|𝒞(σ₀)|)` (5936-5940, the Spine's `epsSeq`), `c_n = ν_n⁻²`,
and `μ = μ_n(z) = muWin σ₀ ν_n z` (5946).  **`concreteReturnSeq D G : ReturnSeq`** has
`ops n z = concreteOps … (μ_n(z))`, `Grd n = GrdG c_n` and `gradhA n z = G n`, where `G n` is the
gradient `A ↦ ∇ĥ_A` (4976-4985, 5011-5013): its pin `IsAffineGradPinned` lives in
`Concrete/AffineGradPin.lean`, which cannot be imported together with `Concrete/SourceL.lean`
while both declare `Concrete.affTerm_nonneg` (`ReturnAffExamples.lean:32`, `SourceL.lean:367`),
so `G` is an argument and the statements that involve `gradhA` assume its pin or its bound.

## Statements along the sequence

* `concreteReturnSeq_fieldNorms_le` : the `F_A, E_A, ĥ_A` part of the first line of
  `ret:general-affine-bounds` (5009-5013), from the leaves of `ReturnInst/AffineFields.lean`.
* `concreteReturnSeq_rA_le` : the second line (5014-5016), from `RABoundExists` (Lemma
  `ret:physical-affine` with its bound, 5001-5079) and `SrcPairingNondeg` (the pin determines
  `𝔯_A`).
* The pins of the concrete base: `concreteBase_isNearLinked`, `_isBodyLinked`,
  `_isExactMultiplier`, `_isStressInverse`, `_isWardPinned`, `_isAffinePinned`, `_isRAPinned`,
  `_isSourceLPinned`, each from the existence of the pinned operator.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest Params)
open UnforcedLeray.Blueprint.Planar (PlanarData)

/-! ## 1. The space `𝒜` and its inclusion -/

/-- The norm topology of `𝒜 = AffSp a_s` (source 4750).  `AffSp` is an `abbrev` of a subtype of
`ℝ → Mat3`, so instance search would otherwise also find the subtype (pointwise) topology
`instTopologicalSpaceSubtype`, a different topology; every map out of or into `𝒜` is continuous
for the norm. -/
instance (priority := high) affSpTopology (as : ℝ) : TopologicalSpace (AffSp as) :=
  @UniformSpace.toTopologicalSpace _ (@PseudoMetricSpace.toUniformSpace _
    (@SeminormedAddCommGroup.toPseudoMetricSpace _
      (@NormedAddCommGroup.toSeminormedAddCommGroup _ (affSpNAG as))))

/-- The norm uniformity of `𝒜` (see `affSpTopology`). -/
instance (priority := high) affSpUniformity (as : ℝ) : UniformSpace (AffSp as) :=
  @PseudoMetricSpace.toUniformSpace _ (@SeminormedAddCommGroup.toPseudoMetricSpace _
    (@NormedAddCommGroup.toSeminormedAddCommGroup _ (affSpNAG as)))

/-- The inclusion `𝒜 → (ℝ → Mat3)`, the subtype map (source 4741-4752). -/
def affIota (as : ℝ) : AffSp as →ₗ[ℝ] (ℝ → Mat3) where
  toFun A := A.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem affIota_apply (as : ℝ) (A : AffSp as) : affIota as A = A.1 := rfl

theorem affIota_mem (as : ℝ) (A : AffSp as) : IsAffElem as (affIota as A) := A.2

theorem affIota_injective (as : ℝ) : Function.Injective (affIota as) :=
  fun _ _ h => Subtype.ext h

/-- `‖ιA‖_𝒜 = ‖A‖`. -/
theorem affNorm_affIota (as : ℝ) (A : AffSp as) : affNorm as (affIota as A) = ‖A‖ :=
  (AffSp.norm_def as A).symm

/-! ## 2. Nonemptiness (for `Classical.epsilon`) -/

instance (c mZ ρb : ℝ) : Nonempty (NearInst.NearOps c mZ ρb) := ⟨⟨0, 0, 0, 0⟩⟩

instance {Vel Str Src Aff Gam : Type}
    [NormedAddCommGroup Vel] [NormedSpace ℝ Vel] [NormedAddCommGroup Str] [NormedSpace ℝ Str]
    [NormedAddCommGroup Src] [NormedSpace ℝ Src] [NormedAddCommGroup Aff] [NormedSpace ℝ Aff]
    [CompleteSpace Aff] [NormedAddCommGroup Gam] [NormedSpace ℝ Gam] [CompleteSpace Gam] :
    Nonempty (ReturnOps Vel Str Src Aff Gam) :=
  ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩

/-! ## 3. The data of one regime -/

theorem cOf_pos {ν : ℝ} (hν : 0 < ν) : 0 < cOf ν := inv_pos.2 (pow_pos hν 2)

/-- The fixed choices of the concrete return: the weight exponent `m_Z` of `Z₁` (source 2697), the
repair bound `ρ_b = C₀ν^{-k₀}e^{m₀/ν}ε^{3/11}` (2706-2713, `IIb.rhoB`), the exponent `a_s` of `𝒜`
(4741-4752), the log gap `δ` and the output-cut exponent `b` (`S = ε^{-b}`) of the far mask
(3902-3912, 4109-4124), and the outward, young-stream and source cutoff profiles (4161-4166,
4750-4752, 4955-4956). -/
structure ReturnConsts where
  mZ : ℝ
  m0 : ℝ
  C0 : ℝ
  k0 : ℕ
  as : ℝ
  δ : ℝ
  b : ℝ
  χo : ℝ → ℝ
  χy : ℝ → ℝ
  χf : ℝ → ℝ
  hχo : IsOutwardCutoff χo

/-- One level of the exact return (source 2026-2713, 4557-4612, 5926-5950): viscosity `ν`, ring
parameter `ε = R⁻¹`, slow age `Σ` of the inlet (`H = Σ/ν`), the actual train at `c = ν⁻²`, the
exact split `U = V + r_b` with inlet support `S_in`, the global pressure of `U`, and the flat
setting of the train. -/
structure ReturnLevel where
  ν : ℝ
  ε : ℝ
  Sig : ℝ
  ν_pos : 0 < ν
  ε_pos : 0 < ε
  Sig_pos : 0 < Sig
  train : UnforcedLeray.B0140.TrainSol ν (cOf ν)
  /-- The actual train is the BUC train of Part I (source 270-288, 2040; as `IIb.BgRegime.train_buc`). -/
  train_buc : UnforcedLeray.Short.PartI.IsBUCTrain train
  /-- The stream `ψ` of the train is jointly smooth for `s > 0` (source 397, 2049; as
  `IIb.BgRegime.train_stream_smooth`). -/
  train_stream_smooth : ContDiffOn ℝ ∞
    (fun x : ℝ × UnforcedLeray.Cyl.Plane => train.ψ x.1 x.2) (Set.Ioi 0 ×ˢ Set.univ)
  Sin : ℝ
  V : ℝ → SpatialField
  rb : ℝ → SpatialField
  pres : ℝ → Space → ℝ
  flat : ConcreteYF.FlatSetting

namespace ReturnLevel

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)

/-- The background level of the near layer (`Cons.C03.Concrete.Params`): `c = ν⁻²`, the planar
mode `q = Pl.mode`, the actual train. -/
def params : Params where
  ν := L.ν
  c := cOf L.ν
  ε := L.ε
  ageCut := L.Sig
  mode := Pl.mode
  ν_pos := L.ν_pos
  c_pos := cOf_pos L.ν_pos
  ε_pos := L.ε_pos
  ageCut_pos := L.Sig_pos
  trainData := L.train

/-- The repair bound `ρ_b = C₀ν^{-k₀}e^{m₀/ν}ε^{3/11}` (source 2706-2713). -/
def ρb : ℝ := UnforcedLeray.Short.IIb.rhoB (L.params Pl) K.m0 K.C0 K.k0

/-- The exact background `U = V + r_b` (source 2669-2672, 5779-5782). -/
def U : ℝ → SpatialField := fun τ y => L.V τ y + L.rb τ y

/-- The output cut `S = ε^{-b}` of the far mask (source 3905-3912, 4109-4124). -/
def Scut : ℝ := L.ε ^ (-K.b)

end ReturnLevel

/-- The gain rate `γ = Re λ` (source 3875, 5117). -/
abbrev gRate (Pl : PlanarData) : ℝ := Pl.eigenvalue.re

/-- Body velocities of the regime. -/
abbrev LVel (Pl : PlanarData) (L : ReturnLevel) := VelG (cOf L.ν) (gRate Pl) L.ν

/-- Body forces of the regime. -/
abbrev LSrc (L : ReturnLevel) := SrcG (cOf L.ν)

/-- Stresses of the regime. -/
abbrev LStr (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) :=
  StrG (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν

/-! ## 4. The near-layer operators of the level -/

section Near

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)

/-- The split multiplier `M_U : H → Z` of the level (source 2706, 3877-3878): *the* bounded `M`
with `IsSplitMult M R V r_b`, `R = ε⁻¹` (it is determined a.e., `isSplitMult_unique`). -/
def nearMU : Hsp (cOf L.ν) →L[ℝ] Zsp (cOf L.ν) K.mZ (L.ρb Pl K) :=
  Classical.epsilon fun M => NearInst.IsSplitMult M (L.params Pl).R L.V L.rb

/-- The near operators of the level at Floquet exponent `μ` (source 3866-3914): operators with the
pins `IsActualNear` (gap `δ`, output cut `S = ε^{-b}`) whose split multiplier is `nearMU`. -/
def nearOpsAt (μ : ℝ) : NearInst.NearOps (cOf L.ν) K.mZ (L.ρb Pl K) :=
  Classical.epsilon fun o =>
    NearInst.IsActualNear (L.params Pl) L.V L.rb μ K.δ (L.Scut K) o ∧ o.MU = nearMU Pl K L

/-- **`M = M_U`** on the gain-normed spaces (source 3876-3877, 4147, 5779-5782): the near-link
transport `(√π)⁻¹ strIso⁻¹ (g⁻¹ M_U g) velIso` of `nearMU` (`NearOps.MG`).  Independent of `μ`. -/
def multOp : LVel Pl L →L[ℝ] LStr Pl K L :=
  NearInst.NearOps.MG ⟨0, 0, 0, nearMU Pl K L⟩ (gRate Pl) L.ν_pos

/-- `S_N` on the gain-normed spaces, the transport `NearOps.SNG` of the near inverse (source
3911-3920, 5785). -/
def SNop (μ : ℝ) : LStr Pl K L →L[ℝ] LVel Pl L :=
  (nearOpsAt Pl K L μ).SNG (gRate Pl) L.ν_pos

/-- The real form `R_ε : H → H` of the curved body inverse `T_ε = (μ - A_ε)⁻¹P_ε` (source
1675-1677, `NearInst.IsBodyTransport`). -/
def bodyReps (μ : ℝ) : Hsp (cOf L.ν) →L[ℝ] Hsp (cOf L.ν) :=
  Classical.epsilon fun R => NearInst.IsBodyTransport R
    (UnforcedLeray.Short.PartIIa.Teps (P := (L.params Pl).period) (L.params Pl).ν_pos
      (L.params Pl).ε_pos (L.params Pl).c_pos rfl (μ : ℂ))

/-- **The physical body inverse `R_μ = D_μ⁻¹ℙ`** on the return spaces (source 4139-4146, 5781,
5820): the transport `bodyG` of `R_ε` (`NearInst.IsBodyLinked`). -/
def Rop (μ : ℝ) : LSrc L →L[ℝ] LVel Pl L :=
  NearInst.bodyG (bodyReps Pl L μ) (gRate Pl) L.ν_pos

/-- Every near-operator family with split multiplier `nearMU` transports to `multOp`. -/
theorem MG_eq_multOp (o : NearInst.NearOps (cOf L.ν) K.mZ (L.ρb Pl K))
    (h : o.MU = nearMU Pl K L) : o.MG (gRate Pl) L.ν_pos = multOp Pl K L := by
  unfold multOp NearInst.NearOps.MG
  rw [h]

end Near

/-! ## 5. The primary physical operators of the regime -/

/-- The Ward pin of `IsWardPinned` (`Concrete/PhysLayer.lean`) stated on three operators. -/
def IsWardTriple {c mZ ρb γ ν : ℝ} (Yf hf : StrG c mZ ρb γ ν →L[ℝ] VelG c γ ν)
    (Ef : StrG c mZ ρb γ ν →L[ℝ] SrcG c) (ε μ : ℝ) {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo)
    (χy : ℝ → ℝ) (U : ℝ → SpatialField) (p : ℝ → Space → ℝ) : Prop :=
  ∀ (T : StrG c mZ ρb γ ν) (g₁ g₂ : Chart → Ten3),
    ((chiOStr c mZ ρb γ ν hχo T).fst : Chart → Ten3) =ᵐ[gainZ1Measure c mZ γ ν] g₁ →
    ((chiOStr c mZ ρb γ ν hχo T).snd : Chart → Ten3) =ᵐ[gainHTMeasure c ρb γ ν] g₂ →
      (Yf T : Chart → Merid) =ᵐ[bodyMeasure c γ ν]
          coefOf ε⁻¹ (wardY ν μ ε⁻¹ c χy (g₁ + g₂)) ∧
        (hf T : Chart → Merid) =ᵐ[bodyMeasure c γ ν]
          coefOf ε⁻¹ (wardH ν μ ε⁻¹ c χy U (g₁ + g₂)) ∧
        (Ef T : Chart → Merid) =ᵐ[srcMeasure c]
          coefOf ε⁻¹ (wardE ν μ ε⁻¹ c χy U p (g₁ + g₂))

theorem isWardPinned_iff {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff]
    [NormedSpace ℝ Aff] [CompleteSpace Aff] (B : ReturnBase c mZ ρb γ ν Aff) (ε μ : ℝ)
    {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) (χy : ℝ → ℝ) (U : ℝ → SpatialField)
    (p : ℝ → Space → ℝ) :
    IsWardPinned B ε μ hχo χy U p ↔ IsWardTriple B.Yf B.hf B.Ef ε μ hχo χy U p := Iff.rfl

/-- The `𝔯_A` pin of `IsRAPinned` (`Concrete/PhysLayer.lean`) stated on the operators. -/
def IsRAOp {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff] [NormedSpace ℝ Aff]
    (M : VelG c γ ν →L[ℝ] StrG c mZ ρb γ ν) (hA : Aff →L[ℝ] VelG c γ ν)
    (FA EA rA : Aff →L[ℝ] SrcG c) (ι : Aff →ₗ[ℝ] (ℝ → Mat3)) (χf : ℝ → ℝ) (ε μ : ℝ) : Prop :=
  ∀ (A : Aff) (Φ : ℝ × Space → CVec3), IsPhaseTest (2 * ε * c) Φ →
    pairF (2 * ε * c) (fun x => L0T ν Φ x + (μ : ℂ) • Φ x) (velPhys ε⁻¹ c (hA A)) -
        stressPair (2 * ε * c) (strPhys ε⁻¹ c (strSum (M (hA A)))) Φ =
      pairF (2 * ε * c) Φ (velPhys ε⁻¹ c ((FA A + EA A + rA A : SrcG c) : Chart → Merid)) -
        scalarPair (2 * ε * c) (sPsiPhys ν ε⁻¹ χf (ι A)) Φ

theorem isRAPinned_iff {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff]
    [NormedSpace ℝ Aff] [CompleteSpace Aff] (B : ReturnBase c mZ ρb γ ν Aff)
    (ι : Aff →ₗ[ℝ] (ℝ → Mat3)) (χf : ℝ → ℝ) (ε μ : ℝ) :
    IsRAPinned B ι χf ε μ ↔ IsRAOp B.M B.hA B.FA B.EA B.rA ι χf ε μ := Iff.rfl

section Ops

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)

/-- **`S_μ = R_μℙ div`** (source 4145, `free:weak-stress` 1556-1572): the weak stress inverse. -/
def Sop (μ : ℝ) : LStr Pl K L →L[ℝ] LVel Pl L :=
  Classical.epsilon fun S => IsWeakStressInverse S L.ε μ

/-- **The Ward fields** `(Y[T], h[T], Ẽ_μ[T])` (source 4161-4303) on the background `U = V + r_b`
with pressure `p`, cutoffs `χ_o, χ_y`. -/
def wardOps (μ : ℝ) :
    (LStr Pl K L →L[ℝ] LVel Pl L) × (LStr Pl K L →L[ℝ] LVel Pl L) × (LStr Pl K L →L[ℝ] LSrc L) :=
  Classical.epsilon fun t => IsWardTriple t.1 t.2.1 t.2.2 L.ε μ K.hχo K.χy L.U L.pres

/-- **`A ↦ ĥ_A`** (source 4979-4980), coefficient convention of `VelG`. Independent of `μ`. -/
def hAOp : AffSp K.as →L[ℝ] LVel Pl L :=
  Classical.epsilon fun H => ∀ A, (H A : Chart → Merid) =ᵐ[bodyMeasure (cOf L.ν) (gRate Pl) L.ν]
    hAcoef L.ν L.ε K.χf (affIota K.as A)

/-- **`A ↦ F_A`** (source 4981), coefficient convention of `SrcG`. -/
def FAOp (μ : ℝ) : AffSp K.as →L[ℝ] LSrc L :=
  Classical.epsilon fun F => ∀ A, (F A : Chart → Merid) =ᵐ[srcMeasure (cOf L.ν)]
    FAcoef L.ν μ K.χf (affIota K.as A)

/-- **`A ↦ E_A`** (source 4981), coefficient convention of `SrcG`. -/
def EAOp (μ : ℝ) : AffSp K.as →L[ℝ] LSrc L :=
  Classical.epsilon fun F => ∀ A, (F A : Chart → Merid) =ᵐ[srcMeasure (cOf L.ν)]
    EAcoef L.ν μ K.χf (affIota K.as A)

/-- **`A ↦ 𝔯_A`** (Lemma `ret:physical-affine`, source 5001-5008, 5022-5050): the exact
unprojected residual `𝔯_A = D_μĥ_A + div M_Uĥ_A - F_A - E_A - ∇_y(sΨ_A)` against every phase test. -/
def rAOp (μ : ℝ) : AffSp K.as →L[ℝ] LSrc L :=
  Classical.epsilon fun r => IsRAOp (multOp Pl K L) (hAOp Pl K L) (FAOp K L μ) (EAOp K L μ) r
    (affIota K.as) K.χf L.ε μ

/-- **`𝓛`** (`source-class:L`, 4792-4796) as a map into `𝒜`. -/
def LjOp (μ : ℝ) : LStr Pl K L →L[ℝ] AffSp K.as :=
  Classical.epsilon fun Lj => ∀ T, affIota K.as (Lj T) =
    LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T

/-- **`a_μ`** (source 4807-4811) as an element of `𝒜`. -/
def aMuOp (μ : ℝ) : AffSp K.as :=
  Classical.epsilon fun a => affIota K.as a = aMuFun μ

/-- The Mellin function `𝒥` of the planar data, on real arguments (source 4703, 5924). -/
def planarJ : ℂ → ℂ := fun z => Pl.mellinJ z.re

/-- **`Λ_{μ,ν}`** (source 4812-4815), with `λ = Pl.eigenvalue`, `κ = Pl.kappa`,
`ℓ₊(H₀) = Pl.strainCoupling` and `𝒥 = Pl.mellinJ`. -/
def LamOp (μ : ℝ) : AffSp K.as →L[ℝ] ℝ :=
  Classical.epsilon fun l => ∀ A, l A =
    LamFun Pl.eigenvalue Pl.kappa Pl.strainCoupling (planarJ Pl) L.ε L.ν μ K.χf (affIota K.as A)

/-- **`𝒦^flat_{μ,ν} = 𝓛_{μ,ν}𝔗_{μ,ν}`** (source 4804-4806) on `𝒜`, with the flat setting of the
level. -/
def KflatOp (μ : ℝ) : AffSp K.as →L[ℝ] AffSp K.as :=
  Classical.epsilon fun Kf => ∀ A, affIota K.as (Kf A) =
    KflatFun L.flat (cOf L.ν) L.ν L.ε μ K.χo K.χy K.χf (affIota K.as A)

end Ops

/-! ## 6. The pinned base and the operators of the return system (source 5777-5833) -/

section Base

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)

/-- The graph `𝓔_ν = {(T, w) : T = Mw}` of the regime with the pair norm, `a = γ/8` (source
5640-5658).  It does not depend on `μ`. -/
abbrev LGam := PairSp (multOp Pl K L) (gRate Pl / 8) L.ν

/-- The return base of the regime with primary fields the pinned operators and a two-sided inverse
`D` of `D_N = I + MS_N` (source 5785-5787). -/
abbrev baseOf (μ : ℝ) (D : LStr Pl K L →L[ℝ] LStr Pl K L)
    (h₁ : ∀ T, D (T + multOp Pl K L (SNop Pl K L μ T)) = T)
    (h₂ : ∀ T, D T + multOp Pl K L (SNop Pl K L μ (D T)) = T) :
    ReturnBase (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν (AffSp K.as) where
  M := multOp Pl K L
  S := Sop Pl K L μ
  SN := SNop Pl K L μ
  R := Rop Pl L μ
  Yf := (wardOps Pl K L μ).1
  hf := (wardOps Pl K L μ).2.1
  Ef := (wardOps Pl K L μ).2.2
  Lj := LjOp Pl K L μ
  hA := hAOp Pl K L
  FA := FAOp K L μ
  EA := EAOp K L μ
  rA := rAOp Pl K L μ
  DNinv := D
  DNinv_left := h₁
  DNinv_right := h₂
  aMu := aMuOp K μ
  Lam := LamOp Pl K L μ
  Kflat := KflatOp K L μ

/-- The near layer of the regime at `μ` (source 3866-3920, 3943-3951): the near operators have the
split multiplier `nearMU` and `D_N = I + M_US_N` is a unit of `Z →L Z` (`NearSolverC`). -/
def NearAt (μ : ℝ) : Prop :=
  IsUnit (nearOpsAt Pl K L μ).DN ∧ (nearOpsAt Pl K L μ).MU = nearMU Pl K L

theorem NearAt.left {Pl K L} {μ : ℝ} (h : NearAt Pl K L μ) (T : LStr Pl K L) :
    (nearOpsAt Pl K L μ).DNinvG (gRate Pl) L.ν_pos (T + multOp Pl K L (SNop Pl K L μ T)) = T := by
  have := NearInst.NearOps.DNinvG_left (nearOpsAt Pl K L μ) L.ν_pos h.1 T
  rwa [MG_eq_multOp Pl K L _ h.2] at this

theorem NearAt.right {Pl K L} {μ : ℝ} (h : NearAt Pl K L μ) (T : LStr Pl K L) :
    (nearOpsAt Pl K L μ).DNinvG (gRate Pl) L.ν_pos T +
      multOp Pl K L (SNop Pl K L μ ((nearOpsAt Pl K L μ).DNinvG (gRate Pl) L.ν_pos T)) = T := by
  have := NearInst.NearOps.DNinvG_right (nearOpsAt Pl K L μ) L.ν_pos h.1 T
  rwa [MG_eq_multOp Pl K L _ h.2] at this

/-- **The pinned return base of the regime** (source 5777-5833), with `D_N⁻¹ = NearOps.DNinvG`
(source 3914-3917, 5787). -/
def concreteBase (μ : ℝ) (h : NearAt Pl K L μ) :
    ReturnBase (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν (AffSp K.as) :=
  baseOf Pl K L μ ((nearOpsAt Pl K L μ).DNinvG (gRate Pl) L.ν_pos) h.left h.right

/-- **`ConcreteReturnOps`** (one regime: `c = ν⁻²`, `ρ_b = C₀ν^{-k₀}e^{m₀/ν}ε^{3/11}`, the exact
background `U = V + r_b`): `B.toOps` for the pinned return base `B` (source 5785-5833). -/
def ConcreteReturnOps (μ : ℝ) (h : NearAt Pl K L μ) :
    ReturnOps (LVel Pl L) (LStr Pl K L) (LSrc L) (AffSp K.as) (LGam Pl K L) :=
  (concreteBase Pl K L μ h).toOps

/-- The return operators of the regime without the invertibility proof (the field `ops` of
`concreteReturnSeq`): `(baseOf … D h₁ h₂).toOps` for a two-sided inverse `D` of `D_N`, which is
unique (`concreteOps_eq`). -/
def concreteOps (μ : ℝ) :
    ReturnOps (LVel Pl L) (LStr Pl K L) (LSrc L) (AffSp K.as) (LGam Pl K L) :=
  Classical.epsilon fun o => ∃ (D : LStr Pl K L →L[ℝ] LStr Pl K L)
    (h₁ : ∀ T, D (T + multOp Pl K L (SNop Pl K L μ T)) = T)
    (h₂ : ∀ T, D T + multOp Pl K L (SNop Pl K L μ (D T)) = T),
    o = (baseOf Pl K L μ D h₁ h₂).toOps

/-- A left inverse and a right inverse of the same map coincide. -/
theorem dnInv_unique {X : Type} (F D D' : X → X) (h₁ : ∀ T, D (F T) = T)
    (h₂ : ∀ T, F (D' T) = T) : D = D' := by
  funext T
  calc D T = D (F (D' T)) := by rw [h₂]
    _ = D' T := h₁ _

/-- **`concreteOps = ConcreteReturnOps`** whenever `D_N` is a unit. -/
theorem concreteOps_eq (μ : ℝ) (h : NearAt Pl K L μ) :
    concreteOps Pl K L μ = ConcreteReturnOps Pl K L μ h := by
  have hex : ∃ o : ReturnOps (LVel Pl L) (LStr Pl K L) (LSrc L) (AffSp K.as) (LGam Pl K L),
      ∃ (D : LStr Pl K L →L[ℝ] LStr Pl K L)
        (h₁ : ∀ T, D (T + multOp Pl K L (SNop Pl K L μ T)) = T)
        (h₂ : ∀ T, D T + multOp Pl K L (SNop Pl K L μ (D T)) = T),
        o = (baseOf Pl K L μ D h₁ h₂).toOps :=
    ⟨_, _, h.left, h.right, rfl⟩
  obtain ⟨D, h₁, h₂, hD⟩ := Classical.epsilon_spec hex
  have hDD : D = (nearOpsAt Pl K L μ).DNinvG (gRate Pl) L.ν_pos := by
    have := dnInv_unique (fun T => T + multOp Pl K L (SNop Pl K L μ T)) D
      ((nearOpsAt Pl K L μ).DNinvG (gRate Pl) L.ν_pos) h₁ h.right
    exact ContinuousLinearMap.ext (congrFun this)
  subst hDD
  exact hD

end Base

/-! ## 7. The pins of the concrete base

Each pin of `Concrete/PhysLayer.lean`, `Concrete/SourceL.lean` and `Concrete/ReturnOps.lean` holds
for `concreteBase` as soon as the pinned operator exists (`Classical.epsilon_spec`); the
existence statements are the leaves. -/

section Pins

variable {Pl : PlanarData} {K : ReturnConsts} {L : ReturnLevel} {μ : ℝ}

/-- The split multiplier is determined by its pin (a.e. in both components). -/
theorem isSplitMult_unique {c mZ ρb R : ℝ} {V rb : ℝ → SpatialField}
    {M M' : Hsp c →L[ℝ] Zsp c mZ ρb} (h : NearInst.IsSplitMult M R V rb)
    (h' : NearInst.IsSplitMult M' R V rb) : M = M' := by
  ext1 u
  obtain ⟨h1, h2⟩ := h u
  obtain ⟨h1', h2'⟩ := h' u
  apply WithLp.ofLp_injective
  refine Prod.ext ?_ ?_
  · exact Lp.ext (h1.trans h1'.symm)
  · exact Lp.ext (h2.trans h2'.symm)

theorem nearMU_spec (h : ∃ M : Hsp (cOf L.ν) →L[ℝ] Zsp (cOf L.ν) K.mZ (L.ρb Pl K),
    NearInst.IsSplitMult M (L.params Pl).R L.V L.rb) :
    NearInst.IsSplitMult (nearMU Pl K L) (L.params Pl).R L.V L.rb :=
  Classical.epsilon_spec h

/-- The near operators of the level exist as soon as operators with the pins `IsActualNear` exist
(`NearInst.NearOpsExistC`); their split multiplier is then `nearMU`. -/
theorem nearOpsAt_spec
    (h : ∃ o : NearInst.NearOps (cOf L.ν) K.mZ (L.ρb Pl K),
      NearInst.IsActualNear (L.params Pl) L.V L.rb μ K.δ (L.Scut K) o) :
    NearInst.IsActualNear (L.params Pl) L.V L.rb μ K.δ (L.Scut K) (nearOpsAt Pl K L μ) ∧
      (nearOpsAt Pl K L μ).MU = nearMU Pl K L := by
  obtain ⟨o, ho⟩ := h
  have hM : NearInst.IsSplitMult (nearMU Pl K L) (L.params Pl).R L.V L.rb :=
    nearMU_spec ⟨o.MU, ho.split⟩
  exact Classical.epsilon_spec (p := fun o : NearInst.NearOps (cOf L.ν) K.mZ (L.ρb Pl K) =>
      NearInst.IsActualNear (L.params Pl) L.V L.rb μ K.δ (L.Scut K) o ∧ o.MU = nearMU Pl K L)
    ⟨o, ho, isSplitMult_unique ho.split hM⟩

/-- `NearAt` from the existence of the actual near operators and the invertibility of their `D_N`
(the conclusion `IsUnit o.DN` of `NearInst.NearSolverC` for every such `o`). -/
theorem nearAt_of
    (h : ∃ o : NearInst.NearOps (cOf L.ν) K.mZ (L.ρb Pl K),
      NearInst.IsActualNear (L.params Pl) L.V L.rb μ K.δ (L.Scut K) o)
    (hU : ∀ o : NearInst.NearOps (cOf L.ν) K.mZ (L.ρb Pl K),
      NearInst.IsActualNear (L.params Pl) L.V L.rb μ K.δ (L.Scut K) o → IsUnit o.DN) :
    NearAt Pl K L μ :=
  ⟨hU _ (nearOpsAt_spec h).1, (nearOpsAt_spec h).2⟩

variable (h : NearAt Pl K L μ)

include h in
/-- The near link (`NearInst.IsNearLinked`, source 3866-3920, 5777-5787). -/
theorem concreteBase_isNearLinked :
    NearInst.IsNearLinked (concreteBase Pl K L μ h) (nearOpsAt Pl K L μ) L.ν_pos :=
  ⟨(MG_eq_multOp Pl K L _ h.2).symm, rfl⟩

include h in
/-- The body link (`NearInst.IsBodyLinked`, source 4084-4086, 4139-4146, 5781). -/
theorem concreteBase_isBodyLinked :
    NearInst.IsBodyLinked (concreteBase Pl K L μ h) (bodyReps Pl L μ) L.ν_pos := rfl

include h in
/-- **(a)** `M = M_U` (`IsExactMultiplier`, source 2669-2672, 3876-3877, 4147, 5779-5782), from the
transport pin `NearInst.MultPinOfLink` and the split pin of `nearMU`. -/
theorem concreteBase_isExactMultiplier (hpin : NearInst.MultPinOfLink)
    (hs : ∃ M : Hsp (cOf L.ν) →L[ℝ] Zsp (cOf L.ν) K.mZ (L.ρb Pl K),
      NearInst.IsSplitMult M (L.params Pl).R L.V L.rb) :
    IsExactMultiplier (concreteBase Pl K L μ h) L.ε⁻¹ L.V L.rb :=
  hpin _ _ _ _ _ L.ν_pos _ (concreteBase Pl K L μ h) ⟨0, 0, 0, nearMU Pl K L⟩ _ _ _
    (nearMU_spec hs) rfl

include h in
/-- **(b)** `S = S_μ` (`IsStressInverse`, source 4145, 1556-1572). -/
theorem concreteBase_isStressInverse
    (hS : ∃ S : LStr Pl K L →L[ℝ] LVel Pl L, IsWeakStressInverse S L.ε μ) :
    IsStressInverse (concreteBase Pl K L μ h) L.ε μ :=
  Classical.epsilon_spec hS

include h in
/-- **(c)** The Ward fields (`IsWardPinned`, source 4161-4303). -/
theorem concreteBase_isWardPinned
    (hW : ∃ t : (LStr Pl K L →L[ℝ] LVel Pl L) × (LStr Pl K L →L[ℝ] LVel Pl L) ×
        (LStr Pl K L →L[ℝ] LSrc L),
      IsWardTriple t.1 t.2.1 t.2.2 L.ε μ K.hχo K.χy L.U L.pres) :
    IsWardPinned (concreteBase Pl K L μ h) L.ε μ K.hχo K.χy L.U L.pres :=
  Classical.epsilon_spec hW

theorem hAOp_spec (hH : ∃ H : AffSp K.as →L[ℝ] LVel Pl L, ∀ A,
      (H A : Chart → Merid) =ᵐ[bodyMeasure (cOf L.ν) (gRate Pl) L.ν]
        hAcoef L.ν L.ε K.χf (affIota K.as A)) (A : AffSp K.as) :
    (hAOp Pl K L A : Chart → Merid) =ᵐ[bodyMeasure (cOf L.ν) (gRate Pl) L.ν]
      hAcoef L.ν L.ε K.χf (affIota K.as A) :=
  Classical.epsilon_spec hH A

theorem FAOp_spec (hF : ∃ F : AffSp K.as →L[ℝ] LSrc L, ∀ A,
      (F A : Chart → Merid) =ᵐ[srcMeasure (cOf L.ν)] FAcoef L.ν μ K.χf (affIota K.as A))
    (A : AffSp K.as) :
    (FAOp K L μ A : Chart → Merid) =ᵐ[srcMeasure (cOf L.ν)]
      FAcoef L.ν μ K.χf (affIota K.as A) :=
  Classical.epsilon_spec hF A

theorem EAOp_spec (hE : ∃ E : AffSp K.as →L[ℝ] LSrc L, ∀ A,
      (E A : Chart → Merid) =ᵐ[srcMeasure (cOf L.ν)] EAcoef L.ν μ K.χf (affIota K.as A))
    (A : AffSp K.as) :
    (EAOp K L μ A : Chart → Merid) =ᵐ[srcMeasure (cOf L.ν)]
      EAcoef L.ν μ K.χf (affIota K.as A) :=
  Classical.epsilon_spec hE A

/-- With the affine field data of the regime (`AffineFieldData`, `ReturnInst/AffineFields.lean`),
the pinned affine fields are the constructed maps `hAL`, `FAL`, `EAL`. -/
theorem affineOps_eq (hd : AffineFieldData K.as L.ν μ L.ε (gRate Pl) K.χf (affIota K.as)) :
    hAOp Pl K L = hd.hAL ∧ FAOp K L μ = hd.FAL ∧ EAOp K L μ = hd.EAL := by
  refine ⟨?_, ?_, ?_⟩
  · ext1 A
    exact Lp.ext ((hAOp_spec ⟨hd.hAL, hd.hA.toCLM_ae⟩ A).trans (hd.hA.toCLM_ae A).symm)
  · ext1 A
    exact Lp.ext ((FAOp_spec ⟨hd.FAL, hd.FA.toCLM_ae⟩ A).trans (hd.FA.toCLM_ae A).symm)
  · ext1 A
    exact Lp.ext ((EAOp_spec ⟨hd.EAL, hd.EA.toCLM_ae⟩ A).trans (hd.EA.toCLM_ae A).symm)

include h in
/-- `ĥ_A, F_A, E_A` are pinned (`IsAffinePinned`, source 4969-4985), from the affine field data. -/
theorem concreteBase_isAffinePinned
    (hd : AffineFieldData K.as L.ν μ L.ε (gRate Pl) K.χf (affIota K.as)) :
    IsAffinePinned (concreteBase Pl K L μ h) (affIota K.as) K.χf μ L.ε := fun A =>
  ⟨hAOp_spec ⟨hd.hAL, hd.hA.toCLM_ae⟩ A, FAOp_spec ⟨hd.FAL, hd.FA.toCLM_ae⟩ A,
    EAOp_spec ⟨hd.EAL, hd.EA.toCLM_ae⟩ A⟩

include h in
/-- **(d)** `𝔯_A` is pinned (`IsRAPinned`, source 5001-5050). -/
theorem concreteBase_isRAPinned
    (hr : ∃ r : AffSp K.as →L[ℝ] LSrc L, IsRAOp (multOp Pl K L) (hAOp Pl K L) (FAOp K L μ)
      (EAOp K L μ) r (affIota K.as) K.χf L.ε μ) :
    IsRAPinned (concreteBase Pl K L μ h) (affIota K.as) K.χf L.ε μ :=
  Classical.epsilon_spec hr

theorem rAOp_spec (hr : ∃ r : AffSp K.as →L[ℝ] LSrc L, IsRAOp (multOp Pl K L) (hAOp Pl K L)
      (FAOp K L μ) (EAOp K L μ) r (affIota K.as) K.χf L.ε μ) :
    IsRAOp (multOp Pl K L) (hAOp Pl K L) (FAOp K L μ) (EAOp K L μ) (rAOp Pl K L μ)
      (affIota K.as) K.χf L.ε μ :=
  Classical.epsilon_spec hr

/-- `𝓛` as a continuous linear map into `𝒜` from membership, linearity and the bound
(`SourceLInAff`, `SourceLLinear`, `SourceLBounded`; source 4792-4803, 4930-4937), the pattern of
`IsL2Family.toCLM`. -/
def ljCLM {c mZ ρb γ ν ε : ℝ} (as μ : ℝ) (χo χy : ℝ → ℝ)
    (hIn : ∀ T : StrG c mZ ρb γ ν, IsAffElem as (LjFun c mZ ρb γ ν ε μ χo χy T))
    (hLin : ∀ (T T' : StrG c mZ ρb γ ν) (r : ℝ),
      LjFun c mZ ρb γ ν ε μ χo χy (T + T') =
          LjFun c mZ ρb γ ν ε μ χo χy T + LjFun c mZ ρb γ ν ε μ χo χy T' ∧
        LjFun c mZ ρb γ ν ε μ χo χy (r • T) = r • LjFun c mZ ρb γ ν ε μ χo χy T)
    (C : ℝ) (hB : ∀ T : StrG c mZ ρb γ ν, affNorm as (LjFun c mZ ρb γ ν ε μ χo χy T) ≤ C * ‖T‖) :
    StrG c mZ ρb γ ν →L[ℝ] AffSp as :=
  LinearMap.mkContinuous
    { toFun := fun T => ⟨LjFun c mZ ρb γ ν ε μ χo χy T, hIn T⟩
      map_add' := fun T T' => Subtype.ext (hLin T T' 1).1
      map_smul' := fun r T => Subtype.ext (hLin T T r).2 }
    C fun T => by
      rw [AffSp.norm_def]
      exact hB T

theorem ljCLM_apply {c mZ ρb γ ν ε : ℝ} (as μ : ℝ) (χo χy : ℝ → ℝ) hIn hLin (C : ℝ) hB
    (T : StrG c mZ ρb γ ν) :
    affIota as (ljCLM (ε := ε) as μ χo χy hIn hLin C hB T) = LjFun c mZ ρb γ ν ε μ χo χy T := rfl

/-- The pinned `𝓛` exists from the source facts of `Concrete/SourceL.lean` (source 4792-4803,
4917-4937) at one regime. -/
theorem exists_LjOp_of (hc : LHyp (cOf L.ν) L.ν L.ε μ K.χo K.χy) (hmZ : 3 / 2 < K.mZ)
    (hγ : 0 < gRate Pl) (has : 0 < K.as) (hK : ({μ} : Set ℝ) ⊆ Ioo 0 (1 / 4))
    (hIn : SourceLInAff K.as (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy)
    (hLin : SourceLLinear (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy)
    (hB : SourceLBounded K.as K.mZ (gRate Pl) {μ} K.χo K.χy) :
    ∃ Lj : LStr Pl K L →L[ℝ] AffSp K.as, ∀ T, affIota K.as (Lj T) =
      LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T := by
  obtain ⟨C, k, hC⟩ := hB has isCompact_singleton hK hmZ hγ
  exact ⟨ljCLM K.as μ K.χo K.χy (hIn has hc hmZ hγ) (hLin hc hmZ hγ)
    (C * L.ν⁻¹ ^ k * (L.ε ^ 3 * Real.exp (gRate Pl / L.ν)))
    (hC (cOf L.ν) (L.ρb Pl K) L.ν L.ε μ hc (Set.mem_singleton μ)), fun T => rfl⟩

/-- The pinned `a_μ` exists (`AMuInAff`, source 4807-4811). -/
theorem exists_aMuOp_of (ha : AMuInAff K.as μ) (has : 0 ≤ K.as) (hμ : 0 < μ) :
    ∃ a : AffSp K.as, affIota K.as a = aMuFun μ :=
  ⟨⟨aMuFun μ, ha has hμ⟩, rfl⟩

include h in
/-- `𝓛, a_μ, Λ, 𝒦^flat` are pinned (`IsSourceLPinned`, source 4792-4815). -/
theorem concreteBase_isSourceLPinned
    (hLj : ∃ Lj : LStr Pl K L →L[ℝ] AffSp K.as, ∀ T, affIota K.as (Lj T) =
      LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T)
    (ha : ∃ a : AffSp K.as, affIota K.as a = aMuFun μ)
    (hLam : ∃ l : AffSp K.as →L[ℝ] ℝ, ∀ A, l A =
      LamFun Pl.eigenvalue Pl.kappa Pl.strainCoupling (planarJ Pl) L.ε L.ν μ K.χf (affIota K.as A))
    (hKf : ∃ Kf : AffSp K.as →L[ℝ] AffSp K.as, ∀ A, affIota K.as (Kf A) =
      KflatFun L.flat (cOf L.ν) L.ν L.ε μ K.χo K.χy K.χf (affIota K.as A)) :
    IsSourceLPinned (concreteBase Pl K L μ h) (affIota K.as) L.flat Pl.eigenvalue Pl.kappa
      Pl.strainCoupling (planarJ Pl) L.ε μ K.χo K.χy K.χf :=
  ⟨Classical.epsilon_spec hLj, Classical.epsilon_spec ha, Classical.epsilon_spec hLam,
    Classical.epsilon_spec hKf⟩

end Pins

/-! ## 8. The phase-locked sequence of regimes (source 5926-5950) -/

/-- The phase-locked viscosities (source 5928-5934): `ν_n = lockedNu(ω, Im κ, arg 𝒞(σ₀))`, with
`ω/ν_n - Im κ log ν_n + arg 𝒞(σ₀) = 2πn sign ω` for large `n`, `ω = Im λ`.  This is the witness
of `PhaseLocked.phaseLockedSequence` and the Spine's `nuSeq` (`ConstructionData.phaseLockedNu`). -/
def retNu (Pl : PlanarData) (σ₀ : ℝ) (n : ℕ) : ℝ :=
  UnforcedLeray.Blueprint.PhaseLock.lockedNu Pl.eigenvalue.im Pl.kappa.im
    (Complex.arg (Pl.signedCoeff σ₀)) n

theorem retNu_pos (Pl : PlanarData) (σ₀ : ℝ) (n : ℕ) : 0 < retNu Pl σ₀ n :=
  UnforcedLeray.Blueprint.PhaseLock.lockedNu_pos _ _ _ n

theorem retNu_tendsto {Pl : PlanarData} (σ₀ : ℝ) (hω : Pl.eigenvalue.im ≠ 0) :
    Tendsto (retNu Pl σ₀) atTop (nhds 0) :=
  UnforcedLeray.Blueprint.PhaseLock.tendsto_lockedNu hω _ _

/-- The phase lock (source 5928-5934). -/
theorem retNu_phase {Pl : PlanarData} (σ₀ : ℝ) (hω : Pl.eigenvalue.im ≠ 0) :
    ∀ᶠ n : ℕ in atTop, Pl.eigenvalue.im / retNu Pl σ₀ n - Pl.kappa.im * Real.log (retNu Pl σ₀ n) +
      Complex.arg (Pl.signedCoeff σ₀) = 2 * Real.pi * Real.sign Pl.eigenvalue.im * n :=
  UnforcedLeray.Blueprint.PhaseLock.eventually_phase_lockedNu hω _ _

/-- The amplitudes `ε_n = (e^{-γ/ν_n} ν_n^{Re κ - 5 - 2σ₀} / (2|𝒞(σ₀)|))^{1/3}` (source 5936-5940;
the Spine's `epsSeq`, `ConstructionData.amplitude`). -/
def retEps (Pl : PlanarData) (σ₀ : ℝ) (n : ℕ) : ℝ :=
  (Real.exp (-(Pl.eigenvalue.re / retNu Pl σ₀ n)) * retNu Pl σ₀ n ^ (Pl.kappa.re - 5 - 2 * σ₀) /
    (2 * ‖Pl.signedCoeff σ₀‖)) ^ (1 / 3 : ℝ)

theorem retEps_pos {Pl : PlanarData} {σ₀ : ℝ} (h : Pl.signedCoeff σ₀ ≠ 0) (n : ℕ) :
    0 < retEps Pl σ₀ n :=
  Real.rpow_pos_of_pos (div_pos (mul_pos (Real.exp_pos _)
    (Real.rpow_pos_of_pos (retNu_pos Pl σ₀ n) _)) (mul_pos two_pos (norm_pos_iff.2 h))) _

/-- The data of the concrete return sequence (source 5926-5950): the planar reference `Pl` and
`σ₀` with `𝒞(σ₀) ≠ 0` (5924-5927), the fixed choices, the slow age `Σ`, and at every level `n`
(viscosity `retNu`, amplitude `retEps`, `c_n = ν_n⁻²`) the actual train, the exact split
`U_n = V_n + r_{b,n}` with inlet support, the global pressure and the flat setting.  The source
fixes one exact background per level and holds it while `σ` varies (5933-5936); the pins of the
per-level data (`IIb.BgRegime`, `IIb.ExactSplitII`, `IsExactProfile`, the flat setting
`FlatSettingInst.actualFlatSetting`) are hypotheses of the statements about the sequence. -/
structure SeqData where
  Pl : PlanarData
  σ₀ : ℝ
  coeff_ne : Pl.signedCoeff σ₀ ≠ 0
  K : ReturnConsts
  Sig : ℝ
  Sig_pos : 0 < Sig
  train : ∀ n, UnforcedLeray.B0140.TrainSol (retNu Pl σ₀ n) (cOf (retNu Pl σ₀ n))
  train_buc : ∀ n, UnforcedLeray.Short.PartI.IsBUCTrain (train n)
  train_stream_smooth : ∀ n, ContDiffOn ℝ ∞
    (fun x : ℝ × UnforcedLeray.Cyl.Plane => (train n).ψ x.1 x.2) (Set.Ioi 0 ×ˢ Set.univ)
  Sin : ℕ → ℝ
  V : ℕ → ℝ → SpatialField
  rb : ℕ → ℝ → SpatialField
  pres : ℕ → ℝ → Space → ℝ
  flat : ℕ → ConcreteYF.FlatSetting

namespace SeqData

variable (D : SeqData)

/-- The level `n` of the sequence. -/
def level (n : ℕ) : ReturnLevel where
  ν := retNu D.Pl D.σ₀ n
  ε := retEps D.Pl D.σ₀ n
  Sig := D.Sig
  ν_pos := retNu_pos D.Pl D.σ₀ n
  ε_pos := retEps_pos D.coeff_ne n
  Sig_pos := D.Sig_pos
  train := D.train n
  train_buc := D.train_buc n
  train_stream_smooth := D.train_stream_smooth n
  Sin := D.Sin n
  V := D.V n
  rb := D.rb n
  pres := D.pres n
  flat := D.flat n

/-- The Floquet window `μ_n(z) = σ₀ + z/(2|log ν_n|)` (source 5946, `Scalar.muWin`). -/
def mu (n : ℕ) (z : ℝ) : ℝ := muWin D.σ₀ (retNu D.Pl D.σ₀ n) z

end SeqData

/-- **The concrete return sequence** (source 5926-5950): at level `n` and `z ∈ ℝ` the return
operators `concreteOps` of the regime at `μ = μ_n(z)`; spaces `VelG, StrG, SrcG` at `c_n = ν_n⁻²`,
`γ = Re λ`, `𝒜 = AffSp a_s`, the graph `𝓔_ν` of `M_U`, and the gradient space `GrdG c_n`.

`G n : A ↦ ∇ĥ_A` is the gradient of the affine lift at level `n` (source 4976-4985, 5011-5013),
pinned by `IsAffineGradPinned` (`Concrete/AffineGradPin.lean`).  It is an argument because that
file cannot yet be imported together with `Concrete/SourceL.lean` (both declare
`Concrete.affTerm_nonneg`: `ReturnAffExamples.lean:32`, `SourceL.lean:367`); statements that
involve `gradhA` assume the pin of `G`. -/
def concreteReturnSeq (D : SeqData)
    (G : ∀ n, AffSp D.K.as →L[ℝ] GrdG (cOf (retNu D.Pl D.σ₀ n))) : ReturnSeq where
  Vel n := LVel D.Pl (D.level n)
  Str n := LStr D.Pl D.K (D.level n)
  Src n := LSrc (D.level n)
  Aff _ := AffSp D.K.as
  Gam n := LGam D.Pl D.K (D.level n)
  Grd n := GrdG (cOf (retNu D.Pl D.σ₀ n))
  ν n := retNu D.Pl D.σ₀ n
  ops n z := concreteOps D.Pl D.K (D.level n) (D.mu n z)
  gradhA n _ := (G n : AffSp D.K.as →ₗ[ℝ] GrdG (cOf (retNu D.Pl D.σ₀ n)))

theorem concreteReturnSeq_ops (D : SeqData) G (n : ℕ) (z : ℝ) :
    (concreteReturnSeq D G).ops n z = concreteOps D.Pl D.K (D.level n) (D.mu n z) := rfl

/-- Where the near layer is invertible, the operators of the sequence are `B.toOps` for the pinned
base (`ConcreteReturnOps`). -/
theorem concreteReturnSeq_ops_eq (D : SeqData) G (n : ℕ) (z : ℝ)
    (h : NearAt D.Pl D.K (D.level n) (D.mu n z)) :
    (concreteReturnSeq D G).ops n z = ConcreteReturnOps D.Pl D.K (D.level n) (D.mu n z) h :=
  concreteOps_eq _ _ _ _ h

/-- The near-inverse identities of the sequence (source 5787) where the near layer is invertible. -/
theorem concreteReturnSeq_isNearInverse (D : SeqData) G (n : ℕ) (z : ℝ)
    (h : NearAt D.Pl D.K (D.level n) (D.mu n z)) :
    ((concreteReturnSeq D G).ops n z).IsNearInverse := by
  rw [concreteReturnSeq_ops_eq D G n z h]
  exact (concreteBase _ _ _ _ h).toOps_isNearInverse

/-- The graph and lift identities of the sequence (source 5790-5818) where the near layer is
invertible. -/
theorem concreteReturnSeq_isGraphLift (D : SeqData) G (n : ℕ) (z : ℝ)
    (h : NearAt D.Pl D.K (D.level n) (D.mu n z)) :
    ((concreteReturnSeq D G).ops n z).IsGraphLift := by
  rw [concreteReturnSeq_ops_eq D G n z h]
  exact (concreteBase _ _ _ _ h).toOps_isGraphLift

/-- The pair norm of `𝓔_ν` along the sequence (source 5657-5658) where the near layer is
invertible. -/
theorem concreteReturnSeq_pairNorm (D : SeqData) G (n : ℕ) (z : ℝ)
    (h : NearAt D.Pl D.K (D.level n) (D.mu n z)) (V : (concreteReturnSeq D G).Gam n) :
    ‖V‖ = ‖((concreteReturnSeq D G).ops n z).Tc V‖ +
      Real.exp (-(gRate D.Pl / 8) / (concreteReturnSeq D G).ν n) *
        ‖((concreteReturnSeq D G).ops n z).wc V‖ := by
  rw [concreteReturnSeq_ops_eq D G n z h]
  exact (concreteBase _ _ _ _ h).toOps_pairNorm V

/-! ## 9. The affine fields along the sequence (first line of `ret:general-affine-bounds`) -/

/-- The `F_A, E_A, ĥ_A` part of the first line of `ret:general-affine-bounds` (source 5009-5016)
for `concreteReturnSeq`, with `M(A) = affM ν_n χ_f (ιA)` (4955-4962), from the leaves of
`ReturnInst/AffineFields.lean`, the generic envelope at each level (`henv`, source 5089-5091), the
asymptotics `ν_n, ε_n ≤ 1`, `μ_n(z) ∈ K ⋐ (0, 1/4)` for large `n` (5945-5950), and the near layer
(`NearAt`, eventually). -/
theorem concreteReturnSeq_fieldNorms_le (D : SeqData)
    (G : ∀ n, AffSp D.K.as →L[ℝ] GrdG (cOf (retNu D.Pl D.σ₀ n)))
    (lh : HhatCoefLinear D.K.as D.K.χf) (lF : FACoefLinear D.K.as D.K.χf)
    (lE : EACoefLinear D.K.as D.K.χf) (bh : HhatCoefBound D.K.as D.K.χf)
    (bF : FACoefBound D.K.as D.K.χf) (bE : EACoefBound D.K.as D.K.χf) (hγ : 0 ≤ gRate D.Pl)
    {Kset : Set ℝ} (hK : IsCompact Kset) (hK' : Kset ⊆ Ioo 0 (1 / 4))
    (henv : ∀ n, ∃ Cenv : ℝ, ∀ A : AffSp D.K.as,
      affM (retNu D.Pl D.σ₀ n) D.K.χf (affIota D.K.as A) ≤ Cenv * ‖A‖)
    (hasym : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n ≤ 1 ∧ retEps D.Pl D.σ₀ n ≤ 1 ∧
      ∀ z ∈ Icc (-1 : ℝ) 1, D.mu n z ∈ Kset)
    (hnear : ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      NearAt D.Pl D.K (D.level n) (D.mu n z)) :
    ∃ (C : ℝ) (k : ℕ) (N : ℕ), ∀ n ≥ N, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∀ A : (concreteReturnSeq D G).Aff n,
        ‖((concreteReturnSeq D G).ops n z).FA A‖ + ‖((concreteReturnSeq D G).ops n z).EA A‖ +
            ‖((concreteReturnSeq D G).ops n z).hA A‖ ≤
          C * ((concreteReturnSeq D G).ν n)⁻¹ ^ k *
            affM ((concreteReturnSeq D G).ν n) D.K.χf (affIota D.K.as A) := by
  obtain ⟨C, k, hC⟩ := affineFieldNorms_le bh bF bE hK hK'
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hasym.and hnear)
  refine ⟨C, k, N, fun n hn z hz A => ?_⟩
  obtain ⟨⟨hν1, hε1, hμK⟩, hnr⟩ := hN n hn
  obtain ⟨Cenv, hCenv⟩ := henv n
  have hd : AffineFieldData D.K.as (retNu D.Pl D.σ₀ n) (D.mu n z) (retEps D.Pl D.σ₀ n)
      (gRate D.Pl) D.K.χf (affIota D.K.as) :=
    affineFieldData_of (affIota_mem D.K.as) (retNu_pos D.Pl D.σ₀ n) hν1
      (retEps_pos D.coeff_ne n) hε1 hγ hK hK' (hμK z hz) Cenv hCenv lh lF lE bh bF bE
  rw [concreteReturnSeq_ops_eq D G n z (hnr z hz)]
  obtain ⟨e1, e2, e3⟩ := affineOps_eq (Pl := D.Pl) (K := D.K) (L := D.level n) hd
  show ‖FAOp D.K (D.level n) (D.mu n z) A‖ + ‖EAOp D.K (D.level n) (D.mu n z) A‖ +
      ‖hAOp D.Pl D.K (D.level n) A‖ ≤ _
  rw [e1, e2, e3]
  exact hC (retNu D.Pl D.σ₀ n) (D.mu n z) (retEps D.Pl D.σ₀ n) (gRate D.Pl) (retNu_pos _ _ _)
    hν1 (retEps_pos D.coeff_ne n) hε1 hγ (hμK z hz) (affIota D.K.as) (affIota_mem D.K.as) hd A

/-! ## 10. The remainder `𝔯_A` along the sequence (second line of `ret:general-affine-bounds`) -/

/-- Body forces are determined by their phase pairings: if the lifts `𝒩_v f`, `𝒩_v g` have the
same pairing with every phase test, then `f = g` in `SrcG c` (the distributional identity of
`ret:physical-affine` "against all tests determines `𝔯_A`", `Concrete/PhysLayer.lean` pin (d);
source 5001-5008, 2683). -/
def SrcPairingNondeg : Prop :=
  ∀ (c ε : ℝ), 0 < c → 0 < ε → ∀ f g : SrcG c,
    (∀ Φ : ℝ × Space → CVec3, IsPhaseTest (2 * ε * c) Φ →
      pairF (2 * ε * c) Φ (velPhys ε⁻¹ c (f : Chart → Merid)) =
        pairF (2 * ε * c) Φ (velPhys ε⁻¹ c (g : Chart → Merid))) → f = g

/-- The `𝔯_A` pin determines `𝔯_A`. -/
theorem isRAOp_unique (hN : SrcPairingNondeg) {c mZ ρb γ ν : ℝ} {Aff : Type}
    [NormedAddCommGroup Aff] [NormedSpace ℝ Aff] {M : VelG c γ ν →L[ℝ] StrG c mZ ρb γ ν}
    {hA : Aff →L[ℝ] VelG c γ ν} {FA EA r r' : Aff →L[ℝ] SrcG c} {ι : Aff →ₗ[ℝ] (ℝ → Mat3)}
    {χf : ℝ → ℝ} {ε μ : ℝ} (hc : 0 < c) (hε : 0 < ε) (h : IsRAOp M hA FA EA r ι χf ε μ)
    (h' : IsRAOp M hA FA EA r' ι χf ε μ) : r = r' := by
  ext1 A
  have key : FA A + EA A + r A = FA A + EA A + r' A := by
    refine hN c ε hc hε _ _ fun Φ hΦ => ?_
    have e := (h A Φ hΦ).symm.trans (h' A Φ hΦ)
    exact sub_left_injective e
  exact add_left_cancel key

/-- `δ_base = P_ν e^{C_Σ/ν - b_Σc²}` (source 4371, 5018-5020: the train-to-Gaussian and
cross-center envelope on `0 ≤ s ≤ 1.1/ν`; the factor `P_ν` is absorbed in the `P_ν` of the
bound), `c = ν⁻²`. -/
def deltaBase (Csig bsig ν : ℝ) : ℝ := Real.exp (Csig / ν - bsig * cOf ν ^ 2)

/-- `d` bounds `δ_U = ‖U - U_raw‖_{W^{1,∞}}` at level `n` (source 5007-5008, 5049-5050):
`|U - U_raw| ≤ d` and `‖∇(U - U_raw)‖ ≤ d` at every phase and point of level `n`.  `δ_U` is a
quantity of one level (`ret:physical-affine` is a statement at one level), so the bound of `𝔯_A`
(`RABoundExists`) is stated for every bound at that level. -/
def SeqData.IsW1InfBoundAt (D : SeqData) (n : ℕ) (d : ℝ) : Prop :=
  ∀ (τ : ℝ) (y : Space),
    ‖(D.level n).U τ y - ((D.level n).params D.Pl).raw τ y‖ ≤ d ∧
      ‖fderiv ℝ (fun y' => (D.level n).U τ y' - ((D.level n).params D.Pl).raw τ y') y‖ ≤ d

/-- `dU` bounds `δ_U = ‖U - U_raw‖_{W^{1,∞}}` at every level (source 5007-5008, 5049-5050):
`|U - U_raw| ≤ dU n` and `‖∇(U - U_raw)‖ ≤ dU n` at every phase and point. -/
def SeqData.IsW1InfBound (D : SeqData) (dU : ℕ → ℝ) : Prop :=
  ∀ (n : ℕ) (τ : ℝ) (y : Space),
    ‖(D.level n).U τ y - ((D.level n).params D.Pl).raw τ y‖ ≤ dU n ∧
      ‖fderiv ℝ (fun y' => (D.level n).U τ y' - ((D.level n).params D.Pl).raw τ y') y‖ ≤ dU n

/-- A bound at every level is a bound at level `n`. -/
theorem SeqData.IsW1InfBound.atLevel {D : SeqData} {dU : ℕ → ℝ} (h : D.IsW1InfBound dU)
    (n : ℕ) : D.IsW1InfBoundAt n (dU n) :=
  h n

/-- The per-level data of `D` are the source's objects at level `n` (source 2026-2713, 4139-4141):
the level is in the background regime with loss exponent `d_n = -ν_n log ε_n ∈ [d₋, d₊]`
(2031-2037), the exact split holds with the repair bound `ρ_b` and inlet support `S_in`
(2664-2713), `U = V + r_b` with the pressure is an exact profile of period `P = 2εc`
(4139-4141), and the split is the contraction-ball background (`ball`, below).

`ball` (source 2505-2524, 2706-2711): the state `z = (w, A)` of the split is the fixed point of
`short-bg:result`, `‖w‖_{X_p} + R^{8/11}|α| = ‖z‖_Z ≤ 𝒫_νe^{m/ν}ε^{3/11}` (2513-2520), and
`ρ_b = P_νε^{3/11}e^{m₀/ν}` is "a fixed upper bound from the exact-background construction"
(2706-2711), so `‖z‖_Z ≤ ρ_b` (`IsBallSplit`, `ReturnInst/Background/Ball.lean`).  `split`
(`IIb.ExactSplitII`) bounds only `|αᵢ|` and the `11/4 + ∞` energy of `r_b`; `short-bg:strong`
(`IIb.StrongRegularity`, 2525-2562) is stated on the ball, and the symmetry of `U` (2031,
2522-2523, 4144-4145) and the `W^{1,∞}` bound of `U - U_raw` (5007-5008, 5094) come from it
through `ball` (`ReturnInst/Background/Seq.lean`).

Producer: the state of level `n` is taken from `IIb.BackgroundResult` (2505-2524) with
`m = D.K.m0`, `2m₀ < 3d₋/11` (the contraction condition after decreasing `m`, 2510-2512), and
`C₀ ≥ C`, `k₀ ≥ k` (so `Cν^{-k} ≤ C₀ν^{-k₀}` for `ν ≤ 1`), not from `IIb.ExactSplitExport`, whose
`ExactSplitII` forgets `‖z‖_Z`. -/
structure SeqData.IsActualLevel (D : SeqData) (dm dp : ℝ) (n : ℕ) : Prop where
  regime : UnforcedLeray.Short.IIb.BgRegime ((D.level n).params D.Pl)
    (-(retNu D.Pl D.σ₀ n) * Real.log (retEps D.Pl D.σ₀ n)) dm dp
  split : UnforcedLeray.Short.IIb.ExactSplitII ((D.level n).params D.Pl)
    ((D.level n).ρb D.Pl D.K) (D.Sin n) (D.V n) (D.rb n)
  profile : IsExactProfile (retNu D.Pl D.σ₀ n)
    (2 * retEps D.Pl D.σ₀ n * cOf (retNu D.Pl D.σ₀ n)) (D.level n).U (D.pres n)
  /-- The pressure of level `n` is the global `L²` pressure of the exact background (source
  117-118: "The pressure is the global choice `p = Σ R_iR_k(u_iu_k)`"; 2641-2642:
  "`p_U = Σ_{i,j} R_iR_j(U_iU_j) ∈ C_per L²` recovers the discarded gradient part of the exact
  projected equation"; 4139-4141: "its full pressure `p`"; 5245-5257 uses `ℙ∇p = 0`).  `profile`
  fixes only `∇p`, so `p` is `p_U` up to a function of `τ`: at every phase `p(τ) - c ∈ L²(ℝ³)` for
  some constant `c`.  Also `∇p_U = Σ R_iR_j∇(U_iU_j)` with `∇(U⊗U) ∈ L² ∩ L^∞ ⊂ L^{11/4}`
  (2607-2612: `D^jU ∈ C_per L⁴` for `j ≤ 2`, `𝕋 = U⊗U ∈ C_per H²`; 2525-2530: `U ∈ W^{1,∞}`), and
  the Riesz transforms are bounded on `L^{11/4}`, so `∇p(τ) ∈ L^{11/4}`.  This is
  `ExactPresDecayAt (D.level n)` (`Sub/PartIII-b_C_rep_8_2_pres_3_2_1_org.lean`). -/
  presL2 : ∀ τ : ℝ, (∃ c : ℝ, MemLp (fun y => D.pres n τ y - c) 2 volume) ∧
    MemLp (physGrad (D.pres n τ)) (11 / 4) volume
  ball : IsBallSplit ((D.level n).params D.Pl) ((D.level n).ρb D.Pl D.K) (D.V n) (D.rb n)
  /-- The actual train of level `n` is the BUC solution of the source (261-288, 397): the decaying
  smooth stream-function train, so its stream is jointly smooth for `s > 0`
  (`PartI.trainStreamSmooth`). -/
  buc : UnforcedLeray.Short.PartI.IsBUCTrain (D.train n)

/-- **Lemma `ret:physical-affine` with the second line of `ret:general-affine-bounds`** along the
sequence (source 5001-5016, proof 5022-5079): if the levels are actual for large `n` (window
`[d₋, d₊]`), then for large `n` and `z ∈ [-1, 1]` there is a pinned `𝔯_A` (the exact unprojected
residual, `IsRAOp`) with `R⁻¹‖𝔯_A‖_{Y_2} ≤ P_ν(ε + δ_base + δ_U)M(A)` for every bound `d` of
`δ_U` at level `n` (`IsW1InfBoundAt`), `P_ν = Cν^{-k}`, `δ_base = deltaBase C_Σ b_Σ ν`.  The bound
is per level: the data of `D` at the levels before the actual range are unconstrained, so a bound
of `δ_U` at every level need not exist. -/
def RABoundExists (D : SeqData) (dm dp : ℝ) : Prop :=
  (∀ᶠ n : ℕ in atTop, D.IsActualLevel dm dp n) →
    ∃ (Csig bsig C : ℝ) (k N : ℕ), 0 < bsig ∧ ∀ n ≥ N, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∃ r : AffSp D.K.as →L[ℝ] LSrc (D.level n),
        IsRAOp (multOp D.Pl D.K (D.level n)) (hAOp D.Pl D.K (D.level n))
          (FAOp D.K (D.level n) (D.mu n z)) (EAOp D.K (D.level n) (D.mu n z)) r
          (affIota D.K.as) D.K.χf (retEps D.Pl D.σ₀ n) (D.mu n z) ∧
        ∀ d : ℝ, D.IsW1InfBoundAt n d → ∀ A : AffSp D.K.as,
          ‖r A‖ ≤ C * (retNu D.Pl D.σ₀ n)⁻¹ ^ k *
            (retEps D.Pl D.σ₀ n + deltaBase Csig bsig (retNu D.Pl D.σ₀ n) + d) *
              affM (retNu D.Pl D.σ₀ n) D.K.χf (affIota D.K.as A)

/-- The second line of `ret:general-affine-bounds` for `concreteReturnSeq` (source 5014-5016),
from `RABoundExists`, the uniqueness of the pinned `𝔯_A` and the near layer. -/
theorem concreteReturnSeq_rA_le (D : SeqData)
    (G : ∀ n, AffSp D.K.as →L[ℝ] GrdG (cOf (retNu D.Pl D.σ₀ n))) {dm dp : ℝ}
    (hN : SrcPairingNondeg) (hex : RABoundExists D dm dp)
    (hact : ∀ᶠ n : ℕ in atTop, D.IsActualLevel dm dp n)
    (hnear : ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      NearAt D.Pl D.K (D.level n) (D.mu n z)) :
    ∃ (Csig bsig C : ℝ) (k N : ℕ), 0 < bsig ∧ ∀ dU : ℕ → ℝ, D.IsW1InfBound dU →
      ∀ n ≥ N, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ A : (concreteReturnSeq D G).Aff n,
        ‖((concreteReturnSeq D G).ops n z).rA A‖ ≤
          C * ((concreteReturnSeq D G).ν n)⁻¹ ^ k *
            (retEps D.Pl D.σ₀ n + deltaBase Csig bsig ((concreteReturnSeq D G).ν n) + dU n) *
              affM ((concreteReturnSeq D G).ν n) D.K.χf (affIota D.K.as A) := by
  obtain ⟨Csig, bsig, C, k, N₁, hb, hr⟩ := hex hact
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 hnear
  refine ⟨Csig, bsig, C, k, max N₁ N₂, hb, fun dU hdU n hn z hz A => ?_⟩
  obtain ⟨r, hpin, hbd⟩ := hr n (le_trans (le_max_left _ _) hn) z hz
  have hnr := hN₂ n (le_trans (le_max_right _ _) hn) z hz
  rw [concreteReturnSeq_ops_eq D G n z hnr]
  have hre : rAOp D.Pl D.K (D.level n) (D.mu n z) = r :=
    isRAOp_unique hN (cOf_pos (retNu_pos _ _ _)) (retEps_pos D.coeff_ne n)
      (rAOp_spec ⟨r, hpin⟩) hpin
  show ‖rAOp D.Pl D.K (D.level n) (D.mu n z) A‖ ≤ _
  rw [hre]
  exact hbd (dU n) (hdU.atLevel n) A

/-! ## 11. The pinned gradient `A ↦ ∇ĥ_A` along the sequence (source 4990-4999, 5008-5013)

`Concrete/AffineGradPin.lean` is imported here since the duplicate `Concrete.affTerm_nonneg` of
`SourceL.lean` was renamed `affTerm_six_nonneg` (`ORG:return-concrete/instance-3/clash`).  The
pinned sequence is `concreteReturnSeq D (concreteGrad D)`, whose `gradhA n z` is
`concreteGrad D n` by definition. -/

/-- **The gradient `A ↦ ∇ĥ_A` at level `n`** (source 4990-4992: the lift `ĥ_A`; 4999: linear in
`A`; 5011-5013: the term `R⁻¹‖∇ĥ_A‖_{Y_2}` of `ret:general-affine-bounds`): the continuous linear
map `𝒜 → GrdG c_n` with the pin `IsAffineGradPinned` (`Concrete/AffineGradPin.lean`: `G A` is the
tensor coefficient `s⁻¹∇ĥ_{ιA}` a.e., `ι = affIota a_s`) at `ν = ν_n`, `ε = ε_n`, as the
`Classical.epsilon` of the pin.  The pin determines the map (an `L²` class is determined by an
a.e. representative), and a pinned map exists in the regime of `concreteGrad_spec`. -/
def concreteGrad (D : SeqData) (n : ℕ) : AffSp D.K.as →L[ℝ] GrdG (cOf (retNu D.Pl D.σ₀ n)) :=
  Classical.epsilon fun G : AffSp D.K.as →L[ℝ] GrdG (cOf (retNu D.Pl D.σ₀ n)) =>
    IsAffineGradPinned G (affIota D.K.as) D.K.χf (retNu D.Pl D.σ₀ n) (retEps D.Pl D.σ₀ n)

/-- `concreteGrad D n` is pinned at every level with `ν_n, ε_n ≤ 1` (the regime `0 < ε, ν ≤ 1` of
source 5008; `ν_n, ε_n > 0` always), from the gradient leaves `GradCoefLinear` (`A ↦ s⁻¹∇ĥ_A` is
linear, source 4999) and `GradCoefBound` (the `∇ĥ_A` part of source 5011-5013) and the generic
envelope at the level, `M(ιA) ≤ C_env‖A‖` (source 5089-5091; `affM_le_norm_of`,
`Concrete/AffineEnvelope.lean`), through `affineGradData_of`. -/
theorem concreteGrad_spec (D : SeqData) (lg : GradCoefLinear D.K.as D.K.χf)
    (bg : GradCoefBound D.K.as D.K.χf) {n : ℕ} (hν1 : retNu D.Pl D.σ₀ n ≤ 1)
    (hε1 : retEps D.Pl D.σ₀ n ≤ 1)
    (henv : ∃ Cenv : ℝ, ∀ A : AffSp D.K.as,
      affM (retNu D.Pl D.σ₀ n) D.K.χf (affIota D.K.as A) ≤ Cenv * ‖A‖) :
    IsAffineGradPinned (concreteGrad D n) (affIota D.K.as) D.K.χf (retNu D.Pl D.σ₀ n)
      (retEps D.Pl D.σ₀ n) := by
  obtain ⟨Cenv, hCenv⟩ := henv
  have hex : ∃ G : AffSp D.K.as →L[ℝ] GrdG (cOf (retNu D.Pl D.σ₀ n)),
      IsAffineGradPinned G (affIota D.K.as) D.K.χf (retNu D.Pl D.σ₀ n) (retEps D.Pl D.σ₀ n) :=
    ⟨_, (affineGradData_of (affIota_mem D.K.as) (retNu_pos D.Pl D.σ₀ n) hν1
      (retEps_pos D.coeff_ne n) hε1 Cenv hCenv lg bg).isAffineGradPinned_of⟩
  exact Classical.epsilon_spec hex

end UnforcedLeray.Short.PartIIIb.Concrete
