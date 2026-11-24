import UnforcedLeray.Short.Spine.PartIII
import UnforcedLeray.Short.Spine.PartII
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair
import UnforcedLeray.Short.PartIIIb.Concrete.Standing.Choices
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.FlatPin
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Leaves
import UnforcedLeray.Short.PartIIIa.FlatCausal
import UnforcedLeray.Short.PartI.Sub.T01
import UnforcedLeray.Short.PartI.StatementsTrain

/-!
# The wiring of Part III-b into `Spine.PartIIIOutput`: the inputs (task `PartIII-b:IIIb-D5`)

Source of record: `the November 2 reference manuscript` (73 pages): the exact
return 5777-5833, the parameter budget and its order of choice 5835-5920, the phase selection and
the energy mode 5922-5985, the split `U = V + r_b` and `ρ_b` 2664-2713, the fixed inlet cutoff
2316-2318, the contraction-ball background 2505-2524, one background per level held while `σ`
varies 5951-5954.

`Proofs/Wiring/Skeleton.lean` proves `partIIIOutput_of_inputs : <inputs> → Spine.PartIIIOutput`.
This file states the inputs.

* **Objects.** `Spine.ShortBackground` (`Short/Spine/Background.lean`) is the background data of
  a level quantified in `Spine.PartIIIOutput` (`Short/Spine/PartIII.lean`); `Wiring.seqOf`
  (INSTANCE, step 2) is the concrete sequence datum `SeqData` of a family of such backgrounds:
  train, split `V = U_raw + E_εα`, `r_b = w` (`U = V + r_b`), pressure, inlet support
  `S_in = Σ/(2ν_n)` of level `n` from the background of level `n`, the flat setting
  `levelFlat … FI_n` of the level's train (`AffineSource/FlatPin.lean`), the fixed constants `K`
  and the slow age `Σ`.
* **BRIDGE** (step 3): `Wiring.BackgroundBridge`, the per-level background facts
  `SeqData.StandingBridge` (`SeqData.IsActualLevel`, the inlet bound `S_in ≤ ε_n^{-b}` and
  `RepairDerivBound`) of `seqOf` from `Spine.IsShortBackground`.
* **STANDING** (step 4): `Wiring.StandingInput`, the instantiated producer of
  `SeqData.RepairStanding` (`repairStanding_of_inputs`, `Concrete/Standing/Producer.lean`, task
  `PartIII-b:C/standing`).
* **MODE** (step 5): `Wiring.ModeOfReturn`, from the exact-return solution to
  `Interface.IsEnergyMode` (5969-5985).
* the module inputs of `concrete_energyModes`, each the statement of its supplier task:
  `ErrorFamilyInput` (IIIb-D4), `FlatLimitInput` (IIIb-D3), `PLBoundInput` (C/rep/15),
  `ContinuityInput` (C/cont/main), `NearBodyInput` (C/rep/11), `FlatColumnInput` (C/flatset/col),
  `WardAffineSeq` (C/rinst/5 along the sequence), and the order of choice `ConstantsExist`
  (5835-5859).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Blueprint.Planar
open UnforcedLeray.Cons.Data

namespace Wiring

/-! ## 1. The background of one level and the sequence datum of a family of backgrounds -/

/-- `𝒯 = 2εc` with `c = ν⁻²`: the Spine's `Train.per ν = ν⁻¹²` is `cOf ν = (ν²)⁻¹`. -/
theorem per_eq (ν : ℝ) : Train.per ν = cOf ν := by
  simp [Train.per, cOf, inv_pow]

/-- Transport of a train along an equality of cell sizes. -/
def castTrain {ν c c' : ℝ} (h : c = c') (T : UnforcedLeray.B0140.TrainSol ν c) :
    UnforcedLeray.B0140.TrainSol ν c' :=
  h ▸ T

theorem castTrain_buc {ν c c' : ℝ} (h : c = c') {T : UnforcedLeray.B0140.TrainSol ν c}
    (hT : PartI.IsBUCTrain T) : PartI.IsBUCTrain (castTrain h T) := by
  subst h
  exact hT

/-- The phase-locked viscosities are at most one (`lockedRecip ≥ threshold ≥ 1`). -/
theorem retNu_le_one (Pl : PlanarData) (σ₀ : ℝ) (n : ℕ) : retNu Pl σ₀ n ≤ 1 :=
  inv_le_one_of_one_le₀ (le_trans (UnforcedLeray.Blueprint.PhaseLock.one_le_threshold _ _)
    (UnforcedLeray.Blueprint.PhaseLock.threshold_le_lockedRecip _ _ _ n))

theorem one_le_cOf_retNu (Pl : PlanarData) (σ₀ : ℝ) (n : ℕ) : 1 ≤ cOf (retNu Pl σ₀ n) := by
  have h0 := retNu_pos Pl σ₀ n
  have h1 := retNu_le_one Pl σ₀ n
  unfold cOf
  exact one_le_inv₀ (pow_pos h0 2) |>.2 (pow_le_one₀ h0.le h1)

open scoped Classical in
/-- **The train of level `n`**: the background's train (at `c = ν_n^{-2}`) when its parameters are
those of level `n` and it is in the BUC class (always so at the levels where the background is
given, `Spine.IsShortBackground`), otherwise a BUC train of `TrainGlobalExistence` (source 270-288;
`ν_n ≤ 1`, so `c_n ≥ 1`). -/
def levelTrain (htr : PartI.TrainGlobalExistence) (R : Reference) (n : ℕ)
    (B : Spine.ShortBackground) :
    UnforcedLeray.B0140.TrainSol (retNu R.planar R.σ₀ n) (cOf (retNu R.planar R.σ₀ n)) :=
  if h : B.par.ν = retNu R.planar R.σ₀ n ∧ B.par.c = cOf (retNu R.planar R.σ₀ n) ∧
      PartI.IsBUCTrain B.par.trainData then
    cast (by rw [h.1, h.2.1]) B.par.trainData
  else Classical.choose (htr _ _ (retNu_pos _ _ n) (one_le_cOf_retNu _ _ n))

theorem castTrain2_buc {ν ν' c c' : ℝ} (hν : ν = ν') (hc : c = c')
    {T : UnforcedLeray.B0140.TrainSol ν c} (hT : PartI.IsBUCTrain T) :
    PartI.IsBUCTrain (cast (by rw [hν, hc]) T : UnforcedLeray.B0140.TrainSol ν' c') := by
  subst hν hc
  exact hT

theorem levelTrain_buc (htr : PartI.TrainGlobalExistence) (R : Reference) (n : ℕ)
    (B : Spine.ShortBackground) : PartI.IsBUCTrain (levelTrain htr R n B) := by
  unfold levelTrain
  split_ifs with h
  · exact castTrain2_buc h.1 h.2.1 h.2.2
  · exact Classical.choose_spec (htr _ _ (retNu_pos _ _ n) (one_le_cOf_retNu _ _ n))

open scoped Classical in
/-- **The global pressure of level `n`** (source 117-118, 2641-2642, 4139-4141): a smooth
periodic global `L²` pressure `p` of `B.U` with `∇p(τ) ∈ L^{11/4}` solving the pointwise profile
equation `D₀U + U·∇U + ∇p = 0` (`IsExactProfile` and `presL2`) when one exists (all large levels,
from the contraction-ball background construction of `short-bg:result` and
`p_U = Σ R_iR_j(U_iU_j)`, 2505-2642), otherwise `B.pres`. -/
def levelPres (R : Reference) (n : ℕ) (B : Spine.ShortBackground) : ℝ → Space → ℝ :=
  if h : ∃ pr : ℝ → Space → ℝ,
      IsExactProfile (retNu R.planar R.σ₀ n)
        (2 * retEps R.planar R.σ₀ n * cOf (retNu R.planar R.σ₀ n)) B.U pr ∧
      ∀ τ : ℝ, (∃ c : ℝ, MemLp (fun y => pr τ y - c) 2 volume) ∧
        MemLp (physGrad (pr τ)) (11 / 4) volume then
    Classical.choose h
  else B.pres

/-- A flat setting used only at the levels where no flat data exists (no statement concerns it). -/
def flat0 : ConcreteYF.FlatSetting where
  pk := { X := ℂ, Uev := fun _ _ => 0, q := fun _ _ => 0, ell := fun _ _ => 0 }
  conjX := id
  Hper := fun _ => 0
  Rper := fun _ => 0
  Mcell := fun _ _ _ => 0
  chiO := fun _ => 0
  c := 0
  eps3 := 0

/-- The weight `m = 9 > 8` of `X_{m,c}` used for the flat data (source 4349-4350; `m > 8` in
`TrainEvolutionExists`, `FrozenPairExists`). -/
instance instFactOneLtNine : Fact (1 < (9 : ℝ)) := ⟨by norm_num⟩

open scoped Classical in
/-- **The flat setting of a level** (source 4557-4612): `levelFlat … FI χ̂_o ε` for pinned flat
data `FI` of the level's train at `m = 9` when such data exists (all large levels, from
`TrainEvolutionExists`, `FrozenPairExists`, `GaussSourcesExist`). -/
def levelFlatOf (κ : IIIa.PlanarFrameKernels) (χo : ℝ → ℝ) {ν : ℝ} (hν : 0 < ν) (ε : ℝ)
    (tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)) : ConcreteYF.FlatSetting :=
  if h : Nonempty (FlatSettingInst.FlatInstData κ ν (cOf ν) 9 tr) then
    levelFlat hν (Classical.choice h) χo ε
  else flat0

/-- **INSTANCE: the concrete sequence datum of a family of backgrounds** (source 5926-5954): the
reference `R` (`ν_n = retNu`, `ε_n = retEps`, the Spine's `nuSeq`, `epsSeq`), the fixed constants
`K` (5835-5859), the slow age `Σ` of the inlet (2316-2318), and at level `n` the background `B n`
(one background per level, held while `σ` varies, 5951-5954): its train, `V = U_raw + E_εα`,
`r_b = w` (`U = V + r_b`, 2664-2672), its global pressure, the inlet support `S_in = Σ/(2ν_n)` of
its fixed inlet cutoff (`H/2`, `H = Σ/ν_n`, 2316-2318), and the actual flat setting of its train. -/
def seqOf (R : Reference) (hc : R.planar.signedCoeff R.σ₀ ≠ 0) (K : ReturnConsts) (Sig : ℝ)
    (hSig : 0 < Sig) (htr : PartI.TrainGlobalExistence) (hsm : PartI.TrainStreamSmooth)
    (κ : IIIa.PlanarFrameKernels) (B : ℕ → Spine.ShortBackground) : SeqData where
  Pl := R.planar
  σ₀ := R.σ₀
  coeff_ne := hc
  K := K
  Sig := Sig
  Sig_pos := hSig
  train n := levelTrain htr R n (B n)
  train_buc n := levelTrain_buc htr R n (B n)
  train_stream_smooth n := hsm _ _ (retNu_pos _ _ n) (cOf_pos (retNu_pos _ _ n)) _
    (levelTrain_buc htr R n (B n))
  Sin n := Sig / (2 * retNu R.planar R.σ₀ n)
  V n := (B n).V
  rb n := (B n).rb
  pres n := levelPres R n (B n)
  flat n := levelFlatOf κ K.χo (retNu_pos R.planar R.σ₀ n) (retEps R.planar R.σ₀ n)
    (levelTrain htr R n (B n))

/-- The flat pin of the sequence at `m = 9` (source 4557-4612): for large `n` the flat setting is
the actual one of the level's train (`SeqData.IsActualFlat`). -/
def FlatPin (D : SeqData) : Prop :=
  ∃ κ : IIIa.PlanarFrameKernels, ∀ᶠ n : ℕ in atTop, D.IsActualFlat κ 9 n

/-! ## 2. Sequence form of `PartIIIOutput` -/

/-- **`PartIIIOutput` in sequence form** (source 5951-5954, 5975-5985): since
`ORG:Spine/background-for-PartIII`, `Spine.PartIIIOutput` (`Short/Spine/PartIII.lean`) is
itself the sequence form over `Spine.ShortBackground`. -/
abbrev PartIIIOutputSeq : Prop := Spine.PartIIIOutput

/-- **QSWAP** (unused since `Spine.PartIIIOutput` is in sequence form; kept so
`Proofs/Wiring/QSwap.lean` compiles). -/
def QSwap : Prop :=
  Spine.PartIIOutput → PartIIIOutputSeq → Spine.PartIIIOutput

/-! ## 3. BRIDGE (step 3), STANDING (step 4), MODE (step 5) -/

/-- **BRIDGE: the per-level background facts from the Spine's backgrounds** (source 2026-2037,
2316-2318, 2505-2524, 2664-2713, 4139-4141, 5134-5139): for every slow age `Σ > 0` of the fixed
inlet and every family of backgrounds `B : ℕ → Spine.ShortBackground` satisfying
`Spine.IsShortBackground` at `(m, C, N, Σ)` for large `n`, with `m ≤ m₀`, `2m₀ < 3d₋/11`,
`2C ≤ C₀`, `N ≤ k₀`, the sequence datum `seqOf` with `ρ_b = C₀ν^{-k₀}e^{m₀/ν}ε^{3/11}` has actual
levels (`SeqData.IsActualLevel`: regime, `ExactSplitII`, `IsExactProfile`, `presL2`,
`IsBallSplit`, BUC train), inlet support `S_in = Σ/(2ν_n)` below the output cut `ε_n^{-b}` and the
repair derivative bounds `RepairDerivBound` (`SeqData.StandingBridge`). -/
def BackgroundBridge : Prop :=
  ∀ R : Reference, R.IsReferenceChoice →
    ∀ (b m0 C0 : ℝ) (k0 : ℕ) (m C : ℝ) (N : ℕ) (dm dp Sig : ℝ) (hSig : 0 < Sig),
      0 < b → 0 < m → m ≤ m0 → 2 * m0 < 3 * dm / 11 → 0 < C0 → 2 * C ≤ C0 → N ≤ k0 →
      0 < dm → dm < gRate R.planar / 3 → gRate R.planar / 3 < dp →
      ∀ K : ReturnConsts, K.b = b → K.m0 = m0 → K.C0 = C0 → K.k0 = k0 →
        ∀ (hc : R.planar.signedCoeff R.σ₀ ≠ 0)
          (htr : PartI.TrainGlobalExistence) (hsm : PartI.TrainStreamSmooth)
          (κ : IIIa.PlanarFrameKernels) (B : ℕ → Spine.ShortBackground),
          (∀ᶠ n : ℕ in atTop,
            Spine.IsShortBackground R.planar (Spine.nuSeq R n) (Spine.epsSeq R n) m C N Sig
              (B n)) →
            (seqOf R hc K Sig hSig htr hsm κ B).StandingBridge dm dp

/-- **STANDING: the producer of the standing hypotheses** (source 5115-5146, 5150-5160, 5303-5306,
5777-5833, 5835-5859, 5926-5950), in the form of `repairStanding_of_inputs`
(`Concrete/Standing/Producer.lean`) with its family inputs discharged (task
`PartIII-b:C/standing`): an integer `Kint` chosen after the reference, `σ₀`, `m_Z`, `[d₋, d₊]`
such that the choices after `Kint` and the per-level background facts give
`SeqData.RepairStanding`. -/
def StandingInput : Prop :=
  ∀ (Pl : PlanarData), IsPlanarReference Pl → Pl.eigenvalue.im ≠ 0 → ∀ σ₀ : ℝ, 0 < σ₀ →
    σ₀ < 1 / 4 → ∀ mZ : ℝ, 3 / 2 < mZ → ∀ dm dp : ℝ, 0 < dm →
      ∃ Kint : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ →
        D.StandingChoices Kint dm → D.StandingBridge dm dp → D.RepairStanding dm dp

/-- **MODE: the energy mode of an exact-return solution** (source 5969-5985): at a level of the
sequence where the standing hypotheses hold (actual level, pinned operators, invertible near
layer) and `σ = μ_n(z) ∈ (0, 1/4)`, a solution `T' ≠ 0`, `DT' = 0` of the exact return with
`b = -S_σT'`, `T' = M_U b`, `b ≠ 0` gives the energy mode: the physical field of `b` (`velPhys`)
is nonzero, real, `𝒫_n`-periodic, solenoidal, axisymmetric without swirl, `b, ∇b ∈ Y₂`, and solves
the mode equation against periodic tests (from the pins `IsWeakStressInverse` of `S_σ` and
`IsSplitMult` of `M_U`: "`b = w + Y + h - h_{LT}`, so the masked terms recombine into the physical
equation with its full pressure", 5982-5984), on the background `U = V + r_b` of the level with
period `𝒫_n = 2ε_nc_n`.  (`IsEnergyMode` does not involve the datum `a` and the remainder `Q`.) -/
def ModeOfReturn : Prop :=
  ∀ (D : SeqData) (dm dp : ℝ), D.RepairStanding dm dp → ∀ n : ℕ, D.IsActualLevel dm dp n →
    2 * (D.level n).ε * cOf (D.level n).ν ≤ 1 →
    ∀ z ∈ Icc (-1 : ℝ) 1, NearAt D.Pl D.K (D.level n) (D.mu n z) →
      RegimePins D.Pl D.K (D.level n) (D.mu n z) → 0 < D.mu n z → D.mu n z < 1 / 4 →
      ∀ (T' : LStr D.Pl D.K (D.level n)) (b : LVel D.Pl (D.level n)), T' ≠ 0 →
        (concreteOps D.Pl D.K (D.level n) (D.mu n z)).D T' = 0 →
        b = -((concreteOps D.Pl D.K (D.level n) (D.mu n z)).S T') →
        T' = (concreteOps D.Pl D.K (D.level n) (D.mu n z)).M b → b ≠ 0 →
        ∀ (a : SpatialField) (Q : ℝ → SobolevGraph.H2), ∃ M : Interface.EnergyModeCore,
          M.σ = D.mu n z ∧ Interface.IsEnergyMode
            ⟨retNu D.Pl D.σ₀ n, 2 * retEps D.Pl D.σ₀ n * cOf (retNu D.Pl D.σ₀ n), a,
              (D.level n).U, Q⟩ M

/-! ## 4. The module inputs of `concrete_energyModes` (statements of the supplier tasks) -/

/-- **The order of choice of the constants** (source 5835-5859): for `γ > 0`, `d₋ > 0` and the
integers `Kint` (near layer, 3927-3946) and `k₀` (error families, 5607-5627) there are `b_win`,
`δ`, `m₀` with the near parameter choice for every `C₀ > 0` (`K₀(a + b_win) < 1/100`,
`η_δ, m₀ < ϑd₀/8`, `d₀ = γ/3`), `δ < log(12/11)`, the contraction condition `2m₀ < 3d₋/11`
(2510-2512), `m₀ < γ/1000`, `k₀b_wind₀ < γ/1000` and `0 ≤ η_δ < γ/1000`. -/
def ConstantsExist : Prop :=
  ∀ (γ dm : ℝ) (Kint k₀ : ℕ), 0 < γ → 0 < dm →
    ∃ b δ m0 : ℝ, (∀ C0 : ℝ, 0 < C0 → NearInst.NearChoice Kint γ dm b δ m0 C0) ∧
      0 < b ∧ b < 1 ∧ 0 < δ ∧ δ < Real.log (12 / 11) ∧ 0 < m0 ∧ 2 * m0 < 3 * dm / 11 ∧
      m0 < γ / 1000 ∧ (k₀ : ℝ) * b * (γ / 3) < γ / 1000 ∧ 0 ≤ NearInst.etaDelta γ δ ∧
      NearInst.etaDelta γ δ < γ / 1000

/-- The statement of `errorFamilyBounds_concrete` (task `PartIII-b:IIIb-D4`, source 5607-5627,
5687-5697). -/
def ErrorFamilyInput : Prop :=
  ∀ (Pl : PlanarData) (σ₀ mZ dm dp : ℝ), ∃ k₀ : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ →
    D.K.mZ = mZ → D.RepairStanding dm dp →
      ∀ G : ∀ n, AffSp D.K.as →L[ℝ] GrdG (cOf (retNu D.Pl D.σ₀ n)),
        ErrorFamilyBounds (concreteReturnSeq D G) (gRate D.Pl)
          ((k₀ : ℝ) * D.K.b * (gRate D.Pl / 3)) D.K.m0

/-- The statement of `flatLimit_concrete` (task `PartIII-b:IIIb-D3`, source 4821-4916). -/
def FlatLimitInput : Prop :=
  ∀ (D : SeqData) {dm dp : ℝ}, D.RepairStanding dm dp →
    (∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      NearInst.Kflat.IsFlatDuhamelColumn (D.flat n) (cOf_pos (retNu_pos D.Pl D.σ₀ n)) (D.train n)
        (D.mu n z) D.K.as D.K.χf) →
    ∀ G : ∀ n, AffSp D.K.as →L[ℝ] GrdG (cOf (retNu D.Pl D.σ₀ n)),
      FlatLimit (concreteReturnSeq D G) D.Pl.eigenvalue D.Pl.kappa D.Pl.strainCoupling
        (planarJ D.Pl) D.σ₀ D.K.as

/-- The statement of `plBound_concrete` (task `PartIII-b:C/rep/15`, source 5883-5891). -/
def PLBoundInput : Prop :=
  NearInst.NearSolverC → NearInst.NearOpsExistC →
    (∀ (as c mZ ρb γ ν ε μ : ℝ) (χo χy : ℝ → ℝ), SourceLInAff as c mZ ρb γ ν ε μ χo χy) →
    (∀ (as : ℝ) (χf : ℝ → ℝ), IsSourceCutoffC χf → FACoefBound as χf) →
    (∀ χ : ℝ → ℝ, IsSourceCutoffC χ → ∃ C : ℝ, 0 ≤ C ∧ ∀ (as ν : ℝ) (A : ℝ → Mat3),
      0 ≤ as → 0 < ν → IsAffElem as A → affM ν χ A ≤ C * Real.exp (1.1 * as / ν) * affNorm as A) →
    ∀ (Pl : PlanarData) (σ₀ mZ dm dp : ℝ), ∃ Kint : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ →
      D.K.mZ = mZ → NearInst.NearChoice Kint (gRate Pl) dm D.K.b D.K.δ D.K.m0 D.K.C0 →
      D.RepairStanding dm dp → D.NearBody →
      ∀ G : ∀ n, AffSp D.K.as →L[ℝ] GrdG (cOf (retNu D.Pl D.σ₀ n)),
        PLBound (concreteReturnSeq D G) D.K.as

/-- The statement of `returnNormContinuity_concrete` (task `PartIII-b:C/cont/main`, source
5684-5685, 5918-5920). -/
def ContinuityInput : Prop :=
  ∀ (D : SeqData) {dm dp : ℝ}, D.RepairStanding dm dp →
    ∀ G : ∀ n, AffSp D.K.as →L[ℝ] GrdG (cOf (retNu D.Pl D.σ₀ n)), ConcreteReturnNormContinuity D G

/-- The statement of `nearBody` (task `PartIII-b:C/rep/11`, source 5536-5547): the near-body
bound `D.NearBody` used by `plBound_concrete`. -/
def NearBodyInput : Prop :=
  ∀ (D : SeqData) {dm dp : ℝ}, D.RepairStanding dm dp → D.NearBody

/-- The statement of `isFlatDuhamelColumn_actual` (task `PartIII-b:C/flatset/col`, source
4084-4086, 4557-4612): the actual flat setting carries the flat Duhamel column. -/
def FlatColumnInput : Prop :=
  IIIa.PolyCausal → ∀ {P : PlanarData}, IsPlanarReference P → ∀ {Kset : Set ℝ}, IsCompact Kset →
    Kset ⊆ Ioo 0 (1 / 4) → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀, ∀ (m : ℝ) [Fact (1 < m)]
      [Fact (0 < cOf ν)] (κ : IIIa.PlanarFrameKernels) (tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)),
      PartI.IsBUCTrain tr → ∀ (FI : FlatSettingInst.FlatInstData κ ν (cOf ν) m tr) (χo : ℝ → ℝ)
        (ε : ℝ) (hc : 0 < cOf ν), ∀ μ ∈ Kset, ∀ (as : ℝ) (χf : ℝ → ℝ),
          NearInst.Kflat.IsFlatDuhamelColumn (FlatSettingInst.actualFlatSetting FI χo ε) hc tr μ
            as χf

/-- **`ret:ward-stress-normal`, `ret:physical-affine` and the nilpotency along the sequence**
(source 4300-4303, 5001-5008, 5796-5814): `concreteOps_wardAffineNilpotent` (task
`PartIII-b:C/rinst/5`) at the levels of a sequence with the standing hypotheses and the flat pin,
for large `n` and `z ∈ [-1, 1]`. -/
def WardAffineSeq : Prop :=
  ∀ (D : SeqData) (dm dp : ℝ), D.RepairStanding dm dp → FlatPin D →
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      (concreteOps D.Pl D.K (D.level n) (D.mu n z)).WardStressNormal ∧
      (concreteOps D.Pl D.K (D.level n) (D.mu n z)).PhysAffineIdentity ∧
      (concreteOps D.Pl D.K (D.level n) (D.mu n z)).HNilpotent

end Wiring

end UnforcedLeray.Short.PartIIIb.Concrete
