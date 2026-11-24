import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Inverses.Leaves
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_B
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Basic
import UnforcedLeray.Short.PartIIb.Bridge.Consequences

/-!
# The free inverses of the concrete return at one level: `S_μ`, `R_μ` and `S_N = S_μ - S_far`
(source 1351-1362, 1556-1583, 1675-1679, 3888-3920, 4139-4146, 5781-5785, 5820)

Source of record: `the November 2 reference manuscript` (73 pages).

`Concrete/ReturnInst.lean` pins the operators of the concrete base by their source properties
(`Classical.epsilon`): `Sop` is *the* weak stress inverse (`IsWeakStressInverse`, source 4145,
1556-1572), `Rop = bodyG R_ε` with `R_ε = bodyReps` the real form of `T_ε = (μ - A_ε)⁻¹P_ε`
(1675-1677), and `SNop = (nearOpsAt …).SNG` the transport of the near inverse `S_N` of the actual
near operators (3911-3920, 5785).  This file proves, at one level, the three pins of the base that
involve them.

## The transported stress inverse

`stressG S γ hν = √π velIso⁻¹ (g⁻¹ S g) strIso : StrG → VelG` carries a chart stress inverse
`S : Z → H` of the near layer to the gain-normed return spaces, acting on the same chart functions
(`coeFn_stressG`, `zsum_zOfStr`); it is `NearOps.SNG` with `S` in the slot `S_N`
(`SNG_eq_stressG`) and is additive in `S` (`stressG_sub`).  At fixed `ν` the gains are bounded
above and below (`e^{-|γ|/ν} ≤ g⁻¹ ≤ e^{|γ|/ν}`), so the transport of a bounded `S` is bounded.

## (a) `S_μ = R_μℙ div` (source 3888-3890, 1556-1572, 4145)

"The finite-curvature free inverse is the conjugate of the Cartesian weak-stress inverse"
(3888-3889): the real form `S_ε` of the stress map of `T_ε` (`IsStressMap`, `IsStressTransport`,
1675-1679) is, lifted, a weak Cartesian stress solution (`StressMapWeakSol`), so
`stressG S_ε` is a weak stress inverse (`isWeakStressInverse_stressG`).  `StressTransportExists`
(the real `S_ε` exists, 1675-1690) is proved from `PartIIa.NearStressMapExists` and the reality of
stress maps (`stressTransportExists_of`, the first half of `Masked.maskedNearExists_of`).  Hence
`S_μ` exists at every level with `ε ≤ 1`, `P = 2εc ≤ 1`, `μ > -1/4`
(`exists_weakStressInverse_level`); this is the hypothesis of `concreteBase_isStressInverse`.

## (c) `S_N = S_μ - S_far` (source 3902-3920, 5785)

For the actual near operators `o = nearOpsAt …` the pin `IsMaskedNear` gives
`o.SN = S_ε - S_far'` in real form.  Transported: `SNop = stressG S_ε - stressG S_far'`; the first
term is a weak stress inverse, hence equal to `Sop` by free weak uniqueness
(`eq_of_isWeakStressInverse`, `FreeWeakUniqueness`, source 1571, 1580-1583); the second satisfies
the gain-normed far pin (`isFarMaskG_stressG`, the same kernel formula on the same functions).  So
`IsNearSplit` holds (`isNearSplit_of_masked`, `concreteBase_isNearSplit`).

## (b) `R_μ = D_μ⁻¹ℙ` (source 1351-1362, 1675-1677, 4139-4146, 5781, 5820)

`bodyG R_ε f` lifted is a weak free solution of `D_μ w = ℙ𝒩_v f` (`TepsWeakSol`,
`bodyG_isWeakDmu`).  The weak-to-graph upgrade `WeakToFreeResponse` (proved here from
`bg:common-body-graph`: the graph solution exists, `IIb.field_response_exists`, and the difference
of two `Y_2` weak solutions vanishes, `FWUHomog`; with the leaves `YrSub`, `WeakDmuSubY`,
`FreeResponseAECongr`) and `Y_2`-membership of the lifts (`fwuLiftYr`, `SrcLiftYr`) give the free
response `IIb.IsFreeResponse` (`isBodyInverse_of_bodyG`, `concreteBase_isBodyInverse`).

## Hypotheses (source facts, each a queued or accepted task)

`NearInst.StressMapWeakSol` (`PartIII-b:C/near/pins/5`), `NearInst.StressPairAE`
(`C/near/pins/1`, accepted), `PartIIa.NearStressMapExists` (`PartII-a:N01`),
`Masked.StressMapReal` (`C/near/masked/8`, accepted), `Masked.CellPtHT`, `CellPtInvH`, `CellPtH`
(`C/near/masked/1`, `/3`, `/2`, accepted), `FreeWeakUniqueness` (`PartIII-b:IIIb-D2/1`),
`NearInst.TepsWeakSol` (`C/near/pins/3`), `IIb.LerayPairSol` (`PartII-b:T10/org/1`, accepted),
`FWUHomog` (`PartIII-b:IIIb-D2/1/3`), and the leaves of `Inverses/Leaves.lean`
(`PartIII-b:C/inv/1`-`4`).  `fwuLiftYr` (`IIIb-D2/1/2`, accepted) is used directly.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest Params)
open UnforcedLeray.Blueprint.Planar (PlanarData)
open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)

/-! ## 1. The transported stress inverse -/

section Transport

variable {c mZ ρb : ℝ}

/-- **A chart stress inverse on the return spaces** (source 3875-3880, 5116-5143, 5609): for
`S : Z → H` of the near layer, `√π velIso⁻¹ (g⁻¹ S g) strIso : StrG → VelG`, the operator `S`
acting on the same chart functions (`NearInst.NearOps.SNG` with `S` in the slot `S_N`). -/
def stressG (S : Zsp c mZ ρb →L[ℝ] Hsp c) (γ : ℝ) {ν : ℝ} (hν : 0 < ν) :
    StrG c mZ ρb γ ν →L[ℝ] VelG c γ ν :=
  NearInst.NearOps.SNG (⟨0, S, 0, 0⟩ : NearInst.NearOps c mZ ρb) γ hν

theorem SNG_eq_stressG (o : NearInst.NearOps c mZ ρb) (γ : ℝ) {ν : ℝ} (hν : 0 < ν) :
    o.SNG γ hν = stressG o.SN γ hν := rfl

theorem stressG_apply (S : Zsp c mZ ρb →L[ℝ] Hsp c) (γ : ℝ) {ν : ℝ} (hν : 0 < ν)
    (T : StrG c mZ ρb γ ν) :
    stressG S γ hν T = Real.sqrt Real.pi • (NearInst.velIso c γ ν).symm
      ((NearInst.gainH c γ hν).symm
        (S (NearInst.gainEquiv c mZ ρb γ hν (NearInst.strIso c mZ ρb γ ν T)))) := rfl

theorem stressG_sub (S S' : Zsp c mZ ρb →L[ℝ] Hsp c) (γ : ℝ) {ν : ℝ} (hν : 0 < ν) :
    stressG (S - S') γ hν = stressG S γ hν - stressG S' γ hν := by
  ext1 T
  rw [ContinuousLinearMap.sub_apply, stressG_apply, stressG_apply, stressG_apply,
    ContinuousLinearMap.sub_apply, map_sub, map_sub, smul_sub]

/-- `stressG S T` is the chart function `S F`, `F = gainEquiv (strIso T)` the same stress in `Z`. -/
theorem coeFn_stressG (S : Zsp c mZ ρb →L[ℝ] Hsp c) (γ : ℝ) {ν : ℝ} (hν : 0 < ν)
    (T : StrG c mZ ρb γ ν) :
    (stressG S γ hν T : Chart → Merid) =ᵐ[ageμ c (-3 / 2)]
      (S (NearInst.gainEquiv c mZ ρb γ hν (NearInst.strIso c mZ ρb γ ν T)) : Chart → Merid) :=
  NearInst.coeFn_SNG (⟨0, S, 0, 0⟩ : NearInst.NearOps c mZ ρb) γ hν T

/-- The stress `gainEquiv (strIso T) ∈ Z` has the component sum `T₁ + T₂` of `T` (source 2700:
the stress inverse acts on the sum of the components). -/
theorem zsum_zOfStr (γ : ℝ) {ν : ℝ} (hν : 0 < ν) (hρ : 0 < ρb) (T : StrG c mZ ρb γ ν) :
    NearInst.zsum (NearInst.gainEquiv c mZ ρb γ hν (NearInst.strIso c mZ ρb γ ν T))
      =ᵐ[ageμ c (-1 / 2)] strSum T := by
  have h1 := NearInst.coeFn_zOfStr_fst γ hν T
  have h2 := NearInst.coeFn_zOfStr_snd γ hν T
  rw [NearInst.ae_z1Measure] at h1
  rw [NearInst.ae_htRhoMeasure hρ] at h2
  filter_upwards [h1, h2] with p a1 a2
  simp only [NearInst.zsum, strSum]
  rw [a1, a2]

end Transport

/-! ## 2. (a) The weak stress inverse `S_μ = R_μℙ div` -/

/-- **(a) The transported curved stress inverse is a weak stress inverse** (source 3888-3890:
"the finite-curvature free inverse is the conjugate of the Cartesian weak-stress inverse";
1556-1572, 1675-1679, 4145): if `S_ε : Z → H` is the real form of a stress map of `T_ε`, then
`stressG S_ε` satisfies `IsWeakStressInverse` at `(ε, μ)`, `P = 2εc ≤ 1`, `μ > -1/4`. -/
theorem isWeakStressInverse_stressG (hW : NearInst.StressMapWeakSol)
    (hPA : NearInst.StressPairAE) {p : Params} {μ : ℝ} (hP : p.period ≤ 1) (hμ : -(1 / 4) < μ)
    {mZ ρb : ℝ} (γ : ℝ) (hmZ : 0 ≤ mZ) (hρ : 0 < ρb) {Seps : Zsp p.c mZ ρb →L[ℝ] Hsp p.c}
    {Seps' : UnforcedLeray.Short.PartIIa.HTSpace p.c →L[ℂ] HSpace p.c MeridC}
    (hmap : UnforcedLeray.Short.PartIIa.IsStressMap p.c p.ε
      (UnforcedLeray.Short.PartIIa.Teps (P := p.period) p.ν_pos p.ε_pos p.c_pos rfl (μ : ℂ)) Seps')
    (htr : NearInst.IsStressTransport Seps Seps') :
    IsWeakStressInverse (stressG Seps γ p.ν_pos) p.ε μ := by
  intro T
  have hsol := hW p μ hP hμ mZ ρb γ hmZ hρ Seps Seps' hmap htr _ (stressG Seps γ p.ν_pos T)
    (coeFn_stressG Seps γ p.ν_pos T)
  refine ⟨hsol.solenoidal, fun Φ hΦ => ?_⟩
  exact (hsol.equation Φ hΦ).trans
    (congrArg Neg.neg (hPA p.c p.ε p.c_pos p.ε_pos _ _ (zsum_zOfStr γ p.ν_pos hρ T) Φ))

/-- **The real curved stress inverse exists** (source 1675-1690: `S_ε = T_ε s div_ε`, completion
from smooth tensors with the energy bound `near:free-energy`; real form, 1641-1646, 2676-2679):
at a level with `ε ≤ 1`, `P = 2εc ≤ 1` and real `μ > -1/4`, for every `m_Z ≥ 0`, `ρ_b > 0` there
is a real form `S_ε : Z → H` (`IsStressTransport`) of a stress map of `T_ε`. -/
def StressTransportExists : Prop :=
  ∀ (p : Params) (μ : ℝ), p.ε ≤ 1 → p.period ≤ 1 → -(1 / 4) < μ → ∀ (mZ ρb : ℝ), 0 ≤ mZ →
    0 < ρb → ∃ (Seps : Zsp p.c mZ ρb →L[ℝ] Hsp p.c)
      (Seps' : UnforcedLeray.Short.PartIIa.HTSpace p.c →L[ℂ] HSpace p.c MeridC),
      UnforcedLeray.Short.PartIIa.IsStressMap p.c p.ε
          (UnforcedLeray.Short.PartIIa.Teps (P := p.period) p.ν_pos p.ε_pos p.c_pos rfl (μ : ℂ))
          Seps' ∧ NearInst.IsStressTransport Seps Seps'

/-- `StressTransportExists` from the complex stress map of `T_ε` (`PartIIa.NearStressMapExists`,
source 1678-1690), its reality (`Masked.StressMapReal`, 1675-1679) and the cell recentring
(`Masked.CellPtHT`, `CellPtInvH`, `CellPtH`), with the real form `Masked.realForm`
(`Masked.isStressTransport_realForm`); the first half of `Masked.maskedNearExists_of`, at real
`μ > -1/4` with `M = |μ|`, `γ_* = μ + 1/4`. -/
theorem stressTransportExists_of (hN : UnforcedLeray.Short.PartIIa.NearStressMapExists)
    (hR : NearInst.Masked.StressMapReal) (hT : ∀ c : ℝ, 0 < c → NearInst.Masked.CellPtHT c)
    (hH : ∀ c : ℝ, 0 < c → NearInst.Masked.CellPtInvH c)
    (hH' : ∀ c : ℝ, 0 < c → NearInst.Masked.CellPtH c) : StressTransportExists := by
  intro p μ hε1 hP1 hμ mZ ρb hmZ hρ
  obtain ⟨C, _, hNS⟩ := hN
  have hμr : μ + 1 / 4 ≤ (μ : ℂ).re + 1 / 4 := by rw [Complex.ofReal_re]
  obtain ⟨⟨S', hS', -⟩, -⟩ := hNS p.ν p.c ‖(μ : ℂ)‖ (μ + 1 / 4) p.ν_pos p.c_pos (by linarith)
    p.ε p.ε_pos hε1 p.period rfl hP1 (μ : ℂ) le_rfl hμr
  have hreal : NearInst.Masked.IsRealStress p.c S' :=
    hR p.ν p.ε p.c p.period p.ν_pos p.ε_pos p.c_pos rfl μ hμ S' hS'
  exact ⟨NearInst.Masked.realForm p.c mZ ρb hmZ hρ (hT p.c p.c_pos) (hH p.c p.c_pos) S', S', hS',
    NearInst.Masked.isStressTransport_realForm hmZ hρ (hT p.c p.c_pos) (hH p.c p.c_pos)
      (hH' p.c p.c_pos) S' hreal⟩

/-! ## 3. (c) `S_N = S_μ - S_far` -/

/-- Weak stress inverses are unique (free weak uniqueness, source 1571, 1580-1583). -/
theorem eq_of_isWeakStressInverse {c mZ ρb γ ν ε μ : ℝ} (hU : FreeWeakUniqueness c γ ν ε μ)
    {S S' : StrG c mZ ρb γ ν →L[ℝ] VelG c γ ν} (h : IsWeakStressInverse S ε μ)
    (h' : IsWeakStressInverse S' ε μ) : S = S' :=
  ContinuousLinearMap.ext fun T => hU _ _ _ (h T) (h' T)

/-- **The transported far part has the gain-normed far pin** (source 3902-3912): if
`S_far' : Z → H` has the exact kernel realization `IsFarMask`, then `stressG S_far'` has
`IsFarMaskG` (the same kernel formula, on the same chart functions with the same component sum). -/
theorem isFarMaskG_stressG {c mZ ρb R ν μ δ Scut : ℝ} (γ : ℝ) (hν : 0 < ν) (hρ : 0 < ρb)
    {Sf : Zsp c mZ ρb →L[ℝ] Hsp c} (h : NearInst.IsFarMask R ν μ δ Scut Sf) :
    IsFarMaskG R μ δ Scut (stressG Sf γ hν) := fun F f hf hFf =>
  (coeFn_stressG Sf γ hν F).trans (h _ f hf ((zsum_zOfStr γ hν hρ F).trans hFf))

/-- **(c) The near split from the masked near pin** (source 3888-3920, 5785): for a return base
whose stress inverse is a weak stress inverse (`IsStressInverse`) and whose near inverse is the
transport of `o.SN` with `o.SN = S_ε - S_far'` (`IsMaskedNear`): `B.SN = B.S - stressG S_far'`
with `IsFarMaskG`, since `B.S = stressG S_ε` by free weak uniqueness. -/
theorem isNearSplit_of_masked (hW : NearInst.StressMapWeakSol) (hPA : NearInst.StressPairAE)
    {p : Params} {μ δ Scut : ℝ} (hP : p.period ≤ 1) (hμ : -(1 / 4) < μ) {mZ ρb γ : ℝ}
    (hmZ : 0 ≤ mZ) (hρ : 0 < ρb) (hU : FreeWeakUniqueness p.c γ p.ν p.ε μ) {Aff : Type}
    [NormedAddCommGroup Aff] [NormedSpace ℝ Aff] [CompleteSpace Aff]
    (B : ReturnBase p.c mZ ρb γ p.ν Aff) (o : NearInst.NearOps p.c mZ ρb)
    (hS : IsStressInverse B p.ε μ) (hSN : B.SN = o.SNG γ p.ν_pos)
    (hN : NearInst.IsMaskedNear p μ δ Scut o.SN) : IsNearSplit B p.ε μ δ Scut := by
  obtain ⟨Seps, Sf, Seps', hmap, htr, hfar, hoSN⟩ := hN
  have hSe := isWeakStressInverse_stressG hW hPA hP hμ γ hmZ hρ hmap htr
  have hBS : B.S = stressG Seps γ p.ν_pos := eq_of_isWeakStressInverse hU hS hSe
  refine ⟨stressG Sf γ p.ν_pos, isFarMaskG_stressG γ p.ν_pos hρ hfar, ?_⟩
  rw [hSN, SNG_eq_stressG, hoSN, stressG_sub, hBS]

/-! ## 4. (b) The body inverse `R_μ = D_μ⁻¹ℙ` -/

/-- **The weak-to-graph upgrade** (source 1351-1362 `bg:common-body-graph` at `r = 2`,
`γ_2 = 1/4`, `0 < P ≤ 1`; 1580-1583): a field `w ∈ Y_2` that is a weakly solenoidal
distributional solution of `D_μ w = ℙf` against solenoidal tests, `f ∈ Y_2`, `μ > -1/4`, is the
free response of `f` (it lies in the maximal graph `D_2`). -/
def WeakToFreeResponse : Prop :=
  ∀ (P ν μ : ℝ) (f w : ℝ × Space → CVec3), 0 < P → P ≤ 1 → 0 < ν → 0 < μ + 1 / 4 →
    UnforcedLeray.Short.IIb.IsInYr P 2 f → UnforcedLeray.Short.IIb.IsInYr P 2 w →
    IsWeakDmu ν μ P w (fun Φ => pairF P Φ f) →
      UnforcedLeray.Short.IIb.IsFreeResponse ν (μ : ℂ) 2 P f w

/-- `WeakToFreeResponse` (source 1351-1362, 1580-1583): the graph solution `w₁` of `f` exists
(`IIb.field_response_exists`), `w₁ - w` is a homogeneous `Y_2` weak solution (`YrSub`,
`WeakDmuSubY`), hence vanishes (`FWUHomog`), and free responses are a.e. classes
(`FreeResponseAECongr`). -/
theorem weakToFreeResponse_of (hLP : UnforcedLeray.Short.IIb.LerayPairSol) (hH : FWUHomog)
    (hY : YrSub) (hS : WeakDmuSubY) (hC : FreeResponseAECongr) : WeakToFreeResponse := by
  intro P ν μ f w hP hP1 hν hμ hf hw hweak
  have hμ' : 0 < (μ : ℂ).re + (3 / (2 : ℝ) - 1) / 2 := by
    rw [Complex.ofReal_re]
    linarith
  obtain ⟨w₁, h₁⟩ := UnforcedLeray.Short.IIb.field_response_exists hLP hf hP hP1 hν hμ'
    (by norm_num) (by norm_num)
  have hw₁ : IsWeakDmu ν μ P w₁ (fun Φ => pairF P Φ f) := ⟨h₁.solenoidal, h₁.equation⟩
  have hd := hS ν μ P w₁ w _ hP h₁.mem_w hw hw₁ hweak
  have h0 := hH P ν μ hP hP1 hν hμ (w₁ - w) (hY P w₁ w hP h₁.mem_w hw) hd
  have hae : w =ᵐ[volume] w₁ := by
    filter_upwards [h0] with x hx
    have hx' : w₁ x - w x = 0 := hx
    exact (sub_eq_zero.1 hx').symm
  exact hC ν (μ : ℂ) 2 P f w₁ w h₁ hae

/-- **The lift of `bodyG R_ε f` is a weak free solution** (source 1675-1677, 1351-1362,
4139-4146): `bodyG R_ε f` carries the chart function `R_ε h`, `h` the same force in `H`
(`coeFn_bodyG`); `TepsWeakSol` applies to the complexified recentred force (`Body.cplxH`).
(The middle of `NearInst.isBodyLinked_of`.) -/
theorem bodyG_isWeakDmu (hT : NearInst.TepsWeakSol) {p : Params} {μ : ℝ} (hP : p.period ≤ 1)
    (hμ : -(1 / 4) < μ) (γ : ℝ) (hHc : NearInst.Masked.CellPtH p.c)
    {Reps : Hsp p.c →L[ℝ] Hsp p.c}
    (hR : NearInst.IsBodyTransport Reps
      (UnforcedLeray.Short.PartIIa.Teps (P := p.period) p.ν_pos p.ε_pos p.c_pos rfl (μ : ℂ)))
    (f : SrcG p.c) :
    IsWeakDmu p.ν μ (2 * p.ε * p.c) (velPhys p.ε⁻¹ p.c (NearInst.bodyG Reps γ p.ν_pos f))
      (fun Φ => pairF (2 * p.ε * p.c) Φ (velPhys p.ε⁻¹ p.c f)) := by
  set h : Hsp p.c := (Real.sqrt Real.pi)⁻¹ • NearInst.srcIso p.c f with hhdef
  have hh : (h : Chart → Merid) =ᵐ[ageμ p.c (-3 / 2)] (f : Chart → Merid) :=
    NearInst.coeFn_hOfSrc f
  have hh0 := NearInst.Body.cplxH_ae p.c hHc h
  have hpull := NearInst.ae_cellPt_of hHc hh
  have hh' : (NearInst.Body.cplxH p.c hHc h : Profile → MeridC) =ᵐ[measureH p.c]
      (fun q => NearInst.merC ((f : Chart → Merid) (NearInst.cellPt p.c q))) := by
    filter_upwards [hh0, hpull] with q a1 a2
    rw [a1, a2]
  set w : VelG p.c γ p.ν := NearInst.bodyG Reps γ p.ν_pos f with hwdef
  have hwR := NearInst.coeFn_bodyG (γ := γ) p.ν_pos Reps f
  have hwpull := NearInst.ae_cellPt_of hHc hwR
  have hTw : (UnforcedLeray.Short.PartIIa.Teps (P := p.period) p.ν_pos p.ε_pos p.c_pos rfl
      (μ : ℂ) (NearInst.Body.cplxH p.c hHc h) : Profile → MeridC) =ᵐ[measureH p.c]
      (fun q => NearInst.merC ((w : Chart → Merid) (NearInst.cellPt p.c q))) := by
    filter_upwards [hR h (NearInst.Body.cplxH p.c hHc h) hh0, hwpull] with q a1 a2
    rw [a1, a2]
  exact hT p μ hP hμ γ f (NearInst.Body.cplxH p.c hHc h) w hh' hTw

/-- **(b) The body pin for a base whose body inverse is `bodyG R_ε`** (source 1351-1362,
1675-1677, 4139-4146, 5781, 5820): `B.R f` lifted is the free response of `𝒩_v f`
(`IsBodyInverse`), from the weak solution (`bodyG_isWeakDmu`), the weak-to-graph upgrade and the
`Y_2`-membership of the lifts (`fwuLiftYr`, `SrcLiftYr`). -/
theorem isBodyInverse_of_bodyG (hT : NearInst.TepsWeakSol) (hWF : WeakToFreeResponse)
    (hSY : SrcLiftYr) {p : Params} {μ : ℝ} (hP : p.period ≤ 1) (hμ : -(1 / 4) < μ)
    (hHc : NearInst.Masked.CellPtH p.c) {mZ ρb γ : ℝ} {Aff : Type} [NormedAddCommGroup Aff]
    [NormedSpace ℝ Aff] [CompleteSpace Aff] (B : ReturnBase p.c mZ ρb γ p.ν Aff)
    {Reps : Hsp p.c →L[ℝ] Hsp p.c}
    (hR : NearInst.IsBodyTransport Reps
      (UnforcedLeray.Short.PartIIa.Teps (P := p.period) p.ν_pos p.ε_pos p.c_pos rfl (μ : ℂ)))
    (hB : B.R = NearInst.bodyG Reps γ p.ν_pos) : IsBodyInverse B p.ε μ := by
  intro f
  rw [hB]
  have hP0 : 0 < 2 * p.ε * p.c := p.period_pos
  exact hWF (2 * p.ε * p.c) p.ν μ _ _ hP0 hP p.ν_pos (by linarith)
    (hSY p.c p.ε p.c_pos p.ε_pos f) (fwuLiftYr p.c_pos p.ν_pos p.ε_pos _)
    (bodyG_isWeakDmu hT hP hμ γ hHc hR f)

/-! ## 5. The pins of the concrete base at one level -/

section Concrete

variable {Pl : PlanarData} {K : ReturnConsts} {L : ReturnLevel} {μ : ℝ}

/-- `ρ_b = C₀ν^{-k₀}e^{m₀/ν}ε^{3/11} > 0` for `C₀ > 0` (source 2706-2713). -/
theorem inv_rhoB_pos (hC0 : 0 < K.C0) : 0 < L.ρb Pl K := by
  unfold ReturnLevel.ρb UnforcedLeray.Short.IIb.rhoB
  exact mul_pos (mul_pos (mul_pos hC0 (inv_pos.2 (pow_pos (L.params Pl).ν_pos _)))
    (Real.exp_pos _)) (Real.rpow_pos_of_pos (L.params Pl).ε_pos _)

/-- **(a) `S_μ` exists at a level** (source 4145, 1556-1572, 1580-1583, 3888-3890) with `ε ≤ 1`,
`P = 2εc ≤ 1`, `μ > -1/4`, `m_Z ≥ 0`, `ρ_b > 0`: the transported real stress inverse of `T_ε`.
This is the hypothesis of `concreteBase_isStressInverse`. -/
theorem exists_weakStressInverse_level (hST : StressTransportExists)
    (hW : NearInst.StressMapWeakSol) (hPA : NearInst.StressPairAE) (hε1 : L.ε ≤ 1)
    (hP : (L.params Pl).period ≤ 1) (hμ : -(1 / 4) < μ) (hmZ : 0 ≤ K.mZ) (hρ : 0 < L.ρb Pl K) :
    ∃ S : LStr Pl K L →L[ℝ] LVel Pl L, IsWeakStressInverse S L.ε μ := by
  obtain ⟨Seps, Seps', hmap, htr⟩ := hST (L.params Pl) μ hε1 hP hμ K.mZ (L.ρb Pl K) hmZ hρ
  exact ⟨stressG Seps (gRate Pl) L.ν_pos,
    isWeakStressInverse_stressG hW hPA hP hμ (gRate Pl) hmZ hρ hmap htr⟩

/-- **(c) The near split pin of the concrete base** (source 3888-3920, 5785): with the actual near
operators `nearOpsAt` (whose existence is the hypothesis `hex`), `SNop = Sop - S_far` with
`IsFarMaskG`, gap `δ` and output cut `S = ε^{-b}`. -/
theorem concreteBase_isNearSplit (hW : NearInst.StressMapWeakSol) (hPA : NearInst.StressPairAE)
    (hU : FreeWeakUniqueness (cOf L.ν) (gRate Pl) L.ν L.ε μ) (hP : (L.params Pl).period ≤ 1)
    (hμ : -(1 / 4) < μ) (hmZ : 0 ≤ K.mZ) (hρ : 0 < L.ρb Pl K)
    (hex : ∃ o : NearInst.NearOps (cOf L.ν) K.mZ (L.ρb Pl K),
      NearInst.IsActualNear (L.params Pl) L.V L.rb μ K.δ (L.Scut K) o)
    (h : NearAt Pl K L μ) :
    IsNearSplit (concreteBase Pl K L μ h) L.ε μ K.δ (L.Scut K) := by
  have hA := (nearOpsAt_spec hex).1
  obtain ⟨Seps, Sf, Seps', hmap, htr, -, -⟩ := hA.near
  have hS : IsStressInverse (concreteBase Pl K L μ h) L.ε μ :=
    concreteBase_isStressInverse h
      ⟨_, isWeakStressInverse_stressG hW hPA hP hμ (gRate Pl) hmZ hρ hmap htr⟩
  exact isNearSplit_of_masked hW hPA (p := L.params Pl) hP hμ hmZ hρ hU
    (concreteBase Pl K L μ h) (nearOpsAt Pl K L μ) hS rfl hA.near

/-- **(b) The body pin of the concrete base** (source 1351-1362, 1675-1677, 4139-4146, 5781,
5820): `Rop = bodyG R_ε` with `R_ε = bodyReps` the real form of `T_ε` (whose existence is the
hypothesis `hBR`, `NearInst.BodyRealForms`), so `IsBodyInverse`. -/
theorem concreteBase_isBodyInverse (hT : NearInst.TepsWeakSol) (hWF : WeakToFreeResponse)
    (hSY : SrcLiftYr) (hHc : NearInst.Masked.CellPtH (cOf L.ν)) (hP : (L.params Pl).period ≤ 1)
    (hμ : -(1 / 4) < μ)
    (hBR : ∃ R : Hsp (cOf L.ν) →L[ℝ] Hsp (cOf L.ν), NearInst.IsBodyTransport R
      (UnforcedLeray.Short.PartIIa.Teps (P := (L.params Pl).period) (L.params Pl).ν_pos
        (L.params Pl).ε_pos (L.params Pl).c_pos rfl (μ : ℂ)))
    (h : NearAt Pl K L μ) :
    IsBodyInverse (concreteBase Pl K L μ h) L.ε μ :=
  isBodyInverse_of_bodyG hT hWF hSY (p := L.params Pl) hP hμ hHc (concreteBase Pl K L μ h)
    (Reps := bodyReps Pl L μ) (Classical.epsilon_spec hBR) rfl

end Concrete

end UnforcedLeray.Short.PartIIIb.Concrete
