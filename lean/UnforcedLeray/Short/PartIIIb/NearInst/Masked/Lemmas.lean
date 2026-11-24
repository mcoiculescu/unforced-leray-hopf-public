import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Defs

/-!
# The lemmas for `MaskedNearExists` and `NearMaskedFreeBoundC` (source 1638-1690, 3611-3621,
3888-3912, 3996-4031)

Source of record: `the November 2 reference manuscript`.  One `Prop` per source
step, over the concrete objects of `NearInst.lean`, `NearInst/Chart.lean`, `NearInst/Delta/Defs.lean`
and `NearInst/Masked/Defs.lean`.

## (a) The real form of `S_ε` (source 1641-1646, 1675-1690)

* `TepsReal` : `T_ε = (μ - A_ε)^{-1}P_ε` maps real fields to real fields for real `μ` (1675-1677).
* `TensorTestDense`, `TensorTestDivMem` : smooth tensor tests are dense in `H_T`, and
  `s div_ε M ∈ H` for a test `M` ("the tensor map means completion from smooth tensors", 1678).
* `StressMapReal` : a stress map of `T_ε` (real `μ`) maps real tensors to real fields.
* `StressMapUnique` : the stress map is unique (completion from smooth tensors, 1678).
* `StressTransportNorm` : `‖S‖_{Z→H} ≤ ‖S'‖_{H_T→H}` for a real form (`W ≥ 1`, `ρ_b ≤ 1`).
* `RealStressBound` : `near:free-energy` (1680-1689) in real form, `‖S_ε‖_{Z→H} ≤ Cν^{-1/2}`.

## (b) The far part (source 3905-3912, 3996-4011)

* `BoxDenseZ` : the inputs `F ∈ Z` with `F₁ + F₂` a box tensor are dense.
* `FarKernelL2`, `FarKernelLinear` : the kernel realization `farOut` is bounded `L²` on box tensors
  (positive majorant `C|x|^{-4}` of `sep:kernel`, separation of the radii, dilation margin,
  Young) and linear.
* `FarMaskExists` : a bounded `S_far` with the pin `IsFarMask` exists.

## (c) The masked free bound (source 3974-4031)

* `StressKernelRealization` : `S_ε` acts on box tensors by the unmasked kernel `fullOut`
  (`sep:resolvent`, 3611-3621; "the finite-curvature free inverse is the conjugate of the Cartesian
  weak-stress inverse", 3888-3891).
* `MaskedSupport` : `1_{s<T}S_N1_{t≥e^δT} = 0` for `T ≤ S` (the mask keeps only `t ≤ e^δ s`).
* `FarBlockZero` : `1_{s≥l}S_far1_{t<e^δ l} = 0` (complete blocks see no far part).
* `FarUpperZero` : `1_{s≥S}S_far = 0` (the factor `1_{s<S}`).
* `StripKernelBound`, `MaskedStripBound` : the partial strip `1_{l≤s<r}S_N1_{t≥e^δ l}` has norm
  `≤ P_ν ε√r` (3996-4005).
* `ForbiddenKernelBound`, `ForbiddenBlockBound` : the forbidden separated subblock
  `1_{s<s₋}S_far1_{t<e^δ s₋}` has norm `≤ P_ν ε√s₋` (4011-4014).
* `GainBlockBound` : `‖g⁻¹1_A X 1_B g‖ ≤ (sup_A g⁻¹)(sup_B g)‖X‖` (the cost of the gain on a block,
  3978-3981).
* `MaskedLowerPiece`, `MaskedBinPiece`, `MaskedUpperPiece` : the gained pieces of
  `g⁻¹S_N g` on `s < s₋`, a bin `[l, r)` and `s ≥ S` (4022-4031: "the same complete blocks, using
  free energy in place of the difference estimate ... the lower end has gain ratio `1 + o(1)`, and
  the upper end has the ratio just displayed").
* `OutBandPartition` : the output regions `s < s₋`, the bins of `[s₋, S)` and `s ≥ S` partition the
  chart (3974-3977).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

/-! ## (a) The real form of `S_ε` -/

/-- **`T_ε` preserves real fields** (source 1675-1677: `T_ε = (μ - A_ε)^{-1}P_ε`, with
`A_ε = -S + νs[(Q_ε² + ∂_η²)I - ε²E]` a real operator and `P_ε` the conjugated Cartesian Leray
projection, a real operator; `PartIIa.Teps = B0223.RepsVec ∘ PepsC`, the Laplace transform of the
real Ornstein-Uhlenbeck semigroup conjugated by the real lift, and the orthogonal projection onto
the complexification of the real solenoidal subspace).  For real `μ > -1/4`, `T_ε` maps
`IsRealH` fields to `IsRealH` fields. -/
def TepsReal : Prop :=
  ∀ (ν ε c P : ℝ) [Fact (0 < P)] (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c)
    (μ : ℝ), -(1 / 4) < μ → ∀ g : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC,
      IsRealH c g → IsRealH c (UnforcedLeray.Short.PartIIa.Teps hν hε hc hP (μ : ℂ) g)

/-- **Smooth tensor tests are dense in `H_T`** (source 1678: "the tensor map means completion from
smooth tensors"; `PartIIa.IsTensorTest`: smooth, `c`-periodic in `q`, supported in a band
`s₀ ≤ s ≤ s₁`, `|η| ≤ L`). -/
def TensorTestDense : Prop :=
  ∀ c : ℝ, 0 < c → ∀ (F : UnforcedLeray.Short.PartIIa.HTSpace c) (η : ℝ), 0 < η →
    ∃ M : UnforcedLeray.B0220.Profile → UnforcedLeray.Short.PartIIa.TensorVal,
      UnforcedLeray.Short.PartIIa.IsTensorTest c M ∧
        ∃ hM : MemLp M 2 (UnforcedLeray.Short.PartIIa.measureHT c), ‖F - hM.toLp M‖ < η

/-- **`s div_ε M ∈ H` for a smooth tensor test** (source 1660-1665, 1678; smooth with band support
on the cell, so bounded with support of finite measure). -/
def TensorTestDivMem : Prop :=
  ∀ c ε : ℝ, 0 < c → ∀ M : UnforcedLeray.B0220.Profile → UnforcedLeray.Short.PartIIa.TensorVal,
    UnforcedLeray.Short.PartIIa.IsTensorTest c M →
      MemLp (fun p => (p.1 : ℂ) • UnforcedLeray.Short.PartIIa.divEps ε M p) 2
        (UnforcedLeray.B0220.measureH c)

/-- **Stress maps of `T_ε` are real** (source 1675-1679): for real `μ > -1/4`, a stress map `S'` of
`T_ε` (`PartIIa.IsStressMap`) maps real tensors to real fields. -/
def StressMapReal : Prop :=
  ∀ (ν ε c P : ℝ) [Fact (0 < P)] (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c)
    (μ : ℝ), -(1 / 4) < μ →
    ∀ S' : UnforcedLeray.Short.PartIIa.HTSpace c →L[ℂ]
      UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC,
      UnforcedLeray.Short.PartIIa.IsStressMap c ε
          (UnforcedLeray.Short.PartIIa.Teps hν hε hc hP (μ : ℂ)) S' → IsRealStress c S'

/-- **Uniqueness of the stress map** (source 1678: completion from smooth tensors). -/
def StressMapUnique : Prop :=
  ∀ (c ε : ℝ)
    (T : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC →L[ℂ]
      UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC)
    (S₁ S₂ : UnforcedLeray.Short.PartIIa.HTSpace c →L[ℂ]
      UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC),
    0 < c → UnforcedLeray.Short.PartIIa.IsStressMap c ε T S₁ →
      UnforcedLeray.Short.PartIIa.IsStressMap c ε T S₂ → S₁ = S₂

/-- **The real form has at most the norm of the complex map** (source 1641-1646, 2676-2679,
3564-3565: the two cell normalisations `dq` and `dq/c` change both norms by `√c`;
`‖tv4 T‖ ≤ ‖T‖`; `‖F₁ + F₂‖_{H_T} ≤ ‖F₁‖_{Z₁} + √ρ_b‖F₂‖_{ρ_b^{-1/2}H_T} ≤ ‖F‖_Z` for `W ≥ 1`,
`ρ_b ≤ 1`). -/
def StressTransportNorm : Prop :=
  ∀ (c mZ ρb : ℝ), 0 < c → 0 ≤ mZ → 0 < ρb → ρb ≤ 1 →
    ∀ (S' : UnforcedLeray.Short.PartIIa.HTSpace c →L[ℂ]
        UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC)
      (S : Zsp c mZ ρb →L[ℝ] Hsp c), IsStressTransport S S' → ‖S‖ ≤ ‖S'‖

/-- **`near:free-energy` in real form** (source 1680-1689, the `b`-part: `‖S_εM‖_H ≤ Cν^{-1/2}‖M‖_{H_T}`
uniformly for `0 < ε ≤ 1`, `P = 2εc ≤ 1` and `μ` in a compact subset of `Re μ > -1/4`; here
`0 < μ < 1/4`): every real form of a stress map of `T_ε` has `‖S‖_{Z→H} ≤ Cν^{-1/2}`. -/
def RealStressBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν ε c P : ℝ) [Fact (0 < P)] (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c)
    (hP : P = 2 * ε * c), ε ≤ 1 → P ≤ 1 → ∀ μ : ℝ, 0 < μ → μ < 1 / 4 →
    ∀ (mZ ρb : ℝ), 0 ≤ mZ → 0 < ρb → ρb ≤ 1 →
    ∀ (S' : UnforcedLeray.Short.PartIIa.HTSpace c →L[ℂ]
        UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC)
      (S : Zsp c mZ ρb →L[ℝ] Hsp c),
      UnforcedLeray.Short.PartIIa.IsStressMap c ε
          (UnforcedLeray.Short.PartIIa.Teps hν hε hc hP (μ : ℂ)) S' →
        IsStressTransport S S' → ‖S‖ ≤ C * ν ^ (-(1 / 2 : ℝ))

/-! ## (b) The far part -/

/-- **Box inputs are dense in `Z`** (source 3905-3912: the kernel pin is on the dense class): for
`c > 0`, `m_Z ≥ 0`, `ρ_b > 0`, every `F ∈ Z` is approximated by `F'` whose component sum
`F'₁ + F'₂` is a.e. a box tensor (`IsBoxTensor`: bounded measurable, `s₁ ≤ s ≤ s₂`, `|η| ≤ L`). -/
def BoxDenseZ : Prop :=
  ∀ c mZ ρb : ℝ, 0 < c → 0 ≤ mZ → 0 < ρb → ∀ (F : Zsp c mZ ρb) (η : ℝ), 0 < η →
    ∃ F' : Zsp c mZ ρb, (∃ f : Chart → Ten3, IsBoxTensor f ∧ zsum F' =ᵐ[ageμ c (-1 / 2)] f) ∧
      ‖F - F'‖ < η

/-- **The far kernel is bounded on box tensors** (source 3996-4011: on the far region `t > e^δ s`
the source radius `R/√t` is below `e^{-δ/2}` times the output radius `R/√s`, also after the
contraction `z ↦ λz` of `sep:resolvent`; the heat-Leray kernel has the positive majorant
`|∇K_t(x)| ≤ C|x|^{-4}` (`sep:kernel`, `IIIa.SepKernelBounds`), whose `L¹` norm outside distance
`d` is `C/d`; the dilation integral has power `λ^{2Re μ+1/2}`; Young and normalized-phase
Minkowski give an `L²` bound; the lifts `b ↦ √s b`, `T ↦ sT` multiply both norms by `√πR`).
For `R, c, ν, δ, S > 0` and real `μ > -1/4` there is `C` with
`‖farOut f‖_H ≤ C ‖f‖_{H_T}` for every box tensor `f` (and `farOut f` is a.e. strongly
measurable). -/
def FarKernelL2 : Prop :=
  ∀ (R c ν δ S μ : ℝ), 0 < R → 0 < c → 0 < ν → 0 < δ → 0 < S → -(1 / 4) < μ →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Chart → Ten3, IsBoxTensor f →
      AEStronglyMeasurable (farOut R c ν μ δ S f) (ageμ c (-3 / 2)) ∧
        eLpNorm (farOut R c ν μ δ S f) 2 (ageμ c (-3 / 2)) ≤
          ENNReal.ofReal C * eLpNorm f 2 (ageμ c (-1 / 2))

/-- **The far kernel is linear on box tensors** (source 3905-3912; the masked `sep:resolvent`
integrals converge absolutely on box tensors since the mask keeps only separated pairs, and
`cartLift`, the mask and `sepW` are linear in the tensor). -/
def FarKernelLinear : Prop :=
  ∀ (R c ν δ S μ : ℝ), 0 < R → 0 < c → 0 < ν → 0 < δ → 0 < S → -(1 / 4) < μ →
    ∀ f g : Chart → Ten3, IsBoxTensor f → IsBoxTensor g → ∀ a : ℝ,
      farOut R c ν μ δ S (f + a • g) =ᵐ[ageμ c (-3 / 2)]
        farOut R c ν μ δ S f + a • farOut R c ν μ δ S g

/-- **`S_far` exists** (source 3905-3912, "its exact kernel realization"): for `c, R, ν, δ, S > 0`,
`m_Z ≥ 0`, `ρ_b > 0` and real `μ > -1/4` there is a bounded `S_far : Z → H` with the pin
`IsFarMask` (extension by density from box inputs, `FarKernelL2`, `FarKernelLinear`,
`BoxDenseZ`). -/
def FarMaskExists : Prop :=
  ∀ (c mZ ρb R ν δ S μ : ℝ), 0 < c → 0 ≤ mZ → 0 < ρb → 0 < R → 0 < ν → 0 < δ → 0 < S →
    -(1 / 4) < μ → ∃ Sf : Zsp c mZ ρb →L[ℝ] Hsp c, IsFarMask R ν μ δ S Sf

/-! ## (c) The masked free bound -/

/-- **The kernel realization of `S_ε`** (source 3611-3621 `sep:resolvent`: `S_μ T = -W_μ`; source
3888-3891: "the finite-curvature free inverse is the conjugate of the Cartesian weak-stress
inverse"; lifts `𝒩_v b = √s b`, `𝒩_T T = sT`, 2683; chart `R = ε⁻¹`, 1640-1641): every real form
`S` of a stress map of `T_ε` acts on box inputs by the unmasked kernel `fullOut ε⁻¹ c ν μ` (the
pin `IsFarMask` without mask and output cut). -/
def StressKernelRealization : Prop :=
  ∀ (ν ε c P : ℝ) [Fact (0 < P)] (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c)
    (μ : ℝ), -(1 / 4) < μ → ∀ (mZ ρb : ℝ)
    (S' : UnforcedLeray.Short.PartIIa.HTSpace c →L[ℂ]
      UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC)
    (S : Zsp c mZ ρb →L[ℝ] Hsp c),
    UnforcedLeray.Short.PartIIa.IsStressMap c ε
        (UnforcedLeray.Short.PartIIa.Teps hν hε hc hP (μ : ℂ)) S' → IsStressTransport S S' →
      ∀ (F : Zsp c mZ ρb) (f : Chart → Ten3), IsBoxTensor f → zsum F =ᵐ[ageμ c (-1 / 2)] f →
        (S F : Chart → Merid) =ᵐ[ageμ c (-3 / 2)] fullOut ε⁻¹ c ν μ f

/-- **The mask keeps only `t ≤ e^δ s`** (source 3905-3912): for `0 < T ≤ S`, outputs `s < T` of
`S_N = S_ε - S_far` see no input `t ≥ e^δ T` (there the far part is all of `S_ε`). -/
def MaskedSupport : Prop :=
  ∀ (p : Params) (mZ ρb μ δ S T : ℝ), 0 ≤ mZ → 0 < ρb → ρb ≤ 1 → 0 < μ → 0 < δ → 0 < T →
    T ≤ S → ∀ Seps Sf : Zsp p.c mZ ρb →L[ℝ] Hsp p.c, IsMaskedPair p μ δ S Seps Sf →
      outRestr p.c (ageBelow T) ∘L (Seps - Sf) ∘L
          inRestr p.c mZ ρb (ageAbove (Real.exp δ * T)) = 0

/-- **Complete blocks see no far part** (source 3905-3912, 3978-3979): outputs `s ≥ l` of `S_far`
see no input `t < e^δ l` (the mask keeps `t > e^δ s ≥ e^δ l`). -/
def FarBlockZero : Prop :=
  ∀ (c mZ ρb R ν μ δ S l : ℝ), 0 < c → 0 ≤ mZ → 0 < ρb → ρb ≤ 1 → 0 < δ → 0 < l →
    ∀ Sf : Zsp c mZ ρb →L[ℝ] Hsp c, IsFarMask R ν μ δ S Sf →
      outRestr c (ageAbove l) ∘L Sf ∘L inRestr c mZ ρb (ageBelow (Real.exp δ * l)) = 0

/-- **The far part has no output `s ≥ S`** (source 3907: the factor `1_{s<S}`; 4015-4016: "for
`s > S`, use the full free inverse"). -/
def FarUpperZero : Prop :=
  ∀ (c mZ ρb R ν μ δ S : ℝ), 0 < c → 0 ≤ mZ → 0 < ρb → ρb ≤ 1 →
    ∀ Sf : Zsp c mZ ρb →L[ℝ] Hsp c, IsFarMask R ν μ δ S Sf → outRestr c (ageAbove S) ∘L Sf = 0

/-- **The partial-strip kernel estimate** (source 3996-4005): for a bin `l < r ≤ e^{δ/2}l`,
`r ≤ S = ε^{-b}`, and a box tensor `f` supported in `t ≥ e^δ l`, the strip kernel
`fullOut - farOut` (mask `e^δ l ≤ t ≤ e^δ s`) on the outputs `l ≤ s < r` satisfies
`‖·‖_H ≤ P_ν ε√r ‖f‖_{H_T}`: the source radius is separated from the output radius by a fixed
multiple of `R/√r` (`t ≥ e^δ l > e^{δ/2}s`), the positive majorant `C|x|^{-4}` (`sep:kernel`) has
`L¹` norm `C/d` outside distance `d`, the dilation integral has power `λ^{2Re μ+1/2}`, then Young
and normalized-phase Minkowski. -/
def StripKernelBound : Prop :=
  ∀ Kset : Set ℝ, IsCompact Kset → Kset ⊆ Ioo 0 (1 / 4) → ∀ dm dp : ℝ, 0 < dm →
    ∀ b δ : ℝ, 0 < b → b < 1 → 0 < δ →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ μ ∈ Kset, ∀ l r : ℝ, 0 < l → l < r → r ≤ Real.exp (δ / 2) * l → r ≤ p.ε ^ (-b) →
      ∀ f : Chart → Ten3, IsBoxTensor f → (∀ x, f x ≠ 0 → Real.exp δ * l ≤ x.1) →
        eLpNorm ((ageBand l r).indicator
            (fullOut p.R p.c p.ν μ f - farOut p.R p.c p.ν μ δ (p.ε ^ (-b)) f)) 2
            (ageμ p.c (-3 / 2)) ≤
          ENNReal.ofReal (C * p.ν⁻¹ ^ k * (p.ε * Real.sqrt r)) * eLpNorm f 2 (ageμ p.c (-1 / 2))

/-- **The partial strip** (source 3996-4005, operator form): for a bin `l < r ≤ e^{δ/2}l`,
`r ≤ S = ε^{-b}`, `‖1_{l≤s<r}S_N1_{t≥e^δ l}‖_{Z→H} ≤ P_ν ε√r`. -/
def MaskedStripBound : Prop :=
  ∀ Kset : Set ℝ, IsCompact Kset → Kset ⊆ Ioo 0 (1 / 4) → ∀ mZ : ℝ, 0 ≤ mZ →
    ∀ dm dp : ℝ, 0 < dm → ∀ b δ : ℝ, 0 < b → b < 1 → 0 < δ →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ ρb : ℝ, 0 < ρb → ρb ≤ 1 → ∀ μ ∈ Kset, ∀ Seps Sf : Zsp p.c mZ ρb →L[ℝ] Hsp p.c,
        IsMaskedPair p μ δ (p.ε ^ (-b)) Seps Sf →
      ∀ l r : ℝ, 0 < l → l < r → r ≤ Real.exp (δ / 2) * l → r ≤ p.ε ^ (-b) →
        ‖outRestr p.c (ageBand l r) ∘L (Seps - Sf) ∘L
            inRestr p.c mZ ρb (ageAbove (Real.exp δ * l))‖ ≤
          C * p.ν⁻¹ ^ k * (p.ε * Real.sqrt r)

/-- **The forbidden separated subblock, kernel estimate** (source 4011-4014): for `0 < s₋ ≤ S` and a
box tensor `f` supported in `t < e^δ s₋`, the far kernel on the outputs `s < s₋` (mask
`e^δ s < t < e^δ s₋`) satisfies `‖·‖_H ≤ P_ν ε√s₋ ‖f‖_{H_T}`, "by the same positive-kernel
estimate" as the partial strips. -/
def ForbiddenKernelBound : Prop :=
  ∀ Kset : Set ℝ, IsCompact Kset → Kset ⊆ Ioo 0 (1 / 4) → ∀ dm dp : ℝ, 0 < dm →
    ∀ b δ : ℝ, 0 < b → b < 1 → 0 < δ →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ μ ∈ Kset, ∀ sm : ℝ, 0 < sm → sm ≤ p.ε ^ (-b) →
      ∀ f : Chart → Ten3, IsBoxTensor f → (∀ x, f x ≠ 0 → x.1 < Real.exp δ * sm) →
        eLpNorm ((ageBelow sm).indicator (farOut p.R p.c p.ν μ δ (p.ε ^ (-b)) f)) 2
            (ageμ p.c (-3 / 2)) ≤
          ENNReal.ofReal (C * p.ν⁻¹ ^ k * (p.ε * Real.sqrt sm)) * eLpNorm f 2 (ageμ p.c (-1 / 2))

/-- **The forbidden separated subblock** (source 4011-4014, operator form):
`‖1_{s<s₋}S_far1_{t<e^δ s₋}‖_{Z→H} ≤ P_ν ε√s₋` for `0 < s₋ ≤ S = ε^{-b}`. -/
def ForbiddenBlockBound : Prop :=
  ∀ Kset : Set ℝ, IsCompact Kset → Kset ⊆ Ioo 0 (1 / 4) → ∀ mZ : ℝ, 0 ≤ mZ →
    ∀ dm dp : ℝ, 0 < dm → ∀ b δ : ℝ, 0 < b → b < 1 → 0 < δ →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ ρb : ℝ, 0 < ρb → ρb ≤ 1 → ∀ μ ∈ Kset, ∀ Sf : Zsp p.c mZ ρb →L[ℝ] Hsp p.c,
        IsFarMask p.R p.ν μ δ (p.ε ^ (-b)) Sf → ∀ sm : ℝ, 0 < sm → sm ≤ p.ε ^ (-b) →
          ‖outRestr p.c (ageBelow sm) ∘L Sf ∘L inRestr p.c mZ ρb (ageBelow (Real.exp δ * sm))‖ ≤
            C * p.ν⁻¹ ^ k * (p.ε * Real.sqrt sm)

/-- **The cost of the gain on a block** (source 3978-3981: "multiplication by `g` on inputs and
`g⁻¹` on outputs costs at most" the ratio of their sups): if `g⁻¹ ≤ a` on the output region `A` and
`g ≤ b` on the input region `B`, then `‖g⁻¹1_A X 1_B G‖_{Z→H} ≤ ab‖X‖`. -/
def GainBlockBound : Prop :=
  ∀ (c mZ ρb γ ν : ℝ) (hν : 0 < ν) (A B : Set Chart) (a b : ℝ) (X : Zsp c mZ ρb →L[ℝ] Hsp c),
    MeasurableSet A → MeasurableSet B → 0 ≤ a → 0 ≤ b →
    (∀ x ∈ A, gainInvFun γ ν x ≤ a) → (∀ x ∈ B, gainFun γ ν x ≤ b) →
      ‖gainBlockS γ hν A B X‖ ≤ a * b * ‖X‖

/-- **The lower end** (source 4011-4014, 4027-4028): for the planar reference (`γ = Re λ > 0`),
the output region `s < s₋ = ε^b` of `g⁻¹S_N g` has norm `≤ P_ν`: retained inputs have
`t < e^δ s₋` (`MaskedSupport`), where `g ≤ e^{γe^δ s₋}` and `g⁻¹ ≤ 1` (gain ratio `1 + o(1)`);
`1_{s<s₋}S_N1_{t<e^δ s₋} = 1_{s<s₋}S_ε1_{t<e^δ s₋} - 1_{s<s₋}S_far1_{t<e^δ s₋}`, the first bounded
by the free energy (`RealStressBound`), the second by `ForbiddenBlockBound`. -/
def MaskedLowerPiece : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ Kset : Set ℝ, IsCompact Kset →
    Kset ⊆ Ioo 0 (1 / 4) → ∀ mZ : ℝ, 0 ≤ mZ → ∀ dm dp : ℝ, 0 < dm →
    ∀ b δ : ℝ, 0 < b → b < 1 → 0 < δ →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ ρb : ℝ, 0 < ρb → ρb ≤ 1 → ∀ μ ∈ Kset, ∀ SN : Zsp p.c mZ ρb →L[ℝ] Hsp p.c,
        IsMaskedNear p μ δ (p.ε ^ (-b)) SN →
          ‖gainRestrS P.eigenvalue.re p.ν_pos (ageBelow (p.ε ^ b)) SN‖ ≤ C * p.ν⁻¹ ^ k

/-- **A bin** (source 3974-3990, 3996-4007, 4022-4026): for `0 < l < r ≤ e^{δ/2}l`, `r ≤ S = ε^{-b}`,
the output band `l ≤ s < r` of `g⁻¹S_N g` has norm `≤ P_ν e^{η_δ/ν}`, `η_δ = γ tanh(3δ/8)`:
the complete block `1_{bin}S_N1_{t<e^δ l} = 1_{bin}S_ε1_{t<e^δ l}` (`FarBlockZero`) costs the gain
ratio `g(e^δ l)/g(l) ≤ e^{γ tanh(δ/4)/ν}` times the free energy (`RealStressBound`); the partial
strip `1_{bin}S_N1_{t≥e^δ l}` has inputs `t < e^δ r ≤ e^{3δ/2}l` (`MaskedSupport`), gain ratio
`≤ e^{η_δ/ν}` (`GainRatioSup` with `M = e^{3δ/2}`, `GainRatioTanh`), and norm `P_ν ε√r ≤ P_ν`
(`MaskedStripBound`). -/
def MaskedBinPiece : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ Kset : Set ℝ, IsCompact Kset →
    Kset ⊆ Ioo 0 (1 / 4) → ∀ mZ : ℝ, 0 ≤ mZ → ∀ dm dp : ℝ, 0 < dm →
    ∀ b δ : ℝ, 0 < b → b < 1 → 0 < δ →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ ρb : ℝ, 0 < ρb → ρb ≤ 1 → ∀ μ ∈ Kset, ∀ SN : Zsp p.c mZ ρb →L[ℝ] Hsp p.c,
        IsMaskedNear p μ δ (p.ε ^ (-b)) SN →
      ∀ l r : ℝ, 0 < l → l < r → r ≤ Real.exp (δ / 2) * l → r ≤ p.ε ^ (-b) →
        ‖gainRestrS P.eigenvalue.re p.ν_pos (ageBand l r) SN‖ ≤
          C * p.ν⁻¹ ^ k * Real.exp (etaDelta P.eigenvalue.re δ / p.ν)

/-- **The upper end** (source 4015-4020, 4028): the output region `s ≥ S = ε^{-b}` of `g⁻¹S_N g` has
norm `≤ P_ν`: there `S_N = S_ε` (`FarUpperZero`), and the gain ratio is at most
`e^{γ/ν}/g(S) = exp{γ/[ν(1+νS)]} = 1 + o(1)` (`νS = νe^{bd/ν} → ∞`), times the free energy. -/
def MaskedUpperPiece : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ Kset : Set ℝ, IsCompact Kset →
    Kset ⊆ Ioo 0 (1 / 4) → ∀ mZ : ℝ, 0 ≤ mZ → ∀ dm dp : ℝ, 0 < dm →
    ∀ b δ : ℝ, 0 < b → b < 1 → 0 < δ →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ ρb : ℝ, 0 < ρb → ρb ≤ 1 → ∀ μ ∈ Kset, ∀ SN : Zsp p.c mZ ρb →L[ℝ] Hsp p.c,
        IsMaskedNear p μ δ (p.ε ^ (-b)) SN →
          ‖gainRestrS P.eigenvalue.re p.ν_pos (ageAbove (p.ε ^ (-b))) SN‖ ≤ C * p.ν⁻¹ ^ k

/-- **The output partition** (source 3974-3977): for `0 < s₋ < S` and `δ > 0`, the regions
`s < s₋`, the `N = binCount s₋ S δ` bins `[l_j, l_{j+1})` (`l_j = binEdge s₋ S N j`) and `s ≥ S`
partition the chart, so the restrictions sum to the identity of `H`. -/
def OutBandPartition : Prop :=
  ∀ (c sm S δ : ℝ), 0 < sm → sm < S → 0 < δ → ∀ u : Hsp c,
    outRestr c (ageBelow sm) u +
        (∑ j ∈ Finset.range (binCount sm S δ),
          outRestr c (ageBand (binEdge sm S (binCount sm S δ) j)
            (binEdge sm S (binCount sm S δ) (j + 1))) u) +
        outRestr c (ageAbove S) u = u

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
