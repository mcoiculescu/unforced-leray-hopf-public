import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F5_2_2

/-!
# `PartII-b:F5/2/2/3` (`P0SliceLiftH1`): statement gap and needed inputs (statements only)

Source: SP lines 2213-2239 (`g = -P_0(v·∇b_0 + b_0·∇v)`).

**Gap.** The conclusion `HasWeakVec vQ0 dZero g gq` requires `Integrable (g_i * ∂_q φ)` on `Coord`
for every `IsCoordTest φ`, i.e. `g ∈ L¹_loc(s > 0)`. `IsBodySource` (tests: compactly supported
planar solenoidal fields), `QPeriodic c g` and the slice bound pin `g(s, ·) = -P₀ U(s, ·)` on a.e.
slice (the only `q`-periodic harmonic gradient in `L²(cell)` is `0`). `P₀` is nonlocal, so
`g ∈ L¹_loc` needs local-in-`s` integrability of `s ↦ ‖U(s, ·)‖_{L²(cell)}`. The hypotheses give
only a.e. finiteness of `sliceH1Norm c U Uq Uη`; `tr` is an arbitrary `B0140.TrainSol` (no decay,
no `IsBUCTrain`), so this is not derivable. The same gap sits in the parent
`CylBodySourceProjection` (arbitrary `p : Params`, no `BgRegime`).

**Fix.** Add the hypothesis `hLoc` of `P0SliceLiftH1Loc` below. In the caller it follows from
`sliceH1Norm_flatBv_le`, `sLpNorm_sliceLpNorm_le_hNorm` (Hölder in `s` on `[a, b]`), and a local
bound of `trainSliceNorm22_3` on compacts of `(0, ∞)` (`TrainWeightedLp22over3Loc` in
`FlatBvSliceGoodAe/Needed.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal

namespace UnforcedLeray.Short.IIb.P0SliceLiftH1Needed

open UnforcedLeray.Short.IIb

/-- `P0SliceLiftH1` with the added hypothesis `hLoc`: the slice `H¹(C_c)` norm of `U` is
integrable on every `[a, b] ⊂ (0, ∞)`. -/
def P0SliceLiftH1Loc : Prop :=
  ∀ (m : ℝ), 8 < m → ∀ {ν c : ℝ} (tr : B0140.TrainSol ν c), 0 < c →
  ∀ (b0 b0' b0q b0η : CProf) (D2 : Fin 2 → Fin 2 → CProf),
    InFlatClass c bgp b0 →
    (∀ᵐ x : Coord, 0 < x.1 → b0' x = b0 x) →
    InHr c bgp b0' → InHr c bgp (sqrtS b0q) → InHr c bgp (sqrtS b0η) →
    (∀ i j, InHr c bgp (mulS (D2 i j))) →
    StronglyMeasurable b0' → StronglyMeasurable b0q → StronglyMeasurable b0η →
    (∀ i j, StronglyMeasurable (D2 i j)) →
    HasWeakVec vQ0 dZero b0 b0q → HasWeakVec vEta dZero b0 b0η →
    HasWeakVec vQ0 dZero b0q (D2 0 0) → HasWeakVec vEta dZero b0q (D2 0 1) →
    HasWeakVec vQ0 dZero b0η (D2 1 0) → HasWeakVec vEta dZero b0η (D2 1 1) →
    let U := flatBv tr b0' b0q b0η
    let Uq := flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0)
    let Uη := flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1)
    HasWeakVec vQ0 dZero U Uq → HasWeakVec vEta dZero U Uη →
    (∀ a b : ℝ, 0 < a → ∫⁻ s in Icc a b, sliceH1Norm c U Uq Uη s < ⊤) →
    (∀ᵐ s ∂volume, 0 < s →
      sliceH1Norm c U Uq Uη s < ⊤ ∧
      sliceXmNorm c m (profCurl Uq Uη) s < ⊤ ∧
      (∀ i : Fin 2,
        IIIa.HasWeakCellDerivC c 0 (fun z => U (s, z) i) (fun z => Uq (s, z) i) ∧
        IIIa.HasWeakCellDerivC c 1 (fun z => U (s, z) i) (fun z => Uη (s, z) i)) ∧
      IntegrableOn (fun z => profCurl Uq Uη (s, z)) (B0579.cell c) volume ∧
      ∫ z in B0579.cell c, profCurl Uq Uη (s, z) = 0) →
    ∃ g gq gη : CProf,
      StronglyMeasurable g ∧ StronglyMeasurable gq ∧ StronglyMeasurable gη ∧
      QPeriodic c g ∧ HasWeakVec vQ0 dZero g gq ∧ HasWeakVec vEta dZero g gη ∧
      IsBodySource tr b0' b0q b0η g ∧
      (∀ s : ℝ, 0 < s →
        sliceH1Norm c g gq gη s ≤ ENNReal.ofReal 2 * sliceH1Norm c U Uq Uη s) ∧
      (∀ s : ℝ, 0 < s →
        ((∀ z, gq (s, z) = 0 ∧ gη (s, z) = 0) ∨
          (∀ᵐ z ∂(volume.restrict (B0579.cell c)),
            profCurl gq gη (s, z) = -profCurl Uq Uη (s, z)))) ∧
      (∀ᵐ s ∂volume, 0 < s →
        ∀ᵐ z ∂(volume.restrict (B0579.cell c)),
          profCurl gq gη (s, z) = -profCurl Uq Uη (s, z))

/-- (N1) Slices of a jointly strongly measurable profile are a strongly measurable path in
`L²(cell; ℝ²)` (real and imaginary parts; `toL2v` is `0` off `L²`). Input of
`Infra.JointMeasurableRep.exists_stronglyMeasurable_rep` for `s ↦ P0re/P0im c (U(s, ·))`. -/
def SliceL2Measurable : Prop :=
  ∀ c : ℝ, 0 < c → ∀ U : CProf, StronglyMeasurable U →
    StronglyMeasurable (fun s : ℝ => IIIa.toL2v c (IIIa.reVec (fun z i => U (s, z) i))) ∧
      StronglyMeasurable (fun s : ℝ => IIIa.toL2v c (IIIa.imVec (fun z i => U (s, z) i)))

/-- (N2) Slice-wise cylinder weak derivatives give the joint `HasWeakVec` on `Coord`
(periodization of coordinate tests into `B0579.IsCylTest`, unfolding `∫_{ℝ²} = ∫_cell` by
`q`-periodicity, Fubini; integrability from `hLoc`-type local `L²` bounds). -/
def SliceWeakToJoint : Prop :=
  ∀ c : ℝ, 0 < c → ∀ (j : Fin 2) (g G : CProf),
    StronglyMeasurable g → StronglyMeasurable G → QPeriodic c g → QPeriodic c G →
    (∀ a b : ℝ, 0 < a → ∫⁻ s in Icc a b,
      (eLpNorm (fun z => g (s, z)) 2 (volume.restrict (B0579.cell c)) +
        eLpNorm (fun z => G (s, z)) 2 (volume.restrict (B0579.cell c))) < ⊤) →
    (∀ᵐ s ∂volume, 0 < s → ∀ i : Fin 2,
      IIIa.HasWeakCellDerivC c j (fun z => g (s, z) i) (fun z => G (s, z) i)) →
    HasWeakVec (![vQ0, vEta] j) dZero g G

/-- (N3) Slice-wise solenoidality and orthogonality to cylinder divergence-free test fields give
`IsBodySource` on `Coord` (same periodization/unfolding/Fubini as (N2)). -/
def SliceBodySourceToJoint : Prop :=
  ∀ c : ℝ, 0 < c → ∀ {ν : ℝ} (tr : B0140.TrainSol ν c) (b0 b0q b0η g : CProf),
    StronglyMeasurable g → AEStronglyMeasurable (flatBv tr b0 b0q b0η) volume →
    QPeriodic c g → QPeriodic c (flatBv tr b0 b0q b0η) →
    (∀ a b : ℝ, 0 < a → ∫⁻ s in Icc a b,
      (eLpNorm (fun z => g (s, z)) 2 (volume.restrict (B0579.cell c)) +
        eLpNorm (fun z => flatBv tr b0 b0q b0η (s, z)) 2
          (volume.restrict (B0579.cell c))) < ⊤) →
    (∀ᵐ s ∂volume, 0 < s → ∀ ψ : B0579.Plane → ℝ, B0579.IsCylTest c ψ →
      ∫ z in B0579.cell c,
        (g (s, z) 0 * (B0579.pd 0 ψ z : ℂ) + g (s, z) 1 * (B0579.pd 1 ψ z : ℂ)) = 0) →
    (∀ᵐ s ∂volume, 0 < s → ∀ Ψ : B0579.Plane → Fin 2 → ℝ, IIIa.IsDivFreeTestField c Ψ →
      ∫ z in B0579.cell c,
        ∑ i : Fin 2, (g (s, z) i + flatBv tr b0 b0q b0η (s, z) i) * (Ψ z i : ℂ) = 0) →
    IsBodySource tr b0 b0q b0η g

/-- (N4) Pointwise form of `Cyl.curl_P0`: `curl P₀ f = curl f` a.e. on the cell, for `f ∈ H¹(C_c)`
(weak curl via `IIIa.p0CommWeakC_proof`, then `Cyl.curl_P0` and the fundamental lemma on the
cell with `B0579.IsCylTest` tests). -/
def P0CurlAe : Prop :=
  ∀ c : ℝ, 0 < c → ∀ (f : B0579.Plane → Fin 2 → ℂ) (g : Fin 2 → B0579.Plane → Fin 2 → ℂ),
    MemLp (IIIa.reVec f) 2 (UnforcedLeray.Cyl.cellμ c) →
    MemLp (IIIa.imVec f) 2 (UnforcedLeray.Cyl.cellμ c) →
    (∀ j, MemLp (IIIa.reVec (g j)) 2 (UnforcedLeray.Cyl.cellμ c)) →
    (∀ j, MemLp (IIIa.imVec (g j)) 2 (UnforcedLeray.Cyl.cellμ c)) →
    (∀ i j, IIIa.HasWeakCellDerivC c j (fun x => f x i) (fun x => g j x i)) →
    (fun x => IIIa.P0C c (g 0) x 1 - IIIa.P0C c (g 1) x 0)
      =ᵐ[volume.restrict (B0579.cell c)] (fun x => g 0 x 1 - g 1 x 0)

end UnforcedLeray.Short.IIb.P0SliceLiftH1Needed

end
