import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F5_2_2

/-!
# `PartII-b:F5/2/2/2` (`FlatBvSliceGoodAe`): statement gap and needed inputs (statements only)

Source: SP lines 2213-2239 (Hölder `1/2 = 3/22 + 4/11` with the train in `L^{22/3}`, SP 2228-2233).

**Gap.** Clauses `sliceH1Norm c U Uq Uη s < ⊤` and `sliceXmNorm c m (profCurl Uq Uη) s < ⊤`
(a.e. `s > 0`) need the weighted train jet norm `trainSliceNorm22_3 c m tr s < ⊤`: `U` contains
`v·b0q` with `b0q(s, ·) ∈ L^{11/4}(cell)` only (the cell has infinite measure), so `v(s, ·)` must be
in `L^{22/3}` (weighted by `⟨z⟩^{m}` for `X_m`). The only bounds are `sliceH1Norm_flatBv_le`,
`sliceXmNorm_flatBv_curl_le` (factor `trainSliceNorm22_3`), and the train bound is proved only under
`BgRegime` (`IsBUCTrain` + Part I tails, `trainWeightedLp22over3_proof`). Here `tr` is an arbitrary
`B0140.TrainSol ν c` (any `ν`), whose fields give no decay or boundedness in `η`. The parent
`CylBodySourceProjection` has the same gap (arbitrary `p : Params`, no `BgRegime`).

**Fix.** Add `hTr` (as in `FlatBvSliceGoodAeTr`); supply it in the parent from a local train bound
(`TrainWeightedLp22over3Loc`, same proof as `trainWeightedLp22over3_proof`: its `ν₀` comes from
`trainStreamVelocityPressureTails_uncond` and does not depend on `Σ`; `polyPS` is bounded on
`[a, b]`). Proof of `FlatBvSliceGoodAeTr` from the sub-statements below: finiteness from
`sliceH1Norm_flatBv_le`, `sliceXmNorm_flatBv_curl_le`, `hTr`, and `sLpNorm_sliceLpNorm_le_hNorm`
(+ `sLpNorm_sqrtS_sliceLpNorm_le`, `sLpNorm_mulS_sliceLpNorm_le`); weak derivatives from
`JointWeakToSlice` (periodicity of `U, Uq, Uη` from `InHr.periodic` and `IsTrain.periodic_v`);
integrability from `IntegrableOnCellOfXm`; zero circulation from `ZeroCirculationOfWeak` with
`u0 = U_0, u1 = U_1`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal

namespace UnforcedLeray.Short.IIb.FlatBvSliceGoodAeNeeded

open UnforcedLeray.Short.IIb
open UnforcedLeray.Cons.C03.Concrete

/-- `FlatBvSliceGoodAe` with the added train hypothesis `hTr`. -/
def FlatBvSliceGoodAeTr : Prop :=
  ∀ (m : ℝ), 8 < m → ∀ {ν c : ℝ} (tr : B0140.TrainSol ν c), 0 < c →
  (∀ᵐ s ∂volume, 0 < s → trainSliceNorm22_3 c m tr s < ⊤) →
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
    HasWeakVec vQ0 dZero (flatBv tr b0' b0q b0η)
      (flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0)) →
    HasWeakVec vEta dZero (flatBv tr b0' b0q b0η)
      (flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1)) →
    let U := flatBv tr b0' b0q b0η
    let Uq := flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0)
    let Uη := flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1)
    ∀ᵐ s ∂volume, 0 < s →
      sliceH1Norm c U Uq Uη s < ⊤ ∧
      sliceXmNorm c m (profCurl Uq Uη) s < ⊤ ∧
      (∀ i : Fin 2,
        IIIa.HasWeakCellDerivC c 0 (fun z => U (s, z) i) (fun z => Uq (s, z) i) ∧
        IIIa.HasWeakCellDerivC c 1 (fun z => U (s, z) i) (fun z => Uη (s, z) i)) ∧
      IntegrableOn (fun z => profCurl Uq Uη (s, z)) (B0579.cell c) volume ∧
      ∫ z in B0579.cell c, profCurl Uq Uη (s, z) = 0

/-- Local-in-age train bound on all of `(0, ∞)` (supplies `hTr` and, with
`sliceH1Norm_flatBv_le`, the `hLoc` of `P0SliceLiftH1Loc`). -/
def TrainWeightedLp22over3Loc : Prop :=
  ∀ m : ℝ, 8 < m → ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ →
    ∀ a b : ℝ, 0 < a → ∃ C : ℝ, ∀ s ∈ Icc a b,
      trainSliceNorm22_3 p.c m p.train s ≤ ENNReal.ofReal C

/-- (S1) Fubini disintegration of a joint weak derivative into cylinder weak derivatives on a.e.
slice (tests `θ(s) χ(q) ψ(q, η)` with `∑ₖ χ(q + k c) = 1`, unfolding by `q`-periodicity, the
fundamental lemma in `s`, and a countable `H¹(cell)`-dense family of `B0579.IsCylTest`). -/
def JointWeakToSlice : Prop :=
  ∀ c : ℝ, 0 < c → ∀ (j : Fin 2) (U G : CProf),
    StronglyMeasurable U → StronglyMeasurable G → QPeriodic c U → QPeriodic c G →
    HasWeakVec (![vQ0, vEta] j) dZero U G →
    ∀ᵐ s ∂volume, 0 < s →
      MemLp (fun z => U (s, z)) 2 (volume.restrict (B0579.cell c)) →
      MemLp (fun z => G (s, z)) 2 (volume.restrict (B0579.cell c)) →
      ∀ i : Fin 2, IIIa.HasWeakCellDerivC c j (fun z => U (s, z) i) (fun z => G (s, z) i)

/-- (S2) `X_m ⊂ L¹(cell)` for `m > 1` (Cauchy-Schwarz with `∫_cell ⟨z⟩^{-2m} < ∞`). -/
def IntegrableOnCellOfXm : Prop :=
  ∀ c m : ℝ, 1 < m → ∀ w : B0579.Plane → ℂ,
    AEStronglyMeasurable w (volume.restrict (B0579.cell c)) →
    eLpNorm w 2 (B0579.cellMeasure c m) < ⊤ → IntegrableOn w (B0579.cell c)

/-- (S3) Zero cell circulation of `∂_q u₁ - ∂_η u₀` (tests `χ(η / R)`, `R → ∞`; `u₀ ∈ L²(cell)`). -/
def ZeroCirculationOfWeak : Prop :=
  ∀ c : ℝ, 0 < c → ∀ (u0 u1 a b : B0579.Plane → ℂ),
    MemLp u0 2 (volume.restrict (B0579.cell c)) →
    IIIa.HasWeakCellDerivC c 0 u1 a → IIIa.HasWeakCellDerivC c 1 u0 b →
    IntegrableOn (fun z => a z - b z) (B0579.cell c) →
    ∫ z in B0579.cell c, (a z - b z) = 0

end UnforcedLeray.Short.IIb.FlatBvSliceGoodAeNeeded

end
