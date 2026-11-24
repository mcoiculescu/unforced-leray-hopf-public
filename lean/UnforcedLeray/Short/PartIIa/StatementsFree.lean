import UnforcedLeray.Units.B0411
import UnforcedLeray.Units.B0414.PhaseOrthogonal
import UnforcedLeray.Units.B0428
import UnforcedLeray.Units.B0431
import UnforcedLeray.Units.B0447
import UnforcedLeray.Lib.FreeStressCouplings.FreeStress28Y2
import UnforcedLeray.Lib.PhaseSpace.ExtendedTest

/-!
# Part II-a, module `free-foundation.tex`: statements

Source of record: `the November 2 reference manuscript`, lines 1339-1633.

* `Y_r = L^r((ℝ/Pℤ) × ℝ³)` with normalised phase measure is `PhaseSpace.Yq P r` (draft
  `Lib/PhaseSpace/Test.lean`); `D_r = {w ∈ Y_r : νΔw, 𝒯w ∈ Y_r}` (maximal distributional graph,
  lines 1343-1349) is `B0411.D P ν r` with `nuLapD`, `T0D`, `L0D`, `graphNormD`
  (`‖w‖_{D_r} = ‖w‖ + ‖νΔw‖ + ‖𝒯w‖`); `L = 𝒯 - νΔ - 1/2` is `B0411.L0D`; Cartesian Leray
  projection on `Y_r` is `RieszLp.lerayY` (draft `Lib/LerayC/Phase.lean`).
* `∇w ∈ Y_r` is expressed by a triple `g` with `HasPhaseOp (-dy j) w (g j)` (the distribution
  `∂_j w = g_j`), `‖∇w‖` is `∑_j ‖g_j‖` (equivalent to the Frobenius norm up to a
  dimensional constant, absorbed in `C_r`).
* The half-drift weight `C = 1 + |B|` (`B = 𝒯 - 3/4`) is `FreeStress.phaseC0 P`
  (`Lib/FreeStressCouplings`), with `HasPow (1/2)` meaning `C^{1/2}`.
* Tensors of `Y_2(Sym_3)` are triples of rows in `Y_2` (`PiLp 2`, Frobenius norm), cut out by
  the symmetry constraint (`symY2`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- `γ_r = (3/r - 1)/2` (line 1351); `a_r = Re μ + γ_r`. -/
def gammaR (r : ℝ≥0∞) : ℝ := (3 / r.toReal - 1) / 2

/-- The operator `μ + L : D_r → Y_r`, `L = 𝒯 - νΔ - 1/2` (lines 1346, 1353). -/
def bodyOp (P ν : ℝ) [Fact (0 < P)] (r : ℝ≥0∞) [Fact (1 ≤ r)] (μ : ℂ) :
    D P ν r →ₗ[ℂ] Yq P r :=
  μ • (D P ν r).subtype + L0L

/-- `HasGrad w g`: the distributional gradient of `w ∈ Y_r` is `g` (`∂_j w = g_j ∈ Y_r`). -/
def HasGrad {P : ℝ} [Fact (0 < P)] {r : ℝ≥0∞} [Fact (1 ≤ r)] (w : Yq P r)
    (g : Fin 3 → Yq P r) : Prop :=
  ∀ j, HasPhaseOp (fun Φ => -dy j Φ) w (g j)

/-! ### Lemma `bg:common-body-graph` (lines 1351-1362) -/

/-- **The graph bound (`bg:body-graph`)**: for `1 < r < 3`, `a_r = Re μ + γ_r > 0`, `ν > 0`,
`0 < P ≤ 1`, every `w ∈ D_r` has a gradient in `Y_r` and
`‖w‖_{D_r} + √ν ‖∇w‖_{Y_r} ≤ C_r [1 + (1+|μ|)/a_r] ‖(μ+L)w‖_{Y_r}`, with `C_r` independent of
`P, ν, μ`. -/
def CommonBodyGraphBound : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], 1 < r → r < 3 → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ ν : ℝ, 0 < ν → ∀ μ : ℂ, 0 < μ.re + gammaR r →
      ∀ w : D P ν r, ∃ g : Fin 3 → Yq P r, HasGrad (w : Yq P r) g ∧
        graphNormD w + Real.sqrt ν * ∑ j, ‖g j‖ ≤
          C * (1 + (1 + ‖μ‖) / (μ.re + gammaR r)) * ‖bodyOp P ν r μ w‖

/-- **Existence for the body equation** (lines 1363-1368 and 1394-1402 of the proof, the
distributional inverse `ℛ_μ f(τ) = ∫_0^∞ e^{-μt} S(t) f(τ-t) dt` with
`S(t)h(y) = e^{t/2}[e^{ν(e^t-1)Δ}h](e^{t/2}y)`): `μ + L : D_r → Y_r` is surjective. -/
def CommonBodySurjective : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], 1 < r → r < 3 →
    ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ ν : ℝ, 0 < ν → ∀ μ : ℂ, 0 < μ.re + gammaR r →
      Function.Surjective (bodyOp P ν r μ)

/-- **Bijectivity of `μ + L : D_r → Y_r`** (lines 1353-1355). -/
def CommonBodyBijective : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], 1 < r → r < 3 →
    ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ ν : ℝ, 0 < ν → ∀ μ : ℂ, 0 < μ.re + gammaR r →
      Function.Bijective (bodyOp P ν r μ)

/-- **Projected inverse** (lines 1358-1359): the solution of `(μ+L)w = 𝐏f` (Cartesian Leray
projection applied to `f`) exists and is solenoidal. -/
def CommonBodyProjected : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)] (h1 : 1 < r) (h3 : r < 3),
    ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ ν : ℝ, 0 < ν → ∀ μ : ℂ, 0 < μ.re + gammaR r →
      ∀ f : Yq P r, ∃ w : D P ν r, (w : Yq P r) ∈ Ysigma P r ∧
        bodyOp P ν r μ w = lerayY P r h1 (ne_top_of_lt h3) f

/-- **Maximal distributional domain** (lines 1409-1412, 1393-1400): every distributional `Y_r`
solution `w` of `(μ + L) w = f` with `f ∈ Y_r` lies in `D_r` (the transpose of `μ + L` against
phase tests is `μ + L0T`); together with uniqueness there is no larger hidden null space. -/
def CommonBodyMaximalDomain : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], 1 < r → r < 3 →
    ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ ν : ℝ, 0 < ν → ∀ μ : ℂ, 0 < μ.re + gammaR r →
      ∀ w f : Yq P r, HasPhaseOp (fun Φ => μ • Φ + L0T ν Φ) w f → w ∈ D P ν r

/-- **The adjoint at `r = 2`** (lines 1359-1361, 1426-1440): for `a_2 = Re μ + 1/4 > 0` the
adjoint equation `(μ̄ - 𝒯 - νΔ + 1) w = f` (the formal adjoint `L* = -𝒯 - νΔ + 1`, taken in
distributions: its transpose against phase tests is `μ̄ + L`) has a solution `w ∈ Y_2`, and
every distributional solution lies in the same maximal graph `D_2` with the same bound,
independently of `P`. -/
def CommonBodyAdjoint : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ ν : ℝ, 0 < ν → ∀ μ : ℂ, 0 < μ.re + 1 / 4 →
      ∀ f : Yq P 2, (∃ w : Yq P 2, HasPhaseOp (fun Φ => (starRingEnd ℂ) μ • Φ + L0 ν Φ) w f) ∧
        ∀ w : Yq P 2, HasPhaseOp (fun Φ => (starRingEnd ℂ) μ • Φ + L0 ν Φ) w f →
          ∃ hw : w ∈ D P ν 2, ∃ g : Fin 3 → Yq P 2, HasGrad w g ∧
            graphNormD (⟨w, hw⟩ : D P ν 2) + Real.sqrt ν * ∑ j, ‖g j‖ ≤
              C * (1 + (1 + ‖μ‖) / (μ.re + 1 / 4)) * ‖f‖

/-- **Lemma `bg:common-body-graph`** (lines 1351-1362). -/
def CommonBodyGraphLemma : Prop :=
  CommonBodyBijective ∧ CommonBodyGraphBound ∧ CommonBodyMaximalDomain ∧ CommonBodyProjected ∧
    CommonBodyAdjoint

/-- **Holomorphy of the body inverse** (line 1621): `μ ↦ (μ+L)^{-1}𝐏` is holomorphic (operator
norm) on `{Re μ + γ_r > 0}`. -/
def BodyInverseHolomorphic : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)] (h1 : 1 < r) (h3 : r < 3),
    ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ ν : ℝ, 0 < ν →
      ∀ R : ℂ → (Yq P r →L[ℂ] Yq P r),
        (∀ μ : ℂ, 0 < μ.re + gammaR r → ∀ f : Yq P r, ∃ w : D P ν r,
          (w : Yq P r) = R μ f ∧ bodyOp P ν r μ w = lerayY P r h1 (ne_top_of_lt h3) f) →
        DifferentiableOn ℂ R {μ : ℂ | 0 < μ.re + gammaR r}

/-! ### Lemma `bg:graph-embeddings` (lines 1515-1531) -/

/-- **Phase embedding (`bg:phase-embedding`)**: every `w ∈ D_r` has a representative
`W ∈ C(ℝ/Pℤ; L^r)` and
`sup_τ ‖W(τ)‖_r ≤ (1 + 3P/(2r)) ‖w‖_{Y_r} + P ‖𝒯w‖_{Y_r}`. -/
def GraphPhaseEmbedding : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], 1 < r → r ≠ ⊤ →
    ∀ (P : ℝ) [Fact (0 < P)] (ν : ℝ) (w : D P ν r),
      ∃ W : AddCircle P → Lp CVec3 r (volume : Measure Space), Continuous W ∧
        (∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)), W τ = (w : Yq P r) τ) ∧
        ∀ τ, ‖W τ‖ ≤ (1 + 3 * P / (2 * r.toReal)) * ‖(w : Yq P r)‖ + P * ‖T0D w‖

/-- **Supremum embedding (`bg:supremum-embedding`)**: for `r > 5/2`, `ν > 0`, `0 < P ≤ 1`,
`w ∈ D_r` has a representative continuous in `(τ, y)` with
`‖w‖_{L^∞_{τ,y}} ≤ C_r ν^{-3/(2r)} ‖w‖_{D_r}`. -/
def GraphSupEmbedding : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], 5 / 2 < r → r ≠ ⊤ → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ ν : ℝ, 0 < ν → ∀ w : D P ν r,
      ∃ W : AddCircle P × Space → CVec3, Continuous W ∧
        (∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)),
          (fun y => W (τ, y)) =ᵐ[volume] ((w : Yq P r) τ : Lp CVec3 r volume)) ∧
        ∀ (τ : AddCircle P) (y : Space), ‖W (τ, y)‖ ≤
          C * ν ^ (-(3 / (2 * r.toReal))) * graphNormD w

/-- **Lemma `bg:graph-embeddings`** (lines 1515-1531). -/
def GraphEmbeddingsLemma : Prop := GraphPhaseEmbedding ∧ GraphSupEmbedding

/-! ### Tensor forces and Lemma `free:weak-stress` (lines 1533-1633) -/

/-- `Y_2(Sym_3)`-ambient: three rows, each in `Y_2` (`ℂ³`-valued), Frobenius norm. -/
abbrev Y2Sym (P : ℝ) [Fact (0 < P)] := PiLp 2 (fun _ : Fin 3 => Yq P 2)

/-- The functional `T ↦ ⟨φ e_j, T_i⟩ - ⟨φ e_i, T_j⟩` on tensor rows. -/
def symFun (P : ℝ) [Fact (0 < P)] (i j : Fin 3) (φ : ℝ × Space → ℂ) : Y2Sym P →L[ℂ] ℂ :=
  (phasePair P 2 (fun p => φ p • (EuclideanSpace.single j 1 : CVec3))).comp
      (PiLp.proj 2 (fun _ : Fin 3 => Yq P 2) i) -
    (phasePair P 2 (fun p => φ p • (EuclideanSpace.single i 1 : CVec3))).comp
      (PiLp.proj 2 (fun _ : Fin 3 => Yq P 2) j)

/-- Symmetric tensors `T_ij = T_ji` in the distributional sense (against all phase tests). -/
def symY2 (P : ℝ) [Fact (0 < P)] : Submodule ℂ (Y2Sym P) :=
  ⨅ (i : Fin 3) (j : Fin 3) (φ : {φ : ℝ × Space → ℂ // IsPhaseTest P φ}),
    LinearMap.ker (symFun P i j φ.1).toLinearMap

/-- A smooth phase tensor given by its rows `G i`, as an element of `Y_2(Sym_3)`-ambient. -/
def smoothTensor (P : ℝ) [Fact (0 < P)] (G : Fin 3 → ℝ × Space → CVec3) : Y2Sym P :=
  WithLp.toLp 2 fun i => testElem P 2 (G i)

/-- Pointwise symmetry of a smooth tensor given by rows. -/
def IsSymRows (G : Fin 3 → ℝ × Space → CVec3) : Prop := ∀ i j p, G i p j = G j p i

/-- The divergence `(div T)_i = Σ_j ∂_j T_ij` of a smooth tensor given by rows. -/
def tensorDiv (G : Fin 3 → ℝ × Space → CVec3) : ℝ × Space → CVec3 :=
  fun p => WithLp.toLp 2 fun i => ∑ j, dy j (G i) p j

/-- The pairing `⟨∇Φ, T⟩ = Σ_{ij} ∫ ∂_jΦ_i T_ij`. -/
def tensorGradPair (P : ℝ) [Fact (0 < P)] (Φ : ℝ × Space → CVec3) (T : Y2Sym P) : ℂ :=
  ∑ i, phasePair P 2 (fun p => (WithLp.toLp 2 fun j => dy j Φ p i : CVec3)) (T i)

/-- **`S_μ = ℛ_μ div` on smooth tensors** (line 1537, "extends uniquely"): `S` is a bounded
linear map on `Y_2(Sym_3)` which on every smooth symmetric phase tensor `G` returns the
solution `w ∈ D_2` of `(μ+L)w = 𝐏 div G` (Cartesian Leray projection of the divergence). -/
def IsWeakStressInverse (P ν : ℝ) [Fact (0 < P)] (μ : ℂ) (S : symY2 P →L[ℂ] Yq P 2) : Prop :=
  ∀ (T : symY2 P) (G : Fin 3 → ℝ × Space → CVec3), (∀ i, IsPhaseTest P (G i)) → IsSymRows G →
    smoothTensor P G = (T : Y2Sym P) →
      ∃ w : D P ν 2, (w : Yq P 2) = S T ∧
        bodyOp P ν 2 μ w = lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top
          (testElem P 2 (tensorDiv G))

/-- Smooth symmetric tensors are dense in `Y_2(Sym_3)` ("completion from smooth tensors"). -/
def SmoothTensorsDense : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)], Dense {T : symY2 P | ∃ G : Fin 3 → ℝ × Space → CVec3,
    (∀ i, IsPhaseTest P (G i)) ∧ IsSymRows G ∧ smoothTensor P G = (T : Y2Sym P)}

/-- **Existence and energy bounds (`free:stress-energy`)** (lines 1537-1544): for
`a = Re μ + 1/4 > 0` there is a bounded extension `S_μ` of `ℛ_μ div` with
`‖S_μ T‖ ≤ ‖T‖/(2√(aν))` and `‖∇ S_μ T‖ ≤ ν⁻¹ ‖T‖`. -/
def WeakStressExists : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ ν : ℝ, 0 < ν → ∀ μ : ℂ, 0 < μ.re + 1 / 4 →
    ∃ S : symY2 P →L[ℂ] Yq P 2, IsWeakStressInverse P ν μ S ∧ ∀ T : symY2 P,
      ‖S T‖ ≤ ‖(T : Y2Sym P)‖ / (2 * Real.sqrt ((μ.re + 1 / 4) * ν)) ∧
      ∃ g : Fin 3 → Yq P 2, HasGrad (S T) g ∧
        Real.sqrt (∑ j, ‖g j‖ ^ 2) ≤ ν⁻¹ * ‖(T : Y2Sym P)‖

/-- **Half-drift bound (`free:half-drift`)** (lines 1545-1547): uniformly on compact subsets
of `Re μ > -1/4`, `‖(1 + |B|)^{1/2} S_μ T‖_{Y_2} ≤ C_μ ν^{-1/2} ‖T‖_{Y_2}`, `C_μ` independent of
`P ≤ 1`, `ν`. -/
def WeakStressHalfDrift : Prop :=
  ∀ K : Set ℂ, IsCompact K → (∀ μ ∈ K, 0 < μ.re + 1 / 4) → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ ν : ℝ, 0 < ν → ∀ μ ∈ K,
      ∀ S : symY2 P →L[ℂ] Yq P 2, IsWeakStressInverse P ν μ S → ∀ T : symY2 P,
        ∃ w : Yq P 2, (FreeStress.phaseC0 P).HasPow (1 / 2) (S T) w ∧
          ‖w‖ ≤ C * ν ^ (-(1 / 2 : ℝ)) * ‖(T : Y2Sym P)‖

/-- **Distributional uniqueness** (lines 1548-1549): a solenoidal `w ∈ Y_2` solving the weak
equation `⟨(μ + L^t)Φ, w⟩ = -⟨∇Φ, T⟩` for every solenoidal phase test `Φ` equals `S_μ T`
(no a priori graph, rough tensors `T ∈ Y_2(Sym_3)` allowed). -/
def WeakStressUnique : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ ν : ℝ, 0 < ν → ∀ μ : ℂ, 0 < μ.re + 1 / 4 →
    ∀ S : symY2 P →L[ℂ] Yq P 2, IsWeakStressInverse P ν μ S → ∀ (T : symY2 P) (w : Yq P 2),
      IsPhaseSolenoidal w →
      (∀ Φ : ℝ × Space → CVec3, IsPhaseTest P Φ → (∀ p, ∑ j, dy j Φ p j = 0) →
        phasePair P 2 (μ • Φ + L0T ν Φ) w = -tensorGradPair P Φ (T : Y2Sym P)) →
      w = S T

/-- **Holomorphy of the stress inverse** (lines 1550-1551, 1623-1632): any family
`μ ↦ S_μ` of weak stress inverses is operator-norm holomorphic on `Re μ > -1/4`. -/
def WeakStressHolomorphic : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ ν : ℝ, 0 < ν →
    ∀ S : ℂ → (symY2 P →L[ℂ] Yq P 2),
      (∀ μ : ℂ, 0 < μ.re + 1 / 4 → IsWeakStressInverse P ν μ (S μ)) →
        DifferentiableOn ℂ S {μ : ℂ | 0 < μ.re + 1 / 4}

/-- **Lemma `free:weak-stress`** (lines 1533-1633). -/
def WeakStressLemma : Prop :=
  WeakStressExists ∧ SmoothTensorsDense ∧ WeakStressHalfDrift ∧ WeakStressUnique ∧
    WeakStressHolomorphic

/-! ### Numerical consequences (lines 1599-1618) -/

/-- Body gaps: `γ_{11/4} = 1/22` and `γ_{23/8} = 1/46`. -/
def GapValues : Prop := gammaR (11 / 4) = 1 / 22 ∧ gammaR (23 / 8) = 1 / 46

/-- **Product estimate at `r = 11/4`** (lines 1601-1604): for `u, v ∈ D_r`,
`‖𝐏[(u·∇)v]‖_{Y_r} ≤ C ν^{-23/22} ‖u‖_{D_r} ‖v‖_{D_r}`, where `(u·∇)v = Σ_j u_j ∂_j v`
(the product is an element of `Y_r`, by the sup/phase embeddings). -/
def FreeProductEstimate : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)] (h1 : 1 < r) (h3 : r ≠ ⊤), r = 11 / 4 →
    ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ ν : ℝ, 0 < ν → ∀ u v : D P ν r,
      ∀ g : Fin 3 → Yq P r, HasGrad (v : Yq P r) g →
        ∃ f : Yq P r, (∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)),
            ((f τ : Lp CVec3 r volume) : Space → CVec3) =ᵐ[volume] fun y =>
              ∑ j, (((u : Yq P r) τ : Lp CVec3 r volume) y j) •
                ((g j τ : Lp CVec3 r volume) y)) ∧
          ‖lerayY P r h1 h3 f‖ ≤
            C * ν ^ (-(23 / 22 : ℝ)) * graphNormD u * graphNormD v

/-- **Transported stress map** (lines 1627-1632): for unitary lifts `J_v : H → Y_2`,
`J_T : H_T → Y_2`, the stress map is `J_v⁻¹ S_μ J_T`. (Definitional; in the near-field module
it is the operator `S_ε` of `near:compact-free-comparison`.) -/
def TransportedStress {H HT : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup HT] [InnerProductSpace ℂ HT] (P : ℝ) [Fact (0 < P)]
    (Jv : H ≃ₗᵢ[ℂ] Yq P 2) (JT : HT →ₗᵢ[ℂ] symY2 P) (S : symY2 P →L[ℂ] Yq P 2) :
    HT →L[ℂ] H :=
  Jv.symm.toLinearIsometry.toContinuousLinearMap ∘L S ∘L JT.toContinuousLinearMap

end UnforcedLeray.Short.PartIIa
