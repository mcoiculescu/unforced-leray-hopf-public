import UnforcedLeray.Cons.C08PhysicalMode.Slices
import UnforcedLeray.Loc.L01Coefficient.Leibniz
import UnforcedLeray.Analysis.LerayProjection.TranslationGenerator
import UnforcedLeray.Blueprint.Construction.Steps
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Step C8, part 3: the body force `𝔓 div(U⊗w + w⊗U)` is in `𝒴₂`

`paper/main.tex` lines 10900–10903 (`eq:st18-t00633`, blueprint unit B0773): "Set `w = 𝒩_vb`.
By (3.5), `w` and its first gradient are in `Y₂`. Since the fixed actual background has
bounded `U, ∇U`, its body force `𝔓(U·∇w + w·∇U)` is in `Y₂`."

**Statements proved (unconditionally).**
* `lerayDivIntegral_eq_bodyForce` (one phase): for `U` differentiable with `|U|, |DU| ≤ C`
  and `w ∈ H¹` (an `L²` field with three `L²` weak derivatives `G_j`), the stress pairing of
  the cylinder problem satisfies
  `-Σ_j ∫ ⟨(U⊗w + w⊗U)_{·j}, 𝔓∂_jφ⟩ = ⟨𝔓 f, φ⟩` for every vector test `φ`, with the body force
  `f = Σ_j ∂_j(w_jU + U_jw) = Σ_j [(∂_jU)_j w + w_j ∂_jU + U_j G_j + (G_j)_j U]`
  (`bodyForce`). Since `div U = div w = 0` this is `U·∇w + w·∇U`; the simplification is not
  needed, only `f ∈ L²`.
* `exists_bodyForce` (spacetime): on a background with `IsBoundedBackground`, periodic, and
  for `w` in the periodic `H¹` class `IsH1Periodic`, there is a real periodic body force
  `g ∈ 𝒴₂` (`B0005.IsY2`) with
  `weakCoupling U w ψ τ = ⟨𝔓 g(τ), ψ(τ)⟩_{L²}` at almost every phase, for every test `ψ`.

**Proof.** The product rule `∂_j B(U, w) = B(∂_jU, w) + B(U, ∂_jw)` for the bilinear
`B_j(u, v) = v_ju + u_jv` is the compiled weak Leibniz rule (`L01.leibniz`), once the
classical derivative of `U` is shown to be a weak derivative (integration by parts for
differentiable functions, `hasWeak_of_differentiable`, no continuity of `DU` needed). The
compiled commutation `𝔓∂_j = ∂_j𝔓` on `L²` (`Leray.weakDerivative_projection`) and
self-adjointness of `𝔓` move the derivative: `⟨T_{·j}, 𝔓∂_jφ⟩ = ⟨𝔓T_{·j}, ∂_jφ⟩ =
-⟨𝔓∂_jT_{·j}, φ⟩`. In spacetime, the weak gradient of `IsH1Periodic` is periodized
(`Slices.lean`) and `∂_jU` is jointly measurable (`aestronglyMeasurable_partial`).

Status: proved. Theorem A is not proved in Lean.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Cons.C08

open UnforcedLeray.Blueprint UnforcedLeray.SobolevGraph

/-! ## The bilinear column map -/

/-- `B_j(u, v) = v_j u + u_j v`, so that column `j` of `u⊗v + v⊗u` is `B_j(u, v)`. -/
def symCol (j : Fin 3) : Space →L[ℝ] Space →L[ℝ] Space :=
  ContinuousLinearMap.smulRightL ℝ Space Space (EuclideanSpace.proj j) +
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ).smulRight (ContinuousLinearMap.id ℝ Space)

theorem symCol_apply (j : Fin 3) (u v : Space) : symCol j u v = v j • u + u j • v := by
  simp [symCol]

theorem symTensorColumns_eq (u v : SpatialField) (j : Fin 3) :
    symTensorColumns u v j = fun y => symCol j (u y) (v y) := by
  funext y
  rw [symCol_apply]
  rfl

/-! ## `L²` bounds for products with a bounded factor -/

theorem memLp_bilin_bdd {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (B : Space →L[ℝ] Space →L[ℝ] Space) {a f : α → Space}
    (ha : AEStronglyMeasurable a μ) {C : ℝ} (hC : ∀ x, ‖a x‖ ≤ C) (hf : MemLp f 2 μ) :
    MemLp (fun x => B (a x) (f x)) 2 μ := by
  refine hf.of_le_mul (c := ‖B‖ * C) (B.aestronglyMeasurable_comp₂ ha hf.1)
    (Eventually.of_forall fun x => ?_)
  calc ‖B (a x) (f x)‖ ≤ ‖B‖ * ‖a x‖ * ‖f x‖ := B.le_opNorm₂ _ _
    _ ≤ ‖B‖ * C * ‖f x‖ := by gcongr; exact hC x

theorem norm_coordinateVector' (i : Fin 3) : ‖coordinateVector i‖ = 1 := by
  simp [coordinateVector]

theorem norm_fderiv_apply_le {f : SpatialField} {C : ℝ} (hC : ∀ x, ‖fderiv ℝ f x‖ ≤ C)
    (i : Fin 3) (x : Space) : ‖fderiv ℝ f x (coordinateVector i)‖ ≤ C := by
  calc ‖fderiv ℝ f x (coordinateVector i)‖ ≤ ‖fderiv ℝ f x‖ * ‖coordinateVector i‖ :=
        (fderiv ℝ f x).le_opNorm _
    _ = ‖fderiv ℝ f x‖ := by rw [norm_coordinateVector', mul_one]
    _ ≤ C := hC x

/-! ## Weak derivatives of the background -/

/-- A differentiable field with bounded derivative has its classical partial derivatives as
weak derivatives (integration by parts for differentiable functions; `DU` need not be
continuous). -/
theorem hasWeak_of_differentiable {f : SpatialField} (hf : Differentiable ℝ f) {C : ℝ}
    (hC : ∀ x, ‖fderiv ℝ f x‖ ≤ C) (i : Fin 3) :
    HasWeakSpatialDerivative i f (fun x => fderiv ℝ f x (coordinateVector i)) := by
  have hm : AEStronglyMeasurable (fun x => fderiv ℝ f x (coordinateVector i)) volume :=
    (measurable_fderiv_apply_const ℝ f _).aestronglyMeasurable
  have hint : ∀ φ, IsSpatialTest φ →
      Integrable (fun x => φ x • fderiv ℝ f x (coordinateVector i)) := fun φ hφ =>
    (hφ.smooth.continuous.integrable_of_hasCompactSupport hφ.compact).smul_bdd C hm
      (Eventually.of_forall fun x => norm_fderiv_apply_le hC i x)
  refine ⟨fun φ hφ => (hφ.derivative i).integrable_smul hf.continuous, hint, fun φ hφ => ?_⟩
  have hparts := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    ((hφ.derivative i).integrable_smul hf.continuous)
    (hint φ hφ) (hφ.integrable_smul hf.continuous)
    (fun x _ => (hφ.smooth.differentiable (by simp)).differentiableAt)
    (fun x _ => hf.differentiableAt)
  exact neg_eq_iff_eq_neg.mp hparts.symm

/-- A bounded measurable field is locally `L²` in the sense of `L01.LocL2`. -/
theorem locL2_of_bound {a : SpatialField} (ha : AEStronglyMeasurable a volume) {C : ℝ}
    (hC : ∀ x, ‖a x‖ ≤ C) : L01.LocL2 a := fun _ hφ =>
  (memLp_top_of_bound ha C (Eventually.of_forall hC)).smul (hφ.memLp 2)

/-! ## Integration by parts against vector tests -/

/-- `⟨F, ∂_jφ⟩ = -⟨G, φ⟩` for `L²` classes with `∂_jF = G` weakly, and a vector test `φ`
(the one-direction form of `L01.H1_inner_testPartial`). -/
theorem inner_testPartial_of_weak {F G : L2Space} {j : Fin 3}
    (h : HasWeakSpatialDerivative j (F : SpatialField) (G : SpatialField))
    {φ : Space → Space} (hφ : IsVectorTest φ) :
    inner ℝ F (toL2 (testPartial φ j)) = -inner ℝ G (toL2 φ) := by
  have hgraph : (F, G) ∈ derivativeGraph j := (mem_derivativeGraph_iff j _ _).mpr h
  rw [L01.toL2_testPartial_eq_sum hφ j, L01.toL2_vectorTest_eq_sum hφ, inner_sum, inner_sum,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  have h := (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hgraph
    ⟨L01.testComponent φ m, L01.isSpatialTest_testComponent hφ m⟩) (EuclideanSpace.single m 1)
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at h
  change pairing (spatialTestDerivative j (L01.testComponent φ m)) _ _ F +
    pairing (L01.testComponent φ m) _ _ G = 0 at h
  change inner ℝ F (testVector _ _ _) = -inner ℝ G (testVector _ _ _)
  rw [real_inner_comm, real_inner_comm _ G]
  exact eq_neg_of_add_eq_zero_left h

theorem toL2_finsetSum {D : Fin 3 → SpatialField} (hD : ∀ j, MemLp (D j) 2 volume) :
    toL2 (fun x => ∑ j, D j x) = ∑ j, toL2 (D j) := by
  have hs : MemLp (fun x => ∑ j, D j x) 2 volume :=
    memLp_finsetSum Finset.univ (fun j _ => hD j)
  apply Lp.ext
  filter_upwards [coeFn_toL2 hs, L01.coeFn_finsetSum Finset.univ (fun j => toL2 (D j)),
    ae_all_iff.mpr (fun j => coeFn_toL2 (hD j))] with x h1 h2 h3
  rw [h1, h2]
  exact Finset.sum_congr rfl fun j _ => (h3 j).symm

/-! ## The body force at one phase -/

/-- The body force `Σ_j ∂_j(w_jU + U_jw) = Σ_j [B_j(∂_jU, w) + B_j(U, ∂_jw)]`, with the
derivatives `dU j = ∂_jU` and `G j = ∂_jw` supplied. -/
def bodyForce (U : SpatialField) (dU G : Fin 3 → SpatialField) (w : SpatialField) :
    SpatialField :=
  fun x => ∑ j : Fin 3, (symCol j (dU j x) (w x) + symCol j (U x) (G j x))

/-- The classical partial derivatives `∂_jU`. -/
def partials (U : SpatialField) : Fin 3 → SpatialField :=
  fun j x => fderiv ℝ U x (coordinateVector j)

/-- **The body-force identity at one phase** (line 10902). For `U` differentiable with
`|U|, |DU| ≤ C` and `w ∈ L²` with `L²` weak derivatives `G_j`:
`⟨𝔓 div(U⊗w + w⊗U), φ⟩ = -Σ_j ∫⟨(U⊗w + w⊗U)_{·j}, 𝔓∂_jφ⟩ = ⟨𝔓 f, φ⟩`, `f = bodyForce`. -/
theorem lerayDivIntegral_eq_bodyForce {U w : SpatialField} {G : Fin 3 → SpatialField}
    (hU : Differentiable ℝ U) {C : ℝ} (hUb : ∀ x, ‖U x‖ ≤ C) (hdU : ∀ x, ‖fderiv ℝ U x‖ ≤ C)
    (hw : MemLp w 2 volume) (hG : ∀ i, MemLp (G i) 2 volume)
    (hwG : ∀ i, HasWeakSpatialDerivative i w (G i))
    {φ : Space → Space} (hφ : IsVectorTest φ) :
    lerayDivIntegral (symTensorColumns U w) φ =
      inner ℝ (Leray.projection (toL2 (bodyForce U (partials U) G w))) (toL2 φ) := by
  have hUm : AEStronglyMeasurable U volume := hU.continuous.aestronglyMeasurable
  have hdUm : ∀ j, AEStronglyMeasurable (partials U j) volume := fun j =>
    (measurable_fderiv_apply_const ℝ U _).aestronglyMeasurable
  have hdUb : ∀ j x, ‖partials U j x‖ ≤ C := fun j x => norm_fderiv_apply_le hdU j x
  have hcol : ∀ j, MemLp (symTensorColumns U w j) 2 volume := fun j => by
    rw [symTensorColumns_eq]
    exact memLp_bilin_bdd (symCol j) hUm hUb hw
  set D : Fin 3 → SpatialField :=
    fun j x => symCol j (partials U j x) (w x) + symCol j (U x) (G j x) with hDdef
  have hD : ∀ j, MemLp (D j) 2 volume := fun j =>
    (memLp_bilin_bdd (symCol j) (hdUm j) (hdUb j) hw).add
      (memLp_bilin_bdd (symCol j) hUm hUb (hG j))
  have hweak : ∀ j, HasWeakSpatialDerivative j (symTensorColumns U w j) (D j) := by
    intro j
    have hL := L01.leibniz (symCol j) j (hasWeak_of_differentiable hU hdU j)
      (locL2_of_bound hUm hUb) (locL2_of_bound (hdUm j) (hdUb j)) (H1.ofFields w G hw hG hwG)
    simp only [H1.value_ofFields, H1.derivative_ofFields] at hL
    rw [symTensorColumns_eq]
    refine hL.congr ?_ ?_
    · filter_upwards [coeFn_toL2 hw] with x hx
      rw [hx]
    · filter_upwards [coeFn_toL2 hw, coeFn_toL2 (hG j)] with x hx hx'
      rw [hx, hx']
      rfl
  have hP : ∀ j, HasWeakSpatialDerivative j
      (Leray.projection (toL2 (symTensorColumns U w j)) : SpatialField)
      (Leray.projection (toL2 (D j)) : SpatialField) := fun j =>
    Leray.weakDerivative_projection _ _ j
      ((hweak j).congr (coeFn_toL2 (hcol j)).symm (coeFn_toL2 (hD j)).symm)
  have hbf : bodyForce U (partials U) G w = fun x => ∑ j, D j x := rfl
  rw [lerayDivIntegral_eq_lerayDivPairing hcol, lerayDivPairing, hbf, toL2_finsetSum hD,
    map_sum, sum_inner, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Leray.projection_selfadjoint, inner_testPartial_of_weak (hP j) hφ, neg_neg]

/-! ## The body force in spacetime -/

/-- A phase slice of a similarity test is a vector test. -/
theorem isVectorTest_slice {ψ : SpaceTime → Space} (hψ : IsSimilarityTest ψ) (τ : ℝ) :
    IsVectorTest (slice ψ τ) where
  smooth := hψ.smooth.comp (contDiff_const.prodMk contDiff_id)
  compact := hψ.compact.comp_isClosedEmbedding
    ⟨isEmbedding_prodMkRight τ, (isClosedMap_prodMk_left τ).isClosed_range⟩

/-- The spacetime body force on a background `U`, for `w` with weak gradient `G`. -/
def spacetimeForce (U w : ℝ → SpatialField) (G : Fin 3 → ℝ → SpatialField) :
    ℝ → SpatialField :=
  fun τ => bodyForce (U τ) (partials (U τ)) (fun j => G j τ) (w τ)

/-- **The body force is in `𝒴₂`** (lines 10900–10903, unit B0773). On a periodic background
with `IsBoundedBackground` and for `w` in the periodic `H¹` class, there is a real
`𝒯`-periodic `g ∈ 𝒴₂` with `⟨𝔓 div(U⊗w + w⊗U)(τ), ψ(τ)⟩ = ⟨𝔓 g(τ), ψ(τ)⟩` at almost every
phase, for every similarity test `ψ`, the left side in the Lebesgue form `weakCoupling` of the
cylinder problem. At those phases `w(τ) ∈ L²` as well. -/
theorem exists_bodyForce {P : ℝ} (hP : 0 < P) {U w : ℝ → SpatialField}
    (hU : IsBoundedBackground U) (hUper : Function.Periodic U P) (hw : IsH1Periodic P w) :
    ∃ g : ℝ → SpatialField, B0005.IsY2 P g ∧
      ∀ᵐ τ, MemLp (w τ) 2 volume ∧ ∀ ψ, IsSimilarityTest ψ →
        weakCoupling U w ψ τ =
          inner ℝ (Leray.projection (toL2 (g τ))) (toL2 (slice ψ τ)) := by
  obtain ⟨C, hC⟩ := hU.bounded
  obtain ⟨G, hG⟩ := hw.gradient
  set Gp : Fin 3 → ℝ → SpatialField := fun i => periodize hP (G i) with hGp
  have hGper : ∀ i, Function.Periodic (Gp i) P := fun i => periodize_periodic (G i)
  have hGm : ∀ i, AEStronglyMeasurable (fun z : SpaceTime => Gp i z.1 z.2) volume := fun i =>
    aestronglyMeasurable_periodize (hG i).1
  have hGL : ∀ i, MemLp (fun z : SpaceTime => Gp i z.1 z.2) 2
      (volume.restrict (periodSlab P)) := fun i => memLp_periodize (hG i).2.1
  have hGw : ∀ i, ∀ᵐ τ, HasWeakSpatialDerivative i (w τ) (Gp i τ) := fun i =>
    ae_periodize (q := fun τ v => HasWeakSpatialDerivative i (w τ) v)
      (fun τ v => by rw [hw.value.periodic τ]) (hG i).2.2
  have hwm : AEStronglyMeasurable (fun z : SpaceTime => w z.1 z.2) volume := hw.value.measurable
  have hUm : AEStronglyMeasurable (fun z : SpaceTime => U z.1 z.2) volume := hU.measurable
  have hdUm : ∀ j, AEStronglyMeasurable (fun z : SpaceTime => partials (U z.1) j z.2) volume :=
    fun j => aestronglyMeasurable_partial hU.measurable hU.differentiable j
  have hUb : ∀ z : SpaceTime, ‖U z.1 z.2‖ ≤ C := fun z => (hC z.1 z.2).1
  have hdUb : ∀ j, ∀ z : SpaceTime, ‖partials (U z.1) j z.2‖ ≤ C := fun j z =>
    norm_fderiv_apply_le (fun x => (hC z.1 x).2) j z.2
  refine ⟨spacetimeForce U w Gp, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro τ
    simp only [spacetimeForce, hUper τ, hw.value.periodic τ, hGper _ τ]
  · show AEStronglyMeasurable (fun z : SpaceTime => ∑ j : Fin 3,
      (symCol j (partials (U z.1) j z.2) (w z.1 z.2) + symCol j (U z.1 z.2) (Gp j z.1 z.2))) volume
    refine Finset.aestronglyMeasurable_fun_sum Finset.univ fun j _ => ?_
    exact ((symCol j).aestronglyMeasurable_comp₂ (hdUm j) hwm).add
      ((symCol j).aestronglyMeasurable_comp₂ hUm (hGm j))
  · show MemLp (fun z : SpaceTime => ∑ j : Fin 3,
      (symCol j (partials (U z.1) j z.2) (w z.1 z.2) + symCol j (U z.1 z.2) (Gp j z.1 z.2))) 2
      (volume.restrict (periodSlab P))
    refine memLp_finsetSum Finset.univ fun j _ => ?_
    exact (memLp_bilin_bdd (symCol j) (hdUm j).restrict (hdUb j) hw.value.memL2).add
      (memLp_bilin_bdd (symCol j) hUm.restrict hUb (hGL j))
  · have hwL := ae_memLp_slice hP hw.value.periodic hw.value.memL2
    have hGL' : ∀ i, ∀ᵐ τ, MemLp (Gp i τ) 2 volume := fun i =>
      ae_memLp_slice hP (hGper i) (hGL i)
    filter_upwards [hwL, ae_all_iff.mpr hGL', ae_all_iff.mpr hGw] with τ hτw hτG hτGw
    refine ⟨hτw, fun ψ hψ => ?_⟩
    exact lerayDivIntegral_eq_bodyForce (hU.differentiable τ) (fun x => (hC τ x).1)
      (fun x => (hC τ x).2) hτw hτG hτGw
      (isVectorTest_slice hψ τ)

end UnforcedLeray.Cons.C08
