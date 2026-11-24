import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_4.KcJointMeasurable

/-!
# `KcGradient` from three source facts (decomposition of `PartIII-b:C/flatset/col/4/3`)

Source of record `the November 2 reference manuscript`: 3426-3430 (energy class:
weak gradient of `K_cξ` in `L²`), 3236-3240 (`K_c = ∇^⊥Δ⁻¹`).

The gradient of `K_c(Re ξ)` is the pair of real `L²(cell)` fields `kcGQ ξ = Re ∂_q K_c`,
`kcGE ξ = Re ∂_η K_c` (`B0583.velGradQ`, `B0583.velGradEta`); they are the weak derivatives of
`kcLp ξ` (`MixedEvolution.realBiotSavart_hasWeakDerivs`).  Three leaves:
* `KcGradRep`: a jointly measurable representative of the path `s ↦ (kcGQ (ξ s), kcGE (ξ s))`
  (continuity of both gradient maps in `ξ` by linearity and `norm_velGradQ_le`,
  `norm_velGradEta_le`; then `Infra.JointMeasurableRep.exists_stronglyMeasurable_rep_of_continuousOn`
  exactly as `kcRep` in `KcJointMeasurable.lean`; zero for `s ≤ 0`).
* `KcGradWeak`: the Lp weak derivative identity transported to `HasWeakCellDerivC` for the
  pointwise representatives (`realBiotSavart_hasWeakDerivs`, `kcMer_ae`).
* `KcGradSlice`: the slice bound `∫_cell |K_cξ|²+|∇K_cξ|² ≤ K ‖ξ‖²` (`B0583.norm_velocity_le`,
  `norm_velGradQ_le`, `norm_velGradEta_le`, `norm_reX_le`, `cellVol c = c⁻¹ volume|cell`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (vnorm2 tnorm2 HasWeakCellDerivC)

/-- `Re ∂_q K_c(Re ξ)` in `L²(cell)`. -/
def kcGQ {c m : ℝ} [Fact (1 < m)] [Fact (0 < c)] (ξ : Xmc c m) :=
  UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.realPartVelocityLp
    (UnforcedLeray.B0583.velGradQ c one_le_of_fact (reX ξ.1))

/-- `Re ∂_η K_c(Re ξ)` in `L²(cell)`. -/
def kcGE {c m : ℝ} [Fact (1 < m)] [Fact (0 < c)] (ξ : Xmc c m) :=
  UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.realPartVelocityLp
    (UnforcedLeray.B0583.velGradEta c one_le_of_fact (reX ξ.1) (reX_circ ξ))

/-- The gradient matrix `G i j = ∂_j (K)_i` from its two column fields. -/
def gradC (a b : Merid) : Fin 2 → Fin 2 → ℂ := fun i j => (((![a, b] j) i : ℝ) : ℂ)

/-- **Leaf A** (source 3426-3430): jointly measurable representative of the gradient path. -/
def KcGradRep : Prop :=
  ∀ (c m : ℝ) [Fact (1 < m)] [Fact (0 < c)] (ξ : ℝ → Xmc c m),
    ContinuousOn ξ (Ioi 0) → (∀ s, s ≤ 0 → ξ s = 0) →
      ∃ G0 : ℝ × (ℝ × ℝ) → Merid × Merid, Measurable G0 ∧
        ∀ s : ℝ, 0 < s →
          (fun x => (G0 (s, x)).1) =ᵐ[volume.restrict (B0579.cell c)]
              (kcGQ (ξ s) : ℝ × ℝ → Merid) ∧
            (fun x => (G0 (s, x)).2) =ᵐ[volume.restrict (B0579.cell c)]
              (kcGE (ξ s) : ℝ × ℝ → Merid)

/-- **Leaf B** (source 3236-3240, 3426-3430): the weak cell derivative of `K_cξ` is the pair of
gradient fields, for any pointwise representatives. -/
def KcGradWeak : Prop :=
  ∀ (c m : ℝ) [Fact (1 < m)] [Fact (0 < c)] (ξ : Xmc c m) (G1 G2 : ℝ × ℝ → Merid),
    G1 =ᵐ[volume.restrict (B0579.cell c)] (kcGQ ξ : ℝ × ℝ → Merid) →
    G2 =ᵐ[volume.restrict (B0579.cell c)] (kcGE ξ : ℝ × ℝ → Merid) →
      ∀ i j : Fin 2, HasWeakCellDerivC c j (fun x => ((kcMer ξ x i : ℝ) : ℂ))
        (fun x => gradC (G1 x) (G2 x) i j)

/-- **Leaf C** (source 3426-3430): the slice energy bound for the velocity and its gradient. -/
def KcGradSlice : Prop :=
  ∀ (c m : ℝ) [Fact (1 < m)] [Fact (0 < c)], ∃ K : ℝ, ∀ (ξ : Xmc c m) (G1 G2 : ℝ × ℝ → Merid),
    G1 =ᵐ[volume.restrict (B0579.cell c)] (kcGQ ξ : ℝ × ℝ → Merid) →
    G2 =ᵐ[volume.restrict (B0579.cell c)] (kcGE ξ : ℝ × ℝ → Merid) →
      ∫⁻ x in B0579.cell c, ENNReal.ofReal
        (vnorm2 (fun i => ((kcMer ξ x i : ℝ) : ℂ)) ^ 2 + tnorm2 (gradC (G1 x) (G2 x)) ^ 2) ≤
        ENNReal.ofReal (K * ‖ξ‖ ^ 2)

theorem measurable_gradC {α : Type*} [MeasurableSpace α] {a b : α → Merid}
    (ha : Measurable a) (hb : Measurable b) (i j : Fin 2) :
    Measurable fun p => gradC (a p) (b p) i j := by
  have h1 : Measurable fun p => ((a p) i : ℝ) :=
    (EuclideanSpace.proj i : Merid →L[ℝ] ℝ).continuous.measurable.comp ha
  have h2 : Measurable fun p => ((b p) i : ℝ) :=
    (EuclideanSpace.proj i : Merid →L[ℝ] ℝ).continuous.measurable.comp hb
  fin_cases j
  · exact Complex.measurable_ofReal.comp h1
  · exact Complex.measurable_ofReal.comp h2

/-- `KcGradient` from the three leaves. -/
theorem kcGradient_of (hA : KcGradRep) (hB : KcGradWeak) (hC : KcGradSlice) : KcGradient := by
  intro c m _ _ ξ hξ h0
  obtain ⟨G0, hG0, hae⟩ := hA c m ξ hξ h0
  obtain ⟨K, hK⟩ := hC c m
  refine ⟨fun p i j => gradC (G0 p).1 (G0 p).2 i j, fun i j => ?_, fun s hs i j => ?_, ⟨K, ?_⟩⟩
  · exact measurable_gradC (measurable_fst.comp hG0) (measurable_snd.comp hG0) i j
  · exact hB c m (ξ s) (fun x => (G0 (s, x)).1) (fun x => (G0 (s, x)).2) (hae s hs).1
      (hae s hs).2 i j
  · intro s hs
    exact hK (ξ s) (fun x => (G0 (s, x)).1) (fun x => (G0 (s, x)).2) (hae s hs).1 (hae s hs).2

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
