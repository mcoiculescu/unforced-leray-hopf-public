import UnforcedLeray.Short.PartI.Tasks.DilationUniformComplement

/-!
# `PartI:S18` decomposed: `seedDilation_continuous`

Source `the November 2 reference manuscript`
lines 946-953: the seed projection `P` is a finite-rank operator built from Gaussian-class
vectors and functionals, so `a ↦ J_a P J_a⁻¹` is norm continuous (dominated convergence).

Leaves: `DilX0StrongCont` (`a ↦ J_a f` continuous in `X0`), `DilX0DualCont`
(`a ↦ ℓ ∘ J_{1/a}` continuous in the dual norm; `X0` is a Hilbert space, so the adjoint group is
strongly continuous as well), `SeedProjFiniteRank` (`P` has the finite-rank form).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ComplexConjugate ContDiff Topology

namespace UnforcedLeray.Short.PartI

/-- **Leaf 1 (strong continuity of the dilations)** (source 946-953): `a ↦ J_a f` is continuous
`(0,∞) → X0` for each `f` (dominated convergence for the weighted `L²` dilation). -/
def DilX0StrongCont : Prop :=
  ∀ (M : ℝ) (hM : 1 < M) (f : Planar.X0 hM),
    Continuous (fun a : Set.Ioi (0 : ℝ) => (Planar.dilX0 hM a.2 f : Planar.X0 hM))

/-- **Leaf 2 (dual norm continuity)** (source 946-953): for a bounded functional `ℓ` on `X0`,
`a ↦ ℓ ∘ J_{1/a}` is norm continuous `(0,∞) → X0*`.  (Riesz: `ℓ = ⟨·, v⟩`, so
`ℓ ∘ J_{1/a} = ⟨·, J_{1/a}^* v⟩`; the adjoint group on the Hilbert space `X0` is strongly
continuous, e.g. by the explicit weighted-`L²` dilation formula and dominated convergence.) -/
def DilX0DualCont : Prop :=
  ∀ (M : ℝ) (hM : 1 < M) (ℓ : Planar.X0 hM →L[ℂ] ℂ),
    Continuous (fun a : Set.Ioi (0 : ℝ) =>
      ℓ.comp (Planar.dilX0 hM (inv_pos.2 a.2) : Planar.X0 hM →L[ℂ] Planar.X0 hM))

/-- **Leaf 3 (finite rank)** (source 946-953): the projection `P` of the growing pair
(`seedProjFun`) on `X0` is `∑ᵢ φᵢ ⊗ uᵢ` with `uᵢ ∈ X0` and `φᵢ ∈ X0*` (`P f = ℓ₂(f₂) q + ℓ_m(f_{-2}) q̄`;
`growingProj`, `growingProjW_rankOne_apply`). -/
def SeedProjFiniteRank : Prop :=
  ∀ (lam : ℂ) (h : ℝ → ℂ) (hh : MemLp h 2 B0010.xGMeasure) (ℓ : B0010.XG →L[ℂ] ℂ),
    IsSeedXG lam (hh.toLp h) ℓ → ∀ (M : ℝ) (hM : 1 < M),
      ∃ P : Planar.X0 hM →L[ℂ] Planar.X0 hM,
        (∀ f : Planar.X0 hM, ⇑((P f : Planar.X0 hM) : Planar.L2w M) =ᵐ[volume]
          fun y => seedProjFun h (⇑((f : Planar.X0 hM) : Planar.L2w M)) y) ∧
        ∃ (u : Fin 2 → Planar.X0 hM) (φ : Fin 2 → (Planar.X0 hM →L[ℂ] ℂ)),
          P = ∑ i, (φ i).smulRight (u i)

theorem seedDilation_continuous_of (h1 : DilX0StrongCont) (h2 : DilX0DualCont)
    (h3 : SeedProjFiniteRank) :
    ∀ (lam : ℂ) (h : ℝ → ℂ) (hh : MemLp h 2 B0010.xGMeasure) (ℓ : B0010.XG →L[ℂ] ℂ),
      IsSeedXG lam (hh.toLp h) ℓ → ∀ (M : ℝ) (hM : 1 < M) (A : ℝ), 1 ≤ A →
      ∃ P : Planar.X0 hM →L[ℂ] Planar.X0 hM,
        (∀ f : Planar.X0 hM, ⇑((P f : Planar.X0 hM) : Planar.L2w M) =ᵐ[volume]
          fun y => seedProjFun h (⇑((f : Planar.X0 hM) : Planar.L2w M)) y) ∧
        Continuous (fun a : Set.Icc (1 : ℝ) A =>
          Planar.dilX0 hM (lt_of_lt_of_le one_pos a.2.1) ∘L P ∘L
            Planar.dilX0 hM (inv_pos.2 (lt_of_lt_of_le one_pos a.2.1))) := by
  intro lam h hh ℓ hs M hM A hA
  obtain ⟨P, hP, u, φ, hPe⟩ := h3 lam h hh ℓ hs M hM
  refine ⟨P, hP, ?_⟩
  let ι : Set.Icc (1 : ℝ) A → Set.Ioi (0 : ℝ) := fun a => ⟨a.1, lt_of_lt_of_le one_pos a.2.1⟩
  have hι : Continuous ι := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val
  have hterm : ∀ a : Set.Icc (1 : ℝ) A,
      Planar.dilX0 hM (lt_of_lt_of_le one_pos a.2.1) ∘L P ∘L
          Planar.dilX0 hM (inv_pos.2 (lt_of_lt_of_le one_pos a.2.1)) =
        ∑ i, ((φ i).comp (Planar.dilX0 hM (inv_pos.2 (ι a).2))).smulRight
          (Planar.dilX0 hM (ι a).2 (u i)) := by
    intro a
    ext1 f
    rw [hPe]
    simp only [ContinuousLinearMap.comp_apply, sum_apply,
      ContinuousLinearMap.smulRight_apply, map_sum, map_smul, ι]
  refine (continuous_congr hterm).2 ?_
  refine continuous_finsetSum _ fun i _ => ?_
  have hu : Continuous (fun a : Set.Icc (1 : ℝ) A => Planar.dilX0 hM (ι a).2 (u i)) :=
    (h1 M hM (u i)).comp hι
  have hφ : Continuous (fun a : Set.Icc (1 : ℝ) A =>
      (φ i).comp (Planar.dilX0 hM (inv_pos.2 (ι a).2))) :=
    (h2 M hM (φ i)).comp hι
  have hb := (isBoundedBilinearMap_smulRight (𝕜 := ℂ) (E := Planar.X0 hM)
    (F := Planar.X0 hM)).continuous
  exact hb.comp (hφ.prodMk hu)

end UnforcedLeray.Short.PartI
