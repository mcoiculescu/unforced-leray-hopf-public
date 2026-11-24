import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6

/-!
# `PhaseSliceWeakGrad` from a product-test Fubini argument and a countable dense family

Source `the November 2 reference manuscript` lines 1351-1362 (weak `y`-gradient of the
stream potential, tested against phase tests) and 1334-1337 (`Y_r`).

Route.  For `g ∈ C_c^∞(ℝ³)`, `j, i ∈ {1,2,3}` put
`wgFun j i g (t) = ∫ ∂ⱼg · ψᵢ(t, ·) + ∫ g · Dⱼᵢ(t, ·)` (`ψ = bsPot Φ`).

* `FubiniUnfold`: `wgFun` is integrable over one period and `∫₀ᴾ s · wgFun = 0` for every smooth
  `P`-periodic `s` (product phase tests `s(t) g(y) eᵢ`, Fubini);
* `FunctionalPeriodic`: `wgFun` is a.e. `P`-periodic;
* `PhaseFundLemma`: hence `wgFun g = 0` a.e. (fundamental lemma over periodic `s`);
* `SliceLocInt`: a.e. slices of `ψ` and `Dⱼ` are locally integrable;
* `TestDense` and `SliceDetermined`: a countable family `D` dense in `C¹` (uniformly, with common
  support radius) determines the weak relation for all `C_c^∞` tests.

Only the final countable-intersection and vector assembly is proved in this file.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt)
open UnforcedLeray.Short.IIb (IsInYr HasPtwOp)

/-- Hypotheses of `PhaseSliceWeakGrad` for the data `(P, Φ, Dψ)`. -/
def WGHyp (P : ℝ) (Φ : ℝ × Space → CVec3) (Dψ : Fin 3 → ℝ × Space → CVec3) : Prop :=
  0 < P ∧ IsInYr P 2 Φ ∧
    ∀ j : Fin 3, IsInYr P 2 (Dψ j) ∧ HasPtwOp P (fun Θ => -dy j Θ) (bsPot Φ) (Dψ j)

/-- Scalar weak-gradient functional of the phase `t`, component `i`, direction `j`, test `g`:
`∫ ∂ⱼg · (bsPot Φ)ᵢ(t, ·) + ∫ g · (Dψ j)ᵢ(t, ·)`. -/
def wgFun (Φ : ℝ × Space → CVec3) (Dψ : Fin 3 → ℝ × Space → CVec3) (j i : Fin 3)
    (g : Space → ℂ) (t : ℝ) : ℂ :=
  (∫ y : Space, fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ)) * bsPot Φ (t, y) i) +
    ∫ y : Space, g y * Dψ j (t, y) i

/-- The product phase test `(t, y) ↦ s(t) g(y) eᵢ`. -/
def prodTest (s : ℝ → ℂ) (g : Space → ℂ) (i : Fin 3) : ℝ × Space → CVec3 :=
  fun x => (s x.1 * g x.2) • (EuclideanSpace.single i (1 : ℂ) : CVec3)

/-- `C_c^∞` test function. -/
def SmoothCS (g : Space → ℂ) : Prop := ContDiff ℝ ∞ g ∧ HasCompactSupport g

/-- **FubiniUnfold** (source 1351-1362): for the hypotheses of `PhaseSliceWeakGrad`, and a
`C_c^∞` test `g`, `wgFun` is integrable over one period and orthogonal to every smooth `P`-periodic
`s` (the phase test `s(t) g(y) eᵢ` in the relation `HasPtwOp`, with Fubini). -/
def FubiniUnfold : Prop :=
  ∀ (P : ℝ) (Φ : ℝ × Space → CVec3) (Dψ : Fin 3 → ℝ × Space → CVec3), WGHyp P Φ Dψ →
    ∀ g : Space → ℂ, SmoothCS g → ∀ j i : Fin 3,
      IntegrableOn (wgFun Φ Dψ j i g) (Ioc 0 P) volume ∧
      ∀ s : ℝ → ℂ, ContDiff ℝ ∞ s → (∀ t, s (t + P) = s t) →
        ∫ t in Ioc 0 P, s t * wgFun Φ Dψ j i g t = 0

/-- `wgFun` is a.e. `P`-periodic (slices of `bsPot Φ` and `Dψ j` are a.e. periodic). -/
def FunctionalPeriodic : Prop :=
  ∀ (P : ℝ) (Φ : ℝ × Space → CVec3) (Dψ : Fin 3 → ℝ × Space → CVec3), WGHyp P Φ Dψ →
    ∀ (g : Space → ℂ) (j i : Fin 3), ∀ᵐ t : ℝ, wgFun Φ Dψ j i g (t + P) = wgFun Φ Dψ j i g t

/-- Fundamental lemma over smooth periodic multipliers (source 1351-1362). -/
def PhaseFundLemma : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ H : ℝ → ℂ, IntegrableOn H (Ioc 0 P) volume →
    (∀ᵐ t : ℝ, H (t + P) = H t) →
    (∀ s : ℝ → ℂ, ContDiff ℝ ∞ s → (∀ t, s (t + P) = s t) → ∫ t in Ioc 0 P, s t * H t = 0) →
    ∀ᵐ t : ℝ, H t = 0

/-- A.e. phase slices of `bsPot Φ` and `Dψ j` are locally integrable on `ℝ³`. -/
def SliceLocInt : Prop :=
  ∀ (P : ℝ) (Φ : ℝ × Space → CVec3) (Dψ : Fin 3 → ℝ × Space → CVec3), WGHyp P Φ Dψ →
    ∀ᵐ t : ℝ, ∀ R : ℝ, IntegrableOn (fun y : Space => bsPot Φ (t, y)) (closedBall 0 R) volume ∧
      ∀ j : Fin 3, IntegrableOn (fun y : Space => Dψ j (t, y)) (closedBall 0 R) volume

/-- `D` is a countable family of `C_c^∞` functions, dense in `C¹` uniformly with a common support
radius `n` (the same `n` for the approximant as for the target). -/
def TDFam (D : Set (Space → ℂ)) : Prop :=
  D.Countable ∧ (∀ χ ∈ D, SmoothCS χ) ∧
    ∀ (n : ℕ) (φ : Space → ℂ), ContDiff ℝ ∞ φ → (∀ y : Space, (n : ℝ) < ‖y‖ → φ y = 0) →
      ∀ ε : ℝ, 0 < ε → ∃ χ ∈ D, (∀ y : Space, (n : ℝ) < ‖y‖ → χ y = 0) ∧
        (∀ y : Space, ‖φ y - χ y‖ ≤ ε) ∧
        ∀ (j : Fin 3) (y : Space), ‖fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ)) -
          fderiv ℝ χ y (EuclideanSpace.single j (1 : ℝ))‖ ≤ ε

/-- Such a family exists. -/
def TestDense : Prop := ∃ D : Set (Space → ℂ), TDFam D

/-- A family `D` with `TDFam D` determines the weak relation: if `∫ ∂ⱼχ u + ∫ χ E = 0` for `χ ∈ D`
(`u, E` locally integrable) then the same holds for every `C_c^∞` test `φ`. -/
def SliceDetermined : Prop :=
  ∀ D : Set (Space → ℂ), TDFam D → ∀ (u E : Space → ℂ) (j : Fin 3),
    (∀ R : ℝ, IntegrableOn u (closedBall 0 R) volume) →
    (∀ R : ℝ, IntegrableOn E (closedBall 0 R) volume) →
    (∀ χ ∈ D, (∫ y : Space, fderiv ℝ χ y (EuclideanSpace.single j (1 : ℝ)) * u y) +
      ∫ y : Space, χ y * E y = 0) →
    ∀ φ : Space → ℂ, SmoothCS φ →
      (∫ y : Space, fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ)) * u y) +
        ∫ y : Space, φ y * E y = 0

/-- A compactly supported continuous scalar times a locally integrable vector field is
integrable. -/
theorem wg_integrable_smul (c : Space → ℂ) (hc : Continuous c) (hcc : HasCompactSupport c)
    (u : Space → CVec3) (hu : ∀ R : ℝ, IntegrableOn u (closedBall 0 R) volume) :
    Integrable (fun y : Space => c y • u y) volume := by
  obtain ⟨R, hR⟩ := hcc.isCompact.isBounded.subset_closedBall (0 : Space)
  have h1 : IntegrableOn (fun y : Space => c y • u y) (closedBall 0 R) volume :=
    (hu R).continuousOn_smul hc.continuousOn (isCompact_closedBall 0 R)
  refine h1.integrable_of_forall_notMem_eq_zero ?_
  intro y hy
  have : y ∉ tsupport c := fun h => hy (hR h)
  simp [image_eq_zero_of_notMem_tsupport this]

/-- The `i`-th coordinate of a vector-valued integral. -/
theorem wg_integral_apply (f : Space → CVec3) (hf : Integrable f volume) (i : Fin 3) :
    (∫ y : Space, f y) i = ∫ y : Space, f y i := by
  have L : CVec3 →L[ℝ] ℂ := ((EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).restrictScalars ℝ)
  exact (ContinuousLinearMap.integral_comp_comm
    ((EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).restrictScalars ℝ) hf).symm

theorem wg_coord_integrable (f : Space → CVec3) (hf : Integrable f volume) (i : Fin 3) :
    Integrable (fun y : Space => f y i) volume :=
  ContinuousLinearMap.integrable_comp
    ((EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).restrictScalars ℝ) hf

theorem phaseSliceWeakGrad_of (hFU : FubiniUnfold) (hFP : FunctionalPeriodic)
    (hPF : PhaseFundLemma) (hLI : SliceLocInt) (hTD : TestDense) (hDS : SliceDetermined) :
    PhaseSliceWeakGrad := by
  intro P hP Φ hΦ Dψ hD
  have hW : WGHyp P Φ Dψ := ⟨hP, hΦ, hD⟩
  obtain ⟨D, hDf⟩ := hTD
  have hv : ∀ᵐ t : ℝ, ∀ g ∈ D, ∀ j i : Fin 3, wgFun Φ Dψ j i g t = 0 := by
    refine (ae_ball_iff hDf.1 (p := fun t g _ => ∀ j i : Fin 3, wgFun Φ Dψ j i g t = 0)).2 ?_
    intro g hg
    rw [ae_all_iff]; intro j
    rw [ae_all_iff]; intro i
    have h1 := hFU P Φ Dψ hW g (hDf.2.1 g hg) j i
    exact hPF P hP _ h1.1 (hFP P Φ Dψ hW g j i) h1.2
  filter_upwards [hv, hLI P Φ Dψ hW] with t hvt hlt
  intro j φ hφ hφc
  have hscal : ∀ i : Fin 3, (∫ y : Space, fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ)) *
        bsPot Φ (t, y) i) + ∫ y : Space, φ y * Dψ j (t, y) i = 0 := by
    intro i
    refine hDS D hDf (fun y => bsPot Φ (t, y) i) (fun y => Dψ j (t, y) i) j ?_ ?_ ?_ φ ⟨hφ, hφc⟩
    · intro R
      exact ContinuousLinearMap.integrableOn_comp
        ((EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).restrictScalars ℝ) (hlt R).1
    · intro R
      exact ContinuousLinearMap.integrableOn_comp
        ((EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).restrictScalars ℝ) ((hlt R).2 j)
    · intro χ hχ
      exact hvt χ hχ j i
  have hc1 : Continuous (fun y : Space => fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hc1c : HasCompactSupport (fun y : Space => fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))) :=
    (hφc.fderiv ℝ).comp_left (g := fun L : Space →L[ℝ] ℂ => L (EuclideanSpace.single j (1 : ℝ))) (by simp)

  have hi1 := wg_integrable_smul _ hc1 hc1c (fun y => bsPot Φ (t, y)) (fun R => (hlt R).1)
  have hi2 := wg_integrable_smul φ (hφ.continuous) hφc (fun y => Dψ j (t, y))
    (fun R => (hlt R).2 j)
  have hsum : (∫ y : Space, fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ)) • bsPot Φ (t, y)) +
      ∫ y : Space, φ y • Dψ j (t, y) = 0 := by
    ext i
    rw [PiLp.add_apply, wg_integral_apply _ hi1, wg_integral_apply _ hi2, PiLp.zero_apply]
    simpa [smul_eq_mul] using hscal i
  exact eq_neg_of_add_eq_zero_left hsum

end UnforcedLeray.Short.PartIIIb.Concrete
