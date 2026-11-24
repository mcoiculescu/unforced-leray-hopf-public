import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T12_7_6
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.HeatSymm
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.SliceIdentity.Split.FlatHeatInt

/-!
# Part II-b, task `PartII-b:T12/7/6/1` (`deqPairSplit`): algebraic splitting of `deqPair`

Source of record: `the November 2 reference manuscript`, lines 1923-1927.

`flatTranspose ν μ Ψ (s,z) i = (μ-1) Ψ_i(s,z) - s · φ_i(s,z)` with
`φ_i = ∂_sΨ_i + ν(∂_q²+∂_η²)Ψ_i` (`deqPhiCoef`). Splitting the `z`-integral (integrability from
`deqFlatHeatMulInt`, `Split/FlatHeatInt.lean`) and applying `deqHeatSymm` to the two test slices
`Ψ_i(s,·)` and `φ_i(s,·)` gives the claim, since `deqSmoothD = ∫ K · φ_i(s, · - w)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- The real coefficient `∂_sΨ_i + ν(∂_q²+∂_η²)Ψ_i` of the transpose `flatTranspose`. -/
def deqPhiCoef (ν : ℝ) (Ψ : Coord → Fin 2 → ℝ) (i : Fin 2) (x : Coord) : ℝ :=
  cpd 0 (fun y => Ψ y i) x + ν * (cpd 1 (fun y => cpd 1 (fun z => Ψ z i) y) x +
    cpd 2 (fun y => cpd 2 (fun z => Ψ z i) y) x)

theorem deqCpdCompact {φ : Coord → ℝ} (hφ : HasCompactSupport φ) (j : Fin 3) :
    HasCompactSupport (fun x => cpd j φ x) := by
  unfold cpd
  exact hφ.fderiv_apply (𝕜 := ℝ) (cdir j)

theorem deqPhiCoef_compact (ν : ℝ) {Ψ : Coord → Fin 2 → ℝ} {i : Fin 2}
    (hi : IsCoordTest (fun x => Ψ x i)) : HasCompactSupport (deqPhiCoef ν Ψ i) := by
  have h0 := deqCpdCompact hi.compact 0
  have h1 := deqCpdCompact (deqCpdCompact hi.compact 1) 1
  have h2 := deqCpdCompact (deqCpdCompact hi.compact 2) 2
  have h12 := h1.add h2
  have h3 : HasCompactSupport (fun x => ν * (cpd 1 (fun y => cpd 1 (fun z => Ψ z i) y) x +
      cpd 2 (fun y => cpd 2 (fun z => Ψ z i) y) x)) :=
    HasCompactSupport.comp_left (g := fun y : ℝ => ν * y) h12 (by simp)
  unfold deqPhiCoef
  exact h0.add h3

theorem deqPhiCoef_contDiff (ν : ℝ) {Ψ : Coord → Fin 2 → ℝ} {i : Fin 2}
    (hi : IsCoordTest (fun x => Ψ x i)) : Continuous (deqPhiCoef ν Ψ i) := by
  unfold deqPhiCoef
  exact (deqT_cpd_contDiff hi.smooth 0).continuous.add
    (continuous_const.mul ((deqT_cpd_contDiff (deqT_cpd_contDiff hi.smooth 1) 1).continuous.add
      (deqT_cpd_contDiff (deqT_cpd_contDiff hi.smooth 2) 2).continuous))

theorem deqSlice_cont {h : Coord → ℝ} (hh : Continuous h) (s : ℝ) :
    Continuous (fun z : ℝ × ℝ => h (s, z)) :=
  hh.comp (continuous_const.prodMk continuous_id)

theorem deqSlice_compact {h : Coord → ℝ} (hh : HasCompactSupport h) (s : ℝ) :
    HasCompactSupport (fun z : ℝ × ℝ => h (s, z)) :=
  hh.comp_isClosedEmbedding
    ⟨isEmbedding_prodMkRight s, (isClosedMap_prodMk_left s).isClosed_range⟩

/-- **Task `PartII-b:T12/7/6/1`** (SP 1923-1927): algebraic splitting of `deqPair`. -/
theorem deqPairSplit : UnforcedLeray.Short.IIb.DeqPairSplit := by
  intro ν μ c r t hν ht hc hr g hg Ψ hΨ s hts
  have hθ : 0 < ν * (s - t) := mul_pos hν (sub_pos.2 hts)
  have hT : ∀ (i : Fin 2) (z : ℝ × ℝ), flatTranspose ν μ Ψ (s, z) i =
      (μ - 1) * (Ψ (s, z) i : ℂ) - (s : ℂ) * (deqPhiCoef ν Ψ i (s, z) : ℂ) := by
    intro i z
    simp only [flatTranspose, deqPhiCoef]
    push_cast
    ring
  have hI1 : ∀ i : Fin 2, Integrable (fun z : ℝ × ℝ =>
      flatHeat (ν * (s - t)) g z i * (Ψ (s, z) i : ℂ)) := fun i =>
    deqFlatHeatMulInt hc hr hg hθ (ψ := fun z => Ψ (s, z) i)
      (deqSlice_cont (hΨ.smooth i).smooth.continuous s)
      (deqSlice_compact (hΨ.smooth i).compact s) i
  have hI2 : ∀ i : Fin 2, Integrable (fun z : ℝ × ℝ =>
      flatHeat (ν * (s - t)) g z i * (deqPhiCoef ν Ψ i (s, z) : ℂ)) := fun i =>
    deqFlatHeatMulInt hc hr hg hθ (ψ := fun z => deqPhiCoef ν Ψ i (s, z))
      (deqSlice_cont (deqPhiCoef_contDiff ν (hΨ.smooth i)) s)
      (deqSlice_compact (deqPhiCoef_compact ν (hΨ.smooth i)) s) i
  have e1 : ∀ i : Fin 2, ∫ z : ℝ × ℝ, flatHeat (ν * (s - t)) g z i * (Ψ (s, z) i : ℂ) =
      ∫ z : ℝ × ℝ, g z i * (deqSmooth ν Ψ i t s z : ℂ) := fun i =>
    deqHeatSymm c r g hc hr hg (ν * (s - t)) hθ (fun z => Ψ (s, z) i)
      (deqSlice_cont (hΨ.smooth i).smooth.continuous s)
      (deqSlice_compact (hΨ.smooth i).compact s) i
  have e2 : ∀ i : Fin 2, ∫ z : ℝ × ℝ, flatHeat (ν * (s - t)) g z i *
      (deqPhiCoef ν Ψ i (s, z) : ℂ) =
      ∫ z : ℝ × ℝ, g z i * (deqSmoothD ν Ψ i t s z : ℂ) := fun i =>
    deqHeatSymm c r g hc hr hg (ν * (s - t)) hθ (fun z => deqPhiCoef ν Ψ i (s, z))
      (deqSlice_cont (deqPhiCoef_contDiff ν (hΨ.smooth i)) s)
      (deqSlice_compact (deqPhiCoef_compact ν (hΨ.smooth i)) s) i
  have key : ∀ i : Fin 2,
      ∫ z : ℝ × ℝ, flatHeat (ν * (s - t)) g z i * flatTranspose ν μ Ψ (s, z) i =
        (μ - 1) * (∫ z : ℝ × ℝ, g z i * (deqSmooth ν Ψ i t s z : ℂ)) -
          (s : ℂ) * (∫ z : ℝ × ℝ, g z i * (deqSmoothD ν Ψ i t s z : ℂ)) := by
    intro i
    have hsplit : ∫ z : ℝ × ℝ, flatHeat (ν * (s - t)) g z i * flatTranspose ν μ Ψ (s, z) i =
        ∫ z : ℝ × ℝ, ((μ - 1) * (flatHeat (ν * (s - t)) g z i * (Ψ (s, z) i : ℂ)) -
          (s : ℂ) * (flatHeat (ν * (s - t)) g z i * (deqPhiCoef ν Ψ i (s, z) : ℂ))) := by
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      dsimp only
      rw [hT i z]
      ring
    rw [hsplit, integral_sub ((hI1 i).const_mul (μ - 1)) ((hI2 i).const_mul (s : ℂ)),
      integral_const_mul, integral_const_mul, e1 i, e2 i]
  have hint : ∀ i ∈ (Finset.univ : Finset (Fin 2)),
      Integrable (fun z : ℝ × ℝ =>
        flatHeat (ν * (s - t)) g z i * flatTranspose ν μ Ψ (s, z) i) := by
    intro i _
    refine (((hI1 i).const_mul (μ - 1)).sub ((hI2 i).const_mul (s : ℂ))).congr
      (Eventually.of_forall fun z => ?_)
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [hT i z]
    ring
  unfold deqPair
  rw [integral_finsetSum _ hint]
  exact Finset.sum_congr rfl fun i _ => key i

end UnforcedLeray.Short.IIb
