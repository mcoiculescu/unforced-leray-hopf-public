import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellFixedCutoff

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint
open UnforcedLeray.PhaseSpace

/-- The actual spatial slice gradient of a rough spacetime scalar. Unlike `gradT`, this definition
uses only spatial slice derivatives and imposes no temporal differentiability. -/
def scalarSliceGrad (F : SpaceTime → ℂ) (z : SpaceTime) : CVec3 :=
  ∑ j : Fin 3,
    (fderiv ℝ (fun x : Space => F (z.1, x)) z.2 (EuclideanSpace.single j (1 : ℝ))) •
      EuclideanSpace.single j (1 : ℂ)

/-- The finite-dimensional vector gradient inherits the actual cell Lp convergence of each
spatial component of the nested cutoff mollifications. -/
theorem tendsto_nestedCutoff_gradT_cellLp
    {P : ℝ} [Fact (0 < P)] {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {U : ℝ → SpatialField} (hU : IsBoundedBackground U)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (n : ℕ) (hn : 2 / ((n : ℝ) + 1) ≤ P) :
    Tendsto (fun k => eLpNorm
      (fun z : SpaceTime =>
        PhaseSpace.gradT (nestedCutoffMollification P n k Φ U) z -
          (phaseInteriorCutoff P n z.1) ^ 2 •
            scalarSliceGrad (scalarTestBackground Φ U) z) p
      (volume.restrict (phaseCell P))) atTop (𝓝 0) := by
  let μ : Measure SpaceTime := volume.restrict (phaseCell P)
  let err : ℕ → Fin 3 → SpaceTime → ℂ := fun k j z =>
    PhaseSpace.dy j (nestedCutoffMollification P n k Φ U) z -
      (phaseInteriorCutoff P n z.1) ^ 2 •
        fderiv ℝ (fun x : Space => scalarTestBackground Φ U (z.1, x)) z.2
          (EuclideanSpace.single j (1 : ℝ))
  let term : ℕ → Fin 3 → SpaceTime → CVec3 := fun k j z =>
    err k j z • EuclideanSpace.single j (1 : ℂ)
  let V : ℕ → SpaceTime → CVec3 := fun k z =>
    PhaseSpace.gradT (nestedCutoffMollification P n k Φ U) z -
      (phaseInteriorCutoff P n z.1) ^ 2 • scalarSliceGrad (scalarTestBackground Φ U) z
  have hdecomp (k : ℕ) : V k = fun z => ∑ j : Fin 3, term k j z := by
    funext z
    ext i
    simp [V, term, err, PhaseSpace.gradT, PhaseSpace.dy, scalarSliceGrad,
      Complex.real_smul, smul_eq_mul]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hcomp (j : Fin 3) :
      Tendsto (fun m : ℕ => eLpNorm (err m j) p μ) atTop (𝓝 0) := by
    simpa [err, μ] using
      tendsto_nestedCutoff_spatialDerivative_cellLp hΦ hU hp n j hn
  have htermmeas (k : ℕ) (j : Fin 3) : AEStronglyMeasurable (term k j) μ := by
    have hNcd : ContDiff ℝ ∞ (nestedCutoffMollification P n k Φ U) :=
      (nestedCutoffMollification_isCompactInteriorTest
        (P := P) (n := n) (k := k) hΦ hU hn).1
    have hdy : Continuous (fun z : SpaceTime =>
        PhaseSpace.dy j (nestedCutoffMollification P n k Φ U) z) := by
      exact (hNcd.continuous_fderiv (by simp)).clm_apply continuous_const
    have hcell := scalarTestBackground_spatialDerivative_memLp_cell hΦ hU hp j
    have hχ : Continuous (fun z : SpaceTime =>
        Complex.ofReal (phaseInteriorCutoff P n z.1 ^ 2)) := by
      exact Complex.continuous_ofReal.comp
        (((contDiff_phaseInteriorCutoff P n).continuous.comp continuous_fst).pow 2)
    have herr : AEStronglyMeasurable (err k j) μ := by
      apply hdy.aestronglyMeasurable.sub
      change AEStronglyMeasurable
        ((fun z : SpaceTime => Complex.ofReal (phaseInteriorCutoff P n z.1 ^ 2)) *
          (fun z => fderiv ℝ (fun x : Space => scalarTestBackground Φ U (z.1, x))
            z.2 (EuclideanSpace.single j (1 : ℝ)))) μ
      exact hχ.aestronglyMeasurable.mul hcell.aestronglyMeasurable
    exact herr.smul (continuous_const.aestronglyMeasurable)
  have hsum (k : ℕ) :
      eLpNorm (V k) p μ ≤ ∑ j : Fin 3, eLpNorm (err k j) p μ := by
    calc
      eLpNorm (V k) p μ = eLpNorm (fun z => ∑ j : Fin 3, term k j z) p μ := by
        rw [hdecomp k]
      _ ≤ ∑ j : Fin 3, eLpNorm (term k j) p μ := by
        exact eLpNorm_sum_le (s := (Finset.univ : Finset (Fin 3)))
          (f := fun j z => term k j z) (fun j _ => htermmeas k j) Fact.out
      _ ≤ ∑ j : Fin 3, eLpNorm (err k j) p μ := by
        apply Finset.sum_le_sum
        intro j hj
        apply eLpNorm_mono_ae
        filter_upwards with z
        simp [term, norm_smul]
  have hsumT : Tendsto (fun k : ℕ => ∑ j : Fin 3, eLpNorm (err k j) p μ)
      atTop (𝓝 0) := by
    simpa using tendsto_finsetSum (s := Finset.univ) (fun j hj => hcomp j)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsumT
    (fun k => bot_le) hsum

#print axioms tendsto_nestedCutoff_gradT_cellLp

end UnforcedLeray.Cons.C03.Concrete
