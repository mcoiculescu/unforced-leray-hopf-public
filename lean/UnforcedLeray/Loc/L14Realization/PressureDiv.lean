import UnforcedLeray.Loc.L14Realization.Quadratic
import UnforcedLeray.Analysis.Pressure.KernelCommutation
import UnforcedLeray.Analysis.Pressure.HeatTest
import UnforcedLeray.Analysis.WeakL2R3

/-!
# Step L14, helpers: the Newton pressure identity in divergence form

Support for `Loc/L14Realization.lean` (step L14 `RealizationStep`, `paper/main.tex`
lines 107–111 and 559–561, blueprint unit B1032, decision D6 of the scoping plan, critic §6).

For a solenoidal `u ∈ L²` with `L²` weak derivatives `g`, forcing `F = (u·∇)u ∈ L²` and
columns `uⱼu ∈ L²`, the compiled Newton pressure `p = PressureAnalysis.velocityPressure u g`
satisfies, for every compact smooth vector test `φ`,

  `∫ p div φ = -Σⱼ ⟨uⱼu, (I - 𝔓)∂ⱼφ⟩`   (`velocityPressure_div_identity`),

that is `∇p = -(I - 𝔓) div(u ⊗ u)`, the identity of line 561 ("add `∇p` to the projected
equation"). The `(u·∇)u` form `∫ p div φ = ⟨(I - 𝔓)F, φ⟩` is
`RieszLp.velocityPressure_pressure_identity` (`Lib/CZL2/PressureIdentity.lean`, INF01 T5).
With `ψ = N ∗ div φ`, `(I - 𝔓)φ = -∇ψ` and `(I - 𝔓)∂ⱼφ = -∇∂ⱼψ`
(`RieszLp.toL2_sub_projection_vecField` for the test `∂ⱼφ`, whose potential is `∂ⱼψ`), so the
two forms differ by `∫ Fᵢ ∂ᵢψ = -Σⱼ ∫ uⱼuᵢ ∂ⱼ∂ᵢψ`, the weak product rule against the bounded
smooth `∂ᵢψ`; it follows from the compact-test rule against `χ_R ∂ᵢψ` as `R → ∞`.

`isMinusLerayDiv_eq_neg_projection`: under the same hypotheses, `-𝔓 div(u ⊗ u) = -𝔓 F` in
`L²`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology InnerProductSpace

namespace UnforcedLeray.Blueprint.L14

open PressureAnalysis RieszLp

/-- Smooth functions have symmetric second coordinate derivatives. -/
theorem spatialTestDerivative_comm_of_contDiff {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (i j : Fin 3) (x : Space) :
    spatialTestDerivative i (spatialTestDerivative j ψ) x =
      spatialTestDerivative j (spatialTestDerivative i ψ) x := by
  have hd : ∀ y, HasFDerivAt (fderiv ℝ ψ) (fderiv ℝ (fderiv ℝ ψ) y) y := fun y =>
    ((hψ.fderiv_right (m := 1) (by simp)).differentiable (by simp) y).hasFDerivAt
  have key : ∀ a b : Fin 3, spatialTestDerivative a (spatialTestDerivative b ψ) x =
      fderiv ℝ (fderiv ℝ ψ) x (coordinateVector a) (coordinateVector b) := by
    intro a b
    have hx := (hd x).clm_apply (hasFDerivAt_const (coordinateVector b) x)
    unfold spatialTestDerivative
    rw [hx.fderiv]
    simp
  rw [key, key]
  exact (hψ.contDiffAt.isSymmSndFDerivAt (by simp)).eq _ _

theorem decayWeight_le_one (y : Space) : decayWeight y ≤ 1 := by
  unfold decayWeight
  apply inv_le_one_of_one_le₀
  nlinarith [norm_nonneg y]

/-- `div(∂ₖφ) = ∂ₖ div φ` for tests. -/
theorem divTest_partial {f : Fin 3 → Space → ℝ} (hf : ∀ j, IsSpatialTest (f j)) (k : Fin 3) :
    divTest (fun j => spatialTestDerivative k (f j)) = spatialTestDerivative k (divTest f) := by
  funext x
  change ∑ j : Fin 3, spatialTestDerivative j (spatialTestDerivative k (f j)) x =
    spatialTestDerivative k (fun y => ∑ j : Fin 3, spatialTestDerivative j (f j) y) x
  rw [spatialTestDerivative_sum _ (fun j => (hf j).derivative j)]
  exact Finset.sum_congr rfl fun j _ =>
    congrFun (SobolevGraph.spatialTestDerivative_comm (hf j) j k) x

/-- The potential of `∂ₖφ` is `∂ₖψ`. -/
theorem lerayPotential_partial {f : Fin 3 → Space → ℝ} (hf : ∀ j, IsSpatialTest (f j))
    (k : Fin 3) :
    lerayPotential (fun j => spatialTestDerivative k (f j)) =
      spatialTestDerivative k (lerayPotential f) := by
  unfold lerayPotential
  rw [divTest_partial hf k, spatialTestDerivative_newtonConv (isSpatialTest_divTest hf) k]

/-- The components of `∂ₖφ` are `∂ₖφⱼ`. -/
theorem testPartial_eq_vecField {φ : Space → Space} (hφ : IsVectorTest φ) (k : Fin 3) :
    testPartial φ k = vecField (fun j => spatialTestDerivative k (fun y => φ y j)) := by
  rw [← vecField_components (testPartial φ k)]
  congr 1
  funext j x
  exact (L10.spatialTestDerivative_testComponent hφ j k x).symm

/-- `(I - 𝔓)∂ₖφ = -∇∂ₖψ` with `ψ = N ∗ div φ`. -/
theorem toL2_sub_projection_testPartial {φ : Space → Space} (hφ : IsVectorTest φ) (k : Fin 3) :
    toL2 (testPartial φ k) - Leray.projection (toL2 (testPartial φ k)) =
      -toL2 (gradField (spatialTestDerivative k (lerayPotential (fun j x => φ x j)))) := by
  have hf : ∀ j, IsSpatialTest (fun x => φ x j) := fun j => L10.isSpatialTest_testComponent hφ j
  have hfk : ∀ j, IsSpatialTest (spatialTestDerivative k (fun y => φ y j)) :=
    fun j => (hf j).derivative k
  rw [testPartial_eq_vecField hφ k, toL2_sub_projection_vecField hfk, lerayPotential_partial hf k]

/-- `⟨toL2 A, toL2 ∇χ⟩ = Σᵢ ∫ Aᵢ ∂ᵢχ`. -/
theorem inner_toL2_gradField {A : SpatialField} {χ : Space → ℝ} (hA : MemLp A 2 volume)
    (hχ : MemLp (gradField χ) 2 volume)
    (hi : ∀ i, Integrable (fun x => A x i * spatialTestDerivative i χ x)) :
    inner ℝ (toL2 A) (toL2 (gradField χ)) = ∑ i : Fin 3, ∫ x, A x i * spatialTestDerivative i χ x := by
  rw [inner_toL2_eq_integral hA hχ, ← integral_finsetSum _ fun i _ => hi i]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  have h := inner_vecField_gradField (fun j x => A x j) χ x
  rwa [vecField_components] at h

section Div

variable {u : SpatialField} {g : Fin 3 → SpatialField}

/-- The weak product rule against a bounded smooth `∂ᵢψ` whose derivatives are bounded:
`∫ ∂ᵢψ Fᵢ = -Σⱼ ∫ ∂ⱼ∂ᵢψ uⱼuᵢ`. -/
theorem integral_forcing_mul_smooth (hu : MemLp u 2 volume) (hg : ∀ j, MemLp (g j) 2 volume)
    (hderiv : ∀ j, HasWeakSpatialDerivative j u (g j)) (hs : IsSolenoidal u)
    (hF : ∀ i, MemLp (velocityForcing u g i) 2 volume)
    {a : Space → ℝ} (ha : ContDiff ℝ ∞ a) (ha2 : MemLp a 2 volume) {A : ℝ}
    (haA : ∀ x, |a x| ≤ A) {B : ℝ} (hdaB : ∀ j x, |spatialTestDerivative j a x| ≤ B) (i : Fin 3) :
    ∫ x, a x * velocityForcing u g i x =
      -∑ j : Fin 3, ∫ x, spatialTestDerivative j a x * (u x j * u x i) := by
  have huu : ∀ j, Integrable (fun x => u x j * u x i) := fun j =>
    memLp_one_iff_integrable.mp ((EnergyInterpolation.coordinate_memLp hu i).mul'
      (EnergyInterpolation.coordinate_memLp hu j))
  have hda : ∀ j, ContDiff ℝ ∞ (spatialTestDerivative j a) := fun j =>
    contDiff_spatialTestDerivative ha j
  have hI1 : Integrable (fun x => a x * velocityForcing u g i x) :=
    memLp_one_iff_integrable.mp ((hF i).mul' ha2)
  have hI2 : ∀ j, Integrable (fun x => spatialTestDerivative j a x * (u x j * u x i)) :=
    fun j => (huu j).bdd_mul (c := B) (hda j).continuous.aestronglyMeasurable
      (Eventually.of_forall fun x => (Real.norm_eq_abs _).trans_le (hdaB j x))
  have hI3 : ∀ j, Integrable (fun x => a x * (u x j * u x i)) :=
    fun j => (huu j).bdd_mul (c := A) ha.continuous.aestronglyMeasurable
      (Eventually.of_forall fun x => (Real.norm_eq_abs _).trans_le (haA x))
  have hlim := tendsto_integral_cutoff_mul hI1
  have hr := (tendsto_finsetSum Finset.univ (fun j _ =>
    (tendsto_integral_cutoff_mul (hI2 j)).add (tendsto_integral_cutoff_deriv_mul (hI3 j) j))).neg
  simp only [add_zero] at hr
  refine tendsto_nhds_unique hlim (hr.congr' (Eventually.of_forall fun n => ?_))
  -- the compact identity at `R = n + 1`
  set R : ℝ := (n : ℝ) + 1
  have hR : 0 < R := by positivity
  have hχ := cutoff_isSpatialTest hR
  have hζ : IsSpatialTest (fun x => cutoff R x * a x) :=
    ⟨(cutoff_contDiff R).mul ha, hχ.compact.mul_right⟩
  have hid := velocityForcing_test_identity hu hg hderiv hs hζ i
  have hL : ∫ x, cutoff R x * (a x * velocityForcing u g i x) =
      ∫ x, (cutoff R x * a x) * velocityForcing u g i x :=
    integral_congr_ae (Eventually.of_forall fun x => by ring)
  refine Eq.symm ?_
  show (∫ x, cutoff R x * (a x * velocityForcing u g i x)) = _
  rw [hL, hid]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have hJ1 : Integrable (fun x => cutoff R x * (spatialTestDerivative j a x * (u x j * u x i))) :=
    (hI2 j).bdd_mul (c := 1) (cutoff_contDiff R).continuous.aestronglyMeasurable
      (Eventually.of_forall fun x => (Real.norm_eq_abs _).trans_le (abs_cutoff_le_one R x))
  have hJ2 : Integrable (fun x => spatialTestDerivative j (cutoff R) x * (a x * (u x j * u x i))) :=
    (hI3 j).bdd_mul (c := R⁻¹ * (Classical.choose exists_fderiv_baseBump_bound))
      ((hχ.derivative j).smooth.continuous.aestronglyMeasurable)
      (Eventually.of_forall fun x => (Real.norm_eq_abs _).trans_le
        (abs_spatialTestDerivative_cutoff_le hR
          (Classical.choose_spec exists_fderiv_baseBump_bound).2 j x))
  rw [← integral_add hJ1 hJ2]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [RieszLp.spatialTestDerivative_mul (cutoff_contDiff R) ha j x]
  ring

/-- **Newton pressure identity in divergence form** (`∇p = -(I - 𝔓) div(u ⊗ u)`). -/
theorem velocityPressure_div_identity (hu : MemLp u 2 volume) (hg : ∀ j, MemLp (g j) 2 volume)
    (hderiv : ∀ j, HasWeakSpatialDerivative j u (g j)) (hs : IsSolenoidal u)
    (hF : ∀ i, MemLp (velocityForcing u g i) 2 volume)
    (hcol : ∀ j, MemLp (tensorColumns u u j) 2 volume)
    {φ : Space → Space} (hφ : IsVectorTest φ) :
    ∫ x, velocityPressure u g x * ∑ i : Fin 3, testPartial φ i x i =
      -∑ j : Fin 3, inner ℝ (toL2 (tensorColumns u u j))
        (toL2 (testPartial φ j) - Leray.projection (toL2 (testPartial φ j))) := by
  have hf : ∀ j, IsSpatialTest (fun x => φ x j) := fun j => L10.isSpatialTest_testComponent hφ j
  set ψ := lerayPotential (fun j x => φ x j) with hψdef
  have hψ : ContDiff ℝ ∞ ψ := lerayPotential_contDiff hf
  obtain ⟨M, -, hM⟩ := lerayPotential_decay hf
  have hdec2 : ∀ k, ∃ M', ∀ i y, |spatialTestDerivative i (spatialTestDerivative k ψ) y| ≤
      M' * decayWeight y := by
    intro k
    obtain ⟨M', -, hM'⟩ := lerayPotential_decay (fun j => (hf j).derivative k)
    refine ⟨M', fun i y => ?_⟩
    have := hM' i y
    rwa [lerayPotential_partial hf k] at this
  choose M' hM' using hdec2
  have hle : ∀ (c : ℝ) (y : Space), c * decayWeight y ≤ |c| := fun c y =>
    calc c * decayWeight y ≤ |c| * decayWeight y :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (decayWeight_pos y).le
      _ ≤ |c| := mul_le_of_le_one_right (abs_nonneg _) (decayWeight_le_one y)
  have hA : ∀ i x, |spatialTestDerivative i ψ x| ≤ |M| := fun i x => (hM i x).trans (hle M x)
  have hB : ∀ i j x, |spatialTestDerivative j (spatialTestDerivative i ψ) x| ≤
      ∑ k : Fin 3, |M' k| := by
    intro i j x
    rw [spatialTestDerivative_comm_of_contDiff hψ j i x]
    exact (hM' j i x).trans ((hle (M' j) x).trans (Finset.single_le_sum
      (f := fun k => |M' k|) (fun k _ => abs_nonneg _) (Finset.mem_univ j)))
  have hdψ2 : ∀ i, MemLp (spatialTestDerivative i ψ) 2 volume := fun i =>
    memLp_two_of_norm_le (contDiff_spatialTestDerivative hψ i).continuous.aestronglyMeasurable
      (M := M) fun y => (Real.norm_eq_abs _).trans_le (hM i y)
  have hd2ψ2 : ∀ j i, MemLp (spatialTestDerivative i (spatialTestDerivative j ψ)) 2 volume :=
    fun j i => memLp_two_of_norm_le
      ((contDiff_spatialTestDerivative (contDiff_spatialTestDerivative hψ j) i).continuous
        |>.aestronglyMeasurable) (M := M' j) fun y => (Real.norm_eq_abs _).trans_le (hM' j i y)
  -- the left side, by the `(u·∇)u` form of the identity
  have hdiv : ∀ x, ∑ i : Fin 3, testPartial φ i x i =
      ∑ j : Fin 3, spatialTestDerivative j (fun y => φ y j) x := fun x =>
    Finset.sum_congr rfl fun i _ => (L10.spatialTestDerivative_testComponent hφ i i x).symm
  have hLHS : ∫ x, velocityPressure u g x * ∑ i : Fin 3, testPartial φ i x i =
      ∫ x, velocityPressure u g x *
        ∑ j : Fin 3, spatialTestDerivative j (fun y => φ y j) x :=
    integral_congr_ae (Eventually.of_forall fun x => by simp only [hdiv x])
  rw [hLHS, velocityPressure_pressure_identity hu hg hF φ hf]
  set A := forcingL2 u g with hAdef
  have hφm : MemLp φ 2 volume := L10.vectorTest_memLp hφ 2
  have h1 : ∫ x, inner ℝ ((A - Leray.projection A) x) (φ x) =
      inner ℝ (A - Leray.projection A) (toL2 φ) := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_toL2 hφm] with x hx
    rw [hx]
  have h2 : inner ℝ (A - Leray.projection A) (toL2 φ) =
      inner ℝ A (toL2 φ - Leray.projection (toL2 φ)) := by
    rw [inner_sub_left, inner_sub_right, Leray.projection_selfadjoint]
  have h3 : toL2 φ - Leray.projection (toL2 φ) = -toL2 (gradField ψ) := by
    have h := toL2_sub_projection_vecField hf
    rwa [vecField_components] at h
  have hFv := memLp_vecField_of_components hF
  have hgψ : MemLp (gradField ψ) 2 volume := memLp_gradField hψ hM
  have h4 : inner ℝ A (toL2 (gradField ψ)) =
      ∑ i : Fin 3, ∫ x, velocityForcing u g i x * spatialTestDerivative i ψ x := by
    have hint : ∀ i, Integrable (fun x => vecField (velocityForcing u g) x i *
        spatialTestDerivative i ψ x) := fun i => by
      simp only [vecField_apply]
      exact memLp_one_iff_integrable.mp ((hdψ2 i).mul' (hF i))
    have h := inner_toL2_gradField hFv hgψ hint
    simp only [vecField_apply] at h
    exact h
  rw [h1, h2, h3, inner_neg_right, h4]
  -- the right side
  have hR : ∀ j, inner ℝ (toL2 (tensorColumns u u j))
      (toL2 (testPartial φ j) - Leray.projection (toL2 (testPartial φ j))) =
      -∑ i : Fin 3, ∫ x, tensorColumns u u j x i *
        spatialTestDerivative i (spatialTestDerivative j ψ) x := by
    intro j
    have hgj : MemLp (gradField (spatialTestDerivative j ψ)) 2 volume :=
      memLp_gradField (contDiff_spatialTestDerivative hψ j) (hM' j)
    rw [toL2_sub_projection_testPartial hφ j, ← hψdef, inner_neg_right,
      inner_toL2_gradField (hcol j) hgj (fun i => memLp_one_iff_integrable.mp
        ((hd2ψ2 j i).mul' (EnergyInterpolation.coordinate_memLp (hcol j) i)))]
  have hL : ∀ i, ∫ x, velocityForcing u g i x * spatialTestDerivative i ψ x =
      -∑ j : Fin 3, ∫ x, spatialTestDerivative j (spatialTestDerivative i ψ) x *
        (u x j * u x i) := by
    intro i
    rw [← integral_forcing_mul_smooth hu hg hderiv hs hF (contDiff_spatialTestDerivative hψ i)
      (hdψ2 i) (hA i) (hB i) i]
    exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  rw [Finset.sum_congr rfl fun i _ => hL i, Finset.sum_congr rfl fun j _ => hR j]
  simp only [Finset.sum_neg_distrib, neg_neg]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ =>
    integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [tensorColumns_apply]
  rw [spatialTestDerivative_comm_of_contDiff hψ j i x]
  ring

end Div

end UnforcedLeray.Blueprint.L14
