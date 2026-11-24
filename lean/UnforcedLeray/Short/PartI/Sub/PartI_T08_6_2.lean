import UnforcedLeray.Short.PartI.Sub.PartI_T08_6

/-!


Source: `the November 2 reference manuscript`,
line 346 (pressure term, order zero: `∫ f · ∇P = 0` for `div f = 0`, `P` bounded).

Route (a smooth cutoff in `η` replaces the slab limit): with `χ_R(η) = β(η/R)`, `β = 1` on `[-1,1]`,
`β = 0` off `(-2,2)`,
* `EtaCutIBP`: `∫_cell χ_R (f·∇P) = -∫_cell χ_R' P f₂` (the `q`-part is `∂_q(P f₀)`, zero by
  periodicity; the `η`-part is `∂_η(χ_R P f₁) - χ_R' P f₁` with `χ_R P f₁` compactly supported in
  `η`, hence in `L¹(cell)`; `div f = 0` removes the term `P div f`);
* `EtaCutLimit`: dominated convergence, `∫ χ_R g → ∫ g` for `g ∈ L¹(cell)`  (proved here);
* `EtaCutTail`: `∫ χ_R' P f₂ → 0` since `|χ_R'| ≤ K/R · 1_{|η| ≤ 2R}` has `L²(cell)` norm
  `O(R^{-1/2})` and `P f₂ ∈ L²(cell)` (Cauchy-Schwarz).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-- The standard bump: `1` on `[-1, 1]`, `0` outside `(-2, 2)`. -/
def etaBump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The cutoff in `η`: `χ_R(η) = β(η / R)`. -/
def etaCut (R η : ℝ) : ℝ := etaBump (R⁻¹ * η)

theorem etaCut_eq_one {R η : ℝ} (hR : 0 < R) (h : |η| ≤ R) : etaCut R η = 1 := by
  unfold etaCut
  have h1 : |R⁻¹ * η| ≤ 1 := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hR), inv_mul_le_iff₀ hR, mul_one]
    exact h
  apply etaBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
  exact h1

theorem etaCut_nonneg (R η : ℝ) : 0 ≤ etaCut R η := etaBump.nonneg
theorem etaCut_le_one (R η : ℝ) : etaCut R η ≤ 1 := etaBump.le_one

theorem continuous_etaCut (R : ℝ) : Continuous (etaCut R) :=
  etaBump.continuous.comp (continuous_const.mul continuous_id)

theorem contDiff_etaCut (R : ℝ) : ContDiff ℝ ∞ (etaCut R) :=
  etaBump.contDiff.comp (contDiff_const.mul contDiff_id)

theorem etaCut_eq_zero {R η : ℝ} (hR : 0 < R) (h : 2 * R ≤ |η|) : etaCut R η = 0 := by
  unfold etaCut
  have h1 : 2 ≤ |R⁻¹ * η| := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hR), le_inv_mul_iff₀ hR]
    linarith
  apply etaBump.zero_of_le_dist
  rw [Real.dist_eq, sub_zero]
  exact h1

/-- Hypotheses of the order-zero pressure orthogonality. -/
def PressureZeroHyp (c : ℝ) (f : Plane → Train.Vec) (P : Plane → ℝ) : Prop :=
  0 < c ∧ CellSmoothL2 c f ∧ (∀ z : Plane, Cyl.divergence f z = 0) ∧ ContDiff ℝ ∞ P ∧
    Cyl.IsPeriodic c P ∧ (∃ M : ℝ, ∀ z : Plane, |P z| ≤ M) ∧
    (∀ (w : List Bool) (k : Fin 2), MemLp (wordComp w (Train.gradS P) k) 2 (Cyl.cellμ c))

/-- **Leaf 1** (cutoff integration by parts, source line 346). -/
def EtaCutIBP : Prop :=
  ∀ (c : ℝ) (f : Plane → Train.Vec) (P : Plane → ℝ), PressureZeroHyp c f P → ∀ R : ℝ, 0 < R →
    ∫ z in Cyl.cell c, etaCut R z.2 * (f z 0 * Cyl.partialQ P z + f z 1 * Cyl.partialEta P z) =
      -∫ z in Cyl.cell c, deriv (etaCut R) z.2 * (P z * f z 1)

/-- **Leaf 3** (the cutoff-derivative term vanishes in the limit, source line 346). -/
def EtaCutTail : Prop :=
  ∀ (c : ℝ) (f : Plane → Train.Vec) (P : Plane → ℝ), PressureZeroHyp c f P →
    Tendsto (fun R : ℝ => ∫ z in Cyl.cell c, deriv (etaCut R) z.2 * (P z * f z 1)) atTop (𝓝 0)

/-- Leaf 2, proved: dominated convergence for the cutoff. -/
theorem etaCut_limit {c : ℝ} {g : Plane → ℝ} (hg : IntegrableOn g (Cyl.cell c)) :
    Tendsto (fun R : ℝ => ∫ z in Cyl.cell c, etaCut R z.2 * g z) atTop
      (𝓝 (∫ z in Cyl.cell c, g z)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun z => ‖g z‖) ?_ ?_ hg.norm ?_
  · exact Eventually.of_forall fun R =>
      (((continuous_etaCut R).comp continuous_snd).aestronglyMeasurable).mul hg.aestronglyMeasurable
  · refine Eventually.of_forall fun R => Eventually.of_forall fun z => ?_
    rw [norm_mul, Real.norm_of_nonneg (etaCut_nonneg _ _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (etaCut_le_one _ _)
  · refine Eventually.of_forall fun z => ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (|z.2| + 1)] with R hR
    have hR0 : 0 < R := by linarith [abs_nonneg z.2]
    rw [etaCut_eq_one hR0 (by linarith), one_mul]

theorem jetPressureOrthZero_of (h1 : EtaCutIBP) (h3 : EtaCutTail) : JetPressureOrthZero := by
  intro c hc f hf hdiv P hP hper hM hL2P
  have hyp : PressureZeroHyp c f P := ⟨hc, hf, hdiv, hP, hper, hM, hL2P⟩
  obtain ⟨_, _, hL2⟩ := hf
  have hint : IntegrableOn (fun z => f z 0 * Cyl.partialQ P z + f z 1 * Cyl.partialEta P z)
      (Cyl.cell c) := by
    have a0 := (hL2 [] 0).integrable_mul (hL2P [] 0)
    have a1 := (hL2 [] 1).integrable_mul (hL2P [] 1)
    exact a0.add a1
  have hjet : jetPair c 0 f (Train.gradS P) =
      ∫ z in Cyl.cell c, (f z 0 * Cyl.partialQ P z + f z 1 * Cyl.partialEta P z) := by
    unfold jetPair
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp [wordsOfLength, wordComp, B0151.derivWord, Train.gradS, Fin.sum_univ_two]
  rw [hjet]
  have hL := etaCut_limit hint
  have hR := h3 c f P hyp
  have heq : (fun R : ℝ => ∫ z in Cyl.cell c, etaCut R z.2 *
      (f z 0 * Cyl.partialQ P z + f z 1 * Cyl.partialEta P z)) =ᶠ[atTop]
      fun R => -∫ z in Cyl.cell c, deriv (etaCut R) z.2 * (P z * f z 1) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR0
    exact h1 c f P hyp R hR0
  have hL' := hL.congr' heq
  have := tendsto_nhds_unique hL' hR.neg
  simpa using this

end UnforcedLeray.Short.PartI
