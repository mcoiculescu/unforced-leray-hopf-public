import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_1_1_2_2_1
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.EtaCutoffFacts

/-!
# Part I, task `PartI:T08/4/1/1/1/2/2/1/1` (`cutoffL2BoundQ_proof`): quantitative `L²` from a cutoff bound

Source of record: `the November 2 reference manuscript`, lines 286-287.
The Prop is `CutoffL2BoundQ` in `Sub/PartI_T08_4_1_1_1_2_2_1.lean`.

Route as `cutoffL2OfBound_proof`: Fatou gives `∫⁻ ofReal (f²) ≤ ofReal B`; then
`ofReal_integral_eq_lintegral_ofReal` converts this to `ofReal (∫ f²) ≤ ofReal B`, and
`B ≥ 0` (the `R = 1` truncated integral is nonnegative) gives `∫ f² ≤ B`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-- **`CutoffL2BoundQ`** (proved). -/
theorem cutoffL2BoundQ_proof : UnforcedLeray.Short.PartI.CutoffL2BoundQ := by
  intro c B f hc hf hbound
  have hnn : ∀ n : ℕ, 0 ≤ᵐ[volume.restrict (Cyl.cell c)]
      (fun z : Plane => etaCutoff ((n : ℝ) + 1) z.2 * f z ^ 2) := fun n =>
    Filter.Eventually.of_forall (fun z => mul_nonneg (etaCutoff_nonneg _ _) (sq_nonneg _))
  have hint : ∀ n : ℕ, Integrable (fun z : Plane => etaCutoff ((n : ℝ) + 1) z.2 * f z ^ 2)
      (volume.restrict (Cyl.cell c)) := fun n =>
    vjl_cutoff_integrable (c := c) (R := (n : ℝ) + 1) (by positivity)
      (g := fun z => f z ^ 2) (hf.pow 2)
  have hlev : ∀ n : ℕ, ∫⁻ z in Cyl.cell c, ENNReal.ofReal (etaCutoff ((n : ℝ) + 1) z.2 * f z ^ 2)
      ≤ ENNReal.ofReal B := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hint n) (hnn n)]
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    exact ENNReal.ofReal_le_ofReal (hbound ((n : ℝ) + 1) (by linarith))
  have hlim : ∀ z : Plane, Tendsto
      (fun n : ℕ => ENNReal.ofReal (etaCutoff ((n : ℝ) + 1) z.2 * f z ^ 2)) atTop
      (𝓝 (ENNReal.ofReal (f z ^ 2))) := by
    intro z
    obtain ⟨N, hN⟩ := exists_nat_ge |z.2|
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    have hR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hab : |z.2| ≤ (n : ℝ) + 1 := by linarith
    rw [ecOne ((n : ℝ) + 1) hR z.2 hab, one_mul]
  have hmeas : ∀ n : ℕ, Measurable
      (fun z : Plane => ENNReal.ofReal (etaCutoff ((n : ℝ) + 1) z.2 * f z ^ 2)) := fun n =>
    (((cehd_eta_cont _).mul (hf.pow 2)).measurable).ennreal_ofReal
  have hfat := lintegral_liminf_le (μ := volume.restrict (Cyl.cell c)) (u := atTop) hmeas
  have hlhs : ∫⁻ a, liminf
      (fun n : ℕ => ENNReal.ofReal (etaCutoff ((n : ℝ) + 1) a.2 * f a ^ 2)) atTop
        ∂(volume.restrict (Cyl.cell c))
      = ∫⁻ a, ENNReal.ofReal (f a ^ 2) ∂(volume.restrict (Cyl.cell c)) :=
    lintegral_congr (fun a => (hlim a).liminf_eq)
  have hrhs : liminf (fun n : ℕ => ∫⁻ a in Cyl.cell c,
      ENNReal.ofReal (etaCutoff ((n : ℝ) + 1) a.2 * f a ^ 2)) atTop ≤ ENNReal.ofReal B :=
    liminf_le_of_frequently_le' (Eventually.of_forall hlev).frequently
  have key : ∫⁻ a, ENNReal.ofReal (f a ^ 2) ∂(volume.restrict (Cyl.cell c)) ≤ ENNReal.ofReal B :=
    le_trans (le_of_eq hlhs.symm) (hfat.trans hrhs)
  have hnn2 : 0 ≤ᵐ[volume.restrict (Cyl.cell c)] (fun z : Plane => f z ^ 2) :=
    Filter.Eventually.of_forall (fun z => sq_nonneg (f z))
  have hint2 : Integrable (fun z : Plane => f z ^ 2) (volume.restrict (Cyl.cell c)) :=
    ⟨(hf.pow 2).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hnn2).2 (lt_of_le_of_lt key ENNReal.ofReal_lt_top)⟩
  have hB0 : 0 ≤ B := by
    have h1 := hbound 1 le_rfl
    have h0 : 0 ≤ ∫ z in Cyl.cell c, etaCutoff 1 z.2 * f z ^ 2 :=
      integral_nonneg (fun z => mul_nonneg (etaCutoff_nonneg _ _) (sq_nonneg _))
    linarith
  refine ⟨(memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2 hint2, ?_⟩
  refine (ENNReal.ofReal_le_ofReal_iff hB0).1 ?_
  rw [ofReal_integral_eq_lintegral_ofReal hint2 hnn2]
  exact key

end UnforcedLeray.Short.PartI
