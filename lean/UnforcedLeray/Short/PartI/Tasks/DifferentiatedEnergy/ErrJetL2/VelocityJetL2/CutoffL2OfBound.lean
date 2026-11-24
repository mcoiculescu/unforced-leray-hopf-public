import UnforcedLeray.Short.PartI.Sub.PartI_T08_2_2
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.EtaCutoffFacts

/-!
# Part I, task `PartI:T08/2/2/3` (`cutoffL2OfBound_proof`): `L²` from a uniform cutoff bound

Source of record: `the November 2 reference manuscript`, lines 286-287
(transverse cutoffs, `R → ∞`). The Prop is `CutoffL2OfBound` in `Sub/PartI_T08_2_2.lean`.

Route: the integrands `g_n = etaCutoff (n+1) η · f²` are integrable on the cell and nonnegative,
and `g_n → f²` pointwise (`ecOne`: the cutoff is `1` once `|η| ≤ n+1`). Fatou
(`lintegral_liminf_le`) gives `∫⁻ ofReal (f²) ≤ liminf ∫⁻ ofReal g_n ≤ ofReal B < ⊤`; then
`hasFiniteIntegral_iff_ofReal` and `memLp_two_iff_integrable_sq`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-- **`CutoffL2OfBound`** (proved). -/
theorem cutoffL2OfBound_proof : UnforcedLeray.Short.PartI.CutoffL2OfBound := by
  intro c B f hc hf hbound
  -- nonnegativity and integrability of the truncated integrands
  have hnn : ∀ n : ℕ, 0 ≤ᵐ[volume.restrict (Cyl.cell c)]
      (fun z : Plane => etaCutoff ((n : ℝ) + 1) z.2 * f z ^ 2) := fun n =>
    Filter.Eventually.of_forall (fun z => mul_nonneg (etaCutoff_nonneg _ _) (sq_nonneg _))
  have hint : ∀ n : ℕ, Integrable (fun z : Plane => etaCutoff ((n : ℝ) + 1) z.2 * f z ^ 2)
      (volume.restrict (Cyl.cell c)) := fun n =>
    vjl_cutoff_integrable (c := c) (R := (n : ℝ) + 1) (by positivity)
      (g := fun z => f z ^ 2) (hf.pow 2)
  -- the truncated integrals are bounded by `B`
  have hlev : ∀ n : ℕ, ∫⁻ z in Cyl.cell c, ENNReal.ofReal (etaCutoff ((n : ℝ) + 1) z.2 * f z ^ 2)
      ≤ ENNReal.ofReal B := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hint n) (hnn n)]
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    exact ENNReal.ofReal_le_ofReal (hbound ((n : ℝ) + 1) (by linarith))
  -- pointwise convergence to `f²`
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
  -- Fatou
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
  -- finiteness and conclusion
  have hnn2 : 0 ≤ᵐ[volume.restrict (Cyl.cell c)] (fun z : Plane => f z ^ 2) :=
    Filter.Eventually.of_forall (fun z => sq_nonneg (f z))
  have hint2 : Integrable (fun z : Plane => f z ^ 2) (volume.restrict (Cyl.cell c)) :=
    ⟨(hf.pow 2).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hnn2).2 (lt_of_le_of_lt key ENNReal.ofReal_lt_top)⟩
  exact (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2 hint2

end UnforcedLeray.Short.PartI
