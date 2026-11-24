import UnforcedLeray.Units.B0306.Conv
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# B0306 helper: splitting an inverse-distance field at the origin

Helper module of blueprint unit B0306 (`background:eq:2.48`, `paper/main.tex` lines
5909--5921). A field `b` smooth off zero with `|D^j b(x)| ≤ C_j |x|^{-1-j}` is split with a fixed
smooth cutoff `cut` (equal to `1` on `|x| ≤ 1/4`, vanishing on `|x| ≥ 1/2`) as
`b = nearPart b + farPart b`:

* `nearPart b = cut • b` is integrable (`nearPart_integrable`), since `|x|^{-1}` is locally
  integrable in three dimensions; derivatives of its heat smoothing fall on the Gaussian
  ("differentiating the Gaussian, without differentiating the singular datum at zero",
  tex lines 5919--5921);
* `farPart b = (1 - cut) • b` is smooth on all of space with every derivative bounded
  (`farPart_smooth`, `farPart_bddDerivs`), and equals `b` near every `|y| > 1/2`
  (`farPart_eventuallyEq`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Metric
open scoped ContDiff Topology

namespace UnforcedLeray.B0306

/-- The fixed cutoff: `1` on `|x| ≤ 1/4`, `0` on `|x| ≥ 1/2`. -/
def cut : ContDiffBump (0 : Space) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

theorem cut_smooth : ContDiff ℝ ∞ (cut : Space → ℝ) := cut.contDiff

theorem cut_eq_one {x : Space} (hx : ‖x‖ ≤ 1 / 4) : cut x = 1 :=
  cut.one_of_mem_closedBall (mem_closedBall_zero_iff.2 hx)

theorem cut_eq_zero {x : Space} (hx : 1 / 2 ≤ ‖x‖) : cut x = 0 :=
  cut.zero_of_le_dist (by rw [dist_zero_right]; exact hx)

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The part of `b` near the origin. -/
def nearPart (b : Space → F) (x : Space) : F := cut x • b x

/-- The part of `b` away from the origin. -/
def farPart (b : Space → F) (x : Space) : F := (1 - cut x) • b x

theorem nearPart_add_farPart (b : Space → F) (x : Space) :
    nearPart b x + farPart b x = b x := by
  simp only [nearPart, farPart, sub_smul, one_smul, add_sub_cancel]

theorem nearPart_eq_zero (b : Space → F) {x : Space} (hx : 1 / 2 ≤ ‖x‖) : nearPart b x = 0 := by
  simp only [nearPart, cut_eq_zero hx, zero_smul]

theorem norm_nearPart_le (b : Space → F) (x : Space) : ‖nearPart b x‖ ≤ ‖b x‖ := by
  rw [nearPart, norm_smul, Real.norm_of_nonneg cut.nonneg]
  exact mul_le_of_le_one_left (norm_nonneg _) cut.le_one

theorem farPart_eventuallyEq_zero (b : Space → F) {x : Space} (hx : ‖x‖ < 1 / 4) :
    farPart b =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hx)] with z hz
  simp only [farPart, cut_eq_one (mem_ball_zero_iff.1 hz).le, sub_self, zero_smul]

theorem farPart_eventuallyEq (b : Space → F) {y : Space} (hy : 1 / 2 < ‖y‖) :
    farPart b =ᶠ[𝓝 y] b := by
  have hopen : IsOpen {z : Space | 1 / 2 < ‖z‖} := isOpen_lt continuous_const continuous_norm
  filter_upwards [hopen.mem_nhds hy] with z hz
  simp only [farPart, cut_eq_zero (le_of_lt hz), sub_zero, one_smul]

/-- The bound constants of an inverse-distance field are nonnegative. -/
theorem bound_nonneg {b : Space → F} {C : ℕ → ℝ}
    (hC : ∀ j x, x ≠ 0 → ‖iteratedFDeriv ℝ j b x‖ ≤ C j / ‖x‖ ^ (j + 1)) (j : ℕ) :
    0 ≤ C j := by
  have hn : ‖(EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : Space)‖ = 1 := by simp
  have he : (EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : Space) ≠ 0 := by
    intro h; rw [h, norm_zero] at hn; exact zero_ne_one hn
  have h := (norm_nonneg _).trans (hC j _ he)
  rw [hn, one_pow, div_one] at h
  exact h

theorem aestronglyMeasurable_of_contDiffOn {b : Space → F} (hb : ContDiffOn ℝ ∞ b {0}ᶜ) :
    AEStronglyMeasurable b volume := by
  have h := hb.continuousOn.aestronglyMeasurable (μ := volume)
    isOpen_compl_singleton.measurableSet
  rwa [restrict_compl_singleton] at h

/-- The near part is integrable: `|x|^{-1}` is locally integrable in three dimensions. -/
theorem nearPart_integrable {b : Space → F} (hb : ContDiffOn ℝ ∞ b {0}ᶜ) {C : ℕ → ℝ}
    (hC : ∀ j x, x ≠ 0 → ‖iteratedFDeriv ℝ j b x‖ ≤ C j / ‖x‖ ^ (j + 1)) :
    Integrable (nearPart b) := by
  have hm : AEStronglyMeasurable (nearPart b) volume :=
    cut_smooth.continuous.aestronglyMeasurable.smul (aestronglyMeasurable_of_contDiffOn hb)
  have hfin : Module.finrank ℝ Space = 3 := finrank_euclideanSpace_fin
  have hloc : LocallyIntegrable (nearPart b) volume := by
    refine locallyIntegrable_of_norm_le_rpow (C := C 0) (α := 1) ?_ ?_ ?_ hm
    · rw [hfin]; norm_num
    · rw [hfin]; norm_num
    · filter_upwards [Measure.ae_ne volume (0 : Space)] with x hx
      calc ‖nearPart b x‖ ≤ ‖b x‖ := norm_nearPart_le b x
        _ ≤ C 0 / ‖x‖ := by simpa using hC 0 x hx
        _ = C 0 * ‖x‖ ^ (-(1 : ℝ)) := by rw [Real.rpow_neg_one, div_eq_mul_inv]
  have hint : IntegrableOn (nearPart b) (closedBall 0 (1 / 2)) volume :=
    hloc.integrableOn_isCompact (isCompact_closedBall 0 _)
  refine hint.integrable_of_forall_notMem_eq_zero fun x hx => nearPart_eq_zero b ?_
  rw [mem_closedBall_zero_iff, not_le] at hx
  exact hx.le

/-- The far part is smooth on all of space. -/
theorem farPart_smooth {b : Space → F} (hb : ContDiffOn ℝ ∞ b {0}ᶜ) :
    ContDiff ℝ ∞ (farPart b) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    exact contDiffAt_const.congr_of_eventuallyEq
      (farPart_eventuallyEq_zero b (by rw [norm_zero]; norm_num))
  · have hbx : ContDiffAt ℝ ∞ b x := hb.contDiffAt (isOpen_compl_singleton.mem_nhds hx)
    exact (contDiffAt_const.sub cut_smooth.contDiffAt).smul hbx

/-- Every derivative of `1 - cut` is bounded. -/
theorem one_sub_cut_bdd (i : ℕ) : ∃ A : ℝ, 0 ≤ A ∧
    ∀ x, ‖iteratedFDeriv ℝ i (fun x => 1 - (cut : Space → ℝ) x) x‖ ≤ A := by
  obtain ⟨B, hB⟩ := (cut_smooth.continuous_iteratedFDeriv (m := i)
    (by exact_mod_cast le_top)).bounded_above_of_compact_support
    (cut.hasCompactSupport.iteratedFDeriv i)
  refine ⟨1 + |B|, by positivity, fun x => ?_⟩
  have hsub : iteratedFDeriv ℝ i (fun x => 1 - (cut : Space → ℝ) x) x =
      iteratedFDeriv ℝ i (fun _ : Space => (1 : ℝ)) x - iteratedFDeriv ℝ i cut x :=
    iteratedFDeriv_sub_apply (f := fun _ : Space => (1 : ℝ)) (g := (cut : Space → ℝ))
      contDiffAt_const (cut_smooth.of_le (by exact_mod_cast le_top)).contDiffAt
  have hc : ‖iteratedFDeriv ℝ i (fun _ : Space => (1 : ℝ)) x‖ ≤ 1 := by
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp
    · rw [iteratedFDeriv_const_of_ne hi.ne']; simp
  rw [hsub]
  calc _ ≤ ‖iteratedFDeriv ℝ i (fun _ : Space => (1 : ℝ)) x‖ + ‖iteratedFDeriv ℝ i cut x‖ :=
        norm_sub_le _ _
    _ ≤ 1 + |B| := add_le_add hc ((hB x).trans (le_abs_self B))

/-- Every derivative of the far part is bounded on all of space. -/
theorem farPart_bddDerivs {b : Space → F} (hb : ContDiffOn ℝ ∞ b {0}ᶜ) {C : ℕ → ℝ}
    (hC : ∀ j x, x ≠ 0 → ‖iteratedFDeriv ℝ j b x‖ ≤ C j / ‖x‖ ^ (j + 1)) :
    BddDerivs (farPart b) := by
  intro k
  choose A hA0 hA using one_sub_cut_bdd
  refine ⟨max 0 (∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℝ) * A i * (C (k - i) / (1 / 4) ^ (k - i + 1))), fun x => ?_⟩
  by_cases hx : ‖x‖ < 1 / 4
  · rw [((farPart_eventuallyEq_zero b hx).iteratedFDeriv ℝ k).eq_of_nhds]
    simp
  · have hx0 : x ≠ 0 := by
      rintro rfl; rw [norm_zero] at hx; norm_num at hx
    have hmem : x ∈ ({0}ᶜ : Set Space) := hx0
    have hopen : IsOpen ({0}ᶜ : Set Space) := isOpen_compl_singleton
    have hf : ContDiffOn ℝ ∞ (fun x => 1 - (cut : Space → ℝ) x) {0}ᶜ :=
      (contDiff_const.sub cut_smooth).contDiffOn
    have key := norm_iteratedFDerivWithin_smul_le hf hb hopen.uniqueDiffOn hmem (n := k)
      (by exact_mod_cast le_top)
    rw [iteratedFDerivWithin_of_isOpen k hopen hmem] at key
    refine le_max_of_le_right (key.trans (Finset.sum_le_sum fun i _ => ?_))
    rw [iteratedFDerivWithin_of_isOpen i hopen hmem,
      iteratedFDerivWithin_of_isOpen (k - i) hopen hmem]
    have h2 : ‖iteratedFDeriv ℝ (k - i) b x‖ ≤ C (k - i) / (1 / 4) ^ (k - i + 1) :=
      (hC _ x hx0).trans (div_le_div_of_nonneg_left (bound_nonneg hC _) (by positivity)
        (pow_le_pow_left₀ (by norm_num) (not_lt.1 hx) _))
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hA i x) (Nat.cast_nonneg _)) h2
      (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hA0 i))

end UnforcedLeray.B0306
