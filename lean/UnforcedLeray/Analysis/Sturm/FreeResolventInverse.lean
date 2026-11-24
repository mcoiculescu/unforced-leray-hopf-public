import UnforcedLeray.Analysis.Sturm.FreeResolventWeak
import UnforcedLeray.Analysis.Sturm.FreeResolventSelfAdjoint

/-!
# The Green operator inverts the free differential expression on tests

The all-L² weak equation, tested against the conjugate of a smooth compactly
supported function, identifies the adjoint action of the differential
expression. Selfadjointness of the actual Green operator then proves its
inverse identity on these functions.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ComplexConjugate InnerProductSpace ContDiff

namespace UnforcedLeray.Sturm

open NonUniqueEuler.Sob

/-- The actual free Sturm differential expression. -/
def freeDifferential (L : ℝ) (u : ℝ → ℂ) : ℝ → ℂ :=
  fun x => -deriv (deriv u) x + (L : ℂ) ^ 2 * u x

theorem iterDirDeriv_two_eq (u : ℝ → ℂ) :
    iterDirDeriv (derivList 2) u = deriv (deriv u) := by
  rw [iterDirDeriv_derivList, show (2 : ℕ) = 1 + 1 from rfl,
    iteratedDeriv_succ, iteratedDeriv_one]

theorem contDiff_freeDifferential (L : ℝ) {u : ℝ → ℂ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (freeDifferential L u) := by
  have hd1 : ContDiff ℝ ∞ (deriv u) := (contDiff_infty_iff_deriv.mp hu).2
  have hd2 : ContDiff ℝ ∞ (deriv (deriv u)) := (contDiff_infty_iff_deriv.mp hd1).2
  exact hd2.neg.add (contDiff_const.mul hu)

theorem hasCompactSupport_freeDifferential (L : ℝ) {u : ℝ → ℂ}
    (hc : HasCompactSupport u) : HasCompactSupport (freeDifferential L u) := by
  have hm : HasCompactSupport (fun x => (L : ℂ) ^ 2 * u x) := hc.mul_left
  exact hc.deriv.deriv.neg.add hm

theorem memLp_freeDifferential (L : ℝ) {u : ℝ → ℂ} (hu : ContDiff ℝ ∞ u)
    (hc : HasCompactSupport u) : MemLp (freeDifferential L u) 2 (volume : Measure ℝ) :=
  (contDiff_freeDifferential L hu).continuous.memLp_of_hasCompactSupport
    (hasCompactSupport_freeDifferential L hc)

theorem inner_toLp_left_eq_integral (u : ℝ → ℂ) (hu : MemLp u 2 (volume : Measure ℝ))
    (f : ComplexL2) : ⟪hu.toLp u, f⟫_ℂ = ∫ x, f x * conj (u x) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hu.coeFn_toLp] with x hx
  simp only [RCLike.inner_apply, hx]

/-- Testing the actual weak equation against the conjugate test function. -/
theorem inner_freeDifferential_freeResolventOperator {L : ℝ} (hL : 0 < L)
    {u : ℝ → ℂ} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) (f : ComplexL2) :
    ⟪(memLp_freeDifferential L hu hc).toLp (freeDifferential L u),
      freeResolventOperator hL f⟫_ℂ =
      ⟪(hu.continuous.memLp_of_hasCompactSupport hc).toLp u, f⟫_ℂ := by
  have hut : IsTestFn univ u := ⟨hu, hc, subset_univ _⟩
  have huc : IsTestFn univ (fun x => conj (u x)) := by
    refine ⟨?_, ?_, subset_univ _⟩
    · exact Complex.conjCLE.contDiff.comp hu
    · exact hc.comp_left (by simp)
  have hd2 : MemLp (deriv (deriv u)) 2 (volume : Measure ℝ) := by
    simpa only [iterDirDeriv_two_eq] using testFn_memLp (hut.iterDirDeriv (derivList 2))
  let U : ComplexL2 := (testFn_memLp hut).toLp u
  let D : ComplexL2 := hd2.toLp (deriv (deriv u))
  have hstar : deriv (deriv (fun x => conj (u x))) = fun x => conj (deriv (deriv u) x) := by
    change deriv (deriv (fun x => star (u x))) = fun x => star (deriv (deriv u) x)
    simp only [deriv.star']
  have hw := freeResolventOperator_weak_two hL f (fun x => conj (u x)) huc
  rw [iterDirDeriv_two_eq, hstar] at hw
  simp only [derivList_length, neg_one_sq, one_mul] at hw
  have hpair : ⟪D, freeResolventOperator hL f⟫_ℂ =
      ⟪U, freeResolventSecondOperator hL f⟫_ℂ := by
    rw [inner_toLp_left_eq_integral, inner_toLp_left_eq_integral]
    exact hw
  have hsource : (memLp_freeDifferential L hu hc).toLp (freeDifferential L u) =
      -D + (L : ℂ) ^ 2 • U := by
    apply Lp.ext
    filter_upwards [(memLp_freeDifferential L hu hc).coeFn_toLp,
      Lp.coeFn_add (-D) ((L : ℂ) ^ 2 • U), Lp.coeFn_neg D,
      Lp.coeFn_smul ((L : ℂ) ^ 2) U, hd2.coeFn_toLp, (testFn_memLp hut).coeFn_toLp]
      with x hs ha hn hm hd hu'
    simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at ha hn hm
    change _ = _ at hs hd hu'
    rw [hs, ha, hn, hm, hd, hu']
    rfl
  have hpair' : ⟪D, freeResolventOperator hL f⟫_ℂ =
      (L : ℂ) ^ 2 * ⟪U, freeResolventOperator hL f⟫_ℂ - ⟪U, f⟫_ℂ := by
    rw [hpair]
    change ⟪U, (L : ℂ) ^ 2 • freeResolventOperator hL f - f⟫_ℂ = _
    rw [inner_sub_right, inner_smul_right]
  rw [hsource, inner_add_left, inner_neg_left, inner_smul_left, hpair']
  simp only [map_pow, Complex.conj_ofReal]
  change -((L : ℂ) ^ 2 * ⟪U, freeResolventOperator hL f⟫_ℂ - ⟪U, f⟫_ℂ) +
    (L : ℂ) ^ 2 * ⟪U, freeResolventOperator hL f⟫_ℂ = ⟪U, f⟫_ℂ
  ring

/-- The actual Green operator is an inverse of `-u'' + L²u` on smooth
compactly supported functions. -/
theorem freeResolventOperator_inverse_smoothCompact {L : ℝ} (hL : 0 < L)
    {u : ℝ → ℂ} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) :
    freeResolventOperator hL
        ((memLp_freeDifferential L hu hc).toLp (freeDifferential L u)) =
      (hu.continuous.memLp_of_hasCompactSupport hc).toLp u := by
  apply ext_inner_right ℂ
  intro f
  exact ((freeResolventOperator_isSelfAdjoint hL).isSymmetric _ _).trans
    (inner_freeDifferential_freeResolventOperator hL hu hc f)

end UnforcedLeray.Sturm
