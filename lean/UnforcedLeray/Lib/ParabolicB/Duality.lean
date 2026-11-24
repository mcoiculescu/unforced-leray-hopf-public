import UnforcedLeray.Lib.Parabolic
import UnforcedLeray.Lib.CZCore

/-!
# The backward test in `L^{q'}`, and the identification for `L^q` solutions (INF02 T8)


target T8 ("distributional lemma eq:11: … identification"), on the `L^q` bounds of target T7
(`Lib/Parabolic/LqBound`). Manuscript: the lemma eq:free-stress-11 (`paper/main.tex` lines
7447–7477, blueprint unit B0423), proof lines 7472–7476 ("to identify this operator with the
distributional second derivatives …").

* `backOp_eLpNorm_le`: the transpose `backOp = reflL2 ∘ secondDerivOp ∘ reflL2` (at `ν = 1`) is
  bounded on `L² ∩ L^p`, `1 < p < ∞` (time reversal preserves every `L^p` norm).
* `memLp_backTest_rpow`: for a test `φ`, the backward test `Ψ = backTest 1 i j φ` lies in every
  `L^p`, `1 < p < ∞`; so does `∂_k Ψ = backTest 1 i j (∂_k φ)` (`memLp_sD_backTest_rpow`).
* `integral_mul_sD2_eq_of_integrable`: the cutoff argument of `Parabolic.integral_mul_sD2_eq`
  (`Lib/Parabolic/QTwo`) with the `L²` hypotheses replaced by the integrability of the products
  that occur: `∫ u ∂_i∂_jφ = ∫ F Ψ` whenever `(∂_t - νΔ)u = F` against tests.
* `integral_mul_sD2_eq_rpow`: the same for `u, F ∈ L^q`, `1 < q < ∞`, at `ν = 1` (Hölder with
  `Ψ, ∇Ψ ∈ L^{q'}`).

No compact time support of `u` is needed here: the backward test is in `L^{q'}` globally.
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.Parabolic

open MeasureTheory Real Set Filter
open scoped ENNReal NNReal ContDiff Topology

open UnforcedLeray.Gaussian (Euc gaussKernel)

variable {d : ℕ}

section BackBound

theorem eLpNorm_reflL2 (G : Lp ℝ 2 (volume : Measure (PS d))) (p : ℝ≥0∞) :
    eLpNorm (reflL2 d G) p volume = eLpNorm G p volume := by
  rw [eLpNorm_congr_ae (coeFn_reflL2 G)]
  exact eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable G) measurePreserving_trev

theorem memLp_reflL2 {G : Lp ℝ 2 (volume : Measure (PS d))} {p : ℝ≥0∞}
    (hG : MemLp G p volume) : MemLp (reflL2 d G) p volume :=
  ⟨Lp.aestronglyMeasurable _, by rw [eLpNorm_reflL2]; exact hG.2⟩

/-- **`L^p` bound for the transpose** (at `ν = 1`), `1 < p < ∞`: `backOp` is the time
reflection of `secondDerivOp`, so `secondDerivOp_eLpNorm_le` transfers. -/
theorem backOp_eLpNorm_le (i j : Fin d) {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ≥0, ∀ G : Lp ℝ 2 (volume : Measure (PS d)), MemLp G (ENNReal.ofReal p) volume →
      eLpNorm (backOp one_pos i j G) (ENNReal.ofReal p) volume ≤
        C * eLpNorm G (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC⟩ := secondDerivOp_eLpNorm_le (d := d) i j hp
  refine ⟨C, fun G hG => ?_⟩
  have e : backOp one_pos i j G = reflL2 d (secondDerivOp one_pos i j (reflL2 d G)) := rfl
  rw [e, eLpNorm_reflL2, ← eLpNorm_reflL2 G]
  exact hC _ (memLp_reflL2 hG)

/-- The backward test of a test function lies in `L^p`, `1 < p < ∞` (at `ν = 1`). -/
theorem memLp_backTest_rpow {φ : PS d → ℝ} (hφ : IsSTTest φ) (i j : Fin d) {p : ℝ}
    (hp : 1 < p) : MemLp (backTest 1 i j φ) (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC⟩ := backOp_eLpNorm_le (d := d) i j hp
  have h2 := memLp_backTest one_pos hφ i j
  have hφp : MemLp ((hφ.memLp 2).toLp φ) (ENNReal.ofReal p) volume :=
    (hφ.memLp _).ae_eq (hφ.memLp 2).coeFn_toLp.symm
  have hb := hC _ hφp
  rw [backOp_toLp one_pos hφ i j, eLpNorm_congr_ae h2.coeFn_toLp] at hb
  refine ⟨h2.1, hb.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top ?_)⟩
  rw [eLpNorm_congr_ae (hφ.memLp 2).coeFn_toLp]
  exact (hφ.memLp _).2

/-- `∂_k` of the backward test lies in `L^p`, `1 < p < ∞` (at `ν = 1`). -/
theorem memLp_sD_backTest_rpow {φ : PS d → ℝ} (hφ : IsSTTest φ) (i j k : Fin d) {p : ℝ}
    (hp : 1 < p) : MemLp (sD k (backTest 1 i j φ)) (ENNReal.ofReal p) volume := by
  rw [sD_backTest one_pos hφ i j k]
  exact memLp_backTest_rpow (hφ.dirD _) i j hp

end BackBound

section Identification

variable {ν : ℝ} {u F : PS d → ℝ}

/-- **The identification, integrability form.** If `(∂_t - νΔ)u = F` against tests, then
`∫ u ∂_i∂_j φ = ∫ F · backTest ν i j φ` for every test `φ`, provided the products of `u` with
tests, with `Ψ = backTest ν i j φ` and with `∂_k Ψ`, and of `F` with `Ψ`, are integrable.
(Same cutoff argument as `Parabolic.integral_mul_sD2_eq`, `Lib/Parabolic/QTwo`.) -/
theorem integral_mul_sD2_eq_of_integrable (hν : 0 < ν) (hu : AEStronglyMeasurable u volume)
    (hF : AEStronglyMeasurable F volume)
    (heq : ∀ φ : PS d → ℝ, IsSTTest φ →
      ∫ X, u X * (-tD φ X - ν * sLap φ X) = ∫ X, F X * φ X)
    (iut : ∀ g : PS d → ℝ, IsSTTest g → Integrable (fun X => u X * g X) volume)
    {φ : PS d → ℝ} (hφ : IsSTTest φ) (i j : Fin d)
    (iuΨ0 : Integrable (fun X => u X * backTest ν i j φ X) volume)
    (iuk0 : ∀ k : Fin d, Integrable (fun X => u X * sD k (backTest ν i j φ) X) volume)
    (iFΨ : Integrable (fun X => F X * backTest ν i j φ X) volume) :
    ∫ X, u X * sD2 i j φ X = ∫ X, F X * backTest ν i j φ X := by
  set Ψ := backTest ν i j φ with hΨdef
  have hΨ : ContDiff ℝ ∞ Ψ := contDiff_backTest hν hφ i j
  obtain ⟨K, hK0, hK⟩ := exists_scut_bound (d := d) ν
  have iuφ : Integrable (fun X => u X * sD2 i j φ X) volume := iut _ (hφ.sD2 i j)
  have iuΨ : Integrable (fun X => |u X| * |Ψ X|) volume := iuΨ0.abs.congr
    (Eventually.of_forall fun X => by simp [abs_mul])
  have iuk : ∀ k : Fin d, Integrable (fun X => |u X| * |sD k Ψ X|) volume := fun k =>
    (iuk0 k).abs.congr (Eventually.of_forall fun X => by simp [abs_mul])
  set M : ℝ := ∫ X, (|u X| * |Ψ X| + 2 * |ν| * ∑ k : Fin d, |u X| * |sD k Ψ X|) with hM
  have iM : Integrable (fun X => |u X| * |Ψ X| + 2 * |ν| * ∑ k : Fin d, |u X| * |sD k Ψ X|)
      volume := iuΨ.add ((integrable_finsetSum _ fun k _ => iuk k).const_mul _)
  have hχ : ∀ n : ℕ, IsSTTest (fun X => scut n X * Ψ X) := fun n =>
    ⟨(scut_isSTTest n).1.mul hΨ, (scut_isSTTest n).2.mul_right⟩
  set R : ℕ → PS d → ℝ := fun n X => Ψ X * (-tD (scut n) X - ν * sLap (scut n) X) -
    2 * ν * ∑ k : Fin d, sD k (scut n) X * sD k Ψ X with hR
  have hRb : ∀ (n : ℕ) (X : PS d), ‖u X * R n X‖ ≤ K / ((n : ℝ) + 1) *
      (|u X| * |Ψ X| + 2 * |ν| * ∑ k : Fin d, |u X| * |sD k Ψ X|) := by
    intro n X
    obtain ⟨h1, h2⟩ := hK n X
    have hn : (0 : ℝ) ≤ K / ((n : ℝ) + 1) := by positivity
    rw [Real.norm_eq_abs, abs_mul]
    have hRX : |R n X| ≤ K / ((n : ℝ) + 1) *
        (|Ψ X| + 2 * |ν| * ∑ k : Fin d, |sD k Ψ X|) := by
      simp only [hR]
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_mul, abs_mul, abs_two]
      have hs : |∑ k : Fin d, sD k (scut n) X * sD k Ψ X| ≤
          K / ((n : ℝ) + 1) * ∑ k : Fin d, |sD k Ψ X| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (h2 k) (abs_nonneg _)
      calc |Ψ X| * |-tD (scut n) X - ν * sLap (scut n) X| +
            2 * |ν| * |∑ k : Fin d, sD k (scut n) X * sD k Ψ X|
          ≤ |Ψ X| * (K / ((n : ℝ) + 1)) +
            2 * |ν| * (K / ((n : ℝ) + 1) * ∑ k : Fin d, |sD k Ψ X|) := by
            gcongr
        _ = K / ((n : ℝ) + 1) * (|Ψ X| + 2 * |ν| * ∑ k : Fin d, |sD k Ψ X|) := by ring
    calc |u X| * |R n X| ≤ |u X| * (K / ((n : ℝ) + 1) *
          (|Ψ X| + 2 * |ν| * ∑ k : Fin d, |sD k Ψ X|)) :=
          mul_le_mul_of_nonneg_left hRX (abs_nonneg _)
      _ = K / ((n : ℝ) + 1) *
          (|u X| * |Ψ X| + 2 * |ν| * ∑ k : Fin d, |u X| * |sD k Ψ X|) := by
          rw [← Finset.mul_sum]; ring
  have hRc : ∀ n : ℕ, Continuous (R n) := by
    intro n
    rw [hR]
    have hs := scut_isSTTest (d := d) n
    have hsl : Continuous (sLap (scut (d := d) n)) := by
      have e : sLap (scut (d := d) n) = fun X => ∑ k : Fin d, sD2 k k (scut n) X := rfl
      rw [e]; exact continuous_finsetSum _ fun k _ => (hs.sD2 k k).continuous
    exact (hΨ.continuous.mul ((hs.dirD tdir).continuous.neg.sub (continuous_const.mul hsl))).sub
      (continuous_const.mul (continuous_finsetSum _ fun k _ =>
        (hs.dirD (sdir k)).continuous.mul (contDiff_dirD hΨ _).continuous))
  have iR : ∀ n : ℕ, Integrable (fun X => u X * R n X) volume := fun n =>
    (iM.const_mul (K / ((n : ℝ) + 1))).mono' (hu.mul (hRc n).aestronglyMeasurable)
      (Eventually.of_forall fun X => hRb n X)
  have hsplit : ∀ n : ℕ, ∫ X, F X * (scut n X * Ψ X) =
      (∫ X, u X * (scut n X * sD2 i j φ X)) + ∫ X, u X * R n X := by
    intro n
    rw [← heq _ (hχ n)]
    have hpt : ∀ X, u X * (-tD (fun Y => scut n Y * Ψ Y) X -
        ν * sLap (fun Y => scut n Y * Ψ Y) X) = u X * (scut n X * sD2 i j φ X) + u X * R n X := by
      intro X
      rw [heatAdj_mul (scut_isSTTest n).1 hΨ ν X, hΨdef, backTest_heatAdj hν hφ i j X]
      simp only [hR]; ring
    have i1 : Integrable (fun X => u X * (scut n X * sD2 i j φ X)) volume := by
      have ht : IsSTTest (fun X => scut n X * sD2 i j φ X) :=
        ⟨(scut_isSTTest n).1.mul (hφ.sD2 i j).1, (hφ.sD2 i j).2.mul_left⟩
      exact iut _ ht
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_add i1 (iR n)]
  have L1 : Tendsto (fun n : ℕ => ∫ X, F X * (scut n X * Ψ X)) atTop (𝓝 (∫ X, F X * Ψ X)) := by
    refine tendsto_integral_of_dominated_convergence (fun X => |F X * Ψ X|)
      (fun n => hF.mul ((scut_isSTTest n).continuous.mul hΨ.continuous).aestronglyMeasurable)
      iFΨ.abs (fun n => Eventually.of_forall fun X => ?_) (Eventually.of_forall fun X => ?_)
    · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg (scut_nonneg n X),
        mul_left_comm]
      exact mul_le_of_le_one_left (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (scut_le_one n X)
    · have := ((tendsto_scut X).mul_const (Ψ X)).const_mul (F X)
      simpa using this
  have L2 : Tendsto (fun n : ℕ => ∫ X, u X * (scut n X * sD2 i j φ X)) atTop
      (𝓝 (∫ X, u X * sD2 i j φ X)) := by
    refine tendsto_integral_of_dominated_convergence (fun X => |u X * sD2 i j φ X|)
      (fun n => hu.mul ((scut_isSTTest n).continuous.mul
        (hφ.sD2 i j).continuous).aestronglyMeasurable)
      iuφ.abs (fun n => Eventually.of_forall fun X => ?_) (Eventually.of_forall fun X => ?_)
    · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg (scut_nonneg n X),
        mul_left_comm]
      exact mul_le_of_le_one_left (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (scut_le_one n X)
    · have := ((tendsto_scut X).mul_const (sD2 i j φ X)).const_mul (u X)
      simpa using this
  have L3 : Tendsto (fun n : ℕ => ∫ X, u X * R n X) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ => K * M * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (K * M)
    refine squeeze_zero_norm (fun n => ?_) hlim
    refine (norm_integral_le_of_norm_le ((iM.const_mul (K / ((n : ℝ) + 1))))
      (Eventually.of_forall fun X => hRb n X)).trans (le_of_eq ?_)
    rw [integral_const_mul, ← hM]; ring
  have L4 := L2.add L3
  rw [add_zero] at L4
  have L5 : Tendsto (fun n : ℕ => ∫ X, F X * (scut n X * Ψ X)) atTop
      (𝓝 (∫ X, u X * sD2 i j φ X)) := L4.congr fun n => (hsplit n).symm
  exact tendsto_nhds_unique L5 L1

/-- The conjugate exponent as a Hölder triple in `ℝ≥0∞`. -/
theorem holderTriple_ofReal {q : ℝ} (hq : 1 < q) :
    ENNReal.HolderTriple (ENNReal.ofReal q) (ENNReal.ofReal q.conjExponent) 1 := by
  have hpq : q.HolderConjugate q.conjExponent := Real.HolderConjugate.conjExponent hq
  have : ENNReal.HolderConjugate (ENNReal.ofReal q) (ENNReal.ofReal q.conjExponent) :=
    hpq.ennrealOfReal
  infer_instance

/-- An `L^q` function times a test is integrable. -/
theorem integrable_mul_test_of_memLp {q : ℝ} (hq : 1 < q) {u : PS d → ℝ}
    (hu : MemLp u (ENNReal.ofReal q) volume) {g : PS d → ℝ} (hg : IsSTTest g) :
    Integrable (fun X => u X * g X) volume := by
  have := holderTriple_ofReal hq
  exact hu.integrable_mul (hg.memLp (ENNReal.ofReal q.conjExponent))

/-- **The identification for `L^q` solutions** (`ν = 1`, `1 < q < ∞`). If `u, F ∈ L^q` and
`(∂_t - Δ)u = F` against tests, then `∫ u ∂_i∂_j φ = ∫ F · backTest 1 i j φ` for every
test `φ`. -/
theorem integral_mul_sD2_eq_rpow {q : ℝ} (hq : 1 < q) (hu : MemLp u (ENNReal.ofReal q) volume)
    (hF : MemLp F (ENNReal.ofReal q) volume)
    (heq : ∀ φ : PS d → ℝ, IsSTTest φ →
      ∫ X, u X * (-tD φ X - 1 * sLap φ X) = ∫ X, F X * φ X)
    {φ : PS d → ℝ} (hφ : IsSTTest φ) (i j : Fin d) :
    ∫ X, u X * sD2 i j φ X = ∫ X, F X * backTest 1 i j φ X := by
  have := holderTriple_ofReal hq
  have hq' : 1 < q.conjExponent := (Real.HolderConjugate.conjExponent hq).symm.lt
  exact integral_mul_sD2_eq_of_integrable one_pos hu.1 hF.1 heq
    (fun g hg => integrable_mul_test_of_memLp hq hu hg) hφ i j
    (hu.integrable_mul (memLp_backTest_rpow hφ i j hq'))
    (fun k => hu.integrable_mul (memLp_sD_backTest_rpow hφ i j k hq'))
    (hF.integrable_mul (memLp_backTest_rpow hφ i j hq'))

end Identification

end UnforcedLeray.Parabolic
