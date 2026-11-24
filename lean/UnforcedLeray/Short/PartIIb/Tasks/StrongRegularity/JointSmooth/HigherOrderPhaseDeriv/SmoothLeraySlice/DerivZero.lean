import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3_1_2_1
import UnforcedLeray.Lib.LerayLp.Helmholtz
import UnforcedLeray.Lib.SobolevB.Mollify
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Data.Fin.Tuple.Basic

/-!
# `PartII-b:S3/1/2/1/2` (`SmoothLeraySliceDerivZero`, SP 2552, 2559-2562)

Source of record: `the November 2 reference manuscript`
(SP), lines 2552 and 2559-2562:
"These estimates are uniform in phase; the bounded Cartesian Leray map preserves them in $W^{k,p}$.
... On positive physical-time compact intervals the resulting $C_\tau W^{k,4}$ regularity and the
projected equation give all time derivatives".

Proves `smoothLeraySliceDerivZero_proof : UnforcedLeray.Short.IIb.SmoothLeraySliceDerivZero`:
given `hRep : SmoothLerayRepExists`, if `F, F' : ℝ → SpatialField` lie in
`IsUniformSmoothL4SliceFamily` and `HasPhaseJetDeriv F F'`, then for all `(τ, y) ∈ ℝ × Space`,
`HasDerivAt (fun τ' : ℝ => smoothLeraySlice F τ' y) (smoothLeraySlice F' τ y) τ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff BigOperators

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace

local instance fact_one_le_four_dz : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

namespace SmoothLeraySliceDerivZeroAux

/-! ## 1. Parametric differentiation of spatial pairings and `L⁴(ℝ³)` mean value bound -/

theorem integrable_inner_of_bounded {f ψ : SpatialField}
    (hf_cont : Continuous f) {M₀ : ℝ} (hf_bdd : ∀ x : Space, ‖f x‖ ≤ M₀)
    (hψ : Integrable ψ volume) :
    Integrable (fun x : Space => inner ℝ (f x) (ψ x)) volume := by
  set M₀' : ℝ := max M₀ 0
  refine (hψ.norm.const_mul M₀').mono' (hf_cont.aestronglyMeasurable.inner hψ.aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  calc ‖inner ℝ (f x) (ψ x)‖
      ≤ ‖f x‖ * ‖ψ x‖ := norm_inner_le_norm _ _
    _ ≤ M₀' * ‖ψ x‖ :=
        mul_le_mul_of_nonneg_right ((hf_bdd x).trans (le_max_left M₀ 0)) (norm_nonneg _)

/-- Parametric differentiation of `s ↦ ∫ x, ⟨H s x, ψ x⟩` for `ψ ∈ L¹(ℝ³)`. -/
theorem hasDerivAt_integral_inner_of_integrable
    (H H' : ℝ → SpatialField)
    (hH_cont : ∀ t : ℝ, Continuous (H t))
    (hH_bdd : ∀ t : ℝ, ∃ M₀ : ℝ, ∀ x : Space, ‖H t x‖ ≤ M₀)
    (hH'_cont : ∀ t : ℝ, Continuous (H' t))
    {M_inf : ℝ} (hH'_bdd : ∀ (t : ℝ) (x : Space), ‖H' t x‖ ≤ M_inf)
    (hderiv : ∀ (t : ℝ) (x : Space), HasDerivAt (fun s : ℝ => H s x) (H' t x) t)
    {ψ : SpatialField} (hψ : Integrable ψ volume) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ x : Space, inner ℝ (H s x) (ψ x))
      (∫ x : Space, inner ℝ (H' t x) (ψ x)) t := by
  obtain ⟨M₀, hM₀⟩ := hH_bdd t
  have hF_meas : ∀ s : ℝ, AEStronglyMeasurable (fun x : Space => inner ℝ (H s x) (ψ x)) volume :=
    fun s => (hH_cont s).aestronglyMeasurable.inner hψ.aestronglyMeasurable
  have hF_int : Integrable (fun x : Space => inner ℝ (H t x) (ψ x)) volume :=
    integrable_inner_of_bounded (hH_cont t) hM₀ hψ
  have hF'_meas : AEStronglyMeasurable (fun x : Space => inner ℝ (H' t x) (ψ x)) volume :=
    (hH'_cont t).aestronglyMeasurable.inner hψ.aestronglyMeasurable
  have hbound : ∀ (x : Space) (s : ℝ), s ∈ (Set.univ : Set ℝ) →
      ‖inner ℝ (H' s x) (ψ x)‖ ≤ M_inf * ‖ψ x‖ := by
    intro x s _
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hH'_bdd s x) (norm_nonneg _))
  have hB : Integrable (fun x : Space => M_inf * ‖ψ x‖) volume := hψ.norm.const_mul M_inf
  have hdiff : ∀ (x : Space) (s : ℝ), s ∈ (Set.univ : Set ℝ) →
      HasDerivAt (fun r : ℝ => inner ℝ (H r x) (ψ x)) (inner ℝ (H' s x) (ψ x)) s := by
    intro x s _
    simpa using (hderiv s x).inner ℝ (hasDerivAt_const s (ψ x))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s x => inner ℝ (H s x) (ψ x))
    (F' := fun s x => inner ℝ (H' s x) (ψ x))
    (bound := fun x => M_inf * ‖ψ x‖)
    univ_mem (Eventually.of_forall hF_meas) hF_int hF'_meas
    (Eventually.of_forall hbound) hB (Eventually.of_forall hdiff)).2

/-- `L⁴(ℝ³)` mean value inequality for a phase-indexed spatial field `H` with phase derivative `H'`. -/
theorem eLpNorm_sub_le_of_hasDerivAt
    (H H' : ℝ → SpatialField)
    (hH_cont : ∀ t : ℝ, Continuous (H t))
    (hH_bdd : ∀ t : ℝ, ∃ M₀ : ℝ, ∀ x : Space, ‖H t x‖ ≤ M₀)
    (hH_l4 : ∀ t : ℝ, MemLp (H t) 4 volume)
    (hH'_cont : ∀ t : ℝ, Continuous (H' t))
    {M_inf : ℝ} (hH'_bdd : ∀ (t : ℝ) (x : Space), ‖H' t x‖ ≤ M_inf)
    {M_4 : ℝ} (hM_4 : 0 ≤ M_4)
    (hH'_l4 : ∀ t : ℝ, eLpNorm (H' t) 4 volume ≤ ENNReal.ofReal M_4)
    (hderiv : ∀ (t : ℝ) (x : Space), HasDerivAt (fun s : ℝ => H s x) (H' t x) t)
    (a b : ℝ) :
    eLpNorm (H b - H a) 4 volume ≤ ENNReal.ofReal (M_4 * ‖b - a‖) := by
  set u : SpatialField := H b - H a
  have hu : MemLp u 4 volume := (hH_l4 b).sub (hH_l4 a)
  have hu_cont : Continuous u := (hH_cont b).sub (hH_cont a)
  set A : ℝ≥0∞ := ∫⁻ x : Space, ‖u x‖ₑ ^ (4 : ℝ)
  have heLp : eLpNorm u 4 volume = A ^ (1 / 4 : ℝ) := by
    simpa [A] using eLpNorm_eq_lintegral_rpow_enorm_toReal (f := u) (μ := volume)
      (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)
  have hAfin : A ≠ ⊤ := by
    have hlt : A ^ (1 / 4 : ℝ) < ⊤ := by rw [← heLp]; exact hu.eLpNorm_lt_top
    have hpow : (A ^ (1 / 4 : ℝ)) ^ (4 : ℝ) < ⊤ :=
      ENNReal.rpow_lt_top_of_nonneg (by norm_num) hlt.ne
    rw [← ENNReal.rpow_mul, one_div_mul_cancel (by norm_num), ENNReal.rpow_one] at hpow
    exact hpow.ne
  set K : ℕ → Set Space := fun n => Metric.closedBall (0 : Space) n
  set ψ₀ : SpatialField := fun x => ‖u x‖ ^ 2 • u x
  set ψ : ℕ → SpatialField := fun n => (K n).indicator ψ₀
  have hψ₀_cont : Continuous ψ₀ := (hu_cont.norm.pow 2).smul hu_cont
  have hψ_int : ∀ n : ℕ, Integrable (ψ n) volume := fun n =>
    (integrable_indicator_iff measurableSet_closedBall).2
      (hψ₀_cont.continuousOn.integrableOn_compact (isCompact_closedBall (0 : Space) n))
  have hψ₀_enorm : ∀ x : Space, ‖ψ₀ x‖ₑ = ‖u x‖ₑ ^ (3 : ℝ) := by
    intro x
    have hnorm : ‖ψ₀ x‖ = ‖u x‖ ^ (3 : ℕ) := by
      dsimp [ψ₀]
      rw [norm_smul, Real.norm_of_nonneg (sq_nonneg _)]
      ring
    rw [← ofReal_norm, hnorm, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm,
      ← ENNReal.rpow_natCast]
    norm_num
  have hψ_rpow_le : ∀ (n : ℕ) (x : Space), ‖ψ n x‖ₑ ^ (4 / 3 : ℝ) ≤ ‖u x‖ₑ ^ (4 : ℝ) := by
    intro n x
    dsimp only [ψ]
    by_cases hx : x ∈ K n
    · rw [Set.indicator_of_mem hx, hψ₀_enorm x, ← ENNReal.rpow_mul]
      norm_num
    · rw [Set.indicator_of_notMem hx, enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num)]
      exact zero_le
  have hH'_enorm : ∀ t : ℝ, (∫⁻ x : Space, ‖H' t x‖ₑ ^ (4 : ℝ)) ^ (1 / 4 : ℝ) ≤
      ENNReal.ofReal M_4 := by
    intro t
    have h1 : eLpNorm (H' t) 4 volume = (∫⁻ x : Space, ‖H' t x‖ₑ ^ (4 : ℝ)) ^ (1 / 4 : ℝ) := by
      simpa using eLpNorm_eq_lintegral_rpow_enorm_toReal (f := H' t) (μ := volume)
        (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)
    rw [← h1]
    exact hH'_l4 t
  have hψ_lq : ∀ n : ℕ, (∫⁻ x : Space, ‖ψ n x‖ₑ ^ (4 / 3 : ℝ)) ^ (1 / (4 / 3 : ℝ)) ≤
      A ^ (1 / (4 / 3 : ℝ)) := fun n =>
    ENNReal.rpow_le_rpow (lintegral_mono (hψ_rpow_le n)) (by positivity)
  have hderiv_bound_enorm : ∀ (n : ℕ) (t : ℝ),
      ‖∫ x : Space, inner ℝ (H' t x) (ψ n x)‖ₑ ≤ ENNReal.ofReal M_4 * A ^ (1 / (4 / 3 : ℝ)) := by
    intro n t
    have hpq : (4 : ℝ).HolderConjugate (4 / 3) :=
      Real.holderConjugate_iff.2 ⟨by norm_num, by norm_num⟩
    calc ‖∫ x : Space, inner ℝ (H' t x) (ψ n x)‖ₑ
        ≤ ∫⁻ x : Space, ‖inner ℝ (H' t x) (ψ n x)‖ₑ := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ x : Space, ‖H' t x‖ₑ * ‖ψ n x‖ₑ := by
          refine lintegral_mono fun x => ?_
          rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (norm_inner_le_norm _ _)
      _ ≤ (∫⁻ x : Space, ‖H' t x‖ₑ ^ (4 : ℝ)) ^ (1 / 4 : ℝ) *
            (∫⁻ x : Space, ‖ψ n x‖ₑ ^ (4 / 3 : ℝ)) ^ (1 / (4 / 3 : ℝ)) :=
          ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq
            (hH'_cont t).aestronglyMeasurable.enorm
            (hψ_int n).aestronglyMeasurable.enorm
      _ ≤ ENNReal.ofReal M_4 * A ^ (1 / (4 / 3 : ℝ)) :=
          mul_le_mul' (hH'_enorm t) (hψ_lq n)
  set D_enn : ℝ≥0∞ := ENNReal.ofReal M_4 * A ^ (1 / (4 / 3 : ℝ))
  have hD_fin : D_enn ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hAfin)
  set D : ℝ := D_enn.toReal
  have hderiv_bound_real : ∀ (n : ℕ) (t : ℝ),
      ‖∫ x : Space, inner ℝ (H' t x) (ψ n x)‖ ≤ D := by
    intro n t
    have h1 := ENNReal.toReal_mono hD_fin (hderiv_bound_enorm n t)
    rwa [toReal_enorm] at h1
  set fn : ℕ → Space → ℝ≥0∞ := fun n => (K n).indicator (fun x => ‖u x‖ₑ ^ (4 : ℝ))
  have hfn_bound : ∀ n : ℕ, ∫⁻ x : Space, fn n x ≤
      ENNReal.ofReal (M_4 * ‖b - a‖) * A ^ (1 / (4 / 3 : ℝ)) := by
    intro n
    have hmvt := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun s : ℝ => ∫ x : Space, inner ℝ (H s x) (ψ n x))
      (f' := fun s : ℝ => ∫ x : Space, inner ℝ (H' s x) (ψ n x))
      (C := D)
      (fun s _ => (hasDerivAt_integral_inner_of_integrable H H' hH_cont hH_bdd hH'_cont
        hH'_bdd hderiv (hψ_int n) s).hasDerivWithinAt)
      (fun s _ => hderiv_bound_real n s) (mem_univ a) (mem_univ b)
    obtain ⟨Mb, hMb⟩ := hH_bdd b
    obtain ⟨Ma, hMa⟩ := hH_bdd a
    have hint_b : Integrable (fun x : Space => inner ℝ (H b x) (ψ n x)) volume :=
      integrable_inner_of_bounded (hH_cont b) hMb (hψ_int n)
    have hint_a : Integrable (fun x : Space => inner ℝ (H a x) (ψ n x)) volume :=
      integrable_inner_of_bounded (hH_cont a) hMa (hψ_int n)
    have hsub_int : (∫ x : Space, inner ℝ (H b x) (ψ n x)) -
        (∫ x : Space, inner ℝ (H a x) (ψ n x)) =
        ∫ x : Space, inner ℝ (u x) (ψ n x) := by
      rw [← integral_sub hint_b hint_a]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp [u, inner_sub_left]
    rw [hsub_int] at hmvt
    have hinner_eq : ∀ x : Space,
        inner ℝ (u x) (ψ n x) = (K n).indicator (fun x => ‖u x‖ ^ (4 : ℕ)) x := by
      intro x
      by_cases hx : x ∈ K n
      · simp only [ψ, ψ₀, Set.indicator_of_mem hx, real_inner_smul_right,
          real_inner_self_eq_norm_sq]
        ring
      · simp [ψ, Set.indicator_of_notMem hx]
    have hnonneg : ∀ x : Space, 0 ≤ inner ℝ (u x) (ψ n x) := by
      intro x
      rw [hinner_eq x]
      by_cases hx : x ∈ K n
      · rw [Set.indicator_of_mem hx]; positivity
      · rw [Set.indicator_of_notMem hx]
    have hint_u : Integrable (fun x : Space => inner ℝ (u x) (ψ n x)) volume := by
      have heq : (fun x : Space => inner ℝ (u x) (ψ n x)) =
          (fun x : Space => inner ℝ (H b x) (ψ n x) - inner ℝ (H a x) (ψ n x)) := by
        funext x; simp [u, inner_sub_left]
      rw [heq]
      exact hint_b.sub hint_a
    have hlint : ∫⁻ x : Space, fn n x =
        ENNReal.ofReal (∫ x : Space, inner ℝ (u x) (ψ n x)) := by
      rw [ofReal_integral_eq_lintegral_ofReal hint_u (Eventually.of_forall hnonneg)]
      refine lintegral_congr fun x => ?_
      rw [hinner_eq x]
      by_cases hx : x ∈ K n
      · simp only [fn, Set.indicator_of_mem hx]
        rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ← ENNReal.rpow_natCast]
        norm_num
      · simp [fn, Set.indicator_of_notMem hx]
    have hle_real : ∫ x : Space, inner ℝ (u x) (ψ n x) ≤ D * ‖b - a‖ :=
      (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hmvt)
    calc ∫⁻ x : Space, fn n x
        = ENNReal.ofReal (∫ x : Space, inner ℝ (u x) (ψ n x)) := hlint
      _ ≤ ENNReal.ofReal (D * ‖b - a‖) := ENNReal.ofReal_le_ofReal hle_real
      _ = D_enn * ENNReal.ofReal ‖b - a‖ := by
          rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hD_fin]
      _ = ENNReal.ofReal (M_4 * ‖b - a‖) * A ^ (1 / (4 / 3 : ℝ)) := by
          dsimp [D_enn]
          rw [ENNReal.ofReal_mul hM_4]
          ring
  have hfn_meas : ∀ n : ℕ, Measurable (fn n) := fun n =>
    (hu_cont.enorm.measurable.pow_const (4 : ℝ)).indicator measurableSet_closedBall
  have hfn_mono : Monotone fn := by
    intro m n hmn x
    exact Set.indicator_le_indicator_of_subset
      (Metric.closedBall_subset_closedBall (Nat.cast_le.2 hmn)) (fun _ => zero_le) x
  have hfn_sup : ∀ x : Space, (⨆ n : ℕ, fn n x) = ‖u x‖ₑ ^ (4 : ℝ) := by
    intro x
    refine le_antisymm (iSup_le fun n => Set.indicator_le_self _ _ x) ?_
    refine le_iSup_of_le ⌈‖x‖⌉₊ ?_
    have hx : x ∈ K ⌈‖x‖⌉₊ := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact Nat.le_ceil ‖x‖
    dsimp only [fn]
    rw [Set.indicator_of_mem hx]
  have hA_key : A ≤ ENNReal.ofReal (M_4 * ‖b - a‖) * A ^ (1 / (4 / 3 : ℝ)) := by
    calc A = ∫⁻ x : Space, ⨆ n : ℕ, fn n x :=
          lintegral_congr fun x => (hfn_sup x).symm
      _ = ⨆ n : ℕ, ∫⁻ x : Space, fn n x := lintegral_iSup hfn_meas hfn_mono
      _ ≤ ENNReal.ofReal (M_4 * ‖b - a‖) * A ^ (1 / (4 / 3 : ℝ)) := iSup_le hfn_bound
  rw [heLp]
  by_cases hA0 : A = 0
  · rw [hA0, ENNReal.zero_rpow_of_pos (by positivity)]
    exact zero_le
  have hsplit : A ^ (1 / (4 : ℝ)) * A ^ (1 / (4 / 3 : ℝ)) = A := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have hq0 : A ^ (1 / (4 / 3 : ℝ)) ≠ 0 :=
    (ENNReal.rpow_pos (pos_iff_ne_zero.2 hA0) hAfin).ne'
  have hqt : A ^ (1 / (4 / 3 : ℝ)) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hAfin
  rw [← ENNReal.mul_le_mul_iff_left hq0 hqt, hsplit]
  exact hA_key

/-! ## 2. Coordinate words and uniform `W^{k,4}` / `C¹` bounds on difference quotients -/

/-- Coordinate index list associated with a tuple `w : Fin k → Fin 3`. -/
def coordList : ∀ {k : ℕ}, (Fin k → Fin 3) → List (Fin 3)
  | 0, _ => []
  | _ + 1, w => coordList (Fin.tail w) ++ [w 0]

/-- Pointwise bound on `iteratedFDeriv ℝ k H y` by the sum over all coordinate words of length `k`. -/
theorem norm_iteratedFDeriv_le_sum_coordList :
    ∀ (k : ℕ) {H : SpatialField}, ContDiff ℝ ∞ H → ∀ y : Space,
      ‖iteratedFDeriv ℝ k H y‖ ≤
        ∑ w : Fin k → Fin 3, ‖dirSpatialJet H ((coordList w).map coordinateVector) y‖
  | 0, H, _, y => by
      rw [Fintype.sum_unique]
      simp [coordList, norm_iteratedFDeriv_zero]
  | k + 1, H, hH, y => by
      calc ‖iteratedFDeriv ℝ (k + 1) H y‖
          ≤ ∑ i : Fin 3, ‖iteratedFDeriv ℝ k (dirSpatialJet H [coordinateVector i]) y‖ :=
            SmoothLeraySliceSub.norm_iteratedFDeriv_succ_le_sum_dirSpatialJet hH k y
        _ ≤ ∑ i : Fin 3, ∑ w' : Fin k → Fin 3,
              ‖dirSpatialJet (dirSpatialJet H [coordinateVector i])
                ((coordList w').map coordinateVector) y‖ :=
            Finset.sum_le_sum fun i _ =>
              norm_iteratedFDeriv_le_sum_coordList k
                (JointSmoothSub.contDiff_infty_dirSpatialJet hH [coordinateVector i]) y
        _ = ∑ p : Fin 3 × (Fin k → Fin 3),
              ‖dirSpatialJet H ((coordList (Fin.cons p.1 p.2)).map coordinateVector) y‖ := by
            rw [Fintype.sum_prod_type]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun w' _ => ?_
            simp [coordList, HigherPhaseSub.dirSpatialJet_append]
        _ = ∑ w : Fin (k + 1) → Fin 3,
              ‖dirSpatialJet H ((coordList w).map coordinateVector) y‖ :=
            Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (k + 1) => Fin 3))
              (fun w => ‖dirSpatialJet H ((coordList w).map coordinateVector) y‖)

/-- `L⁴(ℝ³)` norm bound on `iteratedFDeriv ℝ k H` by the sum over all coordinate words of length `k`. -/
theorem eLpNorm_iteratedFDeriv_le_sum_coordList (k : ℕ) {H : SpatialField}
    (hH : ContDiff ℝ ∞ H) :
    eLpNorm (fun y => iteratedFDeriv ℝ k H y) 4 volume ≤
      ∑ w : Fin k → Fin 3,
        eLpNorm (dirSpatialJet H ((coordList w).map coordinateVector)) 4 volume := by
  have hpt : ∀ y : Space,
      ‖iteratedFDeriv ℝ k H y‖ ≤
        ‖(∑ w : Fin k → Fin 3, fun y' =>
          ‖dirSpatialJet H ((coordList w).map coordinateVector) y'‖) y‖ := by
    intro y
    rw [Finset.sum_apply, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
    exact norm_iteratedFDeriv_le_sum_coordList k hH y
  have hmeas : ∀ w ∈ (Finset.univ : Finset (Fin k → Fin 3)),
      AEStronglyMeasurable
        (fun y : Space => ‖dirSpatialJet H ((coordList w).map coordinateVector) y‖) volume := by
    intro w _
    exact (JointSmoothSub.contDiff_infty_dirSpatialJet hH
      ((coordList w).map coordinateVector)).continuous.norm.aestronglyMeasurable
  calc eLpNorm (fun y => iteratedFDeriv ℝ k H y) 4 volume
      ≤ eLpNorm (∑ w : Fin k → Fin 3, fun y =>
          ‖dirSpatialJet H ((coordList w).map coordinateVector) y‖) 4 volume :=
        eLpNorm_mono hpt
    _ ≤ ∑ w : Fin k → Fin 3,
          eLpNorm (fun y =>
            ‖dirSpatialJet H ((coordList w).map coordinateVector) y‖) 4 volume :=
        eLpNorm_sum_le hmeas (by norm_num)
    _ = ∑ w : Fin k → Fin 3,
          eLpNorm (dirSpatialJet H ((coordList w).map coordinateVector)) 4 volume := by
        simp_rw [eLpNorm_norm]

/-- Difference-quotient remainder `Q F F' τ h = h⁻¹ • (F (τ + h) - F τ - h • F' τ)`. -/
def diffQuotRem (F F' : ℝ → SpatialField) (τ h : ℝ) : SpatialField :=
  h⁻¹ • (F (τ + h) - F τ - h • F' τ)

theorem contDiff_diffQuotRem {F F' : ℝ → SpatialField}
    (hF : IsUniformSmoothL4SliceFamily F) (hF' : IsUniformSmoothL4SliceFamily F')
    (τ h : ℝ) :
    ContDiff ℝ ∞ (diffQuotRem F F' τ h) := by
  have h1 := HigherPhaseSub.sliceFamily_contDiff_infty hF (τ + h)
  have h2 := HigherPhaseSub.sliceFamily_contDiff_infty hF τ
  have h3 := HigherPhaseSub.sliceFamily_contDiff_infty hF' τ
  exact ((h1.sub h2).sub (h3.const_smul h)).const_smul h⁻¹

/-- Uniform `L⁴(ℝ³)` bound on `dirSpatialJet (diffQuotRem F F' τ h) ws` across all `h : ℝ`. -/
theorem exists_eLpNorm_dirSpatialJet_diffQuotRem_le
    {F F' : ℝ → SpatialField}
    (hF : IsUniformSmoothL4SliceFamily F) (hF' : IsUniformSmoothL4SliceFamily F')
    (dF : HasPhaseJetDeriv F F') (τ : ℝ) (ws : List Space) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ h : ℝ,
      eLpNorm (dirSpatialJet (diffQuotRem F F' τ h) ws) 4 volume ≤ ENNReal.ofReal M := by
  have hF_ws : IsUniformSmoothL4SliceFamily (fun s => dirSpatialJet (F s) ws) :=
    HigherPhaseSub.sliceFamily_dirSpatialJet hF ws
  have hF'_ws : IsUniformSmoothL4SliceFamily (fun s => dirSpatialJet (F' s) ws) :=
    HigherPhaseSub.sliceFamily_dirSpatialJet hF' ws
  obtain ⟨Minf, hMinf⟩ := hF'_ws.iteratedFDeriv_bounded 0
  obtain ⟨M4, hM4⟩ := hF'_ws.l4_bounded 0
  set Binf : ℝ := 2 * max Minf 0
  set B4 : ℝ := 2 * max M4 0
  have hB4_nonneg : 0 ≤ B4 := by positivity
  refine ⟨B4, hB4_nonneg, fun h => ?_⟩
  set H : ℝ → SpatialField := fun s =>
    dirSpatialJet (F s) ws - (s - τ) • dirSpatialJet (F' τ) ws
  set H' : ℝ → SpatialField := fun s =>
    dirSpatialJet (F' s) ws - dirSpatialJet (F' τ) ws
  have hH_cont : ∀ s : ℝ, Continuous (H s) := fun s =>
    (HigherPhaseSub.sliceFamily_contDiff_infty hF_ws s).continuous.sub
      ((HigherPhaseSub.sliceFamily_contDiff_infty hF'_ws τ).continuous.const_smul (s - τ))
  have hH_bdd : ∀ s : ℝ, ∃ M₀ : ℝ, ∀ x : Space, ‖H s x‖ ≤ M₀ := by
    intro s
    obtain ⟨M1, hM1⟩ := hF_ws.iteratedFDeriv_bounded 0
    refine ⟨max M1 0 + |s - τ| * max Minf 0, fun x => ?_⟩
    have hx1 : ‖dirSpatialJet (F s) ws x‖ ≤ max M1 0 := by
      rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := dirSpatialJet (F s) ws)]
      exact (hM1 s x).trans (le_max_left M1 0)
    have hx2 : ‖dirSpatialJet (F' τ) ws x‖ ≤ max Minf 0 := by
      rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := dirSpatialJet (F' τ) ws)]
      exact (hMinf τ x).trans (le_max_left Minf 0)
    calc ‖H s x‖
        ≤ ‖dirSpatialJet (F s) ws x‖ + ‖(s - τ) • dirSpatialJet (F' τ) ws x‖ := norm_sub_le _ _
      _ ≤ max M1 0 + |s - τ| * max Minf 0 := by
          rw [norm_smul, Real.norm_eq_abs]
          exact add_le_add hx1 (mul_le_mul_of_nonneg_left hx2 (abs_nonneg _))
  have hH_l4 : ∀ s : ℝ, MemLp (H s) 4 volume := fun s => by
    have h1 : MemLp (dirSpatialJet (F s) ws) 4 volume :=
      SmoothLeraySliceSub.memLp_dirSpatialJet_of_memLp_iteratedFDeriv
        (HigherPhaseSub.sliceFamily_contDiff_infty hF_ws s) []
        (SmoothLeraySliceSub.memLp_iteratedFDeriv_of_sliceFamily hF_ws 0 s)
    have h2 : MemLp (dirSpatialJet (F' τ) ws) 4 volume :=
      SmoothLeraySliceSub.memLp_dirSpatialJet_of_memLp_iteratedFDeriv
        (HigherPhaseSub.sliceFamily_contDiff_infty hF'_ws τ) []
        (SmoothLeraySliceSub.memLp_iteratedFDeriv_of_sliceFamily hF'_ws 0 τ)
    exact h1.sub (h2.const_smul (s - τ))
  have hH'_cont : ∀ s : ℝ, Continuous (H' s) := fun s =>
    (HigherPhaseSub.sliceFamily_contDiff_infty hF'_ws s).continuous.sub
      (HigherPhaseSub.sliceFamily_contDiff_infty hF'_ws τ).continuous
  have hH'_bdd : ∀ (s : ℝ) (x : Space), ‖H' s x‖ ≤ Binf := by
    intro s x
    have hx1 : ‖dirSpatialJet (F' s) ws x‖ ≤ max Minf 0 := by
      rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := dirSpatialJet (F' s) ws)]
      exact (hMinf s x).trans (le_max_left Minf 0)
    have hx2 : ‖dirSpatialJet (F' τ) ws x‖ ≤ max Minf 0 := by
      rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := dirSpatialJet (F' τ) ws)]
      exact (hMinf τ x).trans (le_max_left Minf 0)
    calc ‖H' s x‖
        ≤ ‖dirSpatialJet (F' s) ws x‖ + ‖dirSpatialJet (F' τ) ws x‖ := norm_sub_le _ _
      _ ≤ max Minf 0 + max Minf 0 := add_le_add hx1 hx2
      _ = Binf := by dsimp [Binf]; ring
  have hH'_l4 : ∀ s : ℝ, eLpNorm (H' s) 4 volume ≤ ENNReal.ofReal B4 := by
    intro s
    have h0 : ∀ r : ℝ, eLpNorm (dirSpatialJet (F' r) ws) 4 volume ≤
        ENNReal.ofReal (max M4 0) := by
      intro r
      have heq : eLpNorm (dirSpatialJet (F' r) ws) 4 volume =
          eLpNorm (fun y => iteratedFDeriv ℝ 0 (dirSpatialJet (F' r) ws) y) 4 volume :=
        eLpNorm_congr_norm_ae (Eventually.of_forall fun y => norm_iteratedFDeriv_zero.symm)
      rw [heq]
      exact (hM4 r).trans (ENNReal.ofReal_le_ofReal (le_max_left M4 0))
    calc eLpNorm (H' s) 4 volume
        ≤ eLpNorm (dirSpatialJet (F' s) ws) 4 volume +
            eLpNorm (dirSpatialJet (F' τ) ws) 4 volume :=
          eLpNorm_sub_le
            (HigherPhaseSub.sliceFamily_contDiff_infty hF'_ws s).continuous.aestronglyMeasurable
            (HigherPhaseSub.sliceFamily_contDiff_infty hF'_ws τ).continuous.aestronglyMeasurable
            (by norm_num)
      _ ≤ ENNReal.ofReal (max M4 0) + ENNReal.ofReal (max M4 0) := add_le_add (h0 s) (h0 τ)
      _ = ENNReal.ofReal B4 := by
          rw [← ENNReal.ofReal_add (le_max_right M4 0) (le_max_right M4 0)]
          dsimp [B4]; ring_nf
  have hderiv : ∀ (s : ℝ) (x : Space), HasDerivAt (fun r : ℝ => H r x) (H' s x) s := by
    intro s x
    have hd1 : HasDerivAt (fun r : ℝ => dirSpatialJet (F r) ws x) (dirSpatialJet (F' s) ws x) s :=
      dF ws s x
    have hd2 : HasDerivAt (fun r : ℝ => (r - τ) • dirSpatialJet (F' τ) ws x)
        (dirSpatialJet (F' τ) ws x) s := by
      simpa using (((hasDerivAt_id s).sub_const τ).smul_const (dirSpatialJet (F' τ) ws x))
    exact hd1.sub hd2
  have hmvt := eLpNorm_sub_le_of_hasDerivAt H H' hH_cont hH_bdd hH_l4 hH'_cont hH'_bdd
    hB4_nonneg hH'_l4 hderiv τ (τ + h)
  have hjet_eq : dirSpatialJet (diffQuotRem F F' τ h) ws = h⁻¹ • (H (τ + h) - H τ) := by
    have hs1 := HigherPhaseSub.sliceFamily_contDiff_infty hF (τ + h)
    have hs2 := HigherPhaseSub.sliceFamily_contDiff_infty hF τ
    have hs3 := HigherPhaseSub.sliceFamily_contDiff_infty hF' τ
    change dirSpatialJet (h⁻¹ • (F (τ + h) - F τ - h • F' τ)) ws = _
    rw [HigherPhaseSub.dirSpatialJet_smul (F := F (τ + h) - F τ - h • F' τ)
        h⁻¹ ((hs1.sub hs2).sub (hs3.const_smul h)) ws,
      HigherPhaseSub.dirSpatialJet_sub (F := F (τ + h) - F τ) (G := h • F' τ)
        (hs1.sub hs2) (hs3.const_smul h) ws,
      HigherPhaseSub.dirSpatialJet_sub (F := F (τ + h)) (G := F τ) hs1 hs2 ws,
      HigherPhaseSub.dirSpatialJet_smul (F := F' τ) h hs3 ws]
    congr 1
    funext x
    simp [H]
    abel
  have hmul_le : ‖h⁻¹‖ * (B4 * ‖(τ + h) - τ‖) ≤ B4 := by
    rw [add_sub_cancel_left]
    by_cases hh : h = 0
    · subst hh; simp [hB4_nonneg]
    · have hnorm_ne : ‖h‖ ≠ 0 := norm_ne_zero_iff.2 hh
      rw [norm_inv, ← mul_assoc, mul_comm ‖h‖⁻¹ B4, mul_assoc, inv_mul_cancel₀ hnorm_ne, mul_one]
  calc eLpNorm (dirSpatialJet (diffQuotRem F F' τ h) ws) 4 volume
      = ‖h⁻¹‖ₑ * eLpNorm (H (τ + h) - H τ) 4 volume := by
        rw [hjet_eq, eLpNorm_const_smul]
    _ ≤ ENNReal.ofReal ‖h⁻¹‖ * ENNReal.ofReal (B4 * ‖(τ + h) - τ‖) := by
        rw [ofReal_norm]
        exact mul_le_mul_of_nonneg_left hmvt zero_le
    _ = ENNReal.ofReal (‖h⁻¹‖ * (B4 * ‖(τ + h) - τ‖)) :=
        (ENNReal.ofReal_mul (norm_nonneg _)).symm
    _ ≤ ENNReal.ofReal B4 := ENNReal.ofReal_le_ofReal hmul_le

/-- Uniform `L⁴(ℝ³)` bound on `iteratedFDeriv ℝ k (diffQuotRem F F' τ h)` across all `h : ℝ`. -/
theorem exists_eLpNorm_iteratedFDeriv_diffQuotRem_le
    {F F' : ℝ → SpatialField}
    (hF : IsUniformSmoothL4SliceFamily F) (hF' : IsUniformSmoothL4SliceFamily F')
    (dF : HasPhaseJetDeriv F F') (τ : ℝ) (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ h : ℝ,
      eLpNorm (fun y => iteratedFDeriv ℝ k (diffQuotRem F F' τ h) y) 4 volume ≤
        ENNReal.ofReal M := by
  choose M hM0 hM using fun w : Fin k → Fin 3 =>
    exists_eLpNorm_dirSpatialJet_diffQuotRem_le hF hF' dF τ ((coordList w).map coordinateVector)
  refine ⟨∑ w : Fin k → Fin 3, M w, Finset.sum_nonneg fun w _ => hM0 w, fun h => ?_⟩
  calc eLpNorm (fun y => iteratedFDeriv ℝ k (diffQuotRem F F' τ h) y) 4 volume
      ≤ ∑ w : Fin k → Fin 3,
          eLpNorm (dirSpatialJet (diffQuotRem F F' τ h)
            ((coordList w).map coordinateVector)) 4 volume :=
        eLpNorm_iteratedFDeriv_le_sum_coordList k (contDiff_diffQuotRem hF hF' τ h)
    _ ≤ ∑ w : Fin k → Fin 3, ENNReal.ofReal (M w) :=
        Finset.sum_le_sum fun w _ => hM w h
    _ = ENNReal.ofReal (∑ w : Fin k → Fin 3, M w) :=
        (ENNReal.ofReal_sum_of_nonneg fun w _ => hM0 w).symm

theorem memLp_iteratedFDeriv_diffQuotRem
    {F F' : ℝ → SpatialField}
    (hF : IsUniformSmoothL4SliceFamily F) (hF' : IsUniformSmoothL4SliceFamily F')
    (dF : HasPhaseJetDeriv F F') (τ h : ℝ) (k : ℕ) :
    MemLp (fun y => iteratedFDeriv ℝ k (diffQuotRem F F' τ h) y) 4 volume := by
  obtain ⟨M, _, hM⟩ := exists_eLpNorm_iteratedFDeriv_diffQuotRem_le hF hF' dF τ k
  refine ⟨((contDiff_diffQuotRem hF hF' τ h).continuous_iteratedFDeriv
    (by exact_mod_cast le_top)).aestronglyMeasurable, ?_⟩
  exact (hM h).trans_lt ENNReal.ofReal_lt_top

theorem smoothLeraySlice_diffQuot_eq
    (hRep : SmoothLerayRepExists)
    {F F' : ℝ → SpatialField}
    (hF : IsUniformSmoothL4SliceFamily F) (hF' : IsUniformSmoothL4SliceFamily F')
    (τ h : ℝ) :
    h⁻¹ • (smoothLeraySlice F (τ + h) - smoothLeraySlice F τ - h • smoothLeraySlice F' τ) =
      smoothLerayProj (diffQuotRem F F' τ h) := by
  rw [SmoothLeraySliceSub.smoothLeraySlice_sub_sub_smul hRep hF hF' τ h]
  have h1 := (SmoothLeraySliceSub.smoothLeraySlice_rep_and_memLp hRep hF (τ + h)).1
  have h2 := (SmoothLeraySliceSub.smoothLeraySlice_rep_and_memLp hRep hF τ).1
  have h3 := (SmoothLeraySliceSub.smoothLeraySlice_rep_and_memLp hRep hF' τ).1
  have hsub12 : IsSmoothLerayRep (F (τ + h) - F τ) (smoothLerayProj (F (τ + h) - F τ)) := by
    rw [SmoothLeraySliceSub.smoothLerayProj_sub h1 h2]
    exact SmoothLeraySliceSub.isSmoothLerayRep_sub h1 h2
  have hsmul3 : IsSmoothLerayRep (h • F' τ) (smoothLerayProj (h • F' τ)) := by
    rw [SmoothLeraySliceSub.smoothLerayProj_smul h h3]
    exact SmoothLeraySliceSub.isSmoothLerayRep_smul h h3
  have hrem : IsSmoothLerayRep (F (τ + h) - F τ - h • F' τ)
      (smoothLerayProj (F (τ + h) - F τ - h • F' τ)) := by
    rw [SmoothLeraySliceSub.smoothLerayProj_sub hsub12 hsmul3]
    exact SmoothLeraySliceSub.isSmoothLerayRep_sub hsub12 hsmul3
  exact (SmoothLeraySliceSub.smoothLerayProj_smul h⁻¹ hrem).symm

/-! ## 3. Mollifier approximation bound for `C¹` fields with bounded gradient -/

theorem norm_moll_sub_le_of_fderiv_le {f : SpatialField} (hf : ContDiff ℝ ∞ f)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ z : Space, ‖fderiv ℝ f z‖ ≤ C)
    (b : ContDiffBump (0 : Space)) (x : Space) :
    ‖UnforcedLeray.Sob.moll b volume f x - f x‖ ≤ C * b.rOut := by
  have hloc : LocallyIntegrable f volume := hf.continuous.locallyIntegrable
  have hrepr : UnforcedLeray.Sob.moll b volume f x - f x =
      ∫ t : Space, b.normed volume t • (f (x - t) - f x) := by
    rw [UnforcedLeray.Sob.moll_apply_swap]
    have h1 := UnforcedLeray.Sob.integrable_kernel_swap (b.continuous_normed (μ := volume))
      (b.hasCompactSupport_normed (μ := volume)) hloc x
    have h2 : Integrable (fun t : Space => b.normed volume t • f x) volume :=
      (b.integrable_normed (μ := volume)).smul_const _
    simp_rw [smul_sub]
    rw [integral_sub h1 h2, integral_smul_const, b.integral_normed (μ := volume), one_smul]
  have hdiff : Differentiable ℝ f := JointSmoothSub.differentiable_dirSpatialJet hf []
  have hpt : ∀ t : Space, ‖b.normed volume t • (f (x - t) - f x)‖ ≤
      b.normed volume t * (C * b.rOut) := by
    intro t
    rw [norm_smul, Real.norm_of_nonneg (b.nonneg_normed t)]
    by_cases ht : t ∈ Metric.ball (0 : Space) b.rOut
    · refine mul_le_mul_of_nonneg_left ?_ (b.nonneg_normed t)
      have hlip := convex_univ.norm_image_sub_le_of_norm_fderiv_le
        (fun z _ => hdiff z) (fun z _ => hC z) (mem_univ x) (mem_univ (x - t))
      have hdist : ‖(x - t) - x‖ ≤ b.rOut := by
        rw [sub_sub_cancel_left, norm_neg]
        have ht' : ‖t‖ < b.rOut := by simpa [Metric.mem_ball, dist_zero_right] using ht
        exact ht'.le
      exact hlip.trans (mul_le_mul_of_nonneg_left hdist hC0)
    · have h0 : b.normed volume t = 0 := by
        rw [← Function.notMem_support, b.support_normed_eq (μ := volume)]
        exact ht
      simp [h0]
  have hint_norm : Integrable (fun t : Space => ‖b.normed volume t • (f (x - t) - f x)‖) volume := by
    have h1 := UnforcedLeray.Sob.integrable_kernel_swap (b.continuous_normed (μ := volume))
      (b.hasCompactSupport_normed (μ := volume)) hloc x
    have h2 : Integrable (fun t : Space => b.normed volume t • f x) volume :=
      (b.integrable_normed (μ := volume)).smul_const _
    have hsub := (h1.sub h2).norm
    refine hsub.congr (Eventually.of_forall fun t => ?_)
    simp [smul_sub]
  rw [hrepr]
  calc ‖∫ t : Space, b.normed volume t • (f (x - t) - f x)‖
      ≤ ∫ t : Space, ‖b.normed volume t • (f (x - t) - f x)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : Space, b.normed volume t * (C * b.rOut) :=
        integral_mono hint_norm ((b.integrable_normed (μ := volume)).mul_const (C * b.rOut)) hpt
    _ = C * b.rOut := by
        rw [integral_mul_const, b.integral_normed (μ := volume), one_mul]

/-! ## 4. Duality identity for mollified smooth Leray representatives -/

theorem moll_smoothLerayRep_coord_eq_innerPairing
    {Q D_G : SpatialField} (hQ : MemLp Q 4 volume) (hrep : IsSmoothLerayRep Q D_G)
    (b : ContDiffBump (0 : Space)) (y : Space) (j : Fin 3) :
    have : Fact (1 ≤ (4 : ℝ≥0∞).conjExponent) :=
      ⟨UnforcedLeray.RieszLp.one_le_conjExponent 4⟩
    (UnforcedLeray.Sob.moll b volume D_G y) j =
      UnforcedLeray.RieszLp.innerPairing 4 (4 : ℝ≥0∞).conjExponent
        (hQ.toLp Q)
        (UnforcedLeray.RieszLp.lerayLp (4 : ℝ≥0∞).conjExponent
          (UnforcedLeray.RieszLp.one_lt_of_holderConjugate (p := 4) (by norm_num))
          (UnforcedLeray.RieszLp.ne_top_of_holderConjugate (p := 4) (by norm_num))
          ((((b.continuous_normed (μ := volume)).smul continuous_const).memLp_of_hasCompactSupport
            ((b.hasCompactSupport_normed (μ := volume)).smul_right)).comp_measurePreserving
            (Measure.measurePreserving_sub_left volume y) |>.toLp
            (fun x : Space => b.normed volume (y - x) • coordinateVector j))) := by
  let q : ℝ≥0∞ := (4 : ℝ≥0∞).conjExponent
  have : Fact (1 ≤ q) := ⟨UnforcedLeray.RieszLp.one_le_conjExponent 4⟩
  have hq1 : 1 < q := UnforcedLeray.RieszLp.one_lt_of_holderConjugate (p := 4) (by norm_num)
  have hq : q ≠ ⊤ := UnforcedLeray.RieszLp.ne_top_of_holderConjugate (p := 4) (by norm_num)
  obtain ⟨hQ', hDG_smooth, hDG_ae⟩ := hrep
  have htoLp_eq : hQ'.toLp Q = hQ.toLp Q := rfl
  set Φ : SpatialField := fun x => b.normed volume (y - x) • coordinateVector j
  have hΦ_q : MemLp Φ q volume :=
    (((b.continuous_normed (μ := volume)).smul continuous_const).memLp_of_hasCompactSupport
      ((b.hasCompactSupport_normed (μ := volume)).smul_right)).comp_measurePreserving
      (Measure.measurePreserving_sub_left volume y)
  have hloc : LocallyIntegrable D_G volume := hDG_smooth.continuous.locallyIntegrable
  have hint_conv : Integrable (fun x : Space => b.normed volume (y - x) • D_G x) volume := by
    have h1 := UnforcedLeray.Sob.integrable_kernel_swap (b.continuous_normed (μ := volume))
      (b.hasCompactSupport_normed (μ := volume)) hloc y
    have hcomp : (fun t : Space => b.normed volume t • D_G (y - t)) =
        (fun x : Space => b.normed volume (y - x) • D_G x) ∘ (fun t : Space => y - t) := by
      funext t
      simp [Function.comp]
    rw [hcomp] at h1
    exact ((Measure.measurePreserving_sub_left volume y).integrable_comp_emb
      (Homeomorph.subLeft y).measurableEmbedding).1 h1
  let L_j : Space →L[ℝ] ℝ := (innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).flip (coordinateVector j)
  have hL_j_apply : ∀ v : Space, L_j v = v j := by
    intro v
    change inner ℝ v (coordinateVector j) = v j
    have h1 := UnforcedLeray.RieszLp.inner_smul_coordinateVector v 1 j
    rwa [one_smul, one_mul] at h1
  have hmoll_eq : (UnforcedLeray.Sob.moll b volume D_G y) j =
      ∫ x : Space, inner ℝ (D_G x) (Φ x) := by
    rw [← hL_j_apply (UnforcedLeray.Sob.moll b volume D_G y),
      UnforcedLeray.Sob.moll, UnforcedLeray.Sob.cv_apply,
      ← L_j.integral_comp_comm hint_conv]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    change inner ℝ (b.normed volume (y - x) • D_G x) (coordinateVector j) =
      inner ℝ (D_G x) (b.normed volume (y - x) • coordinateVector j)
    rw [real_inner_smul_left, real_inner_smul_right]
  rw [hmoll_eq]
  have hae_pair : (fun x : Space => inner ℝ (D_G x) (Φ x)) =ᵐ[volume]
      fun x : Space =>
        inner ℝ (UnforcedLeray.RieszLp.lerayLp 4 (by norm_num) (by norm_num) (hQ.toLp Q) x)
          ((hΦ_q.toLp Φ) x) := by
    rw [← htoLp_eq]
    filter_upwards [hDG_ae, hΦ_q.coeFn_toLp] with x hx1 hx2
    rw [hx1, hx2]
  rw [integral_congr_ae hae_pair,
    UnforcedLeray.RieszLp.integral_inner_lerayLp_symm (by norm_num) (by norm_num) hq1 hq
      (hQ.toLp Q) (hΦ_q.toLp Φ),
    ← UnforcedLeray.RieszLp.innerPairing_apply]

end SmoothLeraySliceDerivZeroAux

/-- **`PartII-b:S3/1/2/1/2` (`SmoothLeraySliceDerivZero`)**
(`the November 2 reference manuscript`,
lines 2552 and 2559-2562: "These estimates are uniform in phase; the bounded Cartesian Leray map
preserves them in $W^{k,p}$. ... On positive physical-time compact intervals the resulting
$C_\tau W^{k,4}$ regularity and the projected equation give all time derivatives"):
given `SmoothLerayRepExists`, if `F, F' : ℝ → SpatialField` lie in `IsUniformSmoothL4SliceFamily`
and `HasPhaseJetDeriv F F'`, then `τ' ↦ smoothLeraySlice F τ' y` has derivative
`smoothLeraySlice F' τ y` at every `(τ, y) ∈ ℝ × Space`. -/
theorem smoothLeraySliceDerivZero_proof : UnforcedLeray.Short.IIb.SmoothLeraySliceDerivZero := by
  intro hRep F F' hF hF' dF τ y
  open SmoothLeraySliceDerivZeroAux in
  let q : ℝ≥0∞ := (4 : ℝ≥0∞).conjExponent
  have : Fact (1 ≤ q) := ⟨UnforcedLeray.RieszLp.one_le_conjExponent 4⟩
  have hq1 : 1 < q := UnforcedLeray.RieszLp.one_lt_of_holderConjugate (p := 4) (by norm_num)
  have hq : q ≠ ⊤ := UnforcedLeray.RieszLp.ne_top_of_holderConjugate (p := 4) (by norm_num)
  set Q : ℝ → SpatialField := diffQuotRem F F' τ
  set D_G : ℝ → SpatialField := fun h => smoothLerayProj (Q h)
  have hQ_mem : ∀ h : ℝ, MemLp (Q h) 4 volume := fun h =>
    SmoothLeraySliceSub.memLp_dirSpatialJet_of_memLp_iteratedFDeriv
      (contDiff_diffQuotRem hF hF' τ h) []
      (memLp_iteratedFDeriv_diffQuotRem hF hF' dF τ h 0)
  have hDG_rep : ∀ h : ℝ, IsSmoothLerayRep (Q h) (D_G h) ∧
      ContDiff ℝ ∞ (D_G h) ∧
      ∀ k : ℕ, MemLp (fun z => iteratedFDeriv ℝ k (D_G h) z) 4 volume := by
    intro h
    obtain ⟨g, hg_rep, hg_m⟩ := hRep (Q h) (contDiff_diffQuotRem hF hF' τ h)
      (memLp_iteratedFDeriv_diffQuotRem hF hF' dF τ h)
    have heq : D_G h = g := HigherPhaseSub.smoothLerayProj_eq_of_isSmoothLerayRep hg_rep
    rw [heq]
    exact ⟨hg_rep, hg_rep.2.1, hg_m⟩
  obtain ⟨M0_Q, hM0_Q_nonneg, hM0_Q⟩ := exists_eLpNorm_iteratedFDeriv_diffQuotRem_le hF hF' dF τ 0
  have hQ_l4_bound : ∀ h : ℝ, eLpNorm (Q h) 4 volume ≤ ENNReal.ofReal M0_Q := by
    intro h
    have heq : eLpNorm (Q h) 4 volume =
        eLpNorm (fun z => iteratedFDeriv ℝ 0 (Q h) z) 4 volume :=
      eLpNorm_congr_norm_ae (Eventually.of_forall fun z => norm_iteratedFDeriv_zero.symm)
    rw [heq]
    exact hM0_Q h
  have hDG_iter_bound : ∀ k : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ h : ℝ,
      eLpNorm (fun z => iteratedFDeriv ℝ k (D_G h) z) 4 volume ≤ ENNReal.ofReal B := by
    intro k
    obtain ⟨Mk, hMk0, hMk⟩ := exists_eLpNorm_iteratedFDeriv_diffQuotRem_le hF hF' dF τ k
    set CL : ℝ := (‖UnforcedLeray.RieszLp.lerayLp 4 (by norm_num) (by norm_num)‖₊ : ℝ)
    refine ⟨(3 : ℝ) ^ k * CL * Mk, by positivity, fun h => ?_⟩
    have hbound := SmoothLeraySliceSub.eLpNorm_iteratedFDeriv_lerayRep_le k
      (contDiff_diffQuotRem hF hF' τ h)
      (memLp_iteratedFDeriv_diffQuotRem hF hF' dF τ h)
      (hDG_rep h).2.2 (hDG_rep h).1
    have hcoe : ((3 : ℝ≥0∞) ^ k *
        ‖UnforcedLeray.RieszLp.lerayLp 4 (by norm_num) (by norm_num)‖₊) =
        ENNReal.ofReal ((3 : ℝ) ^ k * CL) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
        ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal]
    calc eLpNorm (fun z => iteratedFDeriv ℝ k (D_G h) z) 4 volume
        ≤ (3 : ℝ≥0∞) ^ k *
            ‖UnforcedLeray.RieszLp.lerayLp 4 (by norm_num) (by norm_num)‖₊ *
            eLpNorm (fun z => iteratedFDeriv ℝ k (Q h) z) 4 volume := hbound
      _ ≤ ENNReal.ofReal ((3 : ℝ) ^ k * CL) * ENNReal.ofReal Mk := by
          rw [← hcoe]
          exact mul_le_mul_of_nonneg_left (hMk h) zero_le
      _ = ENNReal.ofReal ((3 : ℝ) ^ k * CL * Mk) :=
          (ENNReal.ofReal_mul (by positivity)).symm
  obtain ⟨B1, hB1_0, hB1⟩ := hDG_iter_bound 1
  obtain ⟨B2, hB2_0, hB2⟩ := hDG_iter_bound 2
  obtain ⟨CM, hCM0, hCM⟩ := smoothMorreyL4Bound_of_field smoothMorreyL4FieldBound_proof 1
  set C1 : ℝ := CM * (B1 + B2)
  have hC1_0 : 0 ≤ C1 := by positivity
  have hDG_fderiv_le : ∀ (h : ℝ) (z : Space), ‖fderiv ℝ (D_G h) z‖ ≤ C1 := by
    intro h z
    rw [← norm_iteratedFDeriv_one]
    have hm := hCM (D_G h) (hDG_rep h).2.1 B1 B2 (hB1 h) (hB2 h) z
    rwa [max_eq_left hB1_0, max_eq_left hB2_0] at hm
  have hmoll_tendsto : ∀ b : ContDiffBump (0 : Space),
      Tendsto (fun h : ℝ => UnforcedLeray.Sob.moll b volume (D_G h) y) (𝓝[≠] 0) (𝓝 0) := by
    intro b
    have hcoord_tendsto : ∀ j : Fin 3,
        Tendsto (fun h : ℝ => (UnforcedLeray.Sob.moll b volume (D_G h) y) j) (𝓝[≠] 0) (𝓝 0) := by
      intro j
      set Φ : SpatialField := fun x => b.normed volume (y - x) • coordinateVector j
      have hΦ_q : MemLp Φ q volume :=
        (((b.continuous_normed (μ := volume)).smul continuous_const).memLp_of_hasCompactSupport
          ((b.hasCompactSupport_normed (μ := volume)).smul_right)).comp_measurePreserving
          (Measure.measurePreserving_sub_left volume y)
      set W : Lp Space q volume :=
        UnforcedLeray.RieszLp.lerayLp q hq1 hq (hΦ_q.toLp Φ)
      rw [Metric.tendsto_nhds]
      intro ε hε
      set K_pair : ℝ := ‖UnforcedLeray.RieszLp.innerPairing 4 q‖ * M0_Q + 1
      have hK_pair_pos : 0 < K_pair := by positivity
      set η : ℝ := ε / (4 * K_pair)
      have hη_pos : 0 < η := div_pos hε (by positivity)
      obtain ⟨g, hgs, hgu, hgc, hgp⟩ :=
        (Lp.memLp W).exists_hasCompactSupport_eLpNorm_sub_le hq (ENNReal.ofReal_pos.2 hη_pos).ne'
      have hW_sub_le : ‖W - hgp.toLp g‖ ≤ η := by
        rw [Lp.norm_def]
        have h1 : (⇑(W - hgp.toLp g) : SpatialField) =ᵐ[volume] (W : SpatialField) - g := by
          filter_upwards [Lp.coeFn_sub W (hgp.toLp g), hgp.coeFn_toLp] with x hx1 hx2
          rw [hx1, Pi.sub_apply, Pi.sub_apply, hx2]
        rw [eLpNorm_congr_ae h1]
        have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hgu
        rwa [ENNReal.toReal_ofReal hη_pos.le] at h2
      have hg_int : Integrable g volume := hgc.integrable_of_hasCompactSupport hgs
      obtain ⟨Minf_F', hMinf_F'⟩ := hF'.iteratedFDeriv_bounded 0
      have hF_bdd : ∀ s : ℝ, ∃ M₀ : ℝ, ∀ x : Space, ‖F s x‖ ≤ M₀ := by
        intro s
        obtain ⟨M₀, hM₀⟩ := hF.iteratedFDeriv_bounded 0
        refine ⟨M₀, fun x => ?_⟩
        rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := F s)]
        exact hM₀ s x
      have hF'_bdd : ∀ (s : ℝ) (x : Space), ‖F' s x‖ ≤ Minf_F' := by
        intro s x
        rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := F' s)]
        exact hMinf_F' s x
      have hderiv_g : HasDerivAt (fun s : ℝ => ∫ x : Space, inner ℝ (F s x) (g x))
          (∫ x : Space, inner ℝ (F' τ x) (g x)) τ :=
        hasDerivAt_integral_inner_of_integrable F F'
          (fun s => (HigherPhaseSub.sliceFamily_contDiff_infty hF s).continuous) hF_bdd
          (fun s => (HigherPhaseSub.sliceFamily_contDiff_infty hF' s).continuous) hF'_bdd
          (dF []) hg_int τ
      have hslope_g : Tendsto
          (fun h : ℝ => h⁻¹ • ((∫ x : Space, inner ℝ (F (τ + h) x) (g x)) -
            (∫ x : Space, inner ℝ (F τ x) (g x))) -
            (∫ x : Space, inner ℝ (F' τ x) (g x)))
          (𝓝[≠] 0) (𝓝 0) :=
        tendsto_sub_nhds_zero_iff.2 (hasDerivAt_iff_tendsto_slope_zero.1 hderiv_g)
      have hpair_g_tendsto : Tendsto
          (fun h : ℝ => UnforcedLeray.RieszLp.innerPairing 4 q
            ((hQ_mem h).toLp (Q h)) (hgp.toLp g))
          (𝓝[≠] 0) (𝓝 0) := by
        refine hslope_g.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with h (hh : h ≠ 0)
        rw [UnforcedLeray.RieszLp.innerPairing_apply]
        have hae : (fun x : Space =>
            inner ℝ (((hQ_mem h).toLp (Q h) : SpatialField) x)
              ((hgp.toLp g : SpatialField) x)) =ᵐ[volume]
            fun x : Space => inner ℝ (Q h x) (g x) := by
          filter_upwards [(hQ_mem h).coeFn_toLp, hgp.coeFn_toLp] with x hx1 hx2
          rw [hx1, hx2]
        rw [integral_congr_ae hae]
        obtain ⟨M1, hM1⟩ := hF_bdd (τ + h)
        obtain ⟨M2, hM2⟩ := hF_bdd τ
        have hint1 : Integrable (fun x : Space => inner ℝ (F (τ + h) x) (g x)) volume :=
          integrable_inner_of_bounded
            (HigherPhaseSub.sliceFamily_contDiff_infty hF (τ + h)).continuous hM1 hg_int
        have hint2 : Integrable (fun x : Space => inner ℝ (F τ x) (g x)) volume :=
          integrable_inner_of_bounded
            (HigherPhaseSub.sliceFamily_contDiff_infty hF τ).continuous hM2 hg_int
        have hint12 : Integrable (fun x : Space =>
            inner ℝ (F (τ + h) x) (g x) - inner ℝ (F τ x) (g x)) volume :=
          hint1.sub hint2
        have hint3 : Integrable (fun x : Space => inner ℝ (F' τ x) (g x)) volume :=
          integrable_inner_of_bounded
            (HigherPhaseSub.sliceFamily_contDiff_infty hF' τ).continuous (hF'_bdd τ) hg_int
        have hpoint : ∀ x : Space, inner ℝ (Q h x) (g x) =
            h⁻¹ * ((inner ℝ (F (τ + h) x) (g x) - inner ℝ (F τ x) (g x)) -
              h * inner ℝ (F' τ x) (g x)) := by
          intro x
          change inner ℝ ((h⁻¹ • (F (τ + h) - F τ - h • F' τ)) x) (g x) = _
          simp only [Pi.smul_apply, Pi.sub_apply, real_inner_smul_left, inner_sub_left]
        rw [integral_congr_ae (Eventually.of_forall hpoint),
          integral_const_mul, integral_sub hint12 (hint3.const_mul h),
          integral_sub hint1 hint2, integral_const_mul, smul_eq_mul]
        symm
        rw [mul_sub, inv_mul_cancel_left₀ hh]
      filter_upwards [hpair_g_tendsto.eventually (Metric.ball_mem_nhds 0 (half_pos hε))] with h hh
      rw [dist_zero_right] at hh ⊢
      rw [moll_smoothLerayRep_coord_eq_innerPairing (hQ_mem h) (hDG_rep h).1 b y j]
      set uQ : Lp Space 4 volume := (hQ_mem h).toLp (Q h)
      have huQ_norm : ‖uQ‖ ≤ M0_Q := by
        rw [Lp.norm_toLp]
        have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hQ_l4_bound h)
        rwa [ENNReal.toReal_ofReal hM0_Q_nonneg] at h1
      have hsplit_pair : UnforcedLeray.RieszLp.innerPairing 4 q uQ W =
          UnforcedLeray.RieszLp.innerPairing 4 q uQ (W - hgp.toLp g) +
            UnforcedLeray.RieszLp.innerPairing 4 q uQ (hgp.toLp g) := by
        rw [← map_add, sub_add_cancel]
      have herr_bound : ‖UnforcedLeray.RieszLp.innerPairing 4 q uQ (W - hgp.toLp g)‖ < ε / 2 := by
        have hpair_nonneg : 0 ≤ ‖UnforcedLeray.RieszLp.innerPairing 4 q‖ :=
          ContinuousLinearMap.opNorm_nonneg _
        calc ‖UnforcedLeray.RieszLp.innerPairing 4 q uQ (W - hgp.toLp g)‖
            ≤ ‖UnforcedLeray.RieszLp.innerPairing 4 q‖ * ‖uQ‖ * ‖W - hgp.toLp g‖ :=
              (UnforcedLeray.RieszLp.innerPairing 4 q).le_opNorm₂ uQ (W - hgp.toLp g)
          _ ≤ ‖UnforcedLeray.RieszLp.innerPairing 4 q‖ * M0_Q * η :=
              mul_le_mul (mul_le_mul_of_nonneg_left huQ_norm hpair_nonneg)
                hW_sub_le (norm_nonneg _) (mul_nonneg hpair_nonneg hM0_Q_nonneg)
          _ ≤ K_pair * η := by
              refine mul_le_mul_of_nonneg_right ?_ hη_pos.le
              dsimp [K_pair]; linarith
          _ = ε / 4 := by
              dsimp [η]
              field_simp [hK_pair_pos.ne']
          _ < ε / 2 := by linarith
      rw [hsplit_pair]
      exact ((norm_add_le _ _).trans_lt (add_lt_add herr_bound hh)).trans_eq (add_halves ε)
    have hsum_eq : ∀ v : Space, v = ∑ j : Fin 3, (v j) • coordinateVector j := by
      intro v
      ext i
      simp [coordinateVector, Pi.single_apply]
    have hsum_tendsto : Tendsto
        (fun h : ℝ => ∑ j : Fin 3,
          ((UnforcedLeray.Sob.moll b volume (D_G h) y) j) • coordinateVector j)
        (𝓝[≠] 0) (𝓝 (∑ _j : Fin 3, (0 : ℝ) • coordinateVector _j)) :=
      tendsto_finsetSum Finset.univ fun j _ => (hcoord_tendsto j).smul_const (coordinateVector j)
    simpa [← hsum_eq] using hsum_tendsto
  have hDG_tendsto : Tendsto (fun h : ℝ => D_G h y) (𝓝[≠] 0) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    set rOut : ℝ := ε / (4 * (C1 + 1))
    set rIn : ℝ := ε / (8 * (C1 + 1))
    have hrIn_pos : 0 < rIn := div_pos hε (by positivity)
    have hrIn_lt : rIn < rOut := by
      dsimp [rIn, rOut]
      exact div_lt_div_of_pos_left hε (by positivity) (by linarith)
    let b : ContDiffBump (0 : Space) := ⟨rIn, rOut, hrIn_pos, hrIn_lt⟩
    have hmoll_lt : ∀ h : ℝ, ‖UnforcedLeray.Sob.moll b volume (D_G h) y - D_G h y‖ < ε / 2 := by
      intro h
      calc ‖UnforcedLeray.Sob.moll b volume (D_G h) y - D_G h y‖
          ≤ C1 * b.rOut :=
            norm_moll_sub_le_of_fderiv_le (hDG_rep h).2.1 hC1_0 (hDG_fderiv_le h) b y
        _ ≤ (C1 + 1) * rOut := by
            change C1 * rOut ≤ (C1 + 1) * rOut
            exact mul_le_mul_of_nonneg_right (by linarith) (hrIn_pos.trans hrIn_lt).le
        _ = ε / 4 := by
            dsimp [rOut]
            have hne : C1 + 1 ≠ 0 := by positivity
            field_simp [hne]
        _ < ε / 2 := by linarith
    filter_upwards [(hmoll_tendsto b).eventually (Metric.ball_mem_nhds 0 (half_pos hε))] with h hh
    rw [dist_zero_right] at hh ⊢
    calc ‖D_G h y‖
        = ‖(D_G h y - UnforcedLeray.Sob.moll b volume (D_G h) y) +
            UnforcedLeray.Sob.moll b volume (D_G h) y‖ := by abel_nf
      _ ≤ ‖UnforcedLeray.Sob.moll b volume (D_G h) y - D_G h y‖ +
            ‖UnforcedLeray.Sob.moll b volume (D_G h) y‖ := by
          rw [norm_sub_rev]
          exact norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hmoll_lt h) hh
      _ = ε := add_halves ε
  rw [hasDerivAt_iff_tendsto_slope_zero, ← tendsto_sub_nhds_zero_iff]
  refine hDG_tendsto.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h (hh : h ≠ 0)
  have h1 := congrFun (smoothLeraySlice_diffQuot_eq hRep hF hF' τ h) y
  change smoothLerayProj (diffQuotRem F F' τ h) y = _
  rw [← h1]
  simp [smul_sub, inv_smul_smul₀ hh]

end UnforcedLeray.Short.IIb

end
