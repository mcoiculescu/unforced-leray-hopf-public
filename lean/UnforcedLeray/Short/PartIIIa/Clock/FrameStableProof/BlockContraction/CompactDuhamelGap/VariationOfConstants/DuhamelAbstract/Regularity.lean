import UnforcedLeray.Units.B0104.Evolution
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Leaf A helper: uniform bounds and strong continuity of a Duhamel evolution on one block

Helper for `PartIII-a:T21/c3/2/1/2/1` (`DuhamelVoCAbstract`, SP 2962-2982).

For a `B0104.IsDuhamelEvolution` `U` of `(F, A)` with `F` strongly continuous on the block triangle
`{0 ≤ σ ≤ τ ≤ B}` and `A` bounded on `[0, B]`:

* `exists_opNorm_bound`: `F` is uniformly bounded on the triangle (Banach-Steinhaus);
* `norm_U_le`: `‖U(t,s)‖ ≤ 2 M e^{(2MK+1)B}` on the triangle (Gronwall);
* `norm_U_min_sub_le`, `U_min_uniform`: `s ↦ U(t, min s t) x` is continuous, uniformly in `t`
  (Gronwall against the uniform continuity of `F` on the compact triangle);
* `continuousOn_U_min_left`: `t ↦ U(t, min s t) x` is continuous (dominated convergence);
* `continuousOn_U_min`: `(t, s) ↦ U(t, min s t) x` is jointly continuous on `[0,B]²`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa.DuhamelAbstractSub

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The closed block triangle `{(τ, σ) | 0 ≤ σ ≤ τ ≤ B}`. -/
def tri (B : ℝ) : Set (ℝ × ℝ) := {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ B}

theorem isCompact_tri (B : ℝ) : IsCompact (tri B) := by
  refine ((isCompact_Icc (a := (0 : ℝ)) (b := B)).prod
    (isCompact_Icc (a := (0 : ℝ)) (b := B))).of_isClosed_subset ?_ ?_
  · exact (isClosed_le continuous_const continuous_snd).inter
      ((isClosed_le continuous_snd continuous_fst).inter (isClosed_le continuous_fst continuous_const))
  · rintro ⟨t, s⟩ ⟨h0, h1, h2⟩
    exact ⟨⟨h0.trans h1, h2⟩, ⟨h0, h1.trans h2⟩⟩

/-- Banach-Steinhaus on the compact triangle. -/
theorem exists_opNorm_bound {B : ℝ} {F : ℝ → ℝ → H →L[ℂ] H}
    (hFc : ∀ x : H, ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2 x) (tri B)) :
    ∃ M, 0 ≤ M ∧ ∀ t s, 0 ≤ s → s ≤ t → t ≤ B → ‖F t s‖ ≤ M := by
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun p : tri B => F p.1.1 p.1.2) fun x => by
    obtain ⟨C, hC⟩ := (isCompact_tri B).exists_bound_of_continuousOn (hFc x)
    exact ⟨C, fun p => hC p.1 p.2⟩
  exact ⟨max C 0, le_max_right _ _, fun t s h0 h1 h2 =>
    (hC ⟨(t, s), h0, h1, h2⟩).trans (le_max_left _ _)⟩

theorem norm_FAU_le {M K CU : ℝ} {T S V : H →L[ℂ] H} (hT : ‖T‖ ≤ M) (hS : ‖S‖ ≤ K)
    (hV : ‖V‖ ≤ CU) (hM : 0 ≤ M) (hK : 0 ≤ K) (x : H) :
    ‖T (S (V x))‖ ≤ M * K * CU * ‖x‖ := by
  calc ‖T (S (V x))‖ ≤ M * K * ‖V x‖ := UnforcedLeray.B0104.norm_apply_apply_le hT hS _
    _ ≤ M * K * (CU * ‖x‖) := mul_le_mul_of_nonneg_left
        ((V.le_opNorm x).trans (mul_le_mul_of_nonneg_right hV (norm_nonneg _)))
        (mul_nonneg hM hK)
    _ = M * K * CU * ‖x‖ := by ring

section Evolution

variable {B M K : ℝ} {F : ℝ → ℝ → H →L[ℂ] H} {A : ℝ → H →L[ℂ] H} {U : ℝ → ℝ → H →L[ℂ] H}

/-- Uniform exponential bound of the Duhamel evolution on the block triangle. -/
theorem norm_U_le
    (hU : UnforcedLeray.B0104.IsDuhamelEvolution (ι := Unit) B (fun _ => F) (fun _ => A)
      (fun _ => U))
    (hM : 0 ≤ M) (hF : ∀ t s, 0 ≤ s → s ≤ t → t ≤ B → ‖F t s‖ ≤ M)
    (hK : 0 ≤ K) (hA : ∀ r, 0 ≤ r → r ≤ B → ‖A r‖ ≤ K) :
    ∀ t s, 0 ≤ s → s ≤ t → t ≤ B → ‖U t s‖ ≤ 2 * M * Real.exp ((2 * (M * K) + 1) * B) := by
  intro t s hs hst htB
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  obtain ⟨C, hC⟩ := hU.bounded () s
  have hB0 : 0 ≤ B := hs.trans (hst.trans htB)
  have G := UnforcedLeray.B0104.gronwall_family (I := Unit) (fun _ t => ‖U t s x‖) (s := s)
    (B := B - s) (a := M * ‖x‖) (L := M * K) (C := C * ‖x‖) (by positivity) (by positivity)
    (fun _ t h1 h2 => ((U t s).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (hC t h1 (by linarith)) (norm_nonneg _)))
    (fun g hg t h1 h2 _ hφ _ => by
      have htB' : t ≤ B := by linarith
      rw [hU.duhamel () s t h1 (by linarith) x]
      calc ‖F t s x + ∫ r in s..t, F t r (A r (U r s x))‖
          ≤ ‖F t s x‖ + ‖∫ r in s..t, F t r (A r (U r s x))‖ := norm_add_le _ _
        _ ≤ M * ‖x‖ + ∫ r in s..t, M * K * g r := by
          refine add_le_add (((F t s).le_opNorm x).trans
            (mul_le_mul_of_nonneg_right (hF t s hs h1 htB') (norm_nonneg _))) ?_
          refine intervalIntegral.norm_integral_le_of_norm_le h1
            (ae_of_all _ fun r hr => ?_) ((hg.const_mul _).intervalIntegrable _ _)
          calc ‖F t r (A r (U r s x))‖ ≤ M * K * ‖U r s x‖ :=
                UnforcedLeray.B0104.norm_apply_apply_le
                  (hF t r (hs.trans hr.1.le) hr.2 htB')
                  (hA r (hs.trans hr.1.le) (hr.2.trans htB')) _
            _ ≤ M * K * g r :=
                mul_le_mul_of_nonneg_left (hφ () r hr.1.le hr.2) (by positivity)
        _ = M * ‖x‖ + M * K * ∫ r in s..t, g r := by
          rw [intervalIntegral.integral_const_mul]) () t hst (by linarith)
  calc ‖U t s x‖ ≤ 2 * (M * ‖x‖) * Real.exp ((2 * (M * K) + 1) * (t - s)) := G
    _ ≤ 2 * (M * ‖x‖) * Real.exp ((2 * (M * K) + 1) * B) := by
        gcongr
        linarith
    _ = 2 * M * Real.exp ((2 * (M * K) + 1) * B) * ‖x‖ := by ring

/-- Gronwall comparison of the evolutions started at `s ≤ s'` (extended by `U(t,t)` before the
start). -/
theorem norm_U_min_sub_le {CU ω : ℝ}
    (hU : UnforcedLeray.B0104.IsDuhamelEvolution (ι := Unit) B (fun _ => F) (fun _ => A)
      (fun _ => U))
    (hM : 0 ≤ M) (hF : ∀ t s, 0 ≤ s → s ≤ t → t ≤ B → ‖F t s‖ ≤ M)
    (hK : 0 ≤ K) (hA : ∀ r, 0 ≤ r → r ≤ B → ‖A r‖ ≤ K)
    (hCU : ∀ t s, 0 ≤ s → s ≤ t → t ≤ B → ‖U t s‖ ≤ CU) (x : H) {s s' : ℝ} (hs : 0 ≤ s)
    (hss' : s ≤ s') (hs'B : s' ≤ B)
    (hω : ∀ t, 0 ≤ t → t ≤ B → ‖F t (min s t) x - F t (min s' t) x‖ ≤ ω) :
    ∀ t, 0 ≤ t → t ≤ B → ‖U t (min s t) x - U t (min s' t) x‖ ≤
      2 * (ω + M * K * CU * ‖x‖ * (s' - s)) * Real.exp ((2 * (M * K) + 1) * B) := by
  have hB0 : 0 ≤ B := hs.trans (hss'.trans hs'B)
  have hω0 : 0 ≤ ω := (norm_nonneg _).trans (hω 0 le_rfl hB0)
  have hCU0 : 0 ≤ CU := (norm_nonneg _).trans (hCU 0 0 le_rfl le_rfl hB0)
  have hκ : 0 ≤ M * K * CU * ‖x‖ := by positivity
  have hUx : ∀ t σ, 0 ≤ σ → σ ≤ t → t ≤ B → ‖U t σ x‖ ≤ CU * ‖x‖ := fun t σ h0 h1 h2 =>
    ((U t σ).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hCU t σ h0 h1 h2) (norm_nonneg _))
  intro t ht0 htB
  have G := UnforcedLeray.B0104.gronwall_family (I := Unit)
    (fun _ t => ‖U t (min s t) x - U t (min s' t) x‖) (s := 0) (B := B)
    (a := ω + M * K * CU * ‖x‖ * (s' - s)) (L := M * K) (C := CU * ‖x‖ + CU * ‖x‖)
    (by nlinarith) (by positivity)
    (fun _ t h1 h2 => (norm_sub_le _ _).trans (add_le_add
      (hUx t _ (le_min hs h1) (min_le_right _ _) (by linarith))
      (hUx t _ (le_min (hs.trans hss') h1) (min_le_right _ _) (by linarith))))
    (fun g hg t h1 h2 hg0 hφ _ => by
      have htB : t ≤ B := by linarith
      have hint : 0 ≤ M * K * ∫ r in (0 : ℝ)..t, g r :=
        mul_nonneg (mul_nonneg hM hK)
          (intervalIntegral.integral_nonneg h1 fun r hr => hg0 r hr.1 hr.2)
      have hωt := hω t h1 htB
      rcases le_or_gt t s with hts | hst
      · rw [min_eq_right hts, min_eq_right (hts.trans hss'), sub_self, norm_zero]
        nlinarith
      rcases le_or_gt t s' with hts' | hs't
      · rw [min_eq_left hst.le, min_eq_right hts'] at hωt ⊢
        have hd := hU.duhamel () s t hst.le (by linarith) x
        have hd' := hU.duhamel () t t le_rfl (by linarith) x
        rw [intervalIntegral.integral_same, add_zero] at hd'
        rw [hd, hd']
        have hI : ‖∫ r in s..t, F t r (A r (U r s x))‖ ≤ M * K * CU * ‖x‖ * (s' - s) := by
          calc ‖∫ r in s..t, F t r (A r (U r s x))‖ ≤ M * K * CU * ‖x‖ * |t - s| := by
                refine intervalIntegral.norm_integral_le_of_norm_le_const fun r hr => ?_
                rw [Set.uIoc_of_le hst.le] at hr
                exact norm_FAU_le (hF t r (hs.trans hr.1.le) hr.2 htB)
                  (hA r (hs.trans hr.1.le) (hr.2.trans htB))
                  (hCU r s hs hr.1.le (hr.2.trans htB)) hM hK x
            _ ≤ M * K * CU * ‖x‖ * (s' - s) := by
                rw [abs_of_nonneg (by linarith)]
                exact mul_le_mul_of_nonneg_left (by linarith) hκ
        calc ‖(F t s x + ∫ r in s..t, F t r (A r (U r s x))) - F t t x‖
            = ‖(F t s x - F t t x) + ∫ r in s..t, F t r (A r (U r s x))‖ := by
              congr 1; abel
          _ ≤ ‖F t s x - F t t x‖ + ‖∫ r in s..t, F t r (A r (U r s x))‖ := norm_add_le _ _
          _ ≤ ω + M * K * CU * ‖x‖ * (s' - s) := add_le_add hωt hI
          _ ≤ _ := by linarith
      · rw [min_eq_left hst.le, min_eq_left hs't.le] at hωt ⊢
        have hd := hU.duhamel () s t hst.le (by linarith) x
        have hd' := hU.duhamel () s' t hs't.le (by linarith) x
        have hi := hU.integrable () s t hst.le (by linarith) x
        have hi' := hU.integrable () s' t hs't.le (by linarith) x
        have hi1 : IntervalIntegrable (fun r => F t r (A r (U r s x))) volume s s' :=
          hi.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc
            (Set.mem_uIcc_of_le hss' hs't.le))
        have hi2 : IntervalIntegrable (fun r => F t r (A r (U r s x))) volume s' t :=
          hi.mono_set (Set.uIcc_subset_uIcc (Set.mem_uIcc_of_le hss' hs't.le)
            Set.right_mem_uIcc)
        rw [hd, hd', ← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
        have hI1 : ‖∫ r in s..s', F t r (A r (U r s x))‖ ≤ M * K * CU * ‖x‖ * (s' - s) := by
          calc ‖∫ r in s..s', F t r (A r (U r s x))‖ ≤ M * K * CU * ‖x‖ * |s' - s| := by
                refine intervalIntegral.norm_integral_le_of_norm_le_const fun r hr => ?_
                rw [Set.uIoc_of_le hss'] at hr
                exact norm_FAU_le (hF t r (hs.trans hr.1.le) (hr.2.trans hs't.le) htB)
                  (hA r (hs.trans hr.1.le) (hr.2.trans hs'B))
                  (hCU r s hs hr.1.le (hr.2.trans hs'B)) hM hK x
            _ = M * K * CU * ‖x‖ * (s' - s) := by rw [abs_of_nonneg (by linarith)]
        have hI2 : ‖∫ r in s'..t, (F t r (A r (U r s x)) - F t r (A r (U r s' x)))‖ ≤
            M * K * ∫ r in (0 : ℝ)..t, g r := by
          calc ‖∫ r in s'..t, (F t r (A r (U r s x)) - F t r (A r (U r s' x)))‖
              ≤ ∫ r in s'..t, M * K * g r := by
                refine intervalIntegral.norm_integral_le_of_norm_le hs't.le
                  (ae_of_all _ fun r hr => ?_) ((hg.const_mul _).intervalIntegrable _ _)
                have hr0 : 0 ≤ r := (hs.trans hss').trans hr.1.le
                rw [← map_sub, ← map_sub]
                have hφr := hφ () r hr0 hr.2
                rw [min_eq_left (hss'.trans hr.1.le), min_eq_left hr.1.le] at hφr
                calc ‖F t r (A r (U r s x - U r s' x))‖ ≤ M * K * ‖U r s x - U r s' x‖ :=
                      UnforcedLeray.B0104.norm_apply_apply_le (hF t r hr0 hr.2 htB)
                        (hA r hr0 (hr.2.trans htB)) _
                  _ ≤ M * K * g r := mul_le_mul_of_nonneg_left hφr (mul_nonneg hM hK)
            _ ≤ ∫ r in (0 : ℝ)..t, M * K * g r := by
                refine intervalIntegral.integral_mono_interval (hs.trans hss') hs't.le le_rfl
                  ?_ ((hg.const_mul _).intervalIntegrable _ _)
                filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
                exact mul_nonneg (mul_nonneg hM hK) (hg0 r hr.1.le hr.2)
            _ = M * K * ∫ r in (0 : ℝ)..t, g r := intervalIntegral.integral_const_mul _ _
        have hsplit : F t s x + ((∫ r in s..s', F t r (A r (U r s x))) +
              ∫ r in s'..t, F t r (A r (U r s x))) -
            (F t s' x + ∫ r in s'..t, F t r (A r (U r s' x))) =
            (F t s x - F t s' x) + (∫ r in s..s', F t r (A r (U r s x))) +
              ∫ r in s'..t, (F t r (A r (U r s x)) - F t r (A r (U r s' x))) := by
          rw [intervalIntegral.integral_sub hi2 hi']
          abel
        rw [hsplit]
        calc ‖(F t s x - F t s' x) + (∫ r in s..s', F t r (A r (U r s x))) +
              ∫ r in s'..t, (F t r (A r (U r s x)) - F t r (A r (U r s' x)))‖
            ≤ ‖F t s x - F t s' x‖ + ‖∫ r in s..s', F t r (A r (U r s x))‖ +
              ‖∫ r in s'..t, (F t r (A r (U r s x)) - F t r (A r (U r s' x)))‖ :=
              norm_add₃_le
          _ ≤ ω + M * K * CU * ‖x‖ * (s' - s) + M * K * ∫ r in (0 : ℝ)..t, g r := by
              gcongr) () t ht0 (by linarith)
  calc ‖U t (min s t) x - U t (min s' t) x‖
      ≤ 2 * (ω + M * K * CU * ‖x‖ * (s' - s)) * Real.exp ((2 * (M * K) + 1) * (t - 0)) := G
    _ ≤ 2 * (ω + M * K * CU * ‖x‖ * (s' - s)) * Real.exp ((2 * (M * K) + 1) * B) := by
        have : 0 ≤ 2 * (ω + M * K * CU * ‖x‖ * (s' - s)) := by nlinarith
        gcongr
        linarith

end Evolution

end UnforcedLeray.Short.IIIa.DuhamelAbstractSub
