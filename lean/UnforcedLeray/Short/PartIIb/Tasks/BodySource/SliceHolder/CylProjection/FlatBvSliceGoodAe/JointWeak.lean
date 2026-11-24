import UnforcedLeray.Short.PartIIb.Tasks.BodySource.SliceHolder.CylProjection.FlatBvSliceGoodAe.Needed
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# `PartII-b:F5/2/2/2/1` (`JointWeakToSlice`): Fubini disintegration of joint weak derivatives

Proves `UnforcedLeray.Short.IIb.FlatBvSliceGoodAeNeeded.JointWeakToSlice` (SP lines 2213-2239).
-/

noncomputable section

namespace UnforcedLeray.Short.IIb.FlatBvSliceGoodAeJointWeak

open MeasureTheory Set Filter Topology
open scoped ContDiff

private lemma coord_fst_snd_eq (x : Coord) : (x.1, x.2) = x := by
  ext <;> rfl

/-! ### Smooth `c`-periodic partition of unity on `ℝ` -/

section Partition

private def qBump (c : ℝ) (hc : 0 < c) : ContDiffBump (0 : ℝ) where
  rIn := c / 2
  rOut := c
  rIn_pos := half_pos hc
  rIn_lt_rOut := half_lt_self hc

private def qBumpSum (c : ℝ) (hc : 0 < c) (q : ℝ) : ℝ :=
  ∑' k : ℤ, qBump c hc (q + (k : ℝ) * c)

private lemma qBump_eq_zero_of_abs_ge {c : ℝ} (hc : 0 < c) {q : ℝ} (hq : c ≤ |q|) :
    qBump c hc q = 0 := by
  apply (qBump c hc).zero_of_le_dist
  dsimp [qBump]
  simpa [Real.dist_eq, sub_zero] using hq

private lemma qBump_eq_one_of_abs_le {c : ℝ} (hc : 0 < c) {q : ℝ} (hq : |q| ≤ c / 2) :
    qBump c hc q = 1 := by
  apply (qBump c hc).one_of_mem_closedBall
  dsimp [qBump]
  simpa [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hq

private lemma qBump_shift_eq_zero_of_large {c : ℝ} (hc : 0 < c) {a b : ℝ} :
    ∃ N : ℕ, ∀ q ∈ Ioo a b, ∀ k : ℤ, k ∉ Finset.Icc (-(N : ℤ)) (N : ℤ) →
      qBump c hc (q + (k : ℝ) * c) = 0 := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((max |a| |b|) / c + 1)
  refine ⟨N, fun q hq k hk => ?_⟩
  have hq_abs : |q| ≤ max |a| |b| := by
    rw [abs_le]
    have ha : -max |a| |b| ≤ a := neg_le_of_abs_le (le_max_left _ _)
    have hb : b ≤ max |a| |b| := le_trans (le_abs_self _) (le_max_right _ _)
    exact ⟨by linarith [hq.1], by linarith [hq.2]⟩
  apply qBump_eq_zero_of_abs_ge hc
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hk
  have hk_abs : (N : ℝ) + 1 ≤ |(k : ℝ)| := by
    have hk_int : (N : ℤ) + 1 ≤ |k| := by
      rcases hk with hk | hk
      · rw [abs_of_neg (by omega)]; omega
      · rw [abs_of_nonneg (by omega)]; omega
    have hk_r : ((N : ℤ) + 1 : ℝ) ≤ (|k| : ℝ) := by exact_mod_cast hk_int
    simpa [Int.cast_abs] using hk_r
  have h1 : c < |(k : ℝ)| * c - |q| := by
    have hNc : max |a| |b| + c < (N : ℝ) * c := by
      have := mul_lt_mul_of_pos_right hN hc
      field_simp [hc.ne'] at this ⊢
      linarith
    have hkc : ((N : ℝ) + 1) * c ≤ |(k : ℝ)| * c := mul_le_mul_of_nonneg_right hk_abs hc.le
    linarith
  have h2 : |(k : ℝ)| * c - |q| ≤ |q + (k : ℝ) * c| := by
    have := abs_sub_abs_le_abs_add ((k : ℝ) * c) q
    rw [add_comm, abs_mul, abs_of_pos hc] at this
    linarith
  linarith

private lemma qBumpSum_eq_finset {c : ℝ} (hc : 0 < c) {a b : ℝ} :
    ∃ N : ℕ, ∀ q ∈ Ioo a b,
      qBumpSum c hc q = ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), qBump c hc (q + (k : ℝ) * c) := by
  obtain ⟨N, hN⟩ := qBump_shift_eq_zero_of_large hc (a := a) (b := b)
  exact ⟨N, fun q hq => tsum_eq_sum (hN q hq)⟩

private lemma qBumpSum_summable {c : ℝ} (hc : 0 < c) (q : ℝ) :
    Summable (fun k : ℤ => qBump c hc (q + (k : ℝ) * c)) := by
  obtain ⟨N, hN⟩ := qBump_shift_eq_zero_of_large hc (a := q - 1) (b := q + 1)
  exact summable_of_ne_finset_zero (s := Finset.Icc (-(N : ℤ)) (N : ℤ))
    (fun k hk => hN q ⟨by linarith, by linarith⟩ k hk)

private lemma qBumpSum_contDiff {c : ℝ} (hc : 0 < c) : ContDiff ℝ ∞ (qBumpSum c hc) := by
  rw [contDiff_iff_contDiffAt]
  intro q₀
  obtain ⟨N, hN⟩ := qBumpSum_eq_finset hc (a := q₀ - 1) (b := q₀ + 1)
  have h_eq : qBumpSum c hc =ᶠ[𝓝 q₀]
      fun q => ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), qBump c hc (q + (k : ℝ) * c) :=
    Filter.eventually_of_mem (Ioo_mem_nhds (by linarith) (by linarith)) hN
  refine ContDiffAt.congr_of_eventuallyEq ?_ h_eq
  refine ContDiff.contDiffAt ?_
  refine ContDiff.sum fun k _ => ?_
  exact (qBump c hc).contDiff.comp (contDiff_id.add contDiff_const)

private lemma one_le_qBumpSum {c : ℝ} (hc : 0 < c) (q : ℝ) : 1 ≤ qBumpSum c hc q := by
  let k : ℤ := -⌊q / c + 1 / 2⌋
  have h1 : (⌊q / c + 1 / 2⌋ : ℝ) ≤ q / c + 1 / 2 := Int.floor_le _
  have h2 : q / c + 1 / 2 < (⌊q / c + 1 / 2⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have hk_mem : |q + (k : ℝ) * c| ≤ c / 2 := by
    have hk_eq : q + (k : ℝ) * c = c * (q / c - (⌊q / c + 1 / 2⌋ : ℝ)) := by
      simp only [k, Int.cast_neg]
      field_simp [hc.ne']
      ring
    rw [hk_eq, abs_mul, abs_of_pos hc, show c / 2 = c * (1 / 2) by ring,
      mul_le_mul_iff_right₀ hc, abs_le]
    constructor <;> nlinarith
  have h_one : qBump c hc (q + (k : ℝ) * c) = 1 := qBump_eq_one_of_abs_le hc hk_mem
  rw [← h_one]
  exact (qBumpSum_summable hc q).le_tsum k (fun m _ => (qBump c hc).nonneg)

private lemma qBumpSum_periodic {c : ℝ} (hc : 0 < c) (q : ℝ) :
    qBumpSum c hc (q + c) = qBumpSum c hc q := by
  simp only [qBumpSum]
  have e : (fun k : ℤ => qBump c hc (q + c + (k : ℝ) * c)) =
      (fun k : ℤ => qBump c hc (q + ((k + 1 : ℤ) : ℝ) * c)) := by
    funext k
    push_cast
    ring_nf
  rw [e]
  exact (Equiv.addRight (1 : ℤ)).tsum_eq (fun k : ℤ => qBump c hc (q + (k : ℝ) * c))

private def qPart (c : ℝ) (hc : 0 < c) (q : ℝ) : ℝ :=
  qBump c hc q / qBumpSum c hc q

private lemma qPart_contDiff {c : ℝ} (hc : 0 < c) : ContDiff ℝ ∞ (qPart c hc) :=
  (qBump c hc).contDiff.div (qBumpSum_contDiff hc) fun q => by linarith [one_le_qBumpSum hc q]

private lemma qPart_eq_zero_of_abs_ge {c : ℝ} (hc : 0 < c) {q : ℝ} (hq : c ≤ |q|) :
    qPart c hc q = 0 := by
  simp [qPart, qBump_eq_zero_of_abs_ge hc hq]

private lemma qPart_hasCompactSupport {c : ℝ} (hc : 0 < c) : HasCompactSupport (qPart c hc) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -c) (b := c)) ?_
  intro q hq
  by_contra h
  rw [mem_Icc, not_and_or, not_le, not_le] at h
  have hq_abs : c ≤ |q| := by
    rcases h with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
  exact hq (qPart_eq_zero_of_abs_ge hc hq_abs)

private lemma qBumpSum_periodic_int {c : ℝ} (hc : 0 < c) (q : ℝ) (k : ℤ) :
    qBumpSum c hc (q + (k : ℝ) * c) = qBumpSum c hc q := by
  simp only [qBumpSum]
  have e : (fun m : ℤ => qBump c hc (q + (k : ℝ) * c + (m : ℝ) * c)) =
      (fun m : ℤ => qBump c hc (q + ((m + k : ℤ) : ℝ) * c)) := by
    funext m; push_cast; ring_nf
  rw [e]
  exact (Equiv.addRight k).tsum_eq (fun m : ℤ => qBump c hc (q + (m : ℝ) * c))

private lemma qPart_sum_eq_one {c : ℝ} (hc : 0 < c) {q : ℝ} (hq : q ∈ Ioo (-c) c) :
    ∑ k ∈ Finset.Icc (-1 : ℤ) 1, qPart c hc (q + (k : ℝ) * c) = 1 := by
  have hsum_eq : ∑ k ∈ Finset.Icc (-1 : ℤ) 1, qBump c hc (q + (k : ℝ) * c) = qBumpSum c hc q := by
    symm
    refine tsum_eq_sum fun k hk => ?_
    apply qBump_eq_zero_of_abs_ge hc
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hk
    have hq1 : -c < q := hq.1
    have hq2 : q < c := hq.2
    rcases hk with hk | hk
    · have hk' : (k : ℝ) ≤ -2 := by exact_mod_cast Int.le_sub_one_of_lt hk
      have hkc : (k : ℝ) * c ≤ -2 * c := by nlinarith
      rw [abs_of_neg (by linarith)]
      linarith
    · have hk' : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Int.add_one_le_of_lt hk
      have hkc : 2 * c ≤ (k : ℝ) * c := by nlinarith
      rw [abs_of_nonneg (by linarith)]
      linarith
  have hpos : qBumpSum c hc q ≠ 0 := by linarith [one_le_qBumpSum hc q]
  calc ∑ k ∈ Finset.Icc (-1 : ℤ) 1, qPart c hc (q + (k : ℝ) * c)
      = ∑ k ∈ Finset.Icc (-1 : ℤ) 1, qBump c hc (q + (k : ℝ) * c) / qBumpSum c hc q := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [qPart, qBumpSum_periodic_int hc q k]
    _ = (∑ k ∈ Finset.Icc (-1 : ℤ) 1, qBump c hc (q + (k : ℝ) * c)) / qBumpSum c hc q := by
        rw [← Finset.sum_div]
    _ = 1 := by rw [hsum_eq, div_self hpos]

private lemma deriv_qPart_sum_eq_zero {c : ℝ} (hc : 0 < c) {q : ℝ} (hq : q ∈ Ioo (-c) c) :
    ∑ k ∈ Finset.Icc (-1 : ℤ) 1, deriv (qPart c hc) (q + (k : ℝ) * c) = 0 := by
  have h_ev : (fun t : ℝ => ∑ k ∈ Finset.Icc (-1 : ℤ) 1, qPart c hc (t + (k : ℝ) * c)) =ᶠ[𝓝 q]
      fun _ => (1 : ℝ) :=
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hq) fun t ht => qPart_sum_eq_one hc ht
  have hd : deriv (fun t : ℝ => ∑ k ∈ Finset.Icc (-1 : ℤ) 1, qPart c hc (t + (k : ℝ) * c)) q = 0 := by
    rw [h_ev.deriv_eq, deriv_const]
  have h_sum_deriv : HasDerivAt (fun t : ℝ => ∑ k ∈ Finset.Icc (-1 : ℤ) 1, qPart c hc (t + (k : ℝ) * c))
      (∑ k ∈ Finset.Icc (-1 : ℤ) 1, deriv (qPart c hc) (q + (k : ℝ) * c)) q := by
    refine HasDerivAt.fun_sum fun k _ => ?_
    have hdiff : HasDerivAt (qPart c hc) (deriv (qPart c hc) (q + (k : ℝ) * c)) (q + (k : ℝ) * c) :=
      ((qPart_contDiff hc).differentiable (by simp)).differentiableAt.hasDerivAt
    simpa [Function.comp_def] using hdiff.comp q ((hasDerivAt_id q).add_const ((k : ℝ) * c))
  linarith [h_sum_deriv.deriv]

end Partition

/-! ### Coordinate test functions and `coordTranspose` -/

section TestFun

private def cylCoordTest (θ χ : ℝ → ℝ) (ψ : ℝ × ℝ → ℝ) (x : Coord) : ℝ :=
  θ x.1 * χ x.2.1 * ψ x.2

private lemma isCoordTest_cylCoordTest {c : ℝ} {θ χ : ℝ → ℝ} {ψ : ℝ × ℝ → ℝ}
    (hθ_s : ContDiff ℝ ∞ θ) (hθ_c : HasCompactSupport θ) (hθ_i : tsupport θ ⊆ Ioi 0)
    (hχ_s : ContDiff ℝ ∞ χ) (hχ_c : HasCompactSupport χ)
    (hψ : B0579.IsCylTest c ψ) :
    IsCoordTest (cylCoordTest θ χ ψ) where
  smooth := ((hθ_s.comp contDiff_fst).mul (hχ_s.comp (contDiff_fst.comp contDiff_snd))).mul
    (hψ.smooth.comp contDiff_snd)
  compact := by
    obtain ⟨R, hR⟩ := hψ.band
    have hK_χ : IsCompact (tsupport χ) := hχ_c
    have hK_θ : IsCompact (tsupport θ) := hθ_c
    have hK : IsCompact (tsupport θ ×ˢ (tsupport χ ×ˢ Icc (-|R|) |R|)) :=
      hK_θ.prod (hK_χ.prod isCompact_Icc)
    refine HasCompactSupport.of_support_subset_isCompact hK ?_
    intro x hx
    rw [Function.mem_support] at hx
    refine ⟨?_, ?_, ?_⟩
    · exact subset_tsupport θ (fun h => hx (by simp [cylCoordTest, h]))
    · exact subset_tsupport χ (fun h => hx (by simp [cylCoordTest, h]))
    · rw [mem_Icc]
      by_contra hη
      have hgt : R < |x.2.2| := by
        rw [← abs_le] at hη
        exact lt_of_le_of_lt (le_abs_self R) (lt_of_not_ge hη)
      exact hx (by simp [cylCoordTest, hR x.2 hgt])
  supp := by
    intro x hx
    refine ⟨hθ_i ?_, trivial⟩
    by_contra hxθ
    have hU : (tsupport θ)ᶜ ×ˢ (univ : Set (ℝ × ℝ)) ∈ 𝓝 x :=
      ((isClosed_tsupport (f := θ)).isOpen_compl.prod isOpen_univ).mem_nhds ⟨hxθ, trivial⟩
    have hev : cylCoordTest θ χ ψ =ᶠ[𝓝 x] fun _ => 0 := by
      refine Filter.eventually_of_mem hU fun y hy => ?_
      have hy0 : θ y.1 = 0 := by
        by_contra hne
        exact hy.1 (subset_tsupport θ hne)
      simp [cylCoordTest, hy0]
    exact absurd hx (notMem_tsupport_iff_eventuallyEq.2 hev)

private lemma coordTranspose_cylCoordTest_0 {c : ℝ} {θ χ : ℝ → ℝ} {ψ : ℝ × ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hχ : ContDiff ℝ ∞ χ) (hψ : B0579.IsCylTest c ψ) (x : Coord) :
    coordTranspose vQ0 dZero (cylCoordTest θ χ ψ) x =
      -(θ x.1 * (deriv χ x.2.1 * ψ x.2 + χ x.2.1 * B0579.pd 0 ψ x.2)) := by
  have hφ_diff : Differentiable ℝ (cylCoordTest θ χ ψ) :=
    ((hθ.comp contDiff_fst).mul (hχ.comp (contDiff_fst.comp contDiff_snd))).mul
      (hψ.smooth.comp contDiff_snd) |>.differentiable (by simp)
  have hcp0 : cpd 0 (fun y => vQ0 y 0 * cylCoordTest θ χ ψ y) x = 0 := by
    simp [vQ0, cpd]
  have hcp2 : cpd 2 (fun y => vQ0 y 2 * cylCoordTest θ χ ψ y) x = 0 := by
    simp [vQ0, cpd]
  have hcp1 : cpd 1 (fun y => vQ0 y 1 * cylCoordTest θ χ ψ y) x =
      θ x.1 * (deriv χ x.2.1 * ψ x.2 + χ x.2.1 * B0579.pd 0 ψ x.2) := by
    have hv1 : (fun y => vQ0 y 1 * cylCoordTest θ χ ψ y) = cylCoordTest θ χ ψ := by
      funext y; simp [vQ0]
    rw [hv1, cpd]
    have hc1 : cdir 1 = (0, (1, 0)) := rfl
    rw [hc1]
    have h_curve : HasDerivAt (fun t : ℝ => cylCoordTest θ χ ψ (x + t • ((0, (1, 0)) : Coord)))
        (fderiv ℝ (cylCoordTest θ χ ψ) x (0, (1, 0))) 0 := by
      have h1 : HasFDerivAt (cylCoordTest θ χ ψ) (fderiv ℝ (cylCoordTest θ χ ψ) x) (x + (0 : ℝ) • (0, (1, 0))) := by
        simpa using (hφ_diff x).hasFDerivAt
      have h2 : HasDerivAt (fun t : ℝ => x + t • ((0, (1, 0)) : Coord)) (0, (1, 0)) 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).smul_const ((0, (1, 0)) : Coord) |>.const_add x
      exact h1.comp_hasDerivAt 0 h2
    have h_curve2 : HasDerivAt (fun t : ℝ => cylCoordTest θ χ ψ (x + t • ((0, (1, 0)) : Coord)))
        (θ x.1 * (deriv χ x.2.1 * ψ x.2 + χ x.2.1 * B0579.pd 0 ψ x.2)) 0 := by
      have heq : (fun t : ℝ => cylCoordTest θ χ ψ (x + t • ((0, (1, 0)) : Coord))) =
          fun t : ℝ => θ x.1 * (χ (x.2.1 + t) * ψ (x.2 + t • ((1, 0) : ℝ × ℝ))) := by
        funext t
        simp [cylCoordTest, Prod.smul_mk, mul_assoc]
      rw [heq]
      have hχd : HasDerivAt (fun t : ℝ => χ (x.2.1 + t)) (deriv χ x.2.1) 0 := by
        have h := ((hχ.differentiable (by simp) (x.2.1 + 0)).hasDerivAt).comp 0
          ((hasDerivAt_id (0 : ℝ)).const_add x.2.1)
        simpa [Function.comp_def] using h
      have hψd : HasDerivAt (fun t : ℝ => ψ (x.2 + t • ((1, 0) : ℝ × ℝ))) (B0579.pd 0 ψ x.2) 0 := by
        have h1 : HasFDerivAt ψ (fderiv ℝ ψ x.2) (x.2 + (0 : ℝ) • ((1, 0) : ℝ × ℝ)) := by
          simpa using (hψ.differentiable x.2).hasFDerivAt
        have h2 : HasDerivAt (fun t : ℝ => x.2 + t • ((1, 0) : ℝ × ℝ)) ((1, 0) : ℝ × ℝ) 0 := by
          simpa using (hasDerivAt_id (0 : ℝ)).smul_const ((1, 0) : ℝ × ℝ) |>.const_add x.2
        simpa [B0579.pd, B0579.dir, Function.comp_def] using h1.comp_hasDerivAt 0 h2
      simpa using (hχd.mul hψd).const_mul (θ x.1)
    exact h_curve.unique h_curve2
  simp [coordTranspose, Fin.sum_univ_three, hcp0, hcp1, hcp2, dZero]

private lemma coordTranspose_cylCoordTest_1 {c : ℝ} {θ χ : ℝ → ℝ} {ψ : ℝ × ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hχ : ContDiff ℝ ∞ χ) (hψ : B0579.IsCylTest c ψ) (x : Coord) :
    coordTranspose vEta dZero (cylCoordTest θ χ ψ) x =
      -(θ x.1 * χ x.2.1 * B0579.pd 1 ψ x.2) := by
  have hφ_diff : Differentiable ℝ (cylCoordTest θ χ ψ) :=
    ((hθ.comp contDiff_fst).mul (hχ.comp (contDiff_fst.comp contDiff_snd))).mul
      (hψ.smooth.comp contDiff_snd) |>.differentiable (by simp)
  have hcp0 : cpd 0 (fun y => vEta y 0 * cylCoordTest θ χ ψ y) x = 0 := by
    simp [vEta, cpd]
  have hcp1 : cpd 1 (fun y => vEta y 1 * cylCoordTest θ χ ψ y) x = 0 := by
    simp [vEta, cpd]
  have hcp2 : cpd 2 (fun y => vEta y 2 * cylCoordTest θ χ ψ y) x =
      θ x.1 * χ x.2.1 * B0579.pd 1 ψ x.2 := by
    have hv2 : (fun y => vEta y 2 * cylCoordTest θ χ ψ y) = cylCoordTest θ χ ψ := by
      funext y; simp [vEta]
    rw [hv2, cpd]
    have hc2 : cdir 2 = (0, (0, 1)) := rfl
    rw [hc2]
    have h_curve : HasDerivAt (fun t : ℝ => cylCoordTest θ χ ψ (x + t • ((0, (0, 1)) : Coord)))
        (fderiv ℝ (cylCoordTest θ χ ψ) x (0, (0, 1))) 0 := by
      have h1 : HasFDerivAt (cylCoordTest θ χ ψ) (fderiv ℝ (cylCoordTest θ χ ψ) x) (x + (0 : ℝ) • (0, (0, 1))) := by
        simpa using (hφ_diff x).hasFDerivAt
      have h2 : HasDerivAt (fun t : ℝ => x + t • ((0, (0, 1)) : Coord)) (0, (0, 1)) 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).smul_const ((0, (0, 1)) : Coord) |>.const_add x
      exact h1.comp_hasDerivAt 0 h2
    have h_curve2 : HasDerivAt (fun t : ℝ => cylCoordTest θ χ ψ (x + t • ((0, (0, 1)) : Coord)))
        (θ x.1 * χ x.2.1 * B0579.pd 1 ψ x.2) 0 := by
      have heq : (fun t : ℝ => cylCoordTest θ χ ψ (x + t • ((0, (0, 1)) : Coord))) =
          fun t : ℝ => (θ x.1 * χ x.2.1) * ψ (x.2 + t • ((0, 1) : ℝ × ℝ)) := by
        funext t
        simp [cylCoordTest, Prod.smul_mk]
      rw [heq]
      have hψd : HasDerivAt (fun t : ℝ => ψ (x.2 + t • ((0, 1) : ℝ × ℝ))) (B0579.pd 1 ψ x.2) 0 := by
        have h1 : HasFDerivAt ψ (fderiv ℝ ψ x.2) (x.2 + (0 : ℝ) • ((0, 1) : ℝ × ℝ)) := by
          simpa using (hψ.differentiable x.2).hasFDerivAt
        have h2 : HasDerivAt (fun t : ℝ => x.2 + t • ((0, 1) : ℝ × ℝ)) ((0, 1) : ℝ × ℝ) 0 := by
          simpa using (hasDerivAt_id (0 : ℝ)).smul_const ((0, 1) : ℝ × ℝ) |>.const_add x.2
        simpa [B0579.pd, B0579.dir, Function.comp_def] using h1.comp_hasDerivAt 0 h2
      simpa using hψd.const_mul (θ x.1 * χ x.2.1)
    exact h_curve.unique h_curve2
  simp [coordTranspose, Fin.sum_univ_three, hcp0, hcp1, hcp2, dZero]

end TestFun

/-! ### `QPeriodic` shift invariance and cell unfolding -/

section Periodicity

private lemma qShift_measurePreserving (c : ℝ) :
    MeasurePreserving (qShift c) (volume.restrict {x : Coord | 0 < x.1})
      (volume.restrict {x : Coord | 0 < x.1}) := by
  have he : qShift c = fun x : Coord => x + ((0, (c, 0)) : Coord) := by
    funext x; ext <;> simp [qShift]
  rw [he]
  refine ⟨measurable_add_const _, ?_⟩
  ext s hs
  rw [Measure.map_apply (measurable_add_const _) hs,
    Measure.restrict_apply (measurable_add_const _ hs),
    Measure.restrict_apply hs]
  have hpre : (fun x : Coord => x + (0, (c, 0))) ⁻¹' (s ∩ {x : Coord | 0 < x.1}) =
      ((fun x : Coord => x + (0, (c, 0))) ⁻¹' s) ∩ {x : Coord | 0 < x.1} := by
    ext x; simp
  rw [← hpre]
  have hmp : MeasurePreserving (fun x : Coord => x + ((0, (c, 0)) : Coord)) volume volume :=
    measurePreserving_add_right volume ((0, (c, 0)) : Coord)
  exact hmp.measure_preimage (hs.inter (measurableSet_lt measurable_const measurable_fst)).nullMeasurableSet

private lemma qPeriodic_shift_k {c : ℝ} {b : CProf} (hb : QPeriodic c b) (k : ℤ) :
    ∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}),
      b (x.1, (x.2.1 + (k : ℝ) * c, x.2.2)) = b x := by
  have hmp := qShift_measurePreserving c
  have h1 : ∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}), b (qShift c x) = b x := hb
  have hm1 : ∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}),
      b (x.1, (x.2.1 - c, x.2.2)) = b x := by
    have hmp_inv : MeasurePreserving (fun x : Coord => x + ((0, (-c, 0)) : Coord))
        (volume.restrict {x : Coord | 0 < x.1}) (volume.restrict {x : Coord | 0 < x.1}) := by
      have := qShift_measurePreserving (-c)
      convert this using 1
      funext x; ext <;> simp [qShift]
    filter_upwards [hmp_inv.quasiMeasurePreserving.ae h1] with x hx
    have hq : qShift c (x + (0, (-c, 0))) = x := by ext <;> simp [qShift]
    rw [hq] at hx
    rw [show (x.1, (x.2.1 - c, x.2.2)) = x + ((0, (-c, 0)) : Coord) from by
      ext <;> simp [sub_eq_add_neg]]
    exact hx.symm
  induction k using Int.induction_on with
  | zero =>
    refine Eventually.of_forall fun x => ?_
    simp
  | succ k ih =>
    have hshift := hmp.quasiMeasurePreserving.ae ih
    filter_upwards [hshift, h1] with x hx1 hx2
    have hx_eq : (x.1, (x.2.1 + (((k : ℤ) + 1 : ℤ) : ℝ) * c, x.2.2)) =
        ((qShift c x).1, ((qShift c x).2.1 + ((k : ℤ) : ℝ) * c, (qShift c x).2.2)) := by
      ext <;> simp [qShift]; ring
    rw [hx_eq, hx1, hx2]
  | pred k ih =>
    have hmp_inv : MeasurePreserving (fun x : Coord => (x.1, (x.2.1 - c, x.2.2)))
        (volume.restrict {x : Coord | 0 < x.1}) (volume.restrict {x : Coord | 0 < x.1}) := by
      have := qShift_measurePreserving (-c)
      convert this using 1
      funext x; ext <;> simp [qShift, sub_eq_add_neg]
    have hshift := hmp_inv.quasiMeasurePreserving.ae ih
    filter_upwards [hshift, hm1] with x hx1 hx2
    have hx_eq : (x.1, (x.2.1 + ((-(k : ℤ) - 1 : ℤ) : ℝ) * c, x.2.2)) =
        ((x.1, (x.2.1 - c, x.2.2)).1,
          ((x.1, (x.2.1 - c, x.2.2)).2.1 + ((-(k : ℤ) : ℤ) : ℝ) * c, (x.1, (x.2.1 - c, x.2.2)).2.2)) := by
      ext <;> simp; ring
    rw [hx_eq, hx1, hx2]

private lemma B0579_periodic_k {c : ℝ} {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest c ψ)
    (k : ℤ) (z : ℝ × ℝ) : ψ (z.1 + (k : ℝ) * c, z.2) = ψ z := by
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have hthis : (z.1 + (((k : ℤ) + 1 : ℤ) : ℝ) * c, z.2) = (z.1 + ((k : ℤ) : ℝ) * c + c, z.2) := by
      push_cast; ring_nf
    have hp := hψ.periodic (z.1 + ((k : ℤ) : ℝ) * c, z.2)
    simp only at hp
    rw [hthis, hp, ih]
  | pred k ih =>
    have h := hψ.periodic (z.1 + ((-(k : ℤ) - 1 : ℤ) : ℝ) * c, z.2)
    have hthis : (z.1 + ((-(k : ℤ) - 1 : ℤ) : ℝ) * c + c, z.2) =
        (z.1 + ((-(k : ℤ) : ℤ) : ℝ) * c, z.2) := by
      push_cast; ring_nf
    simp only at h
    rw [hthis, ih] at h
    exact h.symm

private lemma integral_plane_unfold {c : ℝ} (hc : 0 < c) {F : ℝ × ℝ → ℂ}
    (hF_supp : ∀ z : ℝ × ℝ, c ≤ |z.1| → F z = 0)
    (hF_int : Integrable F) :
    ∫ z : ℝ × ℝ, F z =
      ∑ k ∈ Finset.Icc (-1 : ℤ) 1, ∫ z in B0579.cell c, F (z.1 + (k : ℝ) * c, z.2) := by
  let S : ℤ → Set (ℝ × ℝ) := fun k => Ico (-(c / 2) + (k : ℝ) * c) (c / 2 + (k : ℝ) * c) ×ˢ univ
  have h_eq_ind : ∫ z : ℝ × ℝ, F z = ∫ z in ⋃ k ∈ Finset.Icc (-1 : ℤ) 1, S k, F z := by
    symm
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_
    apply hF_supp
    by_contra hlt
    push Not at hlt
    rw [abs_lt] at hlt
    apply hz
    rw [mem_iUnion₂]
    by_cases h1 : z.1 < -(c / 2)
    · refine ⟨-1, by decide, ?_, trivial⟩
      simp only [Int.cast_neg, Int.cast_one, neg_one_mul]
      exact ⟨by linarith, by linarith⟩
    · push Not at h1
      by_cases h2 : z.1 < c / 2
      · refine ⟨0, by decide, ?_, trivial⟩
        simp only [Int.cast_zero, zero_mul, add_zero]
        exact ⟨h1, h2⟩
      · push Not at h2
        refine ⟨1, by decide, ?_, trivial⟩
        simp only [Int.cast_one, one_mul]
        exact ⟨by linarith, by linarith⟩
  rw [h_eq_ind, integral_biUnion_finset]
  · refine Finset.sum_congr rfl fun k _ => ?_
    have hshift : (fun z : ℝ × ℝ => z + ((k : ℝ) * c, 0)) ⁻¹' S k = B0579.cell c := by
      ext z
      simp only [S, B0579.cell, mem_preimage, mem_prod, mem_Ico, mem_univ, and_true,
        Prod.fst_add, Prod.snd_add]
      constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩
    have hmp : MeasurePreserving (fun z : ℝ × ℝ => z + ((k : ℝ) * c, 0)) volume volume :=
      measurePreserving_add_right volume ((k : ℝ) * c, 0)
    have h := hmp.setIntegral_preimage_emb (measurableEmbedding_addRight _) F (S k)
    rw [hshift] at h
    simpa [Prod.add_def, add_zero] using h.symm
  · intro k _
    exact measurableSet_Ico.prod MeasurableSet.univ
  · intro k _ l _ hkl
    change Disjoint (S k) (S l)
    rw [Set.disjoint_left]
    intro z hzk hzl
    simp only [S, mem_prod, mem_Ico, mem_univ, and_true] at hzk hzl
    have hkl' : k < l ∨ l < k := lt_or_gt_of_ne hkl
    rcases hkl' with hlt | hlt
    · have : (k : ℝ) + 1 ≤ l := by exact_mod_cast Int.add_one_le_of_lt hlt
      nlinarith
    · have : (l : ℝ) + 1 ≤ k := by exact_mod_cast Int.add_one_le_of_lt hlt
      nlinarith
  · intro k _
    exact hF_int.integrableOn

end Periodicity

/-! ### Main theorem -/

private lemma locallyIntegrableOn_slice {c : ℝ} (hc : 0 < c) (j : Fin 2) (U G : CProf)
    (hw : HasWeakVec (![vQ0, vEta] j) dZero U G)
    (i : Fin 2) (ψ : ℝ × ℝ → ℝ) (hψ : B0579.IsCylTest c ψ) :
    LocallyIntegrableOn
      (fun s => ∫ z in B0579.cell c, G (s, z) i * (ψ z : ℂ) + U (s, z) i * (B0579.pd j ψ z : ℂ))
      (Ioi 0) volume := by
  let χ := qPart c hc
  have hχ_s : ContDiff ℝ ∞ χ := qPart_contDiff hc
  have hχ_c : HasCompactSupport χ := qPart_hasCompactSupport hc
  let χSum : ℝ → ℝ := fun q => ∑ k ∈ Finset.Icc (-1 : ℤ) 1, χ (q - (k : ℝ) * c)
  have hχSum_s : ContDiff ℝ ∞ χSum :=
    ContDiff.sum fun k _ => hχ_s.comp (contDiff_id.sub contDiff_const)
  have hχSum_c : HasCompactSupport χSum := by
    have h_eq : χSum = ∑ k ∈ Finset.Icc (-1 : ℤ) 1, fun q : ℝ => χ (q - (k : ℝ) * c) := by
      ext q; simp [χSum]
    rw [h_eq]
    exact HasCompactSupport.finset_sum fun k _ =>
      hχ_c.comp_homeomorph (Homeomorph.subRight ((k : ℝ) * c))
  have hχSum_one : ∀ q ∈ Ioo (-c) c, χSum q = 1 := by
    intro q hq
    have h := qPart_sum_eq_one hc hq
    have he : ∑ k ∈ Finset.Icc (-1 : ℤ) 1, χ (q - (k : ℝ) * c) =
        ∑ k ∈ Finset.Icc (-1 : ℤ) 1, χ (q + (k : ℝ) * c) := by
      refine Finset.sum_bij (fun k _ => -k) ?_ ?_ ?_ ?_
      · intro k hk; rw [Finset.mem_Icc] at hk ⊢; omega
      · intro k₁ _ k₂ _ h; omega
      · intro k hk; refine ⟨-k, ?_, by simp⟩; rw [Finset.mem_Icc] at hk ⊢; omega
      · intro k _; simp [sub_eq_add_neg]
    dsimp [χSum]
    rw [he]; exact h
  intro s₀ hs₀
  let r := min (s₀ / 2) 1
  have hr : 0 < r := lt_min (half_pos hs₀) one_pos
  let θb : ContDiffBump s₀ := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  have hθ_supp : tsupport θb ⊆ Ioi 0 := by
    intro s hs
    have hs' : s ∈ Metric.closedBall s₀ r :=
      closure_minimal (by rw [θb.support_eq]; exact Metric.ball_subset_closedBall)
        Metric.isClosed_closedBall hs
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hs'
    have hr1 : r ≤ s₀ / 2 := min_le_left _ _
    change 0 < s
    linarith
  let Φ := cylCoordTest θb χSum ψ
  have hΦ : IsCoordTest Φ :=
    isCoordTest_cylCoordTest θb.contDiff θb.hasCompactSupport hθ_supp hχSum_s hχSum_c hψ
  have hwG := (hw i).1 Φ hΦ |>.2
  have hwU := (hw i).1 Φ hΦ |>.1
  have hΦ_cell : ∀ x ∈ univ ×ˢ B0579.cell c, Φ x = θb x.1 * ψ x.2 := by
    intro x hx
    have hq : x.2.1 ∈ Ioo (-c) c := by
      have hx1 := hx.2.1
      rw [mem_Ico] at hx1
      exact ⟨by linarith, by linarith⟩
    simp [Φ, cylCoordTest, hχSum_one x.2.1 hq]
  have hΦ_tr : ∀ x ∈ univ ×ˢ B0579.cell c,
      coordTranspose (![vQ0, vEta] j) dZero Φ x = -(θb x.1 * B0579.pd j ψ x.2) := by
    intro x hx
    have hq : x.2.1 ∈ Ioo (-c) c := by
      have hx1 := hx.2.1
      rw [mem_Ico] at hx1
      exact ⟨by linarith, by linarith⟩
    have hev : Φ =ᶠ[𝓝 x] cylCoordTest θb (fun _ => 1) ψ := by
      have hU : (univ : Set ℝ) ×ˢ (Ioo (-c) c ×ˢ (univ : Set ℝ)) ∈ 𝓝 x :=
        (isOpen_univ.prod (isOpen_Ioo.prod isOpen_univ)).mem_nhds ⟨trivial, hq, trivial⟩
      filter_upwards [hU] with y hy
      simp [Φ, cylCoordTest, hχSum_one y.2.1 hy.2.1]
    have h_eq_tr : coordTranspose (![vQ0, vEta] j) dZero Φ x =
        coordTranspose (![vQ0, vEta] j) dZero (cylCoordTest θb (fun _ => 1) ψ) x := by
      simp only [coordTranspose, dZero, zero_mul, add_zero]
      congr 1; congr 1; funext m
      have hev_m : (fun y => (![vQ0, vEta] j) y m * Φ y) =ᶠ[𝓝 x]
          fun y => (![vQ0, vEta] j) y m * cylCoordTest θb (fun _ => 1) ψ y :=
        hev.mono fun y (hy : Φ y = cylCoordTest θb (fun _ => 1) ψ y) =>
          congrArg ((![vQ0, vEta] j) y m * ·) hy
      simp only [cpd, hev_m.fderiv_eq]
    rw [h_eq_tr]
    fin_cases j <;> dsimp
    · rw [coordTranspose_cylCoordTest_0 θb.contDiff contDiff_const hψ]
      simp [deriv_const]
    · rw [coordTranspose_cylCoordTest_1 θb.contDiff contDiff_const hψ]
      simp
  have hG_intOn : IntegrableOn (fun x : Coord => G x i * ((θb x.1 * ψ x.2 : ℝ) : ℂ))
      (univ ×ˢ B0579.cell c) :=
    hwG.integrableOn.congr_fun (fun x hx => by simp [hΦ_cell x hx])
      (MeasurableSet.univ.prod (B0579.measurableSet_cell c))
  have hU_intOn : IntegrableOn (fun x : Coord => U x i * ((θb x.1 * B0579.pd j ψ x.2 : ℝ) : ℂ))
      (univ ×ˢ B0579.cell c) :=
    hwU.integrableOn.neg.congr_fun
      (fun x hx => by
        change -(U x i * (coordTranspose (![vQ0, vEta] j) dZero Φ x : ℂ)) =
          U x i * ((θb x.1 * B0579.pd j ψ x.2 : ℝ) : ℂ)
        rw [hΦ_tr x hx]; push_cast; ring)
      (MeasurableSet.univ.prod (B0579.measurableSet_cell c))
  have h_sum_int : Integrable (fun x : ℝ × (ℝ × ℝ) =>
      (G x i * ((θb x.1 * ψ x.2 : ℝ) : ℂ) +
        U x i * ((θb x.1 * B0579.pd j ψ x.2 : ℝ) : ℂ)))
      (volume.prod (volume.restrict (B0579.cell c))) := by
    have h_meas_eq : (volume.prod (volume.restrict (B0579.cell c)) : Measure Coord) =
        volume.restrict (univ ×ˢ B0579.cell c) := by
      rw [← Measure.restrict_univ (μ := (volume : Measure ℝ)), Measure.prod_restrict,
        ← Measure.volume_eq_prod]
    rw [h_meas_eq]
    exact hG_intOn.add hU_intOn
  have hf_int_prod := h_sum_int.integral_prod_left
  refine ⟨Metric.closedBall s₀ (r / 2), nhdsWithin_le_nhds (Metric.closedBall_mem_nhds s₀ (half_pos hr)), ?_⟩
  have h_eq_on : ∀ s ∈ Metric.closedBall s₀ (r / 2),
      (∫ z in B0579.cell c, G (s, z) i * (ψ z : ℂ) + U (s, z) i * (B0579.pd j ψ z : ℂ)) =
        ∫ z in B0579.cell c,
          G (s, z) i * ((θb s * ψ z : ℝ) : ℂ) + U (s, z) i * ((θb s * B0579.pd j ψ z : ℝ) : ℂ) := by
    intro s hs
    have h1 : θb s = 1 := θb.one_of_mem_closedBall hs
    simp [h1]
  exact (hf_int_prod.integrableOn (s := Metric.closedBall s₀ (r / 2))).congr_fun
      (fun s hs => (h_eq_on s hs).symm) measurableSet_closedBall

private lemma ae_slice_of_fixed_test {c : ℝ} (hc : 0 < c) (j : Fin 2) (U G : CProf)
    (_hUm : StronglyMeasurable U) (_hGm : StronglyMeasurable G)
    (hUp : QPeriodic c U) (hGp : QPeriodic c G)
    (hw : HasWeakVec (![vQ0, vEta] j) dZero U G)
    (i : Fin 2) (ψ : ℝ × ℝ → ℝ) (hψ : B0579.IsCylTest c ψ) :
    ∀ᵐ s ∂volume, 0 < s →
      ∫ z in B0579.cell c, G (s, z) i * (ψ z : ℂ) + U (s, z) i * (B0579.pd j ψ z : ℂ) = 0 := by
  let χ := qPart c hc
  have hχ_s : ContDiff ℝ ∞ χ := qPart_contDiff hc
  have hχ_c : HasCompactSupport χ := qPart_hasCompactSupport hc
  let f : ℝ → ℂ := fun s =>
    ∫ z in B0579.cell c, G (s, z) i * (ψ z : ℂ) + U (s, z) i * (B0579.pd j ψ z : ℂ)
  have hf_loc : LocallyIntegrableOn f (Ioi 0) volume :=
    locallyIntegrableOn_slice hc j U G hw i ψ hψ
  refine isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero hf_loc ?_
  intro θ hθ_s hθ_c hθ_i
  let φ := cylCoordTest θ χ ψ
  have hφ : IsCoordTest φ := isCoordTest_cylCoordTest hθ_s hθ_c hθ_i hχ_s hχ_c hψ
  have hwG := (hw i).1 φ hφ |>.2
  have hwU := (hw i).1 φ hφ |>.1
  have hwEq := (hw i).2 φ hφ
  let H : Coord → ℂ := fun x =>
    G x i * (φ x : ℂ) - U x i * (coordTranspose (![vQ0, vEta] j) dZero φ x : ℂ)
  have hH_int : Integrable H := hwG.sub hwU
  have hH_zero : ∫ x : Coord, H x = 0 := by
    rw [integral_sub hwG hwU, hwEq, sub_self]
  rw [← hH_zero]
  change _ = ∫ x : ℝ × (ℝ × ℝ), H x ∂(volume.prod volume)
  rw [integral_prod H hH_int]
  have h_ae_int : ∀ᵐ s ∂volume, Integrable (fun z : ℝ × ℝ => H (s, z)) :=
    hH_int.prod_right_ae
  have hUp_all : ∀ k ∈ Finset.Icc (-1 : ℤ) 1,
      ∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}),
        U (x.1, (x.2.1 + (k : ℝ) * c, x.2.2)) = U x :=
    fun k _ => qPeriodic_shift_k hUp k
  have hGp_all : ∀ k ∈ Finset.Icc (-1 : ℤ) 1,
      ∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}),
        G (x.1, (x.2.1 + (k : ℝ) * c, x.2.2)) = G x :=
    fun k _ => qPeriodic_shift_k hGp k
  have hUp_s : ∀ᵐ s ∂volume, ∀ᵐ z ∂volume, 0 < s → ∀ k ∈ Finset.Icc (-1 : ℤ) 1,
      U (s, (z.1 + (k : ℝ) * c, z.2)) = U (s, z) := by
    have h_all : ∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}),
        ∀ k ∈ Finset.Icc (-1 : ℤ) 1, U (x.1, (x.2.1 + (k : ℝ) * c, x.2.2)) = U x :=
      (ae_ball_iff (Finset.countable_toSet _)).2 hUp_all
    have h_all' : ∀ᵐ x : ℝ × (ℝ × ℝ) ∂(volume.prod volume),
        0 < x.1 → ∀ k ∈ Finset.Icc (-1 : ℤ) 1, U (x.1, (x.2.1 + (k : ℝ) * c, x.2.2)) = U x :=
      (ae_restrict_iff' (measurableSet_lt measurable_const measurable_fst)).1 h_all
    exact Measure.ae_ae_of_ae_prod h_all'
  have hGp_s : ∀ᵐ s ∂volume, ∀ᵐ z ∂volume, 0 < s → ∀ k ∈ Finset.Icc (-1 : ℤ) 1,
      G (s, (z.1 + (k : ℝ) * c, z.2)) = G (s, z) := by
    have h_all : ∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}),
        ∀ k ∈ Finset.Icc (-1 : ℤ) 1, G (x.1, (x.2.1 + (k : ℝ) * c, x.2.2)) = G x :=
      (ae_ball_iff (Finset.countable_toSet _)).2 hGp_all
    have h_all' : ∀ᵐ x : ℝ × (ℝ × ℝ) ∂(volume.prod volume),
        0 < x.1 → ∀ k ∈ Finset.Icc (-1 : ℤ) 1, G (x.1, (x.2.1 + (k : ℝ) * c, x.2.2)) = G x :=
      (ae_restrict_iff' (measurableSet_lt measurable_const measurable_fst)).1 h_all
    exact Measure.ae_ae_of_ae_prod h_all'
  refine integral_congr_ae ?_
  filter_upwards [h_ae_int, hUp_s, hGp_s] with s hs_int hsU hsG
  by_cases hs : 0 < s
  · have hsU' : ∀ k ∈ Finset.Icc (-1 : ℤ) 1,
        ∀ᵐ z ∂volume, U (s, (z.1 + (k : ℝ) * c, z.2)) = U (s, z) :=
      fun k hk => hsU.mono fun z hz => hz hs k hk
    have hsG' : ∀ k ∈ Finset.Icc (-1 : ℤ) 1,
        ∀ᵐ z ∂volume, G (s, (z.1 + (k : ℝ) * c, z.2)) = G (s, z) :=
      fun k hk => hsG.mono fun z hz => hz hs k hk
    have h_supp : ∀ z : ℝ × ℝ, c ≤ |z.1| → H (s, z) = 0 := by
      intro z hz
      have hχ0 : χ z.1 = 0 := qPart_eq_zero_of_abs_ge hc hz
      have hdχ0 : deriv χ z.1 = 0 := by
        have hopen : IsOpen {q : ℝ | c < |q|} := isOpen_lt continuous_const continuous_abs
        by_cases hgt : c < |z.1|
        · have hev : χ =ᶠ[𝓝 z.1] fun _ => 0 :=
            Filter.eventually_of_mem (hopen.mem_nhds hgt) fun q hq =>
              qPart_eq_zero_of_abs_ge hc hq.le
          rw [hev.deriv_eq, deriv_const]
        · have h_cont : Continuous (deriv χ) := (hχ_s.continuous_deriv (by simp))
          have h_zero_out : ∀ q : ℝ, c < |q| → deriv χ q = 0 := fun q hq => by
            have hev : χ =ᶠ[𝓝 q] fun _ => 0 :=
              Filter.eventually_of_mem (hopen.mem_nhds hq) fun t ht =>
                qPart_eq_zero_of_abs_ge hc ht.le
            rw [hev.deriv_eq, deriv_const]
          have h_eq_abs : |z.1| = c := le_antisymm (not_lt.1 hgt) hz
          rcases abs_eq hc.le |>.1 h_eq_abs with hzc | hzc
          · have hlim : Tendsto (fun n : ℕ => z.1 + ((n : ℝ) + 1)⁻¹) atTop (𝓝 z.1) := by
              simpa [one_div] using (tendsto_const_nhds (x := z.1)).add tendsto_one_div_add_atTop_nhds_zero_nat
            have hval : (fun n : ℕ => deriv χ (z.1 + ((n : ℝ) + 1)⁻¹)) = fun _ => 0 := by
              funext n
              apply h_zero_out
              rw [hzc, abs_of_pos (by positivity)]
              linarith [show (0 : ℝ) < ((n : ℝ) + 1)⁻¹ by positivity]
            exact tendsto_nhds_unique (h_cont.continuousAt.tendsto.comp hlim)
              (by rw [show (deriv χ ∘ fun n : ℕ => z.1 + ((n : ℝ) + 1)⁻¹) = fun _ => 0 from hval]; exact tendsto_const_nhds)
          · have hlim : Tendsto (fun n : ℕ => z.1 - ((n : ℝ) + 1)⁻¹) atTop (𝓝 z.1) := by
              simpa [one_div] using (tendsto_const_nhds (x := z.1)).sub tendsto_one_div_add_atTop_nhds_zero_nat
            have hval : (fun n : ℕ => deriv χ (z.1 - ((n : ℝ) + 1)⁻¹)) = fun _ => 0 := by
              funext n
              apply h_zero_out
              rw [hzc, abs_of_neg (by linarith [show (0 : ℝ) < ((n : ℝ) + 1)⁻¹ by positivity])]
              linarith [show (0 : ℝ) < ((n : ℝ) + 1)⁻¹ by positivity]
            exact tendsto_nhds_unique (h_cont.continuousAt.tendsto.comp hlim)
              (by rw [show (deriv χ ∘ fun n : ℕ => z.1 - ((n : ℝ) + 1)⁻¹) = fun _ => 0 from hval]; exact tendsto_const_nhds)
      fin_cases j
      · simp [H, φ, cylCoordTest, coordTranspose_cylCoordTest_0 hθ_s hχ_s hψ, hχ0, hdχ0]
      · simp [H, φ, cylCoordTest, coordTranspose_cylCoordTest_1 hθ_s hχ_s hψ, hχ0]
    rw [integral_plane_unfold hc h_supp hs_int]
    have h_k_eq : ∀ k ∈ Finset.Icc (-1 : ℤ) 1,
        ∫ z in B0579.cell c, H (s, (z.1 + (k : ℝ) * c, z.2)) =
          ∫ z in B0579.cell c,
            (θ s : ℂ) * ((χ (z.1 + (k : ℝ) * c) : ℂ) *
              (G (s, z) i * (ψ z : ℂ) + U (s, z) i * (B0579.pd j ψ z : ℂ)) +
              (if j = 0 then Complex.ofReal (deriv χ (z.1 + (k : ℝ) * c)) * (U (s, z) i * (ψ z : ℂ)) else 0)) := by
      intro k hk
      refine setIntegral_congr_ae (B0579.measurableSet_cell c) ?_
      filter_upwards [hsU' k hk, hsG' k hk] with z hzU hzG _
      have hψk : ψ (z.1 + (k : ℝ) * c, z.2) = ψ z := B0579_periodic_k hψ k z
      have hpd_k : B0579.pd j ψ (z.1 + (k : ℝ) * c, z.2) = B0579.pd j ψ z :=
        B0579_periodic_k (hψ.pd j) k z
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · simp only [H, φ]
        rw [show (![vQ0, vEta] 0) = vQ0 from rfl, coordTranspose_cylCoordTest_0 hθ_s hχ_s hψ]
        simp only [cylCoordTest, hzU, hzG, hψk, hpd_k, ↓reduceIte, Complex.ofReal_mul,
          Complex.ofReal_add, Complex.ofReal_neg]
        ring
      · simp only [H, φ]
        rw [show (![vQ0, vEta] 1) = vEta from rfl, coordTranspose_cylCoordTest_1 hθ_s hχ_s hψ]
        simp only [cylCoordTest, hzU, hzG, hψk, hpd_k, Fin.reduceEq, ↓reduceIte, add_zero,
          Complex.ofReal_mul, Complex.ofReal_neg]
        ring
    rw [Finset.sum_congr rfl h_k_eq]
    have h_int_k : ∀ k ∈ Finset.Icc (-1 : ℤ) 1,
        IntegrableOn (fun z : ℝ × ℝ =>
          (θ s : ℂ) * ((χ (z.1 + (k : ℝ) * c) : ℂ) *
            (G (s, z) i * (ψ z : ℂ) + U (s, z) i * (B0579.pd j ψ z : ℂ)) +
            (if j = 0 then Complex.ofReal (deriv χ (z.1 + (k : ℝ) * c)) * (U (s, z) i * (ψ z : ℂ)) else 0)))
          (B0579.cell c) := by
      intro k hk
      have h_int_shift : IntegrableOn (fun z : ℝ × ℝ => H (s, (z.1 + (k : ℝ) * c, z.2)))
          (B0579.cell c) := by
        simpa [Prod.add_def] using (hs_int.comp_add_right ((k : ℝ) * c, 0)).integrableOn
      refine h_int_shift.congr ?_
      have hUk : ∀ᵐ z ∂(volume.restrict (B0579.cell c)),
          U (s, (z.1 + (k : ℝ) * c, z.2)) = U (s, z) := ae_restrict_of_ae (hsU' k hk)
      have hGk : ∀ᵐ z ∂(volume.restrict (B0579.cell c)),
          G (s, (z.1 + (k : ℝ) * c, z.2)) = G (s, z) := ae_restrict_of_ae (hsG' k hk)
      filter_upwards [hUk, hGk] with z hzU hzG
      have hψk : ψ (z.1 + (k : ℝ) * c, z.2) = ψ z := B0579_periodic_k hψ k z
      have hpd_k : B0579.pd j ψ (z.1 + (k : ℝ) * c, z.2) = B0579.pd j ψ z :=
        B0579_periodic_k (hψ.pd j) k z
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · simp only [H, φ]
        rw [show (![vQ0, vEta] 0) = vQ0 from rfl, coordTranspose_cylCoordTest_0 hθ_s hχ_s hψ]
        simp only [cylCoordTest, hzU, hzG, hψk, hpd_k, ↓reduceIte, Complex.ofReal_mul,
          Complex.ofReal_add, Complex.ofReal_neg]
        ring
      · simp only [H, φ]
        rw [show (![vQ0, vEta] 1) = vEta from rfl, coordTranspose_cylCoordTest_1 hθ_s hχ_s hψ]
        simp only [cylCoordTest, hzU, hzG, hψk, hpd_k, Fin.reduceEq, ↓reduceIte, add_zero,
          Complex.ofReal_mul, Complex.ofReal_neg]
        ring
    rw [← integral_finsetSum _ h_int_k]
    have h_sum_z : ∀ z ∈ B0579.cell c,
        (∑ k ∈ Finset.Icc (-1 : ℤ) 1,
          (θ s : ℂ) * ((χ (z.1 + (k : ℝ) * c) : ℂ) *
            (G (s, z) i * (ψ z : ℂ) + U (s, z) i * (B0579.pd j ψ z : ℂ)) +
            (if j = 0 then Complex.ofReal (deriv χ (z.1 + (k : ℝ) * c)) * (U (s, z) i * (ψ z : ℂ)) else 0))) =
          θ s • (G (s, z) i * (ψ z : ℂ) + U (s, z) i * (B0579.pd j ψ z : ℂ)) := by
      intro z hz
      have hzq : z.1 ∈ Ioo (-c) c := by
        have hz1 := hz.1
        rw [mem_Ico] at hz1
        exact ⟨by linarith, by linarith⟩
      have h1 : (∑ k ∈ Finset.Icc (-1 : ℤ) 1, (χ (z.1 + (k : ℝ) * c) : ℂ)) = 1 := by
        exact_mod_cast qPart_sum_eq_one hc hzq
      have h2 : (∑ k ∈ Finset.Icc (-1 : ℤ) 1, Complex.ofReal (deriv χ (z.1 + (k : ℝ) * c))) = 0 := by
        exact_mod_cast deriv_qPart_sum_eq_zero hc hzq
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul, h1, one_mul]
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · simp only [↓reduceIte]
        rw [← Finset.sum_mul, h2, zero_mul, add_zero, Complex.real_smul]
      · simp only [Fin.reduceEq, ↓reduceIte, Finset.sum_const_zero, add_zero, Complex.real_smul]
    rw [setIntegral_congr_fun (B0579.measurableSet_cell c) h_sum_z, integral_smul]
  · have hθ0 : θ s = 0 := by
      by_contra hne
      exact hs (hθ_i (subset_tsupport θ hne))
    have hH0 : ∀ z : ℝ × ℝ, H (s, z) = 0 := by
      intro z
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · simp [H, φ, cylCoordTest, coordTranspose_cylCoordTest_0 hθ_s hχ_s hψ, hθ0]
      · simp [H, φ, cylCoordTest, coordTranspose_cylCoordTest_1 hθ_s hχ_s hψ, hθ0]
    simp [hθ0, hH0]

private lemma isCylTest_memLp {c : ℝ} {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest c ψ) :
    MemLp ψ 2 (volume.restrict (B0579.cell c)) := by
  obtain ⟨R, hR⟩ := hψ.vanish
  exact B0579.memLp_cell_of_continuous hψ.continuous (B0579.isCompact_box c R) hR

private lemma memLp_coord_comp {c : ℝ} {f : ℝ × ℝ → CMerid}
    (hf : MemLp f 2 (volume.restrict (B0579.cell c))) (i : Fin 2) :
    MemLp (fun z => f z i) 2 (volume.restrict (B0579.cell c)) :=
  hf.mono (Continuous.comp_aestronglyMeasurable (PiLp.continuous_apply 2 _ i) hf.aestronglyMeasurable)
    (Eventually.of_forall fun z => PiLp.norm_apply_le (f z) i)

private lemma memLp_ofReal {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {g : α → ℝ} (hg : MemLp g 2 μ) : MemLp (fun x => (g x : ℂ)) 2 μ :=
  hg.mono (Complex.continuous_ofReal.comp_aestronglyMeasurable hg.aestronglyMeasurable)
    (Eventually.of_forall fun _ => by simp)

private lemma norm_integral_mul_ofReal_le_L2 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℂ} {g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖∫ x, f x * (g x : ℂ) ∂μ‖ ≤ ‖hf.toLp f‖ * ‖hg.toLp g‖ := by
  have hf' : MemLp (fun x => star (f x)) 2 μ :=
    hf.mono (continuous_star.comp_aestronglyMeasurable hf.aestronglyMeasurable)
      (Eventually.of_forall fun _ => by simp)
  have hg' : MemLp (fun x => (g x : ℂ)) 2 μ := memLp_ofReal hg
  have h_eq : ∫ x, f x * (g x : ℂ) ∂μ = inner ℂ (hf'.toLp _) (hg'.toLp _) := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hf'.coeFn_toLp, hg'.coeFn_toLp] with x hfx hgx
    rw [hfx, hgx]
    simp [RCLike.inner_apply, mul_comm]
  have h1 : ‖inner ℂ (hf'.toLp _) (hg'.toLp _)‖ ≤ ‖hf'.toLp _‖ * ‖hg'.toLp _‖ :=
    norm_inner_le_norm _ _
  have hnf : ‖hf'.toLp _‖ ≤ ‖hf.toLp f‖ := by
    rw [Lp.norm_toLp, Lp.norm_toLp]
    refine ENNReal.toReal_mono hf.eLpNorm_lt_top.ne ?_
    exact eLpNorm_mono_ae (Eventually.of_forall fun _ => by simp)
  have hng : ‖hg'.toLp _‖ ≤ ‖hg.toLp g‖ := by
    rw [Lp.norm_toLp, Lp.norm_toLp]
    refine ENNReal.toReal_mono hg.eLpNorm_lt_top.ne ?_
    exact eLpNorm_mono_ae (Eventually.of_forall fun _ => by simp)
  rw [h_eq]
  exact h1.trans (mul_le_mul hnf hng (norm_nonneg _) (norm_nonneg _))

protected theorem proof :
    UnforcedLeray.Short.IIb.FlatBvSliceGoodAeNeeded.JointWeakToSlice := by
  intro c hc j U G hUm hGm hUp hGp hw
  let μ := volume.restrict (B0579.cell c)
  have : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  have : TopologicalSpace.SeparableSpace (Lp ℝ 2 μ) := inferInstance
  let T := {ψ : ℝ × ℝ → ℝ // B0579.IsCylTest c ψ}
  let Φ : T → Lp ℝ 2 μ × Lp ℝ 2 μ := fun ψ =>
    ((isCylTest_memLp ψ.2).toLp ψ.1, (isCylTest_memLp (ψ.2.pd j)).toLp (B0579.pd j ψ.1))
  have hsep : TopologicalSpace.IsSeparable (Set.range Φ) :=
    TopologicalSpace.IsSeparable.mono
      (TopologicalSpace.isSeparable_univ_iff.2 inferInstance) (Set.subset_univ _)
  obtain ⟨t, hts, htc, hst⟩ := hsep.exists_countable_dense_subset
  have hpre : ∀ y ∈ t, ∃ ψ : T, Φ ψ = y := fun y hy => hts hy
  choose ψ_of hψ_of using hpre
  let D : Set T := Set.range (fun y : t => ψ_of y.1 y.2)
  have hD_count : D.Countable := by
    have : Countable t := htc.to_subtype
    exact Set.countable_range _
  have hD_dense : Set.range Φ ⊆ closure (Φ '' D) := by
    refine hst.trans (closure_mono ?_)
    intro y hy
    refine ⟨ψ_of y hy, ⟨⟨y, hy⟩, rfl⟩, hψ_of y hy⟩
  have h_ae_D : ∀ ψ' ∈ D, ∀ i : Fin 2, ∀ᵐ s ∂volume, 0 < s →
      ∫ z in B0579.cell c, G (s, z) i * (ψ'.1 z : ℂ) + U (s, z) i * (B0579.pd j ψ'.1 z : ℂ) = 0 :=
    fun ψ' _ i => ae_slice_of_fixed_test hc j U G hUm hGm hUp hGp hw i ψ'.1 ψ'.2
  have h_ae_all : ∀ᵐ s ∂volume, ∀ ψ' ∈ D, ∀ i : Fin 2, 0 < s →
      ∫ z in B0579.cell c, G (s, z) i * (ψ'.1 z : ℂ) + U (s, z) i * (B0579.pd j ψ'.1 z : ℂ) = 0 := by
    rw [ae_ball_iff hD_count]
    intro ψ' hψ'
    rw [ae_all_iff]
    exact h_ae_D ψ' hψ'
  filter_upwards [h_ae_all] with s hs_D hs_pos hU_mem hG_mem i
  have hU_i : MemLp (fun z => U (s, z) i) 2 μ := memLp_coord_comp hU_mem i
  have hG_i : MemLp (fun z => G (s, z) i) 2 μ := memLp_coord_comp hG_mem i
  refine ⟨fun ψ hψ => ⟨?_, ?_⟩, fun ψ hψ => ?_⟩
  · exact hU_i.integrable_mul (memLp_ofReal (isCylTest_memLp (hψ.pd j)))
  · exact hG_i.integrable_mul (memLp_ofReal (isCylTest_memLp hψ))
  · have h_sum_zero :
        ∫ z in B0579.cell c, G (s, z) i * (ψ z : ℂ) + U (s, z) i * (B0579.pd j ψ z : ℂ) = 0 := by
      have h_mem_cl : Φ ⟨ψ, hψ⟩ ∈ closure (Φ '' D) :=
        hD_dense (mem_range_self _)
      have h_norm_zero :
          ‖∫ z in B0579.cell c, G (s, z) i * (ψ z : ℂ) + U (s, z) i * (B0579.pd j ψ z : ℂ)‖ = 0 := by
        refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) (norm_nonneg _)
        rw [zero_add]
        let C : ℝ := ‖hG_i.toLp _‖ + ‖hU_i.toLp _‖ + 1
        have hC_pos : 0 < C := by positivity
        obtain ⟨y, ⟨ψ', hψ'D, rfl⟩, hy⟩ :=
          Metric.mem_closure_iff.1 h_mem_cl (ε / C) (div_pos hε hC_pos)
        rw [Prod.dist_eq, dist_eq_norm, dist_eq_norm] at hy
        have h_dist_1 : ‖(isCylTest_memLp hψ).toLp ψ - (isCylTest_memLp ψ'.2).toLp ψ'.1‖ < ε / C :=
          (le_max_left _ _).trans_lt hy
        have h_dist_2 : ‖(isCylTest_memLp (hψ.pd j)).toLp (B0579.pd j ψ) -
            (isCylTest_memLp (ψ'.2.pd j)).toLp (B0579.pd j ψ'.1)‖ < ε / C :=
          (le_max_right _ _).trans_lt hy
        have hD_zero := hs_D ψ' hψ'D i hs_pos
        have h_int1 : IntegrableOn (fun z => G (s, z) i * (ψ z : ℂ) + U (s, z) i * (B0579.pd j ψ z : ℂ))
            (B0579.cell c) :=
          (hG_i.integrable_mul (memLp_ofReal (isCylTest_memLp hψ))).add
            (hU_i.integrable_mul (memLp_ofReal (isCylTest_memLp (hψ.pd j))))
        have h_int2 : IntegrableOn (fun z => G (s, z) i * (ψ'.1 z : ℂ) + U (s, z) i * (B0579.pd j ψ'.1 z : ℂ))
            (B0579.cell c) :=
          (hG_i.integrable_mul (memLp_ofReal (isCylTest_memLp ψ'.2))).add
            (hU_i.integrable_mul (memLp_ofReal (isCylTest_memLp (ψ'.2.pd j))))
        have h_diff_eq :
            (∫ z in B0579.cell c, G (s, z) i * (ψ z : ℂ) + U (s, z) i * (B0579.pd j ψ z : ℂ)) =
              (∫ z in B0579.cell c, G (s, z) i * ((ψ z - ψ'.1 z : ℝ) : ℂ)) +
                (∫ z in B0579.cell c, U (s, z) i * ((B0579.pd j ψ z - B0579.pd j ψ'.1 z : ℝ) : ℂ)) := by
          have h1 := integral_sub h_int1 h_int2
          rw [hD_zero, sub_zero] at h1
          rw [← h1]
          have hG_diff : Integrable (fun z => G (s, z) i * ((ψ z - ψ'.1 z : ℝ) : ℂ)) μ :=
            hG_i.integrable_mul (memLp_ofReal ((isCylTest_memLp hψ).sub (isCylTest_memLp ψ'.2)))
          have hU_diff : Integrable (fun z => U (s, z) i * ((B0579.pd j ψ z - B0579.pd j ψ'.1 z : ℝ) : ℂ)) μ :=
            hU_i.integrable_mul (memLp_ofReal
              ((isCylTest_memLp (hψ.pd j)).sub (isCylTest_memLp (ψ'.2.pd j))))
          rw [← integral_add hG_diff hU_diff]
          refine integral_congr_ae (Eventually.of_forall fun z => ?_)
          push_cast
          ring
        rw [h_diff_eq]
        have h_cs1 : ‖∫ z in B0579.cell c, G (s, z) i * ((ψ z - ψ'.1 z : ℝ) : ℂ)‖ ≤
            ‖hG_i.toLp _‖ *
              ‖(isCylTest_memLp hψ).toLp ψ - (isCylTest_memLp ψ'.2).toLp ψ'.1‖ := by
          have h_sub := norm_integral_mul_ofReal_le_L2 hG_i ((isCylTest_memLp hψ).sub (isCylTest_memLp ψ'.2))
          rw [← MemLp.toLp_sub]
          exact h_sub
        have h_cs2 : ‖∫ z in B0579.cell c, U (s, z) i * ((B0579.pd j ψ z - B0579.pd j ψ'.1 z : ℝ) : ℂ)‖ ≤
            ‖hU_i.toLp _‖ *
              ‖(isCylTest_memLp (hψ.pd j)).toLp (B0579.pd j ψ) -
                (isCylTest_memLp (ψ'.2.pd j)).toLp (B0579.pd j ψ'.1)‖ := by
          have h_sub := norm_integral_mul_ofReal_le_L2 hU_i
            ((isCylTest_memLp (hψ.pd j)).sub (isCylTest_memLp (ψ'.2.pd j)))
          rw [← MemLp.toLp_sub]
          exact h_sub
        calc ‖(∫ z in B0579.cell c, G (s, z) i * ((ψ z - ψ'.1 z : ℝ) : ℂ)) +
                (∫ z in B0579.cell c, U (s, z) i * ((B0579.pd j ψ z - B0579.pd j ψ'.1 z : ℝ) : ℂ))‖
            ≤ ‖∫ z in B0579.cell c, G (s, z) i * ((ψ z - ψ'.1 z : ℝ) : ℂ)‖ +
                ‖∫ z in B0579.cell c, U (s, z) i * ((B0579.pd j ψ z - B0579.pd j ψ'.1 z : ℝ) : ℂ)‖ :=
              norm_add_le _ _
          _ ≤ ‖hG_i.toLp _‖ * ‖(isCylTest_memLp hψ).toLp ψ - (isCylTest_memLp ψ'.2).toLp ψ'.1‖ +
                ‖hU_i.toLp _‖ * ‖(isCylTest_memLp (hψ.pd j)).toLp (B0579.pd j ψ) -
                  (isCylTest_memLp (ψ'.2.pd j)).toLp (B0579.pd j ψ'.1)‖ :=
              add_le_add h_cs1 h_cs2
          _ ≤ ‖hG_i.toLp _‖ * (ε / C) + ‖hU_i.toLp _‖ * (ε / C) := by
              gcongr
          _ ≤ C * (ε / C) := by
              rw [← add_mul]
              gcongr
              linarith
          _ = ε := mul_div_cancel₀ ε hC_pos.ne'
      exact norm_eq_zero.1 h_norm_zero
    have h_int_G : IntegrableOn (fun z => G (s, z) i * (ψ z : ℂ)) (B0579.cell c) :=
      hG_i.integrable_mul (memLp_ofReal (isCylTest_memLp hψ))
    have h_int_U : IntegrableOn (fun z => U (s, z) i * (B0579.pd j ψ z : ℂ)) (B0579.cell c) :=
      hU_i.integrable_mul (memLp_ofReal (isCylTest_memLp (hψ.pd j)))
    rw [integral_add h_int_G h_int_U] at h_sum_zero
    exact eq_neg_of_add_eq_zero_right h_sum_zero

end UnforcedLeray.Short.IIb.FlatBvSliceGoodAeJointWeak

namespace UnforcedLeray.Short.IIb.FlatBvSliceGoodAeNeeded

/-- **Main theorem** (`PartII-b:F5/2/2/2/1`): Fubini disintegration of a joint weak derivative
into cylinder weak derivatives on a.e. slice `s > 0`. -/
theorem jointWeakToSlice_proof :
    UnforcedLeray.Short.IIb.FlatBvSliceGoodAeNeeded.JointWeakToSlice :=
  UnforcedLeray.Short.IIb.FlatBvSliceGoodAeJointWeak.proof

end UnforcedLeray.Short.IIb.FlatBvSliceGoodAeNeeded
