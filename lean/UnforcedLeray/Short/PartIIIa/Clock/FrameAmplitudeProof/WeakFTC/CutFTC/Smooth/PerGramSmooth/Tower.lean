import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.WeakFTC.CutFTC.Smooth.PhysFrameLam0Smooth.Periodic

/-!
# Smoothness of the Gram entries by a derivative tower (helper for `PartIII-a:T21/c5/1/1/2/1`)

Source `the November 2 reference manuscript`
lines 593-610 and 2891-2905.  The Gram entry is `G(d) = Σ_k T(kd)` with the cross integral
`T(s) = ∫ λ_i(z₁ - s, z₂) e_j(z) dz` (`perGramUnfold`).  Differentiating under the integral,
`T_L' = -T_{∂₁L}`, so `G^{(m)}(d) = Σ_k (-k)^m T_{∂₁^m λ_i}(kd)`; the sharp decay
`|∂₁^m λ_i(z)| ≲ (1+|z|)^{-m-2}` (`LamJet.lean`) and the Gaussian tails of `e_j` give
`|k|^m |T_{∂₁^m λ_i}(kd)| ≲ (1+|k|)^{-2}` uniformly in `d > 1/2`, which is summable.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa.LamJetInf

open UnforcedLeray.Short.IIIa.SeedJet2Aux

/-- The directional derivative in the periodized direction `e₁`. -/
def d1 (L : ℝ × ℝ → ℂ) (z : ℝ × ℝ) : ℂ := fderiv ℝ L z ((1 : ℝ), (0 : ℝ))

theorem good_d1 {L : ℝ × ℝ → ℂ} (hL : Good L) : Good (d1 L) := hL.fderiv_apply _

theorem good_iterate_d1 {L : ℝ × ℝ → ℂ} (hL : Good L) (m : ℕ) : Good (d1^[m] L) := by
  induction m with
  | zero => simpa using hL
  | succ m ih => rw [Function.iterate_succ_apply']; exact good_d1 ih

theorem norm_iteratedFDeriv_iterate_d1_le {L : ℝ × ℝ → ℂ} (hL : Good L) (m : ℕ) :
    ∀ (j : ℕ) (z : ℝ × ℝ),
      ‖iteratedFDeriv ℝ j (d1^[m] L) z‖ ≤ ‖iteratedFDeriv ℝ (j + m) L z‖ := by
  induction m with
  | zero => intro j z; simp
  | succ m ih =>
    intro j z
    rw [Function.iterate_succ_apply']
    have hcd := (good_iterate_d1 hL m).contDiff_fderiv
    have h1 : ‖iteratedFDeriv ℝ j
        (fun y => fderiv ℝ (d1^[m] L) y ((1 : ℝ), (0 : ℝ))) z‖ ≤
        ‖((1 : ℝ), (0 : ℝ))‖ * ‖iteratedFDeriv ℝ j (fderiv ℝ (d1^[m] L)) z‖ :=
      norm_iteratedFDeriv_clm_apply_const (x := z) hcd.contDiffAt (le_top_nat j)
    rw [norm_iteratedFDeriv_fderiv] at h1
    have hn : ‖((1 : ℝ), (0 : ℝ))‖ = 1 := by simp [Prod.norm_def]
    rw [hn, one_mul] at h1
    calc ‖iteratedFDeriv ℝ j (d1 (d1^[m] L)) z‖ ≤ ‖iteratedFDeriv ℝ (j + 1) (d1^[m] L) z‖ := h1
      _ ≤ ‖iteratedFDeriv ℝ (j + 1 + m) L z‖ := ih (j + 1) z
      _ = ‖iteratedFDeriv ℝ (j + (m + 1)) L z‖ := by rw [show j + 1 + m = j + (m + 1) by omega]

/-- Sharp order-zero decay `|∂₁^m L(z)| (1+‖z‖)^{m+2} ≤ C`. -/
theorem good_iterate_d1_norm_le {L : ℝ × ℝ → ℂ} (hL : Good L) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖(d1^[m] L) z‖ * (1 + ‖z‖) ^ (m + 2) ≤ C := by
  obtain ⟨C, hC0, hC⟩ := hL.2 m
  refine ⟨C, hC0, fun z => ?_⟩
  have h := norm_iteratedFDeriv_iterate_d1_le hL m 0 z
  rw [norm_iteratedFDeriv_zero, zero_add] at h
  calc ‖(d1^[m] L) z‖ * (1 + ‖z‖) ^ (m + 2)
      ≤ ‖iteratedFDeriv ℝ m L z‖ * (1 + ‖z‖) ^ (m + 2) := by gcongr
    _ ≤ C := hC z

/-- The cross integral `T_L(s) = ∫ L(z₁ - s, z₂) e(z) dz`. -/
def crossT (e L : ℝ × ℝ → ℂ) (s : ℝ) : ℂ := ∫ z : ℝ × ℝ, L (z.1 - s, z.2) * e z

theorem norm_le_of_weighted {L : ℝ × ℝ → ℂ} {C : ℝ} {p : ℕ}
    (hC : ∀ z, ‖L z‖ * (1 + ‖z‖) ^ p ≤ C) (z : ℝ × ℝ) : ‖L z‖ ≤ C :=
  le_trans (le_mul_of_one_le_right (norm_nonneg _)
    (one_le_pow₀ (by linarith [norm_nonneg z]))) (hC z)

/-- Differentiation of the cross integral under the integral sign: `T_L' = -T_{∂₁L}`. -/
theorem hasDerivAt_crossT {e : ℝ × ℝ → ℂ} (he : Continuous e) {Ce : ℝ}
    (hCe : ∀ z : ℝ × ℝ, ‖e z‖ ≤ Ce * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8))
    {L : ℝ × ℝ → ℂ} (hL : Good L) (s : ℝ) :
    HasDerivAt (crossT e L) (-(crossT e (d1 L) s)) s := by
  obtain ⟨C0, hC00, hC0⟩ := hL.norm_le
  obtain ⟨C1, hC10, hC1⟩ := (good_d1 hL).norm_le
  set F : ℝ → ℝ × ℝ → ℂ := fun d z => L (z.1 - d, z.2) * e z with hF
  set F' : ℝ → ℝ × ℝ → ℂ := fun d z => -(d1 L (z.1 - d, z.2) * e z) with hF'
  have hG8 := Gaussian.integrable_gauss_plane (a := 2) (by norm_num)
  have he8 : ∀ z : ℝ × ℝ, ‖e z‖ ≤ Ce * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * 2)) := fun z => by
    have := hCe z
    rwa [show (4 : ℝ) * 2 = 8 by norm_num]
  have hcontL : Continuous L := hL.1.continuous
  have hcontD : Continuous (d1 L) := (good_d1 hL).1.continuous
  have hin_cont : ∀ d : ℝ, Continuous (fun z : ℝ × ℝ => ((z.1 - d, z.2) : ℝ × ℝ)) := fun d =>
    (continuous_fst.sub continuous_const).prodMk continuous_snd
  have hF_cont : ∀ d, Continuous (F d) := fun d => (hcontL.comp (hin_cont d)).mul he
  have hF'_cont : ∀ d, Continuous (F' d) := fun d => ((hcontD.comp (hin_cont d)).mul he).neg
  have hF_int : Integrable (F s) := by
    refine Integrable.mono' (hG8.const_mul (C0 * Ce)) (hF_cont s).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    simp only [hF, norm_mul]
    calc ‖L (z.1 - s, z.2)‖ * ‖e z‖
        ≤ C0 * (Ce * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * 2))) :=
          mul_le_mul (norm_le_of_weighted hC0 _) (he8 z) (norm_nonneg _) hC00
      _ = C0 * Ce * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * 2)) := by ring
  have h_bound : ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)), ∀ d ∈ (univ : Set ℝ),
      ‖F' d z‖ ≤ C1 * Ce * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * 2)) := by
    refine Filter.Eventually.of_forall fun z d _ => ?_
    simp only [hF', norm_neg, norm_mul]
    calc ‖d1 L (z.1 - d, z.2)‖ * ‖e z‖
        ≤ C1 * (Ce * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * 2))) :=
          mul_le_mul (norm_le_of_weighted hC1 _) (he8 z) (norm_nonneg _) hC10
      _ = C1 * Ce * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * 2)) := by ring
  have h_diff : ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)), ∀ d ∈ (univ : Set ℝ),
      HasDerivAt (fun d => F d z) (F' d z) d := by
    refine Filter.Eventually.of_forall fun z d _ => ?_
    have hin : HasDerivAt (fun d : ℝ => ((z.1 - d, z.2) : ℝ × ℝ)) ((-1 : ℝ), (0 : ℝ)) d :=
      ((hasDerivAt_id d).const_sub z.1).prodMk (hasDerivAt_const d z.2)
    have hcomp := (hL.differentiable (z.1 - d, z.2)).hasFDerivAt.comp_hasDerivAt d hin
    have hmul := hcomp.mul_const (e z)
    have hval : F' d z = fderiv ℝ L (z.1 - d, z.2) ((-1 : ℝ), (0 : ℝ)) * e z := by
      have hv : ((-1 : ℝ), (0 : ℝ)) = -((1 : ℝ), (0 : ℝ)) := by simp
      rw [hv, map_neg]
      simp only [hF', d1]
      ring
    rw [hval]
    exact hmul
  have key := (hasDerivAt_integral_of_dominated_loc_of_deriv_le Filter.univ_mem
    (Filter.Eventually.of_forall fun d => (hF_cont d).aestronglyMeasurable) hF_int
    (hF'_cont s).aestronglyMeasurable h_bound (hG8.const_mul (C1 * Ce)) h_diff).2
  have e2 : ∫ z, F' s z = -(crossT e (d1 L) s) := by
    simp only [hF']
    rw [integral_neg]
    rfl
  rw [← e2]
  exact key

/-- `(1+|x|)^p e^{-(x²+y²)/8} ≤ e^{4p²} e^{-(x²+y²)/16}`. -/
theorem pow_mul_gauss_le (p : ℕ) (x y : ℝ) :
    (1 + |x|) ^ p * Real.exp (-(x ^ 2 + y ^ 2) / 8) ≤
      Real.exp (4 * (p : ℝ) ^ 2) * Real.exp (-(x ^ 2 + y ^ 2) / (4 * 4)) := by
  have h1 : (1 + |x|) ^ p ≤ Real.exp ((p : ℝ) * |x|) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp |x|]) p
  calc (1 + |x|) ^ p * Real.exp (-(x ^ 2 + y ^ 2) / 8)
      ≤ Real.exp ((p : ℝ) * |x|) * Real.exp (-(x ^ 2 + y ^ 2) / 8) := by gcongr
    _ = Real.exp ((p : ℝ) * |x| + -(x ^ 2 + y ^ 2) / 8) := by rw [Real.exp_add]
    _ ≤ Real.exp (4 * (p : ℝ) ^ 2 + -(x ^ 2 + y ^ 2) / (4 * 4)) := by
        apply Real.exp_le_exp.2
        nlinarith [sq_nonneg (|x| / 4 - 2 * (p : ℝ)), sq_abs x, sq_nonneg y]
    _ = Real.exp (4 * (p : ℝ) ^ 2) * Real.exp (-(x ^ 2 + y ^ 2) / (4 * 4)) := by
        rw [Real.exp_add]

/-- Decay of the cross integral: `‖T_L(s)‖ ≤ K (1+|s|)^{-p}` when `‖L z‖ (1+‖z‖)^p ≤ C`. -/
theorem crossT_decay {e : ℝ × ℝ → ℂ} (he : Continuous e) {Ce : ℝ}
    (hCe : ∀ z : ℝ × ℝ, ‖e z‖ ≤ Ce * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8))
    {L : ℝ × ℝ → ℂ} (hLc : Continuous L) {C : ℝ} {p : ℕ}
    (hC : ∀ z, ‖L z‖ * (1 + ‖z‖) ^ p ≤ C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℝ, ‖crossT e L s‖ ≤ K * ((1 + |s|) ^ p)⁻¹ := by
  have hC0 : 0 ≤ C := (by positivity : (0 : ℝ) ≤ ‖L 0‖ * (1 + ‖(0 : ℝ × ℝ)‖) ^ p).trans (hC 0)
  have hCe0 : 0 ≤ Ce := by
    have h := (norm_nonneg _).trans (hCe 0)
    simpa using h
  have hG16 := Gaussian.integrable_gauss_plane (a := 4) (by norm_num)
  set G16 := ∫ z : ℝ × ℝ, Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * 4)) with hG16def
  have hG160 : 0 ≤ G16 := integral_nonneg fun z => (Real.exp_pos _).le
  refine ⟨C * Ce * Real.exp (4 * (p : ℝ) ^ 2) * G16, by positivity, fun s => ?_⟩
  have hs0 : 0 < (1 + |s|) ^ p := by positivity
  have hpt : ∀ z : ℝ × ℝ, ‖L (z.1 - s, z.2) * e z‖ ≤
      (C * Ce * Real.exp (4 * (p : ℝ) ^ 2) * ((1 + |s|) ^ p)⁻¹) *
        Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * 4)) := by
    intro z
    rw [norm_mul]
    have hw : ‖L (z.1 - s, z.2)‖ * (1 + |z.1 - s|) ^ p ≤ C := by
      refine le_trans ?_ (hC (z.1 - s, z.2))
      gcongr
      have : |z.1 - s| ≤ ‖((z.1 - s, z.2) : ℝ × ℝ)‖ := by
        rw [← Real.norm_eq_abs]; exact norm_fst_le ((z.1 - s, z.2) : ℝ × ℝ)
      linarith
    have hpeetre : (1 + |s|) ^ p ≤ (1 + |z.1 - s|) ^ p * (1 + |z.1|) ^ p := by
      rw [← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ p
      have h := Gaussian.one_add_abs_add_le (s - z.1) z.1
      rw [sub_add_cancel, abs_sub_comm] at h
      exact h
    have hgauss := pow_mul_gauss_le p z.1 z.2
    have hez := hCe z
    -- combine
    have hL1 : ‖L (z.1 - s, z.2)‖ * (1 + |s|) ^ p ≤ C * (1 + |z.1|) ^ p := by
      calc ‖L (z.1 - s, z.2)‖ * (1 + |s|) ^ p
          ≤ ‖L (z.1 - s, z.2)‖ * ((1 + |z.1 - s|) ^ p * (1 + |z.1|) ^ p) := by gcongr
        _ = (‖L (z.1 - s, z.2)‖ * (1 + |z.1 - s|) ^ p) * (1 + |z.1|) ^ p := by ring
        _ ≤ C * (1 + |z.1|) ^ p := by gcongr
    have hL2 : ‖L (z.1 - s, z.2)‖ ≤ C * (1 + |z.1|) ^ p * ((1 + |s|) ^ p)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hs0]; exact hL1
    calc ‖L (z.1 - s, z.2)‖ * ‖e z‖
        ≤ (C * (1 + |z.1|) ^ p * ((1 + |s|) ^ p)⁻¹) *
            (Ce * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)) :=
          mul_le_mul hL2 hez (norm_nonneg _) (by positivity)
      _ = C * Ce * ((1 + |s|) ^ p)⁻¹ *
            ((1 + |z.1|) ^ p * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)) := by ring
      _ ≤ C * Ce * ((1 + |s|) ^ p)⁻¹ *
            (Real.exp (4 * (p : ℝ) ^ 2) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * 4))) := by
          gcongr
      _ = (C * Ce * Real.exp (4 * (p : ℝ) ^ 2) * ((1 + |s|) ^ p)⁻¹) *
            Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * 4)) := by ring
  calc ‖crossT e L s‖
      ≤ ∫ z : ℝ × ℝ, (C * Ce * Real.exp (4 * (p : ℝ) ^ 2) * ((1 + |s|) ^ p)⁻¹) *
          Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * 4)) :=
        norm_integral_le_of_norm_le (hG16.const_mul _) (Filter.Eventually.of_forall hpt)
    _ = C * Ce * Real.exp (4 * (p : ℝ) ^ 2) * G16 * ((1 + |s|) ^ p)⁻¹ := by
        rw [integral_const_mul]; ring

end UnforcedLeray.Short.IIIa.LamJetInf
