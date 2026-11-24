import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_b_L4.IntPlanar
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.ComplCoupling.EulerSubBound.Lattice
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_b_L1

/-!
# Leaf B4, finite-rank part: periodization tails (SP 2894-2897)

* `perE_tail`: on the cell, `P_d e - e = O(d⁻²) e^{-|y|²/16}` (Gaussian columns);
* `eLpNorm_gauss_plane`: Gaussian-dominated fields have finite `L²_m` norm on the plane;
* `cellE_sub_e`: `‖1_cell P_d e - e‖_{L²_m} = O(d⁻²)`;
* `xNorm_neg_le_of_bound`: bounded fields have `X_{-m,d}` norm uniformly bounded in `d`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric UnforcedLeray.Blueprint.Planar

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub

namespace BlockPropagatorInteriorSub

open OrgSplit
open scoped ComplexConjugate ContDiff InnerProductSpace InnerProduct ENNReal

namespace OrgSplit3

namespace PlanarB

namespace L4

/-- `e^{-t} ≤ 1/t`-type bound used for the lattice tail. -/
theorem exp_neg_le_inv {t : ℝ} (ht : 0 < t) : Real.exp (-t) ≤ 1 / t := by
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ ht (by linarith [Real.add_one_le_exp t])

/-- **Gaussian tail of the periodization on the cell**: `‖P_d e_i - e_i‖ ≤ C d⁻² e^{-|y|²/16}`. -/
theorem perE_tail (κ : PlanarFrameKernels) :
    ∃ C_t : ℝ, 0 ≤ C_t ∧ ∀ d : ℝ, 1 ≤ d → ∀ (i : Fin 2) (x : ℝ × ℝ), x ∈ B0579.cell d →
      ‖perE κ d i x - κ.e i x‖ ≤ C_t / d ^ 2 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16) := by
  obtain ⟨C, hC⟩ := κ.e_decay
  set C' := |C| with hC'
  have hC'0 : 0 ≤ C' := abs_nonneg C
  refine ⟨C' * 256 * EulerSubCore.sZ, by have := EulerSubCore.sZ_nonneg; positivity,
    fun d hd i x hx => ?_⟩
  have hd0 : 0 < d := lt_of_lt_of_le one_pos hd
  have hx1 : |x.1| ≤ d / 2 := EulerSubCore.abs_fst_le_half_of_mem_cell hx
  have hCe : ∀ z : ℝ × ℝ, ‖κ.e i z‖ ≤ C' * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := fun z =>
    (hC i z).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le)
  have hs : Summable (fun n : ℤ => κ.e i (x.1 + n * d, x.2)) := by
    refine Summable.of_norm_bounded ((Gaussian.summable_translate (s := 2) (c := -d)
      (by norm_num) (neg_ne_zero.2 hd0.ne') x.1).mul_left (16 * C')) (fun n => ?_)
    rw [show x.1 - (n : ℝ) * -d = x.1 + n * d by ring]
    calc ‖κ.e i (x.1 + n * d, x.2)‖
        ≤ C' * Real.exp (-((x.1 + n * d) ^ 2 + x.2 ^ 2) / 8) := hCe _
      _ ≤ C' * (16 * (1 + |x.1 + n * d|) ^ (-(2 : ℝ))) :=
          mul_le_mul_of_nonneg_left (perCont_exp_le_translate_weight _ _) hC'0
      _ = 16 * C' * (1 + |x.1 + n * d|) ^ (-2 : ℝ) := by ring
  set G := Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16) with hG
  have hG0 : 0 ≤ G := (Real.exp_pos _).le
  have hbound : ∀ n : ℤ, n ≠ 0 → ‖κ.e i (x.1 + n * d, x.2)‖ ≤
      C' * 256 / d ^ 2 * G * (1 + |(n : ℝ)|) ^ (-(2 : ℝ)) := by
    intro n hn
    have hN : 1 ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
    have hND : |(n : ℝ)| * d = |(n : ℝ) * d| := by rw [abs_mul, abs_of_pos hd0]
    have htri : |(n : ℝ) * d| ≤ |x.1 + n * d| + |x.1| := by
      calc |(n : ℝ) * d| = |(x.1 + n * d) - x.1| := by congr 1; ring
        _ ≤ |x.1 + n * d| + |x.1| := abs_sub _ _
    have hlow : |(n : ℝ)| * d / 2 ≤ |x.1 + n * d| := by
      nlinarith [mul_le_mul_of_nonneg_right hN hd0.le]
    have hsq : ((n : ℝ) * d) ^ 2 / 4 ≤ (x.1 + n * d) ^ 2 := by
      have h := pow_le_pow_left₀ (by positivity) hlow 2
      have e1 : (|(n : ℝ)| * d / 2) ^ 2 = ((n : ℝ) * d) ^ 2 / 4 := by
        rw [div_pow, mul_pow, sq_abs]; ring
      rwa [e1, sq_abs] at h
    have hx2 : x.1 ^ 2 ≤ d ^ 2 / 4 := by
      have := pow_le_pow_left₀ (abs_nonneg x.1) hx1 2
      rw [sq_abs, div_pow] at this
      linarith
    have hn2 : 1 ≤ (n : ℝ) ^ 2 := by
      have : 1 ≤ |(n : ℝ)| ^ 2 := by nlinarith
      rwa [sq_abs] at this
    have hA : x.1 ^ 2 ≤ (x.1 + n * d) ^ 2 := by
      have : d ^ 2 / 4 ≤ ((n : ℝ) * d) ^ 2 / 4 := by
        rw [mul_pow]; nlinarith [sq_nonneg d]
      linarith
    -- the exponent
    have hexp : Real.exp (-((x.1 + n * d) ^ 2 + x.2 ^ 2) / 8) ≤
        G * Real.exp (-(((n : ℝ) * d) ^ 2 / 64)) := by
      rw [hG, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg x.2]
    have ht : 0 < ((n : ℝ) * d) ^ 2 / 64 := by
      have : 0 < ((n : ℝ) * d) ^ 2 := by
        have h1 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
        positivity
      positivity
    have hinv : Real.exp (-(((n : ℝ) * d) ^ 2 / 64)) ≤
        256 / d ^ 2 * (1 + |(n : ℝ)|) ^ (-(2 : ℝ)) := by
      refine (exp_neg_le_inv ht).trans ?_
      have hpos : 0 < 1 + |(n : ℝ)| := by positivity
      rw [Real.rpow_neg hpos.le, Real.rpow_two]
      have hsq1 : (1 + |(n : ℝ)|) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by
        have : (1 + |(n : ℝ)|) ^ 2 ≤ (2 * |(n : ℝ)|) ^ 2 :=
          pow_le_pow_left₀ hpos.le (by linarith) 2
        rw [mul_pow, sq_abs] at this
        linarith
      have hd2 : 0 < d ^ 2 := by positivity
      have hn0 : (0 : ℝ) < (n : ℝ) ^ 2 := by linarith
      have e1 : 1 / (((n : ℝ) * d) ^ 2 / 64) = 64 / ((n : ℝ) ^ 2 * d ^ 2) := by
        rw [mul_pow]; field_simp
      have e2 : 256 / d ^ 2 * ((1 + |(n : ℝ)|) ^ 2)⁻¹ = 256 / (d ^ 2 * (1 + |(n : ℝ)|) ^ 2) := by
        field_simp
      rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity)]
      have h4 : (0 : ℝ) ≤ (1 + |(n : ℝ)|) ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hsq1 hd2.le]
    calc ‖κ.e i (x.1 + n * d, x.2)‖
        ≤ C' * Real.exp (-((x.1 + n * d) ^ 2 + x.2 ^ 2) / 8) := hCe _
      _ ≤ C' * (G * (256 / d ^ 2 * (1 + |(n : ℝ)|) ^ (-(2 : ℝ)))) :=
          mul_le_mul_of_nonneg_left (hexp.trans (mul_le_mul_of_nonneg_left hinv hG0)) hC'0
      _ = C' * 256 / d ^ 2 * G * (1 + |(n : ℝ)|) ^ (-(2 : ℝ)) := by ring
  have h := EulerSubCore.norm_tsum_sub_zero_le hs (A := C' * 256 / d ^ 2 * G)
    (by positivity) hbound
  simp only [Int.cast_zero, zero_mul, add_zero, Prod.mk.eta] at h
  calc ‖perE κ d i x - κ.e i x‖ = ‖(∑' n : ℤ, κ.e i (x.1 + n * d, x.2)) - κ.e i x‖ := rfl
    _ ≤ C' * 256 / d ^ 2 * G * EulerSubCore.sZ := h
    _ = C' * 256 * EulerSubCore.sZ / d ^ 2 * G := by ring

/-- The `L²_m` norm on the plane of a Gaussian-dominated field. -/
theorem eLpNorm_gauss_plane (m : ℝ) (hm : 0 ≤ m) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ (M : ℝ) (F : ℝ × ℝ → ℂ), 0 ≤ M → AEStronglyMeasurable F volume →
      (∀ x, ‖F x‖ ≤ M * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16)) →
        eLpNorm (fun z => F (cToPlane z)) 2 (Planar.wMeasure m) ≤ ENNReal.ofReal (M * N) := by
  set k : ℝ := m / 2 + 1 with hk
  have hk0 : 0 < k := by rw [hk]; linarith
  have hk16 : 1 ≤ 16 * k := by rw [hk]; linarith
  set A : ℝ := (16 * k) ^ k with hA
  have hA0 : 0 ≤ A := by positivity
  set N : ℝ := A * IIb.jbNegL2Norm 1 with hN
  refine ⟨N, mul_nonneg hA0 (IIb.jbNegL2Norm_nonneg 1), fun M F hM hFm hF => ?_⟩
  have hmp := BlockPropagatorSub.measurePreserving_cToPlane_wMeasure m
  have hF' : AEStronglyMeasurable F (volume.withDensity fun y => (B0579.density m y : ℝ≥0∞)) :=
    hFm.mono_ac (withDensity_absolutelyContinuous _ _)
  have h1 : eLpNorm (fun z => F (cToPlane z)) 2 (Planar.wMeasure m) = eLpNorm F 2 (IIb.planeMeasure m) :=
    eLpNorm_comp_measurePreserving hF' hmp
  rw [h1]
  set g : ℝ × ℝ → ℝ := fun x => M * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16) with hg
  have h2 : eLpNorm F 2 (IIb.planeMeasure m) ≤ eLpNorm g 2 (IIb.planeMeasure m) := by
    refine eLpNorm_mono fun x => (hF x).trans ?_
    rw [hg, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  refine h2.trans ?_
  rw [IIb.eLpNorm_planeMeasure]
  have h3 : ∀ x : ℝ × ℝ, ‖B0579.jb x ^ (m / 2) * g x‖ ≤ ‖(M * A) * B0579.jb x ^ (-(1 : ℝ))‖ := by
    intro x
    have hjb0 : 0 < B0579.jb x := B0579.jb_pos x
    have hjb : B0579.jb x = 1 + (x.1 ^ 2 + x.2 ^ 2) := by unfold B0579.jb; ring
    have hpe := PlanarDampedProof.rpow_le_exp k hk0 hk16 (x.1 ^ 2 + x.2 ^ 2) (by positivity)
    rw [← hjb] at hpe
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)]
    have hsplit : B0579.jb x ^ (m / 2) = B0579.jb x ^ k * B0579.jb x ^ (-(1 : ℝ)) := by
      rw [← Real.rpow_add hjb0]; congr 1; rw [hk]; ring
    rw [hsplit, hg]
    have he : Real.exp ((x.1 ^ 2 + x.2 ^ 2) / 16) * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16) = 1 := by
      rw [← Real.exp_add]; rw [show (x.1 ^ 2 + x.2 ^ 2) / 16 + -(x.1 ^ 2 + x.2 ^ 2) / 16 = 0 by ring]
      exact Real.exp_zero
    have hj1 : 0 ≤ B0579.jb x ^ (-(1 : ℝ)) := Real.rpow_nonneg hjb0.le _
    have hE0 : 0 ≤ Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16) := (Real.exp_pos _).le
    calc B0579.jb x ^ k * B0579.jb x ^ (-(1 : ℝ)) * (M * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16))
        ≤ A * Real.exp ((x.1 ^ 2 + x.2 ^ 2) / 16) * B0579.jb x ^ (-(1 : ℝ)) *
            (M * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16)) := by
          gcongr
      _ = M * A * B0579.jb x ^ (-(1 : ℝ)) *
            (Real.exp ((x.1 ^ 2 + x.2 ^ 2) / 16) * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16)) := by ring
      _ = M * A * B0579.jb x ^ (-(1 : ℝ)) := by rw [he, mul_one]
  refine (eLpNorm_mono h3).trans ?_
  have h4 : eLpNorm (fun x : ℝ × ℝ => (M * A) * B0579.jb x ^ (-(1 : ℝ))) 2 volume =
      ENNReal.ofReal (M * A) * eLpNorm (fun x : ℝ × ℝ => B0579.jb x ^ (-(1 : ℝ))) 2 volume := by
    have := eLpNorm_const_smul (p := 2) (μ := (volume : Measure (ℝ × ℝ))) (M * A)
      (fun x : ℝ × ℝ => B0579.jb x ^ (-(1 : ℝ)))
    rw [Real.enorm_eq_ofReal (by positivity)] at this
    exact this
  rw [h4, ← IIb.ofReal_jbNegL2Norm (s := 1) (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  rw [hN]; ring

/-- `‖1_cell P_d e_i - e_i‖_{L²_m} = O(d⁻²)` on the plane. -/
theorem cellE_sub_e (κ : PlanarFrameKernels) (m : ℝ) (hm : 0 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℝ, 1 ≤ d → ∀ i : Fin 2,
      eLpNorm (fun z => cellZeroExt d (perE κ d i) (cToPlane z) - κ.e i (cToPlane z)) 2
        (Planar.wMeasure m) ≤ ENNReal.ofReal (C / d ^ 2) := by
  obtain ⟨C_t, hC_t, ht⟩ := perE_tail κ
  obtain ⟨N, hN, hgauss⟩ := eLpNorm_gauss_plane m hm
  obtain ⟨C, hC⟩ := κ.e_decay
  set C' := |C| with hC'
  have hC'0 : 0 ≤ C' := abs_nonneg C
  refine ⟨(C_t + 64 * C') * N, by positivity, fun d hd i => ?_⟩
  have hd0 : 0 < d := lt_of_lt_of_le one_pos hd
  have hcont : Continuous (perE κ d i) := perE_continuous_aux κ hd0 i
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ × ℝ => cellZeroExt d (perE κ d i) x - κ.e i x) volume := by
    unfold cellZeroExt
    exact ((hcont.measurable.indicator (B0579.measurableSet_cell d)).sub
      (κ.e_cont i).measurable).aestronglyMeasurable
  have hb := hgauss ((C_t + 64 * C') / d ^ 2) (fun x => cellZeroExt d (perE κ d i) x - κ.e i x)
    (by positivity) hmeas (fun x => ?_)
  · refine hb.trans (le_of_eq ?_)
    congr 1; ring
  · have hG0 : 0 ≤ Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16) := (Real.exp_pos _).le
    by_cases hx : x ∈ B0579.cell d
    · unfold cellZeroExt
      rw [Set.indicator_of_mem hx]
      refine (ht d hd i x hx).trans ?_
      have : C_t / d ^ 2 ≤ (C_t + 64 * C') / d ^ 2 :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
      exact mul_le_mul_of_nonneg_right this hG0
    · unfold cellZeroExt
      rw [Set.indicator_of_notMem hx, zero_sub, norm_neg]
      have hx1 : d / 2 ≤ |x.1| := by
        simp only [B0579.cell, mem_prod, mem_Ico, mem_univ, and_true, not_and_or, not_le,
          not_lt] at hx
        rcases hx with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_nonneg (by linarith)]; linarith
      have hx2 : d ^ 2 / 4 ≤ x.1 ^ 2 := by
        have := pow_le_pow_left₀ (by positivity) hx1 2
        rw [sq_abs, div_pow] at this
        linarith
      have he := hC i x
      have hsplit : Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 8) =
          Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16) * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16) := by
        rw [← Real.exp_add]; congr 1; ring
      have ht' : 0 < d ^ 2 / 64 := by positivity
      have hsmall : Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16) ≤ 64 / d ^ 2 := by
        calc Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16) ≤ Real.exp (-(d ^ 2 / 64)) :=
              Real.exp_le_exp.mpr (by nlinarith [sq_nonneg x.2])
          _ ≤ 1 / (d ^ 2 / 64) := exp_neg_le_inv ht'
          _ = 64 / d ^ 2 := by field_simp
      calc ‖κ.e i x‖ ≤ C' * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 8) :=
            he.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le)
        _ = C' * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16) *
              Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16) := by rw [hsplit]; ring
        _ ≤ C' * (64 / d ^ 2) * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16) := by gcongr
        _ ≤ (C_t + 64 * C') / d ^ 2 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16) := by
            apply mul_le_mul_of_nonneg_right _ hG0
            rw [mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]
            linarith

/-- A field bounded by `M` on the cell has `X_{-m,d}` norm at most `M N_m`, uniformly in `d`. -/
theorem xNorm_neg_le_of_bound {m : ℝ} (hm : 1 < m) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ (d M : ℝ) (f : ℝ × ℝ → ℂ), 0 ≤ M →
      (∀ x ∈ B0579.cell d, ‖f x‖ ≤ M) → xNorm d (-m) f ≤ ENNReal.ofReal (M * N) := by
  refine ⟨IIb.jbNegL2Norm (m / 2), IIb.jbNegL2Norm_nonneg _, fun d M f hM hf => ?_⟩
  unfold xNorm
  rw [IIb.cellMeasure_eq_restrict_planeMeasure]
  have h1 : eLpNorm f 2 ((IIb.planeMeasure (-m)).restrict (B0579.cell d)) ≤
      eLpNorm (fun _ : ℝ × ℝ => M) 2 ((IIb.planeMeasure (-m)).restrict (B0579.cell d)) := by
    refine eLpNorm_mono_ae ?_
    rw [ae_restrict_iff' (B0579.measurableSet_cell d)]
    refine Eventually.of_forall fun x hx => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg hM]
    exact hf x hx
  refine h1.trans ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans ?_)
  rw [IIb.eLpNorm_planeMeasure]
  have h2 : (fun x : ℝ × ℝ => B0579.jb x ^ (-m / 2) * M) =
      fun x => M • B0579.jb x ^ (-(m / 2)) := by
    funext x; rw [smul_eq_mul, mul_comm, neg_div]
  have h3 : (fun x : ℝ × ℝ => M • B0579.jb x ^ (-(m / 2))) =
      M • (fun x : ℝ × ℝ => B0579.jb x ^ (-(m / 2))) := rfl
  rw [h2, h3, eLpNorm_const_smul, Real.enorm_eq_ofReal hM,
    ← IIb.ofReal_jbNegL2Norm (s := m / 2) (by linarith), ← ENNReal.ofReal_mul hM]

end L4

end PlanarB

end OrgSplit3
end BlockPropagatorInteriorSub
end UnforcedLeray.Short.IIIa
