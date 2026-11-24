import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_4_1

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

theorem chm_cpd_test {ψ : Coord → ℝ} (hψ : IsSTTestCoord ψ) (j : Fin 3) :
    IsSTTestCoord (fun x => cpd j ψ x) :=
  ⟨(hψ.smooth.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const,
    hψ.compact.fderiv_apply ℝ (cdir j)⟩

theorem chm_cylT_test (ν : ℝ) {φ : Coord → ℝ} (hφ : IsSTTestCoord φ) :
    IsSTTestCoord (cylHeatT ν φ) := by
  have h1 := chm_cpd_test hφ 0
  have h2 := chm_cpd_test (chm_cpd_test hφ 1) 1
  have h3 := chm_cpd_test (chm_cpd_test hφ 2) 2
  unfold cylHeatT
  refine ⟨?_, ?_⟩
  · exact h1.smooth.neg.sub (contDiff_const.mul (h2.smooth.add h3.smooth))
  · exact (h1.compact.neg).sub ((h2.compact.add h3.compact).mul_left (f := fun _ : Coord => ν))

theorem chm_integrable_memLp {f : Coord → ℝ} {r : ℝ} (hr : 1 < r)
    (hf : MemLp f (ENNReal.ofReal r) volume) {g : Coord → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) : Integrable (fun x => f x * g x) volume := by
  have hloc : LocallyIntegrable f volume := hf.locallyIntegrable (ENNReal.one_le_ofReal.2 hr.le)
  have := hloc.integrable_smul_left_of_hasCompactSupport hg hgc
  simpa only [smul_eq_mul, mul_comm] using this

theorem chm_split_pt (z : ℂ) (c : ℝ) :
    z * (c : ℂ) = ((z.re * c : ℝ) : ℂ) + Complex.I * ((z.im * c : ℝ) : ℂ) := by
  apply Complex.ext <;> simp

theorem chm_split_sum (a b c : ℝ) :
    ((a : ℂ) + Complex.I * (b : ℂ)) * (c : ℂ) =
      ((a * c : ℝ) : ℂ) + Complex.I * ((b * c : ℝ) : ℂ) := by
  push_cast
  ring

theorem chm_int_split (g : Coord → ℂ) (a b : Coord → ℝ)
    (hg : ∀ x, g x = (a x : ℂ) + Complex.I * (b x : ℂ))
    (ha : Integrable a volume) (hb : Integrable b volume) :
    ∫ x, g x = ((∫ x, a x : ℝ) : ℂ) + Complex.I * ((∫ x, b x : ℝ) : ℂ) := by
  simp_rw [hg]
  calc ∫ x, ((a x : ℂ) + Complex.I * (b x : ℂ))
      = (∫ x, (a x : ℂ)) + ∫ x, Complex.I * (b x : ℂ) :=
        integral_add ha.ofReal (hb.ofReal.const_mul Complex.I)
    _ = _ := by
        rw [integral_const_mul, integral_complex_ofReal, integral_complex_ofReal]

theorem chm_ofReal_add_eq {a b c d : ℝ}
    (h : (a : ℂ) + Complex.I * (b : ℂ) = (c : ℂ) + Complex.I * (d : ℂ)) : a = c ∧ b = d := by
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp at h1 h2
  exact ⟨h1, h2⟩

theorem chm_eLpNorm_re_le (z : Coord → ℂ) (p : ℝ≥0∞) :
    eLpNorm (fun x => (z x).re) p volume ≤ eLpNorm z p volume :=
  eLpNorm_mono fun x => by
    rw [Real.norm_eq_abs]
    exact Complex.abs_re_le_norm (z x)

theorem chm_eLpNorm_im_le (z : Coord → ℂ) (p : ℝ≥0∞) :
    eLpNorm (fun x => (z x).im) p volume ≤ eLpNorm z p volume :=
  eLpNorm_mono fun x => by
    rw [Real.norm_eq_abs]
    exact Complex.abs_im_le_norm (z x)

theorem chm_aesm_complex {a b : Coord → ℝ} (ha : AEStronglyMeasurable a volume)
    (hb : AEStronglyMeasurable b volume) :
    AEStronglyMeasurable (fun x => (a x : ℂ) + Complex.I * (b x : ℂ)) volume :=
  (Complex.continuous_ofReal.comp_aestronglyMeasurable ha).add
    ((continuous_const.mul Complex.continuous_ofReal).comp_aestronglyMeasurable hb)

theorem chm_eLpNorm_split {a b : Coord → ℝ} (ha : AEStronglyMeasurable a volume)
    (hb : AEStronglyMeasurable b volume) {g : Coord → ℂ}
    (hg : ∀ x, g x = (a x : ℂ) + Complex.I * (b x : ℂ)) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    eLpNorm g p volume ≤ eLpNorm a p volume + eLpNorm b p volume := by
  calc eLpNorm g p volume ≤ eLpNorm (fun x => ‖a x‖ + ‖b x‖) p volume := by
        apply eLpNorm_mono
        intro x
        show ‖g x‖ ≤ ‖‖a x‖ + ‖b x‖‖
        rw [Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)), hg x]
        calc ‖(a x : ℂ) + Complex.I * (b x : ℂ)‖
            ≤ ‖(a x : ℂ)‖ + ‖Complex.I * (b x : ℂ)‖ := norm_add_le _ _
          _ = ‖a x‖ + ‖b x‖ := by simp
    _ ≤ eLpNorm (fun x => ‖a x‖) p volume + eLpNorm (fun x => ‖b x‖) p volume :=
        eLpNorm_add_le ha.norm hb.norm hp
    _ = eLpNorm a p volume + eLpNorm b p volume := by
        rw [eLpNorm_norm, eLpNorm_norm]

/-- **Splitting, for `1 < r`.** The complex estimate with constant `2 C` follows from the real
one with constant `C` (SP 1377-1424), for `1 < r`, where `L^r` functions are locally integrable
so that `Re u · φ`, `Im u · φ` are integrable against test functions. -/
theorem chm_split_gt : ∀ r C : ℝ, 1 < r → 0 < C → ChmEuclidRealAt r C → ChmEuclidAt r (2 * C) := by
  intro r C hr hC hR
  unfold ChmEuclidAt
  intro ν hν u F hu hF hur hFr heq
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := ENNReal.one_le_ofReal.2 hr.le
  have hu1 : AEStronglyMeasurable (fun x => (u x).re) volume := hu.re
  have hu2 : AEStronglyMeasurable (fun x => (u x).im) volume := hu.im
  have hF1 : AEStronglyMeasurable (fun x => (F x).re) volume := hF.re
  have hF2 : AEStronglyMeasurable (fun x => (F x).im) volume := hF.im
  have hu1f : eLpNorm (fun x => (u x).re) (ENNReal.ofReal r) volume < ⊤ :=
    lt_of_le_of_lt (chm_eLpNorm_re_le u _) hur
  have hu2f : eLpNorm (fun x => (u x).im) (ENNReal.ofReal r) volume < ⊤ :=
    lt_of_le_of_lt (chm_eLpNorm_im_le u _) hur
  have hF1f : eLpNorm (fun x => (F x).re) (ENNReal.ofReal r) volume < ⊤ :=
    lt_of_le_of_lt (chm_eLpNorm_re_le F _) hFr
  have hF2f : eLpNorm (fun x => (F x).im) (ENNReal.ofReal r) volume < ⊤ :=
    lt_of_le_of_lt (chm_eLpNorm_im_le F _) hFr
  have hMu1 : MemLp (fun x => (u x).re) (ENNReal.ofReal r) volume := ⟨hu1, hu1f⟩
  have hMu2 : MemLp (fun x => (u x).im) (ENNReal.ofReal r) volume := ⟨hu2, hu2f⟩
  have hMF1 : MemLp (fun x => (F x).re) (ENNReal.ofReal r) volume := ⟨hF1, hF1f⟩
  have hMF2 : MemLp (fun x => (F x).im) (ENNReal.ofReal r) volume := ⟨hF2, hF2f⟩
  -- real equations for the real and imaginary parts
  have hsplitU : ∀ φ : Coord → ℝ, IsSTTestCoord φ →
      ∫ x, u x * (cylHeatT ν φ x : ℂ) = ((∫ x, (u x).re * cylHeatT ν φ x : ℝ) : ℂ) +
        Complex.I * ((∫ x, (u x).im * cylHeatT ν φ x : ℝ) : ℂ) := by
    intro φ hφ
    have hc := chm_cylT_test ν hφ
    exact chm_int_split (fun x => u x * (cylHeatT ν φ x : ℂ))
      (fun x => (u x).re * cylHeatT ν φ x) (fun x => (u x).im * cylHeatT ν φ x)
      (fun x => chm_split_pt _ _)
      (chm_integrable_memLp hr hMu1 hc.smooth.continuous hc.compact)
      (chm_integrable_memLp hr hMu2 hc.smooth.continuous hc.compact)
  have hsplitF : ∀ φ : Coord → ℝ, IsSTTestCoord φ →
      ∫ x, F x * (φ x : ℂ) = ((∫ x, (F x).re * φ x : ℝ) : ℂ) +
        Complex.I * ((∫ x, (F x).im * φ x : ℝ) : ℂ) := by
    intro φ hφ
    exact chm_int_split (fun x => F x * (φ x : ℂ))
      (fun x => (F x).re * φ x) (fun x => (F x).im * φ x)
      (fun x => chm_split_pt _ _)
      (chm_integrable_memLp hr hMF1 hφ.smooth.continuous hφ.compact)
      (chm_integrable_memLp hr hMF2 hφ.smooth.continuous hφ.compact)
  have hIR1 : IsCylHeatR ν (fun x => (u x).re) (fun x => (F x).re) := by
    intro φ hφ
    have h := heq φ hφ
    rw [hsplitU φ hφ, hsplitF φ hφ] at h
    exact (chm_ofReal_add_eq h).1
  have hIR2 : IsCylHeatR ν (fun x => (u x).im) (fun x => (F x).im) := by
    intro φ hφ
    have h := heq φ hφ
    rw [hsplitU φ hφ, hsplitF φ hφ] at h
    exact (chm_ofReal_add_eq h).2
  obtain ⟨Dt1, D21, hDt1m, hD21m, hDt1w, hD21w, hDt1b, hD21b⟩ :=
    hR ν hν (fun x => (u x).re) (fun x => (F x).re) hu1 hF1 hu1f hF1f hIR1
  obtain ⟨Dt2, D22, hDt2m, hD22m, hDt2w, hD22w, hDt2b, hD22b⟩ :=
    hR ν hν (fun x => (u x).im) (fun x => (F x).im) hu2 hF2 hu2f hF2f hIR2
  have hν0 : ν ≠ 0 := hν.ne'
  have hMDt1 : MemLp Dt1 (ENNReal.ofReal r) volume :=
    ⟨hDt1m, lt_of_le_of_lt hDt1b (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hF1f)⟩
  have hMDt2 : MemLp Dt2 (ENNReal.ofReal r) volume :=
    ⟨hDt2m, lt_of_le_of_lt hDt2b (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hF2f)⟩
  have hMD21 : ∀ i j, MemLp (D21 i j) (ENNReal.ofReal r) volume := by
    intro i j
    have hm : MemLp (fun x => ν * D21 i j x) (ENNReal.ofReal r) volume :=
      ⟨(hD21m i j).const_mul ν,
        lt_of_le_of_lt (hD21b i j) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hF1f)⟩
    have := hm.const_mul ν⁻¹
    convert this using 1
    funext x
    field_simp
  have hMD22 : ∀ i j, MemLp (D22 i j) (ENNReal.ofReal r) volume := by
    intro i j
    have hm : MemLp (fun x => ν * D22 i j x) (ENNReal.ofReal r) volume :=
      ⟨(hD22m i j).const_mul ν,
        lt_of_le_of_lt (hD22b i j) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hF2f)⟩
    have := hm.const_mul ν⁻¹
    convert this using 1
    funext x
    field_simp
  refine ⟨fun x => (Dt1 x : ℂ) + Complex.I * (Dt2 x : ℂ),
    fun i j x => (D21 i j x : ℂ) + Complex.I * (D22 i j x : ℂ), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact chm_aesm_complex hDt1m hDt2m
  · intro i j
    exact chm_aesm_complex (hD21m i j) (hD22m i j)
  · intro φ hφ
    dsimp only
    have hcd := chm_cpd_test hφ 0
    have eL := chm_int_split (fun x => u x * (cpd 0 φ x : ℂ))
      (fun x => (u x).re * cpd 0 φ x) (fun x => (u x).im * cpd 0 φ x)
      (fun x => chm_split_pt _ _)
      (chm_integrable_memLp hr hMu1 hcd.smooth.continuous hcd.compact)
      (chm_integrable_memLp hr hMu2 hcd.smooth.continuous hcd.compact)
    have eR := chm_int_split (fun x => ((Dt1 x : ℂ) + Complex.I * (Dt2 x : ℂ)) * (φ x : ℂ))
      (fun x => Dt1 x * φ x) (fun x => Dt2 x * φ x)
      (fun x => chm_split_sum _ _ _)
      (chm_integrable_memLp hr hMDt1 hφ.smooth.continuous hφ.compact)
      (chm_integrable_memLp hr hMDt2 hφ.smooth.continuous hφ.compact)
    have w1 : ∫ x, (u x).re * cpd 0 φ x = -∫ x, Dt1 x * φ x := hDt1w φ hφ
    have w2 : ∫ x, (u x).im * cpd 0 φ x = -∫ x, Dt2 x * φ x := hDt2w φ hφ
    rw [eL, eR, w1, w2]
    push_cast
    ring
  · intro i j φ hφ
    dsimp only
    have hW := chm_cpd_test (chm_cpd_test hφ j.succ) i.succ
    have eL := chm_int_split (fun x => u x * (cpd i.succ (fun y => cpd j.succ φ y) x : ℂ))
      (fun x => (u x).re * cpd i.succ (fun y => cpd j.succ φ y) x)
      (fun x => (u x).im * cpd i.succ (fun y => cpd j.succ φ y) x)
      (fun x => chm_split_pt _ _)
      (chm_integrable_memLp hr hMu1 hW.smooth.continuous hW.compact)
      (chm_integrable_memLp hr hMu2 hW.smooth.continuous hW.compact)
    have eR := chm_int_split
      (fun x => ((D21 i j x : ℂ) + Complex.I * (D22 i j x : ℂ)) * (φ x : ℂ))
      (fun x => D21 i j x * φ x) (fun x => D22 i j x * φ x)
      (fun x => chm_split_sum _ _ _)
      (chm_integrable_memLp hr (hMD21 i j) hφ.smooth.continuous hφ.compact)
      (chm_integrable_memLp hr (hMD22 i j) hφ.smooth.continuous hφ.compact)
    have w1 : ∫ x, (u x).re * cpd i.succ (fun y => cpd j.succ φ y) x = ∫ x, D21 i j x * φ x :=
      hD21w i j φ hφ
    have w2 : ∫ x, (u x).im * cpd i.succ (fun y => cpd j.succ φ y) x = ∫ x, D22 i j x * φ x :=
      hD22w i j φ hφ
    rw [eL, eR, w1, w2]
  · have hF1le := chm_eLpNorm_re_le F (ENNReal.ofReal r)
    have hF2le := chm_eLpNorm_im_le F (ENNReal.ofReal r)
    calc eLpNorm (fun x => (Dt1 x : ℂ) + Complex.I * (Dt2 x : ℂ)) (ENNReal.ofReal r) volume
        ≤ eLpNorm Dt1 (ENNReal.ofReal r) volume + eLpNorm Dt2 (ENNReal.ofReal r) volume :=
          chm_eLpNorm_split hDt1m hDt2m (fun x => rfl) _ hp1
      _ ≤ ENNReal.ofReal C * eLpNorm (fun x => (F x).re) (ENNReal.ofReal r) volume +
            ENNReal.ofReal C * eLpNorm (fun x => (F x).im) (ENNReal.ofReal r) volume :=
          add_le_add hDt1b hDt2b
      _ ≤ ENNReal.ofReal C * eLpNorm F (ENNReal.ofReal r) volume +
            ENNReal.ofReal C * eLpNorm F (ENNReal.ofReal r) volume :=
          add_le_add (by gcongr) (by gcongr)
      _ = ENNReal.ofReal (2 * C) * eLpNorm F (ENNReal.ofReal r) volume := by
          rw [← add_mul, ← ENNReal.ofReal_add hC.le hC.le, two_mul]
  · intro i j
    dsimp only
    have hF1le := chm_eLpNorm_re_le F (ENNReal.ofReal r)
    have hF2le := chm_eLpNorm_im_le F (ENNReal.ofReal r)
    calc eLpNorm (fun x => (ν : ℂ) * ((D21 i j x : ℂ) + Complex.I * (D22 i j x : ℂ)))
          (ENNReal.ofReal r) volume
        ≤ eLpNorm (fun x => ν * D21 i j x) (ENNReal.ofReal r) volume +
            eLpNorm (fun x => ν * D22 i j x) (ENNReal.ofReal r) volume :=
          chm_eLpNorm_split ((hD21m i j).const_mul ν) ((hD22m i j).const_mul ν)
            (fun x => by push_cast; ring) _ hp1
      _ ≤ ENNReal.ofReal C * eLpNorm (fun x => (F x).re) (ENNReal.ofReal r) volume +
            ENNReal.ofReal C * eLpNorm (fun x => (F x).im) (ENNReal.ofReal r) volume :=
          add_le_add (hD21b i j) (hD22b i j)
      _ ≤ ENNReal.ofReal C * eLpNorm F (ENNReal.ofReal r) volume +
            ENNReal.ofReal C * eLpNorm F (ENNReal.ofReal r) volume :=
          add_le_add (by gcongr) (by gcongr)
      _ = ENNReal.ofReal (2 * C) * eLpNorm F (ENNReal.ofReal r) volume := by
          rw [← add_mul, ← ENNReal.ofReal_add hC.le hC.le, two_mul]

theorem chmEuclidSplit : UnforcedLeray.Short.IIb.ChmEuclidSplit := chm_split_gt

end UnforcedLeray.Short.IIb
