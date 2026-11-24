import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TimeJets.KerVelIsBS
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.TranspApprox.TestApprox
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.TranspApprox.KernelVel
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.VelLipBSSub
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.VelLipBSBound
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.VelLipZeroCirc.CellInt
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org_1_a.Interaction

/-!
# Helper for `PartIII-a:T21/c3/3/1/1/2/2/3/c/2`: the kernel velocity is the Biot-Savart velocity

Source `the November 2 reference manuscript` (SP) lines 2863-2865, 2876-2881,
3230-3240.  For a cell of length `D ≥ 1`, `m > 8`, and a zero-circulation `Ω ∈ X_{m,D}`, every
`L²` Biot-Savart velocity `U` of `Ω` (`IsBiotSavart D Ω U`) agrees a.e. on the cell with the
periodic-kernel velocity `kerVelCx D Ω`.

Proof: approximate `Ω` in `X_{m,D}` by complex tests `ψ_n` of zero circulation (`ladTestDensity`);
for tests the kernel velocity is the Biot-Savart velocity (`kerVelIsBS`), so `U - K_D ψ_n` is the
Biot-Savart velocity of `Ω - ψ_n` and tends to `0` in `L²` (`ladBSSub`, `ladBSBound`); on each
band `[-D/2, D/2) × [-R, R]` the kernel velocity is bounded in `L¹` by the `L¹` norm of the
density (integrable near part of the kernel, bounded far part, Tonelli), and that is bounded by
the `X_{m,D}` norm (weighted Cauchy-Schwarz).  Hence `∫_band |U - K_D Ω| = 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa.ComplFreeRateSub.Leaf2WeakEqFrame.KerBSAux

open UnforcedLeray.Short.IIIa

/-! ## Measurability -/

theorem measurable_kerD' (d : ℝ) (k : Fin 2) : Measurable (fun z => kerD d z k) :=
  ((PiLp.continuous_apply 2 _ k).measurable).comp (UnforcedLeray.Cyl.measurable_bsKernel d)

theorem stronglyMeasurable_kerVelCx' (d : ℝ) {W : ℝ × ℝ → ℂ} (hW : StronglyMeasurable W)
    (k : Fin 2) : StronglyMeasurable (fun y => kerVelCx d W y k) := by
  unfold kerVelCx
  have hk : StronglyMeasurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      ((kerD d (p.1 - p.2) k : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.measurable.comp
      ((measurable_kerD' d k).comp (measurable_fst.sub measurable_snd))).stronglyMeasurable
  have hprod : StronglyMeasurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      W p.2 * ((kerD d (p.1 - p.2) k : ℝ) : ℂ)) :=
    (hW.comp_measurable measurable_snd).mul hk
  exact hprod.integral_prod_right'

/-! ## Biot-Savart velocity of tests -/

theorem meanShear_zero (c : ℝ) (x : ℝ × ℝ) (j : Fin 2) : meanShear c 0 x j = 0 := by
  unfold meanShear
  split_ifs <;> simp

/-- The kernel velocity of a real zero-circulation test is its complex Biot-Savart velocity. -/
theorem isBiotSavart_kerVel_test {D : ℝ} (hD : 1 ≤ D) {a : ℝ × ℝ → ℝ}
    (ha : B0579.IsCylTest D a) (ha0 : ∫ x in B0579.cell D, a x = 0) :
    IsBiotSavart D (fun x => ((a x : ℝ) : ℂ)) (fun x j => ((kerVel D a x j : ℝ) : ℂ)) := by
  obtain ⟨h1, h2, h3⟩ := kerVelIsBS D hD a ha
  refine ⟨fun j => ?_, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · have h := h1 j
    rw [ha0] at h
    simp only [meanShear_zero, sub_zero] at h
    exact h.ofReal
  · have e := h2 φ hφ
    have hfun : (fun x => ((kerVel D a x 0 : ℝ) : ℂ) * ((B0579.pd 0 φ x : ℝ) : ℂ) +
        ((kerVel D a x 1 : ℝ) : ℂ) * ((B0579.pd 1 φ x : ℝ) : ℂ)) = fun x =>
        (((kerVel D a x 0 * B0579.pd 0 φ x + kerVel D a x 1 * B0579.pd 1 φ x : ℝ)) : ℂ) := by
      funext x
      push_cast
      ring
    show ∫ x in B0579.cell D, (((kerVel D a x 0 : ℝ) : ℂ) * ((B0579.pd 0 φ x : ℝ) : ℂ) +
        ((kerVel D a x 1 : ℝ) : ℂ) * ((B0579.pd 1 φ x : ℝ) : ℂ)) = 0
    rw [hfun, integral_complex_ofReal, e]
    simp
  · have e := h3 φ hφ
    have hl : (fun x => ((a x : ℝ) : ℂ) * ((φ x : ℝ) : ℂ)) = fun x => ((a x * φ x : ℝ) : ℂ) := by
      funext x
      push_cast
      ring
    have hr : (fun x => ((kerVel D a x 0 : ℝ) : ℂ) * ((B0579.pd 1 φ x : ℝ) : ℂ) -
        ((kerVel D a x 1 : ℝ) : ℂ) * ((B0579.pd 0 φ x : ℝ) : ℂ)) = fun x =>
        (((kerVel D a x 0 * B0579.pd 1 φ x - kerVel D a x 1 * B0579.pd 0 φ x : ℝ)) : ℂ) := by
      funext x
      push_cast
      ring
    show ∫ x in B0579.cell D, ((a x : ℝ) : ℂ) * ((φ x : ℝ) : ℂ) =
      ∫ x in B0579.cell D, (((kerVel D a x 0 : ℝ) : ℂ) * ((B0579.pd 1 φ x : ℝ) : ℂ) -
        ((kerVel D a x 1 : ℝ) : ℂ) * ((B0579.pd 0 φ x : ℝ) : ℂ))
    rw [hl, hr, integral_complex_ofReal, integral_complex_ofReal, e]

/-- The complex combination `a + i b` of two real zero-circulation tests. -/
theorem isBiotSavart_test_pair {D m : ℝ} (hD : 1 ≤ D) (hm : 1 < m) {a b : ℝ × ℝ → ℝ}
    (ha : B0579.IsCylTest D a) (hb : B0579.IsCylTest D b)
    (ha0 : ∫ x in B0579.cell D, a x = 0) (hb0 : ∫ x in B0579.cell D, b x = 0) :
    IsBiotSavart D (fun x => ((a x : ℝ) : ℂ) + Complex.I * ((b x : ℝ) : ℂ))
      (fun x j => ((kerVel D a x j : ℝ) : ℂ) + Complex.I * ((kerVel D b x j : ℝ) : ℂ)) := by
  have hA := isBiotSavart_kerVel_test hD ha ha0
  have hB := TranspApproxAux.isBiotSavart_smul (-Complex.I) (isBiotSavart_kerVel_test hD hb hb0)
  have hmA : MemLp (fun x => ((a x : ℝ) : ℂ)) 2 (B0579.cellMeasure D m) :=
    (ha.memLp m).ofReal
  have hmB : MemLp (fun x => -Complex.I * ((b x : ℝ) : ℂ)) 2 (B0579.cellMeasure D m) :=
    (hb.memLp m).ofReal.const_mul _
  have h := ladBSSub m D _ _ _ _ hm hmA hmB hA hB
  have e1 : ((fun x => ((a x : ℝ) : ℂ)) - fun x => -Complex.I * ((b x : ℝ) : ℂ)) =
      fun x => ((a x : ℝ) : ℂ) + Complex.I * ((b x : ℝ) : ℂ) := by
    funext x
    simp only [Pi.sub_apply]
    ring
  have e2 : ((fun x j => ((kerVel D a x j : ℝ) : ℂ)) -
      fun x j => -Complex.I * ((kerVel D b x j : ℝ) : ℂ)) =
      fun x j => ((kerVel D a x j : ℝ) : ℂ) + Complex.I * ((kerVel D b x j : ℝ) : ℂ) := by
    funext x j
    simp only [Pi.sub_apply]
    ring
  rw [e1, e2] at h
  exact h

/-- Pointwise (a.e.) splitting of the complex kernel velocity of `a + i b`. -/
theorem kerVelCx_pair_ae {D m : ℝ} (hD : 1 ≤ D) (hm : 1 < m) {a b : ℝ × ℝ → ℝ}
    (ha : B0579.IsCylTest D a) (hb : B0579.IsCylTest D b) :
    ∀ᵐ x ∂(volume.restrict (B0579.cell D)), ∀ j : Fin 2,
      kerVelCx D (fun z => ((a z : ℝ) : ℂ) + Complex.I * ((b z : ℝ) : ℂ)) x j =
        ((kerVel D a x j : ℝ) : ℂ) + Complex.I * ((kerVel D b x j : ℝ) : ℂ) := by
  have hA := BlockPropagatorInteriorSub.OrgSplit.RelIntA.ae_integrableOn_kerVelCx hD hm
    ((ha.memLp m).ofReal (K := ℂ))
  have hB := BlockPropagatorInteriorSub.OrgSplit.RelIntA.ae_integrableOn_kerVelCx hD hm
    ((hb.memLp m).ofReal (K := ℂ))
  filter_upwards [hA, hB] with x hxA hxB j
  unfold kerVelCx kerVel
  have hA' := hxA j
  have hB' := (hxB j).const_mul Complex.I
  have hsplit : (fun z => (((a z : ℝ) : ℂ) + Complex.I * ((b z : ℝ) : ℂ)) *
      ((kerD D (x - z) j : ℝ) : ℂ)) = fun z => ((a z : ℝ) : ℂ) * ((kerD D (x - z) j : ℝ) : ℂ) +
        Complex.I * (((b z : ℝ) : ℂ) * ((kerD D (x - z) j : ℝ) : ℂ)) := by
    funext z
    ring
  have e := integral_add hA' hB'
  have ea : ∫ z in B0579.cell D, ((a z : ℝ) : ℂ) * ((kerD D (x - z) j : ℝ) : ℂ) =
      ((∫ z in B0579.cell D, a z * kerD D (x - z) j : ℝ) : ℂ) := by
    have h1 : (fun z => ((a z : ℝ) : ℂ) * ((kerD D (x - z) j : ℝ) : ℂ)) =
        fun z => ((a z * kerD D (x - z) j : ℝ) : ℂ) := by
      funext z
      push_cast
      ring
    rw [h1, integral_complex_ofReal]
  have eb : ∫ z in B0579.cell D, ((b z : ℝ) : ℂ) * ((kerD D (x - z) j : ℝ) : ℂ) =
      ((∫ z in B0579.cell D, b z * kerD D (x - z) j : ℝ) : ℂ) := by
    have h1 : (fun z => ((b z : ℝ) : ℂ) * ((kerD D (x - z) j : ℝ) : ℂ)) =
        fun z => ((b z * kerD D (x - z) j : ℝ) : ℂ) := by
      funext z
      push_cast
      ring
    rw [h1, integral_complex_ofReal]
  rw [hsplit]
  refine e.trans ?_
  rw [integral_const_mul]
  exact congrArg₂ (fun u v => u + Complex.I * v) ea eb

/-- The complex kernel velocity of a complex zero-circulation test is a Biot-Savart velocity. -/
theorem isBiotSavart_kerVelCx_pair {D m : ℝ} (hD : 1 ≤ D) (hm : 1 < m) {a b : ℝ × ℝ → ℝ}
    (ha : B0579.IsCylTest D a) (hb : B0579.IsCylTest D b)
    (ha0 : ∫ x in B0579.cell D, a x = 0) (hb0 : ∫ x in B0579.cell D, b x = 0) :
    IsBiotSavart D (fun x => ((a x : ℝ) : ℂ) + Complex.I * ((b x : ℝ) : ℂ))
      (kerVelCx D (fun z => ((a z : ℝ) : ℂ) + Complex.I * ((b z : ℝ) : ℂ))) := by
  refine KernelVelAux.bs_congr_u (isBiotSavart_test_pair hD hm ha hb ha0 hb0) ?_
  filter_upwards [kerVelCx_pair_ae hD hm ha hb] with x hx
  funext j
  exact (hx j).symm

/-! ## The `L¹` bounds on a band -/

/-- The band `[-D/2, D/2) × [-R, R]` of the cell. -/
def band (D R : ℝ) : Set (ℝ × ℝ) := Ico (-(D / 2)) (D / 2) ×ˢ Icc (-R) R

theorem band_subset_cell (D R : ℝ) : band D R ⊆ B0579.cell D :=
  fun _ hx => ⟨hx.1, mem_univ _⟩

theorem measurableSet_band (D R : ℝ) : MeasurableSet (band D R) :=
  measurableSet_Ico.prod measurableSet_Icc

theorem volume_band_lt_top (D R : ℝ) : volume (band D R) < ∞ := by
  rw [band, Measure.volume_eq_prod, Measure.prod_prod]
  exact ENNReal.mul_lt_top measure_Ico_lt_top measure_Icc_lt_top

theorem iUnion_band (D : ℝ) : (⋃ n : ℕ, band D n) = B0579.cell D := by
  ext x
  simp only [mem_iUnion, band, B0579.cell, mem_prod, mem_univ, and_true, mem_Icc]
  constructor
  · rintro ⟨n, h, -⟩
    exact h
  · intro h
    obtain ⟨n, hn⟩ := exists_nat_ge |x.2|
    exact ⟨n, h, by linarith [neg_abs_le x.2], by linarith [le_abs_self x.2]⟩

/-- Uniform `L¹` bound of the translated kernel on a band. -/
theorem lintegral_band_kerD_le {D : ℝ} (hD : 1 ≤ D) (R : ℝ) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (z : ℝ × ℝ) (k : Fin 2),
      ∫⁻ y in band D R, ‖kerD D (y - z) k‖ₑ ≤ C := by
  obtain ⟨Cn, -, hsplit⟩ := UnforcedLeray.Cyl.bsKernel_split
  have hD0 : 0 < D := by linarith
  obtain ⟨hnear, hfar, heq⟩ := hsplit D hD
  refine ⟨ENNReal.ofReal Cn + 2 * volume (band D R), ?_, fun z k => ?_⟩
  · exact ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top,
      ENNReal.mul_lt_top (by norm_num) (volume_band_lt_top D R)⟩
  set G : ℝ × ℝ → ℝ≥0∞ := fun w => ‖UnforcedLeray.Cyl.kNear D (IIb.wrapPlane D w)‖ₑ with hG
  have hpt : ∀ y, ‖kerD D (y - z) k‖ₑ ≤ G (y - z) + 2 := by
    intro y
    have h1 : |kerD D (y - z) k| ≤ ‖UnforcedLeray.Cyl.bsKernel D (y - z)‖ :=
      BlockPropagatorInteriorSub.OrgSplit.RelIntA.abs_kerD_le D (y - z) k
    have hw : IIb.wrapPlane D (y - z) ∈ UnforcedLeray.Cyl.cell D := by
      rw [← IIb.cell_eq_cylCell]
      exact IIb.wrapPlane_mem_cell hD0 (y - z)
    have h2 : UnforcedLeray.Cyl.bsKernel D (y - z) =
        UnforcedLeray.Cyl.kNear D (IIb.wrapPlane D (y - z)) +
          UnforcedLeray.Cyl.kFar D (IIb.wrapPlane D (y - z)) := by
      rw [← IIb.bsKernel_wrapPlane D (y - z)]
      exact heq _ hw
    have h3 : ‖UnforcedLeray.Cyl.bsKernel D (y - z)‖ ≤
        ‖UnforcedLeray.Cyl.kNear D (IIb.wrapPlane D (y - z))‖ + 2 := by
      rw [h2]
      exact (norm_add_le _ _).trans (by linarith [hfar (IIb.wrapPlane D (y - z))])
    rw [← ofReal_norm, Real.norm_eq_abs]
    calc ENNReal.ofReal |kerD D (y - z) k|
        ≤ ENNReal.ofReal (‖UnforcedLeray.Cyl.kNear D (IIb.wrapPlane D (y - z))‖ + 2) :=
          ENNReal.ofReal_le_ofReal (h1.trans h3)
      _ = G (y - z) + 2 := by
          rw [ENNReal.ofReal_add (norm_nonneg _) (by norm_num), ofReal_norm]
          simp [hG]
  have hGper : UnforcedLeray.Cyl.IsPeriodic D G := by
    intro w
    simp only [hG]
    rw [IIb.isPeriodic_wrapPlane hD0 w]
  have hGmeas : Measurable G :=
    ((UnforcedLeray.Cyl.measurable_bsKernel D).indicator
      ((UnforcedLeray.Cyl.measurableSet_cell D).inter
        Metric.isOpen_ball.measurableSet)).enorm.comp (IIb.measurable_wrapPlane D)
  have htrans : ∫⁻ y in B0579.cell D, G (y - z) = ∫⁻ y in B0579.cell D, G y := by
    rw [IIb.cell_eq_cylCell]
    have := UnforcedLeray.Cyl.lintegral_cell_comp_add hD0 hGper (-z)
    simpa [sub_eq_add_neg] using this
  have hcell : ∫⁻ y in B0579.cell D, G y ≤ ENNReal.ofReal Cn := by
    refine le_trans (le_of_eq ?_) hnear
    rw [← IIb.cell_eq_cylCell]
    refine setLIntegral_congr_fun (B0579.measurableSet_cell D) fun y hy => ?_
    simp only [hG]
    rw [IIb.wrapPlane_of_mem_cell hD0 hy]
  calc ∫⁻ y in band D R, ‖kerD D (y - z) k‖ₑ
      ≤ ∫⁻ y in band D R, (G (y - z) + 2) := lintegral_mono hpt
    _ = (∫⁻ y in band D R, G (y - z)) + ∫⁻ _y in band D R, (2 : ℝ≥0∞) :=
        lintegral_add_right (fun y => G (y - z)) measurable_const
    _ ≤ (∫⁻ y in B0579.cell D, G (y - z)) + 2 * volume (band D R) := by
        rw [setLIntegral_const]
        gcongr
        exact band_subset_cell D R
    _ ≤ ENNReal.ofReal Cn + 2 * volume (band D R) := by
        gcongr
        exact htrans.le.trans hcell

/-- `L¹` bound of the kernel velocity on a band by the `L¹` norm of the density (Tonelli). -/
theorem lintegral_band_kerVelCx_le {D : ℝ} (hD : 1 ≤ D) (R : ℝ) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (f : ℝ × ℝ → ℂ), StronglyMeasurable f → ∀ k : Fin 2,
      ∫⁻ y in band D R, ‖kerVelCx D f y k‖ₑ ≤ C * ∫⁻ z in B0579.cell D, ‖f z‖ₑ := by
  obtain ⟨C, hC, hK⟩ := lintegral_band_kerD_le hD R
  refine ⟨C, hC, fun f hf k => ?_⟩
  calc ∫⁻ y in band D R, ‖kerVelCx D f y k‖ₑ
      ≤ ∫⁻ y in band D R, ∫⁻ z in B0579.cell D, ‖f z‖ₑ * ‖kerD D (y - z) k‖ₑ := by
        refine lintegral_mono fun y => ?_
        unfold kerVelCx
        refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
        refine lintegral_congr fun z => ?_
        rw [enorm_mul, enorm_ofReal_cx]
    _ = ∫⁻ z in B0579.cell D, ∫⁻ y in band D R, ‖f z‖ₑ * ‖kerD D (y - z) k‖ₑ := by
        refine lintegral_lintegral_swap ?_
        exact ((hf.measurable.comp measurable_snd).enorm.mul
          ((measurable_kerD' D k).comp (measurable_fst.sub measurable_snd)).enorm).aemeasurable
    _ = ∫⁻ z in B0579.cell D, ‖f z‖ₑ * ∫⁻ y in band D R, ‖kerD D (y - z) k‖ₑ := by
        refine lintegral_congr fun z => ?_
        exact lintegral_const_mul' _ _ enorm_ne_top
    _ ≤ ∫⁻ z in B0579.cell D, ‖f z‖ₑ * C :=
        lintegral_mono fun z => mul_le_mul_right (hK z k) _
    _ = C * ∫⁻ z in B0579.cell D, ‖f z‖ₑ := by
        rw [lintegral_mul_const' _ _ hC.ne, mul_comm]

/-- Weighted Cauchy-Schwarz: `∫_cell |f| ≤ C ‖f‖_{X_{m,D}}` for `m > 1`. -/
theorem lintegral_cell_le_xNorm {m : ℝ} (hm : 1 < m) (D : ℝ) : ∃ C : ℝ≥0∞, C < ∞ ∧
    ∀ f : ℝ × ℝ → ℂ, AEStronglyMeasurable f (volume.restrict (B0579.cell D)) →
      ∫⁻ z in B0579.cell D, ‖f z‖ₑ ≤ C * xNorm D m f := by
  set h : ℝ × ℝ → ℂ := fun x => ((B0579.jb x ^ (-(m / 2)) : ℝ) : ℂ) with hh_def
  have hh : MemLp h 2 (volume.restrict (B0579.cell D)) := by
    refine (memLp_two_iff_integrable_sq_norm ?_).2 ?_
    · exact (Complex.continuous_ofReal.comp
        (B0579.continuous_jb_rpow (-(m / 2)))).aestronglyMeasurable
    · refine (CellIntAux.integrable_jb_neg (c := D) hm).congr (Eventually.of_forall fun x => ?_)
      simp only [hh_def]
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _),
        ← Real.rpow_natCast, ← Real.rpow_mul (B0579.jb_pos x).le]
      congr 1
      push_cast
      ring
  refine ⟨eLpNorm h 2 (volume.restrict (B0579.cell D)), hh.eLpNorm_lt_top, fun f hf => ?_⟩
  set g : ℝ × ℝ → ℂ := fun x => ((B0579.jb x ^ (m / 2) : ℝ) : ℂ) * f x with hg_def
  have hg : AEStronglyMeasurable g (volume.restrict (B0579.cell D)) :=
    (Complex.continuous_ofReal.comp (B0579.continuous_jb_rpow (m / 2))).aestronglyMeasurable.mul hf
  have hfg : f = h • g := by
    funext x
    simp only [hh_def, hg_def, Pi.smul_apply, smul_eq_mul, Pi.mul_apply]
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add (B0579.jb_pos x),
      show -(m / 2) + m / 2 = (0 : ℝ) by ring, Real.rpow_zero, Complex.ofReal_one, one_mul]
  have key := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1) hg hh.aestronglyMeasurable
  rw [← hfg, eLpNorm_one_eq_lintegral_enorm] at key
  unfold xNorm
  rw [eLpNorm_cellMeasure_cx]
  exact key

end UnforcedLeray.Short.IIIa.ComplFreeRateSub.Leaf2WeakEqFrame.KerBSAux
