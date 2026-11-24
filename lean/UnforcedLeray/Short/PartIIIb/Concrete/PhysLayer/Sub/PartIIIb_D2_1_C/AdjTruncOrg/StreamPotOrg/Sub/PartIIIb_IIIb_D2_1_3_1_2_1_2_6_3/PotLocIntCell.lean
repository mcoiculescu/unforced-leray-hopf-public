import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6_3.PotMeasPeriodic
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.BsCutoff
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.BsTestConvBound
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.BsPairIntegrable

/-!
# `PotLocIntCell`

`bsPot Φ` is integrable on `[0,P] × B_R` for `Φ ∈ Y_2`.

Route. Replace `Φ` by a measurable version `Ψ` (equal a.e.; `bsPot Φ = bsPot Ψ` a.e.).
Pointwise `‖bsPot Ψ (t,y)‖ₑ ≤ 4 ∫ ‖Ψ(t,z)‖ₑ ‖K(y-z)‖ₑ dz`. Tonelli over the cell, then
`∫_{B_R} ‖K(y-z)‖ₑ dy ≤ C (1+|z|²)⁻¹` (`bsTestConvBound` with the cutoff `bsCut (|R|+1)`, which is
`1` on `B_R`). Finally `∫_{[0,P]} ∫ ‖Ψ‖ (1+|z|²)⁻¹` is finite by Hölder (`Φ ∈ L²`, decay in `L²`).
Source `the November 2 reference manuscript` lines 1351-1362 and 1334-1337.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

set_option maxHeartbeats 1000000 in
theorem potLocIntCell : PotLocIntCell := by
  intro P hP Φ hΦ R
  -- a measurable version of Φ
  set Ψ : ℝ × Space → CVec3 := hΦ.meas.mk Φ with hΨdef
  have hΨm : Measurable Ψ := hΦ.meas.stronglyMeasurable_mk.measurable
  have hΦΨ : ∀ᵐ x : ℝ × Space, Φ x = Ψ x := hΦ.meas.ae_eq_mk
  rw [Measure.volume_eq_prod] at hΦΨ
  have hTr2 : ∀ᵐ t : ℝ, ∀ᵐ y : Space, Φ (t, y) = Ψ (t, y) := Measure.ae_ae_of_ae_prod hΦΨ
  have hTr : ∀ᵐ x : ℝ × Space, bsPot Φ x = bsPot Ψ x := by
    have h2 : ∀ᵐ x : ℝ × Space, ∀ᵐ z : Space, Φ (x.1, z) = Ψ (x.1, z) :=
      (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ))
        (ν := (volume : Measure Space))).ae hTr2
    filter_upwards [h2] with x hx
    unfold bsPot
    refine integral_congr_ae ?_
    filter_upwards [hx] with z hz
    simp only [hz]
  have hTN : ∀ᵐ x : ℝ × Space, ‖bsPot Φ x‖ₑ = ‖bsPot Ψ x‖ₑ := by
    filter_upwards [hTr] with x hx
    rw [hx]
  -- finiteness of the phase L² integral of Φ and Ψ over one period
  have hfinΦ : ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ‖Φ (t, y)‖ₑ ^ (2 : ℝ) < ⊤ := by
    have h := hΦ.finite
    unfold UnforcedLeray.Short.IIb.phaseLpNorm at h
    rw [ENNReal.rpow_lt_top_iff_of_pos (by norm_num)] at h
    rcases ENNReal.mul_lt_top_iff.1 h with ⟨_, h2⟩ | h2 | h2
    · exact h2
    · exact absurd h2 (ENNReal.ofReal_pos.2 (inv_pos.2 hP)).ne'
    · rw [h2]
      exact ENNReal.zero_lt_top
  have hfinΨ : ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ‖Ψ (t, y)‖ₑ ^ (2 : ℝ) < ⊤ := by
    have heq : (∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ‖Ψ (t, y)‖ₑ ^ (2 : ℝ)) =
        ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ‖Φ (t, y)‖ₑ ^ (2 : ℝ) := by
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae hTr2] with t ht
      refine lintegral_congr_ae ?_
      filter_upwards [ht] with y hy
      rw [hy]
    rw [heq]
    exact hfinΦ
  -- the cutoff and the decay constant
  have hR'pos : (0 : ℝ) < |R| + 1 := by positivity
  obtain ⟨C, hC⟩ := bsTestConvBound (bsCut (|R| + 1))
    (bsCut_contDiff (|R| + 1)).continuous (bsCut_hasCompactSupport hR'pos)
  -- measurability facts
  have hKm : Measurable (fun w : Space => ‖bsKernel w‖ₑ) := potMeas_measurable_bsKernel.enorm
  have hΨe : Measurable (fun p : ℝ × Space => ‖Ψ p‖ₑ) := hΨm.enorm
  have hw : Measurable (fun z : Space => (1 + ‖z‖ ^ 2)⁻¹) :=
    (measurable_const.add (measurable_norm.pow_const 2)).inv
  have hGm : Measurable (fun z : Space => ENNReal.ofReal |C| * ‖(1 + ‖z‖ ^ 2)⁻¹‖ₑ) :=
    measurable_const.mul hw.enorm
  have hGne : ∀ z : Space, ENNReal.ofReal |C| * ‖(1 + ‖z‖ ^ 2)⁻¹‖ₑ ≠ ⊤ := fun z =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top enorm_ne_top
  -- the kernel integral over the ball
  have hKint : ∀ z : Space, ∫⁻ y in closedBall (0 : Space) R, ‖bsKernel (y - z)‖ₑ ≤
      ENNReal.ofReal |C| * ‖(1 + ‖z‖ ^ 2)⁻¹‖ₑ := by
    intro z
    have hI := hC z
    have hnn : 0 ≤ᵐ[volume] (fun y : Space => ‖bsCut (|R| + 1) y‖ * ‖bsKernel (y - z)‖) :=
      Eventually.of_forall fun y => by positivity
    have hGeq : ENNReal.ofReal (|C| * (1 + ‖z‖ ^ 2)⁻¹) =
        ENNReal.ofReal |C| * ‖(1 + ‖z‖ ^ 2)⁻¹‖ₑ := by
      rw [ENNReal.ofReal_mul (abs_nonneg C), ← ofReal_norm,
        Real.norm_of_nonneg (show (0 : ℝ) ≤ (1 + ‖z‖ ^ 2)⁻¹ by positivity)]
    calc ∫⁻ y in closedBall (0 : Space) R, ‖bsKernel (y - z)‖ₑ
        ≤ ∫⁻ y in closedBall (0 : Space) R,
            ENNReal.ofReal (‖bsCut (|R| + 1) y‖ * ‖bsKernel (y - z)‖) := by
          refine setLIntegral_mono' measurableSet_closedBall (fun y hy => ?_)
          have hy' : ‖y‖ ≤ |R| + 1 :=
            (mem_closedBall_zero_iff.1 hy).trans (by linarith [le_abs_self R])
          rw [bsCut_one hR'pos hy', norm_one, one_mul, ofReal_norm]
      _ ≤ ∫⁻ y, ENNReal.ofReal (‖bsCut (|R| + 1) y‖ * ‖bsKernel (y - z)‖) :=
          setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (∫ y, ‖bsCut (|R| + 1) y‖ * ‖bsKernel (y - z)‖) :=
          (ofReal_integral_eq_lintegral_ofReal hI.1 hnn).symm
      _ ≤ ENNReal.ofReal (|C| * (1 + ‖z‖ ^ 2)⁻¹) :=
          ENNReal.ofReal_le_ofReal
            (hI.2.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)))
      _ = ENNReal.ofReal |C| * ‖(1 + ‖z‖ ^ 2)⁻¹‖ₑ := hGeq
  -- the decay weight has finite L² integral
  have hwL : ∫⁻ z : Space, ‖(1 + ‖z‖ ^ 2)⁻¹‖ₑ ^ (2 : ℝ) < ⊤ := by
    have h := bsDecay_memLp.eLpNorm_lt_top
    rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)] at h
    simp only [ENNReal.toReal_ofNat] at h
    rwa [ENNReal.rpow_lt_top_iff_of_pos (by norm_num)] at h
  have hGL : ∫⁻ z : Space, (ENNReal.ofReal |C| * ‖(1 + ‖z‖ ^ 2)⁻¹‖ₑ) ^ (2 : ℝ) < ⊤ := by
    have hc : ENNReal.ofReal |C| ^ (2 : ℝ) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
    have heq : (fun z : Space => (ENNReal.ofReal |C| * ‖(1 + ‖z‖ ^ 2)⁻¹‖ₑ) ^ (2 : ℝ)) =
        fun z : Space => ENNReal.ofReal |C| ^ (2 : ℝ) * ‖(1 + ‖z‖ ^ 2)⁻¹‖ₑ ^ (2 : ℝ) :=
      funext fun z => ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
    rw [heq, lintegral_const_mul' _ _ hc]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hc) hwL
  -- pointwise bound on the kernel integral of bsPot Ψ
  have hc4 : ∀ a b : CVec3, ‖crossC a b‖ₑ ≤ ENNReal.ofReal 4 * (‖a‖ₑ * ‖b‖ₑ) := by
    intro a b
    have h := crossC_norm_le' a b
    calc ‖crossC a b‖ₑ = ENNReal.ofReal ‖crossC a b‖ := (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal (4 * ‖a‖ * ‖b‖) := ENNReal.ofReal_le_ofReal h
      _ = ENNReal.ofReal 4 * (‖a‖ₑ * ‖b‖ₑ) := by
          rw [ENNReal.ofReal_mul (p := 4 * ‖a‖) (by positivity),
            ENNReal.ofReal_mul (p := 4) (by norm_num), ofReal_norm, ofReal_norm, mul_assoc]
  have hpt : ∀ x : ℝ × Space, ‖bsPot Ψ x‖ₑ ≤
      ENNReal.ofReal 4 * ∫⁻ z : Space, ‖Ψ (x.1, z)‖ₑ * ‖bsKernel (x.2 - z)‖ₑ := by
    intro x
    unfold bsPot
    calc ‖∫ z : Space, crossC (Ψ (x.1, z)) (bsKernel (x.2 - z))‖ₑ
        ≤ ∫⁻ z : Space, ‖crossC (Ψ (x.1, z)) (bsKernel (x.2 - z))‖ₑ :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ z : Space, ENNReal.ofReal 4 * (‖Ψ (x.1, z)‖ₑ * ‖bsKernel (x.2 - z)‖ₑ) :=
          lintegral_mono fun z => hc4 _ _
      _ = ENNReal.ofReal 4 * ∫⁻ z : Space, ‖Ψ (x.1, z)‖ₑ * ‖bsKernel (x.2 - z)‖ₑ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  -- measurability of the z-swapped integrand on the cell
  have hmF : Measurable (fun q : (ℝ × Space) × Space =>
      ‖Ψ (q.1.1, q.2)‖ₑ * ‖bsKernel (q.1.2 - q.2)‖ₑ) :=
    ((hΨm.comp (measurable_fst.fst.prodMk measurable_snd)).enorm).mul
      (hKm.comp (measurable_fst.snd.sub measurable_snd))
  have hswap1 : ∫⁻ x in Ioc (0 : ℝ) P ×ˢ closedBall (0 : Space) R,
      ∫⁻ z : Space, ‖Ψ (x.1, z)‖ₑ * ‖bsKernel (x.2 - z)‖ₑ =
      ∫⁻ z : Space, ∫⁻ x in Ioc (0 : ℝ) P ×ˢ closedBall (0 : Space) R,
        ‖Ψ (x.1, z)‖ₑ * ‖bsKernel (x.2 - z)‖ₑ :=
    lintegral_lintegral_swap
      (f := fun (x : ℝ × Space) (z : Space) => ‖Ψ (x.1, z)‖ₑ * ‖bsKernel (x.2 - z)‖ₑ)
      hmF.aemeasurable
  -- product structure on the cell for fixed z
  have hsl : ∀ z : Space, ∫⁻ x in Ioc (0 : ℝ) P ×ˢ closedBall (0 : Space) R,
      ‖Ψ (x.1, z)‖ₑ * ‖bsKernel (x.2 - z)‖ₑ =
      (∫⁻ t in Ioc (0 : ℝ) P, ‖Ψ (t, z)‖ₑ) *
        ∫⁻ y in closedBall (0 : Space) R, ‖bsKernel (y - z)‖ₑ := by
    intro z
    have hm : Measurable (fun x : ℝ × Space => ‖Ψ (x.1, z)‖ₑ * ‖bsKernel (x.2 - z)‖ₑ) :=
      ((hΨm.comp (measurable_fst.prodMk measurable_const)).enorm).mul
        (hKm.comp (measurable_snd.sub measurable_const))
    have hinner : ∀ t : ℝ, ∫⁻ y in closedBall (0 : Space) R, ‖Ψ (t, z)‖ₑ * ‖bsKernel (y - z)‖ₑ
        = ‖Ψ (t, z)‖ₑ * ∫⁻ y in closedBall (0 : Space) R, ‖bsKernel (y - z)‖ₑ :=
      fun t => lintegral_const_mul _ (hKm.comp (measurable_id.sub_const z))
    rw [Measure.volume_eq_prod, setLIntegral_prod _ hm.aemeasurable]
    simp only [hinner]
    exact lintegral_mul_const _ (hΨe.comp (measurable_id.prodMk measurable_const))
  -- bound of the cell integral of bsPot Ψ
  have hB : ∫⁻ x in Ioc (0 : ℝ) P ×ˢ closedBall (0 : Space) R,
      ∫⁻ z : Space, ‖Ψ (x.1, z)‖ₑ * ‖bsKernel (x.2 - z)‖ₑ ≤
      ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ z : Space,
        ‖Ψ (t, z)‖ₑ * (ENNReal.ofReal |C| * ‖(1 + ‖z‖ ^ 2)⁻¹‖ₑ) := by
    have hm2 : Measurable (fun p : Space × ℝ =>
        ‖Ψ (p.2, p.1)‖ₑ * (ENNReal.ofReal |C| * ‖(1 + ‖p.1‖ ^ 2)⁻¹‖ₑ)) :=
      (hΨe.comp (measurable_snd.prodMk measurable_fst)).mul
        (measurable_const.mul (hw.enorm.comp measurable_fst))
    rw [hswap1]
    calc ∫⁻ z : Space, ∫⁻ x in Ioc (0 : ℝ) P ×ˢ closedBall (0 : Space) R,
          ‖Ψ (x.1, z)‖ₑ * ‖bsKernel (x.2 - z)‖ₑ
        = ∫⁻ z : Space, (∫⁻ t in Ioc (0 : ℝ) P, ‖Ψ (t, z)‖ₑ) *
            ∫⁻ y in closedBall (0 : Space) R, ‖bsKernel (y - z)‖ₑ :=
          lintegral_congr hsl
      _ ≤ ∫⁻ z : Space, (∫⁻ t in Ioc (0 : ℝ) P, ‖Ψ (t, z)‖ₑ) *
            (ENNReal.ofReal |C| * ‖(1 + ‖z‖ ^ 2)⁻¹‖ₑ) :=
          lintegral_mono fun z => mul_le_mul' le_rfl (hKint z)
      _ = ∫⁻ z : Space, ∫⁻ t in Ioc (0 : ℝ) P,
            ‖Ψ (t, z)‖ₑ * (ENNReal.ofReal |C| * ‖(1 + ‖z‖ ^ 2)⁻¹‖ₑ) :=
          lintegral_congr fun z => (lintegral_mul_const' _ _ (hGne z)).symm
      _ = ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ z : Space,
            ‖Ψ (t, z)‖ₑ * (ENNReal.ofReal |C| * ‖(1 + ‖z‖ ^ 2)⁻¹‖ₑ) :=
          lintegral_lintegral_swap (f := fun (z : Space) (t : ℝ) =>
            ‖Ψ (t, z)‖ₑ * (ENNReal.ofReal |C| * ‖(1 + ‖z‖ ^ 2)⁻¹‖ₑ)) hm2.aemeasurable
  -- finiteness of the weighted phase integral (Cauchy-Schwarz on the product)
  have hfinal : ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ z : Space,
      ‖Ψ (t, z)‖ₑ * (ENNReal.ofReal |C| * ‖(1 + ‖z‖ ^ 2)⁻¹‖ₑ) < ⊤ := by
    have hm5 : Measurable (fun p : ℝ × Space =>
        ‖Ψ p‖ₑ * (ENNReal.ofReal |C| * ‖(1 + ‖p.2‖ ^ 2)⁻¹‖ₑ)) :=
      hΨe.mul (hGm.comp measurable_snd)
    have hfp : ∫⁻ p, ‖Ψ p‖ₑ * (ENNReal.ofReal |C| * ‖(1 + ‖p.2‖ ^ 2)⁻¹‖ₑ)
        ∂((volume.restrict (Ioc (0 : ℝ) P)).prod (volume : Measure Space)) =
        ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ z : Space,
          ‖Ψ (t, z)‖ₑ * (ENNReal.ofReal |C| * ‖(1 + ‖z‖ ^ 2)⁻¹‖ₑ) :=
      lintegral_prod _ hm5.aemeasurable
    rw [← hfp]
    have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq
      ((volume.restrict (Ioc (0 : ℝ) P)).prod (volume : Measure Space))
      Real.HolderConjugate.two_two
      (f := fun p : ℝ × Space => ‖Ψ p‖ₑ)
      (g := fun p : ℝ × Space => ENNReal.ofReal |C| * ‖(1 + ‖p.2‖ ^ 2)⁻¹‖ₑ)
      hΨe.aemeasurable (hGm.comp measurable_snd).aemeasurable
    have h1 : (∫⁻ p, ‖Ψ p‖ₑ ^ (2 : ℝ)
        ∂((volume.restrict (Ioc (0 : ℝ) P)).prod (volume : Measure Space))) < ⊤ := by
      rw [lintegral_prod _ (hΨe.pow_const (2 : ℝ)).aemeasurable]
      exact hfinΨ
    have h2 : (∫⁻ p, (ENNReal.ofReal |C| * ‖(1 + ‖p.2‖ ^ 2)⁻¹‖ₑ) ^ (2 : ℝ)
        ∂((volume.restrict (Ioc (0 : ℝ) P)).prod (volume : Measure Space))) < ⊤ := by
      have hG2m : Measurable (fun p : ℝ × Space =>
          (ENNReal.ofReal |C| * ‖(1 + ‖p.2‖ ^ 2)⁻¹‖ₑ) ^ (2 : ℝ)) :=
        (hGm.comp measurable_snd).pow_const (2 : ℝ)
      rw [lintegral_prod _ hG2m.aemeasurable]
      dsimp only
      rw [setLIntegral_const, Real.volume_Ioc]
      exact ENNReal.mul_lt_top hGL ENNReal.ofReal_lt_top
    refine lt_of_le_of_lt hH ?_
    exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) h1.ne)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) h2.ne)
  -- conclusion
  have hchain : ∫⁻ x in Ioc (0 : ℝ) P ×ˢ closedBall (0 : Space) R, ‖bsPot Ψ x‖ₑ < ⊤ := by
    calc ∫⁻ x in Ioc (0 : ℝ) P ×ˢ closedBall (0 : Space) R, ‖bsPot Ψ x‖ₑ
        ≤ ∫⁻ x in Ioc (0 : ℝ) P ×ˢ closedBall (0 : Space) R,
            ENNReal.ofReal 4 * ∫⁻ z : Space, ‖Ψ (x.1, z)‖ₑ * ‖bsKernel (x.2 - z)‖ₑ :=
          lintegral_mono fun x => hpt x
      _ = ENNReal.ofReal 4 * ∫⁻ x in Ioc (0 : ℝ) P ×ˢ closedBall (0 : Space) R,
            ∫⁻ z : Space, ‖Ψ (x.1, z)‖ₑ * ‖bsKernel (x.2 - z)‖ₑ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal 4 * ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ z : Space,
            ‖Ψ (t, z)‖ₑ * (ENNReal.ofReal |C| * ‖(1 + ‖z‖ ^ 2)⁻¹‖ₑ) :=
          mul_le_mul' le_rfl hB
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfinal
  -- conclusion: integrability of bsPot Φ on the cell
  unfold IntegrableOn Integrable
  refine ⟨(potMeasPeriodic P hP Φ hΦ).1.restrict, ?_⟩
  unfold HasFiniteIntegral
  rw [lintegral_congr_ae (ae_restrict_of_ae hTN)]
  exact hchain

end UnforcedLeray.Short.PartIIIb.Concrete
