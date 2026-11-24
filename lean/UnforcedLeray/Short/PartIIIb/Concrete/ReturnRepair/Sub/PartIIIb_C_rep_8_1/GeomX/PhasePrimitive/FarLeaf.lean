import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive.Leaf
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive.FarLeafOrg.Pointwise
import UnforcedLeray.Short.PartIIIa.T17_SepMeanComparison.MomentSplit

/-!
# `SepOscFar` (task `PartIII-b:C/rep/8/1/1/1/2/1`)

Source `the November 2 reference manuscript`
lines 5400-5427, 3768-3790.

Assembly of `SepOscFar` from `FarLeafOrg.oscFarPt` and `IIIa.sepMomentSplit`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray UnforcedLeray.Short.IIIa
open UnforcedLeray.Short.PartIIIb.Concrete.FarLeafOrg

private lemma sepDiffF_thin_split (ν ε c : ℝ) (μ : ℂ)
    (F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (p : ℝ × Space) :
    sepDiffF ν μ (thinSource ε F) τ p =
      sepDiffF ν μ (thinSource ε (meanLift (IIIa.phaseMean c F))) τ p +
        sepDiffF ν μ (thinSource ε (perpPart c F)) τ p := by
  ext y' i
  have hthin : ∀ σ z, thinSource ε F σ z =
      thinSource ε (meanLift (IIIa.phaseMean c F)) σ z + thinSource ε (perpPart c F) σ z := by
    intro σ z
    unfold thinSource meanLift perpPart
    simp
  simp only [sepDiffF, Pi.add_apply, hthin]
  simp only [Matrix.add_apply, Complex.ofReal_add, mul_add, Finset.sum_add_distrib]

private lemma fderiv_sepW_thin_split {ν c ε ρo ρi : ℝ} {μ : ℂ}
    (hν : 0 < ν) (hc : 0 < c) (hε : 0 < ε) (hρo : 0 ≤ ρo) (hρ : ρo < ρi)
    (hμ : -(1 / 4) < μ.re) {F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hth : ThinHyp c ρo F) (hth1 : ThinHyp c ρo (meanLift (IIIa.phaseMean c F)))
    (hth2 : ThinHyp c ρo (perpPart c F))
    (hN : thinMoment c F ≠ ⊤) (hN1 : thinMoment c (meanLift (IIIa.phaseMean c F)) ≠ ⊤)
    (hN2 : thinMoment c (perpPart c F) ≠ ⊤)
    {xo : Space} (hxo : ρi ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2)) (τ : ℝ) :
    fderiv ℝ (fun y => sepW ν μ (thinSource ε F) y τ) (ε⁻¹ • xo) -
        fderiv ℝ (fun y => sepW ν μ (thinSource ε (meanLift (IIIa.phaseMean c F))) y τ) (ε⁻¹ • xo) =
      fderiv ℝ (fun y => sepW ν μ (thinSource ε (perpPart c F)) y τ) (ε⁻¹ • xo) := by
  set y0 : Space := ε⁻¹ • xo
  have hy0 : ρi / ε ≤ Real.sqrt (y0 0 ^ 2 + y0 1 ^ 2) := by
    change ρi / ε ≤ hor (ε⁻¹ • xo)
    rw [hor_smul _ (inv_nonneg.2 hε.le), div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hxo (inv_nonneg.2 hε.le)
  have hP : 0 < 2 * ε * c := by positivity
  obtain ⟨hInt0, hHas0⟩ := fderiv_sepW_of hν (div_nonneg hρo hε.le)
    (div_lt_div_of_pos_right hρ hε) hP (thin_isSep hε hth) τ y0 hy0
    (sepDom_thin_lt_top hε hc hρ hμ hth hN τ y0)
  obtain ⟨hInt1, hHas1⟩ := fderiv_sepW_of hν (div_nonneg hρo hε.le)
    (div_lt_div_of_pos_right hρ hε) hP (thin_isSep hε hth1) τ y0 hy0
    (sepDom_thin_lt_top hε hc hρ hμ hth1 hN1 τ y0)
  obtain ⟨hInt2, hHas2⟩ := fderiv_sepW_of hν (div_nonneg hρo hε.le)
    (div_lt_div_of_pos_right hρ hε) hP (thin_isSep hε hth2) τ y0 hy0
    (sepDom_thin_lt_top hε hc hρ hμ hth2 hN2 τ y0)
  rw [hHas0.fderiv, hHas1.fderiv, hHas2.fderiv]
  have hae : ∀ᵐ p ∂sepDiffRho,
      fderiv ℝ (sepDiffF ν μ (thinSource ε F) τ p) y0 =
        fderiv ℝ (sepDiffF ν μ (thinSource ε (meanLift (IIIa.phaseMean c F))) τ p) y0 +
          fderiv ℝ (sepDiffF ν μ (thinSource ε (perpPart c F)) τ p) y0 := by
    filter_upwards [sepDiffRho_ae_mem] with p hp
    have hd1 : DifferentiableAt ℝ
        (sepDiffF ν μ (thinSource ε (meanLift (IIIa.phaseMean c F))) τ p) y0 :=
      ((contDiff_pi.2 (sepDiffF_contDiff heatLerayKSmoothAll ν μ _ τ hν p hp)).differentiable
        (by simp)) y0
    have hd2 : DifferentiableAt ℝ
        (sepDiffF ν μ (thinSource ε (perpPart c F)) τ p) y0 :=
      ((contDiff_pi.2 (sepDiffF_contDiff heatLerayKSmoothAll ν μ _ τ hν p hp)).differentiable
        (by simp)) y0
    rw [sepDiffF_thin_split ν ε c μ F τ p]
    exact (hd1.hasFDerivAt.add hd2.hasFDerivAt).fderiv
  rw [integral_congr_ae hae, integral_add hInt1 hInt2, add_sub_cancel_left]

theorem sepOscFar : SepOscFar := by
  intro K hK hRe
  obtain ⟨C₀, k, hC₀, hOsc⟩ := oscFarPt K hK hRe
  refine ⟨2 * C₀, k, by positivity, ?_⟩
  intro ν c ε ρo ρi hν hν1 hc hε hε1 hρo hρ μ hμ F hmeas hper hsupp hN xo hxo
  have hth : ThinHyp c ρo F := ⟨hmeas, hper, hsupp⟩
  obtain ⟨hm1, hm2⟩ := sepMomentSplit c hc F hmeas
  have hN1 : thinMoment c (meanLift (IIIa.phaseMean c F)) ≠ ⊤ :=
    ne_top_of_le_ne_top hN hm1
  have hN2 : thinMoment c (perpPart c F) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp) hN) hm2
  have hGm : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => IIIa.phaseMean c F w.1 w.2 i j :=
    phaseMean_measurable c F hmeas
  have hGs : ∀ x' Y, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → IIIa.phaseMean c F x' Y = 0 := by
    intro x' Y h
    funext i j
    simp [IIIa.phaseMean, hsupp x' Y _ h]
  have hth1 : ThinHyp c ρo (meanLift (IIIa.phaseMean c F)) :=
    ⟨fun i j => (hGm i j).comp (f := fun w : (ℝ × ℝ) × ℝ × ℝ => (w.1, w.2.1)) (by fun_prop),
     fun _ _ _ => rfl,
     fun x' Y _ h => hGs x' Y h⟩
  have hth2 : ThinHyp c ρo (perpPart c F) :=
    ⟨fun i j => (hmeas i j).sub
       ((hGm i j).comp (f := fun w : (ℝ × ℝ) × ℝ × ℝ => (w.1, w.2.1)) (by fun_prop)),
     fun x' Y q => by simp [perpPart, hper],
     fun x' Y q h => by simp [perpPart, hsupp x' Y q h, hGs x' Y h]⟩
  set b : ℝ := 1 + ν⁻¹ + c + ρi⁻¹ + ρi * (ρi - ρo)⁻¹
  set r : ℝ := Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2)
  have hρi : 0 < ρi := lt_of_le_of_lt hρo hρ
  have hrpos : 0 < r := lt_of_lt_of_le hρi hxo
  have hb0 : 0 ≤ b := by
    have : 0 ≤ ρi * (ρi - ρo)⁻¹ := mul_nonneg hρi.le (inv_nonneg.2 (by linarith))
    positivity
  set a : ℝ≥0∞ := ENNReal.ofReal (2 * C₀ * b ^ k * ε ^ 4 * r ^ (-5 : ℝ)) * thinMoment c F
  refine ⟨fun _ => a, measurable_const, fun _ => rfl, ?_, ?_⟩
  · refine Eventually.of_forall fun τ => ?_
    rw [fderiv_sepW_thin_split hν hc hε hρo hρ (hRe μ hμ) hth hth1 hth2 hN hN1 hN2 hxo τ]
    have hpt := hOsc ν c ε ρo ρi hν hν1 hc hε hε1 hρo hρ μ hμ (perpPart c F)
      hth2.meas hth2.per hth2.supp (perpPart_meanZero c hc F) hN2 xo hxo τ
    calc ‖fderiv ℝ (fun y => sepW ν μ (thinSource ε (perpPart c F)) y τ) (ε⁻¹ • xo)‖ₑ
        ≤ ENNReal.ofReal (C₀ * b ^ k * ε ^ 4 * r ^ (-5 : ℝ)) * thinMoment c (perpPart c F) := hpt
      _ ≤ ENNReal.ofReal (C₀ * b ^ k * ε ^ 4 * r ^ (-5 : ℝ)) * (2 * thinMoment c F) :=
          mul_le_mul_right hm2 _
      _ = a := by
          have hc0 : 0 ≤ C₀ * b ^ k * ε ^ 4 * r ^ (-5 : ℝ) := by positivity
          have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by norm_num
          rw [← mul_assoc, h2, ← ENNReal.ofReal_mul hc0]
          congr 2
          ring
  · have hP : 0 < 2 * ε * c := by positivity
    exact (ltauAt_const (2 * ε * c) hP a).le

end UnforcedLeray.Short.PartIIIb.Concrete
end
