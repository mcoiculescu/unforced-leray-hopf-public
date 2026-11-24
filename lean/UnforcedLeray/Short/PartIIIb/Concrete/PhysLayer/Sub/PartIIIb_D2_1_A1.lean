import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_1_1
import UnforcedLeray.Short.PartIIb.Tasks.BodyLift.Linear_4
import UnforcedLeray.Lib.AxisymmetricB.Unitary

/-!
# `fwuSubAE`: a.e. linearity of the lift along `VelG` differences (source 1580-1583, 2666-2700)

The lift `velPhys` of a `VelG`-difference is the a.e. difference of the lifts on the body measure,
transferred to `ageμ c (-3/2)` (positive density), then to `volume` on `ℝ × Space` by
`P`-periodicity in `τ` (`ae_slice`, `ae_zero_of_periodic`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem fwuA1_continuous_realC : Continuous (B0412.realC : Space → CVec3) := by
  unfold B0412.realC
  exact continuous_finsetSum _ fun i _ =>
    (Complex.continuous_ofReal.comp (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous).smul
      continuous_const

theorem fwuA1_realC_sub (x y : Space) :
    B0412.realC (x - y) = B0412.realC x - B0412.realC y := by
  ext i
  simp [B0412.realC_apply]

theorem fwuA1_velPhys_eq (R c : ℝ) (hR : R ≠ 0) (b : Chart → Merid) (x : ℝ × Space) :
    velPhys R c b x = B0412.realC ((Real.sqrt Real.pi * R) • liftFun R c b x) := by
  have h : (Real.sqrt Real.pi * R) ≠ 0 :=
    mul_ne_zero (Real.sqrt_pos.2 Real.pi_pos).ne' hR
  simp only [velPhys, liftFun, smul_smul, mul_inv_cancel₀ h, one_smul]

theorem fwuA1_velPhys_periodic {R c P : ℝ} (hR : 0 < R) (hc : 0 < c) (hP : P = 2 * c / R)
    (b : Chart → Merid) (k : ℤ) (τ : ℝ) (y : Space) :
    velPhys R c b (τ + (k : ℝ) * P, y) = velPhys R c b (τ, y) := by
  have hper : Function.Periodic (fun s => liftFun R c b (s, y)) P :=
    fun s => liftFun_add_period hR hc hP b s y
  have hk : liftFun R c b (τ + (k : ℝ) * P, y) = liftFun R c b (τ, y) :=
    hper.int_mul k τ
  rw [fwuA1_velPhys_eq R c hR.ne' b, fwuA1_velPhys_eq R c hR.ne' b, hk]

theorem fwuA1_measurable_velPhys (R c : ℝ) {b : Chart → Merid} (hb : Measurable b) :
    Measurable (velPhys R c b) :=
  fwuA1_continuous_realC.measurable.comp (measurable_Nv R (measurable_perExt c hb))

/-- The a.e. linearity of the lift on the body measure, transferred to `ageμ c (-3/2)`. -/
theorem fwuA1_ae_ageμ {c γ ν : ℝ} (b b' : VelG c γ ν) :
    ((b - b' : VelG c γ ν) : Chart → Merid) =ᵐ[ageμ c (-3 / 2)]
      ((b : Chart → Merid) - (b' : Chart → Merid)) := by
  have h0 : ((b - b' : VelG c γ ν) : Chart → Merid) =ᵐ[bodyMeasure c γ ν]
      (b : Chart → Merid) - (b' : Chart → Merid) := Lp.coeFn_sub b b'
  have hmeas : Measurable fun p : Chart =>
      ENNReal.ofReal (Real.pi * ginv γ ν p ^ 2) := by
    exact ENNReal.measurable_ofReal.comp
      (measurable_const.mul ((NearInst.gainFun_measurable γ ν).inv.pow_const 2))
  unfold bodyMeasure at h0
  have h2 := (ae_withDensity_iff hmeas).1 h0
  filter_upwards [h2] with p hp
  refine hp ?_
  have : 0 < ginv γ ν p := by
    have : 0 < NearInst.gainFun γ ν p := NearInst.gainFun_pos γ ν p
    exact inv_pos.2 this
  exact (ENNReal.ofReal_pos.2 (by positivity)).ne'

theorem fwuSubAE (c γ ν ε : ℝ) : FWUSubAE c γ ν ε := by
  intro hc hν hε b b'
  have hR : (0 : ℝ) < ε⁻¹ := inv_pos.2 hε
  have hP : 2 * ε * c = 2 * c / ε⁻¹ := by rw [div_inv_eq_mul]; ring
  have hP0 : 0 < 2 * ε * c := by positivity
  have : Fact (0 < 2 * ε * c) := ⟨hP0⟩
  have hfm : Measurable ((b - b' : VelG c γ ν) : Chart → Merid) :=
    (Lp.stronglyMeasurable _).measurable
  have hgm : Measurable (b : Chart → Merid) := (Lp.stronglyMeasurable b).measurable
  have hgm' : Measurable (b' : Chart → Merid) := (Lp.stronglyMeasurable b').measurable
  -- transfer the a.e. identity to the phase measure, through `liftFun`
  have h2 := liftFun_congr_ae hR hc hP hfm (hgm.sub hgm') (fwuA1_ae_ageμ b b')
  rw [liftFun_sub] at h2
  -- the defect of the velocity lift vanishes `phaseμ`-a.e.
  have key : ∀ᵐ x ∂(phaseμ (2 * ε * c)),
      velPhys ε⁻¹ c ((b - b' : VelG c γ ν) : Chart → Merid) x -
        (velPhys ε⁻¹ c (b : Chart → Merid) x - velPhys ε⁻¹ c (b' : Chart → Merid) x) = 0 := by
    filter_upwards [h2] with x hx
    rw [Pi.sub_apply] at hx
    simp only [fwuA1_velPhys_eq ε⁻¹ c hR.ne', hx, smul_sub, fwuA1_realC_sub, sub_self]
  have hs := ae_slice (p := fun x : ℝ × Space =>
      velPhys ε⁻¹ c ((b - b' : VelG c γ ν) : Chart → Merid) x -
        (velPhys ε⁻¹ c (b : Chart → Merid) x - velPhys ε⁻¹ c (b' : Chart → Merid) x) = 0) key
  have hDm : Measurable (fun x : ℝ × Space =>
      velPhys ε⁻¹ c ((b - b' : VelG c γ ν) : Chart → Merid) x -
        (velPhys ε⁻¹ c (b : Chart → Merid) x - velPhys ε⁻¹ c (b' : Chart → Merid) x)) :=
    (fwuA1_measurable_velPhys ε⁻¹ c hfm).sub
      ((fwuA1_measurable_velPhys ε⁻¹ c hgm).sub (fwuA1_measurable_velPhys ε⁻¹ c hgm'))
  have hper : ∀ (k : ℤ) (x : ℝ × Space),
      (fun x : ℝ × Space =>
        velPhys ε⁻¹ c ((b - b' : VelG c γ ν) : Chart → Merid) x -
          (velPhys ε⁻¹ c (b : Chart → Merid) x - velPhys ε⁻¹ c (b' : Chart → Merid) x))
        (x.1 + (k : ℝ) * (2 * ε * c), x.2) =
      (fun x : ℝ × Space =>
        velPhys ε⁻¹ c ((b - b' : VelG c γ ν) : Chart → Merid) x -
          (velPhys ε⁻¹ c (b : Chart → Merid) x - velPhys ε⁻¹ c (b' : Chart → Merid) x)) x := by
    intro k x
    obtain ⟨τ, y⟩ := x
    simp only [fwuA1_velPhys_periodic hR hc hP]
  have hz := UnforcedLeray.Short.IIb.BLRepLinAux.ae_zero_of_periodic (P := 2 * ε * c) hP0 hDm hper hs
  filter_upwards [hz] with x hx
  exact sub_eq_zero.1 hx

end UnforcedLeray.Short.PartIIIb.Concrete
