import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.WeakDmuAdd
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4
import UnforcedLeray.Cons.C07ReducedMatrix.Weak
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Agree

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest phaseCell
  pairF_eq_restrictedProductIntegral)

/-- Variant of `liftFun_congr_ae` with measurability of only the left profile (the right one is
the explicit chart representative, not known to be measurable): a measurable-null superset `N`
of the disagreement set is detected by the lift of the indicator of `N`. -/
theorem liftFun_congr_ae_left {R c P : ℝ} (hR : 0 < R) (hc : 0 < c) (hP : P = 2 * c / R)
    {b b' : ℝ × (ℝ × ℝ) → Merid} (hb : Measurable b)
    (h : b =ᵐ[ageμ c (-3 / 2)] b') : liftFun R c b =ᵐ[phaseμ P] liftFun R c b' := by
  set N : Set (ℝ × (ℝ × ℝ)) := toMeasurable (ageμ c (-3 / 2)) {p | b p ≠ b' p} with hNdef
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : ageμ c (-3 / 2) N = 0 := by
    rw [hNdef, measure_toMeasurable]; exact ae_iff.1 h
  have hsub : {p | b p ≠ b' p} ⊆ N := subset_toMeasurable _ _
  let e0 : Merid := EuclideanSpace.single 0 1
  have he0 : e0 ≠ 0 := by
    intro h0
    have := congrArg (fun v : Merid => v 0) h0
    simp [e0] at this
  let b₁ : ℝ × (ℝ × ℝ) → Merid := N.indicator (fun _ => e0)
  have hb₁ : Measurable b₁ := measurable_const.indicator hNm
  have hb₁0 : b₁ =ᵐ[ageμ c (-3 / 2)] (0 : ℝ × (ℝ × ℝ) → Merid) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with p hp
    simp [b₁, hp]
  have hz := liftFun_congr_ae hR hc hP hb₁ measurable_zero hb₁0
  have hax : ∀ᵐ x ∂phaseμ P, x.2 ∉ axis := by
    rw [ae_iff]
    have : {x : ℝ × Space | ¬ x.2 ∉ axis} = (Set.univ : Set ℝ) ×ˢ axis := by
      ext x; simp
    rw [this]
    unfold phaseμ
    rw [Measure.prod_prod]
    have : (volume : Measure Space) axis = 0 := by
      refine measure_mono_null ?_ UnforcedLeray.Blueprint.C07.volume_axis
      intro y hy
      obtain ⟨h0, h1⟩ := hy
      show y 0 ^ 2 + y 1 ^ 2 = 0
      rw [h0, h1]; norm_num
    rw [this, mul_zero]
  filter_upwards [hz, hax] with x hx hxa
  by_cases hpt : ((chart R x.1 x.2).1, (cellRep c (chart R x.1 x.2).2.1,
      (chart R x.1 x.2).2.2)) ∈ N
  · exfalso
    have hage : 0 < age R x.2 := by
      unfold age
      have : ϱ x.2 ≠ 0 := by
        intro h0
        apply hxa
        have h2 : x.2 0 ^ 2 + x.2 1 ^ 2 = 0 := by
          have := Real.sqrt_eq_zero'.1 h0
          nlinarith [sq_nonneg (x.2 0), sq_nonneg (x.2 1)]
        exact ⟨by nlinarith [sq_nonneg (x.2 0), sq_nonneg (x.2 1)],
          by nlinarith [sq_nonneg (x.2 0), sq_nonneg (x.2 1)]⟩
      positivity
    have h1 : liftFun R c b₁ x = 0 := by
      rw [hx]; simp [liftFun, Nv, perExt]
    have hk : (√Real.pi * R)⁻¹ ≠ 0 := by
      have : 0 < √Real.pi * R := mul_pos (Real.sqrt_pos.2 Real.pi_pos) hR
      exact (inv_pos.2 this).ne'
    have hf : frameL x.2 e0 ≠ 0 := by
      intro h0
      have := norm_frameL hxa e0
      rw [h0, norm_zero] at this
      exact he0 (norm_eq_zero.1 this.symm)
    have h2 : liftFun R c b₁ x = (√Real.pi * R)⁻¹ • (√(age R x.2) • frameL x.2 e0) := by
      simp [liftFun, Nv, perExt, b₁, hpt]
    rw [h2] at h1
    exact smul_ne_zero hk (smul_ne_zero (Real.sqrt_pos.2 hage).ne' hf) h1
  · have : b ((chart R x.1 x.2).1, (cellRep c (chart R x.1 x.2).2.1,
        (chart R x.1 x.2).2.2)) = b' ((chart R x.1 x.2).1, (cellRep c (chart R x.1 x.2).2.1,
        (chart R x.1 x.2).2.2)) := by
      by_contra hne
      exact hpt (hsub hne)
    simp only [liftFun, Nv, perExt, this]

theorem hhatTransfer_of {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff]
    [NormedSpace ℝ Aff] [CompleteSpace Aff] (B : ReturnBase c mZ ρb γ ν Aff)
    {ι : Aff →ₗ[ℝ] (ℝ → Mat3)} {χf : ℝ → ℝ} {μ ε : ℝ} (hc : 0 < c) (hcν : c = cOf ν)
    (hν : 0 < ν) (hε : 0 < ε) (hAff : IsAffinePinned B ι χf μ ε) :
    HhatTransfer B ι χf ε := by
  intro A φ hφ
  have : Fact (0 < 2 * ε * c) := ⟨by positivity⟩
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have hP : 2 * ε * c = 2 * c / ε⁻¹ := by rw [div_inv_eq_mul]; ring
  have hbm : Measurable (B.hA A : Chart → Merid) := (Lp.stronglyMeasurable (B.hA A)).measurable
  have h0 := (hAff A).1
  have h1 : (B.hA A : Chart → Merid) =ᵐ[ageμ c (-3 / 2)] hhatChart ν ε χf (ι A) := by
    have := UnforcedLeray.Short.PartIIIb.NearInst.ae_bodyMeasure c γ ν
    rw [this] at h0
    exact h0
  have h2 := liftFun_congr_ae_left hR hc hP hbm h1
  rw [wda_ae_phaseμ] at h2
  have hae : velPhys ε⁻¹ c (B.hA A : Chart → Merid) =ᵐ[volume.restrict
      (phaseCell (2 * ε * c))] velPhys ε⁻¹ c (hhatChart ν ε χf (ι A)) := by
    rw [wda_velPhys_eq _ _ hR.ne', wda_velPhys_eq _ _ hR.ne']
    filter_upwards [h2] with x hx
    simp only [hx]
  have hI : Integrable (fun x => dotL (gradT φ x) (velPhys ε⁻¹ c (B.hA A : Chart → Merid) x))
      (volume.restrict (phaseCell (2 * ε * c))) :=
    wda_integrable_dotL hφ.gradT.smooth.continuous hφ.gradT.bounded_support
      (wda_memLp_velPhys hc hν hε (B.hA A))
  have hI' : Integrable (fun x => dotL (gradT φ x)
      (velPhys ε⁻¹ c (hhatChart ν ε χf (ι A)) x)) (volume.restrict (phaseCell (2 * ε * c))) := by
    refine hI.congr ?_
    filter_upwards [hae] with x hx
    rw [hx]
  rw [pairF_eq_restrictedProductIntegral hI, pairF_eq_restrictedProductIntegral hI']
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hae] with x hx
  rw [hx]

end UnforcedLeray.Short.PartIIIb.Concrete
