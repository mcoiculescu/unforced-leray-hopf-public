import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2.HhatAPeriodic
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2.HhatNvStream
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2.HhatRingProfile
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2.PsiRingSmooth
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2.RingStreamSmooth
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2.RingStreamYoung
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2.StreamLiftIbp
import UnforcedLeray.Short.PartIIIb.Concrete.HpJGradProof
import UnforcedLeray.Lib.Axisymmetric.RingChart

/-!
# `hhatChartSolenoidal_of`: the chart representative of `ĥ_A` is weakly solenoidal
(source 4991-4997, 5036-5039)

For each `A`, `ĥ_A` is the stream lift `streamLift (ringStream (1/ε) τ ψ^p_A)` off the axis
(`hhatNvStream_proof`, with `ψ^p_A` the lattice stream function of `HpIsJGrad`), and the
per-phase pairing of a gradient of a phase test with a stream lift vanishes (`streamLiftIbp_proof`).
The axis is null, so the spatial integrals agree and the phase average vanishes.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

theorem hhatChartSolenoidal_of {c ν ε : ℝ} {Aff : Type} [NormedAddCommGroup Aff] [NormedSpace ℝ Aff]
    {ι : Aff →ₗ[ℝ] (ℝ → Mat3)} {χf : ℝ → ℝ} {as : ℝ} (hχf : IsSourceCutoffC χf)
    (hι : ∀ A, IsAffElem as (ι A)) (hc : 0 < c) (hcν : c = cOf ν) (hν : 0 < ν) (hε : 0 < ε) :
    HhatChartSolenoidal ν ε c ι χf := by
  intro A φ hφ
  have hR : ε⁻¹ ≠ 0 := inv_ne_zero hε.ne'
  have hRpos : 0 < ε⁻¹ := inv_pos.2 hε
  have hψ : ContDiffOn ℝ 2 (psiRing ν χf (ι A)) (Ioi 0 ×ˢ univ) :=
    psiRingSmooth_proof as χf hχf ν hν (ι A) (hι A)
  -- the chart is in the open set `{s > 0}` off the axis, so `ψ^p_A` is differentiable there
  have hdiffAt : ∀ (τ : ℝ) (y : Space), y ∉ Axi.axis →
      DifferentiableAt ℝ (psiRing ν χf (ι A)) (Axi.chart ε⁻¹ τ y) := by
    intro τ y hy
    have hpos : 0 < (Axi.chart ε⁻¹ τ y).1 := Axi.age_pos hR hy
    have hmem : Axi.chart ε⁻¹ τ y ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
      mem_prod.mpr ⟨hpos, mem_univ _⟩
    exact (hψ.differentiableOn (by norm_num)).differentiableAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds hmem)
  -- off the axis, the physical field of `ĥ_A` is the stream lift of `ρ ψ^p_A`
  have hpeq : ∀ (τ : ℝ) (y : Space), y ∉ Axi.axis →
      Axi.Nv ε⁻¹ (Axi.perExt c (hhatChart ν ε χf (ι A))) τ y
        = Axi.streamLift (Axi.ringStream ε⁻¹ τ (psiRing ν χf (ι A))) y := fun τ y hy =>
    hhatNvStream_proof ν ε c hε χf hcν (hhatAPeriodic_proof ν ε χf) (hhatRingProfile_proof ν ε χf)
      (ι A) (hpIsJGrad_proof ν hν χf (ι A)) τ y hy (hdiffAt τ y hy)
  have hae : ∀ᵐ y ∂(volume : Measure Space), y ∉ Axi.axis :=
    measure_eq_zero_iff_ae_notMem.1 Axi.volume_axis
  -- for each phase `τ`, the spatial integral vanishes
  have hslice : ∀ τ : ℝ,
      ∫ y, dotL (gradT φ (τ, y)) (velPhys ε⁻¹ c (hhatChart ν ε χf (ι A)) (τ, y)) = 0 := by
    intro τ
    obtain ⟨ρ0, hρ0, hz⟩ := ringStreamYoung_proof ν χf hχf hν ε⁻¹ hRpos (ι A) τ
    have hΨ := ringStreamSmooth_proof ε⁻¹ τ (psiRing ν χf (ι A)) hR hψ
    have hIbp := streamLiftIbp_proof (2 * ε * c)
      (Axi.ringStream ε⁻¹ τ (psiRing ν χf (ι A))) hΨ ρ0 hρ0 hz φ hφ τ
    have hcongr : (fun y : Space =>
        dotL (gradT φ (τ, y)) (velPhys ε⁻¹ c (hhatChart ν ε χf (ι A)) (τ, y))) =ᵐ[volume]
        (fun y : Space => dotL (gradT φ (τ, y))
          (B0412.realC (Axi.streamLift (Axi.ringStream ε⁻¹ τ (psiRing ν χf (ι A))) y))) := by
      filter_upwards [hae] with y hy
      show dotL (gradT φ (τ, y))
          (B0412.realC (Axi.Nv ε⁻¹ (Axi.perExt c (hhatChart ν ε χf (ι A))) τ y))
        = dotL (gradT φ (τ, y))
          (B0412.realC (Axi.streamLift (Axi.ringStream ε⁻¹ τ (psiRing ν χf (ι A))) y))
      rw [hpeq τ y hy]
    rw [integral_congr_ae hcongr]
    exact hIbp
  unfold pairF phaseInt
  simp only [hslice, integral_zero, smul_zero]

end UnforcedLeray.Short.PartIIIb.Concrete
