import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_6
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ProfileOfNoSwirl.AvgPG
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ProfileOfNoSwirl.Ext

/-!
# Real and imaginary parts of no-swirl phase fields

Helpers for `PartII-b:T10/6/2`: the real part `reV` and imaginary part `imV` of a complex vector,
their behaviour under the complexified action `B0412.gC`, and the transfer of the per-`g`
no-swirl hypothesis `PhaseNoSwirl` to the real parts.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.B0412 UnforcedLeray.PhaseSpace

/-- The real part of a complex vector in `ℂ³`, as a real vector. -/
def reV (v : CVec3) : Space := WithLp.toLp 2 fun i => (v i).re

/-- The imaginary part of a complex vector in `ℂ³`, as a real vector. -/
def imV (v : CVec3) : Space := WithLp.toLp 2 fun i => (v i).im

theorem reV_add (v w : CVec3) : reV (v + w) = reV v + reV w := by
  ext i
  simp [reV]

theorem imV_add (v w : CVec3) : imV (v + w) = imV v + imV w := by
  ext i
  simp [imV]

theorem reV_realC (x : Space) : reV (realC x) = x := by
  ext i
  simp [reV, realC_apply]

theorem imV_realC (x : Space) : imV (realC x) = 0 := by
  ext i
  simp [imV, realC_apply]

theorem reV_I_smul_realC (x : Space) : reV (Complex.I • realC x) = 0 := by
  ext i
  simp [reV, realC_apply]

theorem imV_I_smul_realC (x : Space) : imV (Complex.I • realC x) = x := by
  ext i
  simp [imV, realC_apply]

theorem realC_decomp (v : CVec3) : v = realC (reV v) + Complex.I • realC (imV v) := by
  ext i
  simp only [PiLp.add_apply, PiLp.smul_apply, realC_apply, reV, imV, smul_eq_mul]
  have h := Complex.re_add_im (v i)
  linear_combination (-1 : ℂ) * h

theorem reV_gC (g : Space ≃ₗᵢ[ℝ] Space) (v : CVec3) : reV (gC g v) = g (reV v) := by
  conv_lhs => rw [realC_decomp v]
  rw [map_add, map_smul, gC_realC, gC_realC, reV_add, reV_realC, reV_I_smul_realC, add_zero]

theorem imV_gC (g : Space ≃ₗᵢ[ℝ] Space) (v : CVec3) : imV (gC g v) = g (imV v) := by
  conv_lhs => rw [realC_decomp v]
  rw [map_add, map_smul, gC_realC, gC_realC, imV_add, imV_realC, imV_I_smul_realC, zero_add]

/-- Transfer of the per-`g` no-swirl relation to a real part `Φ ∘ d'`, for a.e.-equal `d'`. -/
theorem ae_equiv_of_phaseNoSwirl {Φ : CVec3 → Space}
    (hlin : ∀ (g : Space ≃ₗᵢ[ℝ] Space) (v : CVec3), Φ (gC g v) = g (Φ v))
    {d d' : ℝ × Space → CVec3} (hns : PhaseNoSwirl d) (hdd : d' =ᵐ[volume] d)
    (g : Space ≃ₗᵢ[ℝ] Space) (hg : FixesAxis g) :
    ∀ᵐ x ∂(volume : Measure (ℝ × Space)), Φ (d' (x.1, g x.2)) = g (Φ (d' x)) := by
  have h1 : ∀ᵐ x ∂(volume : Measure (ℝ × Space)), gC g (d (x.1, g.symm x.2)) = d x :=
    hns g hg
  have hF : MeasurePreserving (fun x : ℝ × Space => (x.1, g x.2))
      (volume : Measure (ℝ × Space)) volume :=
    (MeasurePreserving.id volume).prod g.measurePreserving
  have h2 := hF.quasiMeasurePreserving.ae h1
  have h3 : ∀ᵐ x ∂(volume : Measure (ℝ × Space)), d' (x.1, g x.2) = d (x.1, g x.2) :=
    hF.quasiMeasurePreserving.ae hdd
  filter_upwards [h2, h3, hdd] with x hx1 hx2 hx3
  simp only [LinearIsometryEquiv.symm_apply_apply] at hx1
  rw [hx2, hx3, ← hx1, hlin]

/-- Transfer of an a.e. statement on `volume` to `phaseμ P`. -/
theorem ae_phase_of_ae_volume {P : ℝ} {Q : ℝ × Space → Prop}
    (h : ∀ᵐ x ∂(volume : Measure (ℝ × Space)), Q x) : ∀ᵐ x ∂UnforcedLeray.Axi.phaseμ P, Q x := by
  unfold UnforcedLeray.Axi.phaseμ
  rw [Measure.prod_smul_left]
  apply Measure.ae_smul_measure
  have e2 : ((volume : Measure ℝ).restrict (Ioc 0 P)).prod (volume : Measure Space) =
      ((volume : Measure ℝ).prod (volume : Measure Space)).restrict (Ioc 0 P ×ˢ univ) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [e2]
  exact ae_restrict_of_ae h

end UnforcedLeray.Short.IIb
