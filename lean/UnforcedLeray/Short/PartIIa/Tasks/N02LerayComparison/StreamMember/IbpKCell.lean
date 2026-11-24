import UnforcedLeray.Short.PartIIa.Sub.N02_2
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.Identity
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.CTestFderiv
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.CTestAlgebra
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.CTestAgeScale
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.BandIntegrable
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.PdAgeScale
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.IbpSCell
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.IbpEtaCell

/-!


Source of record: `the November 2 reference manuscript`, lines 1730-1732.
Target: `IbpKCell` (`Sub/N02_2.lean`): for a complex band test `F`,
`∫_{cell} s^{-3/2} (K F) = 0`.

## Route

On `s > 0`, `s^{-3/2} K F = 2 ∂_s(s^{-1/2} F) + s^{-3/2} ∂_η(η F)` pointwise, so the cell integral
splits into `2 ∫ ∂_s G1` and `∫ s^{-3/2} ∂_η G2` with `G1 = s^{-1/2} F`, `G2 = η F`. The first
vanishes by `IbpSCell`, the second by `IbpEtaCell`.

Helpers (prefix `ikc`): `ikc_pointwise` (the pointwise identity), `ikc_pdEta_snd` (the `η`-derivative
of `η F`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-- Helper (`ikc`): the `η`-derivative of `η F`, for `F` differentiable. -/
theorem ikc_pdEta_snd {F : Profile → ℂ} (hdiff : Differentiable ℝ F) (p : Profile) :
    pdEta (fun x : Profile => (x.2.2 : ℂ) * F x) p = (p.2.2 : ℂ) * pdEta F p + F p := by
  unfold pdEta
  rw [NearStreamMemberAux.fderiv_snd_snd_mul hdiff p ((0, 0, 1) : Profile)]
  simp

/-- Helper (`ikc`): the pointwise identity `s^{-3/2} K F = 2 ∂_s(s^{-1/2} F) + s^{-3/2} ∂_η(η F)`
for `s > 0`. -/
theorem ikc_pointwise {F : Profile → ℂ} (hF : ContDiff ℝ ∞ F) (p : Profile) (hp : 0 < p.1) :
    ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * opK F p =
      2 * pdS (fun x : Profile => ((x.1 ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * F x) p +
        ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * pdEta (fun x : Profile => (x.2.2 : ℂ) * F x) p := by
  obtain ⟨h1, _, _⟩ := pdAgeScale (-(1 / 2 : ℝ)) F hF p hp
  rw [h1, ikc_pdEta_snd (hF.differentiable (by simp)) p, NearStreamMemberAux.opK_eq]
  have ha : p.1 ^ (-(1 / 2 : ℝ) - 1) = p.1 ^ (-(3 / 2 : ℝ)) := by norm_num
  have hb : p.1 ^ (-(3 / 2 : ℝ)) * p.1 = p.1 ^ (-(1 / 2 : ℝ)) := by
    have h32 : (-(1 / 2 : ℝ)) = -(3 / 2 : ℝ) + 1 := by norm_num
    rw [h32, Real.rpow_add hp, Real.rpow_one]
  have hc : ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * ((p.1 : ℝ) : ℂ) =
      ((p.1 ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, hb]
  rw [ha]
  push_cast at hc ⊢
  linear_combination (2 * pdS F p) * hc

/-- **Target `PartII-a:N02/2/16`**: `IbpKCell`, for a complex band test `F`,
`∫_{cell c} s^{-3/2} (K F) = 0`. -/
theorem ibpKCell : UnforcedLeray.Short.PartIIa.IbpKCell := by
  intro c F hF
  have hG1 : IsCTest c (fun p : Profile => ((p.1 ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * F p) :=
    cTestAgeScale c (-(1 / 2 : ℝ)) F hF
  have hsmooth : ContDiff ℝ ∞ (fun x : Profile => (x.2.2 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_snd.comp contDiff_snd)
  have hper : QPeriodic c (fun x : Profile => (x.2.2 : ℂ)) := fun _ => rfl
  have hG2 : IsCTest c (fun p : Profile => (p.2.2 : ℂ) * F p) :=
    ctaMul c F (fun x : Profile => (x.2.2 : ℂ)) hF hsmooth hper
  have hint1 : IntegrableOn (fun p : Profile =>
      pdS (fun x : Profile => ((x.1 ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * F x) p) (cell c) :=
    (bandIntegrable c _ (cTestFderiv c _ hG1 (1, 0, 0))).1
  have hint2 : IntegrableOn (fun p : Profile =>
      ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
        pdEta (fun x : Profile => (x.2.2 : ℂ) * F x) p) (cell c) :=
    (bandIntegrable c _ (cTestFderiv c _ hG2 (0, 0, 1))).2
  have hcell : MeasurableSet (cell c) :=
    measurableSet_Ioi.prod (measurableSet_Ioc.prod MeasurableSet.univ)
  have hcongr : ∫ p in cell c, ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * opK F p =
      ∫ p in cell c, (2 * pdS (fun x : Profile => ((x.1 ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * F x) p +
        ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
          pdEta (fun x : Profile => (x.2.2 : ℂ) * F x) p) :=
    setIntegral_congr_fun hcell (fun p hp => ikc_pointwise hF.smooth p hp.1)
  rw [hcongr, integral_add (hint1.const_mul 2) hint2, integral_const_mul,
    ibpSCell c _ hG1, ibpEtaCell c _ hG2]
  simp

end UnforcedLeray.Short.PartIIa
