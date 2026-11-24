import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollCommDefs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollCommLemmas.KernelIdentity
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollCommLemmas.TestKerSmooth
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjMollLocInt

/-!
# `MollIntegralSplit`: splitting the adjoint integral into the test integral and the commutator

Source `the November 2 reference manuscript` (adjoint graph at `r = 2` and the
mollified commutator; the cited line numbers of the task spec do not match the current file, the
mathematics is that of the docstrings in `MollCommDefs`). Pointwise `adjKer - testKer = ½ kap`
(`kernelIdentity`), so the integrals split once both integrands are integrable. Integrability:
`testKer` and `½ kap` are continuous with compact support and `F` is locally integrable
(`locInt_of_isInYr`), the translate `z ↦ F(x - z)` is handled by `Integrable.comp_sub_left`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- The half commutator kernel `½ kap ρ` is continuous with compact support. -/
theorem mis_halfKap_props (ρ : ContDiffBump (0 : ℝ × Space)) :
    Continuous (fun z : ℝ × Space => (1 / 2 : ℝ) * kap ρ z) ∧
      HasCompactSupport (fun z : ℝ × Space => (1 / 2 : ℝ) * kap ρ z) := by
  have hκs : ContDiff ℝ ∞ (ρ.normed volume) := ρ.contDiff_normed
  have hcs : HasCompactSupport (ρ.normed volume) := ρ.hasCompactSupport_normed
  have hF : ContDiff ℝ ∞ (fderiv ℝ (ρ.normed volume)) := (contDiff_infty_iff_fderiv.mp hκs).2
  have hcont : Continuous (fun z : ℝ × Space => (1 / 2 : ℝ) * kap ρ z) := by
    unfold kap kerDv
    exact continuous_const.mul ((continuous_const.mul hκs.continuous).add
      (hF.continuous.clm_apply (continuous_const.prodMk continuous_snd)))
  have hsupp : HasCompactSupport (fun z : ℝ × Space => (1 / 2 : ℝ) * kap ρ z) := by
    refine HasCompactSupport.intro hcs.isCompact ?_
    intro z hz
    have hκz : ρ.normed volume z = 0 := by
      have := notMem_tsupport_iff_eventuallyEq.mp hz
      simpa using this.self_of_nhds
    have hf : fderiv ℝ (ρ.normed volume) z = 0 := fderiv_of_notMem_tsupport ℝ hz
    simp [kap, kerDv, hκz, hf]
  exact ⟨hcont, hsupp⟩

/-- Integrability of `z ↦ g z • F (x - z)` for a locally integrable `F` and a continuous kernel
`g` with compact support. -/
theorem mis_integrable_kernel {F : ℝ × Space → CVec3} (hF : LocallyIntegrable F volume)
    {g : ℝ × Space → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) (x : ℝ × Space) :
    Integrable (fun z => g z • F (x - z)) volume := by
  have hgx : Continuous (fun w : ℝ × Space => g (x - w)) :=
    hg.comp (continuous_const.sub continuous_id)
  have hgxc : HasCompactSupport (fun w : ℝ × Space => g (x - w)) :=
    hgc.comp_homeomorph (Homeomorph.subLeft x)
  have h1 : Integrable (fun w : ℝ × Space => g (x - w) • F w) volume :=
    hF.integrable_smul_left_of_hasCompactSupport hgx hgxc
  have h2 := h1.comp_sub_left x
  simpa using h2

/-- Splitting of the integrals: `∫ testKer F(x - ·) = ∫ adjKer F(x - ·) - commK ρ F x`. -/
theorem mollIntegralSplit : MollIntegralSplit := by
  intro P ν μ hP F hF ρ x
  have hloc : LocallyIntegrable F volume := locInt_of_isInYr hP hF
  have hT : ContDiff ℝ ∞ (testKer ν μ ρ x) ∧ HasCompactSupport (testKer ν μ ρ x) :=
    testKerSmooth ν μ ρ x
  have hKI : KernelIdentity := kernelIdentity
  have hC := mis_halfKap_props ρ
  have hI1 := mis_integrable_kernel hloc hT.1.continuous hT.2 x
  have hI2 := mis_integrable_kernel hloc hC.1 hC.2 x
  have hsplit : ∫ z, adjKer ν μ ρ x z • F (x - z)
      = (∫ z, testKer ν μ ρ x z • F (x - z)) + ∫ z, ((1 / 2 : ℝ) * kap ρ z) • F (x - z) := by
    rw [← integral_add hI1 hI2]
    congr 1
    funext z
    have hk : adjKer ν μ ρ x z = testKer ν μ ρ x z + (1 / 2 : ℝ) * kap ρ z := by
      have := hKI ν μ ρ x z
      linarith
    simp only [hk, add_smul]
  rw [hsplit]
  simp only [commK]
  abel

end UnforcedLeray.Short.PartIIIb.Concrete
