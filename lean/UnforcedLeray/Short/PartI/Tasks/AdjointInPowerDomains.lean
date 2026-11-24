import UnforcedLeray.Short.PartI.StatementsSeed
import UnforcedLeray.Short.PartI.Tasks.AdjointKernelOneDim
import UnforcedLeray.Short.PartI.Tasks.ModeInPowerDomains.GaussianMemXGj
import UnforcedLeray.Cons.L2.CanonicalBranch
import UnforcedLeray.Lib.PlanarSpectralB.AdjointDomain
import UnforcedLeray.Units.B0122.Coeff

/-!
# Part I, task `PartI:S10b`: the adjoint eigenvector lies in every `X_{G,j}`

Source of record: `the November 2 reference manuscript`, lines 913-929.

Route: the seed `q` is a nonzero multiple of the explicit whole-line mode `qMode`; the explicit
adjoint mode `qdagMode` is an adjoint eigenvector with Gaussian-class radial coefficient
`adjointBeta`, hence lies in every `X_{G,j}` (`gaussianSmoothMemXGj`); by `adjoint_eigenvector_unique`
the Riesz representative of `l` is a nonzero multiple of it.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.ComplexODEC UnforcedLeray.Cons.G3b UnforcedLeray.Cons.C01
open scoped ContDiff ComplexConjugate

namespace UnforcedLeray.Short.PartI

/-- The seed `q` is a nonzero multiple of the explicit mode `qMode`, with `lam = lamMode c`. -/
theorem seed_eq_explicit_mode {lam : ℂ} {q : B0010.XG} {l : B0010.XG →L[ℂ] ℂ}
    (hI : IsSeedXG lam q l) :
    ∃ (c : ℂ) (F : ℝ → ℂ) (hF : WholeLineData c F) (μ : ℂ),
      μ ≠ 0 ∧ q = μ • qMode hF ∧ lam = lamMode c := by
  obtain ⟨c, him, hre0, hre1, -, F, hmode, -, hsmooth, h1, h2, h3, h4⟩ :=
    Rayleigh.Evans.exists_wholeLine_growing_mode
  have hF : WholeLineData c F := ⟨hmode, hsmooth, h1, h2, h3, h4⟩
  obtain ⟨g1, -, -⟩ := Rayleigh.Evans.growthRate_bounds him hre0 hre1
  have hqne : qMode hF ≠ 0 := by
    intro hq
    apply modeVort_not_ae_zero hF
    have hzeroX : modeVort c F =ᵐ[B0010.xGMeasure] (0 : ℝ → ℂ) := by
      filter_upwards [coeFn_qMode hF,
        (show (⇑(qMode hF) : ℝ → ℂ) =ᵐ[B0010.xGMeasure] 0 from by
          rw [hq]
          exact Lp.coeFn_zero ℂ 2 B0010.xGMeasure)] with r h1 h2
      rw [← h1, h2]
    exact B0012.restrict_ac.ae_le hzeroX
  have hqEig : Planar.L0 (qMode hF) = lamMode c • qMode hF := L0_qMode hF
  have hgr : 0 < (lamMode c).re := g1
  obtain ⟨hz, μ, hμ⟩ := Planar.L0_eigen_unique hI.re_pos hgr hI.eigen hqEig hI.ne_zero hqne
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    apply hqne
    rw [hμ, zero_smul]
  refine ⟨c, F, hF, μ⁻¹, inv_ne_zero hμ0, ?_, hz.symm⟩
  rw [hμ, smul_smul, inv_mul_cancel₀ hμ0, one_smul]

theorem sz_wz_eq (z : ℝ × ℝ) :
    B0094.wz z = Complex.equivRealProd.symm z ∧
      B0094.sz z = ‖Complex.equivRealProd.symm z‖ ^ 2 := by
  constructor
  · apply Complex.ext <;> simp [B0094.wz, Complex.equivRealProd]
  · rw [B0094.sz, Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.equivRealProd]
    ring

/-- The explicit adjoint mode lies in every `X_{G,j}`. -/
theorem qdagMode_mem_XGj {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F) (j : ℕ) :
    qdagMode hF ∈ B0121.XGj j := by
  obtain ⟨β₀, hβ₀, hβ⟩ := exists_mode_eq_regLog hF
  have hβ' : ∀ t, F t = β₀ * regLog c t := fun t => (hβ t).1
  let J : ℂ := directAdjointPairing c F
  have hJ : J ≠ 0 := by simpa [J] using directAdjointPairing_ne_zero hF
  have hcd : ContDiff ℝ ∞ (PlanarSpectral.adjointBeta c β₀ J) :=
    PlanarSpectral.contDiff_adjointBeta hF β₀ J
  have hb := PlanarSpectral.derivBound_adjointBeta hF β₀ J
  let f₂ : ℝ → ℂ := fun r => (r : ℂ) ^ 2 * PlanarSpectral.adjointBeta c β₀ J (r ^ 2)
  have hadj : adjointMode c F =ᵐ[B0010.xGMeasure] f₂ := by
    filter_upwards [PlanarSpectral.adjointProfileFormula_ae_eq_adjointBeta hβ' hJ]
      with r hr
    simpa [f₂, adjointMode, adjointKernel, PlanarSpectral.adjointProfileFormula,
      J, directAdjointPairing] using hr
  have hq : (⇑(qdagMode hF) : ℝ → ℂ) =ᵐ[B0010.xGMeasure] f₂ :=
    (MemLp.coeFn_toLp _).trans hadj
  refine gaussianSmoothMemXGj (qdagMode hF)
    (fun y : ℂ => y ^ 2 * PlanarSpectral.adjointBeta c β₀ J (‖y‖ ^ 2))
    (Planar.contDiff_angularTwo hcd)
    (fun k => ?_) ?_ j
  · obtain ⟨C, N, -, h⟩ := PlanarSpectral.norm_iteratedFDeriv_radialSq_le hcd hb k
    exact ⟨C, N, h⟩
  · have h1 : B0121.planar (qdagMode hF) =ᵐ[volume] B0010.angularTwoField f₂ :=
      B0122.angularTwoField_ae_eq_of_xG hq
    refine h1.trans (ae_of_all _ fun z => ?_)
    obtain ⟨hw, hs⟩ := sz_wz_eq z
    rw [show f₂ = fun r : ℝ => (r : ℂ) ^ 2 * PlanarSpectral.adjointBeta c β₀ J (r ^ 2) from rfl,
      PlanarSpectral.angularTwoField_radialSq, hw, hs]

/-- **`PartI:S10b`** (source lines 913-929): the Riesz representative of the seed functional
lies in every `X_{G,j}`. -/
theorem seed_adjoint_mem_XGj {lam : ℂ} {q : B0010.XG} {l : B0010.XG →L[ℂ] ℂ}
    (hI : IsSeedXG lam q l) {qd : B0010.XG} (hqd : ∀ f, l f = inner ℂ qd f) (j : ℕ) :
    qd ∈ B0121.XGj j := by
  obtain ⟨c, F, hF, μ, hμ, hq, hlam⟩ := seed_eq_explicit_mode hI
  have hadj : ContinuousLinearMap.adjoint Planar.L0 (qdagMode hF) =
      (starRingEnd ℂ) lam • qdagMode hF := by
    refine ext_inner_right ℂ (fun f => ?_)
    rw [ContinuousLinearMap.adjoint_inner_left, inner_smul_left, starRingEnd_self_apply, hlam]
    exact inner_qdagMode_L0 hF f
  obtain ⟨κ, hκ⟩ := adjoint_eigenvector_unique hI hqd hadj
  have hκ0 : κ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hκ
    have := inner_qdagMode_qMode hF
    rw [hκ, inner_zero_left] at this
    exact zero_ne_one this
  have : qd = κ⁻¹ • qdagMode hF := by
    rw [hκ, smul_smul, inv_mul_cancel₀ hκ0, one_smul]
  rw [this]
  exact (B0121.XGj j).smul_mem _ (qdagMode_mem_XGj hF j)

end UnforcedLeray.Short.PartI
