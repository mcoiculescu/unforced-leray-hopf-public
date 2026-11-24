import UnforcedLeray.Short.PartI.StatementsSeed
import UnforcedLeray.Lib.ComplexODEC
import UnforcedLeray.Lib.PlanarSpectralB.XGSpectrum

/-!
# Part I, task `PartI:S02`: the growing eigenvalue and its eigenline are unique

Source of record: `the November 2 reference manuscript`, lines 626-840
(the growing eigenvalue is unique and its eigenspace on `X_G` is a line).

Proof. Take a Gaussian growing mode `G` (`Planar.exists_gaussianGrowingMode`). Its eigenvector
`G.h_memLp_XG.toLp G.h` is nonzero, because otherwise its Green streamfunction vanishes
(the argument of `Planar.exists_actual_gaussian_mode_simple_spectral_projection`). The uniqueness
theorem `Planar.L0_eigen_unique` then gives `G.eigenvalue = lam` and `G.h = μ • q`, and the scalar
`μ` is nonzero because `G.h ≠ 0`. Inverting gives `q = μ⁻¹ • G.h`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ContDiff Topology ComplexConjugate

namespace UnforcedLeray.Short.PartI

/-- **Uniqueness of the growing pair** (source lines 626-840): a seed triple `(lam, q, l)` has
`lam` equal to the eigenvalue of a Gaussian growing mode `G`, and `q` is a nonzero multiple of
the eigenvector of `G`. -/
theorem isSeedXG_gaussianGrowingMode {lam : ℂ} {q : B0010.XG} {l : B0010.XG →L[ℂ] ℂ}
    (h : IsSeedXG lam q l) : ∃ (G : Planar.GaussianGrowingMode) (μ : ℂ), μ ≠ 0 ∧ lam = G.eigenvalue ∧ q = μ • (G.h_memLp_XG).toLp G.h := by
  obtain ⟨G⟩ := Planar.exists_gaussianGrowingMode
  -- The eigenvector of `G` is nonzero: otherwise `G.h` vanishes a.e. on `(0, ∞)`, so its Green
  -- streamfunction `φ = greenN 2 h` vanishes, contradicting `G.φ_ne_zero`.
  have hqG0 : (G.h_memLp_XG).toLp G.h ≠ 0 := by
    intro hq
    have hzeroX : G.h =ᵐ[B0010.xGMeasure] (0 : ℝ → ℂ) := by
      filter_upwards [G.h_memLp_XG.coeFn_toLp,
        (show (⇑((G.h_memLp_XG).toLp G.h) : ℝ → ℂ) =ᵐ[B0010.xGMeasure] 0 from by
          rw [hq]
          exact Lp.coeFn_zero ℂ 2 B0010.xGMeasure)]
        with r h1 h2
      rw [← h1, h2]
    have hzeroR : G.h =ᵐ[volume.restrict (Ioi (0 : ℝ))] (0 : ℝ → ℂ) :=
      B0012.restrict_ac.ae_le hzeroX
    obtain ⟨r, hr, hφ⟩ := G.φ_ne_zero
    have hgreen : Planar.greenN 2 G.h r = Planar.greenN 2 (0 : ℝ → ℂ) r :=
      UnforcedLeray.ComplexODEC.greenN_congr_ae hzeroR r
    apply hφ
    rw [G.φ_eq_green r hr, hgreen]
    simp [Planar.greenN]
  have hqEig : Planar.L0 ((G.h_memLp_XG).toLp G.h) =
      G.eigenvalue • (G.h_memLp_XG).toLp G.h := by
    simpa [Planar.GaussianGrowingMode.eigenvalue] using G.L0_eigen
  have hgr : 0 < G.eigenvalue.re := G.growth_pos
  obtain ⟨hz, μ, hμ⟩ := Planar.L0_eigen_unique h.re_pos hgr h.eigen hqEig h.ne_zero hqG0
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    apply hqG0
    rw [hμ, zero_smul]
  refine ⟨G, μ⁻¹, inv_ne_zero hμ0, hz.symm, ?_⟩
  rw [hμ, smul_smul, inv_mul_cancel₀ hμ0, one_smul]

end UnforcedLeray.Short.PartI

end
