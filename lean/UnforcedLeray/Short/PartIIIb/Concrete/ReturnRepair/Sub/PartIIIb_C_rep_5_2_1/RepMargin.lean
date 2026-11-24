import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_1Org
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThinBridge

/-!
# `PartIII-b:C/rep/5/2/1/12`: the repair margins

Source `the November 2 reference manuscript` 5601-5605, 5114-5120, 4109-4124.
`RepMargin` (`Org`) is proved from the `FtPE` calculus of `FarThinBridge` (`ft_retEps_rpow_le`,
`ft_gaugeN_pe`, `ftPE_exp`, `FtPE.mul`, `FtPE.mono`) applied to `ε = retEps`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The power identity `ε^{34/11} (ε^{-b})^{23/22} (ε^{3/11} m) ε⁻¹ = ε^{26/11 - 23b/22} m`. -/
theorem repMargin_eps_identity {ε b m : ℝ} (hε : 0 < ε) :
    ε ^ (34 / 11 : ℝ) * (ε ^ (-b)) ^ (23 / 22 : ℝ) * (ε ^ (3 / 11 : ℝ) * m) * ε⁻¹ =
      ε ^ (26 / 11 - 23 * b / 22 : ℝ) * m := by
  have hpow : ε ^ (26 / 11 - 23 * b / 22 : ℝ) =
      ε ^ (34 / 11 : ℝ) * ε ^ (-b * (23 / 22 : ℝ)) * ε ^ (3 / 11 : ℝ) * ε ^ (-1 : ℝ) := by
    rw [← Real.rpow_add hε, ← Real.rpow_add hε, ← Real.rpow_add hε]
    congr 1
    ring
  rw [hpow, ← Real.rpow_mul hε.le, Real.rpow_neg_one]
  ring

theorem repMargin (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : RepMargin Pl σ₀ mZ dm dp := by
  unfold RepMargin
  intro D hPl hσ _ hst
  subst hPl
  subst hσ
  have hγ : 0 < gRate D.Pl := hst.gamma_pos
  have hb : 0 ≤ D.K.b := hst.b_pos.le
  have hm : 0 ≤ D.K.m0 := hst.m0_pos.le
  have hbg : 0 ≤ D.K.b * gRate D.Pl := mul_nonneg hb hγ.le
  obtain ⟨C, j, _, hfe⟩ := ft_retEps_rpow_le D.coeff_ne (26 / 11 - 23 * D.K.b / 22)
  have hev := retNu_retEps_eventually_le_one hst.omega_ne hγ D.coeff_ne
  refine ⟨C, j + ⌈D.Pl.kappa.re⌉₊, ?_⟩
  filter_upwards [hev] with n hn
  unfold RepMarginAt
  set L := D.level n with hLdef
  have hν1 : L.ν ≤ 1 := hn.1
  have hνp : 0 < L.ν := L.ν_pos
  have hεp : 0 < L.ε := L.ε_pos
  have hA : FtPE (L.ε ^ (26 / 11 - 23 * D.K.b / 22 : ℝ)) L.ν
      (-((26 / 11 - 23 * D.K.b / 22 : ℝ) * (gRate D.Pl / 3))) C j := hfe n hν1
  -- the common product `ε^p e^{m₀/ν}`
  have h1 := FtPE.mul hA (ftPE_exp L.ν D.K.m0)
  -- conjunct 1: times `e^{-4γ/(9ν)}` and `|N_ν|`
  have h2 := FtPE.mul h1 (ftPE_exp L.ν (-(4 * gRate D.Pl / 9)))
  have h3 := FtPE.mul h2 (ft_gaugeN_pe D.Pl L hν1)
  -- conjunct 2: times `e^{3γ/(5ν)}`
  have h5 := FtPE.mul h1 (ftPE_exp L.ν (3 * gRate D.Pl / 5))
  have hEq1 : L.ε ^ (34 / 11 : ℝ) * L.Scut D.K ^ (23 / 22 : ℝ) * rhoRep D.K L * L.ε⁻¹ =
      L.ε ^ (26 / 11 - 23 * D.K.b / 22 : ℝ) * Real.exp (D.K.m0 / L.ν) := by
    unfold rhoRep ReturnLevel.Scut
    exact repMargin_eps_identity hεp
  have ha1 : -((26 / 11 - 23 * D.K.b / 22 : ℝ) * (gRate D.Pl / 3)) + D.K.m0 +
      -(4 * gRate D.Pl / 9) + gRate D.Pl ≤
      -(31 * gRate D.Pl / 165 - ((2 : ℕ) : ℝ) * D.K.b * (gRate D.Pl / 3) - 3 * D.K.m0 / 2) := by
    push_cast
    nlinarith [hbg, hγ, hm]
  have ha2 : -((26 / 11 - 23 * D.K.b / 22 : ℝ) * (gRate D.Pl / 3)) + D.K.m0 +
      3 * gRate D.Pl / 5 ≤
      -(31 * gRate D.Pl / 165 - ((2 : ℕ) : ℝ) * D.K.b * (gRate D.Pl / 3) - 3 * D.K.m0 / 2) := by
    push_cast
    nlinarith [hbg, hγ, hm]
  have hJ1 : j + 0 + 0 + ⌈D.Pl.kappa.re⌉₊ ≤ j + ⌈D.Pl.kappa.re⌉₊ := by simp
  have hJ2 : j + 0 + 0 ≤ j + ⌈D.Pl.kappa.re⌉₊ := by simp
  have g1 := FtPE.mono h3 hνp hν1 ha1 hJ1
  have g2 := FtPE.mono h5 hνp hν1 ha2 hJ2
  constructor
  · rw [hEq1]
    have := g1.2
    simpa only [mul_one] using this
  · rw [hEq1]
    have := g2.2
    simpa only [mul_one] using this

end UnforcedLeray.Short.PartIIIb.Concrete
