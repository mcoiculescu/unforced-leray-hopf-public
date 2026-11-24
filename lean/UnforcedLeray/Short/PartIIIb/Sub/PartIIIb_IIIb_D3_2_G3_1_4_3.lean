import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G3.OldAnisoBareOrg

/-!
# Decomposition of `G3.PreparedDatumCompare` (`PartIII-b:IIIb-D3/2/G3/1/4/3`)

Source of record: `the November 2 reference manuscript`, lines 597–610, 625–627,
3127–3130, 4445–4447.

Reduces `G3.PreparedDatumCompare D` (`OldAnisoBareOrg.lean`) to two planar-to-cell bridges:
* `SeedLinkEqPlanarMode D` (`PartIII-b:IIIb-D3/2/G3/1/4/3/1`,
  `OldAnisoBare/PreparedCompare/SeedLinkEq.lean`): from `D.RepairStanding dm dp` and `SeedLink D κ`,
  the seed kernel `κ.e 0` agrees with `IIIa.planarMode D.Pl.mode`;
* `PeriodizePlanarModeXmc` (`PartIII-b:IIIb-D3/2/G3/1/4/3/2`,
  `OldAnisoBare/PreparedCompare/PeriodizeXmc.lean`): the periodization operator
  `f ↦ IIIa.periodizeC c (IIIa.planarMode f)` maps continuous `Planar.MemXG` profiles into
  `Xmc c m` (for `m > 8`, `c ≥ 1`) with Lipschitz norm bound
  `‖qf - qg‖ ≤ C_m * Planar.gaussianNorm (fun r => f r - g r)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G3

open UnforcedLeray.Blueprint.Planar (Profile MemXG gaussianNorm)
open FlatSettingInst (Xmc xFn)

/-- **Leaf 1 (`SeedLinkEqPlanarMode`, `PartIII-b:IIIb-D3/2/G3/1/4/3/1`)**: under
`D.RepairStanding dm dp` and `SeedLink D κ`, the direct planar seed kernel `κ.e 0` coincides with
`IIIa.planarMode D.Pl.mode` (source lines 597–610, 625–627).
Route: `Planar.L0_eigen_unique` identifies `D.Pl.mode` up to a scalar with the radial seed `h`
from `SeedLink.1` (`IIIa.IsSeedKernels κ`), `PartI.adjoint_eigenvector_unique` identifies
`D.Pl.adjointMode` up to a scalar with the Riesz representative of the seed functional `ℓ`,
and the normalization `gaussianPairing D.Pl.mode D.Pl.adjointMode = 1` together with
`SeedLink.2` (`∫ y, κ.lamP 0 y * FlatSettingInst.hMode 1 y = D.Pl.strainCoupling ≠ 0` via
`PartI.seedStrainCoupling_of` and `seedBiorthExt_proof`) fixes the scalar to `1`. -/
def SeedLinkEqPlanarMode (D : SeqData) : Prop :=
  ∀ (dm dp : ℝ), D.RepairStanding dm dp →
  ∀ (κ : IIIa.PlanarFrameKernels), SeedLink D κ →
    κ.e 0 = IIIa.planarMode D.Pl.mode

/-- **Leaf 2 (`PeriodizePlanarModeXmc`, `PartIII-b:IIIb-D3/2/G3/1/4/3/2`)**: for `m > 8`, there is
a constant `C_m ≥ 0` such that for every cell size `c ≥ 1`:
1. every radial profile `f : Profile` with `MemXG f` and `ContinuousOn f (Ioi 0)` has a
   periodization representative `qf : Xmc c m` satisfying
   `xFn qf =ᵐ[volume.restrict (B0579.cell c)] IIIa.periodizeC c (IIIa.planarMode f)`;
2. for any `f, g : Profile` in `MemXG` with `ContinuousOn f (Ioi 0)`, `ContinuousOn g (Ioi 0)`
   and any `qf, qg : Xmc c m` representing their periodizations on `B0579.cell c`,
   `‖qf - qg‖ ≤ C_m * gaussianNorm (fun r => f r - g r)`
   (source lines 3127–3130, 4445–4447: Cauchy-Schwarz on `ℤ` and `B0579.jb x ^ m ≲ e^{|x - nc|²/8}`
   on `B0579.cell c` embed `X_G` boundedly into `X_{m,c}` uniformly in `c ≥ 1`). -/
def PeriodizePlanarModeXmc : Prop :=
  ∀ (m : ℝ) [Fact (1 < m)], 8 < m →
    ∃ C_m : ℝ, 0 ≤ C_m ∧
      ∀ (c : ℝ) [Fact (0 < c)], 1 ≤ c →
        (∀ (f : Profile), MemXG f → ContinuousOn f (Ioi 0) →
          ∃ qf : Xmc c m,
            xFn qf =ᵐ[volume.restrict (B0579.cell c)]
              IIIa.periodizeC c (IIIa.planarMode f)) ∧
        (∀ (f g : Profile), MemXG f → ContinuousOn f (Ioi 0) →
          MemXG g → ContinuousOn g (Ioi 0) →
          ∀ (qf qg : Xmc c m),
            xFn qf =ᵐ[volume.restrict (B0579.cell c)]
              IIIa.periodizeC c (IIIa.planarMode f) →
            xFn qg =ᵐ[volume.restrict (B0579.cell c)]
              IIIa.periodizeC c (IIIa.planarMode g) →
            ‖qf - qg‖ ≤ C_m * gaussianNorm (fun r => f r - g r))

/-- At age `0` with `0 < ν`, `FlatSettingInst.frozenQ κ ν c true 0` is `IIIa.periodizeC c (κ.e 0)`. -/
theorem frozenQ_true_zero_eq_periodizeC (κ : IIIa.PlanarFrameKernels) {ν : ℝ} (hν : 0 < ν)
    (c : ℝ) :
    FlatSettingInst.frozenQ κ ν c true 0 = IIIa.periodizeC c (κ.e 0) := by
  funext x
  have hage : FlatSettingInst.bandAge ν 0 = 0 := by
    unfold FlatSettingInst.bandAge FlatSettingInst.flatSigma
    have hdiv : (0 : ℝ) ≤ 2 / ν := by positivity
    rw [min_eq_left hdiv, max_self]
  have hA : FlatSettingInst.bandA ν 0 = 1 := by
    unfold FlatSettingInst.bandA IIIa.clockA
    rw [hage, mul_zero, add_zero]
  have hD : FlatSettingInst.bandD ν c 0 = c := by
    unfold FlatSettingInst.bandD IIIa.cellLen
    rw [hA, Real.sqrt_one, div_one]
  have hpm : FlatSettingInst.pmIdx true = 0 := rfl
  unfold FlatSettingInst.frozenQ
  rw [hA, hD, hpm]
  unfold IIIa.Jscale IIIa.perE IIIa.perSum IIIa.periodizeC
  rw [Real.one_rpow, Real.sqrt_one, Complex.ofReal_one, one_mul, div_one, div_one]
  have hneg := (Equiv.neg ℤ).tsum_eq (fun n : ℤ => κ.e 0 (x.1 - (n : ℝ) * c, x.2))
  simpa [sub_eq_add_neg] using hneg

/-- The radial profile inside `IIIa.preparedDatum P ν`. -/
def preparedProfile (P : UnforcedLeray.Blueprint.Planar.PlanarData) (ν : ℝ) : Profile :=
  fun r =>
    Complex.exp (P.eigenvalue * ((ν⁻¹ : ℝ) : ℂ)) * ((ν⁻¹ : ℝ) : ℂ) ^ P.kappa *
      P.canonical ν⁻¹ r

theorem preparedDatum_eq_periodizeC (P : UnforcedLeray.Blueprint.Planar.PlanarData) {ν : ℝ}
    (hν : 0 < ν) :
    IIIa.preparedDatum P ν = IIIa.periodizeC (cOf ν) (IIIa.planarMode (preparedProfile P ν)) := by
  unfold IIIa.preparedDatum cOf preparedProfile
  rw [Real.rpow_neg hν.le, Real.rpow_two]

/-- Scalar multiplication preserves `Planar.MemXG`. -/
theorem memXG_const_mul {f : Profile} (hf : MemXG f) (α : ℂ) :
    MemXG (fun r => α * f r) where
  measurable := hf.measurable.const_mul α
  integrable := by
    have heq : (fun r : ℝ =>
        ‖α * f r‖ ^ 2 * UnforcedLeray.Blueprint.Planar.gaussianWeightInv r * r) =
      fun r : ℝ =>
        ‖α‖ ^ 2 * (‖f r‖ ^ 2 * UnforcedLeray.Blueprint.Planar.gaussianWeightInv r * r) := by
      ext r
      rw [norm_mul, mul_pow]
      ring
    rw [heq]
    exact hf.integrable.const_mul (‖α‖ ^ 2)

theorem memXG_preparedProfile {P : UnforcedLeray.Blueprint.Planar.PlanarData}
    (hP : UnforcedLeray.Blueprint.Planar.IsPlanarReference P) {ν : ℝ} (hν : 0 < ν) :
    MemXG (preparedProfile P ν) :=
  memXG_const_mul (hP.canonical.memXG ν⁻¹ (inv_pos.mpr hν))
    (Complex.exp (P.eigenvalue * ((ν⁻¹ : ℝ) : ℂ)) * ((ν⁻¹ : ℝ) : ℂ) ^ P.kappa)

theorem continuousOn_preparedProfile {P : UnforcedLeray.Blueprint.Planar.PlanarData}
    (hP : UnforcedLeray.Blueprint.Planar.IsPlanarReference P) {ν : ℝ} (hν : 0 < ν) :
    ContinuousOn (preparedProfile P ν) (Ioi 0) := by
  have hcan : ContinuousOn (P.canonical ν⁻¹) (Ioi 0) :=
    hP.canonical.smooth.continuousOn.comp
      (Continuous.continuousOn (continuous_const.prodMk continuous_id))
      (fun r (hr : r ∈ Ioi (0 : ℝ)) =>
        (⟨inv_pos.mpr hν, hr⟩ : ((ν⁻¹, r) : ℝ × ℝ) ∈ Ioi 0 ×ˢ Ioi 0))
  exact continuousOn_const.mul hcan

theorem one_le_cOf_of_le_one {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) : 1 ≤ cOf ν := by
  unfold cOf
  rw [one_le_inv₀ (pow_pos hν 2)]
  exact pow_le_one₀ hν.le hν1

theorem gaussianNorm_sub_comm (f g : Profile) :
    gaussianNorm (fun r => f r - g r) = gaussianNorm (fun r => g r - f r) := by
  unfold gaussianNorm
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi (fun r _ => ?_)
  rw [norm_sub_rev]

/-- Conditional assembly of `G3.PreparedDatumCompare D` from `SeedLinkEqPlanarMode D`
and `PeriodizePlanarModeXmc`. -/
theorem preparedDatumCompare_of_leaves (D : SeqData)
    (hSeed : SeedLinkEqPlanarMode D) (hPer : PeriodizePlanarModeXmc) :
    G3.PreparedDatumCompare D := by
  intro dm dp hst κ hκ m hm1 hm
  obtain ⟨C_m, hCm0, hPer_c⟩ := @hPer m hm1 hm
  obtain ⟨C₀, θ₁, hθ₁, hasym⟩ := hst.planar.canonical.asymptotic
  have hC₀_nonneg : 0 ≤ C₀ := by
    have hspec := hasym θ₁ le_rfl
    have hgn : 0 ≤ gaussianNorm (fun r =>
        Complex.exp (D.Pl.eigenvalue * (θ₁ : ℂ)) * (θ₁ : ℂ) ^ D.Pl.kappa *
          D.Pl.canonical θ₁ r - D.Pl.mode r) := Real.sqrt_nonneg _
    have hdiv : 0 ≤ C₀ / θ₁ := hgn.trans hspec
    exact ((div_nonneg_iff.mp hdiv).resolve_right (fun h => by linarith [h.2])).1
  refine ⟨C_m * C₀, min 1 θ₁⁻¹, mul_nonneg hCm0 hC₀_nonneg,
    lt_min zero_lt_one (inv_pos.mpr hθ₁), fun ν hν hν0 => ?_⟩
  have : Fact (0 < cOf ν) := ⟨cOf_pos hν⟩
  intro tr FI
  have hν1 : ν ≤ 1 := hν0.trans (min_le_left _ _)
  have hνθ : ν ≤ θ₁⁻¹ := hν0.trans (min_le_right _ _)
  have hc1 : 1 ≤ cOf ν := one_le_cOf_of_le_one hν hν1
  obtain ⟨hEx, hLip⟩ := @hPer_c (cOf ν) ⟨cOf_pos hν⟩ hc1
  have hY_mem : MemXG (preparedProfile D.Pl ν) := memXG_preparedProfile hst.planar hν
  have hY_cont : ContinuousOn (preparedProfile D.Pl ν) (Ioi 0) :=
    continuousOn_preparedProfile hst.planar hν
  have hmode_mem : MemXG D.Pl.mode := hst.planar.eigenpair.memXG
  have hmode_cont : ContinuousOn D.Pl.mode (Ioi 0) := hst.planar.eigenpair.smooth.continuousOn
  obtain ⟨qc, hqc⟩ := hEx (preparedProfile D.Pl ν) hY_mem hY_cont
  refine ⟨qc, ?_, ?_⟩
  · rw [preparedDatum_eq_periodizeC D.Pl hν]
    exact hqc
  · have hq0_ae : xFn (FI.pair.q true 0) =ᵐ[volume.restrict (B0579.cell (cOf ν))]
        IIIa.periodizeC (cOf ν) (IIIa.planarMode D.Pl.mode) := by
      refine (FI.pair.q_pin true 0).trans ?_
      rw [frozenQ_true_zero_eq_periodizeC κ hν (cOf ν), hSeed dm dp hst κ hκ]
    have hdiff := hLip D.Pl.mode (preparedProfile D.Pl ν) hmode_mem hmode_cont hY_mem hY_cont
      (FI.pair.q true 0) qc hq0_ae hqc
    have hθ_le : θ₁ ≤ ν⁻¹ := by
      rw [← inv_inv θ₁]
      exact inv_anti₀ hν hνθ
    have hasym_ν := hasym ν⁻¹ hθ_le
    rw [div_inv_eq_mul] at hasym_ν
    rw [gaussianNorm_sub_comm] at hdiff
    calc ‖FI.pair.q true 0 - qc‖
        ≤ C_m * gaussianNorm (fun r => preparedProfile D.Pl ν r - D.Pl.mode r) := hdiff
      _ ≤ C_m * (C₀ * ν) := mul_le_mul_of_nonneg_left hasym_ν hCm0
      _ = C_m * C₀ * ν := by ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G3
