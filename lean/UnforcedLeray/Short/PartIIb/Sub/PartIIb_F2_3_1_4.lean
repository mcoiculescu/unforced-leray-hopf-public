import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2_3_1
import UnforcedLeray.Lib.PlanarSpectralB.XGSpectrum
import UnforcedLeray.Cons.C01ReferenceChoice.Adjoint
import UnforcedLeray.Cons.L2.CanonicalBranch.Bridge

/-!
# `PartII-b:F2/3/1/4` (`Sub/PartII-b_F2_3_1_4.lean`): `PlanarSeedIdentification`

Source of record: `the November 2 reference manuscript` (SP) lines 593-602.
Route: a growing pair `(lam, q)` is an eigenvector of `L0` on `X_G` (bridge
`growing_L0_eq`), so the uniqueness of `L0_eigen_unique` (SP 602, rank-one simplicity) gives
equal eigenvalues and proportional eigenvectors; proportionality is transferred from `X_G`
to `volume.restrict (Ioi 0)` by `ae_xG_iff_restrict`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal
open UnforcedLeray

namespace UnforcedLeray.Short.IIb.PlanarSeedAux

open UnforcedLeray.Blueprint.Planar (IsGrowingEigenpair Profile)

/-- `X_G`-almost everywhere statements are equivalent to statements a.e. on `(0, ∞)`. -/
theorem ae_xG_iff_restrict {p : ℝ → Prop} :
    (∀ᵐ x ∂B0010.xGMeasure, p x) ↔ ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), p x := by
  have hmeas : Measurable (fun r : ℝ => (B0010.xGDensity r : ℝ≥0∞)) :=
    B0010.measurable_xGDensity.coe_nnreal_ennreal
  rw [B0010.xGMeasure, ae_withDensity_iff hmeas]
  constructor
  · intro h
    filter_upwards [h, ae_restrict_mem measurableSet_Ioi] with x hx hxpos
    have hpos : 0 < (B0010.radialGaussianWeight x)⁻¹ * x :=
      mul_pos (inv_pos.2 (B0010.radialGaussianWeight_pos x)) hxpos
    have hne : (B0010.xGDensity x : ℝ≥0∞) ≠ 0 := by
      intro h0
      have h1 := B0010.coe_xGDensity hxpos
      have h0' : B0010.xGDensity x = 0 := ENNReal.coe_eq_zero.1 h0
      have h2 : ((B0010.xGDensity x : NNReal) : ℝ) = 0 := by rw [h0']; rfl
      linarith
    exact hx hne
  · intro h
    filter_upwards [h] with x hx _
    exact hx

/-- The `X_G` pairing of Green inverses: `greenN 2` only sees the profile a.e. on `(0, ∞)`. -/
theorem greenN_two_congr {f g : ℝ → ℂ} (h : f =ᵐ[volume.restrict (Ioi (0 : ℝ))] g) (r : ℝ) :
    UnforcedLeray.Planar.greenN 2 f r = UnforcedLeray.Planar.greenN 2 g r := by
  unfold UnforcedLeray.Planar.greenN
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [h] with ρ hρ
  simp only [hρ]

/-- A growing eigenpair is an `L0`-eigenvector in `X_G`. -/
theorem growing_L0_eq (lam : ℂ) (q : Profile) (hq : IsGrowingEigenpair lam q)
    (hmem : MemLp q 2 B0010.xGMeasure) :
    UnforcedLeray.Planar.L0 (hmem.toLp q) = lam • hmem.toLp q := by
  apply Lp.ext
  have hcoe : ⇑(hmem.toLp q) =ᵐ[B0010.xGMeasure] q := hmem.coeFn_toLp
  have hrestr : ⇑(hmem.toLp q) =ᵐ[volume.restrict (Ioi (0 : ℝ))] q :=
    ae_xG_iff_restrict.1 hcoe
  filter_upwards [UnforcedLeray.Planar.coeFn_L0 (hmem.toLp q), hcoe,
    B0012.ae_xG_pos, Lp.coeFn_smul lam (hmem.toLp q)] with r h1 h2 hr h3
  have he := hq.eigen r hr
  unfold UnforcedLeray.Blueprint.Planar.generatorL0 at he
  rw [UnforcedLeray.Cons.C01.vortexOmega_eq, UnforcedLeray.Cons.C01.strainK_eq,
    UnforcedLeray.Cons.C01.greenInverse_eq_R] at he
  rw [h1, h3, greenN_two_congr hrestr r, UnforcedLeray.Planar.greenN_two_eq_R
    (UnforcedLeray.Cons.C01.wprof_of_memXG hq.memXG) hr]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h2]
  exact he

/-- A growing eigenvector in `X_G` is nonzero. -/
theorem growing_toLp_ne_zero (q : Profile) (hq : ¬ q =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0)
    (hmem : MemLp q 2 B0010.xGMeasure) : hmem.toLp q ≠ 0 := by
  intro h
  apply hq
  have h1 : q =ᵐ[B0010.xGMeasure] ⇑(hmem.toLp q) := hmem.coeFn_toLp.symm
  rw [h] at h1
  have h2 : ∀ᵐ x ∂B0010.xGMeasure, q x = 0 := by
    filter_upwards [h1, Lp.coeFn_zero ℂ 2 B0010.xGMeasure] with x a b
    exact a.trans b
  exact ae_xG_iff_restrict.1 h2

end UnforcedLeray.Short.IIb.PlanarSeedAux

open UnforcedLeray.Short.IIb.PlanarSeedAux in
/-- **Leaf (d)**: seed identification (SP 593-602). -/
theorem planarSeedIdentification : UnforcedLeray.Short.IIb.PlanarFrozenF231.PlanarSeedIdentification := by
  intro lam₁ lam₂ q₁ q₂ h₁ h₂
  have hm₁ : MemLp q₁ 2 B0010.xGMeasure := UnforcedLeray.Cons.G3b.memLp_of_memXG h₁.memXG
  have hm₂ : MemLp q₂ 2 B0010.xGMeasure := UnforcedLeray.Cons.G3b.memLp_of_memXG h₂.memXG
  have e₁ := growing_L0_eq lam₁ q₁ h₁ hm₁
  have e₂ := growing_L0_eq lam₂ q₂ h₂ hm₂
  have n₁ := growing_toLp_ne_zero q₁ h₁.nonzero hm₁
  have n₂ := growing_toLp_ne_zero q₂ h₂.nonzero hm₂
  obtain ⟨hl, μ, hμ⟩ := UnforcedLeray.Planar.L0_eigen_unique h₁.re_pos h₂.re_pos e₁ e₂ n₁ n₂
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    apply n₂
    rw [hμ, zero_smul]
  have A : ∀ᵐ x ∂B0010.xGMeasure, q₂ x = μ * q₁ x := by
    filter_upwards [hm₂.coeFn_toLp, hm₁.coeFn_toLp, Lp.coeFn_smul μ (hm₁.toLp q₁)]
      with x a b c
    rw [← a, hμ, c, Pi.smul_apply, smul_eq_mul, b]
  have B : ∀ᵐ x ∂B0010.xGMeasure, q₁ x = μ⁻¹ * q₂ x := by
    filter_upwards [A] with x hx
    rw [hx, ← mul_assoc, inv_mul_cancel₀ hμ0, one_mul]
  refine ⟨hl.symm, μ⁻¹, inv_ne_zero hμ0, ?_⟩
  exact ae_xG_iff_restrict.1 B
