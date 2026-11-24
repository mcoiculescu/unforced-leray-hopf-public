import UnforcedLeray.Short.PartI.StatementsSeed

/-!
# Part I, task `PartI:S15` (`SeedEulerComplement`, `j = 0`): decomposition

Source: `the November 2 reference manuscript`
lines 612-615 and 841-889.

* `SectorOneStableAll` (leaf `PartI:S15/1`): `Planar.SectorOneStable hM` for all `M > 1`, from
  `ComplexODEC.sector_one_eigen_eq_zero` (sector `1`) and the conjugation `star` for sector `-1`.
* `SeedGrowProjAgree` (leaf `PartI:S15/2`): identification of the Riesz projection of
  `Planar.eulerSemigroup_complement_bound` with the explicit `seedProjFun` (lines 841-889, S09, S01).
* `XjM0Bridge` (leaf `PartI:S15/3`): `𝒳_{0,M}` and `Planar.X0` have the same elements and norms.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ComplexConjugate ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Infra.Dunford (IsSimpleSpectralProj rankOneProj)

/-- Leaf `PartI:S15/1` (line 1350-1356 of the older numbering is `sector_one_eigen_eq_zero`;
source 841-889): the sectors `n = ±1` of `𝓛` carry no eigenvector with `Re z > 0`. -/
def SectorOneStableAll : Prop := ∀ (M : ℝ) (hM : 1 < M), Planar.SectorOneStable hM

/-- Leaf `PartI:S15/2` (source 841-889, 603-607).  For a seed triple, the growing eigenvector
`q' = e q ∈ ProfL2 M` (`PartI:S01` `exists_xgEmbM`, `Lsec hM 2 q' = λ q'`, `q' ≠ 0`) is such that
every pair of simple spectral functionals `ℓ₂, ℓm` with `ℓ₂ q' = 1`, `ℓm (star q') = 1` and
`IsSimpleSpectralProj` (sectors `2`, `-2`, eigenvalues `λ`, `conj λ`) gives a growing projection
agreeing a.e. with `seedProjFun h` on every function `F` a.e. equal to the element
(`ℓ₂ (f₂) = seedEll h f₂` by uniqueness of the Riesz projection of a simple isolated eigenvalue and
`PartI:S09`; sector `-2` by `star`; `seedProjFun h F` depends only on the a.e. class of `F` since
`angularSector F n r` depends on a.e. angle for a.e. `r` by Fubini). -/
def SeedGrowProjAgree : Prop :=
  ∀ (lam : ℂ) (h : ℝ → ℂ) (hh : MemLp h 2 B0010.xGMeasure) (ℓ : B0010.XG →L[ℂ] ℂ),
    IsSeedXG lam (hh.toLp h) ℓ → ∀ (M : ℝ) (hM : 1 < M),
      ∃ q' : Planar.ProfL2 M, q' ≠ 0 ∧ Planar.Lsec hM 2 q' = lam • q' ∧
        ∀ (ℓ₂ ℓm : Planar.ProfL2 M →L[ℂ] ℂ), ℓ₂ q' = 1 → ℓm (star q') = 1 →
          IsSimpleSpectralProj (Planar.Lsec hM 2) (rankOneProj ℓ₂ q') lam →
          IsSimpleSpectralProj (Planar.Lsec hM (-2)) (rankOneProj ℓm (star q'))
            ((starRingEnd ℂ) lam) →
          ∀ (f : Planar.X0 hM) (F : ℂ → ℂ), ⇑((f : Planar.X0 hM) : Planar.L2w M) =ᵐ[volume] F →
            ⇑((Planar.growingProj hM (rankOneProj ℓ₂ q') (rankOneProj ℓm (star q')) f :
              Planar.X0 hM) : Planar.L2w M) =ᵐ[volume] fun y => seedProjFun h F y

/-- Leaf `PartI:S15/3` (`HjM 0 M`: tuple of order-`0` derivatives, so the norm is the `L²_M` norm;
`mem_XjM_iff`, `HjM.valueCLM`): every element of `𝒳_{0,M}` is a.e. the value of an element of
`Planar.X0` of the same norm, and conversely. -/
def XjM0Bridge : Prop :=
  ∀ (M : ℝ) (hM : 1 < M),
    (∀ f : B0008.XjM 0 M, ∃ f' : Planar.X0 hM,
      ⇑((f' : Planar.X0 hM) : Planar.L2w M) =ᵐ[volume] xValue f ∧ ‖f'‖ = ‖f‖) ∧
    (∀ g' : Planar.X0 hM, ∃ g : B0008.XjM 0 M,
      xValue g =ᵐ[volume] ⇑((g' : Planar.X0 hM) : Planar.L2w M) ∧ ‖g‖ = ‖g'‖)

theorem seedEulerComplement_zero_of (h1 : SectorOneStableAll) (hA : SeedGrowProjAgree)
    (hB : XjM0Bridge) :
    ∀ (lam : ℂ) (h : ℝ → ℂ) (hh : MemLp h 2 B0010.xGMeasure) (ℓ : B0010.XG →L[ℂ] ℂ),
      IsSeedXG lam (hh.toLp h) ℓ → ∀ (M : ℝ) (hM : 1 < M) (η : ℝ), 0 < η →
        ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t → ∀ f : B0008.XjM 0 M,
          ∃ (u : Planar.L2w M) (g : B0008.XjM 0 M),
            (⇑u =ᵐ[volume] fun y => xValue f y - seedProjFun h (xValue f) y) ∧
            xValue g =ᵐ[volume] ⇑(Planar.eulerGroupW hM t u) ∧
            ‖g‖ ≤ C * Real.exp (η * t) * ‖f‖ := by
  intro lam h hh ℓ hs M hM η hη
  obtain ⟨q', hq0, hq, hAg⟩ := hA lam h hh ℓ hs M hM
  obtain ⟨ℓ₂, ℓm, h2, hm, hP2, hPm, hbound⟩ :=
    Planar.eulerSemigroup_complement_bound hM (h1 M hM) hs.re_pos hq0 hq
  obtain ⟨C, hC, hCb⟩ := hbound η hη
  refine ⟨C, hC, fun t ht f => ?_⟩
  obtain ⟨f', hf'v, hf'n⟩ := (hB M hM).1 f
  set gp := Planar.growingProj hM (rankOneProj ℓ₂ q') (rankOneProj ℓm (star q')) with hgp
  set u' : Planar.X0 hM := f' - gp f' with hu'
  obtain ⟨g, hgv, hgn⟩ := (hB M hM).2 (Planar.eulerSemigroup hM t u')
  refine ⟨((u' : Planar.X0 hM) : Planar.L2w M), g, ?_, ?_, ?_⟩
  · have hag := hAg ℓ₂ ℓm h2 hm hP2 hPm f' (xValue f) hf'v
    have key : ∀ a b : Planar.L2w M, ⇑(a - b) =ᵐ[volume] fun y => a y - b y := fun a b =>
      (Planar.volume_ac M).ae_le (Lp.coeFn_sub a b)
    have hsub : ⇑((u' : Planar.X0 hM) : Planar.L2w M) =ᵐ[volume]
        fun y => ((f' : Planar.X0 hM) : Planar.L2w M) y - ((gp f' : Planar.X0 hM) : Planar.L2w M) y :=
      key _ _
    filter_upwards [hsub, hag, hf'v] with y h1 h2 h3
    rw [h1, h2, h3]
  · refine hgv.trans ?_
    exact Filter.EventuallyEq.of_eq rfl
  · rw [hgn]
    calc ‖Planar.eulerSemigroup hM t u'‖
        ≤ ‖Planar.eulerSemigroup hM t ∘L (1 - gp)‖ * ‖f'‖ := by
          have : Planar.eulerSemigroup hM t u' = (Planar.eulerSemigroup hM t ∘L (1 - gp)) f' := by
            simp [hu', sub_eq_add_neg]
          rw [this]; exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ C * Real.exp (η * t) * ‖f‖ := by
          rw [← hf'n]
          exact mul_le_mul_of_nonneg_right (hCb t ht) (norm_nonneg _)

end UnforcedLeray.Short.PartI
