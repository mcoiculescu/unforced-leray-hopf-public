import UnforcedLeray.Short.Spine.Proofs.BallB3Output
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.StreamSmooth

/-!
# Contraction-ball slice regularity helper for `PartIII-b:IIIb-D5/bridge`

Source of record: `the November 2 reference manuscript`, lines 2505-2561,
2607-2612, 2641-2642.

Packages the Part II-b contraction-ball outputs (`IIb.ballHeatRemainder_proof`,
`IIb.strongAllOrders_of`, `_root_.bgComovingFirstEquation_proof`, and
`IIb.smoothLeraySliceRegularity_proof`) with `RieszLp.lerayLp_toLp_ae_eq_projection` into a
pure `SpatialField` statement before importing `PartIII-b.Proofs.Wiring.Inputs`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.Wiring.ShortBgExactProfileAux

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Blueprint.Planar

local instance fact_one_le_four_ball : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

private theorem top_ne_zero_ball : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by decide

private theorem memLp_of_ae_coeFn_ball {p : ℝ≥0∞} [Fact (1 ≤ p)] {f : SpatialField}
    {L : Lp Space p (volume : Measure Space)} (h : f =ᵐ[volume] (L : SpatialField)) :
    MemLp f p volume :=
  (Lp.memLp L).ae_eq h.symm

private theorem leray_convect_slice
    {U : ℝ → SpatialField}
    (hF2 : ∀ τ : ℝ, MemLp (fun y => fderiv ℝ (U τ) y (U τ y)) 2 volume)
    (hConv : IIb.IsUniformSmoothL4SliceFamily
      (fun τ => IIb.spatialConvect (U τ) (U τ)))
    (τ : ℝ) :
    MemLp (fun y => fderiv ℝ (U τ) y (U τ y)) 4 volume ∧
      MemLp (IIb.smoothConvectiveLeray U U τ) 2 volume ∧
      MemLp (IIb.smoothConvectiveLeray U U τ) 4 volume ∧
      IIb.smoothConvectiveLeray U U τ =ᵐ[volume]
        ⇑(Leray.projection (toL2 (fun y => fderiv ℝ (U τ) y (U τ y)))) := by
  obtain ⟨hF4, -, hGaeτ⟩ := (IIb.smoothLeraySliceRegularity_proof.1 _ hConv).1 τ
  have hL4 : MemLp (IIb.smoothConvectiveLeray U U τ) 4 volume :=
    memLp_of_ae_coeFn_ball hGaeτ
  have hPproj := RieszLp.lerayLp_toLp_ae_eq_projection (p := 4)
    (by norm_num) (by norm_num) hF4 (hF2 τ)
  have hLae : IIb.smoothConvectiveLeray U U τ =ᵐ[volume]
      ⇑(Leray.projection (toL2 (fun y => fderiv ℝ (U τ) y (U τ y)))) :=
    hGaeτ.trans hPproj
  have hL2 : MemLp (IIb.smoothConvectiveLeray U U τ) 2 volume :=
    memLp_of_ae_coeFn_ball hLae
  exact ⟨hF4, hL2, hL4, hLae⟩

theorem ballState_evol
    {Sig : ℝ} {lam : ℂ} {q : Profile} (hSig : 0 < Sig) (hq : IsGrowingEigenpair lam q)
    {m dm dp : ℝ} (hm : 0 < m) (hdm : 0 < dm) (h2m : 2 * m < 3 * dm / 11)
    (C₁ : ℝ) (k₁ : ℕ) (hC₁ : 0 < C₁) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧
      ∀ (p : Cons.C03.Concrete.Params) (d : ℝ),
        IIb.BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
        ∀ z : p.Z, IIb.ProjectedEquation p z →
        ‖z‖ ≤ C₁ * (p.ν ^ k₁)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) →
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => IIb.bgField p z x.1 x.2) →
        (∃ Cu : ℝ, ∀ τ : ℝ,
          eLpNorm (IIb.bgField p z τ) 4 volume ≤ ENNReal.ofReal Cu ∧
          eLpNorm (fun y => fderiv ℝ (IIb.bgField p z τ) y) 4 volume ≤ ENNReal.ofReal Cu ∧
          eLpNorm (fun y => iteratedFDeriv ℝ 2 (IIb.bgField p z τ) y) 4 volume ≤
            ENNReal.ofReal Cu) ∧
        (∀ τ : ℝ, MemLp (fun y => fderiv ℝ (IIb.bgField p z τ) y (IIb.bgField p z τ y)) 2 volume) ∧
        (∀ τ : ℝ, MemLp (fun y => fderiv ℝ (IIb.bgField p z τ) y (IIb.bgField p z τ y)) 4 volume) ∧
        ∃ L : ℝ → SpatialField,
          (∀ τ : ℝ, MemLp (L τ) 2 volume) ∧
          (∀ τ : ℝ, MemLp (L τ) 4 volume) ∧
          (∀ τ : ℝ, L τ =ᵐ[volume]
            ⇑(Leray.projection
              (toL2 (fun y => fderiv ℝ (IIb.bgField p z τ) y (IIb.bgField p z τ y))))) ∧
          (∀ τ y,
            deriv (fun t => IIb.bgField p z t y) τ -
                (1 / 2 : ℝ) • fderiv ℝ (IIb.bgField p z τ) y y =
              p.ν • IIb.spatialLaplacian (IIb.bgField p z τ) y +
                (1 / 2 : ℝ) • IIb.bgField p z τ y - L τ y) := by
  have h4 := IIb.affineInletFacts_proof
  have hQ1 := IIb.quadBound_of h4
  have hS1 := _root_.strongFirstDerivative_of h4 hQ1
  have hS2 := IIb.strongAllOrders_of h4 hQ1 hS1
  obtain ⟨ν₁, hν₁, HB3⟩ :=
    IIb.ballHeatRemainder_proof Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₃, hν₃, HS2⟩ :=
    hS2 Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₄, hν₄, HC⟩ :=
    _root_.bgComovingFirstEquation_proof Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  refine ⟨min ν₁ (min ν₃ ν₄), lt_min hν₁ (lt_min hν₃ hν₄),
    fun p d hreg hν hS hq' z hz hzn hsmooth => ?_⟩
  have hν₁' : p.ν ≤ ν₁ := hν.trans (min_le_left _ _)
  have hν₃' : p.ν ≤ ν₃ := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν₄' : p.ν ≤ ν₄ := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hUL4, -, hEvol⟩ := HB3 p d hreg hν₁' hS hq' z hz hzn
  obtain ⟨hgrad, hslice, hRaw, hInlet⟩ := HS2 p d hreg hν₃' hS hq' z hz hzn
  have hfam : IIb.IsUniformSmoothL4SliceFamily (IIb.bgField p z) :=
    IIb.isUniformSmoothL4SliceFamily_bgField_of_morreyL4
      (IIb.smoothMorreyL4Bound_of_field IIb.smoothMorreyL4FieldBound_proof) p z hslice
  have hCom := HC p d hreg hν₄' hS hq' z hz hzn hgrad hslice hfam hRaw hInlet
  have hConv : IIb.IsUniformSmoothL4SliceFamily
      (fun τ => IIb.spatialConvect (IIb.bgField p z τ) (IIb.bgField p z τ)) :=
    IIb.HigherPhaseSub.sliceFamily_spatialConvect hfam hfam
  have hF2 : ∀ τ : ℝ,
      MemLp (fun y => fderiv ℝ (IIb.bgField p z τ) y (IIb.bgField p z τ y)) 2 volume :=
    fun τ => (hEvol τ).1
  have hLC := leray_convect_slice hF2 hConv
  refine ⟨hUL4, hF2, fun τ => (hLC τ).1,
    ⟨IIb.smoothConvectiveLeray (IIb.bgField p z) (IIb.bgField p z),
      fun τ => (hLC τ).2.1, fun τ => (hLC τ).2.2.1, fun τ => (hLC τ).2.2.2,
      fun τ y => ?_⟩⟩
  have h1 := IIb.B3EvolAux.hasDerivAt_comoving
    (hsmooth.differentiable top_ne_zero_ball (τ, y))
  have h2 := hCom [] τ y
  simp only [IIb.dirSpatialJet_nil, List.length_nil, Nat.cast_zero, zero_div, zero_smul,
    add_zero] at h2
  exact h1.unique h2

end UnforcedLeray.Short.PartIIIb.Concrete.Wiring.ShortBgExactProfileAux

end
