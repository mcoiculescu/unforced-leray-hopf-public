import UnforcedLeray.Short.PartIIb.Sub.ComparisonAndStrongDesign

/-!
# `PartII-b:S3` decomposition (`Sub/PartII-b_S3.lean`, SP 2525-2562)

Source of record: `the November 2 reference manuscript`
(SP), lines 2525-2562.

Isolates the spacetime time-derivative regularity upgrade `JointSmoothnessFromSpatialAllOrders`
(SP 2559-2562: "On positive physical-time compact intervals the resulting `C_τ W^{k,4}` regularity
and the projected equation give all time derivatives, so `U` is jointly smooth through the axis")
and proves the conditional assembly `strongRegularity_of_jointSmooth` combining
`StrongFirstDerivative` (`PartII-b:S1`, SP 2525-2541), `StrongAllOrders` (`PartII-b:S2`,
SP 2541-2559), `period_le_one_of`, and `bgField_periodic_solenoidal_symmetric`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03 UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace
  UnforcedLeray.B0411 UnforcedLeray.B0412 UnforcedLeray.Blueprint

/-- **`PartII-b:S3/1` (`JointSmoothnessFromSpatialAllOrders`)**
(`the November 2 reference manuscript`,
lines 2559-2562): from the projected equation `ProjectedEquation p z` (`A_0 U + 𝔓(U · ∇U) = 0`,
SP 2519-2523) and the all-order spatial regularity and uniform `L⁴` bounds of `StrongAllOrders`
(SP 2541-2559: all order-`k` distributional spatial derivatives of `w` lie in the maximal graph
`D_p = B0411.D p.period p.ν q0E`, every phase slice `bgField p z τ` is `C^k` on `ℝ³` with
`D^k(p.corr z τ)` uniformly bounded and `D^k(bgField p z τ)` uniformly bounded in `L⁴(ℝ³)`, and
`p.raw`, `p.inlet i` are smooth bounded solenoidal fields), on positive physical-time compact
intervals the resulting `C_τ W^{k,4}` regularity and the projected equation give all time
derivatives, so `U(τ, y) = bgField p z τ y` is jointly smooth (`ContDiff ℝ ∞`) on `ℝ × ℝ³`. -/
def JointSmoothnessFromSpatialAllOrders : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ m : ℝ, 0 < m → ∀ dm dp : ℝ, 0 < dm → 2 * m < 3 * dm / 11 → ∀ (C₁ : ℝ) (k₁ : ℕ), 0 < C₁ →
    ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ z : p.Z, ProjectedEquation p z →
      ‖z‖ ≤ C₁ * (p.ν ^ k₁)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) →
      (∀ k : ℕ, ∃ g : (Fin k → Fin 3) → B0411.D p.period p.ν q0E,
        IsIteratedPhaseGrad p.period q0E k (p.wOf z) (fun α => (g α : Yq p.period q0E))) →
      (∀ k : ℕ, ∃ M : ℝ, ∀ τ : ℝ, ContDiff ℝ k (bgField p z τ) ∧
        (∀ y : Space, ‖iteratedFDeriv ℝ k (p.corr z τ) y‖ ≤ M) ∧
        eLpNorm (fun y => iteratedFDeriv ℝ k (bgField p z τ) y) 4 volume ≤ ENNReal.ofReal M) →
      (IsBoundedBackground p.raw ∧ ∀ τ, IsSolenoidal (p.raw τ)) →
      (∀ i : Fin 2, IsBoundedBackground (p.inlet i) ∧ ∀ τ, IsSolenoidal (p.inlet i τ)) →
      ContDiff ℝ ∞ (fun x : ℝ × Space => bgField p z x.1 x.2)

/-- Conditional assembly of `StrongRegularity` (`PartII-b:S3`, SP 2525-2562) from
`JointSmoothnessFromSpatialAllOrders` (`PartII-b:S3/1`), `StrongFirstDerivative` (`PartII-b:S1`),
and `StrongAllOrders` (`PartII-b:S2`). -/
theorem strongRegularity_of_jointSmooth
    (hJoint : JointSmoothnessFromSpatialAllOrders)
    (hS1 : UnforcedLeray.Short.IIb.StrongFirstDerivative)
    (hS2 : UnforcedLeray.Short.IIb.StrongAllOrders) :
    UnforcedLeray.Short.IIb.StrongRegularity := by
  intro Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨C₂, k₂, ν₁, hC₂, hν₁, HS1⟩ := hS1 Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₂, hν₂, HS2⟩ := hS2 Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₃, hν₃, HJoint⟩ := hJoint Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₄, hν₄, hper⟩ := poly_exp_small 2 dm 2 hdm
  set ν₀ : ℝ := min (min ν₁ ν₂) (min ν₃ ν₄)
  have hν₀ : 0 < ν₀ := lt_min (lt_min hν₁ hν₂) (lt_min hν₃ hν₄)
  refine ⟨C₂, k₂, ν₀, hC₂, hν₀, ?_⟩
  intro p d hreg hν hSg hmode z hproj hz
  have hν₁' : p.ν ≤ ν₁ := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν₂' : p.ν ≤ ν₂ := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν₃' : p.ν ≤ ν₃ := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν₄' : p.ν ≤ ν₄ := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hP1 : p.period ≤ 1 := period_le_one_of hreg (hper p.ν p.ν_pos hν₄')
  obtain ⟨_, hcorr_w1, hcorr_lp, hinlet_w1⟩ := HS1 p d hreg hν₁' hSg hmode z hproj hz
  obtain ⟨hgrad_k, hspace_k, hRaw, hInlet⟩ := HS2 p d hreg hν₂' hSg hmode z hproj hz
  have hsmooth : ContDiff ℝ ∞ (fun x : ℝ × Space => bgField p z x.1 x.2) :=
    HJoint p d hreg hν₃' hSg hmode z hproj hz hgrad_k hspace_k hRaw hInlet
  obtain ⟨hper_bg, hsol_bg, hsym_bg⟩ :=
    bgField_periodic_solenoidal_symmetric p hP1 z hRaw hInlet
  exact ⟨hsmooth, hper_bg, hsol_bg, hsym_bg, hcorr_w1, hcorr_lp, hinlet_w1⟩

end UnforcedLeray.Short.IIb

end
