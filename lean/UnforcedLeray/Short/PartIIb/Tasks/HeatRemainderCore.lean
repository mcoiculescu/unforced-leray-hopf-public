import UnforcedLeray.Short.PartIIb.Sub.B3
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_B3_2
import UnforcedLeray.Short.PartIIb.Compose
import UnforcedLeray.Short.PartIIb.Tasks.DatumFacts
import UnforcedLeray.Short.PartIIb.Tasks.HeatRemainderH2
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison
import UnforcedLeray.Short.PartIIb.Tasks.QuadraticEstimate
import UnforcedLeray.Short.PartIIb.Tasks.StrongFirstDerivative
import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder
import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth
import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth.FirstOrderPhaseDeriv.MorreyL4
import UnforcedLeray.Loc.L01Coefficient.HeatPeriodic

/-!
# `PartII-b:B3/2`: the clauses of Theorem B3 at the contraction-ball states (SP 2563-2628)

Source of record: `the November 2 reference manuscript`, lines 2563-2628.

`B3Stmt.Core p z` asks for a path `Q : ℝ → H²` with `Blueprint.IsB3Core ν P a U Q`, where
`U = bgField p z` (SP 2519-2524), `a = p.datum (p.coord z)` (SP 2565-2583), `P = p.period`.
The clauses come from three places.

* **The datum** (SP 2563-2583): smooth off `0`, solenoidal, nonzero, DSS with factor `e^{P/2}`,
  `|D^ka| ≤ C|x|^{-1-k}` (`k ≤ 4`), axisymmetric without swirl.  This is `PartII-b:B2`
  (`datum_facts_atBallStates`, proved).
* **The background** (`short-bg:strong` and all spatial orders, SP 2525-2562): from
  `StrongAllOrders` (`PartII-b:S2`): the joint smoothness of `U` (`PartII-b:S3/1`,
  `jointSmoothnessFromSpatialAllOrders_proof`, proved) gives the measurability; the uniform
  `C_τ W^{k,4}` bounds and the Morrey inequality (`PartII-b:S3/1/1/1`,
  `smoothMorreyL4FieldBound_proof`, proved) give `U`, `DU` bounded; periodicity, solenoidality
  and symmetry are `bgField_periodic_solenoidal_symmetric` (with `P ≤ 1` for small `ν`,
  `period_le_one_of`).
* **The heat remainder** (SP 2584-2628): `Q = U − H_a ∈ C_per H²`.  The source proves it in two
  steps: the raw-heat comparison `V − H_a ∈ C_per H^k ∩ X_p` (`short-bg:raw-heat`, SP 2586-2603)
  puts `Q = (V − H_a) + w` in `X_p`, and `Q` solves `A₀Q = −𝐏 div 𝕋` with `𝕋 = U ⊗ U ∈ C_per H²`,
  so free uniqueness gives the Duhamel formula `Q = −∫₀^∞ S₀(t)𝐏 div 𝕋(τ − t) dt` whose majorants
  (SP 2622-2628) put `Q ∈ C_per H²`.  This analytic step is the open leaf `BallRemainderH2`
  (a continuous path `Q : ℝ → H²` representing `U − H_a`); the periodicity of `Q` is proved
  here from that of `U` and of `H_a` (`heatProfile_add_period`, the DSS identity of `a`).

Main result: `ballHeatRemainder_Core_of (hS2 : StrongAllOrders) (hR : BallRemainderH2) :
B3Stmt.AtBallStates B3Stmt.Core`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete

namespace B3CoreAux

/-- A continuous `H²` path representing `U − H_a` is periodic when `U` and `H_a` are. -/
theorem remainder_periodic {ν P : ℝ} (hν : 0 < ν) {a : SpatialField} {U : ℝ → SpatialField}
    (hU : Function.Periodic U P)
    (hdss : ∀ x : Space, x ≠ 0 → a (Real.exp (P / 2) • x) = Real.exp (-(P / 2)) • a x)
    {Q : ℝ → UnforcedLeray.SobolevGraph.H2}
    (hQ : ∀ τ : ℝ, ((Q τ).value : SpatialField) =ᵐ[volume]
      U τ - UnforcedLeray.Blueprint.heatProfile ν a τ) :
    Function.Periodic Q P := by
  intro τ
  apply UnforcedLeray.SobolevGraph.H2.ext
  apply Lp.ext
  have h1 := hQ (τ + P)
  have hH : UnforcedLeray.Blueprint.heatProfile ν a (τ + P) =
      UnforcedLeray.Blueprint.heatProfile ν a τ :=
    funext fun y => UnforcedLeray.Blueprint.L01.heatProfile_add_period hν hdss τ y
  rw [hU τ, hH] at h1
  exact h1.trans (hQ τ).symm

end B3CoreAux

/-- **`PartII-b:B3/2` from `StrongAllOrders` and the heat-remainder leaf** (SP 2563-2628): at
every state `z` of the contraction ball there is `Q : ℝ → H²` with
`Blueprint.IsB3Core p.ν p.period (p.datum (p.coord z)) (bgField p z) Q`.  Datum clauses:
`PartII-b:B2`; background clauses: `StrongAllOrders` (`PartII-b:S2`) with the proved joint
smoothness (`PartII-b:S3/1`) and Morrey inequality (`PartII-b:S3/1/1/1`); remainder:
`BallRemainderH2`, periodic by `B3CoreAux.remainder_periodic`. -/
theorem ballHeatRemainder_Core_of (hS2 : StrongAllOrders) (hR : BallRemainderH2) :
    B3Stmt.AtBallStates B3Stmt.Core := by
  intro Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₁, hν₁, HS2⟩ := hS2 Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₂, hν₂, HJ⟩ :=
    jointSmoothnessFromSpatialAllOrders_proof Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₃, hν₃, HD⟩ := datum_facts_atBallStates Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₄, hν₄, HR⟩ := hR Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₅, hν₅, hper⟩ := poly_exp_small 2 dm 2 hdm
  refine ⟨min (min ν₁ ν₂) (min ν₃ (min ν₄ ν₅)),
    lt_min (lt_min hν₁ hν₂) (lt_min hν₃ (lt_min hν₄ hν₅)),
    fun p d hreg hν hS hq' z hz hzn => ?_⟩
  have hν₁' : p.ν ≤ ν₁ := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν₂' : p.ν ≤ ν₂ := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν₃' : p.ν ≤ ν₃ := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν₄' : p.ν ≤ ν₄ :=
    hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hν₅' : p.ν ≤ ν₅ :=
    hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨hgrad, hslice, hRaw, hInlet⟩ := HS2 p d hreg hν₁' hS hq' z hz hzn
  have hsmooth : ContDiff ℝ ∞ (fun x : ℝ × Space => bgField p z x.1 x.2) :=
    HJ p d hreg hν₂' hS hq' z hz hzn hgrad hslice hRaw hInlet
  have hP1 : p.period ≤ 1 := period_le_one_of hreg (hper p.ν p.ν_pos hν₅')
  obtain ⟨hperU, hsolU, hsymU⟩ := bgField_periodic_solenoidal_symmetric p hP1 z hRaw hInlet
  obtain ⟨hD, -, -, -⟩ := HD p d hreg hν₃' hS hq' z hz hzn
  obtain ⟨Q, hQc, hQ⟩ := HR p d hreg hν₄' hS hq' z hz hzn
  have hfam : IsUniformSmoothL4SliceFamily (bgField p z) :=
    isUniformSmoothL4SliceFamily_bgField_of_morreyL4
      (smoothMorreyL4Bound_of_field smoothMorreyL4FieldBound_proof) p z hslice
  obtain ⟨M₀, hM₀⟩ := hfam.iteratedFDeriv_bounded 0
  obtain ⟨M₁, hM₁⟩ := hfam.iteratedFDeriv_bounded 1
  have hbdd : UnforcedLeray.Blueprint.IsBoundedBackground (bgField p z) :=
    { measurable := hsmooth.continuous.aestronglyMeasurable
      differentiable := fun τ => (hfam.slice_contDiff 1 τ).differentiable (by norm_num)
      bounded := ⟨max M₀ M₁, fun τ y => ⟨?_, ?_⟩⟩ }
  · refine ⟨Q,
      { datum_smooth := hD.smooth
        datum_solenoidal := hD.solenoidal
        datum_nonzero := hD.nonzero
        datum_dss := hD.dss
        datum_bounds := hD.bounds
        datum_symmetric := hD.symmetric
        background_bounded := hbdd
        background_periodic := hperU
        background_solenoidal := hsolU
        background_symmetric := hsymU
        remainder := hQ
        remainder_continuous := hQc
        remainder_periodic := B3CoreAux.remainder_periodic p.ν_pos hperU hD.dss hQ }⟩
  · have h := hM₀ τ y
    rw [norm_iteratedFDeriv_zero] at h
    exact h.trans (le_max_left _ _)
  · have h := hM₁ τ y
    rw [norm_iteratedFDeriv_one] at h
    exact h.trans (le_max_right _ _)

/-- Unconditional `PartII-b:B3/2`: `ballHeatRemainder_Core_of` instantiated with the accepted
`StrongAllOrders` proof (`PartII-b:S2`) and `ballRemainderH2_proof` (`PartII-b:B3/2/1`). -/
theorem ballHeatRemainder_Core :
    UnforcedLeray.Short.IIb.B3Stmt.AtBallStates UnforcedLeray.Short.IIb.B3Stmt.Core := by
  have h4 := affineInletFacts_proof
  have hQ1 := quadBound_of h4
  have hS2 := strongAllOrders_of h4 hQ1 (_root_.strongFirstDerivative_of h4 hQ1)
  exact ballHeatRemainder_Core_of hS2 ballRemainderH2_proof

end UnforcedLeray.Short.IIb
