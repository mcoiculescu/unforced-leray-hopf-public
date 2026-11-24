import UnforcedLeray.Short.PartIIb.Sub.B3
import UnforcedLeray.Short.PartIIb.Tasks.HeatRemainderUL4
import UnforcedLeray.Short.PartIIb.Tasks.DatumFacts
import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth
import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth.FirstOrderPhaseDeriv.MorreyL4
import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth.FirstOrderPhaseDeriv.PhaseDerivStep.ComovingEquation
import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth.HigherOrderPhaseDeriv.SmoothLeraySlice
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_8_1.Org
import UnforcedLeray.Lib.LerayLp.Leray

/-!
# `PartII-b:B3/3`: the evolution of the heat remainder at the contraction-ball states (SP 2610-2632)

Source of record: `the November 2 reference manuscript`, lines 2610-2632:
"`𝕋 = U ⊗ U ∈ C_per H²`.  The field `Q = U − H_a ∈ X_p` solves `A₀Q = −𝐏 div 𝕋`" and
"`(∂_τ − y·∇/2)Q = νΔQ + Q/2 − 𝐏 div 𝕋 ∈ C_per L²`", with `D₀H_a = 0` (SP 2614-2617, the free
semigroup) and the projected equation `A₀U + 𝐏(U·∇U) = 0` (SP 2519-2523).

`B3Stmt.Evol p z` asks, at every phase `τ`, for `U·∇U ∈ L²` and
`∂_τW − ½ y·∇W − νΔW − ½W = −𝐏(U·∇U)` a.e. for `W = U − H_a`, `U = bgField p z`,
`a = p.datum (p.coord z)`, `𝐏 = Leray.projection` on `L²`.  The proof:

* `U·∇U ∈ L²`: Hölder from `U, DU ∈ L⁴` (`StrongAllOrders`, orders `0, 1`;
  `prodL2OfL4_proved`).
* `D₀U = −𝐏(U·∇U)` pointwise, with the smooth `L⁴` Leray representative: the projected equation
  along comoving rays, `T₀U = νΔU + ½U − 𝐏(U·∇U)` (`bgComovingFirstEquation_proof`,
  `PartII-b:S3/1/1/2/1`, proved, whose premises are `StrongAllOrders` and the Morrey slice family
  `isUniformSmoothL4SliceFamily_bgField_of_morreyL4`), read at the empty jet; the joint smoothness
  of `U` (`jointSmoothnessFromSpatialAllOrders_proof`, proved) splits the comoving derivative
  `d/dt U(τ + t, e^{-t/2}y)|₀` into `∂_τU − ½ DU(y)[y]` (`hasDerivAt_comoving`).
* `D₀H_a = 0` (`heatProfileDmuZero_proved`) for the datum in the inverse-distance class (the
  bounds of `PartII-b:B2`, `datum_facts_atBallStates`), so `D₀(U − H_a) = D₀U`
  (`Ward1381Org.physDmu_sub`).
* The smooth `L⁴` Leray representative of `U·∇U` (`smoothLeraySliceRegularity_proof`,
  `IsSmoothLerayRep`) agrees a.e. with the `L²` Leray projection on `L⁴ ∩ L²`
  (`RieszLp.lerayLp_toLp_ae_eq_projection`).

Main result: `ballHeatRemainder_Evol_of (hS2 : StrongAllOrders) : B3Stmt.AtBallStates B3Stmt.Evol`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete
open UnforcedLeray.Short.PartIIIb.Concrete (physDmu physLap heatProfileDmuZero_proved
  prodL2OfL4_proved)

local instance fact_one_le_four_b3evol : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

namespace B3EvolAux

/-- The comoving derivative `d/dt Φ(τ + t, e^{-t/2}y)|_{t=0}` of a field jointly differentiable at
`(τ, y)` is `∂_τΦ(τ, y) − ½ DΦ(τ)(y)[y]`. -/
theorem hasDerivAt_comoving {Φ : ℝ → Space → Space} {τ : ℝ} {y : Space}
    (hΦ : DifferentiableAt ℝ (fun x : ℝ × Space => Φ x.1 x.2) (τ, y)) :
    HasDerivAt (fun t : ℝ => Φ (τ + t) (Real.exp (-t / 2) • y))
      (deriv (fun t => Φ t y) τ - (1 / 2 : ℝ) • fderiv ℝ (Φ τ) y y) 0 := by
  set F : ℝ × Space → Space := fun x => Φ x.1 x.2 with hF
  set L := fderiv ℝ F (τ, y) with hL
  have hFd : HasFDerivAt F L (τ, y) := hΦ.hasFDerivAt
  have he : HasDerivAt (fun t : ℝ => Real.exp (-t / 2)) (-(1 / 2 : ℝ)) 0 := by
    have h := ((hasDerivAt_neg' (x := (0 : ℝ))).div_const 2).exp
    convert h using 1
    norm_num
  have hγ : HasDerivAt (fun t : ℝ => ((τ + t, Real.exp (-t / 2) • y) : ℝ × Space))
      ((1 : ℝ), (-(1 / 2 : ℝ)) • y) 0 :=
    ((hasDerivAt_id (0 : ℝ)).const_add τ).prodMk (he.smul_const y)
  have hγ0 : ((τ + 0, Real.exp (-0 / 2) • y) : ℝ × Space) = (τ, y) := by simp
  have hFd' : HasFDerivAt F L ((τ + 0, Real.exp (-0 / 2) • y) : ℝ × Space) := by
    rw [hγ0]; exact hFd
  have hcomp := HasFDerivAt.comp_hasDerivAt (l := F)
    (f := fun t : ℝ => ((τ + t, Real.exp (-t / 2) • y) : ℝ × Space)) (0 : ℝ) hFd' hγ
  have hτ : HasDerivAt (fun t => Φ t y) (L ((1 : ℝ), (0 : Space))) τ := by
    have hi : HasDerivAt (fun t : ℝ => ((t, y) : ℝ × Space)) ((1 : ℝ), (0 : Space)) τ :=
      (hasDerivAt_id τ).prodMk (hasDerivAt_const τ y)
    exact hFd.comp_hasDerivAt τ hi
  have hy : HasFDerivAt (Φ τ) (L.comp (ContinuousLinearMap.inr ℝ ℝ Space)) y :=
    hFd.comp y (hasFDerivAt_prodMk_right τ y)
  have hsplit : L ((1 : ℝ), (-(1 / 2 : ℝ)) • y) =
      L ((1 : ℝ), (0 : Space)) - (1 / 2 : ℝ) • L ((0 : ℝ), y) := by
    have e : ((1 : ℝ), (-(1 / 2 : ℝ)) • y) =
        ((1 : ℝ), (0 : Space)) + (-(1 / 2 : ℝ)) • ((0 : ℝ), y) := by
      ext <;> simp
    rw [e, map_add, map_smul]
    module
  rw [hτ.deriv, hy.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
  rw [← hsplit]
  exact hcomp

/-- The datum clauses give the inverse-distance class `𝒦₂` (SP 2575-2577). -/
theorem invDist_of_datum {P : ℝ} {a : SpatialField} (h : Cons.C03.IsB3Datum P a) :
    ∃ C : ℝ, UnforcedLeray.Heat.InvDistClass 2 C a := by
  obtain ⟨C0, h0⟩ := h.bounds 0 (by norm_num)
  obtain ⟨C1, h1⟩ := h.bounds 1 (by norm_num)
  obtain ⟨C2, h2⟩ := h.bounds 2 (by norm_num)
  refine ⟨max C0 (max C1 C2), ⟨h.smooth.of_le (by first | exact le_top | simp), ?_⟩⟩
  intro j hj x hx
  have hx' : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have key : ‖iteratedFDeriv ℝ j a x‖ * ‖x‖ ^ (j + 1) ≤ max C0 (max C1 C2) := by
    interval_cases j
    · exact (h0 x hx).trans (le_max_left _ _)
    · exact (h1 x hx).trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact (h2 x hx).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hp : (0 : ℝ) < ‖x‖ ^ (j + 1) := pow_pos hx' _
  have hr : ‖x‖ ^ (-(1 + j : ℝ)) = (‖x‖ ^ (j + 1))⁻¹ := by
    rw [Real.rpow_neg hx'.le, show (1 + (j : ℝ)) = ((j + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
  rw [hr, ← div_eq_mul_inv, le_div_iff₀ hp]
  exact key

/-- **Pointwise form of the evolution**: if `U` is jointly differentiable along the phase slice,
`U(τ), H(τ) ∈ C²`, `D₀H = 0` at `τ`, and the comoving derivative of `U` is
`νΔU + ½U − G`, then `∂_τW − ½DW[y] − νΔW − ½W = −G` for `W = U − H`. -/
theorem evol_pointwise {ν τ : ℝ} {U H : ℝ → SpatialField} {G : SpatialField}
    (hUj : ∀ y, DifferentiableAt ℝ (fun x : ℝ × Space => U x.1 x.2) (τ, y))
    (hUs : ContDiff ℝ 2 (U τ)) (hHs : ContDiff ℝ 2 (H τ))
    (hHt : ∀ y, DifferentiableAt ℝ (fun t => H t y) τ)
    (hH0 : ∀ y, physDmu ν 0 H τ y = 0)
    (hcom : ∀ y, HasDerivAt (fun t : ℝ => U (τ + t) (Real.exp (-t / 2) • y))
      (ν • spatialLaplacian (U τ) y + (1 / 2 : ℝ) • U τ y - G y) 0) :
    (fun y => deriv (fun t => U t y - H t y) τ -
        (1 / 2 : ℝ) • fderiv ℝ (fun y' => U τ y' - H τ y') y y -
        ν • UnforcedLeray.Heat.vlap (fun y' => U τ y' - H τ y') y -
        (1 / 2 : ℝ) • (U τ y - H τ y)) = fun y => -G y := by
  funext y
  have hUt : DifferentiableAt ℝ (fun t => U t y) τ := by
    have hi : DifferentiableAt ℝ (fun t : ℝ => ((t, y) : ℝ × Space)) τ :=
      differentiableAt_id.prodMk (differentiableAt_const y)
    exact (hUj y).comp τ hi
  have e1 : deriv (fun t => U t y - H t y) τ -
        (1 / 2 : ℝ) • fderiv ℝ (fun y' => U τ y' - H τ y') y y -
        ν • UnforcedLeray.Heat.vlap (fun y' => U τ y' - H τ y') y -
        (1 / 2 : ℝ) • (U τ y - H τ y) =
      physDmu ν 0 (fun t y => U t y - H t y) τ y := by
    unfold physDmu
    rw [PartIIIb.Concrete.Ward1381Org.physLap_eq_vlap _ (hUs.sub hHs)]
    module
  rw [e1, PartIIIb.Concrete.Ward1381Org.physDmu_sub ν 0 U H τ y hUt (hHt y) hUs hHs, hH0 y,
    sub_zero]
  have hc := (hasDerivAt_comoving (hUj y)).unique (hcom y)
  have hL : physLap (U τ) y = spatialLaplacian (U τ) y := rfl
  unfold physDmu
  rw [hL, hc]
  module

end B3EvolAux

open B3EvolAux in
/-- **`PartII-b:B3/3` from `StrongAllOrders`** (SP 2610-2632 with SP 2519-2523, 2541-2562): at
every state `z` of the contraction ball and every phase `τ`, `U·∇U ∈ L²` and
`(∂_τ − ½y·∇ − νΔ − ½)(U − H_a) = −𝐏(U·∇U)` a.e., `U = bgField p z`, `a = p.datum (p.coord z)`.
Inputs: `StrongAllOrders` (`PartII-b:S2`); proved: `PartII-b:B2` (datum),
`PartII-b:S3/1` (joint smoothness), `PartII-b:S3/1/1/1` (Morrey), `PartII-b:S3/1/1/2/1`
(comoving projected equation), `PartII-b:S3/1/2/1` (smooth Leray representative),
`heatProfileDmuZero_proved` (`D₀H_a = 0`), `prodL2OfL4_proved` (Hölder). -/
theorem ballHeatRemainder_Evol_of (hS2 : StrongAllOrders) :
    B3Stmt.AtBallStates B3Stmt.Evol := by
  intro Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₁, hν₁, HS2⟩ := hS2 Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₂, hν₂, HJ⟩ :=
    jointSmoothnessFromSpatialAllOrders_proof Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₃, hν₃, HD⟩ := datum_facts_atBallStates Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₄, hν₄, HC⟩ :=
    bgComovingFirstEquation_proof Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  refine ⟨min (min ν₁ ν₂) (min ν₃ ν₄), lt_min (lt_min hν₁ hν₂) (lt_min hν₃ hν₄),
    fun p d hreg hν hS hq' z hz hzn => ?_⟩
  have hν₁' : p.ν ≤ ν₁ := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν₂' : p.ν ≤ ν₂ := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν₃' : p.ν ≤ ν₃ := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν₄' : p.ν ≤ ν₄ := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hgrad, hslice, hRaw, hInlet⟩ := HS2 p d hreg hν₁' hS hq' z hz hzn
  have hsmooth : ContDiff ℝ ∞ (fun x : ℝ × Space => bgField p z x.1 x.2) :=
    HJ p d hreg hν₂' hS hq' z hz hzn hgrad hslice hRaw hInlet
  obtain ⟨hD, -, -, -⟩ := HD p d hreg hν₃' hS hq' z hz hzn
  have hfam : IsUniformSmoothL4SliceFamily (bgField p z) :=
    isUniformSmoothL4SliceFamily_bgField_of_morreyL4
      (smoothMorreyL4Bound_of_field smoothMorreyL4FieldBound_proof) p z hslice
  have hCom : HasComovingJetDeriv (bgField p z) (comovingEvolRHS p.ν (bgField p z)) :=
    HC p d hreg hν₄' hS hq' z hz hzn hgrad hslice hfam hRaw hInlet
  obtain ⟨M₀, hM₀⟩ := hslice 0
  obtain ⟨M₁, hM₁⟩ := hslice 1
  obtain ⟨M₂, hM₂⟩ := hslice 2
  obtain ⟨C, hC⟩ := B3UL4Aux.ul4_of_iterated (bgField p z) M₀ M₁ M₂ (fun τ => (hM₀ τ).2.2)
    (fun τ => (hM₁ τ).2.2) (fun τ => (hM₂ τ).2.2)
  obtain ⟨Ca, hca⟩ := invDist_of_datum hD
  obtain ⟨hHs, hHt, hH0⟩ := heatProfileDmuZero_proved p.ν Ca (p.datum (p.coord z)) p.ν_pos hca
  have hConv : IsUniformSmoothL4SliceFamily
      (fun τ => spatialConvect (bgField p z τ) (bgField p z τ)) :=
    HigherPhaseSub.sliceFamily_spatialConvect hfam hfam
  intro τ
  have hUs : ContDiff ℝ 2 (bgField p z τ) :=
    (hsmooth.comp (contDiff_const.prodMk contDiff_id)).of_le (by first | exact le_top | simp)
  have hL2 : MemLp (fun y => fderiv ℝ (bgField p z τ) y (bgField p z τ y)) 2 volume :=
    (prodL2OfL4_proved (bgField p z τ) C (hUs.of_le (by norm_num)) (hC τ).1 (hC τ).2.1).1
  refine ⟨hL2, ?_⟩
  have hcom : ∀ y, HasDerivAt (fun t : ℝ => bgField p z (τ + t) (Real.exp (-t / 2) • y))
      (p.ν • spatialLaplacian (bgField p z τ) y + (1 / 2 : ℝ) • bgField p z τ y -
        smoothConvectiveLeray (bgField p z) (bgField p z) τ y) 0 := by
    intro y
    have h := hCom [] τ y
    simp only [dirSpatialJet_nil, List.length_nil, Nat.cast_zero, zero_div, zero_smul,
      add_zero] at h
    exact h
  have hpt := evol_pointwise (ν := p.ν) (τ := τ) (U := bgField p z)
    (H := UnforcedLeray.Blueprint.heatProfile p.ν (p.datum (p.coord z)))
    (G := smoothConvectiveLeray (bgField p z) (bgField p z) τ)
    (fun y => hsmooth.differentiable (by simp) _) hUs (hHs τ) (hHt τ) (hH0 τ) hcom
  rw [hpt]
  obtain ⟨hF4, -, hGae⟩ := ((smoothLeraySliceRegularity_proof.1 _ hConv).1 τ)
  have hP := UnforcedLeray.RieszLp.lerayLp_toLp_ae_eq_projection (p := 4) (by norm_num)
    (by norm_num) hF4 hL2
  have h1 : (fun y => -smoothConvectiveLeray (bgField p z) (bgField p z) τ y) =ᵐ[volume]
      -(⇑(UnforcedLeray.Leray.projection (UnforcedLeray.toL2
        (fun y => fderiv ℝ (bgField p z τ) y (bgField p z τ y))))) := by
    filter_upwards [hGae.trans hP] with y hy
    simp only [Pi.neg_apply]
    exact congrArg Neg.neg hy
  exact h1.trans (Lp.coeFn_neg _).symm

/-- Unconditional `PartII-b:B3/3`: `ballHeatRemainder_Evol_of` instantiated with the accepted
`StrongAllOrders` proof (`PartII-b:S2`). -/
theorem ballHeatRemainder_Evol :
    UnforcedLeray.Short.IIb.B3Stmt.AtBallStates UnforcedLeray.Short.IIb.B3Stmt.Evol :=
  let h4 := affineInletFacts_proof
  let hQ1 := quadBound_of h4
  let hS1 := _root_.strongFirstDerivative_of h4 hQ1
  let hS2 := strongAllOrders_of h4 hQ1 hS1
  ballHeatRemainder_Evol_of hS2

end UnforcedLeray.Short.IIb
