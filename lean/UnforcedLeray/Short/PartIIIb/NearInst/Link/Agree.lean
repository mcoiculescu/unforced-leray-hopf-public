import UnforcedLeray.Short.PartIIIb.NearInst.Link.Isos

/-!
# The near link of a return base (source 3866-3920, 4079-4118, 5536-5547, 5777-5833)

Source of record: `the November 2 reference manuscript` (73 pages).

A `Concrete.ReturnBase` (`Concrete/ReturnOps.lean`) holds the exact multiplier `M`, the near
inverse `S_N`, the body inverse `R_μ` and `D_N⁻¹` on the gain-normed spaces `VelG`, `StrG`,
`SrcG`.  The source uses one set of operators: `M = M_U` (3876-3878, 5779-5782), `S_N` of
`near:equation-comparison` (3911-3920, 5785), `R_μ` the body inverse whose curved chart form is
`R_ε` (4084-4086, 4139-4146).  This file records that identification through the concrete
isometries of `NearInst/Link/Isos.lean`:

* `IsNearLinked B o hν` : `B.M = o.MG γ hν` and `B.SN = o.SNG γ hν`;
* `IsBodyLinked B Reps hν` : `B.R = bodyG Reps γ hν`.

Consequences proved here:

* `IsNearLinked.isUnit_DN`, `IsNearLinked.dninv_eq` : `D_N` is a unit on `Z` and
  `B.DNinv = o.DNinvG γ hν = strIso⁻¹ (G⁻¹ (Ring.inverse D_N) G) strIso` (the two-sided inverse of
  `ReturnBase` is the near inverse; source 3917, 5787);
* `column_sub_eq`, `norm_column_sub_le` : the curved minus flat forced column
  `D_N⁻¹M R_μ f - T₀ f` is `(√π)⁻¹ strIso⁻¹ G⁻¹ (D_N⁻¹M_U R_ε h - D₀⁻¹M₀R₀ h)`, `h = srcIso f`
  (source 4084-4118).

Helpers for the pins: `ageμ_absCont`, `ae_z1Measure`, `ae_htRhoMeasure`, `ae_bodyMeasure`,
`ae_srcMeasure` (same null sets), `coeFn_SNG`, `coeFn_MG_fst`, `coeFn_MG_snd`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. Null sets of the chart measures -/

/-- The normalized cell measure is `s`-finite (instance search does not unfold `Cyl.avgμ`). -/
instance link_sFinite_avgμ (c : ℝ) : SFinite (UnforcedLeray.Cyl.avgμ c) := by
  unfold UnforcedLeray.Cyl.avgμ
  infer_instance

/-- All age weights `s^a` have the same null sets on the chart. -/
theorem ageμ_absCont (c a b : ℝ) : ageμ c a ≪ ageμ c b := by
  unfold ageμ
  refine Measure.AbsolutelyContinuous.prod ?_ Measure.AbsolutelyContinuous.rfl
  refine (withDensity_absolutelyContinuous _ _).trans ?_
  refine withDensity_absolutelyContinuous' (measurable_ofReal_rpow b).aemeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hs b)).ne'

theorem transWeight_pos (mZ : ℝ) (p : Chart) : 0 < UnforcedLeray.Short.IIIa.transWeight mZ p := by
  unfold UnforcedLeray.Short.IIIa.transWeight
  exact Real.rpow_pos_of_pos (by positivity) _

theorem transWeight_measurable (mZ : ℝ) :
    Measurable (UnforcedLeray.Short.IIIa.transWeight mZ) := by
  unfold UnforcedLeray.Short.IIIa.transWeight
  fun_prop

theorem root_z1 (c mZ : ℝ) :
    IsDensityRoot (z1Measure c mZ) (ageμ c (-1 / 2)) (UnforcedLeray.Short.IIIa.transWeight mZ) :=
  ⟨transWeight_measurable mZ, transWeight_pos mZ, rfl⟩

theorem root_htRho {c ρb : ℝ} (hρ : 0 < ρb) :
    IsDensityRoot (htRhoMeasure c ρb) (ageμ c (-1 / 2)) (fun _ => Real.sqrt ρb⁻¹) := by
  refine ⟨measurable_const, fun _ => Real.sqrt_pos.2 (inv_pos.2 hρ), ?_⟩
  show htRhoMeasure c ρb = (ageμ c (-1 / 2)).withDensity fun _ => ENNReal.ofReal (Real.sqrt ρb⁻¹ ^ 2)
  rw [Real.sq_sqrt (inv_nonneg.2 hρ.le), withDensity_const]
  rfl

theorem ae_z1Measure (c mZ : ℝ) : ae (z1Measure c mZ) = ae (ageμ c (-1 / 2)) :=
  (root_z1 c mZ).ae_eq

theorem ae_htRhoMeasure {c ρb : ℝ} (hρ : 0 < ρb) : ae (htRhoMeasure c ρb) = ae (ageμ c (-1 / 2)) :=
  (root_htRho hρ).ae_eq

theorem ae_bodyMeasure (c γ ν : ℝ) : ae (bodyMeasure c γ ν) = ae (ageμ c (-3 / 2)) :=
  (root_body c γ ν).ae_eq

theorem ae_srcMeasure (c : ℝ) : ae (srcMeasure c) = ae (ageμ c (-3 / 2)) :=
  (root_src c).ae_eq

theorem ae_gainZ1Measure (c mZ γ ν : ℝ) : ae (gainZ1Measure c mZ γ ν) = ae (z1Measure c mZ) :=
  (root_gainZ1 c mZ γ ν).ae_eq

theorem ae_gainHTMeasure (c ρb γ ν : ℝ) : ae (gainHTMeasure c ρb γ ν) = ae (htRhoMeasure c ρb) :=
  (root_gainHT c ρb γ ν).ae_eq

/-! ## 2. The transported operators on functions -/

section Coe

variable {c mZ ρb : ℝ} (o : NearOps c mZ ρb) (γ : ℝ) {ν : ℝ} (hν : 0 < ν)

/-- `S_N T` on the return spaces is the function `S_N F`, `F = gainEquiv (strIso T)` the same stress
in `Z`. -/
theorem coeFn_SNG (T : StrG c mZ ρb γ ν) :
    (o.SNG γ hν T : Chart → Merid) =ᵐ[ageμ c (-3 / 2)]
      (o.SN (gainEquiv c mZ ρb γ hν (strIso c mZ ρb γ ν T)) : Chart → Merid) := by
  rw [NearOps.SNG_apply, ← ae_bodyMeasure c γ ν]
  set F := gainEquiv c mZ ρb γ hν (strIso c mZ ρb γ ν T)
  have h3 := coeFn_gainH_symm (c := c) γ hν (o.SN F)
  rw [← ae_bodyMeasure c γ ν] at h3
  filter_upwards [Lp.coeFn_smul (Real.sqrt Real.pi) ((velIso c γ ν).symm
      ((gainH c γ hν).symm (o.SN F))),
    coeFn_velIso_symm ((gainH c γ hν).symm (o.SN F)), h3] with p h1 h2 h3
  rw [h1, Pi.smul_apply, h2, h3, smul_smul, smul_smul]
  have h4 : Real.sqrt Real.pi * (Real.sqrt Real.pi * Concrete.ginv γ ν p)⁻¹ * gainInvFun γ ν p
      = 1 := by
    rw [← ginv_eq_gainInvFun]
    have := ginv_pos' γ ν p
    field_simp [sqrtPi_pos.ne']
  rw [h4, one_smul]

/-- The thin component of `M_U w` on the return spaces is the function `(M_U u).fst`,
`u = (√π)⁻¹ gainH (velIso w)` the same velocity in `H`. -/
theorem coeFn_MG_fst (w : VelG c γ ν) :
    ((o.MG γ hν w).fst : Chart → Ten3) =ᵐ[gainZ1Measure c mZ γ ν]
      ((o.MU ((Real.sqrt Real.pi)⁻¹ • gainH c γ hν (velIso c γ ν w))).fst : Chart → Ten3) := by
  set u := gainH c γ hν (velIso c γ ν w)
  have hlin : o.MG γ hν w = (strIso c mZ ρb γ ν).symm
      ((gainEquiv c mZ ρb γ hν).symm (o.MU ((Real.sqrt Real.pi)⁻¹ • u))) := by
    rw [NearOps.MG_apply, map_smul, map_smul, map_smul]
  rw [hlin]
  set X := o.MU ((Real.sqrt Real.pi)⁻¹ • u)
  have h2 := coeFn_gainLp_symm (z1Measure c mZ) γ hν X.fst
  rw [← ae_gainZ1Measure c mZ γ ν] at h2
  filter_upwards [coeFn_strIso_symm_fst (γ := γ) (ν := ν) ((gainEquiv c mZ ρb γ hν).symm X),
    h2] with p h1 h2
  rw [h1]
  change (Concrete.ginv γ ν p)⁻¹ • (((gainLp (z1Measure c mZ) γ hν).symm X.fst : Lp Ten3 2 _) :
    Chart → Ten3) p = _
  rw [h2, smul_smul, ← ginv_eq_gainInvFun, inv_mul_cancel₀ (ginv_pos' γ ν p).ne', one_smul]

/-- The repair component of `M_U w` on the return spaces is the function `(M_U u).snd`. -/
theorem coeFn_MG_snd (w : VelG c γ ν) :
    ((o.MG γ hν w).snd : Chart → Ten3) =ᵐ[gainHTMeasure c ρb γ ν]
      ((o.MU ((Real.sqrt Real.pi)⁻¹ • gainH c γ hν (velIso c γ ν w))).snd : Chart → Ten3) := by
  set u := gainH c γ hν (velIso c γ ν w)
  have hlin : o.MG γ hν w = (strIso c mZ ρb γ ν).symm
      ((gainEquiv c mZ ρb γ hν).symm (o.MU ((Real.sqrt Real.pi)⁻¹ • u))) := by
    rw [NearOps.MG_apply, map_smul, map_smul, map_smul]
  rw [hlin]
  set X := o.MU ((Real.sqrt Real.pi)⁻¹ • u)
  have h2 := coeFn_gainLp_symm (htRhoMeasure c ρb) γ hν X.snd
  rw [← ae_gainHTMeasure c ρb γ ν] at h2
  filter_upwards [coeFn_strIso_symm_snd (γ := γ) (ν := ν) ((gainEquiv c mZ ρb γ hν).symm X),
    h2] with p h1 h2
  rw [h1]
  change (Concrete.ginv γ ν p)⁻¹ • (((gainLp (htRhoMeasure c ρb) γ hν).symm X.snd : Lp Ten3 2 _) :
    Chart → Ten3) p = _
  rw [h2, smul_smul, ← ginv_eq_gainInvFun, inv_mul_cancel₀ (ginv_pos' γ ν p).ne', one_smul]

end Coe

/-! ## 3. The link -/

section Link

variable {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff] [NormedSpace ℝ Aff]
  [CompleteSpace Aff]

/-- **The near link** (source 3866-3920, 5777-5787): the exact multiplier `M` and the near inverse
`S_N` of the return base are the near operators `M_U`, `S_N` of `o` acting on the same chart
functions, i.e. conjugated by the concrete isometries `strIso`, `velIso` and the gains
`gainEquiv`, `gainH`. -/
structure IsNearLinked (B : ReturnBase c mZ ρb γ ν Aff) (o : NearOps c mZ ρb) (hν : 0 < ν) :
    Prop where
  mult : B.M = o.MG γ hν
  near : B.SN = o.SNG γ hν

/-- **The body link** (source 4084-4086, 4139-4146, 5781): the physical body inverse `R_μ` of the
return base is the real form `R_ε` (on `H`) of the curved body inverse `T_ε` acting on the same
chart functions. -/
def IsBodyLinked (B : ReturnBase c mZ ρb γ ν Aff) (Reps : Hsp c →L[ℝ] Hsp c) (hν : 0 < ν) :
    Prop :=
  B.R = bodyG Reps γ hν

/-- The candidate inverse of `D_N` on `Z` read off the return base: `G strIso D_N⁻¹ strIso⁻¹ G⁻¹`. -/
def dnInvZ (B : ReturnBase c mZ ρb γ ν Aff) (hν : 0 < ν) : Zsp c mZ ρb →L[ℝ] Zsp c mZ ρb :=
  (gainEquiv c mZ ρb γ hν : Zsp c mZ ρb →L[ℝ] Zsp c mZ ρb) ∘L
    ((strIso c mZ ρb γ ν).toContinuousLinearEquiv : StrG c mZ ρb γ ν →L[ℝ] Zsp c mZ ρb) ∘L
    B.DNinv ∘L
    ((strIso c mZ ρb γ ν).symm.toContinuousLinearEquiv : Zsp c mZ ρb →L[ℝ] StrG c mZ ρb γ ν) ∘L
    ((gainEquiv c mZ ρb γ hν).symm : Zsp c mZ ρb →L[ℝ] Zsp c mZ ρb)

theorem dnInvZ_apply (B : ReturnBase c mZ ρb γ ν Aff) (hν : 0 < ν) (F : Zsp c mZ ρb) :
    dnInvZ B hν F = gainEquiv c mZ ρb γ hν (strIso c mZ ρb γ ν
      (B.DNinv ((strIso c mZ ρb γ ν).symm ((gainEquiv c mZ ρb γ hν).symm F)))) := rfl

namespace IsNearLinked

variable {B : ReturnBase c mZ ρb γ ν Aff} {o : NearOps c mZ ρb} {hν : 0 < ν}

theorem dn_apply (h : IsNearLinked B o hν) (T : StrG c mZ ρb γ ν) :
    T + B.M (B.SN T) = (strIso c mZ ρb γ ν).symm ((gainEquiv c mZ ρb γ hν).symm
      (o.DN (gainEquiv c mZ ρb γ hν (strIso c mZ ρb γ ν T)))) := by
  have h1 := congrArg (fun X : StrG c mZ ρb γ ν →L[ℝ] StrG c mZ ρb γ ν => X T)
    (o.one_add_MG_SNG γ hν)
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.comp_apply] at h1
  rw [h.mult, h.near, h1, strConj_apply]
  rfl

theorem dnInvZ_left (h : IsNearLinked B o hν) (F : Zsp c mZ ρb) : dnInvZ B hν (o.DN F) = F := by
  set T := (strIso c mZ ρb γ ν).symm ((gainEquiv c mZ ρb γ hν).symm F)
  have hT : gainEquiv c mZ ρb γ hν (strIso c mZ ρb γ ν T) = F := by simp [T]
  have key := B.DNinv_left T
  rw [h.dn_apply, hT] at key
  rw [dnInvZ_apply, key, hT]

theorem dnInvZ_right (h : IsNearLinked B o hν) (F : Zsp c mZ ρb) : o.DN (dnInvZ B hν F) = F := by
  set T := (strIso c mZ ρb γ ν).symm ((gainEquiv c mZ ρb γ hν).symm F)
  have key := B.DNinv_right T
  rw [h.dn_apply] at key
  have key2 := congrArg (fun S => gainEquiv c mZ ρb γ hν (strIso c mZ ρb γ ν S)) key
  simp only [LinearIsometryEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply] at key2
  rw [dnInvZ_apply]
  rw [key2]
  simp [T]

/-- The unit `D_N` of `Z →L Z` with inverse `dnInvZ`. -/
def dnUnit (h : IsNearLinked B o hν) : (Zsp c mZ ρb →L[ℝ] Zsp c mZ ρb)ˣ where
  val := o.DN
  inv := dnInvZ B hν
  val_inv := by ext1 F; exact h.dnInvZ_right F
  inv_val := by ext1 F; exact h.dnInvZ_left F

/-- `D_N = I + M_U S_N` is invertible on `Z` (it has the two-sided inverse of the return base). -/
theorem isUnit_DN (h : IsNearLinked B o hν) : IsUnit o.DN := ⟨h.dnUnit, rfl⟩

theorem ring_inverse_DN (h : IsNearLinked B o hν) : Ring.inverse o.DN = dnInvZ B hν := by
  have := Ring.inverse_unit h.dnUnit
  exact this

/-- **`D_N⁻¹` of the return base is the near inverse** (source 3917, 5787):
`B.DNinv = strIso⁻¹ (G⁻¹ (Ring.inverse D_N) G) strIso`. -/
theorem dninv_eq (h : IsNearLinked B o hν) : B.DNinv = o.DNinvG γ hν := by
  ext1 T
  rw [NearOps.DNinvG_apply, h.ring_inverse_DN, dnInvZ_apply]
  simp

end IsNearLinked

/-- For a unit `D_N`, `DNinvG` is a left inverse of `I + M S_N` on the return spaces (the field
`DNinv_left` of a `ReturnBase` built from the near operators, source 3917, 5787). -/
theorem NearOps.DNinvG_left (o : NearOps c mZ ρb) (hν : 0 < ν) (hU : IsUnit o.DN)
    (T : StrG c mZ ρb γ ν) : o.DNinvG γ hν (T + o.MG γ hν (o.SNG γ hν T)) = T := by
  have h1 := congrArg (fun X : StrG c mZ ρb γ ν →L[ℝ] StrG c mZ ρb γ ν => X T)
    (o.one_add_MG_SNG γ hν)
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.comp_apply] at h1
  rw [h1, NearOps.DNinvG_apply, strConj_apply]
  have h2 : Ring.inverse o.DN (o.DN (gainEquiv c mZ ρb γ hν (strIso c mZ ρb γ ν T))) =
      gainEquiv c mZ ρb γ hν (strIso c mZ ρb γ ν T) := by
    rw [← ContinuousLinearMap.mul_apply, Ring.inverse_mul_cancel o.DN hU,
      ContinuousLinearMap.one_apply]
  simp only [conjG, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.apply_symm_apply]
  rw [h2]
  simp

/-- For a unit `D_N`, `DNinvG` is a right inverse of `I + M S_N` on the return spaces (the field
`DNinv_right` of a `ReturnBase` built from the near operators). -/
theorem NearOps.DNinvG_right (o : NearOps c mZ ρb) (hν : 0 < ν) (hU : IsUnit o.DN)
    (T : StrG c mZ ρb γ ν) :
    o.DNinvG γ hν T + o.MG γ hν (o.SNG γ hν (o.DNinvG γ hν T)) = T := by
  have h1 := congrArg (fun X : StrG c mZ ρb γ ν →L[ℝ] StrG c mZ ρb γ ν => X (o.DNinvG γ hν T))
    (o.one_add_MG_SNG γ hν)
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.comp_apply] at h1
  rw [h1, NearOps.DNinvG_apply, strConj_apply]
  have h2 : ∀ F, o.DN (Ring.inverse o.DN F) = F := fun F => by
    rw [← ContinuousLinearMap.mul_apply, Ring.mul_inverse_cancel o.DN hU,
      ContinuousLinearMap.one_apply]
  simp only [conjG, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.apply_symm_apply]
  rw [h2]
  simp

/-! ## 4. The forced columns (source 4079-4118) -/

/-- The curved column `D_N⁻¹M R_μ f` minus the flat column `T₀f = D₀⁻¹M₀R₀f` on the return spaces
is the near-layer difference at `h = srcIso f` (source 4084-4086, 4109-4111). -/
theorem column_sub_eq {B : ReturnBase c mZ ρb γ ν Aff} {o : NearOps c mZ ρb} {hν : 0 < ν}
    {Reps : Hsp c →L[ℝ] Hsp c} (hN : IsNearLinked B o hν) (hR : IsBodyLinked B Reps hν)
    (R0 : Hsp c →L[ℝ] Hsp c) (f : SrcG c) :
    B.DNinv (B.M (B.R f)) - o.flatColG γ hν R0 f =
      (Real.sqrt Real.pi)⁻¹ • (strIso c mZ ρb γ ν).symm ((gainEquiv c mZ ρb γ hν).symm
        (Ring.inverse o.DN (o.MU (Reps (srcIso c f))) -
          Ring.inverse o.D0 (o.M0 (R0 (srcIso c f))))) := by
  rw [hN.dninv_eq, hN.mult, hR, NearOps.DNinvG_apply, NearOps.MG_apply, NearOps.flatColG_apply]
  have hb : gainH c γ hν (velIso c γ ν (bodyG Reps γ hν f)) = Reps (srcIso c f) := by
    simp [bodyG]
  rw [hb]
  simp only [map_smul, map_sub, LinearIsometryEquiv.apply_symm_apply,
    ContinuousLinearEquiv.apply_symm_apply, smul_sub]

theorem inv_sqrtPi_le_one : (Real.sqrt Real.pi)⁻¹ ≤ 1 := by
  have h1 : 1 ≤ Real.sqrt Real.pi := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
  exact inv_le_one_of_one_le₀ h1

/-- `‖D_N⁻¹M R_μ f - T₀f‖_Str ≤ ‖G⁻¹(D_N⁻¹M_U R_ε h - D₀⁻¹M₀R₀ h)‖_Z`, `h = srcIso f`,
`‖h‖_H = ‖f‖_Src`. -/
theorem norm_column_sub_le {B : ReturnBase c mZ ρb γ ν Aff} {o : NearOps c mZ ρb} {hν : 0 < ν}
    {Reps : Hsp c →L[ℝ] Hsp c} (hN : IsNearLinked B o hν) (hR : IsBodyLinked B Reps hν)
    (R0 : Hsp c →L[ℝ] Hsp c) (f : SrcG c) :
    ‖B.DNinv (B.M (B.R f)) - o.flatColG γ hν R0 f‖ ≤
      ‖(gainEquiv c mZ ρb γ hν).symm (Ring.inverse o.DN (o.MU (Reps (srcIso c f))) -
          Ring.inverse o.D0 (o.M0 (R0 (srcIso c f))))‖ := by
  rw [column_sub_eq hN hR R0 f, norm_smul, LinearIsometryEquiv.norm_map,
    Real.norm_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
  exact mul_le_of_le_one_left (norm_nonneg _) inv_sqrtPi_le_one

end Link

end UnforcedLeray.Short.PartIIIb.NearInst
