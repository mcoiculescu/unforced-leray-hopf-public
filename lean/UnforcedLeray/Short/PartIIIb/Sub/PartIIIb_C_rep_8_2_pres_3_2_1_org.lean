import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_org
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_1
import UnforcedLeray.Lib.LerayLp.Helmholtz

/-!
# The pressure identity `∇p - ∇p_lift = -(I-ℙ)(convChg + entSrc + F_R)`
# (`PartIII-b:C/rep/8/2/pres/3/2/1/org`)

Source of record: `the November 2 reference manuscript`
(73 pages): 5245-5260 (the canonical pressure `∇p_V = -(I-ℙ)(V·∇V)` and the exact pressure
correction), 5272-5281 (`∇(p_raw - p_lift) = -(I-ℙ)F_raw`, "the unprojected residual gives"),
1213-1225 (Proposition `sct:lift`: the raw lift, `p_raw = (R/r)²p`, smooth through the axis,
residual `F_R`), 1263 (`F_R = s^{3/2} r`), 4139-4141 (`D₀U + U·∇U + ∇p = 0`), 117-118 (the
pressure is the global choice `p = Σ R_iR_k(u_iu_k)`), 2607-2612 and 2641-2642 (`D^jU ∈ C_per L⁴`,
`p_U = Σ R_iR_j(U_iU_j) ∈ C_per L²`), 2541-2561 (all spatial orders, `U` jointly smooth through the
axis; decay of the train and inlet sources at large radius; "the inlet cutoff vanishes near the
axis").

## The argument (`presHelmholtzAt_of`)

Fix `τ`; `G = presForce τ = convChg + entSrc + F_R`
`= (U·∇U - V·∇V) + (D₀(V - U_raw) + V·∇V - U_raw·∇U_raw) + F_R`, and
`S = dmuChg τ = D₀U - D₀(V - U_raw) - D₀U_raw` (`= D₀r_b` off the axis, `DmuChgLinAt`),
`q = p - p_lift`.

1. **Off the axis** (`RawEqOffAxisAt`: `F_R = D₀U_raw + U_raw·∇U_raw + ∇p_lift`, and
   `IsExactProfile.equation`): `∇q = -S - G` pointwise (algebra, `pf2_presDiff_offAxis`).
2. **The potentials.** `p(τ) - c ∈ L²` and `∇p(τ) ∈ L^{11/4}` (`ExactPresDecayAt`: the full pressure
   is `p_U ∈ C_per L²`, 2641-2642; a standing fact of the exact background, absent from
   `SeqData.RepairStanding`); `p_lift(τ)` agrees off the axis with a `C^∞` function on `ℝ³`
   (`LiftPExtAt`, 1219) and `p_lift(τ) ∈ L^r`, `∇p_lift(τ) ∈ L^{11/4}` (`LiftPDecayAt`, 1202,
   2541-2552).  `RieszLp.lerayLp_gradient_eq_zero` gives `ℙ∇p = ℙ∇p_lift = 0`.
3. **`S` is solenoidal**: `r_b` agrees off the axis with a jointly `C^∞` divergence-free field `X`
   (`RbExtAt`), `S = D₀X` off the axis (`DmuChgLinAt`, linearity and locality of `D₀`), and `D₀`
   preserves divergence-free fields (`DmuDivFreeSol`).  By 1 and 2, `S ∈ L^{11/4}` whenever `G` is;
   `RieszLp.lerayLp_eq_self` gives `ℙS = S`.
4. Hence `ℙG = ℙ(-∇q - S) = -S` and `(I-ℙ)G = G + S = -∇q` a.e.
5. **Measurability**: off the axis `G = -∇q - D₀X` is continuous (`pf2_presForce_contOn`), and the
   axis is null.

## Contents

* object: `dmuChg`;
* data-free leaves `RealCOpsBridge`, `DmuDivFreeSol`;
* leaves at one level: `LiftPSimAt` (chart algebra), `RawEqOffAxisAt`, `ExactPresDecayAt`
  (standing), `LiftPExtAt`, `LiftPDecayAt`, `RbExtAt`, `DmuChgLinAt`; their `SeqData` forms;
* helpers for the drafters: `pf2_retEps_tendsto`, `SeqData.pf2_eventually_regime`,
  `pf2_exactPlanarTrain`, `pf2_physGrad_eq_gradField`, `pf2_isSolenoidal_congr_ae`,
  `pf2_aesm_of_continuousOn`, `pf2_physGrad_congr_offAxis`, `pf2_contDiff_physDmu`;
* **proved here:** `pf2_presDiff_offAxis`, `pf2_presForce_contOn`, `presHelmholtzAt_of`,
  `SeqData.presHelmholtz_of`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-! ## 1. The object -/

/-- **`S = D₀U - D₀(V - U_raw) - D₀U_raw`** (source 4140-4141 `D_μ` at `μ = 0`, 5254-5257,
5274-5279): off the axis this is `D₀r_b`, `r_b = U - V` (`DmuChgLinAt`), the solenoidal part of
`-(∇p - ∇p_lift) - (convChg + entSrc + F_R)`. -/
def dmuChg (Pl : PlanarData) (L : ReturnLevel) (τ : ℝ) (y : Space) : Space :=
  physDmu L.ν 0 L.U τ y - physDmu L.ν 0 (fun t y' => L.V t y' - rawU Pl L t y') τ y -
    physDmu L.ν 0 (rawU Pl L) τ y

/-! ## 2. The data-free leaves -/

/-- **The complexified operators on real fields** (`B0411.L0`, `Cons.C03.Concrete.advT`,
`PhaseSpace.gradT`; source 1263, 4140-4141): at a point `z` near which `X` is jointly `C²` and
where `Pr` is jointly differentiable, `L₀W + (W·∇)W + ∇Q = realC(D₀X + DX[X] + ∇Pr)` for
`W = realC ∘ X`, `Q = Pr` (as complex scalars).  This translates
`IIb.RingResidualCartesianNS` into `physDmu`, `fderiv`, `physGrad`. -/
def RealCOpsBridge : Prop :=
  ∀ (ν : ℝ) (X : ℝ → Space → Space) (Pr : ℝ → Space → ℝ) (z : ℝ × Space),
    ContDiffAt ℝ 2 (fun q : ℝ × Space => X q.1 q.2) z →
    DifferentiableAt ℝ (fun q : ℝ × Space => Pr q.1 q.2) z →
    UnforcedLeray.B0411.L0 ν (fun q : ℝ × Space => UnforcedLeray.B0412.realC (X q.1 q.2)) z +
        UnforcedLeray.Cons.C03.Concrete.advT
          (fun q : ℝ × Space => UnforcedLeray.B0412.realC (X q.1 q.2))
          (fun q : ℝ × Space => UnforcedLeray.B0412.realC (X q.1 q.2)) z +
        UnforcedLeray.PhaseSpace.gradT (fun q : ℝ × Space => ((Pr q.1 q.2 : ℝ) : ℂ)) z =
      UnforcedLeray.B0412.realC (physDmu ν 0 X z.1 z.2 + fderiv ℝ (X z.1) z.2 (X z.1 z.2) +
        physGrad (Pr z.1) z.2)

/-- **`D₀` preserves divergence-free fields** (source 4140-4141, 5254-5257: `D₀r_b` is
solenoidal): for a jointly `C^∞` field `X` with `div X(τ) = 0` pointwise,
`div D₀X = (∂_τ - ½y·∇ - νΔ - 1)div X = 0`, so every slice `D₀X(τ)` is distributionally
solenoidal. -/
def DmuDivFreeSol : Prop :=
  ∀ (ν : ℝ) (X : ℝ → Space → Space),
    ContDiff ℝ ∞ (fun q : ℝ × Space => X q.1 q.2) →
    (∀ τ y, ∑ j : Fin 3, physPd (X τ) j y j = 0) →
    ∀ τ, UnforcedLeray.IsSolenoidal (physDmu ν 0 X τ)

/-! ## 3. The leaves at one level (`R = ε⁻¹`, `c = ν⁻²`, period `P = 2εc`) -/

section Regime

variable (Pl : PlanarData) (L : ReturnLevel)

/-- **`p_lift` is the similarity form of the raw pressure** (source 1217: `p_raw = (R/r)²p`;
2666-2674: the chart `s = R²/ϱ²`, `q = R log(ϱ/R) + Rτ/2`, `η = Rz/ϱ`): off the axis
`liftP L τ y = e^τ p_raw(e^τ, e^{τ/2}y) = simProfile 2 (liftPressure R p_cyl) τ y`, `R = ε⁻¹`. -/
def LiftPSimAt : Prop :=
  ∀ (τ : ℝ) (y : Space), y ∉ axis →
    liftP L τ y = UnforcedLeray.B0190.simProfile 2
      (UnforcedLeray.B0185.liftPressure L.ε⁻¹ (UnforcedLeray.B0190.trainProfile L.train.p)) τ y

/-- **The raw lift equation off the axis** (source 1213-1225, 1263: `F_R = s^{3/2}r` is the
Cartesian residual `D₀U_raw + U_raw·∇U_raw + ∇p_raw` of the similarity lift, `p_raw = (R/r)²p`
(1217), which is `liftP`): at every point off the axis, `F_R = D₀U_raw + U_raw·∇U_raw + ∇p_lift`. -/
def RawEqOffAxisAt : Prop :=
  ∀ (τ : ℝ) (y : Space), y ∉ axis →
    rawResidF Pl L τ y = physDmu L.ν 0 (rawU Pl L) τ y +
      fderiv ℝ (rawU Pl L τ) y (rawU Pl L τ y) + physGrad (liftP L τ) y

/-- **The full pressure of the exact background is the global `L²` pressure** (source 117-118: "The
pressure is the global choice `p = Σ R_iR_k(u_iu_k)`"; 2641-2642: "`p_U = Σ R_iR_j(U_iU_j) ∈ C_per L²`
recovers the discarded gradient part of the exact projected equation"; 2607-2612: `D^jU ∈ C_per L⁴`,
`𝕋 = U⊗U ∈ C_per H²`, and 2525-2530 `U ∈ W^{1,∞}`, so `∇(U⊗U) ∈ L² ∩ L^∞ ⊂ L^{11/4}` and
`∇p_U = Σ R_iR_j∇(U_iU_j) ∈ L^{11/4}`; 5245-5257): at every phase, `p(τ)` minus a constant is in
`L²(ℝ³)` (the profile equation fixes `p` only up to a function of `τ`) and `∇p(τ) ∈ L^{11/4}`.
A standing fact of the exact background, not contained in `SeqData.RepairStanding`. -/
def ExactPresDecayAt : Prop :=
  ∀ τ : ℝ, (∃ c : ℝ, MemLp (fun y => L.pres τ y - c) 2 volume) ∧
    MemLp (physGrad (L.pres τ)) (11 / 4) volume

/-- **The lifted pressure is smooth through the axis** (source 1219: the raw lift "is smooth through
the axis for positive time"; 1305-1322 the heat expansion; 2548-2551 "its even radial powers extend
smoothly through the axis"; `IIb.RingLiftSmoothExt`): at every phase, `p_lift(τ)` agrees off the
axis with a `C^∞` function on `ℝ³`. -/
def LiftPExtAt : Prop :=
  ∀ τ : ℝ, ∃ Pt : Space → ℝ, ContDiff ℝ ∞ Pt ∧ ∀ y : Space, y ∉ axis → Pt y = liftP L τ y

/-- **The lifted pressure decays** (source 1202: the bounded pressure of the planar train; 1213-1225;
2541-2552: "in the large-radius region their unprojected derivatives are bounded by
`C_{k,N}ϱ^{-3-k}(1+|y₃|/ϱ)^{-N}`", and on `ϱ < R` the all-age heat expansion "gives arbitrary axial
decay"; 5274-5276 uses `ℙ∇p_lift = 0`): at every phase, `p_lift(τ) ∈ L^r` for some `r ≥ 1` and
`∇p_lift(τ) ∈ L^{11/4}`. -/
def LiftPDecayAt : Prop :=
  ∀ τ : ℝ, (∃ r : ℝ≥0∞, 1 ≤ r ∧ MemLp (liftP L τ) r volume) ∧
    MemLp (physGrad (liftP L τ)) (11 / 4) volume

/-- **The repair is smooth through the axis and divergence free** (source 2541-2561: all spatial
orders and time derivatives, "`U` is jointly smooth through the axis"; 1219: `U_raw` smooth through
the axis; 2550: "the inlet cutoff vanishes near the axis"; 4139-4141 `div U = 0`, 1211-1214 `U_raw`
exactly solenoidal, 2570-2575 the inlet solenoidal, so `div r_b = 0`): `r_b = U - V` agrees off the
axis with a jointly `C^∞` field on `ℝ × ℝ³` with vanishing divergence. -/
def RbExtAt : Prop :=
  ∃ X : ℝ → Space → Space, ContDiff ℝ ∞ (fun q : ℝ × Space => X q.1 q.2) ∧
    (∀ τ (y : Space), ∑ j : Fin 3, physPd (X τ) j y j = 0) ∧
    ∀ τ (y : Space), y ∉ axis → X τ y = L.rb τ y

/-- **`S = D₀r_b` off the axis** (source 4140-4141; `U = V + r_b`, so
`D₀U - D₀(V - U_raw) - D₀U_raw = D₀r_b` by linearity and locality of `D₀`, `U` smooth, `U_raw`
`C²` off the axis): for every jointly `C^∞` field `X` agreeing with `r_b` off the axis,
`dmuChg = D₀X` off the axis. -/
def DmuChgLinAt : Prop :=
  ∀ X : ℝ → Space → Space, ContDiff ℝ ∞ (fun q : ℝ × Space => X q.1 q.2) →
    (∀ τ (y : Space), y ∉ axis → X τ y = L.rb τ y) →
    ∀ τ (y : Space), y ∉ axis → dmuChg Pl L τ y = physDmu L.ν 0 X τ y

end Regime

namespace SeqData

variable (D : SeqData)

/-- `RawEqOffAxisAt` along the sequence. -/
def RawEqOffAxis : Prop := ∀ᶠ n : ℕ in atTop, RawEqOffAxisAt D.Pl (D.level n)

/-- `ExactPresDecayAt` along the sequence. -/
def ExactPresDecay : Prop := ∀ᶠ n : ℕ in atTop, ExactPresDecayAt (D.level n)

/-- `LiftPExtAt` along the sequence. -/
def LiftPExt : Prop := ∀ᶠ n : ℕ in atTop, LiftPExtAt (D.level n)

/-- `LiftPDecayAt` along the sequence. -/
def LiftPDecay : Prop := ∀ᶠ n : ℕ in atTop, LiftPDecayAt (D.level n)

/-- `RbExtAt` along the sequence. -/
def RbExt : Prop := ∀ᶠ n : ℕ in atTop, RbExtAt (D.level n)

/-- `DmuChgLinAt` along the sequence. -/
def DmuChgLin : Prop := ∀ᶠ n : ℕ in atTop, DmuChgLinAt D.Pl (D.level n)

end SeqData

/-! ## 4. Helpers -/

/-- `ε_n → 0` (source 5936-5940). -/
theorem pf2_retEps_tendsto {Pl : PlanarData} {σ₀ : ℝ} (hγ : 0 < Pl.eigenvalue.re)
    (hω : Pl.eigenvalue.im ≠ 0) :
    Tendsto (fun n : ℕ => retEps Pl σ₀ n) atTop (𝓝 0) := by
  have hνpos : ∀ n : ℕ, 0 < retNu Pl σ₀ n := fun n => retNu_pos Pl σ₀ n
  have hνT : Tendsto (retNu Pl σ₀) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨retNu_tendsto σ₀ hω, Eventually.of_forall hνpos⟩
  have hxT : Tendsto (fun n : ℕ => (retNu Pl σ₀ n)⁻¹) atTop atTop :=
    tendsto_inv_nhdsGT_zero.comp hνT
  have hG : Tendsto (fun x : ℝ => x ^ (-(Pl.kappa.re - 5 - 2 * σ₀)) *
      Real.exp (-Pl.eigenvalue.re * x)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero _ _ hγ
  have h2 : Tendsto (fun n : ℕ => ((retNu Pl σ₀ n)⁻¹) ^ (-(Pl.kappa.re - 5 - 2 * σ₀)) *
      Real.exp (-Pl.eigenvalue.re * (retNu Pl σ₀ n)⁻¹) / (2 * ‖Pl.signedCoeff σ₀‖)) atTop
      (𝓝 0) := by
    have h := (hG.comp hxT).div_const (2 * ‖Pl.signedCoeff σ₀‖)
    rw [zero_div] at h
    exact h
  have hbase : Tendsto (fun n : ℕ => Real.exp (-(Pl.eigenvalue.re / retNu Pl σ₀ n)) *
      retNu Pl σ₀ n ^ (Pl.kappa.re - 5 - 2 * σ₀) / (2 * ‖Pl.signedCoeff σ₀‖)) atTop (𝓝 0) := by
    refine Tendsto.congr' (Eventually.of_forall fun n => ?_) h2
    dsimp only
    rw [retAux_exp_mul_rpow _ _ _ (hνpos n)]
  exact hbase.rpow_const_nhds_zero (by norm_num : (0 : ℝ) < 1 / 3)

/-- **The source regime of the lift along the sequence**: for every `ν₀ > 0`, eventually
`ν_n < ν₀` and `R_n = ε_n⁻¹ ≥ 2` (the hypotheses of `IIb.RingLiftSmoothExt`,
`IIb.RingResidualCartesianNS`, `PartIIa.RingResidualBound`). -/
theorem SeqData.pf2_eventually_regime (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    {ν₀ : ℝ} (hν₀ : 0 < ν₀) :
    ∀ᶠ n : ℕ in atTop, (D.level n).ν < ν₀ ∧ 2 ≤ (D.level n).ε⁻¹ := by
  have h1 : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n < ν₀ :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (gt_mem_nhds hν₀)
  have h2 : ∀ᶠ n : ℕ in atTop, retEps D.Pl D.σ₀ n < 1 / 2 :=
    (pf2_retEps_tendsto hst.gamma_pos hst.omega_ne).eventually (gt_mem_nhds (by norm_num))
  filter_upwards [h1, h2] with n a b
  refine ⟨a, ?_⟩
  have hε : 0 < retEps D.Pl D.σ₀ n := retEps_pos D.coeff_ne n
  change 2 ≤ (retEps D.Pl D.σ₀ n)⁻¹
  rw [le_inv_comm₀ (by norm_num) hε]
  linarith

/-- The actual train of a level is an exact planar train at `c = ν^{-2}` (for
`IIb.RingLiftSmoothExt`, `IIb.RingResidualCartesianNS`). -/
theorem pf2_exactPlanarTrain (Pl : PlanarData) (L : ReturnLevel) :
    UnforcedLeray.Short.PartIIa.IsExactPlanarTrain L.ν (L.ν ^ (-(2 : ℝ)))
      (UnforcedLeray.Short.IIb.trainStream (L.params Pl))
      (UnforcedLeray.Short.IIb.trainPressure (L.params Pl)) :=
  UnforcedLeray.Short.IIb.isExactPlanarTrain_params_rpow (L.params Pl) L.train_buc rfl

/-- `physGrad = RieszLp.gradField`. -/
theorem pf2_physGrad_eq_gradField (q : Space → ℝ) : physGrad q = RieszLp.gradField q := by
  funext y
  ext j
  simp [physGrad, RieszLp.gradField, UnforcedLeray.spatialTestDerivative, coordinateVector,
    Pi.single_apply]

theorem pf2_physGrad_sub_const (q : Space → ℝ) (c : ℝ) :
    physGrad (fun y => q y - c) = physGrad q := by
  funext y
  simp only [physGrad, fderiv_sub_const]

/-- `IsSolenoidal` only sees the a.e. class. -/
theorem pf2_isSolenoidal_congr_ae {f g : SpatialField} (hf : UnforcedLeray.IsSolenoidal f)
    (h : f =ᵐ[volume] g) : UnforcedLeray.IsSolenoidal g := by
  refine ⟨fun φ hφ => (hf.integrable φ hφ).congr ?_, fun φ hφ => ?_⟩
  · filter_upwards [h] with x hx
    rw [hx]
  · rw [← hf.identity φ hφ]
    refine integral_congr_ae ?_
    filter_upwards [h] with x hx
    rw [hx]

/-- A field continuous off the axis is a.e. strongly measurable (the axis is null). -/
theorem pf2_aesm_of_continuousOn {f : Space → Space} (hf : ContinuousOn f axisᶜ) :
    AEStronglyMeasurable f volume := by
  have h1 : AEStronglyMeasurable f ((volume : Measure Space).restrict axisᶜ) :=
    hf.aestronglyMeasurable isOpen_compl_axis.measurableSet
  have h2 : (volume : Measure Space).restrict axisᶜ = volume :=
    Measure.restrict_eq_self_of_ae_mem ae_not_mem_axis
  rwa [h2] at h1

/-- Functions agreeing off the axis have the same gradient off the axis. -/
theorem pf2_physGrad_congr_offAxis {f g : Space → ℝ} (h : ∀ y : Space, y ∉ axis → f y = g y)
    {y : Space} (hy : y ∉ axis) : physGrad f y = physGrad g y := by
  have hev : f =ᶠ[𝓝 y] g :=
    Filter.eventuallyEq_of_mem (isOpen_compl_axis.mem_nhds hy) fun z hz => h z hz
  simp only [physGrad, hev.fderiv_eq]

theorem pf2_contDiff_pd {h : Space → Space} (hh : ContDiff ℝ ∞ h) (v : Space) :
    ContDiff ℝ ∞ (fun y => fderiv ℝ h y v) :=
  (hh.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- `D_μ X(τ)` is smooth for a jointly smooth `X` (as `contDiff_physDmu` of
`Sub/PartIII-b_C_ward_13_8_1.lean`). -/
theorem pf2_contDiff_physDmu (ν μ : ℝ) (X : ℝ → Space → Space)
    (hX : ContDiff ℝ ∞ (fun x : ℝ × Space => X x.1 x.2)) (τ : ℝ) :
    ContDiff ℝ ∞ (physDmu ν μ X τ) := by
  have hXt : ContDiff ℝ ∞ (X τ) := hX.comp (contDiff_const.prodMk contDiff_id)
  have h1 : ContDiff ℝ ∞ (fun y => deriv (fun t => X t y) τ) := by
    have : (fun y => deriv (fun t => X t y) τ) =
        fun y => fderiv ℝ (fun x : ℝ × Space => X x.1 x.2) (τ, y) (1, 0) := by
      funext y
      have hd : DifferentiableAt ℝ (fun x : ℝ × Space => X x.1 x.2) (τ, y) :=
        hX.differentiable (by simp) _
      have hs : HasFDerivAt (fun t : ℝ => ((t, y) : ℝ × Space))
          (ContinuousLinearMap.inl ℝ ℝ Space) τ :=
        hasFDerivAt_prodMk_left τ y
      have := hd.hasFDerivAt.comp τ hs
      rw [show (fun t => X t y) = (fun x : ℝ × Space => X x.1 x.2) ∘
          (fun t : ℝ => ((t, y) : ℝ × Space)) from rfl, this.hasDerivAt.deriv]
      simp
    rw [this]
    exact (hX.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
      |>.comp (contDiff_const.prodMk contDiff_id)
  have h2 : ContDiff ℝ ∞ (fun y => fderiv ℝ (X τ) y y) :=
    (hXt.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_id
  have h3 : ContDiff ℝ ∞ (physLap (X τ)) := by
    unfold physLap physPd2 physPd
    refine ContDiff.sum fun j _ => ?_
    exact pf2_contDiff_pd (pf2_contDiff_pd hXt _) _
  unfold physDmu
  exact ((h1.sub (h2.const_smul (1 / 2 : ℝ))).sub (h3.const_smul ν)).add
    (hXt.const_smul (μ - 1 / 2))

/-- The gradient of a slice of a jointly smooth off-axis function is continuous off the axis. -/
theorem pf2_physGrad_slice_contOn {F : ℝ × Space → ℝ} (hF : ContDiffOn ℝ ∞ F offAxisSet)
    (τ : ℝ) : ContinuousOn (physGrad fun y' => F (τ, y')) axisᶜ := by
  have hmaps : MapsTo (fun y : Space => ((τ, y) : ℝ × Space)) axisᶜ offAxisSet := fun y hy => hy
  exact (physGrad_continuousOn hF).comp (continuous_const.prodMk continuous_id).continuousOn hmaps

/-! ## 5. The reduction -/

section Reduction

variable (Pl : PlanarData) (L : ReturnLevel)

/-- **The pointwise identity off the axis** (source 4139-4141, 1263): `∇p - ∇p_lift = -S - G`. -/
theorem pf2_presDiff_offAxis {P : ℝ} (hE : IsExactProfile L.ν P L.U L.pres)
    (hA : RawEqOffAxisAt Pl L) (τ : ℝ) {y : Space} (hy : y ∉ axis) :
    physGrad (L.pres τ) y - physGrad (liftP L τ) y =
      -dmuChg Pl L τ y - presForce Pl L τ y := by
  have e1 := hE.equation τ y
  have hp : physGrad (L.pres τ) y =
      -(physDmu L.ν 0 L.U τ y + fderiv ℝ (L.U τ) y (L.U τ y)) :=
    eq_neg_of_add_eq_zero_right e1
  simp only [dmuChg, presForce, convChg, entSrc]
  rw [hA τ y hy, hp]
  abel

/-- **`convChg + entSrc + F_R` is continuous off the axis**: there it equals
`-(∇p - ∇p_lift) - D₀X` (`pf2_presDiff_offAxis`, `DmuChgLinAt`), with `p` smooth, `p_lift` smooth
off the axis (`liftP_contDiffOn`) and `X` smooth. -/
theorem pf2_presForce_contOn {P : ℝ} (hE : IsExactProfile L.ν P L.U L.pres)
    (hA : RawEqOffAxisAt Pl L) {X : ℝ → Space → Space}
    (hXs : ContDiff ℝ ∞ (fun q : ℝ × Space => X q.1 q.2))
    (hX : ∀ τ (y : Space), y ∉ axis → dmuChg Pl L τ y = physDmu L.ν 0 X τ y) (τ : ℝ) :
    ContinuousOn (presForce Pl L τ) axisᶜ := by
  have h1 : ContinuousOn (physGrad (L.pres τ)) axisᶜ :=
    pf2_physGrad_slice_contOn (F := fun x : ℝ × Space => L.pres x.1 x.2)
      hE.smoothP.contDiffOn τ
  have h2 : ContinuousOn (physGrad (liftP L τ)) axisᶜ :=
    pf2_physGrad_slice_contOn (liftP_contDiffOn L L.ε_pos) τ
  have h3 : ContinuousOn (physDmu L.ν 0 X τ) axisᶜ :=
    (pf2_contDiff_physDmu L.ν 0 X hXs τ).continuous.continuousOn
  have h4 : ContinuousOn (fun y => -(physGrad (L.pres τ) y - physGrad (liftP L τ) y) -
      physDmu L.ν 0 X τ y) axisᶜ :=
    ((h1.sub h2).neg).sub h3
  refine h4.congr fun y hy => ?_
  have e := pf2_presDiff_offAxis Pl L hE hA τ hy
  have e2 := hX τ y hy
  show presForce Pl L τ y = -(physGrad (L.pres τ) y - physGrad (liftP L τ) y) -
    physDmu L.ν 0 X τ y
  rw [← e2, e]
  abel

/-- **`presHelmholtzAt_of`** (source 5245-5260, 5272-5281, 1213-1225, 4139-4141): the raw lift
equation off the axis, the `L²` pressure of the exact background, the smooth extension and decay
of `p_lift`, and the solenoidality of `D₀r_b` give the pressure identity
`∇p - ∇p_lift = -(I-ℙ)(convChg + entSrc + F_R)`. -/
theorem presHelmholtzAt_of {P : ℝ} (hE : IsExactProfile L.ν P L.U L.pres)
    (hA : RawEqOffAxisAt Pl L) (hC1 : ExactPresDecayAt L) (hC2 : LiftPExtAt L)
    (hC3 : LiftPDecayAt L) (hD1 : DmuDivFreeSol) (hD2 : RbExtAt L) (hD3 : DmuChgLinAt Pl L) :
    PresHelmholtzAt Pl L := by
  obtain ⟨X, hXs, hXdiv, hXeq⟩ := hD2
  have hSX : ∀ τ (y : Space), y ∉ axis → dmuChg Pl L τ y = physDmu L.ν 0 X τ y :=
    hD3 X hXs hXeq
  intro τ
  refine ⟨pf2_aesm_of_continuousOn (pf2_presForce_contOn Pl L hE hA hXs hSX τ), fun hG => ?_⟩
  obtain ⟨⟨c, hpc⟩, hgp⟩ := hC1 τ
  obtain ⟨Pt, hPts, hPtEq⟩ := hC2 τ
  obtain ⟨⟨r, hr, hlr⟩, hgl⟩ := hC3 τ
  -- `S` is solenoidal
  have hsol : UnforcedLeray.IsSolenoidal (dmuChg Pl L τ) := by
    refine pf2_isSolenoidal_congr_ae (hD1 L.ν X hXs hXdiv τ) ?_
    filter_upwards [ae_not_mem_axis] with y hy
    exact (hSX τ y hy).symm
  -- the gradient of the smooth extension is that of `p_lift` off the axis
  have hPtg : ∀ y : Space, y ∉ axis → physGrad Pt y = physGrad (liftP L τ) y :=
    fun y hy => pf2_physGrad_congr_offAxis hPtEq hy
  have hPtr : MemLp Pt r volume := by
    refine hlr.ae_eq ?_
    filter_upwards [ae_not_mem_axis] with y hy
    exact (hPtEq y hy).symm
  have hg₂ : MemLp (physGrad Pt) (11 / 4) volume := by
    refine hgl.ae_eq ?_
    filter_upwards [ae_not_mem_axis] with y hy
    exact (hPtg y hy).symm
  -- the pointwise identity in terms of `physGrad Pt`
  have hpt : ∀ y : Space, y ∉ axis → physGrad (L.pres τ) y - physGrad Pt y =
      -dmuChg Pl L τ y - presForce Pl L τ y := by
    intro y hy
    rw [hPtg y hy]
    exact pf2_presDiff_offAxis Pl L hE hA τ hy
  -- `S ∈ L^{11/4}`
  have hSae : (fun y => -(physGrad (L.pres τ) y - physGrad Pt y) - presForce Pl L τ y)
      =ᵐ[volume] dmuChg Pl L τ := by
    filter_upwards [ae_not_mem_axis] with y hy
    rw [hpt y hy]
    abel
  have hS : MemLp (dmuChg Pl L τ) (11 / 4) volume := (((hgp.sub hg₂).neg).sub hG).ae_eq hSae
  -- the `L^{11/4}` classes
  set T := RieszLp.lerayLp (11 / 4) one_lt_elevenFourths elevenFourths_ne_top with hT
  set X₁ := hgp.toLp (physGrad (L.pres τ)) with hX₁
  set X₂ := hg₂.toLp (physGrad Pt) with hX₂
  set XG := hG.toLp (presForce Pl L τ) with hXG
  set XS := hS.toLp (dmuChg Pl L τ) with hXS
  have hsplit : XG = -(X₁ - X₂) - XS := by
    apply Lp.ext
    filter_upwards [hG.coeFn_toLp, hgp.coeFn_toLp, hg₂.coeFn_toLp, hS.coeFn_toLp,
      Lp.coeFn_sub (-(X₁ - X₂)) XS, Lp.coeFn_neg (X₁ - X₂), Lp.coeFn_sub X₁ X₂,
      ae_not_mem_axis] with y h1 h2 h3 h4 h5 h6 h7 hy
    rw [h5, Pi.sub_apply, h6, Pi.neg_apply, h7, Pi.sub_apply, h1, h2, h3, h4, hpt y hy]
    abel
  -- `ℙ∇(p - c) = 0`
  have hT₁ : T X₁ = 0 := by
    have hφ : ContDiff ℝ ∞ (fun y => L.pres τ y - c) :=
      (hE.smoothP.comp (contDiff_const.prodMk contDiff_id)).sub contDiff_const
    have hgr : RieszLp.gradField (fun y => L.pres τ y - c) = physGrad (L.pres τ) := by
      rw [← pf2_physGrad_eq_gradField, pf2_physGrad_sub_const]
    have hm : MemLp (RieszLp.gradField (fun y => L.pres τ y - c)) (11 / 4) volume := by
      rw [hgr]; exact hgp
    have h0 := RieszLp.lerayLp_gradient_eq_zero one_lt_elevenFourths elevenFourths_ne_top hφ
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hpc hm
    have he : hm.toLp (RieszLp.gradField (fun y => L.pres τ y - c)) = X₁ :=
      MemLp.toLp_congr hm hgp (Filter.EventuallyEq.of_eq hgr)
    rw [← he]
    exact h0
  -- `ℙ∇P̃ = 0`
  have hT₂ : T X₂ = 0 := by
    have hgr : RieszLp.gradField Pt = physGrad Pt := (pf2_physGrad_eq_gradField Pt).symm
    have hm : MemLp (RieszLp.gradField Pt) (11 / 4) volume := by
      rw [hgr]; exact hg₂
    have h0 := RieszLp.lerayLp_gradient_eq_zero one_lt_elevenFourths elevenFourths_ne_top hPts
      hr hPtr hm
    have he : hm.toLp (RieszLp.gradField Pt) = X₂ :=
      MemLp.toLp_congr hm hg₂ (Filter.EventuallyEq.of_eq hgr)
    rw [← he]
    exact h0
  -- `ℙS = S`
  have hTS : T XS = XS :=
    RieszLp.lerayLp_eq_self one_lt_elevenFourths elevenFourths_ne_top XS
      (pf2_isSolenoidal_congr_ae hsol hS.coeFn_toLp.symm)
  -- `(I - ℙ)G = -(∇p - ∇P̃)`
  have hkey : XG - T XG = -(X₁ - X₂) := by
    rw [hsplit, map_sub, map_neg, map_sub, hT₁, hT₂, hTS]
    abel
  have e : lerayComp114 (presForce Pl L τ) = ⇑(XG - T XG) := by
    simp only [lerayComp114, dif_pos hG]
    rfl
  rw [e, hkey]
  filter_upwards [Lp.coeFn_neg (X₁ - X₂), Lp.coeFn_sub X₁ X₂, hgp.coeFn_toLp, hg₂.coeFn_toLp,
    ae_not_mem_axis] with y h1 h2 h3 h4 hy
  rw [h1, Pi.neg_apply, neg_neg, h2, Pi.sub_apply, h3, h4, hPtg y hy]

end Reduction

/-- **`presHelmholtz_of`**: the pressure identity along the sequence (`SeqData.PresHelmholtz`) from
the level leaves and the two data-free leaves; `IsExactProfile` is `hst.actual.profile`. -/
theorem SeqData.presHelmholtz_of (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (hA : D.RawEqOffAxis) (hC1 : D.ExactPresDecay) (hC2 : D.LiftPExt) (hC3 : D.LiftPDecay)
    (hD1 : DmuDivFreeSol) (hD2 : D.RbExt) (hD3 : D.DmuChgLin) : D.PresHelmholtz := by
  filter_upwards [hst.actual, hA, hC1, hC2, hC3, hD2, hD3] with n hact a c1 c2 c3 d2 d3
  exact presHelmholtzAt_of D.Pl (D.level n) hact.profile a c1 c2 c3 hD1 d2 d3

end UnforcedLeray.Short.PartIIIb.Concrete
