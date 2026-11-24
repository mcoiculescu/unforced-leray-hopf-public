import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.PhasePrimitiveLeaf.CommDerivSplit.TimeDeriv
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.PhasePrimitiveLeaf.CommDerivSplit.MainBound

/-!
# Phase regularity of `outPrim` and spatial differentiability of `commPsi` (`CommDerivSplit/TimeReg`)

Proves for `Z = srcX0 ν μ (IIIa.thinSource ε F)` under `FarLeafOrg.ThinHyp c ρo F` and
`IIIa.thinMoment c F ≠ ⊤`, at any `y : Space` with `ρo / ε < ϱ y`:
1. `thin_outPrim_tau`: `ρ ↦ ρ * (∂_τ Z)(τ, !₂[ρ, 0, y 2])_2` is integrable on `Ioi (ϱ y)` and
   `HasDerivAt (fun t => outPrim Z t (ϱ y) (y 2)) (outPrim (∂_τ Z) τ (ϱ y) (y 2)) τ`.
2. `thin_comm_eq_add_nhds`: `comm ν μ R χy Z τ =ᶠ[𝓝 y] commMain ν R χy Z τ + commPsi ν μ R χy Z τ`.
3. `thin_commPsi_diffAt`: `DifferentiableAt ℝ (commPsi ν μ R χy Z τ) y`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.YBPhase

open YBComm FarLeafOrg UnforcedLeray.PhaseSpace

/-- `AEStronglyMeasurable` on `Ioi r` (`r > ρo / ε`) of `ρ ↦ ρ * (∂_τ X₀)_2(ρ, 0, z)` as the
pointwise limit of continuous difference quotients. -/
theorem thin_deriv_tau_aestronglyMeasurable {ν μ ε c ρo : ℝ}
    {F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hε : 0 < ε) (hc : 0 < c) (hρo : 0 ≤ ρo)
    (hth : ThinHyp c ρo F) (hN : IIIa.thinMoment c F ≠ ⊤)
    (τ z : ℝ) {r : ℝ} (hrr : ρo / ε < r) :
    AEStronglyMeasurable
      (fun ρ : ℝ => ρ * (deriv (fun s => srcX0 ν μ (IIIa.thinSource ε F) s !₂[ρ, 0, z]) τ) 2)
      (volume.restrict (Ioi r)) := by
  set Z : ℝ → Space → Space := srcX0 ν μ (IIIa.thinSource ε F)
  set rOut : ℝ := ρo / ε
  have hrOut0 : 0 ≤ rOut := div_nonneg hρo hε.le
  have hsub : Ioi r ⊆ Ioi rOut := Ioi_subset_Ioi hrr.le
  have hZ_cont : ∀ t : ℝ, ContinuousOn (fun ρ : ℝ => Z t !₂[ρ, 0, z] 2) (Ioi r) := by
    intro t
    have hcd : ContDiffOn ℝ 2 (Z t) {y : Space | rOut < ϱ y} :=
      (thin_X0_contDiffOn_top hν hμ hε hc hρo hth hN t).of_le (by simp)
    exact ((EuclideanSpace.proj (2 : Fin 3)).continuous.comp_continuousOn
      ((tcd_cont_val hrOut0 hcd z).mono hsub))
  set dq : ℕ → ℝ → ℝ := fun n ρ =>
    ρ * ((uN n)⁻¹ * (Z (τ + uN n) !₂[ρ, 0, z] 2 - Z τ !₂[ρ, 0, z] 2))
  have hdq_meas : ∀ n : ℕ, AEStronglyMeasurable (dq n) (volume.restrict (Ioi r)) := by
    intro n
    have hc_dq : ContinuousOn (dq n) (Ioi r) :=
      continuousOn_id.mul (continuousOn_const.mul ((hZ_cont (τ + uN n)).sub (hZ_cont τ)))
    exact hc_dq.aestronglyMeasurable measurableSet_Ioi
  have hlim : ∀ᵐ ρ ∂(volume.restrict (Ioi r)),
      Tendsto (fun n : ℕ => dq n ρ) atTop
        (𝓝 (ρ * (deriv (fun s => Z s !₂[ρ, 0, z]) τ) 2)) := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun ρ hρ => ?_)
    have hρ_out : rOut < ρ := hsub hρ
    have hρ0 : 0 ≤ ρ := hrOut0.trans hρ_out.le
    have hρr : rOut < ϱ (!₂[ρ, 0, z] : Space) := by
      rw [tcd_varrho hρ0]; exact hρ_out
    have hd := thin_hasDerivAt_tau hν hμ hε hc hρo hth hN τ hρr
    have hd_ : deriv (fun s => Z s !₂[ρ, 0, z]) τ =
        WithLp.toLp 2 fun i => (kerInt (IIIa.thinSource ε F) (kdDh ν μ) τ !₂[ρ, 0, z] i).re :=
      hd.deriv
    have hc2 : HasDerivAt (fun s => Z s !₂[ρ, 0, z] 2)
        ((deriv (fun s => Z s !₂[ρ, 0, z]) τ) 2) τ := by
      rw [hd_]
      exact (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt τ hd
    have hsl := (hasDerivAt_iff_tendsto_slope_zero.mp hc2).comp uN_tendsto
    exact hsl.const_mul ρ
  exact aestronglyMeasurable_of_tendsto_ae atTop hdq_meas hlim

/-- Integrability of `ρ * (∂_τ X₀)_2` along the half-line and differentiation of `outPrim` in `τ`. -/
theorem thin_outPrim_tau {ν μ ε c ρo : ℝ}
    {F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hε : 0 < ε) (hc : 0 < c) (hρo : 0 ≤ ρo)
    (hth : ThinHyp c ρo F) (hN : IIIa.thinMoment c F ≠ ⊤)
    (τ : ℝ) {y : Space} (hy : ρo / ε < ϱ y) :
    IntegrableOn
      (fun ρ : ℝ => ρ * (deriv (fun s => srcX0 ν μ (IIIa.thinSource ε F) s !₂[ρ, 0, y 2]) τ) 2)
      (Ioi (ϱ y)) ∧
    HasDerivAt (fun t => outPrim (srcX0 ν μ (IIIa.thinSource ε F)) t (ϱ y) (y 2))
      (outPrim (fun t y' => deriv (fun s => srcX0 ν μ (IIIa.thinSource ε F) s y') t)
        τ (ϱ y) (y 2)) τ := by
  set Z : ℝ → Space → Space := srcX0 ν μ (IIIa.thinSource ε F)
  set rOut : ℝ := ρo / ε
  have hrOut0 : 0 ≤ rOut := div_nonneg hρo hε.le
  obtain ⟨Cb, _hCb, hb⟩ := thin_deriv_tau_bound hν hμ hε hc hρo hth hN hy (y 2)
  have hint : Integrable (fun ρ : ℝ => Cb * (ρ - rOut) ^ (-(3 / 2 : ℝ)))
      (volume.restrict (Ioi (ϱ y))) :=
    (tcd_int_shift rOut (ϱ y) (sub_pos.2 hy)).const_mul Cb
  have hF'_meas : AEStronglyMeasurable
      (fun ρ : ℝ => ρ * (deriv (fun s => Z s !₂[ρ, 0, y 2]) τ) 2)
      (volume.restrict (Ioi (ϱ y))) :=
    thin_deriv_tau_aestronglyMeasurable hν hμ hε hc hρo hth hN τ (y 2) hy
  have hi2 : IntegrableOn
      (fun ρ : ℝ => ρ * (deriv (fun s => Z s !₂[ρ, 0, y 2]) τ) 2) (Ioi (ϱ y)) := by
    refine Integrable.mono' hint hF'_meas ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun ρ hρ => ?_)
    rw [Real.norm_eq_abs]
    exact hb τ ρ (le_of_lt hρ)
  refine ⟨hi2, ?_⟩
  have hsub : Ioi (ϱ y) ⊆ Ioi rOut := Ioi_subset_Ioi hy.le
  have hmeas : ∀ t : ℝ, AEStronglyMeasurable
      (fun ρ : ℝ => ρ * Z t (!₂[ρ, 0, y 2] : Space) 2) (volume.restrict (Ioi (ϱ y))) := by
    intro t
    have hcd : ContDiffOn ℝ 2 (Z t) {y' : Space | rOut < ϱ y'} :=
      (thin_X0_contDiffOn_top hν hμ hε hc hρo hth hN t).of_le (by simp)
    have hcont : ContinuousOn (fun ρ : ℝ => ρ * Z t (!₂[ρ, 0, y 2] : Space) 2) (Ioi (ϱ y)) :=
      continuousOn_id.mul ((EuclideanSpace.proj (2 : Fin 3)).continuous.comp_continuousOn
        ((tcd_cont_val hrOut0 hcd (y 2)).mono hsub))
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  have hZ_reg := spatial_outPrim_reg hrOut0 Z τ
    (thin_X0_contDiffOn_top hν hμ hε hc hρo hth hN τ)
    (thin_X0_far_decay hν hμ hε hc hρo hth hN τ)
  have h0 := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (ϱ y)))
    (F := fun t ρ => ρ * Z t (!₂[ρ, 0, y 2] : Space) 2)
    (F' := fun t ρ => ρ * (deriv (fun s => Z s (!₂[ρ, 0, y 2] : Space)) t) 2)
    (x₀ := τ) (bound := fun ρ : ℝ => Cb * (ρ - rOut) ^ (-(3 / 2 : ℝ)))
    (s := Set.univ) Filter.univ_mem (Eventually.of_forall hmeas)
    (hZ_reg.1 (ϱ y) (y 2) hy)
    hF'_meas
    (by
      refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun ρ hρ t _ => ?_)
      rw [Real.norm_eq_abs]
      exact hb t ρ (le_of_lt hρ))
    hint
    (by
      refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun ρ hρ t _ => ?_)
      have hρ_out : rOut < ρ := hsub hρ
      have hρ0 : 0 ≤ ρ := hrOut0.trans hρ_out.le
      have hρr : rOut < ϱ (!₂[ρ, 0, y 2] : Space) := by
        rw [tcd_varrho hρ0]; exact hρ_out
      have hd := thin_hasDerivAt_tau hν hμ hε hc hρo hth hN t hρr
      have hc2 : HasDerivAt (fun s => Z s (!₂[ρ, 0, y 2] : Space) 2)
          ((deriv (fun s => Z s (!₂[ρ, 0, y 2] : Space)) t) 2) t := by
        rw [hd.deriv]
        exact (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hd
      exact hc2.const_mul ρ)
  unfold outPrim
  exact h0.2.neg

/-- Phase derivative of `psiFld` for `thinSource ε F` off the old disk. -/
theorem thin_psi_tau {ν μ ε c ρo : ℝ}
    {F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hε : 0 < ε) (hc : 0 < c) (hρo : 0 ≤ ρo)
    (hth : ThinHyp c ρo F) (hN : IIIa.thinMoment c F ≠ ⊤)
    (τ : ℝ) {y : Space} (hy : ρo / ε < ϱ y) :
    HasDerivAt (fun t => psiFld (srcX0 ν μ (IIIa.thinSource ε F)) t y)
      (psiFld (fun t y' => deriv (fun s => srcX0 ν μ (IIIa.thinSource ε F) s y') t) τ y) τ :=
  (thin_outPrim_tau hν hμ hε hc hρo hth hN τ hy).2.smul_const (UnforcedLeray.coordinateVector 2)

/-- Local equality `comm = commMain + commPsi` on a neighborhood of `y` (`ρo / ε < ϱ y`). -/
theorem thin_comm_eq_add_nhds {ν μ R ε c ρo : ℝ} {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy)
    {F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hε : 0 < ε) (hc : 0 < c) (hρo : 0 ≤ ρo)
    (hth : ThinHyp c ρo F) (hN : IIIa.thinMoment c F ≠ ⊤)
    (τ : ℝ) {y : Space} (hy : ρo / ε < ϱ y) :
    comm ν μ R χy (srcX0 ν μ (IIIa.thinSource ε F)) τ =ᶠ[𝓝 y]
      fun y' => commMain ν R χy (srcX0 ν μ (IIIa.thinSource ε F)) τ y' +
        commPsi ν μ R χy (srcX0 ν μ (IIIa.thinSource ε F)) τ y' := by
  set Z : ℝ → Space → Space := srcX0 ν μ (IIIa.thinSource ε F)
  set rOut : ℝ := ρo / ε
  have hrOut0 : 0 ≤ rOut := div_nonneg hρo hε.le
  have hU : IsOpen {y' : Space | rOut < ϱ y'} := isOpen_lt continuous_const continuous_ϱ
  have hZ_cd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Z τ) {y' : Space | rOut < ϱ y'} :=
    thin_X0_contDiffOn_top hν hμ hε hc hρo hth hN τ
  have hψ_cd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (psiFld Z τ) {y' : Space | rOut < ϱ y'} :=
    (spatial_outPrim_reg hrOut0 Z τ hZ_cd (thin_X0_far_decay hν hμ hε hc hρo hth hN τ)).2.2.2.2.1
  filter_upwards [hU.mem_nhds hy] with y' hy'
  have hρ' : 0 < ϱ y' := lt_of_le_of_lt hrOut0 hy'
  have hZc : ContDiffAt ℝ 2 (Z τ) y' :=
    (hZ_cd.of_le (by simp)).contDiffAt (hU.mem_nhds hy')
  have hZt : DifferentiableAt ℝ (fun t => Z t y') τ :=
    (thin_hasDerivAt_tau hν hμ hε hc hρo hth hN τ hy').differentiableAt
  have hψc : ContDiffAt ℝ 2 (psiFld Z τ) y' :=
    (hψ_cd.of_le (by simp)).contDiffAt (hU.mem_nhds hy')
  have hψt : DifferentiableAt ℝ (fun t => psiFld Z t y') τ :=
    (thin_psi_tau hν hμ hε hc hρo hth hN τ hy').differentiableAt
  exact comm_eq_commMain_add_commPsi_of_reg hχ Z τ hρ' hZc hZt hψc hψt

/-- `tcF0 ν R χy` is `C³` away from `0`. -/
theorem tcle_f0_smooth3 {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy) (ν R : ℝ) {r : ℝ} (hr : r ≠ 0) :
    ContDiffAt ℝ 3 (tcF0 ν R χy) r := by
  have hin : ContDiffAt ℝ 3 (fun r : ℝ => ν * (R ^ 2 / r ^ 2)) r :=
    contDiffAt_const.mul (contDiffAt_const.div (contDiffAt_id.pow 2) (pow_ne_zero 2 hr))
  have h1 : ContDiff ℝ 3 (deriv χy) :=
    ((contDiff_infty_iff_deriv.mp hχ.smooth).2).of_le (by simp)
  have a : ContDiffAt ℝ 3 (fun r : ℝ => deriv χy (ν * (R ^ 2 / r ^ 2))) r :=
    h1.contDiffAt.comp r hin
  have b : ContDiffAt ℝ 3 (fun r : ℝ => -2 * ν * R ^ 2 / r ^ 3) r :=
    contDiffAt_const.div (contDiffAt_id.pow 3) (pow_ne_zero 3 hr)
  exact (a.mul b).div contDiffAt_id hr

/-- Spatial differentiability of `commPsi` at `y` (`ρo / ε < ϱ y`). -/
theorem thin_commPsi_diffAt {ν μ R ε c ρo : ℝ} {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy)
    {F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hε : 0 < ε) (hc : 0 < c) (hρo : 0 ≤ ρo)
    (hth : ThinHyp c ρo F) (hN : IIIa.thinMoment c F ≠ ⊤)
    (τ : ℝ) {y : Space} (hy : ρo / ε < ϱ y) :
    DifferentiableAt ℝ (commPsi ν μ R χy (srcX0 ν μ (IIIa.thinSource ε F)) τ) y := by
  set Z : ℝ → Space → Space := srcX0 ν μ (IIIa.thinSource ε F)
  set rOut : ℝ := ρo / ε
  have hrOut0 : 0 ≤ rOut := div_nonneg hρo hε.le
  set U : Set Space := {y' : Space | rOut < ϱ y'}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_ϱ
  have hZ_cd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Z τ) U :=
    thin_X0_contDiffOn_top hν hμ hε hc hρo hth hN τ
  obtain ⟨hi1, hi3, hi4, hO1, hψ_cd, hO3, hO4⟩ :=
    spatial_outPrim_reg hrOut0 Z τ hZ_cd (thin_X0_far_decay hν hμ hε hc hρo hth hN τ)
  -- Express commPsi on U without ∂_τ Z by cancelling outPrim (∂_τ Z)
  set S : Space → Space := fun y' =>
    - (1 / 2 : ℝ) • fderiv ℝ (cutPsi ν R χy Z τ) y' y'
    - ν • physLap (cutPsi ν R χy Z τ) y'
    + (μ + 1 - 1 / 2) • cutPsi ν R χy Z τ y'
    - tcF0 ν R χy (ϱ y') •
        ((- (1 / 2 : ℝ) * outPrim (fun t y'' => fderiv ℝ (Z t) y'' y'') τ (ϱ y') (y' 2) -
          ν * outPrim (fun t y'' => physLap (Z t) y'') τ (ϱ y') (y' 2) +
          (μ + 1 - 1 / 2) * outPrim Z τ (ϱ y') (y' 2)) •
            (UnforcedLeray.coordinateVector 2 : Space))
  have heq : commPsi ν μ R χy Z τ =ᶠ[𝓝 y] S := by
    filter_upwards [hU.mem_nhds hy] with y' hy'
    obtain ⟨hi2, hd_out⟩ := thin_outPrim_tau hν hμ hε hc hρo hth hN τ hy'
    have hd_cut : deriv (fun t => cutPsi ν R χy Z t y') τ =
        tcF0 ν R χy (ϱ y') •
          (outPrim (fun t y'' => deriv (fun s => Z s y'') t) τ (ϱ y') (y' 2) •
            (UnforcedLeray.coordinateVector 2 : Space)) := by
      have hhd : HasDerivAt (fun t => cutPsi ν R χy Z t y')
          (tcF0 ν R χy (ϱ y') •
            (outPrim (fun t y'' => deriv (fun s => Z s y'') t) τ (ϱ y') (y' 2) •
              (UnforcedLeray.coordinateVector 2 : Space))) τ :=
        (hd_out.smul_const (UnforcedLeray.coordinateVector 2)).const_smul (tcF0 ν R χy (ϱ y'))
      exact hhd.deriv
    have hlin := tcle_outPrim_lin ν (μ + 1) Z τ (ϱ y') (y' 2)
      (hi1 (ϱ y') (y' 2) hy') hi2 (hi3 (ϱ y') (y' 2) hy') (hi4 (ϱ y') (y' 2) hy')
    show commPsi ν μ R χy Z τ y' = S y'
    unfold commPsi physDmu
    rw [hd_cut]
    change (tcF0 ν R χy (ϱ y') •
        (outPrim (fun t y'' => deriv (fun s => Z s y'') t) τ (ϱ y') (y' 2) •
          (UnforcedLeray.coordinateVector 2 : Space)) -
      (1 / 2 : ℝ) • fderiv ℝ (cutPsi ν R χy Z τ) y' y' -
      ν • physLap (cutPsi ν R χy Z τ) y' +
      (μ + 1 - 1 / 2) • cutPsi ν R χy Z τ y') -
      tcF0 ν R χy (ϱ y') • (outPrim (physDmu ν (μ + 1) Z) τ (ϱ y') (y' 2) •
        (UnforcedLeray.coordinateVector 2 : Space)) = S y'
    rw [hlin]
    dsimp only [S]
    ext i
    simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  -- Prove S is DifferentiableAt ℝ at y
  have hF_cd3 : ContDiffOn ℝ 3 (fun y' : Space => tcF0 ν R χy (ϱ y')) U := by
    intro y' hy'
    have hρ' : 0 < ϱ y' := lt_of_le_of_lt hrOut0 hy'
    have hya : y' ∉ axis := tcle_notaxis hρ'
    have hϱ3 : ContDiffAt ℝ 3 ϱ y' :=
      contDiffOn_ϱ.contDiffAt (isOpen_compl_axis.mem_nhds hya)
    exact ((tcle_f0_smooth3 hχ ν R hρ'.ne').comp y' hϱ3).contDiffWithinAt
  have hcut_cd3 : ContDiffOn ℝ 3 (cutPsi ν R χy Z τ) U :=
    hF_cd3.smul (hψ_cd.of_le (by simp))
  have hcut_diff : DifferentiableAt ℝ (cutPsi ν R χy Z τ) y :=
    (hcut_cd3.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)
  have hfderiv_cd2 : ContDiffOn ℝ 2 (fderiv ℝ (cutPsi ν R χy Z τ)) U :=
    hcut_cd3.fderiv_of_isOpen hU (by norm_num)
  have hd_ydir : DifferentiableAt ℝ (fun y' : Space => fderiv ℝ (cutPsi ν R χy Z τ) y' y') y :=
    ((hfderiv_cd2.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)).clm_apply
      differentiableAt_id
  have hd_lap : DifferentiableAt ℝ (physLap (cutPsi ν R χy Z τ)) y := by
    unfold physLap physPd2 physPd
    refine DifferentiableAt.fun_sum fun j _ => ?_
    have hpd_cd2 : ContDiffOn ℝ 2
        (fun y' : Space => fderiv ℝ (cutPsi ν R χy Z τ) y' (UnforcedLeray.coordinateVector j)) U :=
      hfderiv_cd2.clm_apply contDiffOn_const
    have hpd2_cd1 : ContDiffOn ℝ 1
        (fun y' : Space => fderiv ℝ
          (fun y'' => fderiv ℝ (cutPsi ν R χy Z τ) y'' (UnforcedLeray.coordinateVector j)) y'
          (UnforcedLeray.coordinateVector j)) U :=
      (hpd_cd2.fderiv_of_isOpen hU (by norm_num)).clm_apply contDiffOn_const
    exact (hpd2_cd1.contDiffAt (hU.mem_nhds hy)).differentiableAt one_ne_zero
  have hd_F : DifferentiableAt ℝ (fun y' : Space => tcF0 ν R χy (ϱ y')) y :=
    (hF_cd3.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)
  have hd_O1 : DifferentiableAt ℝ (fun y' : Space => outPrim Z τ (ϱ y') (y' 2)) y :=
    (hO1.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)
  have hd_O3 : DifferentiableAt ℝ
      (fun y' : Space => outPrim (fun t y'' => fderiv ℝ (Z t) y'' y'') τ (ϱ y') (y' 2)) y :=
    (hO3.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)
  have hd_O4 : DifferentiableAt ℝ
      (fun y' : Space => outPrim (fun t y'' => physLap (Z t) y'') τ (ϱ y') (y' 2)) y :=
    (hO4.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)
  have hd_comb : DifferentiableAt ℝ
      (fun y' : Space =>
        - (1 / 2 : ℝ) * outPrim (fun t y'' => fderiv ℝ (Z t) y'' y'') τ (ϱ y') (y' 2) -
          ν * outPrim (fun t y'' => physLap (Z t) y'') τ (ϱ y') (y' 2) +
          (μ + 1 - 1 / 2) * outPrim Z τ (ϱ y') (y' 2)) y :=
    (((hd_O3.const_mul (-(1 / 2 : ℝ))).sub (hd_O4.const_mul ν)).add
      (hd_O1.const_mul (μ + 1 - 1 / 2)))
  have hd_S : DifferentiableAt ℝ S y := by
    dsimp only [S]
    exact ((((hd_ydir.const_smul (-(1 / 2 : ℝ))).sub (hd_lap.const_smul ν)).add
      (hcut_diff.const_smul (μ + 1 - 1 / 2))).sub
      (hd_F.smul (hd_comb.smul_const (UnforcedLeray.coordinateVector 2 : Space))))
  exact hd_S.congr_of_eventuallyEq heq

end UnforcedLeray.Short.PartIIIb.Concrete.YBPhase

end
