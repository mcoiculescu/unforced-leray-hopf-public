import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_3.VResidual.Meas
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_1_4
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.TransTable.ThinChart

/-!
# Instantiation of the background hypothesis (H) (`PartIII-b:C/rep/3/4`)

Source `the November 2 reference manuscript`:
- lines 5131-5139 (`V = U_raw + E_ε α_bg` and its background bounds),
- lines 2703-2723 (`StressCoefficients` fourth clause: `‖sup_q |v(s,q,·)|‖_{L²_η} ≤ P_ν`),
- lines 5225-5235 (`vEtaSup` and `R⁻¹(‖DV‖_{Y_2} + ‖D²V‖_{Y_2} + ‖V⊗V‖_{Y_2}) ≤ P_ν`),
- lines 5245-5247 (`∇p_V = -(I-ℙ)(V·∇V)` and `R⁻¹‖∇p_V‖_{Y_2} ≤ P_ν`),
- lines 5255-5258 (`∇(p-p_V) = -(I-ℙ)(V·∇r_b + r_b·∇V + r_b·∇r_b)` and `‖∇(p-p_V)‖_{Y_{11/4}} ≤ P_ν ρ`),
- lines 2607-2612, 2641-2642 (exported background split bounds in Part II-b).

## What is proved unconditionally here
1. `repVBg_contDiffOn`: `ContDiffOn ℝ 2 (fun x : ℝ × Space => (D.level n).V x.1 x.2) {x | 0 < ϱ x.2}`
   eventually in `n`, from `rawU_contDiffOn_offAxis_of` and `IIb.inletJointSmooth`.
2. `repVBg_vEtaSup`: `vEtaSup (D.level n).ε⁻¹ (cOf (D.level n).ν) (D.level n).V s ≤ ENNReal.ofReal (C * (D.level n).ν⁻¹ ^ k)`
   eventually in `n` for all `s > 0`, from `IIIa.stressCoefficients_of IIIa.rawCoeffLate IIIa.rawCoeffEarly IIIa.inletCoeffBounds`
   together with `1 ≤ transWeight` and vanishing of the azimuthal component of `V = raw + ∑ c_i • inlet_i` at `chartY`.
3. `repVBg_vCoefDens_meas`: `AEStronglyMeasurable (ringRead (D.level n).ε⁻¹ fun τ => vCoefDens ((D.level n).V τ)) (ringPhysμ (D.level n).ε⁻¹ (cOf (D.level n).ν))`
   eventually in `n`, from `jet_continuousOn` and `aestronglyMeasurable_ringRead`.
4. `repVBg_presChgDens_meas_of_contDiff`: `AEStronglyMeasurable (ringRead L.ε⁻¹ fun τ => presChgDens (L.pres τ) (pV τ)) (ringPhysμ L.ε⁻¹ (cOf L.ν))`
   from `IsExactProfile.smoothP` and `ContDiff ℝ 1 (fun x : ℝ × Space => pV x.1 x.2)`.

## Missing background facts (stated as leaf `Prop`s below)
- `RepVCoefY2` (`PartIII-b:C/rep/3/4/1`, source lines 5234-5235, 5131-5139, 2607-2612):
  `R⁻¹(‖DV‖_{Y_2} + ‖D²V‖_{Y_2} + ‖V⊗V‖_{Y_2}) ≤ P_ν` in chart form (`vCoefDens`).
- `RepVPres` (`PartIII-b:C/rep/3/4/2`, source lines 5245-5247, 5255-5258, 2641-2642):
  existence of the `C¹` canonical pressure `p_V` satisfying `R⁻¹‖∇p_V‖_{Y_2} ≤ P_ν` and
  `‖∇p - ∇p_V‖_{Y_{11/4}} ≤ P_ν ρ` in chart form (or `RepPresGradY2` via `repVPres_of_presGradY2`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-! ## 1. Unconditional off-axis `C²` smoothness of `V` and measurability of `vCoefDens` and `presChgDens` -/

/-- Joint `C²` smoothness of `(τ, y) ↦ (D.level n).V τ y` on `{x | 0 < ϱ x.2}` for large `n`
(source 5131-5133, 5225). -/
theorem repVBg_contDiffOn (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    ∀ᶠ n : ℕ in atTop,
      ContDiffOn ℝ 2 (fun x : ℝ × Space => (D.level n).V x.1 x.2) {x | 0 < ϱ x.2} := by
  obtain ⟨ν₀, hν₀, hS⟩ := UnforcedLeray.Short.IIb.inletJointSmooth D.Sig D.Pl.eigenvalue D.Pl.mode
    D.Sig_pos hst.planar.eigenpair dm dp hst.dm_pos
  have hν : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n < ν₀ :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (gt_mem_nhds hν₀)
  have hInlet : ∀ᶠ n : ℕ in atTop, ∀ i : Fin 2,
      ContDiff ℝ ∞ (fun x : ℝ × Space => ((D.level n).params D.Pl).inlet i x.1 x.2) := by
    filter_upwards [hst.actual, hν] with n hn hνn
    exact fun i => hS ((D.level n).params D.Pl) _ hn.regime hνn.le rfl rfl i
  have hRaw : ∀ᶠ n : ℕ in atTop,
      ContDiffOn ℝ 2 (fun x : ℝ × Space => ((D.level n).params D.Pl).raw x.1 x.2) offAxis := by
    filter_upwards [hst.actual] with n _hn
    exact rawU_contDiffOn_offAxis_of ((D.level n).params D.Pl) (D.level n).ε_pos
      ((D.level n).train_stream_smooth.of_le (by norm_num))
  filter_upwards [hst.actual, hRaw, hInlet] with n hn hr hi
  rw [vr_offAxis_eq]
  obtain ⟨z, -, hVz, -, -⟩ := hn.split.state
  have he : (fun x : ℝ × Space => (D.level n).V x.1 x.2) =
      fun x : ℝ × Space => ((D.level n).params D.Pl).raw x.1 x.2 +
        ∑ i : Fin 2, ((D.level n).params D.Pl).coord z i •
          ((D.level n).params D.Pl).inlet i x.1 x.2 := by
    funext x
    exact hVz x.1 x.2
  rw [he]
  refine hr.add ?_
  have hi2 : ∀ i : Fin 2, ContDiffOn ℝ 2
      (fun x : ℝ × Space => ((D.level n).params D.Pl).inlet i x.1 x.2) offAxis :=
    fun i => ((hi i).of_le (by norm_num)).contDiffOn
  refine ContDiffOn.sum fun i _ => ?_
  exact (hi2 i).const_smul _

/-- Continuity of `vCoefDens` on an open set where `F` is jointly `C²`. -/
theorem vCoefDens_continuousOn {O : Set (ℝ × Space)} (hO : IsOpen O) {F : ℝ × Space → Space}
    (hF : ContDiffOn ℝ 2 F O) :
    ContinuousOn (fun x : ℝ × Space => vCoefDens (fun y => F (x.1, y)) x.2) O := by
  obtain ⟨f0, f1, f2⟩ := jet_continuousOn hO hF
  unfold vCoefDens
  refine ContinuousOn.add (ContinuousOn.add ?_ ?_) ?_
  · exact f0.norm.pow 2
  · exact continuousOn_finsetSum _ fun j _ => (f1 j).norm
  · exact continuousOn_finsetSum _ fun j _ =>
      continuousOn_finsetSum _ fun l _ => (f2 j l).norm

/-- Measurability of the chart reading of `vCoefDens (L.V τ)` for any level with `V` jointly `C²`
off the axis. -/
theorem repVBg_vCoefDens_meas_of_contDiffOn (L : ReturnLevel)
    (hV : ContDiffOn ℝ 2 (fun x : ℝ × Space => L.V x.1 x.2) {x | 0 < ϱ x.2}) :
    AEStronglyMeasurable (ringRead L.ε⁻¹ fun τ => vCoefDens (L.V τ))
      (ringPhysμ L.ε⁻¹ (cOf L.ν)) := by
  rw [vr_offAxis_eq] at hV
  exact aestronglyMeasurable_ringRead (inv_ne_zero L.ε_pos.ne') (cOf_pos L.ν_pos)
    (vCoefDens_continuousOn isOpen_offAxis hV)

/-- Eventual measurability of `ringRead (D.level n).ε⁻¹ fun τ => vCoefDens ((D.level n).V τ)`
along the sequence (source 5234-5235). -/
theorem repVBg_vCoefDens_meas (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    ∀ᶠ n : ℕ in atTop,
      AEStronglyMeasurable (ringRead (D.level n).ε⁻¹ fun τ => vCoefDens ((D.level n).V τ))
        (ringPhysμ (D.level n).ε⁻¹ (cOf (D.level n).ν)) := by
  filter_upwards [repVBg_contDiffOn D hst] with n hV
  exact repVBg_vCoefDens_meas_of_contDiffOn (D.level n) hV

/-- Joint continuity of `(τ, y) ↦ physGrad (F τ) y` when `(τ, y) ↦ F τ y` is `C¹`. -/
theorem physGrad_continuous_of_contDiff {F : ℝ × Space → ℝ} (hF : ContDiff ℝ 1 F) :
    Continuous (fun x : ℝ × Space => physGrad (fun y => F (x.1, y)) x.2) := by
  have hcont : Continuous (fun x => fderiv ℝ F x) := hF.continuous_fderiv (by norm_num)
  have hG : Continuous (fun x : ℝ × Space =>
      (WithLp.toLp 2 (fun j : Fin 3 => fderiv ℝ F x (0, coordinateVector j)) : Space)) := by
    refine (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp ?_
    refine continuous_pi fun j => ?_
    exact hcont.clm_apply continuous_const
  have heq : (fun x : ℝ × Space => physGrad (fun y => F (x.1, y)) x.2) =
      fun x : ℝ × Space =>
        (WithLp.toLp 2 (fun j : Fin 3 => fderiv ℝ F x (0, coordinateVector j)) : Space) := by
    funext x
    have hd : DifferentiableAt ℝ F x := (hF.differentiable (by norm_num)) x
    have hg : HasFDerivAt (fun y : Space => (x.1, y))
        (ContinuousLinearMap.inr ℝ ℝ Space) x.2 :=
      (hasFDerivAt_const x.1 x.2).prodMk (hasFDerivAt_id x.2)
    have hc : HasFDerivAt (fun y : Space => F (x.1, y))
        ((fderiv ℝ F x).comp (ContinuousLinearMap.inr ℝ ℝ Space)) x.2 :=
      HasFDerivAt.comp x.2 hd.hasFDerivAt hg
    unfold physGrad
    congr 1
    funext j
    rw [hc.fderiv]
    rfl
  rwa [heq]

/-- Measurability of the chart reading of `presChgDens (L.pres τ) (pV τ)` when `L.pres` and `pV`
are `C¹` (source 5255-5258). -/
theorem repVBg_presChgDens_meas_of_contDiff (L : ReturnLevel) {pV : ℝ → Space → ℝ}
    (hP : ContDiff ℝ 1 (fun x : ℝ × Space => L.pres x.1 x.2))
    (hpV : ContDiff ℝ 1 (fun x : ℝ × Space => pV x.1 x.2)) :
    AEStronglyMeasurable (ringRead L.ε⁻¹ fun τ => presChgDens (L.pres τ) (pV τ))
      (ringPhysμ L.ε⁻¹ (cOf L.ν)) := by
  have h1 := physGrad_continuous_of_contDiff hP
  have h2 := physGrad_continuous_of_contDiff hpV
  have hcont : Continuous (fun x : ℝ × Space => presChgDens (L.pres x.1) (pV x.1) x.2) :=
    (h1.sub h2).norm
  exact aestronglyMeasurable_ringRead (inv_ne_zero L.ε_pos.ne') (cOf_pos L.ν_pos)
    hcont.continuousOn

/-! ## 2. Unconditional `vEtaSup` bound from `IIIa.StressCoefficients` -/

private theorem Nv_chartPoint_apply_one {R : ℝ} (hR : 0 < R) (b : ℝ × (ℝ × ℝ) → Merid)
    {pt : ℝ × (ℝ × ℝ)} (hs : 0 < pt.1) :
    Nv R b (NearInst.chartTau R pt) (NearInst.chartY R pt) 1 = 0 := by
  change Nv R b (IIIa.chartPhase R pt) (IIIa.chartPoint R pt) 1 = 0
  rw [Nv, IIIa.age_chartPoint hR hs, IIIa.chart_chartPoint hR hs, frameL_apply,
    IIIa.eR_chartPoint hR hs]
  simp

private theorem norm_space_eq_norm_merid {w : Space} (hw : w 1 = 0) :
    ‖w‖ = ‖(!₂[w 0, w 2] : Merid)‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_three, Fin.sum_univ_two]
  simp [hw]

private theorem one_le_transWeight {mZ : ℝ} (hmZ : 0 ≤ mZ) (pt : ℝ × (ℝ × ℝ)) :
    1 ≤ IIIa.transWeight mZ pt := by
  unfold IIIa.transWeight
  exact Real.one_le_rpow (by linarith [sq_nonneg (pt.2.2 / Real.sqrt (1 + pt.1))]) (by linarith)

/-- When `V (chartTau R (s,(q,η))) (chartY R (s,(q,η))) 1 = 0` and `0 ≤ mZ`, `vEtaSup` is bounded by
`IIIa.etaL2QSup` (source 5225-5232, 2717-2723). -/
theorem vEtaSup_le_etaL2QSup {R c mZ s : ℝ} (hmZ : 0 ≤ mZ)
    {V : ℝ → SpatialField}
    (hV1 : ∀ q η : ℝ, V (NearInst.chartTau R (s, (q, η))) (NearInst.chartY R (s, (q, η))) 1 = 0) :
    vEtaSup R c V s ≤ IIIa.etaL2QSup c mZ (IIIa.chartCoeff R V) s := by
  unfold vEtaSup IIIa.etaL2QSup
  refine ENNReal.rpow_le_rpow (lintegral_mono fun η => ?_) (by norm_num)
  refine ENNReal.rpow_le_rpow (essSup_mono_ae (Eventually.of_forall fun q => ?_)) (by norm_num)
  dsimp only
  have hw := hV1 q η
  have hnorm : ‖V (NearInst.chartTau R (s, (q, η))) (NearInst.chartY R (s, (q, η)))‖ =
      ‖(!₂[V (NearInst.chartTau R (s, (q, η))) (NearInst.chartY R (s, (q, η))) 0,
          V (NearInst.chartTau R (s, (q, η))) (NearInst.chartY R (s, (q, η))) 2] : Merid)‖ :=
    norm_space_eq_norm_merid hw
  have hsq : 0 ≤ (Real.sqrt s)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg s)
  have hcoeff : ‖IIIa.chartCoeff R V (s, (q, η))‖ =
      (Real.sqrt s)⁻¹ * ‖V (NearInst.chartTau R (s, (q, η))) (NearInst.chartY R (s, (q, η)))‖ := by
    change ‖(Real.sqrt s)⁻¹ •
      (!₂[V (NearInst.chartTau R (s, (q, η))) (NearInst.chartY R (s, (q, η))) 0,
          V (NearInst.chartTau R (s, (q, η))) (NearInst.chartY R (s, (q, η))) 2] : Merid)‖ = _
    rw [norm_smul, Real.norm_of_nonneg hsq, hnorm]
  have hW : 1 ≤ IIIa.transWeight mZ (s, (q, η)) := one_le_transWeight hmZ (s, (q, η))
  rw [← ofReal_norm, hcoeff, ← ENNReal.ofReal_mul (by linarith)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hnn : 0 ≤ (Real.sqrt s)⁻¹ *
      ‖V (NearInst.chartTau R (s, (q, η))) (NearInst.chartY R (s, (q, η)))‖ := by positivity
  nlinarith

/-- Eventual bound on `vEtaSup` along the concrete sequence from `IIIa.StressCoefficients`
(source 2703-2723, 5225-5232). -/
theorem repVBg_vEtaSup (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ s : ℝ, 0 < s →
      vEtaSup (D.level n).ε⁻¹ (cOf (D.level n).ν) (D.level n).V s ≤
        ENNReal.ofReal (C * (D.level n).ν⁻¹ ^ k) := by
  have hSC : UnforcedLeray.Short.IIIa.StressCoefficients :=
    UnforcedLeray.Short.IIIa.stressCoefficients_of
      UnforcedLeray.Short.IIIa.rawCoeffLate
      UnforcedLeray.Short.IIIa.rawCoeffEarly
      UnforcedLeray.Short.IIIa.inletCoeffBounds
  obtain ⟨C, k, ν₀, hν₀, h⟩ := hSC dm dp hst.dm_pos D.K.m0 D.K.C0 D.K.k0 hst.m0_pos
    hst.m0_lt.le D.K.mZ hst.mZ_gt D.Sig D.Pl.eigenvalue D.Pl.mode D.Sig_pos hst.planar.eigenpair
  refine ⟨2 * (|C| + 1), k, by positivity, ?_⟩
  have hev2 := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  filter_upwards [hst.actual, (retNu_tendsto D.σ₀ hst.omega_ne).eventually (ge_mem_nhds hν₀),
    hev2] with n hn hν e2 s hs
  have hν0 : 0 < (D.level n).ν := (D.level n).ν_pos
  have hε : 0 < (D.level n).ε := (D.level n).ε_pos
  have hR : 0 < (D.level n).ε⁻¹ := inv_pos.2 hε
  have hmZ : 0 ≤ D.K.mZ := by linarith [hst.mZ_gt]
  have hv := h ((D.level n).params D.Pl) _ hn.regime hν rfl rfl (D.Sin n) (D.V n) (D.rb n) hn.split
  obtain ⟨z, -, hVz, -, -⟩ := hn.split.state
  have hV1 : ∀ q η : ℝ,
      (D.level n).V (NearInst.chartTau (D.level n).ε⁻¹ (s, (q, η)))
        (NearInst.chartY (D.level n).ε⁻¹ (s, (q, η))) 1 = 0 := by
    intro q η
    set pt : ℝ × (ℝ × ℝ) := (s, (q, η))
    set p := (D.level n).params D.Pl
    have hpR : p.R = (D.level n).ε⁻¹ := rfl
    have hax : NearInst.chartY p.R pt ∉ axis :=
      IIIa.chartPoint_not_mem_axis p.R_pos hs
    have hraw1 : ((D.level n).params D.Pl).raw (NearInst.chartTau p.R pt) (NearInst.chartY p.R pt) 1 = 0 := by
      rw [p.raw_eq_off_axis _ _ hax]
      exact Nv_chartPoint_apply_one p.R_pos _ hs
    have hinl1 : ∀ i : Fin 2,
        ((D.level n).params D.Pl).inlet i (NearInst.chartTau p.R pt) (NearInst.chartY p.R pt) 1 = 0 :=
      fun i => Nv_chartPoint_apply_one p.R_pos (p.inletProfile i) hs
    change D.V n (NearInst.chartTau p.R pt) (NearInst.chartY p.R pt) 1 = 0
    rw [hVz]
    simp [Fin.sum_univ_two, hraw1, hinl1 0, hinl1 1]
  refine (vEtaSup_le_etaL2QSup hmZ hV1).trans ?_
  refine (hv.2.2.2 s hs).trans (ENNReal.ofReal_le_ofReal ?_)
  have h1s : 0 < 1 + s := by linarith
  have h1 : (1 + s) ^ (-3 / 4 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have h2 : (1 + s) ^ (-1 / 4 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have h3 : (D.level n).ε * (1 + s) ^ (-1 / 4 : ℝ) ≤ 1 :=
    mul_le_one₀ e2.2 (Real.rpow_nonneg h1s.le _) h2
  have h4 : 0 ≤ (D.level n).ν⁻¹ ^ k := by positivity
  have h5 : 0 ≤ (1 + s) ^ (-3 / 4 : ℝ) + (D.level n).ε * (1 + s) ^ (-1 / 4 : ℝ) :=
    add_nonneg (Real.rpow_nonneg h1s.le _) (mul_nonneg hε.le (Real.rpow_nonneg h1s.le _))
  calc C * (D.level n).ν⁻¹ ^ k * ((1 + s) ^ (-3 / 4 : ℝ) + (D.level n).ε * (1 + s) ^ (-1 / 4 : ℝ))
      ≤ |C| * (D.level n).ν⁻¹ ^ k * 2 := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self C) h4) (by linarith)
          h5 (by positivity)
    _ ≤ 2 * (|C| + 1) * (D.level n).ν⁻¹ ^ k := by nlinarith [abs_nonneg C]

/-! ## 3. Leaf `Prop`s for the missing background bounds and assembly of `RepVBg` -/

/-- **Missing background fact 1 (at one level):** the `Y_2` bound of the thin-coefficient density
`vCoefDens (L.V τ) = |V|² + Σ_j|∂_jV| + Σ_{j,l}|∂_j∂_lV|` (source lines 5234-5235:
`R⁻¹(‖DV‖_{Y_2} + ‖D²V‖_{Y_2} + ‖V⊗V‖_{Y_2}) ≤ P_ν`, with 5131-5139 and 2607-2612). -/
def RepVCoefY2At (L : ReturnLevel) (C : ℝ) (k : ℕ) : Prop :=
  ENNReal.ofReal L.ε * eLpNorm (ringRead L.ε⁻¹ fun τ => vCoefDens (L.V τ)) 2
    (ringPhysμ L.ε⁻¹ (cOf L.ν)) ≤ ENNReal.ofReal (C * L.ν⁻¹ ^ k)

/-- **Missing background fact 1 (along the sequence):** `RepVCoefY2At` eventually in `n`
(source lines 5234-5235, 5131-5139, 2607-2612). -/
def RepVCoefY2 (D : SeqData) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, RepVCoefY2At (D.level n) C k

/-- **Missing background fact 2 (at one level):** existence properties of the canonical background
pressure `p_V` (`∇p_V = -(I-ℙ)(V·∇V)`, source lines 5245-5247 and 5255-5258):
- `p_V` is jointly `C¹`,
- `R⁻¹‖∇p_V‖_{Y_2} ≤ C ν^{-k}` in chart form (source 5245-5247: `‖∇p_V‖_2 ≤ C‖V‖_∞‖DV‖_2`),
- `‖∇p - ∇p_V‖_{Y_{11/4}} ≤ C ν^{-k} ρ` in chart form (source 5255-5258:
  `∇(p-p_V) = -(I-ℙ)(V·∇r_b + r_b·∇V + r_b·∇r_b)`). -/
def RepVPresAt (K : ReturnConsts) (L : ReturnLevel) (pV : ℝ → Space → ℝ) (C : ℝ) (k : ℕ) : Prop :=
  ContDiff ℝ 1 (fun x : ℝ × Space => pV x.1 x.2) ∧
  ENNReal.ofReal L.ε * eLpNorm (ringRead L.ε⁻¹ fun τ y => ‖physGrad (pV τ) y‖) 2
    (ringPhysμ L.ε⁻¹ (cOf L.ν)) ≤ ENNReal.ofReal (C * L.ν⁻¹ ^ k) ∧
  eLpNorm (ringRead L.ε⁻¹ fun τ => presChgDens (L.pres τ) (pV τ)) (11 / 4)
    (ringPhysμ L.ε⁻¹ (cOf L.ν)) ≤ ENNReal.ofReal (C * L.ν⁻¹ ^ k * rhoRep K L)

/-- **Missing background fact 2 (along the sequence):** `RepVPresAt` eventually in `n`
(source lines 5245-5247, 5255-5258, 2641-2642). -/
def RepVPres (D : SeqData) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∃ pV : ℝ → Space → ℝ,
    RepVPresAt D.K (D.level n) pV C k

/-- Sufficient `Y_2` bound on the exact background pressure gradient `∇p` along the sequence
(source lines 2607-2612, 2641-2642, 5245-5260): taking `pV = (D.level n).pres` in `RepVPresAt`
makes `presChgDens` vanish identically, reducing `RepVPres D` to `RepPresGradY2 D`. -/
def RepPresGradY2 (D : SeqData) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop,
    ENNReal.ofReal (D.level n).ε *
      eLpNorm (ringRead (D.level n).ε⁻¹ fun τ y => ‖physGrad ((D.level n).pres τ) y‖) 2
        (ringPhysμ (D.level n).ε⁻¹ (cOf (D.level n).ν)) ≤
      ENNReal.ofReal (C * (D.level n).ν⁻¹ ^ k)

/-- Reduction of `RepVPres D` to `RepPresGradY2 D` by choosing `pV = (D.level n).pres`. -/
theorem repVPres_of_presGradY2 (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (h : RepPresGradY2 D) : RepVPres D := by
  obtain ⟨C, k, hev⟩ := h
  refine ⟨max C 0, k, ?_⟩
  filter_upwards [hst.actual, hev] with n hn hg
  refine ⟨(D.level n).pres, hn.profile.smoothP.of_le (by norm_num), ?_, ?_⟩
  · refine hg.trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left C 0)
      (pow_nonneg (inv_nonneg.2 (D.level n).ν_pos.le) k)
  · have hzero : (ringRead (D.level n).ε⁻¹ fun τ =>
        presChgDens ((D.level n).pres τ) ((D.level n).pres τ)) = 0 := by
      funext p
      simp [ringRead, presChgDens]
    rw [hzero, eLpNorm_zero]
    exact zero_le

/-- **Instantiation of the background hypothesis (H) (`RepVBg`)** from the standing repair
hypotheses and the two missing background facts `RepVCoefY2` and `RepVPres`
(source 5131-5139, 2703-2723, 5225-5235, 5245-5247, 5255-5258, 2607-2612, 2641-2642). -/
theorem repVBg_of (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (hCoef : RepVCoefY2 D) (hPres : RepVPres D) : RepVBg D := by
  obtain ⟨C₁, k₁, hC₁, heta⟩ := repVBg_vEtaSup D hst
  obtain ⟨C₂, k₂, hcoef⟩ := hCoef
  obtain ⟨C₃, k₃, hpres⟩ := hPres
  set C : ℝ := C₁ + |C₂| + |C₃| with hCdef
  set k : ℕ := max k₁ (max k₂ k₃) with hkdef
  have hC0 : 0 ≤ C := by positivity
  have hC1 : C₁ ≤ C := by rw [hCdef]; linarith [abs_nonneg C₂, abs_nonneg C₃]
  have hC2 : C₂ ≤ C := (le_abs_self C₂).trans (by rw [hCdef]; linarith [abs_nonneg C₃])
  have hC3 : C₃ ≤ C := (le_abs_self C₃).trans (by rw [hCdef]; linarith [abs_nonneg C₂])
  have hk1 : k₁ ≤ k := le_max_left _ _
  have hk2 : k₂ ≤ k := (le_max_left k₂ k₃).trans (le_max_right _ _)
  have hk3 : k₃ ≤ k := (le_max_right k₂ k₃).trans (le_max_right _ _)
  have hle := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  refine ⟨C, k, ?_⟩
  filter_upwards [hst.actual, hle, repVBg_contDiffOn D hst, heta,
    repVBg_vCoefDens_meas D hst, hcoef, hpres] with n hn hν hV2 het hvm hc ⟨pV, hp1, hp2, hp3⟩
  have hν0 : 0 < (D.level n).ν := (D.level n).ν_pos
  have hν1 : (D.level n).ν ≤ 1 := hν.1
  have hP1 : ContDiff ℝ 1 (fun x : ℝ × Space => (D.level n).pres x.1 x.2) :=
    hn.profile.smoothP.of_le (by norm_num)
  refine ⟨pV, hV2, hp1, ?_, hvm, ?_, ?_, repVBg_presChgDens_meas_of_contDiff (D.level n) hP1 hp1, ?_⟩
  · intro s hs
    refine (het s hs).trans (ENNReal.ofReal_le_ofReal ?_)
    simpa using pnu_le_pnu hν0 hν1 zero_le_one hC1 hC0 hk1
  · refine hc.trans (ENNReal.ofReal_le_ofReal ?_)
    simpa using pnu_le_pnu hν0 hν1 zero_le_one hC2 hC0 hk2
  · refine hp2.trans (ENNReal.ofReal_le_ofReal ?_)
    simpa using pnu_le_pnu hν0 hν1 zero_le_one hC3 hC0 hk3
  · refine hp3.trans (ENNReal.ofReal_le_ofReal ?_)
    exact pnu_le_pnu hν0 hν1 (rhoRep_nonneg D.K (D.level n)) hC3 hC0 hk3

end UnforcedLeray.Short.PartIIIb.Concrete

end
