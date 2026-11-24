import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F7
import UnforcedLeray.Short.PartIIb.Tasks.BodySource.FlatGraphD2Slice
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradBound
import UnforcedLeray.Short.PartIIb.Tasks.EarlyBound.LinearBodySource
import UnforcedLeray.Short.PartIIb.Tasks.GlobalEnergy.Continuation.BodySourceGlue
import UnforcedLeray.Short.PartIIb.Tasks.GlobalEnergy.Continuation.LinearGlue
import UnforcedLeray.Short.PartI.Sub.PartI_T25_1
import UnforcedLeray.Short.PartI.Tasks.OverlapHighNorm
import UnforcedLeray.Short.PartI.Tasks.OverlapFluctuationDecay
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanPrimitive
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanDecay
import UnforcedLeray.Short.PartI.Tasks.TrainOverlapProof
import UnforcedLeray.Short.PartI.Tasks.TrainStrainIntegralProof
import UnforcedLeray.Units.B0278
import UnforcedLeray.Short.PartIIb.Tasks.GlobalEnergy.Continuation.TailExistence
import UnforcedLeray.Short.PartIIb.Tasks.GlobalEnergy.Continuation.HorizonGluing
import UnforcedLeray.Short.PartIIb.Tasks.GlobalEnergy.Continuation.TailH1Gronwall

/-!
# Part II-b, task `PartII-b:F7/2`: `GlobalEnergyContinuation` (`short-bg:global-energy`, SP 2054–2057, 2289–2295)

Source of record: `the November 2 reference manuscript`
(SP), lines 2054–2057 (`short-bg:train-late`) and 2289–2295 (`short-bg:global-energy` at line 2294).

Given `hEB : EarlyBound`, `hBS : BodySourceBound`, and `hTS : TailSource`, this file (together with
`Continuation/BodySourceGlue.lean` and `Continuation/LinearGlue.lean`) proves:
1. `trainOverlap_uncond` and `trainStrainIntegral_uncond`: unconditional assembly of Part I
   `TrainOverlap` and `TrainStrainIntegral` (`PartI:T12..T16, T18`);
2. `late_train_strain_integral_bound`: the late-train integrable tail bound (`short-bg:train-late`,
   SP 2054–2057) in `BgRegime` at `c = ν⁻²` and `H = Σ / ν`:
   `∫_{p.H}^∞ (‖Dv(s)‖_∞ + ‖D²v(s)‖_∞) ds ≤ C_strain / (p.ν * (1 + Sig)) + C_strain * p.ν ^ 3`
   with `C_strain > 0` independent of `Sig`, `dm`, `dp`, `p`;
3. `ContBodySourceAux.global_linear_bodySource_upgrade`: canonical `ℝ`-linear strongly measurable
   `QPeriodic` body-source maps `(gOf, gqOf, gηOf)` simultaneously obeying `EarlyBound` (`sLpNorm (13/8) p.H`
   and `L¹(0, p.H; H¹)`) and `TailSource` (`L¹((p.H, ∞); H¹)` and `tailLpNorm (-9/8) (max 1 (p.H - 1))`)
   via cylinder Biot–Savart slice uniqueness (resolving the constant-mode `(1, 0)` non-uniqueness);
4. `ContLinearGlueAux.linear_meridional_continuation`: unconditional Hamel-basis `ℝ`-linearization,
   horizon `Ioc 0 p.H` left-continuity transfer (resolving single-slice `p.H` degeneracy), and
   `L²(cell)` entrance curl transfer reducing all `F`-dependence to three `F`-free single-profile PDE
   leaves `MeridionalTailExistence`, `MeridionalHorizonGluing`, and `MeridionalTailH1Gronwall`;
5. `exp_early_mul_late_eq`, `global_sliceH1Norm_add_alpha_le_scaled`, and
   `globalEnergyContinuation_of_leaves`: zero-`sorry` assembly of `GlobalEnergyContinuation` from
   those three PDE leaves.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace

namespace GlobalContHelp

/-! ## 1. Unconditional Part I train overlap and late strain integral (`short-bg:train-late`, SP 2054–2057) -/

/-- Unconditional proof of `PartI.TrainOverlap` (`PartI:T16`) from `PartI:T12..T15`. -/
theorem trainOverlap_uncond : UnforcedLeray.Short.PartI.TrainOverlap := by
  have hHN := UnforcedLeray.Short.PartI.overlap_highnorm_uniform
  have hFD := UnforcedLeray.Short.PartI.overlap_fluctuation_decay hHN
  have hMP := UnforcedLeray.Short.PartI.overlap_mean_primitive
  have hMD := UnforcedLeray.Short.PartI.overlap_mean_decay hHN hFD hMP
  exact UnforcedLeray.Short.PartI.trainOverlap_proof hFD hMD

/-- Unconditional proof of `PartI.TrainStrainIntegral` (`PartI:T18`, SP 318–319, 425–436). -/
theorem trainStrainIntegral_uncond : UnforcedLeray.Short.PartI.TrainStrainIntegral :=
  UnforcedLeray.Short.PartI.trainStrainIntegral_proof trainOverlap_uncond

/-- At `c = (ν²)⁻¹` (`ν > 0`), `Ck / (ν * c ^ 2) = Ck * ν ^ 3`. -/
theorem div_nu_c_sq_eq_nu_cube {Ck ν c : ℝ} (hν : 0 < ν) (hc : c = (ν ^ 2)⁻¹) :
    Ck / (ν * c ^ 2) = Ck * ν ^ 3 := by
  rw [hc]
  have hν_ne : ν ≠ 0 := hν.ne'
  field_simp

/-- **Late-train integrable tail bound (`short-bg:train-late`, SP 2054–2057)**:
there exists a universal constant `C_strain > 0` (independent of `Sig`, `dm`, `dp`, `p`) such that for
every `Sig > 0`, there is `ν_strain > 0` such that for all `p, d` with `BgRegime p d dm dp`,
`p.ν ≤ ν_strain`, and `p.ageCut = Sig`:
* `1 ≤ p.H`,
* `1 + Sig ≤ p.c ^ 2`, and
* `∫⁻ s in Ioi p.H, (B0277.supNormD 1 (p.train.v s) + B0277.supNormD 2 (p.train.v s)) ≤
    ENNReal.ofReal (C_strain / (p.ν * (1 + Sig)) + C_strain * p.ν ^ 3)`. -/
theorem late_train_strain_integral_bound :
    ∃ C_strain : ℝ, 0 < C_strain ∧
      ∀ Sig : ℝ, 0 < Sig →
        ∃ ν_strain : ℝ, 0 < ν_strain ∧ ν_strain ≤ 1 ∧
          ∀ {dm dp : ℝ} (p : Params) (d : ℝ),
            BgRegime p d dm dp → p.ν ≤ ν_strain → p.ageCut = Sig →
            1 ≤ p.H ∧
            1 + Sig ≤ p.c ^ 2 ∧
            ∫⁻ s in Ioi p.H,
                (B0277.supNormD 1 (p.train.v s) + B0277.supNormD 2 (p.train.v s)) ≤
              ENNReal.ofReal (C_strain / (p.ν * (1 + Sig)) + C_strain * p.ν ^ 3) := by
  have hρ : (1 / 2 : ℝ) < 2 := by norm_num
  obtain ⟨C₁, ν₀, hC₁, hν₀, hStrain⟩ := trainStrainIntegral_uncond 2 hρ 1
  refine ⟨C₁, hC₁, fun Sig hSig => ?_⟩
  obtain ⟨ν₁, hν₁, hν₁_le1, hsmall⟩ :=
    B0278.one_add_le_sq_of_small (ρ := 2) (by norm_num) hSig.le
  set ν_strain : ℝ := min (min ν₀ ν₁) Sig
  have hν_strain_pos : 0 < ν_strain := lt_min (lt_min hν₀ hν₁) hSig
  have hν_strain_le1 : ν_strain ≤ 1 :=
    ((min_le_left _ _).trans (min_le_right _ _)).trans hν₁_le1
  refine ⟨ν_strain, hν_strain_pos, hν_strain_le1, fun p d hreg hν_le hAge => ?_⟩
  have hνp : 0 < p.ν := p.ν_pos
  have hν_le0 : p.ν ≤ ν₀ :=
    hν_le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν_le1 : p.ν ≤ ν₁ :=
    hν_le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν_leSig : p.ν ≤ Sig := hν_le.trans (min_le_right _ _)
  have hH_eq : p.H = Sig / p.ν := by rw [Params.H, hAge]
  have hH1 : 1 ≤ p.H := by
    rw [hH_eq, one_le_div hνp]
    exact hν_leSig
  have hc_eq : p.c = (p.ν ^ 2)⁻¹ := hreg.c_eq
  have hc2_per : UnforcedLeray.Short.PartI.trainPeriod 2 p.ν = (p.ν ^ 2)⁻¹ :=
    vb_trainPeriod_two hνp
  have hc_rpow : (p.ν ^ (-2 : ℝ)) = (p.ν ^ 2)⁻¹ := hc2_per
  have h1Sig_per : 1 + Sig ≤ (UnforcedLeray.Short.PartI.trainPeriod 2 p.ν) ^ 2 :=
    hsmall p.ν hνp hν_le1
  have h1Sig_c2 : 1 + Sig ≤ p.c ^ 2 := by
    rwa [hc_eq, ← hc2_per]
  obtain ⟨tr', hbuc, hv_eq⟩ :=
    vb_transport (hc_eq.trans hc2_per.symm) p.train hreg.train_buc
  have hEst := hStrain p.ν hνp hν_le0 tr' hbuc Sig hSig.le h1Sig_per
  unfold B0278.TrainStrainEstimate at hEst
  rw [← hH_eq, hv_eq] at hEst
  have hsum : (fun s => ∑ j ∈ Finset.Icc 1 (1 + 1), B0277.supNormD j (p.train.v s)) =
      fun s => B0277.supNormD 1 (p.train.v s) + B0277.supNormD 2 (p.train.v s) := by
    funext s
    exact B0278.sum_Icc_one_two (fun j => B0277.supNormD j (p.train.v s))
  rw [hsum, div_nu_c_sq_eq_nu_cube hνp hc2_per] at hEst
  exact ⟨hH1, h1Sig_c2, hEst⟩

/-! ## 2. Matching `EarlyBound` flat responses with `FlatGraphD2Slice` and `TailSource` -/

/-- Any `HasWeakVec v d b g` transfers along a.e. equality of the base profile `b = b'` on `0 < x.1`. -/
lemma hasWeakVec_congr_base {v : Coord → Fin 3 → ℝ} {d : Coord → ℝ} {b b' g : CProf}
    (hbb' : ∀ᵐ x : Coord, 0 < x.1 → b x = b' x)
    (hw : HasWeakVec v d b g) :
    HasWeakVec v d b' g := by
  intro i
  refine CongrHelp.hasWeakFO_congr (u := fun x => b' x i) (u' := fun x => b x i) ?_ (hw i)
  filter_upwards [hbb'] with x hx hpos
  rw [hx hpos]

/-- Any `HasWeakVec v d b g` transfers along a.e. equality of the derivative `g = g'` on `0 < x.1`. -/
lemma hasWeakVec_congr_deriv {v : Coord → Fin 3 → ℝ} {d : Coord → ℝ} {b g g' : CProf}
    (hgg' : ∀ᵐ x : Coord, 0 < x.1 → g x = g' x)
    (hw : HasWeakVec v d b g) :
    HasWeakVec v d b g' := by
  intro i
  obtain ⟨h1, h2⟩ := hw i
  have hEq : ∀ φ : Coord → ℝ, IsCoordTest φ →
      (fun x => g x i * (φ x : ℂ)) =ᵐ[volume] (fun x => g' x i * (φ x : ℂ)) := by
    intro φ hφ
    filter_upwards [hgg'] with x hx
    by_cases hpos : 0 < x.1
    · rw [hx hpos]
    · rw [F10K0Help.isCoordTest_zero_of_nonpos hφ hpos]
      simp
  refine ⟨fun φ hφ => ⟨(h1 φ hφ).1, (h1 φ hφ).2.congr (hEq φ hφ)⟩, fun φ hφ => ?_⟩
  rw [← integral_congr_ae (hEq φ hφ)]
  exact h2 φ hφ

/-- Given `hTS : TailSource` and `flatGraphD2Slice_proof`, for any `BgRegime p d dm dp` with
`p.ν ≤ min ν_G ν_ts` and `1 ≤ p.H`, and any `F : HpR p.c` and `b0, b0q, b0η : CProf` satisfying
`InFlatClass p.c bgp b0`, `IsFlatResponse p.ν 0 (toProf p.c F) b0`, `HasWeakVec vQ0 dZero b0 b0q`,
`HasWeakVec vEta dZero b0 b0η`, there exist `g_ts, gq_ts, gη_ts : CProf` solving
`IsBodySource p.train b0 b0q b0η g_ts` with:
* `(∫⁻ s in Ioi p.H, sliceH1Norm p.c g_ts gq_ts gη_ts s) ≤ ENNReal.ofReal (C_ts * (p.ν ^ k_ts)⁻¹ * ‖F‖)`,
* `tailLpNorm (-9 / 8) (max 1 (p.H - 1)) (sliceH1Norm p.c g_ts gq_ts gη_ts) ≤
    ENNReal.ofReal (C_ts * (p.ν ^ k_ts)⁻¹ * ‖F‖)`. -/
theorem tailSource_for_early_b0
    (hTS : TailSource)
    {dm dp : ℝ} (hdm : 0 < dm) :
    ∃ (C_ts : ℝ) (k_ts : ℕ) (ν_ts : ℝ), 0 < C_ts ∧ 0 < ν_ts ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν_ts → 1 ≤ p.H →
      ∀ (F : HpR p.c) (b0 b0q b0η : CProf),
        InFlatClass p.c bgp b0 →
        IsFlatResponse p.ν 0 (toProf p.c F) b0 →
        HasWeakVec vQ0 dZero b0 b0q →
        HasWeakVec vEta dZero b0 b0η →
        ∃ g_ts gq_ts gη_ts : CProf,
          QPeriodic p.c g_ts ∧
          HasWeakVec vQ0 dZero g_ts gq_ts ∧
          HasWeakVec vEta dZero g_ts gη_ts ∧
          IsBodySource p.train b0 b0q b0η g_ts ∧
          Measurable (sliceH1Norm p.c g_ts gq_ts gη_ts) ∧
          (∫⁻ s in Ioi p.H, sliceH1Norm p.c g_ts gq_ts gη_ts s) ≤
            ENNReal.ofReal (C_ts * (p.ν ^ k_ts)⁻¹ * ‖F‖) ∧
          tailLpNorm (-9 / 8) (max 1 (p.H - 1)) (sliceH1Norm p.c g_ts gq_ts gη_ts) ≤
            ENNReal.ofReal (C_ts * (p.ν ^ k_ts)⁻¹ * ‖F‖) := by
  obtain ⟨C_G, hC_G, hFG⟩ := flatGraphD2Slice_proof
  obtain ⟨C_ts, k_ts, ν_t, hC_ts, hν_t, hTS_p⟩ := hTS dm dp hdm
  refine ⟨C_ts, k_ts, ν_t, hC_ts, hν_t, ?_⟩
  intro p d hreg hν_t_le hH1 F b0 b0q b0η hb0_cls hb0_resp hb0q hb0η
  have hν_pos : 0 < p.ν := p.ν_pos
  have hc_pos : 0 < p.c := p.c_pos
  have hH_pos : 0 < p.H := zero_lt_one.trans_le hH1
  have hF_inHr : InHr p.c bgp (toProf p.c F) :=
    ⟨toProf_periodic hc_pos F, toProf_aestronglyMeasurable hc_pos F, by
      rw [hNorm_toProf hc_pos F]; exact enorm_lt_top⟩
  have hF_norm : hNorm p.c bgp (toProf p.c F) = ENNReal.ofReal ‖F‖ := by
    rw [hNorm_toProf hc_pos F, ofReal_norm]
  obtain ⟨b0', b0q₀, b0η₀, D2, hb0'_ae, hb0'_hr, hbq₀_hr, hbη₀_hr, hD2_hr,
      hsm_b0', hsm_bq₀, hsm_bη₀, hsm_D2, hw_q₀, hw_η₀, hw_00, hw_01, hw_10, hw_11, _⟩ :=
    hFG p.ν p.c p.H hν_pos hc_pos hH_pos (toProf p.c F) b0 hF_inHr hb0_cls hb0_resp
  obtain ⟨g_ts, gq_ts, gη_ts, hg_per, hg_wq, hg_wη, hg_src₀, hg_meas, _hg_sl, hg_T⟩ :=
    hTS_p p d hreg hν_t_le (toProf p.c F) b0 b0' b0q₀ b0η₀ D2
      hF_inHr hb0_cls hb0_resp hb0'_ae hb0'_hr hbq₀_hr hbη₀_hr hD2_hr
      hsm_b0' hsm_bq₀ hsm_bη₀ hsm_D2 hw_q₀ hw_η₀ hw_00 hw_01 hw_10 hw_11
  have hq_ae : ∀ᵐ x : Coord, 0 < x.1 → b0q₀ x = b0q x :=
    GradBoundHelp.hasWeakVec_unique hw_q₀ hb0q
  have hη_ae : ∀ᵐ x : Coord, 0 < x.1 → b0η₀ x = b0η x :=
    GradBoundHelp.hasWeakVec_unique hw_η₀ hb0η
  have hg_src : IsBodySource p.train b0 b0q b0η g_ts :=
    LinearBodySourceHelp.isBodySource_congr_deriv hq_ae hη_ae hg_src₀
  have hC_nn : 0 ≤ C_ts * (p.ν ^ k_ts)⁻¹ := by positivity
  have hL1_bd : (∫⁻ s in Ioi p.H, sliceH1Norm p.c g_ts gq_ts gη_ts s) ≤
      ENNReal.ofReal (C_ts * (p.ν ^ k_ts)⁻¹ * ‖F‖) := by
    have hTH := hg_T p.H hH1
    rw [hF_norm, ← ENNReal.ofReal_mul hC_nn] at hTH
    exact le_self_add.trans hTH
  have hLp_bd : tailLpNorm (-9 / 8) (max 1 (p.H - 1)) (sliceH1Norm p.c g_ts gq_ts gη_ts) ≤
      ENNReal.ofReal (C_ts * (p.ν ^ k_ts)⁻¹ * ‖F‖) := by
    have hTm := hg_T (max 1 (p.H - 1)) (le_max_left 1 (p.H - 1))
    rw [hF_norm, ← ENNReal.ofReal_mul hC_nn] at hTm
    exact le_add_self.trans hTm
  exact ⟨g_ts, gq_ts, gη_ts, hg_per, hg_wq, hg_wη, hg_src, hg_meas, hL1_bd, hLp_bd⟩

/-! ## 3. Restriction of `IsGlobalMeridionalCorrection` and Gronwall exponential algebra -/

/-- Any global meridional correction on `(0, ∞)` restricts to `IsMeridionalCorrectionOn p T` on
every finite horizon `(0, T)`. -/
theorem isMeridionalCorrectionOn_of_global {p : Params} {g z zq zη : CProf} {α : E2} (T : ℝ)
    (h : IsGlobalMeridionalCorrection p g z zq zη α) :
    IsMeridionalCorrectionOn p T g z zq zη α :=
  ⟨h.periodic, h.weak_q, h.weak_eta,
    fun φ hφ _ => h.solenoidal φ hφ,
    fun Ψ hΨ _ => h.equation Ψ hΨ,
    h.initial_curl⟩

/-- Exact identity combining the early exponential `exp(a' * p.H)` (`p.H = Sig / p.ν`) with the
late Gronwall amplification factor `exp(C_late / (p.ν * (1 + Sig)) + C_late * p.ν ^ 3)`. -/
theorem exp_early_mul_late_eq {a' Sig C_late : ℝ} (p : Params) (hAge : p.ageCut = Sig) :
    Real.exp (a' * p.H) *
        Real.exp (C_late / (p.ν * (1 + Sig)) + C_late * p.ν ^ 3) =
      Real.exp ((a' * Sig + C_late / (1 + Sig)) / p.ν + C_late * p.ν ^ 3) := by
  have hH : p.H = Sig / p.ν := by rw [Params.H, hAge]
  rw [hH, ← Real.exp_add]
  congr 1
  have hν_ne : p.ν ≠ 0 := p.ν_pos.ne'
  field_simp
  ring

/-- The late amplification factor `exp(C_late / (p.ν * (1 + Sig)) + C_late * p.ν ^ 3)` is `≥ 1`. -/
theorem one_le_exp_late {Sig C_late : ℝ} (p : Params) (hSig : 0 < Sig) (hC_late : 0 < C_late) :
    1 ≤ Real.exp (C_late / (p.ν * (1 + Sig)) + C_late * p.ν ^ 3) := by
  rw [Real.one_le_exp_iff]
  have hν : 0 < p.ν := p.ν_pos
  positivity

/-- The early exponential `exp(a' * p.H)` is at most `M_exp`. -/
theorem exp_early_le_M_exp {a' Sig C_late : ℝ} (p : Params)
    (hSig : 0 < Sig) (hC_late : 0 < C_late) (hAge : p.ageCut = Sig) :
    Real.exp (a' * p.H) ≤
      Real.exp ((a' * Sig + C_late / (1 + Sig)) / p.ν + C_late * p.ν ^ 3) := by
  rw [← exp_early_mul_late_eq p hAge]
  exact le_mul_of_one_le_right (Real.exp_pos _).le (one_le_exp_late p hSig hC_late)

/-- `M_exp ≥ 1` for `a' > 0`, `Sig > 0`, `C_late > 0`. -/
theorem one_le_M_exp {a' Sig C_late : ℝ} (p : Params)
    (ha' : 0 < a') (hSig : 0 < Sig) (hC_late : 0 < C_late) :
    1 ≤ Real.exp ((a' * Sig + C_late / (1 + Sig)) / p.ν + C_late * p.ν ^ 3) := by
  rw [Real.one_le_exp_iff]
  have hν : 0 < p.ν := p.ν_pos
  positivity

/-- **Combined `(0, ∞)` slice `H¹` + entrance amplitude bound (`short-bg:global-energy`, SP 2289–2295)**:
given:
1. the `(0, p.H]` bound from `EarlyBound`:
   `∀ s ∈ Ioc 0 p.H, Z(s) + ‖α‖ ≤ C_eb * (p.ν ^ k_eb)⁻¹ * exp(a' * p.H) * ‖F‖`;
2. the `(p.H, ∞)` differentiated `H¹` Gronwall inequality:
   `∀ s > p.H, Z(s) + ‖α‖ ≤ exp(C_late / (p.ν * (1 + Sig)) + C_late * p.ν ^ 3) *
     ((Z(p.H) + ‖α‖) + K_src * ∫⁻ t in Ioi p.H, G(t))`;
3. the `TailSource` `L¹(Ioi p.H)` bound:
   `∫⁻ t in Ioi p.H, G(t) ≤ C_ts * (p.ν ^ k_ts)⁻¹ * ‖F‖`;
then for every `s > 0`,
`Z(s) + ‖α‖ ≤ (C_eb + K_src * C_ts) * (p.ν ^ max k_eb k_ts)⁻¹ * M_exp * ‖F‖`. -/
theorem global_sliceH1Norm_add_alpha_le
    {Sig a' C_late C_eb C_ts K_src : ℝ} {k_eb k_ts : ℕ}
    (hSig : 0 < Sig) (ha' : 0 < a') (hC_late : 0 < C_late)
    (hC_eb : 0 < C_eb) (hC_ts : 0 < C_ts) (hK_src : 0 ≤ K_src)
    (p : Params) (hν1 : p.ν ≤ 1) (hAge : p.ageCut = Sig)
    (F : HpR p.c) (α : E2) (Z G : ℝ → ℝ≥0∞)
    (h_early : ∀ s ∈ Ioc 0 p.H,
      Z s + ENNReal.ofReal ‖α‖ ≤
        ENNReal.ofReal (C_eb * (p.ν ^ k_eb)⁻¹ * Real.exp (a' * p.H) * ‖F‖))
    (h_late : ∀ s : ℝ, p.H < s →
      Z s + ENNReal.ofReal ‖α‖ ≤
        ENNReal.ofReal (Real.exp (C_late / (p.ν * (1 + Sig)) + C_late * p.ν ^ 3)) *
          ((Z p.H + ENNReal.ofReal ‖α‖) +
            ENNReal.ofReal K_src * ∫⁻ t in Ioi p.H, G t))
    (h_tail_L1 : (∫⁻ t in Ioi p.H, G t) ≤ ENNReal.ofReal (C_ts * (p.ν ^ k_ts)⁻¹ * ‖F‖))
    {s : ℝ} (hs : 0 < s) :
    let M_exp := Real.exp ((a' * Sig + C_late / (1 + Sig)) / p.ν + C_late * p.ν ^ 3)
    let k := max k_eb k_ts
    let C := C_eb + K_src * C_ts
    Z s + ENNReal.ofReal ‖α‖ ≤ ENNReal.ofReal (C * (p.ν ^ k)⁻¹ * M_exp * ‖F‖) := by
  intro M_exp k C
  have hν_pos : 0 < p.ν := p.ν_pos
  have hH_pos : 0 < p.H := by
    rw [Params.H, hAge]
    exact div_pos hSig hν_pos
  have hk_eb : (p.ν ^ k_eb)⁻¹ ≤ (p.ν ^ k)⁻¹ :=
    vb_inv_pow_mono hν_pos hν1 (le_max_left k_eb k_ts)
  have hk_ts : (p.ν ^ k_ts)⁻¹ ≤ (p.ν ^ k)⁻¹ :=
    vb_inv_pow_mono hν_pos hν1 (le_max_right k_eb k_ts)
  have hexp_early_le : Real.exp (a' * p.H) ≤ M_exp :=
    exp_early_le_M_exp p hSig hC_late hAge
  by_cases hsH : s ≤ p.H
  · have h1 := h_early s ⟨hs, hsH⟩
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    have hC_le : C_eb ≤ C := by dsimp [C]; linarith [mul_nonneg hK_src hC_ts.le]
    have hmul1 : C_eb * (p.ν ^ k_eb)⁻¹ ≤ C * (p.ν ^ k)⁻¹ :=
      mul_le_mul hC_le hk_eb (by positivity) (by dsimp [C]; positivity)
    have hmul2 : C_eb * (p.ν ^ k_eb)⁻¹ * Real.exp (a' * p.H) ≤ C * (p.ν ^ k)⁻¹ * M_exp :=
      mul_le_mul hmul1 hexp_early_le (Real.exp_pos _).le (by dsimp [C, M_exp]; positivity)
    exact mul_le_mul_of_nonneg_right hmul2 (norm_nonneg F)
  · have hsH' : p.H < s := not_le.mp hsH
    have hZH := h_early p.H ⟨hH_pos, le_rfl⟩
    have hZH' : Z p.H + ENNReal.ofReal ‖α‖ ≤
        ENNReal.ofReal (C_eb * (p.ν ^ k)⁻¹ * Real.exp (a' * p.H) * ‖F‖) := by
      refine hZH.trans (ENNReal.ofReal_le_ofReal ?_)
      gcongr
    have h1_le_early : 1 ≤ Real.exp (a' * p.H) :=
      Real.one_le_exp (mul_nonneg ha'.le hH_pos.le)
    have hG_bd : ENNReal.ofReal K_src * (∫⁻ t in Ioi p.H, G t) ≤
        ENNReal.ofReal (K_src * C_ts * (p.ν ^ k)⁻¹ * Real.exp (a' * p.H) * ‖F‖) := by
      calc ENNReal.ofReal K_src * (∫⁻ t in Ioi p.H, G t)
          ≤ ENNReal.ofReal K_src * ENNReal.ofReal (C_ts * (p.ν ^ k_ts)⁻¹ * ‖F‖) :=
            mul_le_mul_of_nonneg_left h_tail_L1 zero_le
        _ = ENNReal.ofReal (K_src * (C_ts * (p.ν ^ k_ts)⁻¹ * ‖F‖)) :=
            (ENNReal.ofReal_mul hK_src).symm
        _ ≤ ENNReal.ofReal (K_src * C_ts * (p.ν ^ k)⁻¹ * Real.exp (a' * p.H) * ‖F‖) := by
            apply ENNReal.ofReal_le_ofReal
            have h_k : K_src * C_ts * (p.ν ^ k_ts)⁻¹ ≤
                K_src * C_ts * (p.ν ^ k)⁻¹ * Real.exp (a' * p.H) := by
              calc K_src * C_ts * (p.ν ^ k_ts)⁻¹
                  ≤ K_src * C_ts * (p.ν ^ k)⁻¹ :=
                    mul_le_mul_of_nonneg_left hk_ts (mul_nonneg hK_src hC_ts.le)
                _ ≤ K_src * C_ts * (p.ν ^ k)⁻¹ * Real.exp (a' * p.H) :=
                    le_mul_of_one_le_right (by positivity) h1_le_early
            calc K_src * (C_ts * (p.ν ^ k_ts)⁻¹ * ‖F‖)
                = (K_src * C_ts * (p.ν ^ k_ts)⁻¹) * ‖F‖ := by ring
              _ ≤ (K_src * C_ts * (p.ν ^ k)⁻¹ * Real.exp (a' * p.H)) * ‖F‖ :=
                  mul_le_mul_of_nonneg_right h_k (norm_nonneg F)
    set E_late : ℝ := Real.exp (C_late / (p.ν * (1 + Sig)) + C_late * p.ν ^ 3)
    have hE_late_pos : 0 ≤ E_late := (Real.exp_pos _).le
    have h_eb_nn : 0 ≤ C_eb * (p.ν ^ k)⁻¹ * Real.exp (a' * p.H) * ‖F‖ := by positivity
    have h_ts_nn : 0 ≤ K_src * C_ts * (p.ν ^ k)⁻¹ * Real.exp (a' * p.H) * ‖F‖ := by positivity
    calc Z s + ENNReal.ofReal ‖α‖
        ≤ ENNReal.ofReal E_late *
            ((Z p.H + ENNReal.ofReal ‖α‖) + ENNReal.ofReal K_src * ∫⁻ t in Ioi p.H, G t) :=
          h_late s hsH'
      _ ≤ ENNReal.ofReal E_late *
            (ENNReal.ofReal (C_eb * (p.ν ^ k)⁻¹ * Real.exp (a' * p.H) * ‖F‖) +
              ENNReal.ofReal (K_src * C_ts * (p.ν ^ k)⁻¹ * Real.exp (a' * p.H) * ‖F‖)) :=
          mul_le_mul_of_nonneg_left (add_le_add hZH' hG_bd) zero_le
      _ = ENNReal.ofReal (E_late *
            (C_eb * (p.ν ^ k)⁻¹ * Real.exp (a' * p.H) * ‖F‖ +
              K_src * C_ts * (p.ν ^ k)⁻¹ * Real.exp (a' * p.H) * ‖F‖)) := by
          rw [← ENNReal.ofReal_add h_eb_nn h_ts_nn, ← ENNReal.ofReal_mul hE_late_pos]
      _ = ENNReal.ofReal (C * (p.ν ^ k)⁻¹ * M_exp * ‖F‖) := by
          congr 1
          have h_exp_prod : Real.exp (a' * p.H) * E_late = M_exp :=
            exp_early_mul_late_eq p hAge
          calc E_late *
                (C_eb * (p.ν ^ k)⁻¹ * Real.exp (a' * p.H) * ‖F‖ +
                  K_src * C_ts * (p.ν ^ k)⁻¹ * Real.exp (a' * p.H) * ‖F‖)
              = C * (p.ν ^ k)⁻¹ * (Real.exp (a' * p.H) * E_late) * ‖F‖ := by
                dsimp [C]; ring
            _ = C * (p.ν ^ k)⁻¹ * M_exp * ‖F‖ := by rw [h_exp_prod]

/-- Generalized `(0, ∞)` slice `H¹` + entrance amplitude bound allowing a universal norm-equivalence
factor `A_H1 ≥ 1` (`sliceH1Norm` vs Hilbertian `H¹` norm in `MeridionalTailH1Gronwall`). -/
theorem global_sliceH1Norm_add_alpha_le_scaled
    {Sig a' A_H1 C_late C_eb C_ts K_src : ℝ} {k_eb k_ts : ℕ}
    (hSig : 0 < Sig) (ha' : 0 < a') (hA_H1 : 1 ≤ A_H1) (hC_late : 0 < C_late)
    (hC_eb : 0 < C_eb) (hC_ts : 0 < C_ts) (hK_src : 0 ≤ K_src)
    (p : Params) (hν1 : p.ν ≤ 1) (hAge : p.ageCut = Sig)
    (F : HpR p.c) (α : E2) (Z G : ℝ → ℝ≥0∞)
    (h_early : ∀ s ∈ Ioc 0 p.H,
      Z s + ENNReal.ofReal ‖α‖ ≤
        ENNReal.ofReal (C_eb * (p.ν ^ k_eb)⁻¹ * Real.exp (a' * p.H) * ‖F‖))
    (h_late : ∀ s : ℝ, p.H < s →
      Z s ≤
        ENNReal.ofReal (A_H1 * Real.exp (C_late / (p.ν * (1 + Sig)) + C_late * p.ν ^ 3)) *
          (Z p.H + ENNReal.ofReal K_src * ∫⁻ t in Ioi p.H, G t))
    (h_tail_L1 : (∫⁻ t in Ioi p.H, G t) ≤ ENNReal.ofReal (C_ts * (p.ν ^ k_ts)⁻¹ * ‖F‖))
    {s : ℝ} (hs : 0 < s) :
    let M_exp := Real.exp ((a' * Sig + C_late / (1 + Sig)) / p.ν + C_late * p.ν ^ 3)
    let k := max k_eb k_ts
    let C := A_H1 * C_eb + A_H1 * K_src * C_ts
    Z s + ENNReal.ofReal ‖α‖ ≤ ENNReal.ofReal (C * (p.ν ^ k)⁻¹ * M_exp * ‖F‖) := by
  intro M_exp k C
  have hν_pos : 0 < p.ν := p.ν_pos
  have hA_pos : 0 < A_H1 := zero_lt_one.trans_le hA_H1
  have hH_pos : 0 < p.H := by
    rw [Params.H, hAge]
    exact div_pos hSig hν_pos
  have hk_eb : (p.ν ^ k_eb)⁻¹ ≤ (p.ν ^ k)⁻¹ :=
    vb_inv_pow_mono hν_pos hν1 (le_max_left k_eb k_ts)
  have hk_ts : (p.ν ^ k_ts)⁻¹ ≤ (p.ν ^ k)⁻¹ :=
    vb_inv_pow_mono hν_pos hν1 (le_max_right k_eb k_ts)
  have hexp_early_le : Real.exp (a' * p.H) ≤ M_exp :=
    exp_early_le_M_exp p hSig hC_late hAge
  by_cases hsH : s ≤ p.H
  · have h1 := h_early s ⟨hs, hsH⟩
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    have hC_le : C_eb ≤ C := by
      dsimp [C]
      nlinarith [hA_H1, hC_eb.le, mul_nonneg (mul_nonneg hA_pos.le hK_src) hC_ts.le]
    have hmul1 : C_eb * (p.ν ^ k_eb)⁻¹ ≤ C * (p.ν ^ k)⁻¹ :=
      mul_le_mul hC_le hk_eb (by positivity) (by dsimp [C]; positivity)
    have hmul2 : C_eb * (p.ν ^ k_eb)⁻¹ * Real.exp (a' * p.H) ≤ C * (p.ν ^ k)⁻¹ * M_exp :=
      mul_le_mul hmul1 hexp_early_le (Real.exp_pos _).le (by dsimp [C, M_exp]; positivity)
    exact mul_le_mul_of_nonneg_right hmul2 (norm_nonneg F)
  · have hsH' : p.H < s := not_le.mp hsH
    have hZH := h_early p.H ⟨hH_pos, le_rfl⟩
    have hZH' : Z p.H + ENNReal.ofReal ‖α‖ ≤
        ENNReal.ofReal (C_eb * (p.ν ^ k)⁻¹ * Real.exp (a' * p.H) * ‖F‖) := by
      refine hZH.trans (ENNReal.ofReal_le_ofReal ?_)
      gcongr
    have h1_le_early : 1 ≤ Real.exp (a' * p.H) :=
      Real.one_le_exp (mul_nonneg ha'.le hH_pos.le)
    have hG_bd : ENNReal.ofReal K_src * (∫⁻ t in Ioi p.H, G t) ≤
        ENNReal.ofReal (K_src * C_ts * (p.ν ^ k)⁻¹ * Real.exp (a' * p.H) * ‖F‖) := by
      calc ENNReal.ofReal K_src * (∫⁻ t in Ioi p.H, G t)
          ≤ ENNReal.ofReal K_src * ENNReal.ofReal (C_ts * (p.ν ^ k_ts)⁻¹ * ‖F‖) :=
            mul_le_mul_of_nonneg_left h_tail_L1 zero_le
        _ = ENNReal.ofReal (K_src * (C_ts * (p.ν ^ k_ts)⁻¹ * ‖F‖)) :=
            (ENNReal.ofReal_mul hK_src).symm
        _ ≤ ENNReal.ofReal (K_src * C_ts * (p.ν ^ k)⁻¹ * Real.exp (a' * p.H) * ‖F‖) := by
            apply ENNReal.ofReal_le_ofReal
            have h_k : K_src * C_ts * (p.ν ^ k_ts)⁻¹ ≤
                K_src * C_ts * (p.ν ^ k)⁻¹ * Real.exp (a' * p.H) := by
              calc K_src * C_ts * (p.ν ^ k_ts)⁻¹
                  ≤ K_src * C_ts * (p.ν ^ k)⁻¹ :=
                    mul_le_mul_of_nonneg_left hk_ts (mul_nonneg hK_src hC_ts.le)
                _ ≤ K_src * C_ts * (p.ν ^ k)⁻¹ * Real.exp (a' * p.H) :=
                    le_mul_of_one_le_right (by positivity) h1_le_early
            calc K_src * (C_ts * (p.ν ^ k_ts)⁻¹ * ‖F‖)
                = (K_src * C_ts * (p.ν ^ k_ts)⁻¹) * ‖F‖ := by ring
              _ ≤ (K_src * C_ts * (p.ν ^ k)⁻¹ * Real.exp (a' * p.H)) * ‖F‖ :=
                  mul_le_mul_of_nonneg_right h_k (norm_nonneg F)
    set E_late : ℝ := Real.exp (C_late / (p.ν * (1 + Sig)) + C_late * p.ν ^ 3)
    have h1_le_AE : 1 ≤ A_H1 * E_late :=
      one_le_mul_of_one_le_of_one_le hA_H1 (one_le_exp_late p hSig hC_late)
    have hAE_nn : 0 ≤ A_H1 * E_late := zero_le_one.trans h1_le_AE
    have hα_le : ENNReal.ofReal ‖α‖ ≤ ENNReal.ofReal (A_H1 * E_late) * ENNReal.ofReal ‖α‖ := by
      calc ENNReal.ofReal ‖α‖
          = ENNReal.ofReal 1 * ENNReal.ofReal ‖α‖ := by simp
        _ ≤ ENNReal.ofReal (A_H1 * E_late) * ENNReal.ofReal ‖α‖ :=
            mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal h1_le_AE) zero_le
    have h_eb_nn : 0 ≤ C_eb * (p.ν ^ k)⁻¹ * Real.exp (a' * p.H) * ‖F‖ := by positivity
    have h_ts_nn : 0 ≤ K_src * C_ts * (p.ν ^ k)⁻¹ * Real.exp (a' * p.H) * ‖F‖ := by positivity
    calc Z s + ENNReal.ofReal ‖α‖
        ≤ ENNReal.ofReal (A_H1 * E_late) *
            (Z p.H + ENNReal.ofReal K_src * ∫⁻ t in Ioi p.H, G t) +
          ENNReal.ofReal (A_H1 * E_late) * ENNReal.ofReal ‖α‖ :=
          add_le_add (h_late s hsH') hα_le
      _ = ENNReal.ofReal (A_H1 * E_late) *
            ((Z p.H + ENNReal.ofReal ‖α‖) + ENNReal.ofReal K_src * ∫⁻ t in Ioi p.H, G t) := by
          rw [← mul_add]; ac_rfl
      _ ≤ ENNReal.ofReal (A_H1 * E_late) *
            (ENNReal.ofReal (C_eb * (p.ν ^ k)⁻¹ * Real.exp (a' * p.H) * ‖F‖) +
              ENNReal.ofReal (K_src * C_ts * (p.ν ^ k)⁻¹ * Real.exp (a' * p.H) * ‖F‖)) :=
          mul_le_mul_of_nonneg_left (add_le_add hZH' hG_bd) zero_le
      _ = ENNReal.ofReal ((A_H1 * E_late) *
            (C_eb * (p.ν ^ k)⁻¹ * Real.exp (a' * p.H) * ‖F‖ +
              K_src * C_ts * (p.ν ^ k)⁻¹ * Real.exp (a' * p.H) * ‖F‖)) := by
          rw [← ENNReal.ofReal_add h_eb_nn h_ts_nn, ← ENNReal.ofReal_mul hAE_nn]
      _ = ENNReal.ofReal (C * (p.ν ^ k)⁻¹ * M_exp * ‖F‖) := by
          congr 1
          have h_exp_prod : Real.exp (a' * p.H) * E_late = M_exp :=
            exp_early_mul_late_eq p hAge
          calc (A_H1 * E_late) *
                (C_eb * (p.ν ^ k)⁻¹ * Real.exp (a' * p.H) * ‖F‖ +
                  K_src * C_ts * (p.ν ^ k)⁻¹ * Real.exp (a' * p.H) * ‖F‖)
              = C * (p.ν ^ k)⁻¹ * (Real.exp (a' * p.H) * E_late) * ‖F‖ := by
                dsimp [C]; ring
            _ = C * (p.ν ^ k)⁻¹ * M_exp * ‖F‖ := by rw [h_exp_prod]

end GlobalContHelp

open GlobalContHelp

/-! ## 4. Conditional assembly of `GlobalEnergyContinuation` from the three `F`-free PDE leaves -/

/-- **Conditional assembly of `GlobalEnergyContinuation` (`PartII-b:F7/2`, SP 2054–2057, 2289–2295)**
from the three `F`-free single-profile PDE leaves:
1. `MeridionalTailExistence` (`(a)`: tail `C([T, ∞); H¹_σ(C_c))` existence on `(T, ∞)`),
2. `MeridionalHorizonGluing` (`(b)`: early `C((0, T]; H¹_σ(C_c))` trace extraction and weak gluing
   across `s = T`), and
3. `MeridionalTailH1Gronwall` (`(c)`: differentiated `H¹(C_c)` velocity energy Gronwall inequality
   on `(T, ∞)`),
combined with the unconditional theorems `late_train_strain_integral_bound`,
`ContBodySourceAux.global_linear_bodySource_upgrade`,
`ContLinearGlueAux.linear_meridional_continuation`, and
`global_sliceH1Norm_add_alpha_le_scaled`. -/
theorem globalEnergyContinuation_of_leaves
    (hEx : MeridionalTailExistence)
    (hGlue : MeridionalHorizonGluing)
    (hGron : MeridionalTailH1Gronwall) :
    UnforcedLeray.Short.IIb.GlobalEnergyContinuation := by
  intro hEB _hBS hTS
  obtain ⟨A_H1, K_H1, hA_H1, hK_H1, hGron_step⟩ := hGron
  obtain ⟨C_strain, hC_strain, hTrainLate⟩ := late_train_strain_integral_bound
  set C_late : ℝ := K_H1 * C_strain
  have hC_late_pos : 0 < C_late := mul_pos hK_H1 hC_strain
  have hA_pos : 0 < A_H1 := zero_lt_one.trans_le hA_H1
  refine ⟨C_late, hC_late_pos, ?_⟩
  intro Sig lam q hSig hEig a' ha' ha'_lt dm dp hdm
  obtain ⟨ν_strain, hν_strain, hν_strain_le1, hStrain_p⟩ := hTrainLate Sig hSig
  obtain ⟨C_eb, k_eb, ν_eb, hC_eb, hν_eb, hEB_p⟩ :=
    hEB.2 9 (by norm_num : (8 : ℝ) < 9) Sig lam q hSig hEig a' ha' ha'_lt dm dp hdm
  obtain ⟨C_ts, k_ts, ν_bs, hC_ts, hν_bs, hBS_up⟩ :=
    ContBodySourceAux.global_linear_bodySource_upgrade hTS hdm
  set C_out : ℝ := A_H1 * C_eb + A_H1 * (K_H1 + 1) * C_ts
  set k_out : ℕ := max k_eb k_ts
  set ν₀ : ℝ := min (min ν_strain ν_eb) ν_bs
  have hC_out_pos : 0 < C_out := by dsimp [C_out]; positivity
  have hν₀_pos : 0 < ν₀ := lt_min (lt_min hν_strain hν_eb) hν_bs
  refine ⟨C_out, k_out, ν₀, hC_out_pos, hν₀_pos, ?_⟩
  intro p d hreg hν_le hAge hMode
  have hν_pos : 0 < p.ν := p.ν_pos
  have hν_str_le : p.ν ≤ ν_strain :=
    hν_le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν_eb_le : p.ν ≤ ν_eb :=
    hν_le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν_bs_le : p.ν ≤ ν_bs := hν_le.trans (min_le_right _ _)
  have hν1 : p.ν ≤ 1 := hν_str_le.trans hν_strain_le1
  obtain ⟨hH1, _h1Sig_c2, hStrain_bd⟩ := hStrain_p p d hreg hν_str_le hAge
  obtain ⟨αMap, b0Of, b0qOf, b0ηOf, gOf_eb, gqOf_eb, gηOf_eb, zOf_eb, zqOf_eb, zηOf_eb, hEB_F⟩ :=
    hEB_p p d hreg hν_eb_le hAge hMode
  have hEB_for_bs : ∀ F : HpR p.c,
      InFlatClass p.c bgp (b0Of F) ∧
      IsFlatResponse p.ν 0 (toProf p.c F) (b0Of F) ∧
      HasWeakVec vQ0 dZero (b0Of F) (b0qOf F) ∧
      HasWeakVec vEta dZero (b0Of F) (b0ηOf F) ∧
      QPeriodic p.c (gOf_eb F) ∧
      HasWeakVec vQ0 dZero (gOf_eb F) (gqOf_eb F) ∧
      HasWeakVec vEta dZero (gOf_eb F) (gηOf_eb F) ∧
      IsBodySource p.train (b0Of F) (b0qOf F) (b0ηOf F) (gOf_eb F) ∧
      IsMeridionalCorrectionOn p p.H (gOf_eb F) (zOf_eb F) (zqOf_eb F) (zηOf_eb F) (αMap F) ∧
      Measurable (sliceH1Norm p.c (gOf_eb F) (gqOf_eb F) (gηOf_eb F)) ∧
      sLpNorm (13 / 8) p.H (sliceH1Norm p.c (gOf_eb F) (gqOf_eb F) (gηOf_eb F)) ≤
        ENNReal.ofReal (C_eb * (p.ν ^ k_eb)⁻¹ * ‖F‖) := by
    intro F
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, _, h12, _⟩ := hEB_F F
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h12⟩
  obtain ⟨gOf, gqOf, gηOf, hG_F⟩ :=
    hBS_up p d hSig hC_eb hreg hν_bs_le hν1 hAge hH1
      αMap b0Of b0qOf b0ηOf gOf_eb gqOf_eb gηOf_eb zOf_eb zqOf_eb zηOf_eb hEB_for_bs
  set B_strain : ℝ := C_strain / (p.ν * (1 + Sig)) + C_strain * p.ν ^ 3
  have hB_nn : 0 ≤ B_strain := by dsimp [B_strain]; positivity
  set M_eb : HpR p.c → ℝ := fun F => C_eb * (p.ν ^ k_eb)⁻¹ * Real.exp (a' * p.H) * ‖F‖
  have hM_nn : ∀ F, 0 ≤ M_eb F := fun F => by dsimp [M_eb]; positivity
  have hg_srcH1 : ∀ F : HpR p.c, IsCylSourceH1 p.c (gOf F) (gqOf F) (gηOf F) := by
    intro F
    obtain ⟨hsm_g, hsm_gq, hsm_gη, hper_g, hper_gq, hper_gη, hwq_g, hwη_g, hsrc_g, _⟩ := hG_F F
    exact ⟨hsm_g, hsm_gq, hsm_gη, hper_g, hper_gq, hper_gη, hwq_g, hwη_g, hsrc_g.solenoidal⟩
  have hg_Ioc : ∀ F : HpR p.c,
      (∫⁻ s in Ioc 0 p.H, sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F) s) < ⊤ :=
    fun F => (hG_F F).2.2.2.2.2.2.2.2.2.2.2.2.1
  have hg_Ioi : ∀ F : HpR p.c,
      (∫⁻ s in Ioi p.H, sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F) s) < ⊤ :=
    fun F => lt_of_le_of_lt (hG_F F).2.2.2.2.2.2.2.2.2.2.2.2.2.1 ENNReal.ofReal_lt_top
  have hz_mc : ∀ F : HpR p.c,
      IsMeridionalCorrectionOn p p.H (gOf F) (zOf_eb F) (zqOf_eb F) (zηOf_eb F) (αMap F) :=
    fun F => (hG_F F).2.2.2.2.2.2.2.2.2.1
  have hz_early0 : ∀ F : HpR p.c, ∀ s ∈ Ioc 0 p.H,
      sliceH1Norm p.c (zOf_eb F) (zqOf_eb F) (zηOf_eb F) s + ENNReal.ofReal ‖αMap F‖ ≤
        ENNReal.ofReal (M_eb F) :=
    fun F => (hEB_F F).2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨zOf, zqOf, zηOf, hZ_F⟩ :=
    ContLinearGlueAux.linear_meridional_continuation hEx hGlue hGron_step
      hreg hν1 hH1 hB_nn hM_nn hStrain_bd αMap gOf gqOf gηOf zOf_eb zqOf_eb zηOf_eb
      hg_srcH1 hg_Ioc hg_Ioi hz_mc hz_early0
  refine ⟨αMap, b0Of, b0qOf, b0ηOf, gOf, gqOf, gηOf, zOf, zqOf, zηOf, fun F => ?_⟩
  obtain ⟨hb0_cls, hb0_resp, hb0q, hb0η, _⟩ := hEB_F F
  obtain ⟨_, _, _, hper_g, _, _, hwq_g, hwη_g, hsrc_g, _, hm_g, hsLp_g, _, hL1_Ioi, htailLp_g⟩ :=
    hG_F F
  obtain ⟨_, _, _, hm_z, hGlob, hz_early, hz_late⟩ := hZ_F F
  have hk_eb : (p.ν ^ k_eb)⁻¹ ≤ (p.ν ^ k_out)⁻¹ :=
    vb_inv_pow_mono hν_pos hν1 (le_max_left k_eb k_ts)
  have hk_ts : (p.ν ^ k_ts)⁻¹ ≤ (p.ν ^ k_out)⁻¹ :=
    vb_inv_pow_mono hν_pos hν1 (le_max_right k_eb k_ts)
  have hC_eb_le : C_eb ≤ C_out := by
    dsimp [C_out]
    nlinarith [hA_H1, hC_eb.le, mul_nonneg (mul_nonneg hA_pos.le (add_pos hK_H1 one_pos).le) hC_ts.le]
  have hC_ts_le : C_ts ≤ C_out := by
    have hAK : 1 ≤ A_H1 * (K_H1 + 1) :=
      one_le_mul_of_one_le_of_one_le hA_H1 (by linarith)
    have hmul : C_ts ≤ A_H1 * (K_H1 + 1) * C_ts :=
      le_mul_of_one_le_left hC_ts.le hAK
    dsimp [C_out]
    linarith [mul_nonneg hA_pos.le hC_eb.le]
  have hsLp_bd : sLpNorm (13 / 8) p.H (sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F)) ≤
      ENNReal.ofReal (C_out * (p.ν ^ k_out)⁻¹ * ‖F‖) := by
    refine hsLp_g.trans (ENNReal.ofReal_le_ofReal ?_)
    have hmul : C_eb * (p.ν ^ k_eb)⁻¹ ≤ C_out * (p.ν ^ k_out)⁻¹ :=
      mul_le_mul hC_eb_le hk_eb (by positivity) hC_out_pos.le
    exact mul_le_mul_of_nonneg_right hmul (norm_nonneg F)
  have htailLp_bd :
      (∫⁻ s in Ioi (max 1 (p.H - 1)),
          sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F) s ^ bgp ∂sMeas (-9 / 8)) ^
        (4 / 11 : ℝ) ≤
      ENNReal.ofReal (C_out * (p.ν ^ k_out)⁻¹ * ‖F‖) := by
    change tailLpNorm (-9 / 8) (max 1 (p.H - 1)) (sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F)) ≤ _
    refine htailLp_g.trans (ENNReal.ofReal_le_ofReal ?_)
    have hmul : C_ts * (p.ν ^ k_ts)⁻¹ ≤ C_out * (p.ν ^ k_out)⁻¹ :=
      mul_le_mul hC_ts_le hk_ts (by positivity) hC_out_pos.le
    exact mul_le_mul_of_nonneg_right hmul (norm_nonneg F)
  refine ⟨hb0_cls, hb0_resp, hb0q, hb0η, hper_g, hwq_g, hwη_g, hsrc_g, hGlob,
    hm_g, hm_z, hsLp_bd, htailLp_bd, ?_⟩
  intro s hs
  have hKB_eq : K_H1 * B_strain = C_late / (p.ν * (1 + Sig)) + C_late * p.ν ^ 3 := by
    dsimp [B_strain, C_late]; ring
  have hz_late' : ∀ t : ℝ, p.H < t →
      sliceH1Norm p.c (zOf F) (zqOf F) (zηOf F) t ≤
        ENNReal.ofReal (A_H1 * Real.exp (C_late / (p.ν * (1 + Sig)) + C_late * p.ν ^ 3)) *
          (sliceH1Norm p.c (zOf F) (zqOf F) (zηOf F) p.H +
            ENNReal.ofReal (K_H1 + 1) * ∫⁻ r in Ioi p.H,
              sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F) r) := by
    intro t ht
    refine (hz_late t ht).trans ?_
    rw [hKB_eq]
    gcongr
    linarith
  exact global_sliceH1Norm_add_alpha_le_scaled hSig ha' hA_H1 hC_late_pos hC_eb hC_ts
    (add_pos hK_H1 one_pos).le p hν1 hAge F (αMap F)
    (sliceH1Norm p.c (zOf F) (zqOf F) (zηOf F))
    (sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F)) hz_early hz_late' hL1_Ioi hs

theorem globalEnergyContinuation_proof : UnforcedLeray.Short.IIb.GlobalEnergyContinuation :=
  globalEnergyContinuation_of_leaves
    meridionalTailExistence_proof
    meridionalHorizonGluing_proof
    meridionalTailH1Gronwall_proof

end UnforcedLeray.Short.IIb

end
