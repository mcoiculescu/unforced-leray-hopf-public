import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.ZRegular.Src
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_6_1
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_6_2
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.N0
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Levels

/-!
# `PartIII-b:C/rep/8/1/1/1/4` (`GeomX.ZRegular`): regularity and decay of `zAct, zMid, zMt`

Source `the November 2 reference manuscript`
lines 4178-4186, 5400-5406.

On `clearSet ε ν` (`(εϱ)² > ν/1.1 > 5ν/6`, outside the old source cylinder `ϱ ≤ ε⁻¹√(5ν/6)`):

* `zAct = wardX0 (thinG)` and `zMid = wardX0 (meanQ (thinG))`: the chart tensor `G` of the old thin
  source has finite `|G|²` moment and vanishes a.e. for `νs ≤ 6/5`; the phase mean `meanQ G` has the
  same properties (fibrewise Jensen, `ZRegular/Jensen.lean`).  Either gives an a.e. separated
  source (`sepSrc_of_chart`, the proof of `oldSourceReg_of`), so `sepW` is `C²` off the cylinder
  and `O(ϱ⁻³)` (`sepWSmoothOn_of`, `sepFarDecay`);
* `zMt` is the zero-width Newton field: `xsZSmooth` and `xsZDecay` (`OldThinFinite` from `sourceLN0`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace ZRegAux

theorem ϱ_nonneg' (y : Space) : 0 ≤ ϱ y := Real.sqrt_nonneg _

theorem clear_sub_young {ε ν : ℝ} (hε : 0 < ε) (hν : 0 < ν) :
    clearSet ε ν ⊆ {y : Space | ε⁻¹ * Real.sqrt (5 * ν / 6) < ϱ y} := by
  intro y hy
  obtain ⟨h0, h1⟩ := hy
  simp only [mem_setOf_eq] at h0 h1
  have hsq : (ε⁻¹ * Real.sqrt (5 * ν / 6)) ^ 2 = ε⁻¹ ^ 2 * (5 * ν / 6) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hlt : (ε⁻¹ * Real.sqrt (5 * ν / 6)) ^ 2 < ϱ y ^ 2 := by
    rw [hsq]
    have h2 : ν / (11 / 10) < (ε * ϱ y) ^ 2 := h1
    have h3 : ε⁻¹ ^ 2 * (ε * ϱ y) ^ 2 = ϱ y ^ 2 := by field_simp
    have h4 : ε⁻¹ ^ 2 * (5 * ν / 6) < ε⁻¹ ^ 2 * (ε * ϱ y) ^ 2 := by
      apply mul_lt_mul_of_pos_left _ (by positivity)
      have : 5 * ν / 6 < ν / (11 / 10) := by
        rw [div_lt_div_iff₀ (by norm_num) (by norm_num)]; nlinarith
      linarith
    linarith
  exact lt_of_pow_lt_pow_left₀ 2 (ϱ_nonneg' y) hlt

theorem ϱ_eq_cylR' (y : Space) : ϱ y = cylR (WithLp.ofLp y) := by
  simp [ϱ, cylR]

theorem strSum_zero_young (c mZ ρb γ ν : ℝ) {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo)
    (hρ : 0 < ρb) (T : StrG c mZ ρb γ ν) :
    ∀ᵐ p ∂(ageμ c (-1 / 2)), ν * p.1 ≤ 6 / 5 → strSum (chiOStr c mZ ρb γ ν hχo T) p = 0 := by
  have hc1 : ((chiOStr c mZ ρb γ ν hχo T).fst : Chart → Ten3) =ᵐ[gainZ1Measure c mZ γ ν]
      cutFun χo ν • ((T.fst : Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν)) : Chart → Ten3) :=
    NearInst.mulBdd_apply_ae (cutFun χo ν) (cutFun_measurable hχo ν) 1 (cutFun_bound hχo ν) T.fst
  have hc2 : ((chiOStr c mZ ρb γ ν hχo T).snd : Chart → Ten3) =ᵐ[gainHTMeasure c ρb γ ν]
      cutFun χo ν • ((T.snd : Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν)) : Chart → Ten3) :=
    NearInst.mulBdd_apply_ae (cutFun χo ν) (cutFun_measurable hχo ν) 1 (cutFun_bound hχo ν) T.snd
  rw [NearInst.ae_gainZ1Measure, NearInst.ae_z1Measure] at hc1
  rw [NearInst.ae_gainHTMeasure, NearInst.ae_htRhoMeasure hρ] at hc2
  filter_upwards [hc1, hc2] with p e3 e4 hp
  have h0 : cutFun χo ν p = 0 := hχo.zero _ hp
  simp only [strSum, e3, e4, Pi.smul_apply', h0, zero_smul, add_zero]

theorem rho_b_pos' (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (hC0 : 0 < K.C0) :
    0 < L.ρb Pl K := by
  unfold ReturnLevel.ρb UnforcedLeray.Short.IIb.rhoB
  have hν' : 0 < (L.params Pl).ν := L.ν_pos
  have hε' : 0 < (L.params Pl).ε := L.ε_pos
  exact mul_pos (mul_pos (mul_pos hC0 (inv_pos.2 (pow_pos hν' _))) (Real.exp_pos _))
    (Real.rpow_pos_of_pos hε' _)

/-- The zero-width Newton field `zMt` on the clear region. -/
theorem zMt_regular (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (hLH : LHyp (cOf L.ν) L.ν L.ε μ K.χo K.χy) (hmZ : 3 / 2 < K.mZ) (hγ : 0 < gRate Pl)
    (T : LStr Pl K L) (τ : ℝ) :
    ContDiffOn ℝ 1 (zMt Pl K L μ T τ) (clearSet L.ε L.ν) ∧
      ∀ y ∈ clearSet L.ε L.ν, Tendsto (fun t : ℝ => zMt Pl K L μ T τ (outRay y t)) atTop (𝓝 0) := by
  have hν := L.ν_pos
  have hε := L.ε_pos
  obtain ⟨C, k, hC⟩ := sourceLN0 K.mZ (gRate Pl) hmZ hγ
  have hfin : OldThinFinite (cOf L.ν) L.ν (thinRep T) :=
    (hC (cOf L.ν) L.ν (L.ρb Pl K) hLH.c_pos hν hLH.nu_le T).1
  set Zc : Vec3 → Vec3 := youngW (cOf L.ν) L.ν L.ε μ K.χo (thinRep T) -
      youngW (cOf L.ν) L.ν L.ε (μ + 1) K.χo (thinRep T) with hZc
  have hzeq : zMt Pl K L μ T τ = fun y : Space => WithLp.toLp 2 (Zc (WithLp.ofLp y)) := by
    funext y; rfl
  have hsm := xsZSmooth (cOf L.ν) L.ν L.ε μ K.χo (thinRep T) hLH.c_pos hν hε hLH.mu_pos
    hLH.chiO hfin
  have hsd := xsZDecay (cOf L.ν) L.ν L.ε μ K.χo (thinRep T) hLH.c_pos hν hε hLH.mu_pos
    hLH.chiO hfin
  have hmaps : MapsTo (fun y : Space => WithLp.ofLp y) (clearSet L.ε L.ν) (outReg L.ν L.ε) := by
    intro y hy
    obtain ⟨h0, h1⟩ := hy
    simp only [mem_setOf_eq] at h0 h1
    show 5 * L.ν / (6 * L.ε ^ 2) < cylR (WithLp.ofLp y) ^ 2
    rw [← ϱ_eq_cylR']
    have h2 : L.ν / (11 / 10) < (L.ε * ϱ y) ^ 2 := h1
    have h6 : 0 < 6 * L.ε ^ 2 := by positivity
    rw [div_lt_iff₀ h6]
    have : 5 * L.ν / 6 < L.ν / (11 / 10) := by
      rw [div_lt_div_iff₀ (by norm_num) (by norm_num)]; nlinarith
    nlinarith [sq_nonneg L.ε, mul_pow L.ε (ϱ y) 2]
  refine ⟨?_, ?_⟩
  · rw [hzeq]
    have := (PiLp.contDiff_toLp (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 3 => ℝ) (n := 1)).comp_contDiffOn
      ((hsm.comp (PiLp.contDiff_ofLp (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 3 => ℝ) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).contDiffOn
        hmaps).of_le (by exact_mod_cast le_top))
    exact this
  · intro y hy
    have hyp : 0 < ϱ y := hy.1
    set a : ℝ := L.ν / L.ε ^ 2 with ha
    have ha' : 5 * L.ν / (6 * L.ε ^ 2) < a := by
      rw [ha, div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith [pow_pos hε 2, pow_pos hν 2, mul_pos hν (pow_pos hε 2)]
    obtain ⟨C0, hC0⟩ := hsd a ha' 0
    have hq : Tendsto (fun t : ℝ => Zc (WithLp.ofLp (outRay y t))) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hw : Tendsto (fun t : ℝ => (1 + t / 2)) atTop atTop :=
        tendsto_atTop_add_const_left _ _ (tendsto_id.atTop_div_const (by norm_num))
      have hz : Tendsto (fun t : ℝ => |C0| * (1 + t / 2) ^ (-(4 : ℝ))) atTop (𝓝 0) := by
        have := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 4)).comp hw
        simpa using this.const_mul |C0|
      refine squeeze_zero_norm' ?_ hz
      filter_upwards [eventually_ge_atTop (L.ε⁻¹ * (L.ν + 1))] with t ht
      rw [norm_norm]
      have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
      have hϱ : ϱ (outRay y t) = t := outRay_ϱ hyp ht0.le
      have hcyl : cylR (WithLp.ofLp (outRay y t)) = t := by rw [← ϱ_eq_cylR']; exact hϱ
      have hat : a ≤ cylR (WithLp.ofLp (outRay y t)) ^ 2 := by
        rw [hcyl, ha]
        have h1 : L.ε⁻¹ * (L.ν + 1) ≤ t := ht
        have h2 : (L.ε⁻¹ * (L.ν + 1)) ^ 2 ≤ t ^ 2 := by
          gcongr
        have h3 : L.ν / L.ε ^ 2 ≤ (L.ε⁻¹ * (L.ν + 1)) ^ 2 := by
          rw [mul_pow, inv_pow, ← div_eq_inv_mul]
          apply div_le_div_of_nonneg_right _ (by positivity)
          nlinarith
        exact h3.trans h2
      have hmain := hC0 _ hat
      rw [norm_iteratedFDeriv_zero] at hmain
      have hn := norm_le_pi_norm (WithLp.ofLp (outRay y t)) 0
      have hn1 := norm_le_pi_norm (WithLp.ofLp (outRay y t)) 1
      have e0 : (WithLp.ofLp (outRay y t)) 0 ^ 2 + (WithLp.ofLp (outRay y t)) 1 ^ 2 = t ^ 2 := by
        have := hcyl
        unfold cylR at this
        have h5 := Real.sq_sqrt (by positivity : 0 ≤ (WithLp.ofLp (outRay y t)) 0 ^ 2 +
          (WithLp.ofLp (outRay y t)) 1 ^ 2)
        rw [this] at h5
        linarith
      have hhalf : t / 2 ≤ ‖WithLp.ofLp (outRay y t)‖ := by
        set w := WithLp.ofLp (outRay y t) with hw
        have h0' : |w 0| ≤ ‖w‖ := by simpa using hn
        have h1' : |w 1| ≤ ‖w‖ := by simpa using hn1
        have h2 : t ^ 2 ≤ (2 * ‖w‖) ^ 2 := by
          rw [← e0, ← sq_abs (w 0), ← sq_abs (w 1)]
          nlinarith [abs_nonneg (w 0), abs_nonneg (w 1)]
        have h3 := abs_le_of_sq_le_sq' h2 (by positivity)
        linarith [h3.2]
      have hu : (1 + ‖WithLp.ofLp (outRay y t)‖) ^ (-(4 + ((0 : ℕ) : ℝ))) ≤
          (1 + t / 2) ^ (-(4 : ℝ)) := by
        have := Real.rpow_le_rpow_of_nonpos (x := 1 + t / 2) (y := 1 + ‖WithLp.ofLp (outRay y t)‖)
          (z := -(4 + ((0 : ℕ) : ℝ))) (by positivity) (by linarith) (by norm_num)
        simpa using this
      have hu0 : 0 ≤ (1 + ‖WithLp.ofLp (outRay y t)‖) ^ (-(4 + ((0 : ℕ) : ℝ))) :=
        Real.rpow_nonneg (by positivity) _
      calc ‖Zc (WithLp.ofLp (outRay y t))‖
          ≤ C0 * (1 + ‖WithLp.ofLp (outRay y t)‖) ^ (-(4 + ((0 : ℕ) : ℝ))) := hmain
        _ ≤ |C0| * (1 + ‖WithLp.ofLp (outRay y t)‖) ^ (-(4 + ((0 : ℕ) : ℝ))) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) hu0
        _ ≤ |C0| * (1 + t / 2) ^ (-(4 : ℝ)) := mul_le_mul_of_nonneg_left hu (abs_nonneg _)
    rw [hzeq]
    have e0 : (0 : Space) = WithLp.toLp 2 (fun _ : Fin 3 => (0 : ℝ)) := rfl
    have := ((PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).tendsto (0 : Vec3)).comp hq
    rw [e0]
    exact this

/-- `ZRegularAt` at one regime with the standing hypotheses. -/
theorem zRegularAt_of (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (hLH : LHyp (cOf L.ν) L.ν L.ε μ K.χo K.χy) (hmZ : 3 / 2 < K.mZ) (hγ : 0 < gRate Pl)
    (hC0 : 0 < K.C0) : ZRegularAt Pl K L μ := by
  intro T τ
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hc := hLH.c_pos
  have hρb := rho_b_pos' Pl K L hC0
  have hμ : -(1 / 4) < μ := by linarith [hLH.mu_pos]
  set Tc := chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo (thinPart T) with hTc
  have hGdef : thinG Pl K L T = strSum Tc := rfl
  have hGm : Measurable (thinG Pl K L T) := by
    unfold thinG
    exact (Lp.stronglyMeasurable _).measurable.add (Lp.stronglyMeasurable _).measurable
  have hmom : ∫⁻ p, ‖thinG Pl K L T p‖ₑ ^ 2 ∂(ageμ (cOf L.ν) (-1 / 2)) < ⊤ := by
    rw [hGdef]
    exact strChartL2 (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν hρb (by linarith) hν Tc
  have hz : ∀ᵐ p ∂(ageμ (cOf L.ν) (-1 / 2)), L.ν * p.1 ≤ 6 / 5 → thinG Pl K L T p = 0 := by
    rw [hGdef]
    exact strSum_zero_young _ _ _ _ _ K.hχo hρb _
  obtain ⟨P1, T1, hP1, hS1, hM1, hE1⟩ :=
    sepSrc_of_chart (cOf L.ν) L.ν L.ε hc hν hε _ hGm hmom hz
  have hGm' := measurable_meanQ' (cOf L.ν) hGm
  have hmom' : ∫⁻ p, ‖meanQ (cOf L.ν) (thinG Pl K L T) p‖ₑ ^ 2 ∂(ageμ (cOf L.ν) (-1 / 2)) < ⊤ :=
    lt_of_le_of_lt (mean_moment_le _ _ hc _ hGm) hmom
  have hz' := mean_ae_zero (cOf L.ν) (-1 / 2) L.ν hc _ hGm hz
  obtain ⟨P2, T2, hP2, hS2, hM2, hE2⟩ :=
    sepSrc_of_chart (cOf L.ν) L.ν L.ε hc hν hε _ hGm' hmom' hz'
  have hr0 : 0 ≤ L.ε⁻¹ * Real.sqrt (5 * L.ν / 6) := by positivity
  have hsub := clear_sub_young hε hν
  have hA2 : ContDiffOn ℝ 2 (zAct Pl K L μ T τ) (clearSet L.ε L.ν) :=
    (wardX0_cd hν hμ hr0 hP1 hS1 hM1 hE1 τ).mono hsub
  have hM2' : ContDiffOn ℝ 2 (zMid Pl K L μ T τ) (clearSet L.ε L.ν) :=
    (wardX0_cd hν hμ hr0 hP2 hS2 hM2 hE2 τ).mono hsub
  obtain ⟨hZ1, hZ2⟩ := zMt_regular Pl K L μ hLH hmZ hγ T τ
  refine ⟨?_, ?_⟩
  · intro Z hZ
    rcases hZ with rfl | rfl | rfl
    · exact hA2.of_le (by norm_num)
    · exact hM2'.of_le (by norm_num)
    · exact hZ1
  · intro Z hZ y hy
    rcases hZ with rfl | rfl | rfl
    · exact wardX0_tendsto hν hμ hr0 hP1 hS1 hM1 hE1 τ hy.1
    · exact wardX0_tendsto hν hμ hr0 hP2 hS2 hM2 hE2 τ hy.1
    · exact hZ2 y hy

end ZRegAux

open ZRegAux in
/-- **`PartIII-b:C/rep/8/1/1/1/4`** (`zRegular`): along the sequence, the three fields are `C¹` on
the clear region and tend to zero along every outward ray (source 4178-4186, 5400-5406). -/
theorem zRegular (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.ZRegular := by
  unfold SeqData.ZRegular
  filter_upwards [D.eventually_lHyp hst.omega_ne hst.gamma_pos hst.sigma_pos hst.sigma_lt
    hst.chiY] with n hn z hz
  have h : LHyp (cOf (D.level n).ν) (D.level n).ν (D.level n).ε (D.mu n z) D.K.χo D.K.χy :=
    hn z hz
  exact zRegularAt_of D.Pl D.K (D.level n) (D.mu n z) h hst.mZ_gt hst.gamma_pos hst.C0_pos

end UnforcedLeray.Short.PartIIIb.Concrete
