import UnforcedLeray.Short.PartIIIb.Proofs.Wiring.Inputs
import UnforcedLeray.Short.Spine.ParamsProofs

/-!
# Conditional assembly of `Wiring.BackgroundBridge` (`PartIII-b:IIIb-D5/bridge/org`)

Source of record: `the November 2 reference manuscript`, lines 117-118,
2026-2037, 2316-2318, 2505-2561, 2607-2612, 2641-2642, 2664-2713, 4139-4141, 5134-5139.

From `Spine.IsShortBackground` at `(m, C, N, Sig)` along the sequence (`m ≤ m₀`, `2m₀ < 3d₋/11`,
`2C ≤ C₀`, `N ≤ k₀`), this file proves directly:
1. `levelParams_eq`: `((seqOf …).level n).params R.planar = (B n).par`;
2. `IIb.BgRegime` at large levels (from `Spine.parameterAsymptotics`, `levelTrain_buc` and
   `PartI.TrainStreamSmooth`);
3. `IsBallSplit` at large levels (from `hB.ball` and `hB.equation`);
4. `IIb.ExactSplitII` at large levels (from `hB.equation`, `hB.entrance_bound`, `hB.rb_Lp`,
   `hB.rb_sup` and `Cons.C03.Concrete.ageCutoff_eq_zero`);
5. the inlet support bound `D.Sin n ≤ (retEps D.Pl D.σ₀ n) ^ (-D.K.b)` at large levels;
6. `RepairDerivBound` at large levels (from `hB.rb_sup` and `hB.rb_derivatives`).

The remaining two fields of `SeqData.IsActualLevel` — `profile : IsExactProfile` and `presL2` —
reduce via `levelPres` to `ShortBgExactProfile`: for every sequence of backgrounds satisfying
`Spine.IsShortBackground` at `(m, C, N, Sig)` with `2m < 3d₋/11`, there exists at large levels a
smooth `P_n`-periodic pressure `pr` with `pr(τ) - c(τ) ∈ L²` and `∇pr(τ) ∈ L^{11/4}` satisfying
the pointwise unforced profile equation `IsExactProfile`.
`backgroundBridge_of` assembles `Wiring.BackgroundBridge` from `ShortBgExactProfile`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.Wiring

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Blueprint.Planar
open UnforcedLeray.Cons.Data UnforcedLeray.Cons.C03.Concrete

/-- **Exact profile and pressure regularity along a short-background sequence** (source 117-118,
2505-2561, 2607-2612, 2641-2642, 4139-4141): for every sequence `B : ℕ → Spine.ShortBackground`
satisfying `Spine.IsShortBackground` at `(m, C, N, Sig)` for large `n` with `2m < 3d₋/11`, at all
large levels `n` there exists a smooth `P_n`-periodic pressure `pr` with `pr(τ) - c(τ) ∈ L²(ℝ³)`,
`∇pr(τ) ∈ L^{11/4}(ℝ³)` and `IsExactProfile ν_n P_n (B n).U pr`. -/
def ShortBgExactProfile : Prop :=
  ∀ R : Reference, R.IsReferenceChoice →
    ∀ (m dm dp C Sig : ℝ) (N : ℕ),
      0 < m → 0 < dm → 2 * m < 3 * dm / 11 → dm < gRate R.planar / 3 → gRate R.planar / 3 < dp →
      0 < Sig →
      ∀ B : ℕ → Spine.ShortBackground,
        (∀ᶠ n : ℕ in atTop,
          Spine.IsShortBackground R.planar (Spine.nuSeq R n) (Spine.epsSeq R n) m C N Sig (B n)) →
        ∀ᶠ n : ℕ in atTop, ∃ pr : ℝ → Space → ℝ,
          IsExactProfile (retNu R.planar R.σ₀ n)
            (2 * retEps R.planar R.σ₀ n * cOf (retNu R.planar R.σ₀ n)) (B n).U pr ∧
          ∀ τ : ℝ, (∃ c : ℝ, MemLp (fun y : Space => pr τ y - c) 2 volume) ∧
            MemLp (physGrad (pr τ)) (11 / 4) volume

/-- At any level satisfying `Spine.IsShortBackground`, the `Params` of `seqOf` equals `(B n).par`. -/
theorem levelParams_eq {R : Reference} (hc : R.planar.signedCoeff R.σ₀ ≠ 0) (K : ReturnConsts)
    (Sig : ℝ) (hSig : 0 < Sig) (htr : PartI.TrainGlobalExistence) (hsm : PartI.TrainStreamSmooth)
    (κ : IIIa.PlanarFrameKernels) (B : ℕ → Spine.ShortBackground) {m C : ℝ} {N n : ℕ}
    (hB : Spine.IsShortBackground R.planar (Spine.nuSeq R n) (Spine.epsSeq R n) m C N Sig (B n)) :
    ((seqOf R hc K Sig hSig htr hsm κ B).level n).params R.planar = (B n).par := by
  have hν' : (B n).par.ν = retNu R.planar R.σ₀ n := hB.nu_eq
  have hε' : (B n).par.ε = retEps R.planar R.σ₀ n := hB.eps_eq
  have hc' : (B n).par.c = cOf (retNu R.planar R.σ₀ n) :=
    hB.c_eq.trans (per_eq (Spine.nuSeq R n))
  have htr_eq : levelTrain htr R n (B n) =
      cast (by rw [hν', hc']) (B n).par.trainData :=
    dif_pos ⟨hν', hc', hB.train_buc⟩
  symm
  simpa [ReturnLevel.params, SeqData.level, seqOf, htr_eq] using
    Spine.ShortBackground.params_eq_mk (B n).par hν' hc' hε' hB.ageCut_eq hB.mode_eq
      (retNu_pos R.planar R.σ₀ n) (cOf_pos (retNu_pos R.planar R.σ₀ n))
      (retEps_pos hc n) hSig

/-- `C ≥ 0` from `Spine.IsShortBackground` (`0 ≤ ‖rb 0 0‖ ≤ lossRadius`). -/
theorem nonneg_C_of_isShort {Pl : PlanarData} {ν ε m C Sig : ℝ} {N : ℕ}
    {B : Spine.ShortBackground} (hν : 0 < ν) (hε : 0 < ε)
    (hB : Spine.IsShortBackground Pl ν ε m C N Sig B) : 0 ≤ C := by
  have hLR : 0 ≤ Spine.lossRadius ν ε m C N := le_trans (norm_nonneg _) (hB.rb_sup 0 0).1
  by_contra hneg
  have hneg0 : C < 0 := not_le.1 hneg
  have hpos : 0 < (ν ^ N)⁻¹ * Real.exp (m / ν) * ε ^ (3 / 11 : ℝ) :=
    mul_pos (mul_pos (inv_pos.2 (pow_pos hν N)) (Real.exp_pos _))
      (Real.rpow_pos_of_pos hε _)
  have hneg' : C * (ν ^ N)⁻¹ * Real.exp (m / ν) * ε ^ (3 / 11 : ℝ) < 0 := by
    have hm := mul_neg_of_neg_of_pos hneg0 hpos
    calc C * (ν ^ N)⁻¹ * Real.exp (m / ν) * ε ^ (3 / 11 : ℝ)
        = C * ((ν ^ N)⁻¹ * Real.exp (m / ν) * ε ^ (3 / 11 : ℝ)) := by ring
      _ < 0 := hm
  unfold Spine.lossRadius at hLR
  linarith

/-- For `0 < ν ≤ 1`, `0 < ε`, `m ≤ m0`, `0 ≤ C`, `2 * C ≤ C0`, `N ≤ k0`,
`2 * lossRadius ν ε m C N ≤ C0 * (ν ^ k0)⁻¹ * exp(m0 / ν) * ε ^ (3 / 11)`. -/
theorem two_mul_lossRadius_le {ν ε m m0 C C0 : ℝ} {N k0 : ℕ}
    (hν : 0 < ν) (hν1 : ν ≤ 1) (hε : 0 < ε) (hm : m ≤ m0) (hC : 0 ≤ C) (hCC : 2 * C ≤ C0)
    (hN : N ≤ k0) :
    2 * Spine.lossRadius ν ε m C N ≤
      C0 * (ν ^ k0)⁻¹ * Real.exp (m0 / ν) * ε ^ (3 / 11 : ℝ) := by
  have hpow : ν ^ k0 ≤ ν ^ N := pow_le_pow_of_le_one hν.le hν1 hN
  have hX : (ν ^ N)⁻¹ ≤ (ν ^ k0)⁻¹ := inv_anti₀ (pow_pos hν k0) hpow
  have hC0 : 0 ≤ C0 := by linarith
  have h1 : (2 * C) * (ν ^ N)⁻¹ ≤ C0 * (ν ^ k0)⁻¹ :=
    mul_le_mul hCC hX (inv_nonneg.2 (pow_nonneg hν.le _)) hC0
  have hexp : Real.exp (m / ν) ≤ Real.exp (m0 / ν) :=
    Real.exp_le_exp.2 (div_le_div_of_nonneg_right hm hν.le)
  have h2 : Real.exp (m / ν) * ε ^ (3 / 11 : ℝ) ≤ Real.exp (m0 / ν) * ε ^ (3 / 11 : ℝ) :=
    mul_le_mul_of_nonneg_right hexp (Real.rpow_nonneg hε.le _)
  unfold Spine.lossRadius
  calc 2 * (C * (ν ^ N)⁻¹ * Real.exp (m / ν) * ε ^ (3 / 11 : ℝ))
      = ((2 * C) * (ν ^ N)⁻¹) * (Real.exp (m / ν) * ε ^ (3 / 11 : ℝ)) := by ring
    _ ≤ (C0 * (ν ^ k0)⁻¹) * (Real.exp (m0 / ν) * ε ^ (3 / 11 : ℝ)) :=
        mul_le_mul h1 h2 (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hε.le _))
          (mul_nonneg hC0 (inv_nonneg.2 (pow_nonneg hν.le _)))
    _ = C0 * (ν ^ k0)⁻¹ * Real.exp (m0 / ν) * ε ^ (3 / 11 : ℝ) := by ring

/-- For `0 < ν`, `0 < ε ≤ 1`, `entranceRadius ν ε m C N ≤ lossRadius ν ε m C N`. -/
theorem entranceRadius_le_lossRadius {ν ε m C : ℝ} {N : ℕ}
    (hν : 0 < ν) (hε : 0 < ε) (hε1 : ε ≤ 1) (hC : 0 ≤ C) :
    Spine.entranceRadius ν ε m C N ≤ Spine.lossRadius ν ε m C N := by
  have heps : ε ≤ ε ^ (3 / 11 : ℝ) := by
    calc ε = ε ^ (1 : ℝ) := (Real.rpow_one ε).symm
      _ ≤ ε ^ (3 / 11 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hε hε1 (by norm_num)
  have hfac : 0 ≤ C * (ν ^ N)⁻¹ * Real.exp (m / ν) :=
    mul_nonneg (mul_nonneg hC (inv_nonneg.2 (pow_nonneg hν.le _))) (Real.exp_pos _).le
  unfold Spine.entranceRadius Spine.lossRadius
  exact mul_le_mul_of_nonneg_left heps hfac

/-- The inlet profile vanishes near every chart point of age `> H/2`. -/
private theorem inletProfile_eq_zero_of_age (p : Params) (i : Fin 2) {m : ℝ × (ℝ × ℝ)}
    (hm : p.H / 2 < m.1) : p.inletProfile i m = 0 := by
  have hev : p.cutStream i =ᶠ[𝓝 m] fun _ => (0 : ℝ) := by
    have h1 : ∀ᶠ x in 𝓝 m, p.H / 2 < x.1 :=
      (continuous_fst.tendsto m).eventually (lt_mem_nhds hm)
    filter_upwards [h1] with x hx
    simp [Params.cutStream, ageCutoff_eq_zero p.H_pos hx.le]
  have hφ : p.cutStream i m = 0 := by
    simp [Params.cutStream, ageCutoff_eq_zero p.H_pos hm.le]
  have hd : fderiv ℝ (p.cutStream i) m = 0 := by
    rw [hev.fderiv_eq]
    simp
  simp only [Params.inletProfile, UnforcedLeray.Axi.ringStreamProfile, UnforcedLeray.Axi.dEta,
    UnforcedLeray.Axi.dQ, UnforcedLeray.Axi.dS, hφ, hd]
  simp

/-- The inlet columns vanish at ages `s > H/2`, i.e. when `(H/2) ϱ² < R²` (SP 2716). -/
private theorem inlet_zero_of (p : Params) (i : Fin 2) (τ : ℝ) (y : Space)
    (h : p.H / 2 * (y 0 ^ 2 + y 1 ^ 2) < p.R ^ 2) : p.inlet i τ y = 0 := by
  have hϱ : UnforcedLeray.Axi.ϱ y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
    unfold UnforcedLeray.Axi.ϱ
    exact Real.sq_sqrt (by positivity)
  simp only [Params.inlet, UnforcedLeray.Axi.Nv]
  by_cases h0 : y 0 ^ 2 + y 1 ^ 2 = 0
  · have hage : UnforcedLeray.Axi.age p.R y = 0 := by
      unfold UnforcedLeray.Axi.age
      rw [hϱ, h0, div_zero]
    rw [hage, Real.sqrt_zero, zero_smul]
  · have hpos : 0 < y 0 ^ 2 + y 1 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h0)
    have hgt : p.H / 2 < (UnforcedLeray.Axi.chart p.R τ y).1 := by
      show p.H / 2 < UnforcedLeray.Axi.age p.R y
      unfold UnforcedLeray.Axi.age
      rw [hϱ]
      exact (lt_div_iff₀ hpos).2 h
    rw [inletProfile_eq_zero_of_age p i hgt]
    simp

/-- Relation between `phaseLr P (11 / 4)` and `eLpNorm` on `periodSlab P`. -/
theorem phaseLr_le_of_periodSlab_eLpNorm {E : Type*} [NormedAddCommGroup E]
    {P M : ℝ} (hP : 0 < P) (G : SpaceTime → E)
    (hG : MemLp G (11 / 4) (volume.restrict (periodSlab P)))
    (hb : (eLpNorm G (11 / 4) (volume.restrict (periodSlab P))).toReal ≤
      P ^ (4 / 11 : ℝ) * M) :
    phaseLr P (11 / 4) (fun x => ‖G x‖) ≤ ENNReal.ofReal M := by
  have hslab : (volume : Measure SpaceTime).restrict (periodSlab P) =
      (volume.restrict (Ioc (0 : ℝ) P)).prod (volume : Measure Space) := by
    unfold periodSlab
    rw [show (volume : Measure SpaceTime) = (volume : Measure ℝ).prod (volume : Measure Space) from
      rfl, ← Measure.prod_restrict, Measure.restrict_univ]
  have hmeas : AEMeasurable (fun x : SpaceTime => ENNReal.ofReal |‖G x‖| ^ (11 / 4 : ℝ))
      ((volume.restrict (Ioc (0 : ℝ) P)).prod (volume : Measure Space)) := by
    rw [← hslab]
    have h1 : (fun x : SpaceTime => ENNReal.ofReal |‖G x‖| ^ (11 / 4 : ℝ)) =
        (fun x : SpaceTime => (‖G x‖ₑ : ℝ≥0∞) ^ (11 / 4 : ℝ)) := by
      funext x
      rw [abs_of_nonneg (norm_nonneg _), ← Real.enorm_eq_ofReal (norm_nonneg _), enorm_norm]
    rw [h1]
    exact hG.1.enorm.pow_const (11 / 4 : ℝ)
  have hton : (∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space,
      ENNReal.ofReal |‖G (t, y)‖| ^ (11 / 4 : ℝ)) =
      ∫⁻ x in periodSlab P, (‖G x‖ₑ : ℝ≥0∞) ^ (11 / 4 : ℝ) := by
    rw [← lintegral_prod _ hmeas, ← hslab]
    refine lintegral_congr fun x => ?_
    rw [abs_of_nonneg (norm_nonneg _), ← Real.enorm_eq_ofReal (norm_nonneg _), enorm_norm]
  have heLp : (∫⁻ x in periodSlab P, (‖G x‖ₑ : ℝ≥0∞) ^ (11 / 4 : ℝ)) ^
      (1 / (11 / 4 : ℝ)) = eLpNorm G (11 / 4) (volume.restrict (periodSlab P)) := by
    have h0 : (11 / 4 : ℝ≥0∞) ≠ 0 := by norm_num
    have htop : (11 / 4 : ℝ≥0∞) ≠ ⊤ :=
      ENNReal.div_ne_top ENNReal.coe_ne_top (by norm_num)
    have htoR : ((11 / 4 : ℝ≥0∞).toReal) = (11 / 4 : ℝ) := by norm_num
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h0 htop, htoR]
  have hbound : eLpNorm G (11 / 4) (volume.restrict (periodSlab P)) ≤
      ENNReal.ofReal (P ^ (4 / 11 : ℝ) * M) := by
    rw [← ENNReal.ofReal_toReal (ne_of_lt hG.2)]
    exact ENNReal.ofReal_le_ofReal hb
  unfold phaseLr
  rw [hton, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / (11 / 4)), heLp]
  have hPinv : ENNReal.ofReal P⁻¹ ^ (1 / (11 / 4 : ℝ)) = ENNReal.ofReal (P⁻¹ ^ (4 / 11 : ℝ)) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.2 hP.le) (by norm_num)]
    congr 1
    norm_num
  rw [hPinv]
  calc ENNReal.ofReal (P⁻¹ ^ (4 / 11 : ℝ)) *
        eLpNorm G (11 / 4) (volume.restrict (periodSlab P))
      ≤ ENNReal.ofReal (P⁻¹ ^ (4 / 11 : ℝ)) * ENNReal.ofReal (P ^ (4 / 11 : ℝ) * M) :=
        mul_le_mul_right hbound _
    _ = ENNReal.ofReal (P⁻¹ ^ (4 / 11 : ℝ) * (P ^ (4 / 11 : ℝ) * M)) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (inv_nonneg.2 hP.le) _)]
    _ = ENNReal.ofReal M := by
        congr 1
        rw [Real.inv_rpow hP.le, ← mul_assoc, inv_mul_cancel₀ (Real.rpow_pos_of_pos hP _).ne',
          one_mul]

/-- `IsBallSplit` at a level satisfying `Spine.IsShortBackground`. -/
theorem isBallSplit_of_isShort {R : Reference} (hc : R.planar.signedCoeff R.σ₀ ≠ 0)
    (K : ReturnConsts) (Sig : ℝ) (hSig : 0 < Sig) (htr : PartI.TrainGlobalExistence)
    (hsm : PartI.TrainStreamSmooth) (κ : IIIa.PlanarFrameKernels)
    (B : ℕ → Spine.ShortBackground) {m C : ℝ} {N n : ℕ}
    (hB : Spine.IsShortBackground R.planar (Spine.nuSeq R n) (Spine.epsSeq R n) m C N Sig (B n))
    (hLR : Spine.lossRadius (Spine.nuSeq R n) (Spine.epsSeq R n) m C N ≤
      ((seqOf R hc K Sig hSig htr hsm κ B).level n).ρb R.planar K) :
    IsBallSplit (((seqOf R hc K Sig hSig htr hsm κ B).level n).params R.planar)
      (((seqOf R hc K Sig hSig htr hsm κ B).level n).ρb R.planar K) ((B n).V) ((B n).rb) := by
  rw [levelParams_eq hc K Sig hSig htr hsm κ B hB]
  exact ⟨(B n).z, hB.equation, fun _ _ => rfl, rfl, hB.ball.trans hLR⟩

/-- `IIb.ExactSplitII` at a level satisfying `Spine.IsShortBackground`. -/
theorem exactSplitII_of_isShort {R : Reference} (hc : R.planar.signedCoeff R.σ₀ ≠ 0)
    (K : ReturnConsts) (Sig : ℝ) (hSig : 0 < Sig) (htr : PartI.TrainGlobalExistence)
    (hsm : PartI.TrainStreamSmooth) (κ : IIIa.PlanarFrameKernels)
    (B : ℕ → Spine.ShortBackground) {m C : ℝ} {N n : ℕ}
    (hε1 : Spine.epsSeq R n ≤ 1)
    (hB : Spine.IsShortBackground R.planar (Spine.nuSeq R n) (Spine.epsSeq R n) m C N Sig (B n))
    (h2LR : 2 * Spine.lossRadius (Spine.nuSeq R n) (Spine.epsSeq R n) m C N ≤
      ((seqOf R hc K Sig hSig htr hsm κ B).level n).ρb R.planar K) :
    IIb.ExactSplitII (((seqOf R hc K Sig hSig htr hsm κ B).level n).params R.planar)
      (((seqOf R hc K Sig hSig htr hsm κ B).level n).ρb R.planar K)
      (Sig / (2 * retNu R.planar R.σ₀ n)) ((B n).V) ((B n).rb) := by
  rw [levelParams_eq hc K Sig hSig htr hsm κ B hB]
  set LR := Spine.lossRadius (Spine.nuSeq R n) (Spine.epsSeq R n) m C N
  have hLR0 : 0 ≤ LR := le_trans (norm_nonneg _) (hB.rb_sup 0 0).1
  have hLR : LR ≤ ((seqOf R hc K Sig hSig htr hsm κ B).level n).ρb R.planar K := by linarith
  have hC : 0 ≤ C := nonneg_C_of_isShort (retNu_pos R.planar R.σ₀ n) (retEps_pos hc n) hB
  refine ⟨⟨(B n).z, hB.equation, fun _ _ => rfl, rfl, fun i => ?_⟩, fun τ => ?_, fun i τ y hy => ?_⟩
  · exact (hB.entrance_bound i).trans
      ((entranceRadius_le_lossRadius (retNu_pos R.planar R.σ₀ n) (retEps_pos hc n) hε1 hC).trans hLR)
  · have hbgp : ENNReal.ofReal IIb.bgp = (11 / 4 : ℝ≥0∞) := by
      unfold IIb.bgp
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
      simp
    have hL : eLpNorm ((B n).rb τ) (ENNReal.ofReal IIb.bgp) volume ≤ ENNReal.ofReal LR := by
      rw [hbgp, ← ENNReal.ofReal_toReal (ne_of_lt (hB.rb_Lp τ).1.2)]
      exact ENNReal.ofReal_le_ofReal (hB.rb_Lp τ).2
    have hT : eLpNorm ((B n).rb τ) ⊤ volume ≤ ENNReal.ofReal LR := by
      rw [eLpNorm_exponent_top]
      exact eLpNormEssSup_le_of_ae_bound (ae_of_all _ fun y => (hB.rb_sup τ y).1)
    calc eLpNorm ((B n).rb τ) (ENNReal.ofReal IIb.bgp) volume +
          eLpNorm ((B n).rb τ) ⊤ volume
        ≤ ENNReal.ofReal LR + ENNReal.ofReal LR := add_le_add hL hT
      _ = ENNReal.ofReal (2 * LR) := by
          rw [two_mul, ENNReal.ofReal_add hLR0 hLR0]
      _ ≤ ENNReal.ofReal (((seqOf R hc K Sig hSig htr hsm κ B).level n).ρb R.planar K) :=
          ENNReal.ofReal_le_ofReal h2LR
  · have hH : (B n).par.H / 2 = Sig / (2 * retNu R.planar R.σ₀ n) := by
      unfold Params.H
      rw [hB.ageCut_eq, hB.nu_eq]
      show Sig / retNu R.planar R.σ₀ n / 2 = _
      ring
    apply inlet_zero_of (B n).par i τ y
    rwa [hH]

/-- `RepairDerivBound` at a level satisfying `Spine.IsShortBackground`. -/
theorem repairDeriv_of_isShort {R : Reference} (hc : R.planar.signedCoeff R.σ₀ ≠ 0)
    (K : ReturnConsts) (Sig : ℝ) (hSig : 0 < Sig) (htr : PartI.TrainGlobalExistence)
    (hsm : PartI.TrainStreamSmooth) (κ : IIIa.PlanarFrameKernels)
    (B : ℕ → Spine.ShortBackground) {m C : ℝ} {N n : ℕ} (hm : m ≤ K.m0)
    (hB : Spine.IsShortBackground R.planar (Spine.nuSeq R n) (Spine.epsSeq R n) m C N Sig (B n)) :
    RepairDerivBound K ((seqOf R hc K Sig hSig htr hsm κ B).level n) (max C 0) N := by
  let L := (seqOf R hc K Sig hSig htr hsm κ B).level n
  have hν : 0 < Spine.nuSeq R n := retNu_pos R.planar R.σ₀ n
  have hε : 0 < Spine.epsSeq R n := retEps_pos hc n
  have hC : 0 ≤ C := nonneg_C_of_isShort hν hε hB
  set LR := Spine.lossRadius (Spine.nuSeq R n) (Spine.epsSeq R n) m C N
  have hLR0 : 0 ≤ LR := le_trans (norm_nonneg _) (hB.rb_sup 0 0).1
  have hLR_le : LR ≤ max C 0 * L.ν⁻¹ ^ N * rhoRep K L := by
    have hmax : C = max C 0 := (max_eq_left hC).symm
    have hexp : Real.exp (m / Spine.nuSeq R n) ≤ Real.exp (K.m0 / Spine.nuSeq R n) :=
      Real.exp_le_exp.2 (div_le_div_of_nonneg_right hm hν.le)
    have hfac : 0 ≤ C * (Spine.nuSeq R n ^ N)⁻¹ * Spine.epsSeq R n ^ (3 / 11 : ℝ) :=
      mul_nonneg (mul_nonneg hC (inv_nonneg.2 (pow_nonneg hν.le _))) (Real.rpow_nonneg hε.le _)
    have h1 := mul_le_mul_of_nonneg_left hexp hfac
    unfold LR Spine.lossRadius rhoRep
    show C * (Spine.nuSeq R n ^ N)⁻¹ * Real.exp (m / Spine.nuSeq R n) *
        Spine.epsSeq R n ^ (3 / 11 : ℝ) ≤
      max C 0 * (Spine.nuSeq R n)⁻¹ ^ N *
        (Spine.epsSeq R n ^ (3 / 11 : ℝ) * Real.exp (K.m0 / Spine.nuSeq R n))
    rw [← hmax, inv_pow]
    linarith [h1]
  have hP_eq : 2 * L.ε * cOf L.ν = Spine.shortPeriod (Spine.nuSeq R n) (Spine.epsSeq R n) := by
    show 2 * retEps R.planar R.σ₀ n * cOf (retNu R.planar R.σ₀ n) =
      2 * Spine.epsSeq R n * Train.per (Spine.nuSeq R n)
    rw [per_eq]
    rfl
  have hP_pos : 0 < Spine.shortPeriod (Spine.nuSeq R n) (Spine.epsSeq R n) := by
    rw [← hP_eq]
    exact mul_pos (mul_pos two_pos hε) (cOf_pos hν)
  refine ⟨fun τ y => ((hB.rb_sup τ y).2).trans hLR_le, ?_, ?_⟩
  · have h1 := hB.rb_derivatives 1 le_rfl (by norm_num)
    have hnorm1 : (fun x : SpaceTime => ‖fderiv ℝ (L.rb x.1) x.2‖) =
        (fun x : SpaceTime => ‖iteratedFDeriv ℝ 1 ((B n).rb x.1) x.2‖) := by
      funext x
      exact (norm_iteratedFDeriv_one (𝕜 := ℝ) (f := (B n).rb x.1) (x := x.2)).symm
    rw [hP_eq, hnorm1]
    exact (phaseLr_le_of_periodSlab_eLpNorm hP_pos _ h1.1 h1.2).trans
      (ENNReal.ofReal_le_ofReal hLR_le)
  · have h2 := hB.rb_derivatives 2 (by norm_num) le_rfl
    have hnorm2 : (fun x : SpaceTime => ‖fderiv ℝ (fun y => fderiv ℝ (L.rb x.1) y) x.2‖) =
        (fun x : SpaceTime => ‖iteratedFDeriv ℝ 2 ((B n).rb x.1) x.2‖) := by
      funext x
      have ha := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := (B n).rb x.1) (n := 1) (x := x.2)
      have hb := norm_iteratedFDeriv_one (𝕜 := ℝ) (f := fderiv ℝ ((B n).rb x.1)) (x := x.2)
      exact hb.symm.trans ha
    rw [hP_eq, hnorm2]
    exact (phaseLr_le_of_periodSlab_eLpNorm hP_pos _ h2.1 h2.2).trans
      (ENNReal.ofReal_le_ofReal hLR_le)

/-- **Conditional assembly of `BackgroundBridge`** from `ShortBgExactProfile`. -/
theorem backgroundBridge_of (hPr : ShortBgExactProfile) : BackgroundBridge := by
  intro R hR b m0 C0 k0 m C N dm dp Sig hSig hb0 hm hmm0 hm0b hC0 hCC hN hdm hdmlt hdpgt
    K hKb hKm0 hKC0 hKk0 hc htr hsm κ B hB
  let D := seqOf R hc K Sig hSig htr hsm κ B
  obtain ⟨hνpos, hνlim, hεpos, hlim⟩ := Spine.parameterAsymptotics R hR
  have hν1 : ∀ᶠ n : ℕ in atTop, Spine.nuSeq R n ≤ 1 :=
    ((tendsto_order.1 hνlim).2 1 one_pos).mono fun n hn => hn.le
  have hloss : ∀ᶠ n : ℕ in atTop, Spine.lossExponent R n ∈ Icc dm dp :=
    hlim.eventually (Icc_mem_nhds hdmlt hdpgt)
  have hε1 : ∀ᶠ n : ℕ in atTop, Spine.epsSeq R n ≤ 1 := by
    filter_upwards [hloss] with n hl
    have hlog : Real.log (Spine.epsSeq R n) ≤ 0 := by
      have h1 : 0 ≤ -(Spine.nuSeq R n) * Real.log (Spine.epsSeq R n) := le_trans hdm.le hl.1
      nlinarith [hνpos n]
    exact (Real.log_nonpos_iff (hεpos n).le).1 hlog
  have hm_ball : 2 * m < 3 * dm / 11 := by linarith
  have hPr' := hPr R hR m dm dp C Sig N hm hdm hm_ball hdmlt hdpgt hSig B hB
  refine ⟨?_, ?_, ⟨max C 0, N, ?_⟩⟩
  · -- 1. `actual : ∀ᶠ n, D.IsActualLevel dm dp n`
    filter_upwards [hB, hν1, hε1, hloss, hPr'] with n hBn hν1n hε1n hln hPrn
    have hC : 0 ≤ C := nonneg_C_of_isShort (hνpos n) (hεpos n) hBn
    have h2LR : 2 * Spine.lossRadius (Spine.nuSeq R n) (Spine.epsSeq R n) m C N ≤
        (D.level n).ρb R.planar K := by
      show 2 * Spine.lossRadius (Spine.nuSeq R n) (Spine.epsSeq R n) m C N ≤
        K.C0 * (((D.level n).params R.planar).ν ^ K.k0)⁻¹ *
          Real.exp (K.m0 / ((D.level n).params R.planar).ν) *
          ((D.level n).params R.planar).ε ^ (3 / 11 : ℝ)
      rw [hKm0, hKC0, hKk0]
      exact two_mul_lossRadius_le (hνpos n) hν1n (hεpos n) hmm0 hC hCC hN
    have hLR0 : 0 ≤ Spine.lossRadius (Spine.nuSeq R n) (Spine.epsSeq R n) m C N :=
      le_trans (norm_nonneg _) (hBn.rb_sup 0 0).1
    have hLR : Spine.lossRadius (Spine.nuSeq R n) (Spine.epsSeq R n) m C N ≤
        (D.level n).ρb R.planar K := by linarith
    have hpres_eq : D.pres n = Classical.choose hPrn := dif_pos hPrn
    obtain ⟨hprof, hpresL2⟩ := Classical.choose_spec hPrn
    refine ⟨?_, exactSplitII_of_isShort hc K Sig hSig htr hsm κ B hε1n hBn h2LR, ?_, ?_,
      isBallSplit_of_isShort hc K Sig hSig htr hsm κ B hBn hLR, D.train_buc n⟩
    · refine ⟨hdm, hln.1, hln.2, ?_, rfl, D.train_buc n, D.train_stream_smooth n⟩
      show Spine.epsSeq R n =
        Real.exp (-(-(Spine.nuSeq R n) * Real.log (Spine.epsSeq R n)) / Spine.nuSeq R n)
      have hne : Spine.nuSeq R n ≠ 0 := (hνpos n).ne'
      have hdiv : -(-(Spine.nuSeq R n) * Real.log (Spine.epsSeq R n)) / Spine.nuSeq R n =
          Real.log (Spine.epsSeq R n) := by
        field_simp
      rw [hdiv, Real.exp_log (hεpos n)]
    · rw [hpres_eq]
      exact hprof
    · intro τ
      rw [hpres_eq]
      exact hpresL2 τ
  · -- 2. `inlet : ∀ᶠ n, D.Sin n ≤ retEps D.Pl D.σ₀ n ^ (-D.K.b)`
    have hbdm : 0 < (b * dm) ^ 2 / (2 * Sig) := by positivity
    have hνsmall : ∀ᶠ n : ℕ in atTop, Spine.nuSeq R n < (b * dm) ^ 2 / (2 * Sig) :=
      (tendsto_order.1 hνlim).2 _ hbdm
    filter_upwards [hloss, hνsmall] with n hln hνsn
    show Sig / (2 * Spine.nuSeq R n) ≤ (Spine.epsSeq R n) ^ (-K.b)
    rw [hKb]
    set ν := Spine.nuSeq R n
    set ε := Spine.epsSeq R n
    have hν : 0 < ν := hνpos n
    have hε : 0 < ε := hεpos n
    have hlog : b * dm / ν ≤ Real.log (ε ^ (-b)) := by
      rw [Real.log_rpow hε]
      have h1 : dm ≤ -ν * Real.log ε := hln.1
      have h2 : b * dm ≤ b * (-ν * Real.log ε) := mul_le_mul_of_nonneg_left h1 hb0.le
      rw [div_le_iff₀ hν]
      linarith
    have hexp_le : Real.exp (b * dm / ν) ≤ ε ^ (-b) := by
      rw [← Real.exp_log (Real.rpow_pos_of_pos hε (-b))]
      exact Real.exp_le_exp.2 hlog
    set x := b * dm / ν
    have hx0 : 0 ≤ x := by positivity
    have h1 : x / 2 ≤ Real.exp (x / 2) := by linarith [Real.add_one_le_exp (x / 2)]
    have hx2 : x ^ 2 / 4 ≤ Real.exp x := by
      calc x ^ 2 / 4 = (x / 2) * (x / 2) := by ring
        _ ≤ Real.exp (x / 2) * Real.exp (x / 2) := mul_self_le_mul_self (by positivity) h1
        _ = Real.exp x := by rw [← Real.exp_add]; ring_nf
    have hSin_le : Sig / (2 * ν) ≤ x ^ 2 / 4 := by
      have hle : 2 * Sig * ν ≤ (b * dm) ^ 2 := by
        have := (lt_div_iff₀ (mul_pos two_pos hSig)).1 hνsn
        linarith
      unfold x
      rw [div_pow, div_div, div_le_div_iff₀ (mul_pos two_pos hν) (mul_pos (pow_pos hν 2) four_pos)]
      calc Sig * (ν ^ 2 * 4) = (2 * Sig * ν) * (2 * ν) := by ring
        _ ≤ (b * dm) ^ 2 * (2 * ν) := mul_le_mul_of_nonneg_right hle (by positivity)
    exact (hSin_le.trans hx2).trans hexp_le
  · -- 3. `repairDeriv : ∀ᶠ n, RepairDerivBound D.K (D.level n) (max C 0) N`
    filter_upwards [hB] with n hBn
    exact repairDeriv_of_isShort hc K Sig hSig htr hsm κ B (hKm0 ▸ hmm0) hBn

end UnforcedLeray.Short.PartIIIb.Concrete.Wiring
