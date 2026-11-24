import UnforcedLeray.Short.PartIIIb.Proofs.Wiring.Inputs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.WardAffine
import UnforcedLeray.Short.PartIIIb.Concrete.Standing.Affine
import UnforcedLeray.Short.PartIIIb.Concrete.Standing.Adapters
import UnforcedLeray.Short.PartIIIb.Concrete.Standing.Near
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.EACoefBound
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Inverses.Proofs.WeakToFreeResponse
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Inverses.Proofs.SrcLiftYr
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.TepsWeakSol
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Proofs.MultPin
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.XmtSmooth
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.XmtSolenoidal
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.XmtLinear
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.FrakTLinear
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_2_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_2_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_2_2_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_2_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_2_3_1.DatumNorm
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_2_3_1.KcEmbed
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_2_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_2.AxiU
import UnforcedLeray.Short.PartI.Tasks.OverlapHighNorm
import UnforcedLeray.Short.PartI.Tasks.OverlapFluctuationDecay
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanPrimitive
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanDecay
import UnforcedLeray.Short.PartI.Tasks.TrainOverlapProof
import UnforcedLeray.Short.PartI.Tasks.TrainL2DecayProof

/-!
# `PartIII-b:IIIb-D5/3` — `WardAffineSeq` reduction to `IIIa.CTKineticImpulse`

Source: `the November 2 reference manuscript` lines 4300-4303, 5001-5008,
5796-5814.

Proves:
* `trainL2Decay_unconditional : PartI.TrainL2Decay` (from `PartI:T12..T16`);
* `tfkShortAll : 8 < m → TFKShortAll m` unconditionally (from `FI.ev.locBdd` on the bounded
  interval `[11/10/ν, coreEnd ν b]` and `tfkKcEmbed` at `a = 1`);
* `tfkLongAll_of : 8 < m → (∃ P, IsPlanarReference P) → IIIa.CTKineticImpulse → TFKLongAll m`
  (from `IIIa.CTKineticImpulse` and `IIIa.CTE.biotSavart_exists_uniform`);
* `frakTN0Bound_of : TrainOldStressBound m → FrakTN0Bound as χf m` (from `affMEnvelope`,
  `bmatBound`, `duhGBD_norm_le`, and the old-region slice comparison);
* `wardAffineSeq_of_kflat` (using `pf2b_axiU` for `AxiNoSwirlPt`, without `IIb.StrongRegularity`);
* `wardAffineSeq_of : IIIa.CTKineticImpulse → Wiring.WardAffineSeq`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData IsPlanarReference)
open ConcreteYF FlatSettingInst

/-! ## 1. Unconditional `PartI.TrainL2Decay` and `TFKShortAll` -/

/-- Unconditional assembly of `PartI.TrainL2Decay` (`PartI:T17`) from `PartI:T12..T16`. -/
theorem trainL2Decay_unconditional : UnforcedLeray.Short.PartI.TrainL2Decay := by
  have hHN : UnforcedLeray.Short.PartI.OverlapHighNormUniform :=
    UnforcedLeray.Short.PartI.overlap_highnorm_uniform
  have hFD : UnforcedLeray.Short.PartI.OverlapFluctuationDecay :=
    UnforcedLeray.Short.PartI.overlap_fluctuation_decay hHN
  have hMP : UnforcedLeray.Short.PartI.OverlapMeanPrimitive :=
    UnforcedLeray.Short.PartI.overlap_mean_primitive
  have hMD : UnforcedLeray.Short.PartI.OverlapMeanDecay :=
    UnforcedLeray.Short.PartI.overlap_mean_decay hHN hFD hMP
  exact UnforcedLeray.Short.PartI.trainL2Decay_proof
    (UnforcedLeray.Short.PartI.trainOverlap_proof hFD hMD)

/-- Unconditional proof of `TFKShortAll m`: at each fixed `ν ∈ (0, 1]`,
`[11/10/ν, coreEnd ν b]` is bounded so `FI.ev.locBdd` bounds `‖FI.ev.U u (11/10/ν)‖`, and
`tfkKcEmbed m` at `a = 1` bounds `‖kcLp‖` by `K * ‖·‖`. -/
theorem tfkShortAll (m : ℝ) [Fact (1 < m)] : TFKShortAll m := by
  intro h8
  have hm0 : 0 ≤ m := by linarith
  refine ⟨1, fun b _hb => ⟨1, one_pos, ?_⟩⟩
  intro κ ν hν hν1 tr hbuc FI
  have : Fact (0 < cOf ν) := ⟨UnforcedLeray.Short.PartIIIb.Concrete.cOf_pos hν⟩
  have hcOf : cOf ν = ν ^ (-2 : ℝ) := by
    rw [cOf, Real.rpow_neg hν.le, Real.rpow_two]
  have key : ∀ (c : ℝ) (hc : c = ν ^ (-2 : ℝ)) [Fact (0 < c)]
      (tr : UnforcedLeray.B0140.TrainSol ν c) (_ : UnforcedLeray.Short.PartI.IsBUCTrain tr)
      (FI' : FlatInstData κ ν c m tr),
      ∃ C : ℝ, ∀ u : ℝ,
        11 / 10 / ν ≤ u → u ≤ UnforcedLeray.Short.IIIa.coreEnd ν b →
          ∀ w : Xmc c m, ‖kcLp (FI'.ev.U u (11 / 10 / ν) w)‖ ≤ C * ‖w‖ := by
    intro c hc _ tr _ FI'
    subst hc
    obtain ⟨K, hK0, hK⟩ := tfkKcEmbed m h8 ν hν hν1 _ rfl
    set t0 : ℝ := 11 / 10 / ν
    have ht0nn : 0 ≤ t0 := by positivity
    set T_end : ℝ := max (UnforcedLeray.Short.IIIa.coreEnd ν b) t0
    obtain ⟨C_loc, hC_loc⟩ := FI'.ev.locBdd T_end
    refine ⟨K * max C_loc 0, fun u hu1 hu2 w => ?_⟩
    have haν : (1 : ℝ) ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
    set ξ : Xmc (ν ^ (-2 : ℝ)) m := FI'.ev.U u t0 w
    have hkc := hK 1 le_rfl haν ξ
    have hxn := UnforcedLeray.Short.IIIa.xNorm_JscaleInv_le (ν ^ (-2 : ℝ)) m 1 hm0 le_rfl
      (xFn ξ) (xFn_memLp ξ)
    rw [xNorm_xFn_eq, Real.one_rpow, ENNReal.ofReal_one, one_mul] at hxn
    have hkc' : ENNReal.ofReal ‖kcLp ξ‖ ≤ ENNReal.ofReal (K * ‖ξ‖) := by
      rw [ENNReal.ofReal_mul hK0]
      exact hkc.trans (mul_le_mul_of_nonneg_left hxn bot_le)
    have hkc_real : ‖kcLp ξ‖ ≤ K * ‖ξ‖ :=
      (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hK0 (norm_nonneg _))).1 hkc'
    have hu_end : u ≤ T_end := hu2.trans (le_max_left _ _)
    have hU : ‖FI'.ev.U u t0‖ ≤ max C_loc 0 :=
      (hC_loc u t0 ht0nn hu1 hu_end).trans (le_max_left _ _)
    have hξ : ‖ξ‖ ≤ max C_loc 0 * ‖w‖ :=
      ((FI'.ev.U u t0).le_opNorm w).trans (mul_le_mul_of_nonneg_right hU (norm_nonneg w))
    calc ‖kcLp ξ‖ ≤ K * ‖ξ‖ := hkc_real
      _ ≤ K * (max C_loc 0 * ‖w‖) := mul_le_mul_of_nonneg_left hξ hK0
      _ = K * max C_loc 0 * ‖w‖ := by ring
  exact key (cOf ν) hcOf tr hbuc FI

/-! ## 2. `TFKLongAll` from `IIIa.CTKineticImpulse` -/

private def reProj {c m : ℝ} [Fact (1 < m)] (x : Xmc c m) : Xmc c m :=
  ((2 : ℂ)⁻¹) • (x + conjX x)

private theorem conjX_reProj {c m : ℝ} [Fact (1 < m)] (x : Xmc c m) :
    conjX (reProj x) = reProj x := by
  unfold reProj
  rw [conjX_smul, conjX_add, conjX_conjX, add_comm]
  have h2 : (starRingEnd ℂ) (2 : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by
    rw [map_inv₀, map_ofNat]
  rw [h2]

private theorem norm_reProj_le {c m : ℝ} [Fact (1 < m)] (x : Xmc c m) :
    ‖reProj x‖ ≤ ‖x‖ := by
  unfold reProj
  rw [norm_smul, norm_inv, Complex.norm_ofNat]
  have h1 := norm_add_le x (conjX x)
  rw [norm_conjX] at h1
  linarith

private theorem reProj_comm_U {ν c m : ℝ} [Fact (1 < m)]
    {tr : UnforcedLeray.B0140.TrainSol ν c} (ev : TrainEvolution m tr)
    (s t : ℝ) (x : Xmc c m) :
    ev.U s t (reProj x) = reProj (ev.U s t x) := by
  unfold reProj
  rw [map_smul, map_add, ev.real]

private theorem reX_reProj {c m : ℝ} [Fact (1 < m)] (x : Xmc c m) :
    reX (reProj x).1 = reX x.1 := by
  refine Lp.ext ?_
  have hsmul : ((reProj x).1 : ℝ × ℝ → ℂ) =ᵐ[B0579.cellMeasure c m]
      fun p => (2 : ℂ)⁻¹ * ((x.1 : ℝ × ℝ → ℂ) p + (conjAmb x.1 : ℝ × ℝ → ℂ) p) := by
    change (((2 : ℂ)⁻¹ • (x.1 + conjAmb x.1) : XAmb c m) : ℝ × ℝ → ℂ) =ᵐ[B0579.cellMeasure c m] _
    filter_upwards [Lp.coeFn_smul (2 : ℂ)⁻¹ (x.1 + conjAmb x.1),
      Lp.coeFn_add x.1 (conjAmb x.1)] with p hp1 hp2
    rw [hp1, Pi.smul_apply, hp2, Pi.add_apply, smul_eq_mul]
  filter_upwards [coeFn_reX (reProj x).1, coeFn_reX x.1, hsmul, coeFn_conjAmb x.1] with
    p hp1 hp2 hp3 hp4
  rw [hp1, hp2, hp3, hp4]
  simp [Complex.mul_re]
  ring

private theorem kcLp_reProj {c m : ℝ} [Fact (1 < m)] [Fact (0 < c)] (x : Xmc c m) :
    kcLp (reProj x) = kcLp x := by
  unfold kcLp
  congr 1
  exact reX_reProj x

private theorem jscale_jscaleInv_eq {a : ℝ} (ha : 0 < a) (g : ℝ × ℝ → ℂ) :
    IIIa.Jscale a (IIIa.JscaleInv a g) = g := by
  ext ⟨x1, x2⟩
  unfold IIIa.Jscale IIIa.JscaleInv
  have hsq : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have ha_pow : a ^ (-2 : ℝ) * a ^ 2 = 1 := by
    rw [Real.rpow_neg ha.le, Real.rpow_two, inv_mul_cancel₀ (pow_ne_zero 2 ha.ne')]
  rw [← mul_assoc, ← Complex.ofReal_mul, ha_pow, Complex.ofReal_one, one_mul]
  congr 1
  ext <;> simp [mul_div_cancel₀ _ hsq]

private theorem isLinearisedFlow_congr_initial {ν c m t : ℝ}
    {tr : UnforcedLeray.B0140.TrainSol ν c} {f f' : ℝ × ℝ → ℂ}
    {ω : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (h : IIIa.IsLinearisedFlow ν c m tr t f ω u)
    (hf : f =ᵐ[volume.restrict (B0579.cell c)] f') :
    IIIa.IsLinearisedFlow ν c m tr t f' ω u where
  initial := h.initial.trans hf
  memX := h.memX
  strongCont := h.strongCont
  biotSavart := h.biotSavart
  integrable := h.integrable
  timeIntegrable := h.timeIntegrable
  weak φ hφ s hs := by
    rw [h.weak φ hφ s hs]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hf] with x hx
    rw [hx]

private theorem clockAge_eq_coreEnd {ν r : ℝ} (hν : 0 < ν) (hr : 0 < r) :
    IIIa.clockAge ν r = IIIa.coreEnd ν r := by
  have hνne : ν ≠ 0 := hν.ne'
  have hrne : r ≠ 0 := hr.ne'
  unfold IIIa.clockAge IIIa.coreEnd
  field_simp

private theorem clockAge_clockTheta {ν s : ℝ} (hν : 0 < ν) (hs : 0 ≤ s) :
    IIIa.clockAge ν (IIIa.clockTheta ν s) = s := by
  have hνne : ν ≠ 0 := hν.ne'
  have ha : 0 < 1 + ν * s := by nlinarith
  have hane : 1 + ν * s ≠ 0 := ha.ne'
  unfold IIIa.clockAge IIIa.clockTheta IIIa.clockA
  field_simp
  ring

private theorem inv_nu_mul_clockTheta {ν s : ℝ} (hν : 0 < ν) :
    (ν * IIIa.clockTheta ν s)⁻¹ = IIIa.clockA ν s := by
  have hνne : ν ≠ 0 := hν.ne'
  unfold IIIa.clockTheta
  field_simp

private theorem clockA_coreEnd {ν r : ℝ} (hν : 0 < ν) :
    IIIa.clockA ν (IIIa.coreEnd ν r) = (ν * r)⁻¹ := by
  have hνne : ν ≠ 0 := hν.ne'
  unfold IIIa.clockA IIIa.coreEnd
  field_simp
  ring

private theorem clockTheta_coreEnd {ν r : ℝ} (hν : 0 < ν) (hr : 0 < r) :
    IIIa.clockTheta ν (IIIa.coreEnd ν r) = r := by
  have hνne : ν ≠ 0 := hν.ne'
  have hrne : r ≠ 0 := hr.ne'
  unfold IIIa.clockTheta
  rw [clockA_coreEnd hν]
  field_simp

private theorem dOfTheta_eq_cellLen {ν θ : ℝ} (hν : 0 < ν) (hθ : 0 < θ) :
    IIIa.dOfTheta ν θ = IIIa.cellLen (ν ^ (-2 : ℝ)) (ν * θ)⁻¹ := by
  unfold IIIa.dOfTheta IIIa.cellLen
  have hνne : ν ≠ 0 := hν.ne'
  have hθne : θ ≠ 0 := hθ.ne'
  have h1 : ν ^ (-2 : ℝ) = Real.sqrt ((ν ^ 4)⁻¹) := by
    have hsq : ((ν ^ 2)⁻¹) ^ 2 = (ν ^ 4)⁻¹ := by ring
    rw [Real.rpow_neg hν.le, Real.rpow_two, ← hsq, Real.sqrt_sq (by positivity)]
  rw [h1, ← Real.sqrt_div (by positivity)]
  congr 1
  field_simp

private theorem kcLp_mul_clockA_le_kinNorm {c m : ℝ} [Fact (1 < m)] [Fact (0 < c)]
    {a : ℝ} (ha : 0 < a) {ξ : Xmc c m} (hreal : conjX ξ = ξ) :
    ENNReal.ofReal a * ENNReal.ofReal ‖kcLp ξ‖ ≤
      IIIa.kinNorm (IIIa.cellLen c a) (IIIa.JscaleInv a (xFn ξ)) := by
  have hc : 0 < c := Fact.out
  have hd : 0 < IIIa.cellLen c a := div_pos hc (Real.sqrt_pos.2 ha)
  have hbs0 : IIIa.IsBiotSavart c (xFn ξ) (kcC ξ) := isBiotSavart_kc hreal
  have hx_re : xFn ξ =ᵐ[volume.restrict (B0579.cell c)]
      fun x => (((xFn ξ x).re : ℝ) : ℂ) := by
    filter_upwards [xFn_of_real hreal, ae_cell_of_ae_cellMeasure (coeFn_reX ξ.1)] with x h1 h2
    have h2' : reX ξ.1 x = (xFn ξ x).re := h2
    exact h1.trans (by rw [h2'])
  have hbs_re : IIIa.IsBiotSavart c (fun x => (((xFn ξ x).re : ℝ) : ℂ)) (kcC ξ) :=
    isBiotSavart_congr_ae hbs0 hx_re
  have hkc_le : ENNReal.ofReal ‖kcLp ξ‖ ≤ IIIa.velNorm c (kcC ξ) :=
    kcLp_norm_le_velNorm ξ (kcC ξ) hbs_re
  have hbs_a := isBiotSavart_jscaleInv c a hc ha (xFn ξ) (kcC ξ) hbs0
  have hvel_a := IIIa.velNorm_scale c a hc ha (kcC ξ)
  refine (mul_le_mul_of_nonneg_left hkc_le bot_le).trans (hvel_a.symm.le.trans ?_)
  refine le_iInf₂ fun v hv => ?_
  have hae := IIIa.CTE.isBiotSavart_unique (IIIa.cellLen c a) hd
    (IIIa.JscaleInv a (xFn ξ)) _ v hbs_a hv
  unfold IIIa.velNorm
  refine le_of_eq ?_
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  exact eLpNorm_congr_ae (hae.mono fun x hx => congr_fun hx j)

private theorem exists_kinNorm_reSym_le (m : ℝ) [Fact (1 < m)] (hm8 : 8 < m) :
    ∃ K₁ : ℝ, 0 ≤ K₁ ∧ ∀ {ν c a : ℝ} [Fact (0 < c)],
      0 < ν → ν ≤ 1 → c = ν ^ (-2 : ℝ) → 1 ≤ a → a ≤ ν⁻¹ →
      ∀ ξ : Xmc c m,
        MemLp (IIIa.JscaleInv a (reSym ξ)) 2 (B0579.cellMeasure (IIIa.cellLen c a) m) ∧
        IIIa.HasZeroCirculation (IIIa.cellLen c a) (IIIa.JscaleInv a (reSym ξ)) ∧
        IIIa.IsCentrallyEven (IIIa.JscaleInv a (reSym ξ)) ∧
        IIIa.kinNorm (IIIa.cellLen c a) (IIIa.JscaleInv a (reSym ξ)) ≤
          ENNReal.ofReal K₁ * IIIa.xNorm (IIIa.cellLen c a) m (IIIa.JscaleInv a (xFn ξ)) := by
  obtain ⟨C2, hC2⟩ := IIIa.CTE.biotSavart_exists_uniform m hm8
  refine ⟨max C2 0, le_max_right C2 0, fun {ν c a} _ hν hν1 hc ha1 haν ξ => ?_⟩
  have hc0 : 0 < c := Fact.out
  have ha0 : 0 < a := one_pos.trans_le ha1
  have hd1 : 1 ≤ IIIa.cellLen c a := one_le_cellLen_short hν hν1 hc ha1 haν
  have h1 := reSym_ae ξ
  have h2 := rePart_zeroCirc_aux ξ
  have hgz : IIIa.HasZeroCirculation c (reSym ξ) :=
    ⟨h2.1.congr h1.symm, by rw [integral_congr_ae h1]; exact h2.2⟩
  have hge : IIIa.IsCentrallyEven (reSym ξ) := reSym_even ξ
  obtain ⟨hGe, hGz⟩ := jscaleInv_even_zeroCirc c a hc0 ha0 (reSym ξ) hge hgz
  obtain ⟨hMr, hNr⟩ := jscaleInv_rePart_memLp_le a ha1 ξ
  have hGr := jscaleInv_ae_cellMeasure c a m ha0 h1
  have hGM : MemLp (IIIa.JscaleInv a (reSym ξ)) 2 (B0579.cellMeasure (IIIa.cellLen c a) m) :=
    hMr.ae_eq hGr.symm
  obtain ⟨u_b, hu_b, hv_b⟩ :=
    hC2 (IIIa.cellLen c a) hd1 (IIIa.JscaleInv a (reSym ξ)) hGM hGz hGe
  have hxn : IIIa.xNorm (IIIa.cellLen c a) m (IIIa.JscaleInv a (reSym ξ)) =
      IIIa.xNorm (IIIa.cellLen c a) m
        (IIIa.JscaleInv a (fun x => (((xFn ξ x).re : ℝ) : ℂ))) :=
    eLpNorm_congr_ae hGr
  refine ⟨hGM, hGz, hGe, ?_⟩
  calc IIIa.kinNorm (IIIa.cellLen c a) (IIIa.JscaleInv a (reSym ξ))
      ≤ IIIa.velNorm (IIIa.cellLen c a) u_b := iInf₂_le u_b hu_b
    _ ≤ ENNReal.ofReal C2 *
          IIIa.xNorm (IIIa.cellLen c a) m (IIIa.JscaleInv a (reSym ξ)) := hv_b
    _ ≤ ENNReal.ofReal (max C2 0) *
          IIIa.xNorm (IIIa.cellLen c a) m (IIIa.JscaleInv a (xFn ξ)) := by
        rw [hxn]
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) hNr

/-- `TFKLongAll m` from `IIIa.CTKineticImpulse` (`PartIII-a:T22`, source 3242-3251, 4449-4455). -/
theorem tfkLongAll_of (m : ℝ) [Fact (1 < m)]
    (hP : ∃ P, IsPlanarReference P)
    (hKI : UnforcedLeray.Short.IIIa.CTKineticImpulse) :
    TFKLongAll m := by
  intro h8
  have hm0 : 0 ≤ m := by linarith
  obtain ⟨P, hPref⟩ := hP
  obtain ⟨b₂, hb₂⟩ := hKI P hPref m h8
  obtain ⟨K₁, hK₁, hK_kin⟩ := exists_kinNorm_reSym_le m h8
  refine ⟨max b₂ 1, fun b hb => ?_⟩
  have hb1 : 1 ≤ b := (le_max_right b₂ 1).trans hb
  have hbpos : 0 < b := lt_of_lt_of_le one_pos hb1
  obtain ⟨C_KI, ν₂, hν₂, hC_KI⟩ := hb₂ b ((le_max_left b₂ 1).trans hb)
  set ν₀ : ℝ := min ν₂ ((3 * b)⁻¹)
  have hν₀ : 0 < ν₀ := lt_min hν₂ (inv_pos.2 (by positivity))
  refine ⟨ν₀, hν₀, ?_⟩
  intro κ ν hν hle tr hbuc FI
  have : Fact (0 < cOf ν) := ⟨UnforcedLeray.Short.PartIIIb.Concrete.cOf_pos hν⟩
  have hνa2 : ν ≤ ν₂ := hle.trans (min_le_left _ _)
  have hν3b : ν ≤ (3 * b)⁻¹ := hle.trans (min_le_right _ _)
  have hν1 : ν ≤ 1 := hν3b.trans ((inv_le_one₀ (by positivity)).2 (by linarith))
  have hcOf : cOf ν = ν ^ (-2 : ℝ) := by
    rw [cOf, Real.rpow_neg hν.le, Real.rpow_two]
  have key : ∀ (c : ℝ) (hc : c = ν ^ (-2 : ℝ)) [Fact (0 < c)]
      (tr : UnforcedLeray.B0140.TrainSol ν c) (_ : UnforcedLeray.Short.PartI.IsBUCTrain tr)
      (FI' : FlatInstData κ ν c m tr),
      ∃ C : ℝ, ∀ u : ℝ, 11 / 10 / ν ≤ u →
        IIIa.coreEnd ν b ≤ u →
          ∀ w' : Xmc c m, ‖kcLp (FI'.ev.U u (11 / 10 / ν) w')‖ ≤ C * ‖w'‖ := by
    intro c hc _ tr hbuc FI'
    subst hc
    have hKI_inst := hC_KI ν ⟨hν, hνa2⟩ tr hbuc
    set s₀ : ℝ := 11 / 10 / ν
    set s_b : ℝ := IIIa.coreEnd ν b
    have hs₀_nonneg : 0 ≤ s₀ := by positivity
    have h3_le : 3 ≤ (ν * b)⁻¹ := by
      have h1 := mul_le_mul_of_nonneg_right hν3b (by positivity : (0 : ℝ) ≤ 3 * b)
      rw [inv_mul_cancel₀ (by positivity)] at h1
      rw [le_inv_comm₀ (by positivity : (0 : ℝ) < 3) (mul_pos hν hbpos)]
      linarith
    have hs_b_lo : s₀ ≤ s_b := by
      unfold s₀ s_b IIIa.coreEnd
      rw [div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 hν.le)
    have hs_b_nonneg : 0 ≤ s_b := hs₀_nonneg.trans hs_b_lo
    set a_b : ℝ := (ν * b)⁻¹
    have ha_b_eq : IIIa.clockA ν s_b = a_b := clockA_coreEnd hν
    have ha_b1 : 1 ≤ a_b := by linarith
    have ha_b0 : 0 < a_b := one_pos.trans_le ha_b1
    have ha_b_le : a_b ≤ ν⁻¹ := inv_anti₀ hν (by nlinarith)
    have hθ_b_eq : IIIa.clockTheta ν s_b = b := clockTheta_coreEnd hν hbpos
    set D_b : ℝ := a_b ^ ((3 : ℝ) / 2)
    have hDb0 : 0 ≤ D_b := Real.rpow_nonneg ha_b0.le _
    set U_b : ℝ := ‖FI'.ev.U s_b s₀‖
    have hUb0 : 0 ≤ U_b := norm_nonneg (FI'.ev.U s_b s₀)
    refine ⟨max C_KI 0 * b * ν * K₁ * D_b * U_b, fun u _hu_lo hs_hi w' => ?_⟩
    have hs_nonneg : 0 ≤ u := hs_b_nonneg.trans hs_hi
    set w_re : Xmc (ν ^ (-2 : ℝ)) m := reProj w'
    set x_b : Xmc (ν ^ (-2 : ℝ)) m := FI'.ev.U s_b s₀ w_re
    set x_s : Xmc (ν ^ (-2 : ℝ)) m := FI'.ev.U u s₀ w_re
    have hkc_eq : kcLp (FI'.ev.U u s₀ w') = kcLp x_s := by
      change kcLp (FI'.ev.U u s₀ w') = kcLp (FI'.ev.U u s₀ (reProj w'))
      rw [reProj_comm_U, kcLp_reProj]
    have hreal_b : conjX x_b = x_b := by
      change conjX (FI'.ev.U s_b s₀ (reProj w')) = FI'.ev.U s_b s₀ (reProj w')
      rw [reProj_comm_U, conjX_reProj]
    have hreal_s : conjX x_s = x_s := by
      change conjX (FI'.ev.U u s₀ (reProj w')) = FI'.ev.U u s₀ (reProj w')
      rw [reProj_comm_U, conjX_reProj]
    have hcocycle : x_s = FI'.ev.U u s_b x_b := by
      have hc := FI'.ev.cocycle u s_b s₀ hs₀_nonneg hs_b_lo hs_hi
      exact (congr_arg (fun L => L w_re) hc).symm
    obtain ⟨hGM, hGz, hGe, hkin_b⟩ := hK_kin hν hν1 rfl ha_b1 ha_b_le x_b
    have hxb_scale : IIIa.xNorm (IIIa.cellLen (ν ^ (-2 : ℝ)) a_b) m
        (IIIa.JscaleInv a_b (xFn x_b)) ≤
        ENNReal.ofReal D_b * ENNReal.ofReal ‖x_b‖ := by
      have h := IIIa.xNorm_JscaleInv_le (ν ^ (-2 : ℝ)) m a_b hm0 ha_b1
        (xFn x_b) (xFn_memLp x_b)
      rwa [xNorm_xFn_eq] at h
    set h_b : ℝ × ℝ → ℂ := IIIa.JscaleInv a_b (reSym x_b)
    have hd_b_eq : IIIa.dOfTheta ν b = IIIa.cellLen (ν ^ (-2 : ℝ)) a_b :=
      dOfTheta_eq_cellLen hν hbpos
    set θ : ℝ := IIIa.clockTheta ν u
    have hθ_pos : 0 < θ := IIIa.theta_pos hν hs_nonneg
    have hθ_le_b : θ ≤ b := by
      rw [← hθ_b_eq]
      unfold θ IIIa.clockTheta
      refine inv_anti₀ (mul_pos hν (IIIa.one_le_clockA hν.le hs_b_nonneg |>.trans_lt' one_pos)) ?_
      refine mul_le_mul_of_nonneg_left ?_ hν.le
      unfold IIIa.clockA
      linarith [mul_le_mul_of_nonneg_left hs_hi hν.le]
    set a_s : ℝ := IIIa.clockA ν u
    have ha_s_pos : 0 < a_s := one_pos.trans_le (IIIa.one_le_clockA hν.le hs_nonneg)
    have ha_s_eq : (ν * θ)⁻¹ = a_s := inv_nu_mul_clockTheta hν
    have hd_s_eq : IIIa.dOfTheta ν θ = IIIa.cellLen (ν ^ (-2 : ℝ)) a_s := by
      rw [dOfTheta_eq_cellLen hν hθ_pos, ha_s_eq]
    set Zh : ℝ × ℝ → ℂ := IIIa.JscaleInv (ν * θ)⁻¹ (xFn x_s)
    have hHeat : IIIa.HeatEvolvesTo ν m tr b θ h_b Zh := by
      obtain ⟨u_b, hu_b⟩ := FI'.ev.flow s_b hs_b_nonneg x_b
      have hx_b_re : xFn x_b =ᵐ[volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))] reSym x_b := by
        have h1 : xFn x_b =ᵐ[volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))]
            fun x => (((xFn x_b x).re : ℝ) : ℂ) := by
          filter_upwards [xFn_of_real hreal_b, ae_cell_of_ae_cellMeasure (coeFn_reX x_b.1)] with
            x hx1 hx2
          have hx2' : reX x_b.1 x = (xFn x_b x).re := hx2
          exact hx1.trans (by rw [hx2'])
        exact h1.trans (reSym_ae x_b).symm
      have hj_eq : IIIa.Jscale (ν * b)⁻¹ h_b = reSym x_b :=
        jscale_jscaleInv_eq ha_b0 (reSym x_b)
      have hu_b' : IIIa.IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr (IIIa.clockAge ν b)
          (IIIa.Jscale (ν * b)⁻¹ h_b) (fun t => xFn (FI'.ev.U t s_b x_b)) u_b := by
        rw [clockAge_eq_coreEnd hν hbpos, hj_eq]
        exact isLinearisedFlow_congr_initial hu_b hx_b_re
      refine ⟨fun t => xFn (FI'.ev.U t s_b x_b), u_b, hu_b', ?_⟩
      dsimp only
      rw [clockAge_clockTheta hν hs_nonneg, ← hcocycle]
    have hGM' : MemLp h_b 2 (B0579.cellMeasure (IIIa.dOfTheta ν b) m) := by
      rwa [hd_b_eq]
    have hGz' : IIIa.HasZeroCirculation (IIIa.dOfTheta ν b) h_b := by
      rwa [hd_b_eq]
    have hKI1 := hKI_inst b θ hθ_pos hθ_le_b le_rfl h_b Zh hGM' hGz' hGe hHeat
    have hkin_s : ENNReal.ofReal a_s * ENNReal.ofReal ‖kcLp x_s‖ ≤
        IIIa.kinNorm (IIIa.dOfTheta ν θ) Zh := by
      rw [hd_s_eq]
      change ENNReal.ofReal a_s * ENNReal.ofReal ‖kcLp x_s‖ ≤
        IIIa.kinNorm (IIIa.cellLen (ν ^ (-2 : ℝ)) a_s)
          (IIIa.JscaleInv (ν * θ)⁻¹ (xFn x_s))
      rw [ha_s_eq]
      exact kcLp_mul_clockA_le_kinNorm ha_s_pos hreal_s
    have hCKI_le : C_KI * (b / θ) ≤ max C_KI 0 * (b / θ) :=
      mul_le_mul_of_nonneg_right (le_max_left C_KI 0) (div_nonneg hbpos.le hθ_pos.le)
    have hcalc : ENNReal.ofReal (a_s * ‖kcLp x_s‖) ≤
        ENNReal.ofReal ((max C_KI 0 * (b / θ)) * (K₁ * (D_b * ‖x_b‖))) := by
      rw [ENNReal.ofReal_mul ha_s_pos.le]
      calc ENNReal.ofReal a_s * ENNReal.ofReal ‖kcLp x_s‖
          ≤ IIIa.kinNorm (IIIa.dOfTheta ν θ) Zh := hkin_s
        _ ≤ ENNReal.ofReal (C_KI * (b / θ)) * IIIa.kinNorm (IIIa.dOfTheta ν b) h_b := hKI1
        _ ≤ ENNReal.ofReal (max C_KI 0 * (b / θ)) *
              (ENNReal.ofReal K₁ *
                IIIa.xNorm (IIIa.cellLen (ν ^ (-2 : ℝ)) a_b) m (IIIa.JscaleInv a_b (xFn x_b))) := by
            rw [hd_b_eq]
            exact mul_le_mul' (ENNReal.ofReal_le_ofReal hCKI_le) hkin_b
        _ ≤ ENNReal.ofReal (max C_KI 0 * (b / θ)) *
              (ENNReal.ofReal K₁ * (ENNReal.ofReal D_b * ENNReal.ofReal ‖x_b‖)) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hxb_scale bot_le) bot_le
        _ = ENNReal.ofReal ((max C_KI 0 * (b / θ)) * (K₁ * (D_b * ‖x_b‖))) := by
            rw [← ENNReal.ofReal_mul hDb0,
              ← ENNReal.ofReal_mul hK₁,
              ← ENNReal.ofReal_mul (mul_nonneg (le_max_right C_KI 0) (div_nonneg hbpos.le hθ_pos.le))]
    have hreal : a_s * ‖kcLp x_s‖ ≤ (max C_KI 0 * (b / θ)) * (K₁ * (D_b * ‖x_b‖)) :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hcalc
    have hb_div_θ : b / θ = b * ν * a_s := by
      unfold θ a_s IIIa.clockTheta
      have hνne : ν ≠ 0 := hν.ne'
      have has_ne : IIIa.clockA ν u ≠ 0 := ha_s_pos.ne'
      field_simp
    have hxb_norm : ‖x_b‖ ≤ U_b * ‖w'‖ := by
      calc ‖FI'.ev.U s_b s₀ w_re‖ ≤ U_b * ‖w_re‖ := (FI'.ev.U s_b s₀).le_opNorm w_re
        _ ≤ U_b * ‖w'‖ := mul_le_mul_of_nonneg_left (norm_reProj_le w') hUb0
    rw [hkc_eq]
    refine le_of_mul_le_mul_left ?_ ha_s_pos
    calc a_s * ‖kcLp x_s‖
        ≤ (max C_KI 0 * (b / θ)) * (K₁ * (D_b * ‖x_b‖)) := hreal
      _ ≤ (max C_KI 0 * (b * ν * a_s)) * (K₁ * (D_b * (U_b * ‖w'‖))) := by
          rw [hb_div_θ]
          refine mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hxb_norm hDb0) hK₁)
            (by positivity)
      _ = a_s * (max C_KI 0 * b * ν * K₁ * D_b * U_b * ‖w'‖) := by ring
  exact key (cOf ν) hcOf tr hbuc FI

/-! ## 3. `FrakTN0Bound` from `TrainOldStressBound` -/

private theorem isAffElem_abs {as : ℝ} {A : ℝ → Mat3} (hA : IsAffElem as A) :
    IsAffElem |as| A ∧ affNorm |as| A ≤ affNorm as A ∧ 0 ≤ affNorm as A := by
  have hle : ∀ s > (0 : ℝ), affTerm |as| 6 A s ≤ affNorm as A := by
    intro s hs
    have hexp : Real.exp (-|as| * s) ≤ Real.exp (-as * s) := by
      apply Real.exp_le_exp.2
      have := le_abs_self as
      nlinarith
    have h1 : affTerm |as| 6 A s ≤ affTerm as 6 A s := by
      unfold affTerm
      refine mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hexp (Real.rpow_nonneg hs.le _))
        (Finset.sum_nonneg fun _ _ => frob_nonneg _)
    exact h1.trans (le_csSup hA.bdd ⟨s, Set.mem_Ioi.2 hs, rfl⟩)
  have hbdd : BddAbove (affTerm |as| 6 A '' Ioi 0) := by
    refine ⟨affNorm as A, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    exact hle s hs
  have hA_abs : IsAffElem |as| A :=
    { smooth := hA.smooth
      traceFree := hA.traceFree
      noMixedAzimuth := hA.noMixedAzimuth
      zeroOff := hA.zeroOff
      bdd := hbdd }
  have hnorm_le : affNorm |as| A ≤ affNorm as A := by
    unfold affNorm
    refine csSup_le ((nonempty_Ioi (a := (0 : ℝ))).image _) ?_
    rintro _ ⟨s, hs, rfl⟩
    exact hle s hs
  have hnorm_nn : 0 ≤ affNorm as A := by
    refine (affTerm_nonneg as 6 A 1 one_pos).trans ?_
    exact le_csSup hA.bdd ⟨1, Set.mem_Ioi.2 one_pos, rfl⟩
  exact ⟨hA_abs, hnorm_le, hnorm_nn⟩

/-- `FrakTN0Bound as χf m` from `TrainOldStressBound m` (`PartIII-b:C/asrc/kflat/3`,
source 4804-4806, 4924-4927, 5091-5108). -/
theorem frakTN0Bound_of (as : ℝ) (χf : ℝ → ℝ) (m : ℝ) [Fact (1 < m)]
    (hD : DuhIntegrableProp as χf m) (hK : KcMerLinearProp m)
    (hX : XiDLateProp m) (hS : TrainOldStressBound m) :
    FrakTN0Bound as χf m := by
  intro hχ hm
  obtain ⟨ν₀, hν₀, hS'⟩ := hS hm
  obtain ⟨C_env, hC_env0, hC_env⟩ := affMEnvelope χf hχ
  refine ⟨min ν₀ 1, lt_min hν₀ one_pos, ?_⟩
  intro κ ν μ ε χo hν hνs hμ0 hμ1 tr htr FI
  have : Fact (0 < cOf ν) := ⟨UnforcedLeray.Short.PartIIIb.Concrete.cOf_pos hν⟩
  have hν1 : ν ≤ 1 := hνs.trans (min_le_right _ _)
  have hν0 : ν ≤ ν₀ := hνs.trans (min_le_left _ _)
  obtain ⟨C_S, hC_S⟩ := hS' κ ν hν hν0 tr htr FI
  set T : ℝ := 11 / 10 / ν with hT
  have hTpos : 0 < T := by positivity
  have hTold : T < 6 / 5 / ν := div_lt_div_of_pos_right (by norm_num) hν
  obtain ⟨C_u, hC_u⟩ := FI.ev.locBdd T
  obtain ⟨h1, hH⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    FI.src.H_cont.continuousOn
  obtain ⟨h2, hR⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    FI.src.R_cont.continuousOn
  have hh1 : 0 ≤ h1 := (norm_nonneg (FI.src.H 0)).trans (hH 0 ⟨le_rfl, hTpos.le⟩)
  have hh2 : 0 ≤ h2 := (norm_nonneg (FI.src.R 0)).trans (hR 0 ⟨le_rfl, hTpos.le⟩)
  set E_env : ℝ := C_env * Real.exp (1.1 * |as| / ν)
  have hE_env0 : 0 ≤ E_env := mul_nonneg hC_env0 (Real.exp_pos _).le
  set C_xi : ℝ := T ^ (-μ) * (T ^ μ * max C_u 0 *
    ((1 + μ) * T ^ (3 / 2 : ℝ) * E_env * (2 * h1 + h2)) * volume.real (Ioc (0 : ℝ) T))
  have hC_xi0 : 0 ≤ C_xi := by positivity
  refine ⟨max C_S 0 * C_xi, fun A hA => ?_⟩
  obtain ⟨hA_abs, hnorm_le, hnorm_nn⟩ := isAffElem_abs hA
  have hM_le : max (affM ν χf A) 0 ≤ E_env * affNorm as A := by
    refine max_le ?_ (mul_nonneg hE_env0 hnorm_nn)
    calc affM ν χf A
        ≤ C_env * Real.exp (1.1 * |as| / ν) * affNorm |as| A :=
          hC_env |as| ν A (abs_nonneg as) hν hA_abs
      _ ≤ E_env * affNorm as A := mul_le_mul_of_nonneg_left hnorm_le hE_env0
  set B := Bmat ν μ χf A with hBdef
  set w := xiD FI (μ : ℂ) B T with hw
  -- Step 1: bound `‖w‖` by `C_xi * affNorm as A`
  have hw_norm : ‖w‖ ≤ C_xi * affNorm as A := by
    have hxi_eq : w = (T : ℂ) ^ (-(μ : ℂ)) •
        ∫ t in Ioc 0 T, ((t : ℂ) ^ (μ : ℂ)) • (FI.ev.U T t) (gBD FI B t) :=
      xiD_apply FI (μ : ℂ) B T
    rw [hxi_eq, norm_smul]
    have hTpow : ‖((T : ℂ) ^ (-(μ : ℂ)))‖ = T ^ (-μ) := by
      rw [← Complex.ofReal_neg, Complex.norm_cpow_eq_rpow_re_of_pos hTpos, Complex.ofReal_re]
    rw [hTpow]
    set K_A : ℝ := (1 + μ) * T ^ (3 / 2 : ℝ) * (E_env * affNorm as A)
    have hKA0 : 0 ≤ K_A := by positivity
    have hInt : ‖∫ t in Ioc 0 T, ((t : ℂ) ^ (μ : ℂ)) • (FI.ev.U T t) (gBD FI B t)‖ ≤
        (T ^ μ * max C_u 0 * (K_A * (2 * h1 + h2))) * volume.real (Ioc 0 T) := by
      refine norm_setIntegral_le_of_norm_le_const (by simp) (fun t ht => ?_)
      have hn := duhGBD_norm_le FI B t
      have hpow : ‖((t : ℂ) ^ (μ : ℂ))‖ ≤ T ^ μ := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos ht.1, Complex.ofReal_re]
        exact Real.rpow_le_rpow ht.1.le ht.2 hμ0
      have hU : ‖FI.ev.U T t‖ ≤ max C_u 0 := (hC_u T t ht.1.le ht.2 le_rfl).trans (le_max_left _ _)
      have hHt : ‖FI.src.H t‖ ≤ h1 := hH t ⟨ht.1.le, ht.2⟩
      have hRt : ‖FI.src.R t‖ ≤ h2 := hR t ⟨ht.1.le, ht.2⟩
      have hfrob : frob (B t) ≤ K_A := by
        have hb := bmatBound as χf hχ ν μ hν hμ0 A hA t ht.1 ht.2
        have htp0 : 0 ≤ t ^ (3 / 2 : ℝ) := Real.rpow_nonneg ht.1.le _
        have hTp0 : 0 ≤ T ^ (3 / 2 : ℝ) := Real.rpow_nonneg hTpos.le _
        have htp : t ^ (3 / 2 : ℝ) ≤ T ^ (3 / 2 : ℝ) := Real.rpow_le_rpow ht.1.le ht.2 (by norm_num)
        calc frob (B t)
            ≤ (1 + μ) * t ^ (3 / 2 : ℝ) * affM ν χf A := hb
          _ ≤ (1 + μ) * t ^ (3 / 2 : ℝ) * max (affM ν χf A) 0 :=
              mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
          _ ≤ (1 + μ) * T ^ (3 / 2 : ℝ) * (E_env * affNorm as A) :=
              mul_le_mul (mul_le_mul_of_nonneg_left htp (by linarith)) hM_le
                (le_max_right _ _) (by positivity)
      have hg : ‖gBD FI B t‖ ≤ K_A * (2 * h1 + h2) :=
        hn.trans (mul_le_mul hfrob (by linarith) (by positivity) hKA0)
      rw [norm_smul]
      have hUg : ‖FI.ev.U T t (gBD FI B t)‖ ≤ max C_u 0 * (K_A * (2 * h1 + h2)) :=
        ((FI.ev.U T t).le_opNorm _).trans
          (mul_le_mul hU hg (norm_nonneg _) (le_max_right _ _))
      calc ‖((t : ℂ) ^ (μ : ℂ))‖ * ‖FI.ev.U T t (gBD FI B t)‖
          ≤ T ^ μ * (max C_u 0 * (K_A * (2 * h1 + h2))) :=
            mul_le_mul hpow hUg (norm_nonneg _) (Real.rpow_nonneg hTpos.le _)
        _ = _ := by ring
    calc T ^ (-μ) * ‖∫ t in Ioc 0 T, ((t : ℂ) ^ (μ : ℂ)) • (FI.ev.U T t) (gBD FI B t)‖
        ≤ T ^ (-μ) * ((T ^ μ * max C_u 0 * (K_A * (2 * h1 + h2))) * volume.real (Ioc 0 T)) :=
          mul_le_mul_of_nonneg_left hInt (Real.rpow_nonneg hTpos.le _)
      _ = C_xi * affNorm as A := by unfold C_xi K_A; ring
  -- Step 2: bound `oldN0` by `max C_S 0 * ‖w‖`
  have hBz : ∀ t, T < t → B t = 0 := fun t ht => (eac_bmat_zero χf hχ ν μ hν A t ht).1
  have hIT := hD hχ κ ν μ hν hν1 hμ0 hμ1 tr FI A hA T
  have hlate : ∀ u, T ≤ u → xiD FI (μ : ℂ) B u =
      ((u : ℂ) ^ (-(μ : ℂ)) * (T : ℂ) ^ (μ : ℂ)) • FI.ev.U u T w :=
    fun u hu => hX κ ν μ hν tr FI B T u hTpos hu hBz hIT
  set M := frakT (levelFlat hν FI χo ε) ν μ χf A
  have hslice : ∀ u ∈ Ioi (6 / 5 / ν),
      ‖u ^ (-(3 / 2 : ℝ)) * ∫ x, frob (M (u, x)) ∂(UnforcedLeray.Cyl.avgμ (cOf ν))‖ₑ ≤
        ∫⁻ x, ENNReal.ofReal (u ^ (-(3 / 2 : ℝ)) *
          frob (UnforcedLeray.Short.IIIa.symOuter (NearInst.trainMer tr (u, x))
            (kcMer (FI.ev.U u (11 / 10 / ν) w) x))) ∂(UnforcedLeray.Cyl.avgμ (cOf ν)) := by
    intro u hu
    have hu0 : 0 < u := lt_trans (by positivity) (Set.mem_Ioi.1 hu)
    have hTu : T ≤ u := (hTold.trans (Set.mem_Ioi.1 hu)).le
    set ρ : ℝ := u ^ (-μ) * T ^ μ with hρdef
    have hρ : (u : ℂ) ^ (-(μ : ℂ)) * (T : ℂ) ^ (μ : ℂ) = ((ρ : ℝ) : ℂ) := by
      rw [hρdef, Complex.ofReal_mul, Complex.ofReal_cpow hu0.le, Complex.ofReal_cpow hTpos.le,
        Complex.ofReal_neg]
    have hρ0 : 0 ≤ ρ := mul_nonneg (Real.rpow_nonneg hu0.le _) (Real.rpow_nonneg hTpos.le _)
    have hρ1 : ρ ≤ 1 := by
      rw [hρdef, Real.rpow_neg hu0.le, inv_mul_le_iff₀ (Real.rpow_pos_of_pos hu0 _), mul_one]
      exact Real.rpow_le_rpow hTpos.le hTu hμ0
    have hxi : xiD FI (μ : ℂ) B u = ((ρ : ℝ) : ℂ) • FI.ev.U u T w := by
      rw [hlate u hTu, hρ]
    have hinner : ‖u ^ (-(3 / 2 : ℝ)) * ∫ x, frob (M (u, x)) ∂(UnforcedLeray.Cyl.avgμ (cOf ν))‖ₑ ≤
        ∫⁻ x, ‖u ^ (-(3 / 2 : ℝ)) * frob (M (u, x))‖ₑ ∂(UnforcedLeray.Cyl.avgμ (cOf ν)) := by
      rw [enorm_mul]
      refine (mul_le_mul_of_nonneg_left (enorm_integral_le_lintegral_enorm _) bot_le).trans_eq ?_
      rw [← lintegral_const_mul' _ _ enorm_ne_top]
      refine lintegral_congr fun x => ?_
      rw [enorm_mul]
    refine hinner.trans (lintegral_mono_ae ?_)
    filter_upwards [(hK ν hν (FI.ev.U u T w) (FI.ev.U u T w) ρ).2] with x hx
    have hx' : kcMer (((ρ : ℝ) : ℂ) • FI.ev.U u T w) x = ρ • kcMer (FI.ev.U u T w) x := hx
    have e1 : M (u, x) =
        UnforcedLeray.Short.IIIa.symOuter (NearInst.trainMer tr (u, x))
          (kcMer (xiD FI (μ : ℂ) (Bmat ν μ χf A) u) x) := rfl
    rw [e1, ← hBdef, hxi, hx', symOuter_smul_right']
    have hpow : 0 < u ^ (-(3 / 2 : ℝ)) := Real.rpow_pos_of_pos hu0 _
    have hfr : 0 ≤ frob (ρ • UnforcedLeray.Short.IIIa.symOuter (NearInst.trainMer tr (u, x))
        (kcMer (FI.ev.U u T w) x)) := Real.sqrt_nonneg _
    rw [Real.enorm_eq_ofReal (mul_nonneg hpow.le hfr)]
    exact ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (kfl12_frob_smul_le hρ0 hρ1 _) hpow.le)
  have hold_enorm : ‖oldN0 (cOf ν) ν M‖ₑ ≤ ENNReal.ofReal (max C_S 0 * ‖w‖) := by
    unfold oldN0
    calc ‖∫ u in Ioi (6 / 5 / ν),
            u ^ (-(3 / 2 : ℝ)) * ∫ x, frob (M (u, x)) ∂(UnforcedLeray.Cyl.avgμ (cOf ν))‖ₑ
        ≤ ∫⁻ u in Ioi (6 / 5 / ν),
            ‖u ^ (-(3 / 2 : ℝ)) * ∫ x, frob (M (u, x)) ∂(UnforcedLeray.Cyl.avgμ (cOf ν))‖ₑ :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ u in Ioi (6 / 5 / ν), ∫⁻ x, ENNReal.ofReal (u ^ (-(3 / 2 : ℝ)) *
            frob (UnforcedLeray.Short.IIIa.symOuter (NearInst.trainMer tr (u, x))
              (kcMer (FI.ev.U u (11 / 10 / ν) w) x))) ∂(UnforcedLeray.Cyl.avgμ (cOf ν)) :=
          setLIntegral_mono' measurableSet_Ioi hslice
      _ ≤ ENNReal.ofReal (C_S * ‖w‖) := hC_S w
      _ ≤ ENNReal.ofReal (max C_S 0 * ‖w‖) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg w))
  have hold_real : oldN0 (cOf ν) ν M ≤ max C_S 0 * ‖w‖ := by
    calc oldN0 (cOf ν) ν M
        ≤ ‖oldN0 (cOf ν) ν M‖ := Real.le_norm_self _
      _ = (‖oldN0 (cOf ν) ν M‖ₑ).toReal := by
          rw [← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _)]
      _ ≤ (ENNReal.ofReal (max C_S 0 * ‖w‖)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hold_enorm
      _ = max C_S 0 * ‖w‖ :=
          ENNReal.toReal_ofReal (mul_nonneg (le_max_right _ _) (norm_nonneg w))
  calc oldN0 (cOf ν) ν M
      ≤ max C_S 0 * ‖w‖ := hold_real
    _ ≤ max C_S 0 * (C_xi * affNorm as A) :=
        mul_le_mul_of_nonneg_left hw_norm (le_max_right _ _)
    _ = max C_S 0 * C_xi * affNorm as A := by ring

/-! ## 4. Assembly of `WardAffineSeq` -/

/-- `TrainOldStressBound 9` from `IIIa.CTKineticImpulse` (given a planar reference). -/
theorem trainOldStressBound_nine_of
    (hP : ∃ P, IsPlanarReference P)
    (hKI : UnforcedLeray.Short.IIIa.CTKineticImpulse) :
    TrainOldStressBound 9 :=
  trainOldStressBound_of 9 (trainEnergyUnif_of trainL2Decay_unconditional) (symOuterSlice 9)
    (trainFlowKinetic_of 9 (tfkShortAll 9)
      (tfkLongAll_of 9 hP hKI))

/-- `FrakTOldFinite` at `m = 9` from `IIIa.CTKineticImpulse` (given a planar reference). -/
theorem frakTOldFinite_nine_of
    (hP : ∃ P, IsPlanarReference P)
    (hKI : UnforcedLeray.Short.IIIa.CTKineticImpulse)
    (as : ℝ) (χf : ℝ → ℝ) :
    FrakTOldFinite as χf 9 :=
  frakTOldFinite_of as χf 9 (frakTMeas as χf 9)
    (frakTIntProp_of as χf 9 (frakTMeas as χf 9) (duhIntegrable as χf 9) (kcMerLinear 9)
      (xiDLate 9) (trainOldStressBound_nine_of hP hKI))

/-- `FrakTN0Bound` at `m = 9` from `IIIa.CTKineticImpulse` (given a planar reference). -/
theorem frakTN0Bound_nine_of
    (hP : ∃ P, IsPlanarReference P)
    (hKI : UnforcedLeray.Short.IIIa.CTKineticImpulse)
    (as : ℝ) (χf : ℝ → ℝ) :
    FrakTN0Bound as χf 9 :=
  frakTN0Bound_of as χf 9 (duhIntegrable as χf 9) (kcMerLinear 9) (xiDLate 9)
    (trainOldStressBound_nine_of hP hKI)

/-- **`WardAffineSeq` from the two `𝔗` old-region bounds** (`FrakTOldFinite` and `FrakTN0Bound` at
`m = 9`, source 4300-4303, 5001-5008, 5796-5814).  Uses `pf2b_axiU` for `AxiNoSwirlPt`, so
`IIb.StrongRegularity` is not needed. -/
theorem wardAffineSeq_of_kflat
    (hOld : ∀ (as : ℝ) (χf : ℝ → ℝ), FrakTOldFinite as χf 9)
    (hN0 : ∀ (as : ℝ) (χf : ℝ → ℝ), FrakTN0Bound as χf 9) :
    Wiring.WardAffineSeq := by
  intro D dm dp hst ⟨κ, hflat⟩
  have has0 : 0 ≤ D.K.as := hst.as_pos.le
  have hmZ0 : 0 ≤ D.K.mZ := by linarith [hst.mZ_gt]
  have hlarge := inv_seq_large D hst.dm_pos hst.omega_ne hst.sigma_pos hst.sigma_lt hst.actual
  have hmu := NearInst.eventually_mu_mem D hst.omega_ne hst.sigma_pos hst.sigma_lt
  have haMu := D.eventually_exists_aMuOp hst.omega_ne hst.sigma_pos hst.sigma_lt has0
  have hKf := D.eventually_exists_KflatOp κ 9 hst.omega_ne hst.gamma_pos hst.sigma_pos
    hst.sigma_lt hst.chiY hst.chiF hst.as_pos hflat xmtSmooth xmtSolenoidal xmtLinear
    (fun μ => sourceLAmbient D.K.as {μ} D.K.χo D.K.χy)
    (hOld D.K.as D.K.χf) (frakTLinear D.K.as D.K.χf 9) (hN0 D.K.as D.K.χf)
    (by norm_num) hst.bucTrain
  have haff := seq_affineFieldData D hst.omega_ne hst.gamma_pos hst.sigma_pos hst.sigma_lt
    hst.chiF has0 (eaCoefBound D.K.as D.K.χf hst.chiF)
  have haxi := pf2b_axiU D hst
  filter_upwards [hlarge, hst.pins, hst.near, hmu, haMu, hKf, haff, haxi]
    with n hlargen hpins hnear hmun haMun hKfn haffn haxin z hz
  obtain ⟨hact, hP, -, hmuIcc⟩ := hlargen
  have hwin := NearInst.winK_sub hst.sigma_pos hst.sigma_lt (hmun z hz)
  have hμ' : -(1 / 4) < D.mu n z := by linarith [(hmuIcc z hz).1, hst.sigma_pos]
  have hne := hnear z hz
  have hp := hpins z hz
  have hR : IsBodyInverse (concreteBase D.Pl D.K (D.level n) (D.mu n z) hne)
      (D.level n).ε (D.mu n z) :=
    concreteBase_isBodyInverse NearInst.tepsWeakSol weakToFreeResponse srcLiftYr
      (NearInst.Masked.cpcH_eq _ (cOf_pos (retNu_pos D.Pl D.σ₀ n))) hP hμ' hp.body hne
  rw [concreteOps_eq _ _ _ _ hne]
  exact concreteOps_wardAffineNilpotent hne hst.chiY.isYoungCutoff hst.chiF hP hwin.1 hwin.2
    hact.profile (inv_rhoB_pos hst.C0_pos) hmZ0 haxin NearInst.multPinOfLink hp.split hR
    hp.stress hp.ward (haffn z hz) hp.rA hp.lj (haMun z hz) hp.lam (hKfn z hz)

/-- **`WardAffineSeq` from `IIIa.CTKineticImpulse` (`PartIII-a:T22`)** (source 4300-4303,
5001-5008, 5796-5814). -/
theorem wardAffineSeq_of
    (hKI : UnforcedLeray.Short.IIIa.CTKineticImpulse) :
    Wiring.WardAffineSeq := by
  intro D dm dp hst hflat
  have hP : ∃ P, IsPlanarReference P := ⟨D.Pl, hst.planar⟩
  exact wardAffineSeq_of_kflat
    (frakTOldFinite_nine_of hP hKI)
    (frakTN0Bound_nine_of hP hKI)
    D dm dp hst hflat

end UnforcedLeray.Short.PartIIIb.Concrete
