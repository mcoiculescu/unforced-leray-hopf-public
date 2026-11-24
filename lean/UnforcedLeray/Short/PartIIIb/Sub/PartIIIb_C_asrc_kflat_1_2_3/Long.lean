import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_2_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_2_3_1.DatumNorm
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_2_3_1.KcEmbed
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.CompactWindow.Comparison.FlatStress.PlanarReferenceExists
import UnforcedLeray.Short.PartIIIa.T20_2_BiotSavartUnique
import UnforcedLeray.Short.PartIIIa.T22_CanonicalTransfer.KineticImpulse

/-!


Source of record: `the November 2 reference manuscript`, lines 3228-3251 and
4440-4455 (`eq:ct-kinetic-impulse`).

Proves `tfkLongAll_of_ctKineticImpulse`: once `PartIII-a:T22` provides
`UnforcedLeray.Short.IIIa.ctKineticImpulse : UnforcedLeray.Short.IIIa.CTKineticImpulse`,
`tfkLongAll m` follows in one line:
`theorem tfkLongAll (m : ℝ) [Fact (1 < m)] : TFKLongAll m := tfkLongAll_of_ctKineticImpulse m UnforcedLeray.Short.IIIa.ctKineticImpulse`.
The planar reference `∃ P, IsPlanarReference P` is already discharged unconditionally via
`UnforcedLeray.Short.PartIIIb.NearInst.Delta.planarReferenceExists`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete

open FlatSettingInst

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

/-- `TFKLongAll m` from `IIIa.CTKineticImpulse` (`PartIII-a:T22`, source 3242-3251, 4449-4455),
discharging `∃ P, IsPlanarReference P` unconditionally via `planarReferenceExists`. -/
theorem tfkLongAll_of_ctKineticImpulse (m : ℝ) [Fact (1 < m)]
    (hKI : UnforcedLeray.Short.IIIa.CTKineticImpulse) :
    TFKLongAll m := by
  intro h8
  have h1m : 1 < m := Fact.out
  have hm0 : 0 ≤ m := by linarith
  obtain ⟨P, hPref⟩ := UnforcedLeray.Short.PartIIIb.NearInst.Delta.planarReferenceExists
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

theorem tfkLongAll (m : ℝ) [Fact (1 < m)] : TFKLongAll m :=
  tfkLongAll_of_ctKineticImpulse m UnforcedLeray.Short.IIIa.ctKineticImpulse

end UnforcedLeray.Short.PartIIIb.Concrete
