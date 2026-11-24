import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G3.Org
import UnforcedLeray.Short.PartIIIb.NearInst.Targets
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_2_3_1.DatumNorm
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_2_3_1.KcEmbed.EvenRepAssembly
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_2_3_1.KcEmbed.RealBridge
import UnforcedLeray.Short.PartIIIa.T20_3_NonzeroVelUniform.WeightedHolder
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!


Source: `the November 2 reference manuscript` (73 pp), lines 4610-4612
(`M = v ⊗ K_c ξ + K_c ξ ⊗ v`), 2713-2723 (`stress-short:coefficients`), and 3230-3240
(`eq:ct-embeddings`).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G3

open ConcreteYF FlatSettingInst

/-- Pointwise bound on `2 M_{22} - M_{00}` for `M = symOuter a b`. -/
private theorem abs_symOuter_readout_le (a b : UnforcedLeray.Axi.Merid) :
    |2 * IIIa.symOuter a b 2 2 - IIIa.symOuter a b 0 0| ≤ 6 * ‖a‖ * ‖b‖ := by
  have ha : ‖a‖ ^ 2 = a 0 ^ 2 + a 1 ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
    simp
  have hb : ‖b‖ ^ 2 = b 0 ^ 2 + b 1 ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
    simp
  have hsq : (2 * IIIa.symOuter a b 2 2 - IIIa.symOuter a b 0 0) ^ 2 ≤ (6 * ‖a‖ * ‖b‖) ^ 2 := by
    have e : (6 * ‖a‖ * ‖b‖) ^ 2 = 36 * (‖a‖ ^ 2) * (‖b‖ ^ 2) := by ring
    rw [e, ha, hb]
    simp only [IIIa.symOuter, IIIa.embedMerid, Matrix.cons_val_zero, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons]
    nlinarith [sq_nonneg (a 0 * b 1 + a 1 * b 0), sq_nonneg (a 0 * b 0),
      sq_nonneg (a 0 * b 1), sq_nonneg (a 1 * b 0), sq_nonneg (a 1 * b 1)]
  exact abs_le.2 (abs_le_of_sq_le_sq' hsq (by positivity))

/-- Uniform Biot-Savart bound `‖kcLp ξ‖ ≤ C_m ‖ξ‖` for `1 ≤ c` and `8 < m`, with `C_m`
independent of `c`. -/
private theorem norm_kcLp_le_of_eight_lt (m : ℝ) [Fact (1 < m)] (h8 : 8 < m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : ℝ) [Fact (0 < c)], 1 ≤ c → ∀ ξ : Xmc c m,
      ‖kcLp ξ‖ ≤ C * ‖ξ‖ := by
  obtain ⟨C1, hC1⟩ := IIIa.ctEmbeddings m h8
  obtain ⟨C2, hC2⟩ := IIIa.CTE.biotSavart_exists_uniform m h8
  refine ⟨max C1 0, le_max_right _ _, fun c _ hc1 ξ => ?_⟩
  obtain ⟨g, hg1, hg2, hge, hgz⟩ := rePart_evenRep_zeroCirc ξ
  have hrM : MemLp (fun x => (((xFn ξ x).re : ℝ) : ℂ)) 2 (B0579.cellMeasure c m) :=
    (xFn_memLp ξ).re.ofReal
  have hgM : MemLp g 2 (B0579.cellMeasure c m) := hrM.ae_eq hg2.symm
  obtain ⟨u, hu, -⟩ := hC2 c hc1 g hgM hgz hge
  have hur : IIIa.IsBiotSavart c (fun x => (((xFn ξ x).re : ℝ) : ℂ)) u :=
    isBiotSavart_congr_ae hu hg1
  have hEmb := hC1 c hc1 g hgM hgz hge u hu
  have hk := kcLp_norm_le_velNorm ξ u hur
  have hxn : IIIa.xNorm c m g = IIIa.xNorm c m (fun x => (((xFn ξ x).re : ℝ) : ℂ)) :=
    eLpNorm_congr_ae hg2
  have hre_le : IIIa.xNorm c m (fun x => (((xFn ξ x).re : ℝ) : ℂ)) ≤ IIIa.xNorm c m (xFn ξ) := by
    unfold IIIa.xNorm
    refine eLpNorm_mono fun x => ?_
    simp only [Complex.norm_real, Real.norm_eq_abs]
    exact Complex.abs_re_le_norm _
  have hcalc : ENNReal.ofReal ‖kcLp ξ‖ ≤ ENNReal.ofReal (max C1 0 * ‖ξ‖) := by
    calc ENNReal.ofReal ‖kcLp ξ‖
        ≤ IIIa.velNorm c u := hk
      _ ≤ ENNReal.ofReal ‖IIIa.quadQ c g‖ + IIIa.velNorm c u := le_add_self
      _ ≤ ENNReal.ofReal C1 * IIIa.xNorm c m g := hEmb
      _ ≤ ENNReal.ofReal (max C1 0) * IIIa.xNorm c m g :=
          mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (le_max_left _ _)) bot_le
      _ ≤ ENNReal.ofReal (max C1 0) * IIIa.xNorm c m (xFn ξ) := by
          rw [hxn]
          exact mul_le_mul_of_nonneg_left hre_le bot_le
      _ = ENNReal.ofReal (max C1 0 * ‖ξ‖) := by
          rw [xNorm_xFn_eq, ← ENNReal.ofReal_mul (le_max_right _ _)]
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hcalc

/-- Transverse weight factor `(1 + (η / √(1+s))^2)⁻¹` on the cell. -/
private def invW2 (s : ℝ) (p : ℝ × ℝ) : ℝ :=
  (1 + (p.2 / Real.sqrt (1 + s)) ^ 2)⁻¹

private theorem invW2_nonneg (s : ℝ) (p : ℝ × ℝ) : 0 ≤ invW2 s p := by
  unfold invW2
  positivity

private theorem invW2_le_one (s : ℝ) (p : ℝ × ℝ) : invW2 s p ≤ 1 := by
  unfold invW2
  exact inv_le_one_of_one_le₀ (by linarith [sq_nonneg (p.2 / Real.sqrt (1 + s))])

private theorem transWeight_two_mul_invW2 (s : ℝ) (p : ℝ × ℝ) :
    IIIa.transWeight 2 (s, p) * invW2 s p = 1 := by
  unfold IIIa.transWeight invW2
  have hpos : (0 : ℝ) < 1 + (p.2 / Real.sqrt (1 + s)) ^ 2 := by positivity
  rw [show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one]
  exact mul_inv_cancel₀ hpos.ne'

/-- Integrability and `L¹`/`L²` bounds of `invW2 s` on `cellVol c`. -/
private theorem invW2_memLp_and_sq_integral_le {c s : ℝ} (hc : 0 < c) (hs : 0 ≤ s) :
    MemLp (invW2 s) 2 (B0581.cellVol c) ∧
      ∫ p, invW2 s p ^ (2 : ℝ) ∂(B0581.cellVol c) ≤
        c * (Real.sqrt (1 + s) * Real.pi) := by
  set a : ℝ := Real.sqrt (1 + s) with hadef
  have ha : 0 < a := Real.sqrt_pos.2 (by linarith)
  set h : ℝ → ℝ := fun η => (1 + (η / a) ^ 2)⁻¹ with hhdef
  have hh_int : Integrable h volume := integrable_inv_one_add_sq.comp_div ha.ne'
  have hh_eq : ∫ η : ℝ, h η = a * Real.pi := by
    have hcomp := Measure.integral_comp_div (fun y : ℝ => (1 + y ^ 2)⁻¹) a
    rw [hhdef, hcomp, integral_univ_inv_one_add_sq, smul_eq_mul, abs_of_pos ha]
  set μq : Measure ℝ := volume.restrict (Ico (-(c / 2)) (c / 2)) with hμq
  have hfin : IsFiniteMeasure μq := by
    rw [hμq]
    exact ⟨by simp⟩
  have hprod : B0581.cellVol c = μq.prod volume := by
    unfold B0581.cellVol B0579.cell
    rw [hμq, Measure.restrict_prod_eq_prod_univ, Measure.volume_eq_prod]
  have hf_int : Integrable (invW2 s) (B0581.cellVol c) := by
    rw [hprod]
    exact hh_int.comp_snd μq
  have hf_meas : Measurable (invW2 s) := by
    unfold invW2
    fun_prop
  have hf_sq_int : Integrable (fun p => invW2 s p ^ 2) (B0581.cellVol c) := by
    refine hf_int.mono' (hf_meas.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [invW2_nonneg s p, invW2_le_one s p]
  have hmem : MemLp (invW2 s) 2 (B0581.cellVol c) :=
    (memLp_two_iff_integrable_sq hf_meas.aestronglyMeasurable).2 hf_sq_int
  refine ⟨hmem, ?_⟩
  have hsq_eq : (fun p : ℝ × ℝ => invW2 s p ^ (2 : ℝ)) = fun p => invW2 s p ^ 2 := by
    funext p
    exact Real.rpow_two (invW2 s p)
  rw [hsq_eq]
  have hmono : ∫ p, invW2 s p ^ 2 ∂(B0581.cellVol c) ≤ ∫ p, invW2 s p ∂(B0581.cellVol c) := by
    refine integral_mono hf_sq_int hf_int fun p => ?_
    nlinarith [invW2_nonneg s p, invW2_le_one s p]
  have hint_eq : ∫ p, invW2 s p ∂(B0581.cellVol c) = c * (a * Real.pi) := by
    have hf_int' : Integrable (fun p : ℝ × ℝ => h p.2) (μq.prod volume) := hh_int.comp_snd μq
    calc ∫ p, invW2 s p ∂(B0581.cellVol c)
        = ∫ p : ℝ × ℝ, h p.2 ∂(μq.prod volume) := by rw [hprod]; rfl
      _ = ∫ q, (∫ η, h η) ∂μq := integral_prod (fun p : ℝ × ℝ => h p.2) hf_int'
      _ = ∫ _ in Ico (-(c / 2)) (c / 2), (a * Real.pi) := by rw [hh_eq, hμq]
      _ = c * (a * Real.pi) := by
          rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ico_of_le (by linarith)]
          ring_nf
  exact hmono.trans_eq hint_eq

/-- Cauchy-Schwarz on `B0581.cellVol c` for `invW2 s` and `‖kcLp ξ‖`. -/
private theorem integral_invW2_mul_kcLp_le {c m s : ℝ} [Fact (1 < m)] [Fact (0 < c)]
    (hs : 0 ≤ s) (ξ : Xmc c m) :
    Integrable (fun p => invW2 s p * ‖(kcLp ξ : ℝ × ℝ → UnforcedLeray.Axi.Merid) p‖)
        (B0581.cellVol c) ∧
      ∫ p, invW2 s p * ‖(kcLp ξ : ℝ × ℝ → UnforcedLeray.Axi.Merid) p‖ ∂(B0581.cellVol c) ≤
        (c * (Real.sqrt (1 + s) * Real.pi)) ^ (1 / 2 : ℝ) * ‖kcLp ξ‖ := by
  have hc : 0 < c := Fact.out
  obtain ⟨hf1, hf1_int⟩ := invW2_memLp_and_sq_integral_le hc hs
  set f2 : ℝ × ℝ → ℝ := fun p => ‖(kcLp ξ : ℝ × ℝ → UnforcedLeray.Axi.Merid) p‖ with hf2def
  have hf2 : MemLp f2 2 (B0581.cellVol c) := (Lp.memLp (kcLp ξ)).norm
  have hint : Integrable (fun p => invW2 s p * f2 p) (B0581.cellVol c) :=
    hf1.integrable_mul hf2
  refine ⟨hint, ?_⟩
  have h2 : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  have hf1' : MemLp (invW2 s) (ENNReal.ofReal 2) (B0581.cellVol c) := by rwa [h2]
  have hf2' : MemLp f2 (ENNReal.ofReal 2) (B0581.cellVol c) := by rwa [h2]
  have hf1_nn : 0 ≤ᵐ[B0581.cellVol c] invW2 s := Eventually.of_forall (invW2_nonneg s)
  have hf2_nn : 0 ≤ᵐ[B0581.cellVol c] f2 := Eventually.of_forall fun p => norm_nonneg _
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := B0581.cellVol c) (p := 2) (q := 2)
    Real.HolderConjugate.two_two hf1_nn hf2_nn hf1' hf2'
  have hI2 : (∫ p, f2 p ^ (2 : ℝ) ∂(B0581.cellVol c)) ^ (1 / 2 : ℝ) = ‖kcLp ξ‖ := by
    have hnorm : ∀ p, ‖f2 p‖ = f2 p := fun p => Real.norm_of_nonneg (norm_nonneg _)
    have heq : (∫ p, f2 p ^ (2 : ℝ) ∂(B0581.cellVol c)) ^ (1 / 2 : ℝ) =
        (∫ p, ‖f2 p‖ ^ (2 : ℝ) ∂(B0581.cellVol c)) ^ (1 / 2 : ℝ) := by
      simp_rw [hnorm]
    rw [heq, ← IIIa.CTE.T20_3.WeightedHolderProof.toReal_eLpNorm_two f2 (B0581.cellVol c) hf2]
    rw [hf2def, eLpNorm_norm, ← Lp.norm_def]
  rw [hI2] at hH
  have hf1_nn_int : 0 ≤ ∫ p, invW2 s p ^ (2 : ℝ) ∂(B0581.cellVol c) :=
    integral_nonneg fun p => Real.rpow_nonneg (invW2_nonneg s p) _
  exact hH.trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow hf1_nn_int hf1_int (by norm_num)) (norm_nonneg _))

/-- **The old stress readout on the earlier-old range** (source 4610-4612, 2713-2723, 3230-3240). -/
theorem earlierReadout_of (D : SeqData) (hT : NearInst.FlatTrainMultBound) :
    G3.EarlierReadout D := by
  intro dm dp hst κ hκ m _ hm S hS
  obtain ⟨CT, kT, ν₀, hν₀, hbd⟩ := hT 2 (by norm_num)
  obtain ⟨CBS, hCBS0, hCBS⟩ := norm_kcLp_le_of_eight_lt m hm
  set ν₁ : ℝ := min ν₀ 1 with hν₁def
  have hν₁pos : 0 < ν₁ := lt_min hν₀ one_pos
  have hev : ∀ᶠ n : ℕ in atTop,
      (∃ FI : FlatInstData κ (nu D n) (cOf (nu D n)) m (D.train n),
        S n = levelFlat (retNu_pos D.Pl D.σ₀ n) FI D.K.χo (retEps D.Pl D.σ₀ n)) ∧
      nu D n < ν₁ :=
    hS.and ((retNu_tendsto D.σ₀ hst.omega_ne).eventually (gt_mem_nhds hν₁pos))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  set C' : ℝ := 12 * Real.pi * max CT 0 * CBS with hC'
  refine ⟨C', kT + 2, N, fun n hn s hs1 hs2 => ?_⟩
  obtain ⟨⟨FI, hFI⟩, hνlt⟩ := hN n hn
  set ν := nu D n with hνdef
  have hν : 0 < ν := retNu_pos D.Pl D.σ₀ n
  have hνa : ν ≤ ν₀ := hνlt.le.trans (min_le_left _ _)
  have hν1 : ν ≤ 1 := hνlt.le.trans (min_le_right _ _)
  have hνinv1 : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hs_ge_one : 1 ≤ s := by
    have : (1 : ℝ) ≤ 1.2 / ν := by
      calc (1 : ℝ) ≤ 1.2 * 1 := by norm_num
        _ ≤ 1.2 * ν⁻¹ := mul_le_mul_of_nonneg_left hνinv1 (by norm_num)
        _ = 1.2 / ν := (div_eq_mul_inv _ _).symm
    exact this.trans hs1
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs_ge_one
  set c := cOf ν with hcdef
  have hc0 : 0 < c := cOf_pos hν
  have : Fact (0 < c) := ⟨hc0⟩
  have hc_eq : c = (ν⁻¹) ^ 2 := by
    rw [hcdef, cOf, inv_pow]
  have hc1 : 1 ≤ c := by
    rw [hc_eq]
    nlinarith [hνinv1]
  obtain ⟨-, hpt⟩ := hbd ν ⟨hν, hνa⟩ c rfl (D.train n) (D.train_buc n)
  rw [hFI]
  intro ξ
  have hξ_eq : (levelFlat (retNu_pos D.Pl D.σ₀ n) FI D.K.χo (retEps D.Pl D.σ₀ n)).c = c := rfl
  have hM_eq : ∀ p, (levelFlat (retNu_pos D.Pl D.σ₀ n) FI D.K.χo (retEps D.Pl D.σ₀ n)).Mcell s ξ p =
      IIIa.symOuter (NearInst.trainMer (D.train n) (s, p)) (kcMer ξ p) := fun _ => rfl
  simp only [hξ_eq, hM_eq]
  set S_open : Set (ℝ × ℝ) := (Ioo (-c / 2) (c / 2)) ×ˢ (univ : Set ℝ) with hS_open
  have hsub : S_open ⊆ B0579.cell c := by
    rintro ⟨q, η⟩ ⟨hq, _⟩
    exact ⟨⟨by linarith [hq.1], hq.2⟩, trivial⟩
  set Kvel : ℝ := 6 * max CT 0 * ν⁻¹ ^ kT * (Real.sqrt s)⁻¹ with hKvel
  have hKvel0 : 0 ≤ Kvel := by positivity
  set G : ℝ × ℝ → ℝ := fun p =>
    Kvel * (invW2 s p * ‖(kcLp ξ : ℝ × ℝ → UnforcedLeray.Axi.Merid) p‖) with hGdef
  obtain ⟨hprod_int, hprod_le⟩ := integral_invW2_mul_kcLp_le hs0.le ξ
  have hG_int : Integrable G (B0581.cellVol c) := hprod_int.const_mul Kvel
  have hG0 : ∀ p, 0 ≤ G p := fun p =>
    mul_nonneg hKvel0 (mul_nonneg (invW2_nonneg s p) (norm_nonneg _))
  have hv_le : ∀ p : ℝ × ℝ,
      ‖NearInst.trainMer (D.train n) (s, p)‖ ≤
        max CT 0 * ν⁻¹ ^ kT * (Real.sqrt s)⁻¹ * invW2 s p := by
    intro p
    have h1 := (hpt (s, p) hs0).trans
      (mul_le_mul_of_nonneg_right (le_max_left CT 0) (by positivity))
    have hsq_pos : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
    have hW_eq := transWeight_two_mul_invW2 s p
    have h2 := mul_le_mul_of_nonneg_right h1 (mul_nonneg (inv_nonneg.2 hsq_pos.le) (invW2_nonneg s p))
    calc ‖NearInst.trainMer (D.train n) (s, p)‖
        = Real.sqrt s * (Real.sqrt s)⁻¹ * (IIIa.transWeight 2 (s, p) * invW2 s p) *
            ‖NearInst.trainMer (D.train n) (s, p)‖ := by
          rw [mul_inv_cancel₀ hsq_pos.ne', hW_eq, one_mul, one_mul]
      _ = Real.sqrt s * IIIa.transWeight 2 (s, p) * ‖NearInst.trainMer (D.train n) (s, p)‖ *
            ((Real.sqrt s)⁻¹ * invW2 s p) := by ring
      _ ≤ max CT 0 * ν⁻¹ ^ kT * ((Real.sqrt s)⁻¹ * invW2 s p) := h2
      _ = max CT 0 * ν⁻¹ ^ kT * (Real.sqrt s)⁻¹ * invW2 s p := by ring
  set F : ℝ × ℝ → ℝ := fun p =>
    2 * IIIa.symOuter (NearInst.trainMer (D.train n) (s, p)) (kcMer ξ p) 2 2 -
      IIIa.symOuter (NearInst.trainMer (D.train n) (s, p)) (kcMer ξ p) 0 0 with hFdef
  have hae_cell : ∀ᵐ p ∂(B0581.cellVol c), |F p| ≤ G p := by
    filter_upwards [kcMer_ae ξ] with p hp
    have hsym : |F p| ≤ 6 * ‖NearInst.trainMer (D.train n) (s, p)‖ * ‖kcMer ξ p‖ :=
      abs_symOuter_readout_le (NearInst.trainMer (D.train n) (s, p)) (kcMer ξ p)
    rw [hp] at hsym
    refine hsym.trans ?_
    have hv := hv_le p
    calc 6 * ‖NearInst.trainMer (D.train n) (s, p)‖ *
            ‖(kcLp ξ : ℝ × ℝ → UnforcedLeray.Axi.Merid) p‖
        ≤ 6 * (max CT 0 * ν⁻¹ ^ kT * (Real.sqrt s)⁻¹ * invW2 s p) *
            ‖(kcLp ξ : ℝ × ℝ → UnforcedLeray.Axi.Merid) p‖ := by
          gcongr
      _ = G p := by
          simp only [hGdef, hKvel]
          ring
  have hmeas_le : volume.restrict S_open ≤ B0581.cellVol c :=
    Measure.restrict_mono hsub le_rfl
  have hae_open : ∀ᵐ p ∂(volume.restrict S_open), |F p| ≤ G p :=
    ae_mono hmeas_le hae_cell
  have hint_F : |∫ p in S_open, F p| ≤
      Kvel * ((c * (Real.sqrt (1 + s) * Real.pi)) ^ (1 / 2 : ℝ) * ‖kcLp ξ‖) := by
    calc |∫ p in S_open, F p|
        ≤ ∫ p in S_open, |F p| := abs_integral_le_integral_abs
      _ ≤ ∫ p in S_open, G p :=
          integral_mono_of_nonneg (Eventually.of_forall fun p => abs_nonneg _)
            (hG_int.mono_measure hmeas_le) hae_open
      _ ≤ ∫ p, G p ∂(B0581.cellVol c) :=
          integral_mono_measure hmeas_le (Eventually.of_forall hG0) hG_int
      _ = Kvel * ∫ p, invW2 s p * ‖(kcLp ξ : ℝ × ℝ → UnforcedLeray.Axi.Merid) p‖
            ∂(B0581.cellVol c) := integral_const_mul Kvel _
      _ ≤ Kvel * ((c * (Real.sqrt (1 + s) * Real.pi)) ^ (1 / 2 : ℝ) * ‖kcLp ξ‖) :=
          mul_le_mul_of_nonneg_left hprod_le hKvel0
  have hcell_le : |cellInt c F| ≤
      c⁻¹ * (Kvel * ((c * (Real.sqrt (1 + s) * Real.pi)) ^ (1 / 2 : ℝ) * ‖kcLp ξ‖)) := by
    unfold cellInt
    rw [abs_mul, abs_of_pos (inv_pos.2 hc0)]
    exact mul_le_mul_of_nonneg_left hint_F (inv_nonneg.2 hc0.le)
  have hsq_s_inv : (Real.sqrt s)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (Real.one_le_sqrt.2 hs_ge_one)
  have hKvel_le : Kvel ≤ 6 * max CT 0 * ν⁻¹ ^ kT := by
    rw [hKvel]
    calc 6 * max CT 0 * ν⁻¹ ^ kT * (Real.sqrt s)⁻¹
        ≤ 6 * max CT 0 * ν⁻¹ ^ kT * 1 :=
          mul_le_mul_of_nonneg_left hsq_s_inv (by positivity)
      _ = 6 * max CT 0 * ν⁻¹ ^ kT := mul_one _
  have hs_le_c : s ≤ (ν⁻¹) ^ 2 := by
    have h1 : ν ^ (-(3 / 2 : ℝ)) ≤ ν ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hν hν1 (by norm_num)
    have h2 : ν ^ (-2 : ℝ) = (ν⁻¹) ^ 2 := by
      rw [Real.rpow_neg hν.le, Real.rpow_two, inv_pow]
    exact (hs2.trans h1).trans_eq h2
  have h1s_ge1 : 1 ≤ Real.sqrt (1 + s) :=
    Real.one_le_sqrt.2 (by linarith)
  have h1s_le : Real.sqrt (1 + s) ≤ 2 * (ν⁻¹) ^ 2 := by
    have hle1 : Real.sqrt (1 + s) ≤ 1 + s := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith
    have h1_le_c : 1 ≤ (ν⁻¹) ^ 2 := by nlinarith [hνinv1]
    linarith
  have hpi1 : 1 ≤ Real.pi := by linarith [Real.two_le_pi]
  have hprod_ge1 : 1 ≤ c * (Real.sqrt (1 + s) * Real.pi) := by
    have : 1 ≤ Real.sqrt (1 + s) * Real.pi := by nlinarith
    nlinarith
  have hrpow_le : (c * (Real.sqrt (1 + s) * Real.pi)) ^ (1 / 2 : ℝ) ≤
      c * (Real.sqrt (1 + s) * Real.pi) := by
    calc (c * (Real.sqrt (1 + s) * Real.pi)) ^ (1 / 2 : ℝ)
        ≤ (c * (Real.sqrt (1 + s) * Real.pi)) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hprod_ge1 (by norm_num)
      _ = c * (Real.sqrt (1 + s) * Real.pi) := Real.rpow_one _
  have hkc_le : ‖kcLp ξ‖ ≤ CBS * ‖ξ‖ := hCBS c hc1 ξ
  calc |cellInt c F|
      ≤ c⁻¹ * (Kvel * ((c * (Real.sqrt (1 + s) * Real.pi)) ^ (1 / 2 : ℝ) * ‖kcLp ξ‖)) := hcell_le
    _ ≤ c⁻¹ * ((6 * max CT 0 * ν⁻¹ ^ kT) *
          ((c * (Real.sqrt (1 + s) * Real.pi)) * (CBS * ‖ξ‖))) := by
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hc0.le)
        refine mul_le_mul hKvel_le (mul_le_mul hrpow_le hkc_le (norm_nonneg _) (by positivity))
          (by positivity) (by positivity)
    _ = c⁻¹ * c * (6 * max CT 0 * ν⁻¹ ^ kT) * Real.sqrt (1 + s) * (Real.pi * CBS * ‖ξ‖) := by ring
    _ = (6 * max CT 0 * ν⁻¹ ^ kT) * Real.sqrt (1 + s) * (Real.pi * CBS * ‖ξ‖) := by
        rw [inv_mul_cancel₀ hc0.ne', one_mul]
    _ ≤ (6 * max CT 0 * ν⁻¹ ^ kT) * (2 * (ν⁻¹) ^ 2) * (Real.pi * CBS * ‖ξ‖) := by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h1s_le (by positivity)) (by positivity)
    _ = C' * ν⁻¹ ^ (kT + 2) * ‖ξ‖ := by
        rw [hC', pow_add]
        ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G3
