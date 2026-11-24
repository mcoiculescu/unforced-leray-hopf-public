import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G1.LaterOutput
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G1.LaterOutput.Tail
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G1.GBAdmissible
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G3.ForwardGain
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G3.Readout
import UnforcedLeray.Short.PartIIIb.NearInst.FlatTrain.Proof

/-!
# `PartIII-b:IIIb-D3/2/G1/5/1`: the finite band (`0 < s ≤ H = 2/ν`) of the later output

Source of record: `the November 2 reference manuscript` (73 pages):
* lines 4376-4412 (finite-band estimate and frozen pair on `0 ≤ s ≤ H = 2/ν`);
* lines 4432-4460 (`eq:young-later-output` 4454, uniform Biot-Savart and moment embedding 4443-4450);
* lines 4573-4574 (`χ_o(s) = χ̂_o(νs) = 0` for `s ≤ 1.2/ν`).

What is proved here:
1. `chiO_eq_zero_of_le_cutoff` and `integrand_eq_zero_of_le_cutoff`: for `s ≤ 1.2/ν`, `χ_o(s) = 0`
   and the `momentC` integrand vanishes, so the band integral on `Ioc 0 (2/ν)` reduces to the
   active band `Ioc (1.2/ν) (2/ν)` (`setIntegral_band_eq_active`).
2. `duhamel_band_cocycle_of_bclass` and `xiD_band_eq_of_bclass`: for `1.1/ν ≤ s ≤ 2/ν`, since
   `B(t) = 0` above `1.1/ν`, the cocycle law (`YoungLaws.trans`) gives
   `𝒰(2/ν, s) (duhamel pk μ (g_B B) s) = duhamel pk μ (g_B B) (2/ν)` and
   `ξ_B(s) = s^{-μ} 𝒰(s, 1.1/ν) (duhamel pk μ (g_B B) (1.1/ν))`.
3. `matNorm_symOuter_le` and `bandReadout_of`: proves the uniform Biot-Savart and moment embedding
   `BandReadout D` on the active band `s ∈ [1.2/ν, 2/ν]` from `NearInst.FlatTrainMultBound`,
   `IIIa.ctEmbeddings`, and `IIIa.CTE.biotSavart_exists_uniform`.
4. `bandIntegrable_of`: proves the first conjunct of `BandBound D` (`IntegrableOn` of the
   `momentC` integrand on `Ioc 0 (2/ν)`) from `BandReadout D`, `measurable_integrand_levelFlat`,
   and the continuity of `ξ_B` (`G4.xiD_contOn_of_bclass`).
5. `bandBound_of`: derives `G1.LaterOutput.BandBound D` from `NearInst.FlatTrainMultBound` and
   `BandDuhamelControl D` (the remaining finite-band comparison between `‖ξ_B(s)‖` on
   `[1.2/ν, 2/ν]` and the canonical `rhs` at `H = 2/ν`).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G1.LaterOutput

open ConcreteYF FlatSettingInst

/-! ## 1. Outward cutoff vanishing below `1.2/ν` and reduction to `(1.2/ν, 2/ν]` -/

/-- Below `1.2 / ν`, the outward cutoff `χ_o(s) = χ̂_o(νs)` of `levelFlat` vanishes. -/
theorem chiO_eq_zero_of_le_cutoff {κ : IIIa.PlanarFrameKernels} {ν m : ℝ}
    [Fact (1 < m)] (hν : 0 < ν) {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)}
    (FI : FlatInstData κ ν (cOf ν) m tr) {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) (ε : ℝ)
    {s : ℝ} (hs : s ≤ 1.2 / ν) :
    (levelFlat hν FI χo ε).chiO s = 0 := by
  change χo (ν * s) = 0
  apply hχo.zero
  have h1 : ν * s ≤ 1.2 := by
    calc ν * s ≤ ν * (1.2 / ν) := mul_le_mul_of_nonneg_left hs hν.le
      _ = 1.2 := mul_div_cancel₀ (1.2 : ℝ) hν.ne'
  linarith

/-- Below `1.2 / ν`, the `momentC` integrand of `levelFlat` vanishes. -/
theorem integrand_eq_zero_of_le_cutoff {κ : IIIa.PlanarFrameKernels} {ν m : ℝ}
    [Fact (1 < m)] (hν : 0 < ν) {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)}
    (FI : FlatInstData κ ν (cOf ν) m tr) {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) (ε : ℝ)
    (k : ℕ) (μ : ℝ) (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ) {s : ℝ} (hs : s ≤ 1.2 / ν) :
    (levelFlat hν FI χo ε).chiO s * s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2) *
      cellInt (levelFlat hν FI χo ε).c (fun p =>
        matNorm ((levelFlat hν FI χo ε).Mcell s ((levelFlat hν FI χo ε).xi (μ : ℂ) B s) p)) = 0 := by
  rw [chiO_eq_zero_of_le_cutoff hν FI hχo ε hs, zero_mul, zero_mul]

/-- The `momentC` integrand is nonnegative on `(0, ∞)` for an actual flat setting `levelFlat`. -/
theorem integrand_levelFlat_nonneg {κ : IIIa.PlanarFrameKernels} {ν m : ℝ}
    [Fact (1 < m)] (hν : 0 < ν) {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)}
    (FI : FlatInstData κ ν (cOf ν) m tr) {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) (ε : ℝ)
    (k : ℕ) (μ : ℝ) (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ) {s : ℝ} (hs : 0 < s) :
    0 ≤ (levelFlat hν FI χo ε).chiO s * s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2) *
      cellInt (levelFlat hν FI χo ε).c (fun p =>
        matNorm ((levelFlat hν FI χo ε).Mcell s ((levelFlat hν FI χo ε).xi (μ : ℂ) B s) p)) := by
  have hc : 0 < (levelFlat hν FI χo ε).c := cOf_pos hν
  have hchi : 0 ≤ (levelFlat hν FI χo ε).chiO s := (hχo.range (ν * s)).1
  refine mul_nonneg (mul_nonneg hchi (Real.rpow_nonneg hs.le _)) ?_
  unfold cellInt
  refine mul_nonneg (inv_nonneg.2 hc.le) (setIntegral_nonneg
    (measurableSet_Ioo.prod MeasurableSet.univ) fun p _ => ?_)
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- Since `χ_o = 0` below `1.2 / ν`, the integral over `Ioc 0 (2 / ν)` equals the integral over the
active band `Ioc (1.2 / ν) (2 / ν)`. -/
theorem setIntegral_band_eq_active {D : SeqData} {S : ℕ → FlatSetting} {n k : ℕ} {z : ℝ}
    {B : ℝ → Matrix (Fin 3) (Fin 3) ℝ} {κ : IIIa.PlanarFrameKernels} {m : ℝ} [Fact (1 < m)]
    (FI : FlatInstData κ (nu D n) (cOf (nu D n)) m (D.train n))
    (hSn : S n = levelFlat (retNu_pos D.Pl D.σ₀ n) FI D.K.χo (retEps D.Pl D.σ₀ n)) :
    ∫ s in Ioc 0 (2 / nu D n), integrand D S n k z B s =
      ∫ s in Ioc (1.2 / nu D n) (2 / nu D n), integrand D S n k z B s := by
  have hν : 0 < nu D n := retNu_pos D.Pl D.σ₀ n
  have h12 : (0 : ℝ) ≤ 1.2 / nu D n := by positivity
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc
    (Ioc_subset_Ioc_left h12) fun s hs => ?_
  have hs_le : s ≤ 1.2 / nu D n := by
    by_contra h
    exact hs.2 ⟨not_le.1 h, hs.1.2⟩
  unfold integrand
  rw [hSn]
  exact integrand_eq_zero_of_le_cutoff hν FI D.K.hχo (retEps D.Pl D.σ₀ n) k (D.mu n z) B hs_le

/-! ## 2. Cocycle identities on the post-source band `[1.1/ν, 2/ν]` -/

/-- **Post-source cocycle formula for `ξ_B` (source 4385-4390, 4610)**: for `s ≥ 1.1/ν`,
`ξ_B(s) = s^{-μ} 𝒰(s, 1.1/ν) (duhamel pk μ (g_B B) (1.1/ν))`. -/
theorem xiD_band_eq_of_bclass {κ : IIIa.PlanarFrameKernels} {ν m : ℝ}
    [Fact (1 < m)] (hν : 0 < ν) {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)}
    (FI : FlatInstData κ ν (cOf ν) m tr) {μ a s : ℝ} (hμ : 0 ≤ μ)
    {B : ℝ → Matrix (Fin 3) (Fin 3) ℝ} (hB : IsBclass a ν B) (hs : 1.1 / ν ≤ s) :
    haveI : Fact (0 < cOf ν) := ⟨cOf_pos hν⟩
    xiD FI (μ : ℂ) B s =
      ((s ^ (-μ) : ℝ) : ℂ) •
        FI.ev.U s (1.1 / ν) (duhamel (actualPk FI) (μ : ℂ) (gBD FI B) (1.1 / ν)) := by
  have : Fact (0 < cOf ν) := ⟨cOf_pos hν⟩
  set Tf : ℝ := 1.1 / ν with hTf_def
  have hTfpos : 0 < Tf := div_pos (by norm_num) hν
  have hspos : 0 < s := hTfpos.trans_le hs
  have hBz : ∀ t, Tf < t → B t = 0 := by
    intro t ht
    exact hB.2.2.2.1 t fun htIoo => absurd htIoo.2 (not_lt.2 ht.le)
  have hInt : IntegrableOn (DuhIntegrand FI μ B Tf) (Ioc 0 Tf) :=
    duhIntegrand_integrableOn_of_bclass FI hμ hTfpos hB
  have hlate := xiDLate m κ ν μ hν tr FI B Tf s hTfpos hs hBz hInt
  have hpowTf : (Tf : ℂ) ^ (μ : ℂ) * (Tf : ℂ) ^ (-(μ : ℂ)) = 1 := by
    have hTf0 : (Tf : ℂ) ≠ 0 := by exact_mod_cast hTfpos.ne'
    rw [Complex.cpow_neg, mul_inv_cancel₀ (Complex.cpow_ne_zero_iff.2 (Or.inl hTf0))]
  have hduhTf : ((Tf : ℂ) ^ (μ : ℂ)) • xiD FI (μ : ℂ) B Tf =
      duhamel (actualPk FI) (μ : ℂ) (gBD FI B) Tf := by
    rw [xiD_apply, smul_smul, hpowTf, one_smul]
    rfl
  have hs_cpow : (s : ℂ) ^ (-(μ : ℂ)) = ((s ^ (-μ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_neg, Complex.ofReal_cpow hspos.le]
  rw [hlate, mul_smul, ← map_smul, hduhTf, hs_cpow]

/-- **Forward transport of the Duhamel state across `[1.1/ν, 2/ν]`**: for `1.1/ν ≤ s ≤ 2/ν`,
`𝒰(2/ν, s) (duhamel pk μ (g_B B) s) = duhamel pk μ (g_B B) (2/ν)`. -/
theorem duhamel_band_cocycle_of_bclass {κ : IIIa.PlanarFrameKernels} {ν m : ℝ}
    [Fact (1 < m)] (hν : 0 < ν) {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)}
    (FI : FlatInstData κ ν (cOf ν) m tr) {μ a s : ℝ} (hμ : 0 ≤ μ)
    {B : ℝ → Matrix (Fin 3) (Fin 3) ℝ} (hB : IsBclass a ν B)
    (hs1 : 1.1 / ν ≤ s) (hs2 : s ≤ 2 / ν) :
    haveI : Fact (0 < cOf ν) := ⟨cOf_pos hν⟩
    FI.ev.U (2 / ν) s (duhamel (actualPk FI) (μ : ℂ) (gBD FI B) s) =
      duhamel (actualPk FI) (μ : ℂ) (gBD FI B) (2 / ν) := by
  have : Fact (0 < cOf ν) := ⟨cOf_pos hν⟩
  set H : ℝ := 2 / ν with hH_def
  have hspos : 0 < s := (div_pos (by norm_num) hν).trans_le hs1
  have hHpos : 0 < H := hspos.trans_le hs2
  have hBz : ∀ t, s < t → B t = 0 := by
    intro t ht
    apply hB.2.2.2.1 t
    intro htIoo
    linarith [htIoo.2, hs1, ht]
  have hInt : IntegrableOn (DuhIntegrand FI μ B s) (Ioc 0 s) :=
    duhIntegrand_integrableOn_of_bclass FI hμ hspos hB
  have hlate := xiDLate m κ ν μ hν tr FI B s H hspos hs2 hBz hInt
  have hpowS : (s : ℂ) ^ (μ : ℂ) * (s : ℂ) ^ (-(μ : ℂ)) = 1 := by
    have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hspos.ne'
    rw [Complex.cpow_neg, mul_inv_cancel₀ (Complex.cpow_ne_zero_iff.2 (Or.inl hs0))]
  have hpowH : (H : ℂ) ^ (μ : ℂ) * (H : ℂ) ^ (-(μ : ℂ)) = 1 := by
    have hH0 : (H : ℂ) ≠ 0 := by exact_mod_cast hHpos.ne'
    rw [Complex.cpow_neg, mul_inv_cancel₀ (Complex.cpow_ne_zero_iff.2 (Or.inl hH0))]
  have hduhS : ((s : ℂ) ^ (μ : ℂ)) • xiD FI (μ : ℂ) B s =
      duhamel (actualPk FI) (μ : ℂ) (gBD FI B) s := by
    rw [xiD_apply, smul_smul, hpowS, one_smul]
    rfl
  have hduhH : ((H : ℂ) ^ (μ : ℂ)) • xiD FI (μ : ℂ) B H =
      duhamel (actualPk FI) (μ : ℂ) (gBD FI B) H := by
    rw [xiD_apply, smul_smul, hpowH, one_smul]
    rfl
  rw [← hduhH, hlate, mul_smul, ← map_smul, hduhS, smul_smul, hpowH, one_smul]

/-! ## 3. Uniform Biot-Savart and moment embedding on the finite band -/

private theorem abs_embedMerid_le (v : Merid) (i : Fin 3) :
    |IIIa.embedMerid v i| ≤ ‖v‖ := by
  have hv : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
    simp
  have hv0 : |v 0| ≤ ‖v‖ :=
    abs_le.2 (abs_le_of_sq_le_sq' (by nlinarith [sq_nonneg (v 1)]) (norm_nonneg v))
  have hv1 : |v 1| ≤ ‖v‖ :=
    abs_le.2 (abs_le_of_sq_le_sq' (by nlinarith [sq_nonneg (v 0)]) (norm_nonneg v))
  fin_cases i
  · exact hv0
  · change |(0 : ℝ)| ≤ ‖v‖
    rw [abs_zero]
    exact norm_nonneg v
  · exact hv1

/-- Pointwise bound on `matNorm (symOuter a b)` for meridional vectors `a, b`. -/
theorem matNorm_symOuter_le (a b : Merid) :
    matNorm (IIIa.symOuter a b) ≤ 18 * ‖a‖ * ‖b‖ := by
  have hentry : ∀ i j : Fin 3, |IIIa.symOuter a b i j| ≤ 2 * ‖a‖ * ‖b‖ := by
    intro i j
    have hai := abs_embedMerid_le a i
    have haj := abs_embedMerid_le a j
    have hbi := abs_embedMerid_le b i
    have hbj := abs_embedMerid_le b j
    change |IIIa.embedMerid a i * IIIa.embedMerid b j +
      IIIa.embedMerid b i * IIIa.embedMerid a j| ≤ 2 * ‖a‖ * ‖b‖
    calc |IIIa.embedMerid a i * IIIa.embedMerid b j +
            IIIa.embedMerid b i * IIIa.embedMerid a j|
        ≤ |IIIa.embedMerid a i * IIIa.embedMerid b j| +
            |IIIa.embedMerid b i * IIIa.embedMerid a j| := abs_add_le _ _
      _ = |IIIa.embedMerid a i| * |IIIa.embedMerid b j| +
            |IIIa.embedMerid b i| * |IIIa.embedMerid a j| := by rw [abs_mul, abs_mul]
      _ ≤ ‖a‖ * ‖b‖ + ‖b‖ * ‖a‖ := add_le_add
            (mul_le_mul hai hbj (abs_nonneg _) (norm_nonneg a))
            (mul_le_mul hbi haj (abs_nonneg _) (norm_nonneg b))
      _ = 2 * ‖a‖ * ‖b‖ := by ring
  unfold matNorm
  calc ∑ i : Fin 3, ∑ j : Fin 3, |IIIa.symOuter a b i j|
      ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, (2 * ‖a‖ * ‖b‖) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hentry i j
    _ = 18 * ‖a‖ * ‖b‖ := by
        simp [Finset.sum_const]
        ring

/-- Uniform Biot-Savart bound `‖kcLp ξ‖ ≤ C_m ‖ξ‖` for `1 ≤ c` and `8 < m`, with `C_m`
independent of `c` (source 3230-3240, 4449-4450). -/
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

private theorem integral_invW2_mul_kcLp_le {c m s : ℝ} [Fact (1 < m)] [Fact (0 < c)]
    (hs : 0 ≤ s) (ξ : Xmc c m) :
    Integrable (fun p => invW2 s p * ‖(kcLp ξ : ℝ × ℝ → Merid) p‖)
        (B0581.cellVol c) ∧
      ∫ p, invW2 s p * ‖(kcLp ξ : ℝ × ℝ → Merid) p‖ ∂(B0581.cellVol c) ≤
        (c * (Real.sqrt (1 + s) * Real.pi)) ^ (1 / 2 : ℝ) * ‖kcLp ξ‖ := by
  have hc : 0 < c := Fact.out
  obtain ⟨hf1, hf1_int⟩ := invW2_memLp_and_sq_integral_le hc hs
  set f2 : ℝ × ℝ → ℝ := fun p => ‖(kcLp ξ : ℝ × ℝ → Merid) p‖ with hf2def
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

/-- **Uniform Biot-Savart and moment embedding on the active finite band** (source 4443-4450,
4610-4612, 2713-2723, 3230-3240): for every actual flat sequence and `s ∈ [1.2/ν, 2/ν]`,
`(1/c) ∫_cell |M_B(s)| ≤ C ν^{-k} ‖ξ‖_{X_{m,c}}`. -/
def BandReadout (D : SeqData) : Prop :=
  ForActual D fun S => ∃ (C : ℝ) (k N : ℕ), 0 ≤ C ∧ ∀ n ≥ N,
    ∀ s ∈ Icc (1.2 / nu D n) (2 / nu D n), ∀ ξ : (S n).pk.X,
      cellInt (S n).c (fun p => matNorm ((S n).Mcell s ξ p)) ≤
        C * (nu D n)⁻¹ ^ k * ‖ξ‖

/-- **Proof of `BandReadout`** from the flat train multiplier bound `NearInst.FlatTrainMultBound`
and the uniform Biot-Savart embedding (`IIIa.ctEmbeddings`, `IIIa.CTE.biotSavart_exists_uniform`). -/
theorem bandReadout_of (D : SeqData) (hT : NearInst.FlatTrainMultBound) :
    BandReadout D := by
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
  set C' : ℝ := 36 * Real.pi * max CT 0 * CBS with hC'
  refine ⟨C', kT + 2, N, by positivity, fun n hn s hs => ?_⟩
  obtain ⟨hs1, hs2⟩ := hs
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
  set Kvel : ℝ := 18 * max CT 0 * ν⁻¹ ^ kT * (Real.sqrt s)⁻¹ with hKvel
  have hKvel0 : 0 ≤ Kvel := by positivity
  set G : ℝ × ℝ → ℝ := fun p =>
    Kvel * (invW2 s p * ‖(kcLp ξ : ℝ × ℝ → Merid) p‖) with hGdef
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
    matNorm (IIIa.symOuter (NearInst.trainMer (D.train n) (s, p)) (kcMer ξ p)) with hFdef
  have hae_cell : ∀ᵐ p ∂(B0581.cellVol c), F p ≤ G p := by
    filter_upwards [kcMer_ae ξ] with p hp
    have hsym : F p ≤ 18 * ‖NearInst.trainMer (D.train n) (s, p)‖ * ‖kcMer ξ p‖ :=
      matNorm_symOuter_le (NearInst.trainMer (D.train n) (s, p)) (kcMer ξ p)
    rw [hp] at hsym
    refine hsym.trans ?_
    have hv := hv_le p
    calc 18 * ‖NearInst.trainMer (D.train n) (s, p)‖ *
            ‖(kcLp ξ : ℝ × ℝ → Merid) p‖
        ≤ 18 * (max CT 0 * ν⁻¹ ^ kT * (Real.sqrt s)⁻¹ * invW2 s p) *
            ‖(kcLp ξ : ℝ × ℝ → Merid) p‖ := by
          gcongr
      _ = G p := by
          simp only [hGdef, hKvel]
          ring
  have hmeas_le : volume.restrict S_open ≤ B0581.cellVol c :=
    Measure.restrict_mono hsub le_rfl
  have hae_open : ∀ᵐ p ∂(volume.restrict S_open), F p ≤ G p :=
    ae_mono hmeas_le hae_cell
  have hF0 : ∀ p, 0 ≤ F p := fun p =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hint_F : ∫ p in S_open, F p ≤
      Kvel * ((c * (Real.sqrt (1 + s) * Real.pi)) ^ (1 / 2 : ℝ) * ‖kcLp ξ‖) := by
    calc ∫ p in S_open, F p
        ≤ ∫ p in S_open, G p :=
          integral_mono_of_nonneg (Eventually.of_forall hF0)
            (hG_int.mono_measure hmeas_le) hae_open
      _ ≤ ∫ p, G p ∂(B0581.cellVol c) :=
          integral_mono_measure hmeas_le (Eventually.of_forall hG0) hG_int
      _ = Kvel * ∫ p, invW2 s p * ‖(kcLp ξ : ℝ × ℝ → Merid) p‖
            ∂(B0581.cellVol c) := integral_const_mul Kvel _
      _ ≤ Kvel * ((c * (Real.sqrt (1 + s) * Real.pi)) ^ (1 / 2 : ℝ) * ‖kcLp ξ‖) :=
          mul_le_mul_of_nonneg_left hprod_le hKvel0
  have hcell_le : cellInt c F ≤
      c⁻¹ * (Kvel * ((c * (Real.sqrt (1 + s) * Real.pi)) ^ (1 / 2 : ℝ) * ‖kcLp ξ‖)) := by
    unfold cellInt
    exact mul_le_mul_of_nonneg_left hint_F (inv_nonneg.2 hc0.le)
  have hsq_s_inv : (Real.sqrt s)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (Real.one_le_sqrt.2 hs_ge_one)
  have hKvel_le : Kvel ≤ 18 * max CT 0 * ν⁻¹ ^ kT := by
    rw [hKvel]
    calc 18 * max CT 0 * ν⁻¹ ^ kT * (Real.sqrt s)⁻¹
        ≤ 18 * max CT 0 * ν⁻¹ ^ kT * 1 :=
          mul_le_mul_of_nonneg_left hsq_s_inv (by positivity)
      _ = 18 * max CT 0 * ν⁻¹ ^ kT := mul_one _
  have hs_le_2c : s ≤ 2 * (ν⁻¹) ^ 2 := by
    have h2 : 2 / ν = 2 * ν⁻¹ := div_eq_mul_inv 2 ν
    have h3 : ν⁻¹ ≤ (ν⁻¹) ^ 2 := by nlinarith [hνinv1]
    linarith [hs2]
  have h1s_ge1 : 1 ≤ Real.sqrt (1 + s) :=
    Real.one_le_sqrt.2 (by linarith)
  have h1s_le : Real.sqrt (1 + s) ≤ 2 * (ν⁻¹) ^ 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    have h1_le_c : 1 ≤ (ν⁻¹) ^ 2 := by nlinarith [hνinv1]
    nlinarith [hs_le_2c, h1_le_c]
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
  calc cellInt c F
      ≤ c⁻¹ * (Kvel * ((c * (Real.sqrt (1 + s) * Real.pi)) ^ (1 / 2 : ℝ) * ‖kcLp ξ‖)) := hcell_le
    _ ≤ c⁻¹ * ((18 * max CT 0 * ν⁻¹ ^ kT) *
          ((c * (Real.sqrt (1 + s) * Real.pi)) * (CBS * ‖ξ‖))) := by
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hc0.le)
        refine mul_le_mul hKvel_le (mul_le_mul hrpow_le hkc_le (norm_nonneg _) (by positivity))
          (by positivity) (by positivity)
    _ = c⁻¹ * c * (18 * max CT 0 * ν⁻¹ ^ kT) * Real.sqrt (1 + s) * (Real.pi * CBS * ‖ξ‖) := by ring
    _ = (18 * max CT 0 * ν⁻¹ ^ kT) * Real.sqrt (1 + s) * (Real.pi * CBS * ‖ξ‖) := by
        rw [inv_mul_cancel₀ hc0.ne', one_mul]
    _ ≤ (18 * max CT 0 * ν⁻¹ ^ kT) * (2 * (ν⁻¹) ^ 2) * (Real.pi * CBS * ‖ξ‖) := by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h1s_le (by positivity)) (by positivity)
    _ = C' * ν⁻¹ ^ (kT + 2) * ‖ξ‖ := by
        rw [hC', pow_add]
        ring

/-! ## 4. Integrability on the finite band `0 < s ≤ 2/ν` -/

/-- **Integrability of the `momentC` integrand on the finite band `Ioc 0 (2/ν)`** (first conjunct
of `BandBound`): follows from `BandReadout`, `measurable_integrand_levelFlat`, the continuity of
`ξ_B` (`G4.xiD_contOn_of_bclass`), and the vanishing of `χ_o` below `1.2/ν`. -/
theorem bandIntegrable_of (D : SeqData) (hR : BandReadout D) :
    ForActual D fun S => ∃ N : ℕ, ∀ n ≥ N, ∀ k : ℕ, k ≤ 1 → ∀ z ∈ Icc (-1 : ℝ) 1,
      ∀ B, IsBclass D.K.as (nu D n) B →
        IntegrableOn (integrand D S n k z B) (Ioc 0 (2 / nu D n)) := by
  intro dm dp hst κ hκ m _ hm S hS
  obtain ⟨CR, kR, NR, hCR0, hCR⟩ := hR dm dp hst κ hκ m hm S hS
  have hmu_ev := mu_eventually_mem D hst.omega_ne hst.sigma_pos hst.sigma_lt
  obtain ⟨NS, hNS⟩ := eventually_atTop.1 (hS.and hmu_ev)
  refine ⟨max NR NS, fun n hn k _ z hz B hB => ?_⟩
  obtain ⟨⟨FI, hSn⟩, hmu_z⟩ := hNS n (le_trans (le_max_right _ _) hn)
  have hnR : NR ≤ n := le_trans (le_max_left _ _) hn
  have hν : 0 < nu D n := retNu_pos D.Pl D.σ₀ n
  have : Fact (0 < cOf (nu D n)) := ⟨cOf_pos hν⟩
  have hμ0 : 0 ≤ D.mu n z := by
    have := (hmu_z z hz).1
    linarith [hst.sigma_pos]
  have hmeas : Measurable (integrand D S n k z B) := by
    unfold integrand
    rw [hSn]
    exact measurable_integrand_levelFlat hν FI D.K.hχo (retEps D.Pl D.σ₀ n) k hμ0 hB
  set a1 : ℝ := 1.2 / nu D n
  set a2 : ℝ := 2 / nu D n
  have ha1_pos : 0 < a1 := div_pos (by norm_num) hν
  have hsub_Ioi : Icc a1 a2 ⊆ Ioi (0 : ℝ) := fun s hs => ha1_pos.trans_le hs.1
  have hξ_cont : ContinuousOn (fun s => ‖(S n).xi (D.mu n z : ℂ) B s‖) (Icc a1 a2) := by
    have hc : ContinuousOn (xiD FI (D.mu n z : ℂ) B) (Icc a1 a2) :=
      (G4.xiD_contOn_of_bclass FI hμ0 hB).mono hsub_Ioi
    have hxi_eq : (fun s => ‖(S n).xi (D.mu n z : ℂ) B s‖) =
        fun s => ‖xiD FI (D.mu n z : ℂ) B s‖ := by
      funext s
      rw [hSn]
      rfl
    rw [hxi_eq]
    exact continuous_norm.comp_continuousOn hc
  obtain ⟨Mξ, hMξ⟩ := isCompact_Icc.exists_bound_of_continuousOn hξ_cont
  have hpow_cont : ContinuousOn (fun s : ℝ => s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2)) (Icc a1 a2) := by
    refine ContinuousOn.rpow_const continuousOn_id fun s hs => Or.inl ?_
    exact (ha1_pos.trans_le hs.1).ne'
  obtain ⟨Ms, hMs⟩ := isCompact_Icc.exists_bound_of_continuousOn hpow_cont
  set K : ℝ := max Ms 0 * (CR * (nu D n)⁻¹ ^ kR * max Mξ 0) with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hintK : Integrable (fun _ : ℝ => K) (volume.restrict (Ioc 0 a2)) :=
    integrableOn_const measure_Ioc_lt_top.ne
  refine hintK.mono' hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have hnn : 0 ≤ integrand D S n k z B s := by
    unfold integrand
    rw [hSn]
    exact integrand_levelFlat_nonneg hν FI D.K.hχo (retEps D.Pl D.σ₀ n) k (D.mu n z) B hs.1
  rw [Real.norm_of_nonneg hnn]
  by_cases hsa1 : s ≤ a1
  · have hz0 : integrand D S n k z B s = 0 := by
      unfold integrand
      rw [hSn]
      exact integrand_eq_zero_of_le_cutoff hν FI D.K.hχo (retEps D.Pl D.σ₀ n) k (D.mu n z) B hsa1
    rw [hz0]
    exact hK0
  · have hsIcc : s ∈ Icc a1 a2 := ⟨(not_le.1 hsa1).le, hs.2⟩
    have hchi1 : (S n).chiO s ≤ 1 := by
      rw [hSn]
      exact (D.K.hχo.range (nu D n * s)).2
    have hchi0 : 0 ≤ (S n).chiO s := by
      rw [hSn]
      exact (D.K.hχo.range (nu D n * s)).1
    have hpow0 : 0 ≤ s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2) := Real.rpow_nonneg hs.1.le _
    have hpow_le : s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2) ≤ max Ms 0 := by
      have h1 := hMs s hsIcc
      rw [Real.norm_of_nonneg hpow0] at h1
      exact h1.trans (le_max_left _ _)
    have hξ_le : ‖(S n).xi (D.mu n z : ℂ) B s‖ ≤ max Mξ 0 := by
      have h1 := hMξ s hsIcc
      rw [Real.norm_of_nonneg (norm_nonneg _)] at h1
      exact h1.trans (le_max_left _ _)
    have hcell0 : 0 ≤ cellInt (S n).c (fun p =>
        matNorm ((S n).Mcell s ((S n).xi (D.mu n z : ℂ) B s) p)) := by
      rw [hSn]
      have hc : 0 < (levelFlat hν FI D.K.χo (retEps D.Pl D.σ₀ n)).c := cOf_pos hν
      unfold cellInt
      refine mul_nonneg (inv_nonneg.2 hc.le) (setIntegral_nonneg
        (measurableSet_Ioo.prod MeasurableSet.univ) fun p _ => ?_)
      exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hcell_le : cellInt (S n).c (fun p =>
        matNorm ((S n).Mcell s ((S n).xi (D.mu n z : ℂ) B s) p)) ≤
          CR * (nu D n)⁻¹ ^ kR * max Mξ 0 := by
      refine (hCR n hnR s hsIcc ((S n).xi (D.mu n z : ℂ) B s)).trans ?_
      exact mul_le_mul_of_nonneg_left hξ_le (by positivity)
    unfold integrand
    calc (S n).chiO s * s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2) *
            cellInt (S n).c (fun p => matNorm ((S n).Mcell s ((S n).xi (D.mu n z : ℂ) B s) p))
        ≤ 1 * max Ms 0 * (CR * (nu D n)⁻¹ ^ kR * max Mξ 0) := by
          refine mul_le_mul (mul_le_mul hchi1 hpow_le hpow0 zero_le_one) hcell_le hcell0 ?_
          positivity
      _ = K := by rw [one_mul, hKdef]

/-! ## 5. Full forward-gain band bound (`BandBoundTested` / `BandBound`)

On the finite band `s ∈ [1.2/ν, 2/ν]`, `duhamel pk μ (g_B B) s` is evaluated at ages `s < H = 2/ν`
before the transition age `H = 2/ν`. In `the November 2 reference manuscript`:
* `eq:young-later-output` (lines 4440-4458) bounds the unforced evolution from a state `w(H)` on
  **later ages `s ≥ H = 2/ν`** (`TailBound D` in `LaterOutput/Tail.lean`);
* on the earlier-old band `1.2/ν ≤ s ≤ 2/ν` (contained in `1.2/ν ≤ s < u_o = ν^{-3/2}`), the source
  (lines 4661-4663, 4677-4679, 4685-4694) bounds `duhamel(s)` using the full forward gain estimate
  (`G3.ForwardGain D`) and `G1.GBAdmissible D` in terms of `testedNorm` rather than `duhamel(2/ν)`,
  because radial/complementary sources in `ℬ_{a_s}` can have zero or exponentially damped state at
  `2/ν` while being nonzero on `[1.2/ν, 2/ν)`.

Below we prove the complete finite-band estimate `bandBoundTested_of` with `testedNorm`
on the RHS (`rhsTested`), matching `BandBound D` in `G1/LaterOutput.lean` and `G1/Org.lean`. -/

/-- An actual flat sequence has, at large levels, `c = ν⁻²`. -/
private theorem actual_c_eq {D : SeqData} {κ : IIIa.PlanarFrameKernels} {m : ℝ} [Fact (1 < m)]
    {S : ℕ → FlatSetting} (hS : IsActualSeq D κ m S) :
    ∀ᶠ n : ℕ in atTop, (S n).c = cOf (nu D n) := by
  filter_upwards [hS] with n hn
  obtain ⟨FI, hFI⟩ := hn
  rw [hFI]
  rfl

/-- Pointwise Duhamel control on the active finite band `s ∈ [1.2/ν, 2/ν]` in terms of `rhsTested`. -/
def BandDuhamelControlTested (D : SeqData) : Prop :=
  ForActual D fun S => ∀ kR : ℕ,
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ n ≥ N, ∀ k : ℕ, k ≤ 1 → ∀ z ∈ Icc (-1 : ℝ) 1,
      ∀ B, IsBclass D.K.as (nu D n) B →
      ∀ s ∈ Icc (1.2 / nu D n) (2 / nu D n),
        (nu D n)⁻¹ ^ (kR + 1) * s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2) *
          ‖(S n).xi (D.mu n z : ℂ) B s‖ ≤ C * rhsTested D S n k z B

/-- On the active finite band `s ∈ [1.2/ν, 2/ν]`, `IIIa.gainG γ ν s ≤ exp(2γ/(3ν))`, so the spare
factor `exp(-γ/(3ν))` absorbs all polynomial factors `ν⁻¹ ^ M`, yielding
`BandDuhamelControlTested D` from `G3.ForwardGain D` and `G1.GBAdmissible D`. -/
theorem bandDuhamelControlTested_of (D : SeqData)
    (hG : G3.ForwardGain D) (hA : G1.GBAdmissible D) :
    BandDuhamelControlTested D := by
  intro dm dp hst κ hκ m _ hm S hS kR
  obtain ⟨CG, kG, NG, hCG⟩ := hG dm dp hst κ hκ m hm S hS
  obtain ⟨NA, hNA⟩ := hA dm dp hst κ hκ m hm S hS
  set γ := D.Pl.eigenvalue.re with hγdef
  have hγ : 0 < γ := hst.gamma_pos
  have hev : ∀ᶠ n : ℕ in atTop,
      (S n).c = cOf (nu D n) ∧ nu D n < (1 / 4 : ℝ) ∧
        ∀ z ∈ Icc (-1 : ℝ) 1, D.mu n z ∈ Icc (D.σ₀ / 2) ((D.σ₀ + 1 / 4) / 2) :=
    (actual_c_eq hS).and (((retNu_tendsto D.σ₀ hst.omega_ne).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))).and
      (mu_eventually_mem D hst.omega_ne hst.sigma_pos hst.sigma_lt))
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
  set Kκ : ℝ := (2.1 : ℝ) ^ |D.Pl.kappa.re| with hKκ
  have hKκ0 : 0 ≤ Kκ := by positivity
  set M : ℕ := kR + 1 + kG + 7 + ⌈|D.Pl.kappa.re|⌉₊ with hMdef
  set KM : ℝ := (M.factorial : ℝ) / (γ / 3) ^ M with hKMdef
  have hKM0 : 0 ≤ KM := by positivity
  refine ⟨max CG 0 * Kκ * KM, max (max NG NA) N0, by positivity, ?_⟩
  intro n hn k hk z hz B hB s hs
  have hnG : NG ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnA : NA ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn0 : N0 ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨hc, hνquarter, hμwin⟩ := hN0 n hn0
  obtain ⟨hsupp, -, -, -, -, hint⟩ := hNA n hnA z hz B hB
  set ν := nu D n with hνdef
  have hν : 0 < ν := retNu_pos D.Pl D.σ₀ n
  have hν1 : ν ≤ 1 := by linarith
  set μ := D.mu n z with hμdef
  have hμ0 : 0 ≤ μ := by
    have := (hμwin z hz).1
    linarith [hst.sigma_pos]
  have hμ1 : μ ≤ 1 / 4 := by
    have := (hμwin z hz).2
    linarith [hst.sigma_lt]
  set tN := testedNorm (S n).pk D.Pl.eigenvalue D.Pl.kappa ν (μ : ℂ) (1.1 / ν) ((S n).gB B)
    with htN
  have htN0 : 0 ≤ tN := by
    rw [htN]
    unfold testedNorm
    exact setIntegral_nonneg measurableSet_Ioc fun t ht =>
      mul_nonneg (mul_nonneg (Real.rpow_nonneg ht.1.le _) (inv_nonneg.2 (norm_nonneg _)))
        (norm_nonneg _)
  set uo : ℝ := ν ^ (-(3 / 2 : ℝ)) with huo
  have hs1 : 1.2 / ν ≤ s := hs.1
  have hs_hi : s ≤ 2 / ν := hs.2
  have hs_ge1 : 1 ≤ s := by
    have h12 : (1.2 : ℝ) ≤ 1.2 / ν := by
      rw [le_div_iff₀ hν]
      linarith
    linarith
  have hspos : 0 < s := by linarith
  have hs2 : s ≤ uo := by
    have hsq : Real.sqrt ν ≤ 1 / 2 := by
      calc Real.sqrt ν ≤ Real.sqrt ((1 / 2 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by linarith)
        _ = 1 / 2 := Real.sqrt_sq (by norm_num)
    have h2_inv : 2 ≤ (Real.sqrt ν)⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) (Real.sqrt_pos.2 hν)]
      linarith
    have e1 : ν * uo = (Real.sqrt ν)⁻¹ := by
      have := Real.rpow_add hν (1 : ℝ) (-(3 / 2 : ℝ))
      rw [Real.rpow_one] at this
      rw [huo, ← this, Real.sqrt_eq_rpow, ← Real.rpow_neg hν.le]
      norm_num
    have h2_uo : 2 / ν ≤ uo := by
      have hmul : ν * (2 / ν) ≤ ν * uo := by
        rw [mul_div_cancel₀ _ hν.ne', e1]
        exact h2_inv
      exact le_of_mul_le_mul_left hmul hν
    exact hs_hi.trans h2_uo
  set E : ℝ := Real.exp (γ / ν) * Real.exp (-(γ / 3 * ν⁻¹)) with hE
  have hE0 : 0 ≤ E := by positivity
  -- 1. Gain on `s ≤ 2 / ν`
  have hgain : IIIa.gainG γ ν s ≤ E := by
    unfold IIIa.gainG
    rw [hE, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have hden : 0 < 1 + ν * s := by positivity
    have hνs : ν * s ≤ 2 := by
      calc ν * s ≤ ν * (2 / ν) := mul_le_mul_of_nonneg_left hs_hi hν.le
        _ = 2 := mul_div_cancel₀ _ hν.ne'
    have hsum : γ / ν + -(γ / 3 * ν⁻¹) = 2 * γ / (3 * ν) := by
      rw [ inv_eq_one_div]
      ring
    rw [hsum, div_le_div_iff₀ hden (by positivity)]
    nlinarith
  -- 2. `g(t)⁻¹ ≤ 2.1^{|Re κ|}|F_+(t,0)|⁻¹` on the source band
  have hFinv : ∀ t, 0 < t → t ≤ 1.1 / ν →
      (IIIa.gainG γ ν t)⁻¹ ≤ Kκ * ‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν t 0‖⁻¹ := by
    intro t ht htT
    have ha : 0 < aOf ν t := aOf_pos_of_nonneg ν t hν ht.le
    have ha1 : 1 ≤ aOf ν t := by
      unfold aOf
      nlinarith [mul_pos hν ht]
    have ha2 : aOf ν t ≤ 2.1 := by
      unfold aOf
      have : ν * t ≤ 1.1 := by
        calc ν * t ≤ ν * (1.1 / ν) := mul_le_mul_of_nonneg_left htT hν.le
          _ = 1.1 := by field_simp
      linarith
    have ha0 : aOf ν 0 = 1 := by simp [aOf]
    have hr : 0 < aOf ν t / aOf ν 0 := by rw [ha0, div_one]; exact ha
    have hnorm : ‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν t 0‖ =
        IIIa.gainG γ ν t * aOf ν t ^ D.Pl.kappa.re := by
      rw [fpm_true_eq, fpm_norm_formula _ _ ν t 0 hr, ha0, div_one]
      unfold IIIa.gainG zOf
      rw [ha0, zero_div, sub_zero]
      unfold aOf
      rw [mul_div_assoc]
    have hgpos : 0 < IIIa.gainG γ ν t := Real.exp_pos _
    have hapos : 0 < aOf ν t ^ D.Pl.kappa.re := Real.rpow_pos_of_pos ha _
    have heq : (IIIa.gainG γ ν t)⁻¹ =
        aOf ν t ^ D.Pl.kappa.re * ‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν t 0‖⁻¹ := by
      rw [hnorm]
      field_simp
    have hle : aOf ν t ^ D.Pl.kappa.re ≤ Kκ :=
      (Real.rpow_le_rpow_of_exponent_le ha1 (le_abs_self _)).trans
        (Real.rpow_le_rpow ha.le ha2 (abs_nonneg _))
    rw [heq]
    exact mul_le_mul_of_nonneg_right hle (inv_nonneg.2 (norm_nonneg _))
  -- 3. Duhamel state on the active band
  have hduh : ‖duhamel (S n).pk (μ : ℂ) ((S n).gB B) s‖ ≤
      max CG 0 * ν⁻¹ ^ kG * E * Kκ * tN := by
    have hTs : 1.1 / ν ≤ s := le_trans (div_le_div_of_nonneg_right (by norm_num) hν.le) hs1
    set K0 : ℝ := max CG 0 * ν⁻¹ ^ kG * E * Kκ with hK0
    have hK00 : 0 ≤ K0 := by positivity
    set F : ℝ → ℝ := fun t =>
      t ^ μ * ‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν t 0‖⁻¹ * ‖(S n).gB B t‖ with hF
    have hmaj : Integrable ((Ioc 0 (1.1 / ν)).indicator (fun t => K0 * F t))
        (volume.restrict (Ioc 0 s)) := by
      rw [integrable_indicator_iff measurableSet_Ioc, IntegrableOn,
        Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.2 (Ioc_subset_Ioc_right hTs)]
      exact hint.const_mul K0
    calc ‖duhamel (S n).pk (μ : ℂ) ((S n).gB B) s‖
        ≤ ∫ t in Ioc 0 s, ‖((t : ℂ) ^ (μ : ℂ)) • ((S n).pk.Uev s t) ((S n).gB B t)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ t in Ioc 0 s, (Ioc 0 (1.1 / ν)).indicator (fun t => K0 * F t) t := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _) hmaj ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          by_cases htT : t ≤ 1.1 / ν
          · rw [indicator_of_mem (show t ∈ Ioc 0 (1.1 / ν) from ⟨ht.1, htT⟩)]
            have hU := hCG n hnG t s ht.1 htT hs1 hs2 ((S n).gB B t)
            have hg2 := hFinv t ht.1 htT
            have hgs : 0 ≤ IIIa.gainG γ ν s := (Real.exp_pos _).le
            have hgt : 0 < IIIa.gainG γ ν t := Real.exp_pos _
            have htμ : 0 ≤ t ^ μ := Real.rpow_nonneg ht.1.le _
            have hrat0 : 0 ≤ IIIa.gainG γ ν s / IIIa.gainG γ ν t := div_nonneg hgs hgt.le
            have hratio : IIIa.gainG γ ν s / IIIa.gainG γ ν t ≤
                E * (Kκ * ‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν t 0‖⁻¹) := by
              rw [div_eq_mul_inv]
              exact mul_le_mul hgain hg2 (inv_nonneg.2 hgt.le) hE0
            rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht.1, Complex.ofReal_re]
            have hstep : ‖(S n).pk.Uev s t ((S n).gB B t)‖ ≤ max CG 0 * ν⁻¹ ^ kG *
                (E * (Kκ * ‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν t 0‖⁻¹)) *
                  ‖(S n).gB B t‖ := by
              refine hU.trans ?_
              calc CG * ν⁻¹ ^ kG * (IIIa.gainG γ ν s / IIIa.gainG γ ν t) * ‖(S n).gB B t‖
                  ≤ max CG 0 * ν⁻¹ ^ kG * (IIIa.gainG γ ν s / IIIa.gainG γ ν t) *
                      ‖(S n).gB B t‖ := by
                    gcongr
                    exact le_max_left _ _
                _ ≤ max CG 0 * ν⁻¹ ^ kG *
                    (E * (Kκ * ‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν t 0‖⁻¹)) *
                      ‖(S n).gB B t‖ := by
                    gcongr
            calc t ^ μ * ‖(S n).pk.Uev s t ((S n).gB B t)‖
                ≤ t ^ μ * (max CG 0 * ν⁻¹ ^ kG *
                    (E * (Kκ * ‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν t 0‖⁻¹)) *
                      ‖(S n).gB B t‖) := mul_le_mul_of_nonneg_left hstep htμ
              _ = K0 * F t := by
                  simp only [hK0, hF]
                  ring
          · have hz0 : (S n).gB B t = 0 := hsupp t (lt_of_not_ge htT)
            rw [hz0, map_zero, smul_zero, norm_zero]
            exact indicator_nonneg (fun t ht' => mul_nonneg hK00
              (mul_nonneg (mul_nonneg (Real.rpow_nonneg ht'.1.le _) (inv_nonneg.2 (norm_nonneg _)))
                (norm_nonneg _))) t
      _ = K0 * tN := by
          rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
            inter_eq_left.2 (Ioc_subset_Ioc_right hTs), integral_const_mul]
          rfl
  -- 4. Bounds on `s ^ (-(3/2) - k/2)` and `‖ξ_B(s)‖`
  have hspow : s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2) ≤ 1 := by
    have hexp_np : -(3 / 2 : ℝ) - (k : ℝ) / 2 ≤ 0 := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    exact Real.rpow_le_one_of_one_le_of_nonpos hs_ge1 hexp_np
  have hxi : ‖(S n).xi (μ : ℂ) B s‖ ≤ ‖duhamel (S n).pk (μ : ℂ) ((S n).gB B) s‖ := by
    unfold FlatSetting.xi
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hspos]
    simp only [Complex.neg_re, Complex.ofReal_re]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (Real.rpow_le_one_of_one_le_of_nonpos hs_ge1 (by linarith))
  -- 5. Powers of `ν` and exponential absorption
  have hpow : ν⁻¹ ^ (kR + 1) * ν⁻¹ ^ kG ≤
      ν ^ (-D.Pl.kappa.re) * ν ^ (3 + 2 * μ) * ν ^ (2 : ℕ) * ν ^ k * ν⁻¹ ^ M := by
    have e1 : ∀ j : ℕ, ν⁻¹ ^ j = ν ^ (-(j : ℝ)) := fun j => by
      rw [Real.rpow_neg hν.le, Real.rpow_natCast, inv_pow]
    have e2 : ∀ j : ℕ, ν ^ j = ν ^ (j : ℝ) := fun j => (Real.rpow_natCast ν j).symm
    rw [e1 (kR + 1), e1 kG, e1 M, e2 2, e2 k, ← Real.rpow_add hν, ← Real.rpow_add hν,
      ← Real.rpow_add hν, ← Real.rpow_add hν, ← Real.rpow_add hν]
    apply Real.rpow_le_rpow_of_exponent_ge hν hν1
    have hk_le : (k : ℝ) ≤ 1 := by exact_mod_cast hk
    have hc1 := Nat.le_ceil |D.Pl.kappa.re|
    have hab := neg_le_abs D.Pl.kappa.re
    dsimp [M]
    push_cast
    linarith
  have hM_bound : ν⁻¹ ^ M * Real.exp (-(γ / 3 * ν⁻¹)) ≤ KM := by
    have hpe : (γ / 3 * ν⁻¹) ^ M / (M.factorial : ℝ) ≤ Real.exp (γ / 3 * ν⁻¹) :=
      Real.pow_div_factorial_le_exp _ (by positivity) M
    have hfac_ne : (M.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero M)
    have hg3_ne : (γ / 3) ^ M ≠ 0 := pow_ne_zero M (by positivity)
    have h1 : ν⁻¹ ^ M = ((γ / 3 * ν⁻¹) ^ M / (M.factorial : ℝ)) * KM := by
      dsimp [KM]
      rw [mul_pow]
      field_simp
    calc ν⁻¹ ^ M * Real.exp (-(γ / 3 * ν⁻¹))
        = ((γ / 3 * ν⁻¹) ^ M / (M.factorial : ℝ)) * Real.exp (-(γ / 3 * ν⁻¹)) * KM := by
          rw [h1]
          ring
      _ ≤ Real.exp (γ / 3 * ν⁻¹) * Real.exp (-(γ / 3 * ν⁻¹)) * KM := by
          gcongr
      _ = KM := by
          rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  have hN : ‖Nnu D.Pl.eigenvalue D.Pl.kappa ν‖ = Real.exp (γ / ν) * ν ^ (-D.Pl.kappa.re) := by
    unfold Nnu
    rw [norm_mul, Complex.norm_exp, Complex.norm_cpow_eq_rpow_re_of_pos hν]
    simp [Complex.div_ofReal_re, hγdef]
  -- 6. Combine
  have hspow0 : 0 ≤ s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2) := Real.rpow_nonneg hspos.le _
  have hstep1 : ν⁻¹ ^ (kR + 1) * s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2) * ‖(S n).xi (μ : ℂ) B s‖ ≤
      ν⁻¹ ^ (kR + 1) * (max CG 0 * ν⁻¹ ^ kG * E * Kκ * tN) := by
    calc ν⁻¹ ^ (kR + 1) * s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2) * ‖(S n).xi (μ : ℂ) B s‖
        ≤ ν⁻¹ ^ (kR + 1) * 1 * (max CG 0 * ν⁻¹ ^ kG * E * Kκ * tN) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hspow (by positivity))
            (hxi.trans hduh) (norm_nonneg _) (by positivity)
      _ = ν⁻¹ ^ (kR + 1) * (max CG 0 * ν⁻¹ ^ kG * E * Kκ * tN) := by ring
  have hP0 : 0 ≤ max CG 0 * Kκ * Real.exp (γ / ν) * Real.exp (-(γ / 3 * ν⁻¹)) * tN := by
    positivity
  have hQ0 : 0 ≤ max CG 0 * Kκ * (‖Nnu D.Pl.eigenvalue D.Pl.kappa ν‖ * ν ^ (3 + 2 * μ) / (S n).c) *
      ν ^ k * tN := by
    rw [hc]
    have : 0 < cOf ν := cOf_pos hν
    positivity
  calc ν⁻¹ ^ (kR + 1) * s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2) * ‖(S n).xi (μ : ℂ) B s‖
      ≤ ν⁻¹ ^ (kR + 1) * (max CG 0 * ν⁻¹ ^ kG * E * Kκ * tN) := hstep1
    _ = (max CG 0 * Kκ * Real.exp (γ / ν) * Real.exp (-(γ / 3 * ν⁻¹)) * tN) *
          (ν⁻¹ ^ (kR + 1) * ν⁻¹ ^ kG) := by
        rw [hE]
        ring
    _ ≤ (max CG 0 * Kκ * Real.exp (γ / ν) * Real.exp (-(γ / 3 * ν⁻¹)) * tN) *
          (ν ^ (-D.Pl.kappa.re) * ν ^ (3 + 2 * μ) * ν ^ (2 : ℕ) * ν ^ k * ν⁻¹ ^ M) :=
        mul_le_mul_of_nonneg_left hpow hP0
    _ = (max CG 0 * Kκ * (‖Nnu D.Pl.eigenvalue D.Pl.kappa ν‖ * ν ^ (3 + 2 * μ) / (S n).c) *
          ν ^ k * tN) * (ν⁻¹ ^ M * Real.exp (-(γ / 3 * ν⁻¹))) := by
        rw [hN, hc, cOf, div_inv_eq_mul]
        ring
    _ ≤ (max CG 0 * Kκ * (‖Nnu D.Pl.eigenvalue D.Pl.kappa ν‖ * ν ^ (3 + 2 * μ) / (S n).c) *
          ν ^ k * tN) * KM := mul_le_mul_of_nonneg_left hM_bound hQ0
    _ = (max CG 0 * Kκ * KM) * rhsTested D S n k z B := by
        unfold rhsTested
        rw [← hνdef, ← hμdef, ← htN]
        ring

/-- **Unconditional finite-band bound in terms of `rhsTested`** (source lines 4376-4412,
4677-4694): combines `bandReadout_of`, `bandIntegrable_of`, and `bandDuhamelControlTested_of`. -/
theorem bandBoundTested_of (D : SeqData) (hT : NearInst.FlatTrainMultBound)
    (hG : G3.ForwardGain D) (hA : G1.GBAdmissible D) :
    BandBoundTested D := by
  have hR := bandReadout_of D hT
  have hInt := bandIntegrable_of D hR
  have hB := bandDuhamelControlTested_of D hG hA
  intro dm dp hst κ hκ m _ hm S hS
  obtain ⟨CR, kR, NR, hCR0, hCR⟩ := hR dm dp hst κ hκ m hm S hS
  obtain ⟨NI, hNI⟩ := hInt dm dp hst κ hκ m hm S hS
  obtain ⟨CD, ND, hCD0, hCD⟩ := hB dm dp hst κ hκ m hm S hS kR
  obtain ⟨NS, hNS⟩ := eventually_atTop.1 hS
  refine ⟨CR * CD, max (max NR NI) (max ND NS), by positivity, fun n hn k hk z hz B hBc => ?_⟩
  have hnR : NR ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnI : NI ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hnD : ND ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnS : NS ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  obtain ⟨FI, hSn⟩ := hNS n hnS
  have hint_full := hNI n hnI k hk z hz B hBc
  refine ⟨hint_full, ?_⟩
  rw [setIntegral_band_eq_active FI hSn]
  set ν := nu D n
  have hν : 0 < ν := retNu_pos D.Pl D.σ₀ n
  set a1 : ℝ := 1.2 / ν
  set a2 : ℝ := 2 / ν
  have ha12 : a1 ≤ a2 := div_le_div_of_nonneg_right (by norm_num) hν.le
  have hint_act : IntegrableOn (integrand D S n k z B) (Ioc a1 a2) :=
    hint_full.mono_set (Ioc_subset_Ioc_left (by positivity))
  set M : ℝ := CR * ν * (CD * rhsTested D S n k z B) with hMdef
  have hrhs0 : 0 ≤ rhsTested D S n k z B := by
    unfold rhsTested
    rw [hSn]
    have hc : 0 < (levelFlat hν FI D.K.χo (retEps D.Pl D.σ₀ n)).c := cOf_pos hν
    have htN0 : 0 ≤ testedNorm (levelFlat hν FI D.K.χo (retEps D.Pl D.σ₀ n)).pk
        D.Pl.eigenvalue D.Pl.kappa ν (D.mu n z : ℂ) (1.1 / ν)
        ((levelFlat hν FI D.K.χo (retEps D.Pl D.σ₀ n)).gB B) := by
      unfold testedNorm
      exact setIntegral_nonneg measurableSet_Ioc fun t ht =>
        mul_nonneg (mul_nonneg (Real.rpow_nonneg ht.1.le _) (inv_nonneg.2 (norm_nonneg _)))
          (norm_nonneg _)
    positivity
  have hpt : ∀ s ∈ Ioc a1 a2, integrand D S n k z B s ≤ M := by
    intro s hs
    have hsIcc : s ∈ Icc a1 a2 := ⟨hs.1.le, hs.2⟩
    have hspos : 0 < s := (div_pos (by norm_num) hν).trans hs.1
    have hchi1 : (S n).chiO s ≤ 1 := by
      rw [hSn]
      exact (D.K.hχo.range (ν * s)).2
    have hpow0 : 0 ≤ s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2) := Real.rpow_nonneg hspos.le _
    have hcell0 : 0 ≤ cellInt (S n).c (fun p =>
        matNorm ((S n).Mcell s ((S n).xi (D.mu n z : ℂ) B s) p)) := by
      rw [hSn]
      have hc : 0 < (levelFlat hν FI D.K.χo (retEps D.Pl D.σ₀ n)).c := cOf_pos hν
      unfold cellInt
      refine mul_nonneg (inv_nonneg.2 hc.le) (setIntegral_nonneg
        (measurableSet_Ioo.prod MeasurableSet.univ) fun p _ => ?_)
      exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hcell := hCR n hnR s hsIcc ((S n).xi (D.mu n z : ℂ) B s)
    have hduh := hCD n hnD k hk z hz B hBc s hsIcc
    unfold integrand
    calc (S n).chiO s * s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2) *
            cellInt (S n).c (fun p => matNorm ((S n).Mcell s ((S n).xi (D.mu n z : ℂ) B s) p))
        ≤ 1 * s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2) *
            (CR * ν⁻¹ ^ kR * ‖(S n).xi (D.mu n z : ℂ) B s‖) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right hchi1 hpow0) hcell hcell0 ?_
          positivity
      _ = CR * ν * (ν⁻¹ ^ (kR + 1) * s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2) *
            ‖(S n).xi (D.mu n z : ℂ) B s‖) := by
          rw [pow_succ, ← mul_assoc]
          have : ν * ν⁻¹ = 1 := mul_inv_cancel₀ hν.ne'
          linear_combination (norm := ring_nf)
            -(CR * ν⁻¹ ^ kR * s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2) *
              ‖(S n).xi (D.mu n z : ℂ) B s‖) * this
      _ ≤ CR * ν * (CD * rhsTested D S n k z B) :=
          mul_le_mul_of_nonneg_left hduh (by positivity)
  have hint_const : IntegrableOn (fun _ : ℝ => M) (Ioc a1 a2) :=
    integrableOn_const measure_Ioc_lt_top.ne
  have hle_int : ∫ s in Ioc a1 a2, integrand D S n k z B s ≤ ∫ _ in Ioc a1 a2, M :=
    setIntegral_mono_on hint_act hint_const measurableSet_Ioc hpt
  have hvol : volume.real (Ioc a1 a2) = a2 - a1 := by
    unfold Measure.real
    rw [Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.2 ha12)]
  have hsub_le : a2 - a1 ≤ ν⁻¹ := by
    change 2 / ν - 1.2 / ν ≤ ν⁻¹
    have : 2 / ν - 1.2 / ν = (0.8 : ℝ) * ν⁻¹ := by ring
    rw [this]
    have hinv0 : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    linarith
  calc ∫ s in Ioc a1 a2, integrand D S n k z B s
      ≤ ∫ _ in Ioc a1 a2, M := hle_int
    _ = (a2 - a1) * M := by rw [setIntegral_const, smul_eq_mul, hvol]
    _ ≤ ν⁻¹ * M := mul_le_mul_of_nonneg_right hsub_le (by positivity)
    _ = (CR * CD) * rhsTested D S n k z B := by
        rw [hMdef]
        have : ν⁻¹ * (CR * ν * (CD * rhsTested D S n k z B)) =
            (ν⁻¹ * ν) * (CR * CD * rhsTested D S n k z B) := by ring
        rw [this, inv_mul_cancel₀ hν.ne', one_mul]

/-- **Conditional finite-band bound `BandBound D`** (source lines 4376-4412, 4677-4694). -/
theorem bandBound_of (D : SeqData) (hT : NearInst.FlatTrainMultBound)
    (hG : G3.ForwardGain D) (hA : G1.GBAdmissible D) :
    G1.LaterOutput.BandBound D :=
  bandBoundTested_of D hT hG hA

/-- **Finite-band bound `BandBound D` from `FlatTrainMultBound` and `FullClockLongForward`**
(applying the accepted `G3.forwardGain_of` and `G1.gBAdmissible`). -/
theorem bandBound_of_clock (D : SeqData) (hT : NearInst.FlatTrainMultBound)
    (hLF : UnforcedLeray.Short.IIIa.FullClockLongForward) :
    G1.LaterOutput.BandBound D :=
  bandBoundTested_of D hT (G3.forwardGain_of D hLF) (G1.gBAdmissible D)

/-- **Finite-band bound `BandBound D` from the Part I train estimates and `FullClockLongForward`**
(applying `NearInst.flatTrainMultBound_of`, `G3.forwardGain_of`, and `G1.gBAdmissible`). -/
theorem bandBound_of_partI (D : SeqData)
    (hF : UnforcedLeray.Short.PartI.TrainFluctuationDecay)
    (hM : UnforcedLeray.Short.PartI.TrainMeanExpansion)
    (hE : UnforcedLeray.Short.PartI.TrainMeanEquations)
    (hLF : UnforcedLeray.Short.IIIa.FullClockLongForward) :
    G1.LaterOutput.BandBound D :=
  bandBound_of_clock D (NearInst.flatTrainMultBound_of hF hM hE) hLF

/-- If `duhamel(2/ν) = 0` while the finite-band integral on `Ioc 0 (2/ν)` is positive, the
unmodified `rhs` (which has `‖duhamel(2/ν)‖` as a factor) vanishes and cannot bound the band
integral. -/
theorem not_le_rhs_of_duhamel_two_eq_zero (D : SeqData) (S : ℕ → FlatSetting) (n k : ℕ) (z : ℝ)
    (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (C : ℝ)
    (h0 : duhamel (S n).pk (D.mu n z : ℂ) ((S n).gB B) (2 / nu D n) = 0)
    (hpos : 0 < ∫ s in Ioc 0 (2 / nu D n), integrand D S n k z B s) :
    ¬ (∫ s in Ioc 0 (2 / nu D n), integrand D S n k z B s ≤ C * rhs D S n k z B) := by
  have hrhs : rhs D S n k z B = 0 := by
    unfold rhs
    rw [h0, norm_zero, mul_zero, mul_zero]
  rw [hrhs, mul_zero]
  exact not_le.2 hpos

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G1.LaterOutput

