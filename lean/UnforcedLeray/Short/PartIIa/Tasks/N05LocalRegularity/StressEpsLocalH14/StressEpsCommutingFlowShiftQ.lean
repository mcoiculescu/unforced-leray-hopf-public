import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_3_2
import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.StressEpsLocalH14.StressEpsCommutingFlowShiftQ.CutoffShift

/-!


Source of record: `the November 2 reference manuscript`,
lines 1765–1781 (`near:local-smoothing`).

Proves the log-age commuting-flow translation leaf `PhaseCommutingFlowCutoffShiftQ` by decomposing
pure phase translation `(θ, y) ↦ (θ + 2εh, y)` on `phaseVol P` into:
1. the unitary dilation semigroup `phaseDilation P (2 * ε * h)` (`HalfDrift.lean`),
2. the scalar factor `1 - e^{-(3/2) ε h}` (`L²` norm), and
3. the spatial scaling `y ↦ e^{-ε h} • y` on `spaceBox ε σ H1 L1` (`SliceGrad.lean`),
pulled back through `PhaseLiftBridge.lintegral_profileBox_shiftQ_sub_sq_eq` and localised with
`CutoffShift`, then concludes `stressEpsCommutingFlowShiftQ` via `stressEpsCommutingFlowShiftQ_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp UnforcedLeray.FreeStress
open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226
open N05_1Aux N05_3Aux N05_4Aux N05_3_1Aux N05_3_2Aux N05FlowAux

private theorem lintegral_enorm_sub_sq_eq_ofReal_norm_sub_sq {α E : Type*} [MeasurableSpace α]
    {μ : Measure α} [NormedAddCommGroup E] (f g : Lp E 2 μ) :
    ∫⁻ a, ‖(f : α → E) a - (g : α → E) a‖ₑ ^ (2 : ℝ) ∂μ = ENNReal.ofReal (‖f - g‖ ^ 2) := by
  rw [← lintegral_enorm_sq_eq_ofReal_norm_sq (f - g)]
  refine lintegral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub f g] with a ha
  rw [ha, Pi.sub_apply]

private theorem sum_norm_sq_le_sq_sum {P : ℝ} [Fact (0 < P)] (g : Fin 3 → Yq P 2) :
    ∑ j : Fin 3, ‖g j‖ ^ 2 ≤ (∑ j : Fin 3, ‖g j‖) ^ 2 := by
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  nlinarith [norm_nonneg (g 0), norm_nonneg (g 1), norm_nonneg (g 2),
    mul_nonneg (norm_nonneg (g 0)) (norm_nonneg (g 1)),
    mul_nonneg (norm_nonneg (g 0)) (norm_nonneg (g 2)),
    mul_nonneg (norm_nonneg (g 1)) (norm_nonneg (g 2))]

private theorem three_term_enorm_sq_le (x y w : CVec3) :
    ‖x + y + w‖ₑ ^ (2 : ℝ) ≤
      3 * ‖x‖ₑ ^ (2 : ℝ) + 3 * ‖y‖ₑ ^ (2 : ℝ) + 3 * ‖w‖ₑ ^ (2 : ℝ) := by
  have hreal : ‖x + y + w‖ ^ 2 ≤ 3 * ‖x‖ ^ 2 + 3 * ‖y‖ ^ 2 + 3 * ‖w‖ ^ 2 := by
    have htri : ‖x + y + w‖ ≤ ‖x‖ + ‖y‖ + ‖w‖ := by
      linarith [norm_add_le (x + y) w, norm_add_le x y]
    have hsq : ‖x + y + w‖ ^ 2 ≤ (‖x‖ + ‖y‖ + ‖w‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith [sq_nonneg (‖x‖ - ‖y‖), sq_nonneg (‖x‖ - ‖w‖), sq_nonneg (‖y‖ - ‖w‖)]
  have h1 : ‖x + y + w‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖x + y + w‖ ^ 2) := by
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]
  have h2 : 3 * ‖x‖ₑ ^ (2 : ℝ) + 3 * ‖y‖ₑ ^ (2 : ℝ) + 3 * ‖w‖ₑ ^ (2 : ℝ) =
      ENNReal.ofReal (3 * ‖x‖ ^ 2 + 3 * ‖y‖ ^ 2 + 3 * ‖w‖ ^ 2) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
      ← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
      Real.rpow_two, Real.rpow_two, Real.rpow_two]
  rw [h1, h2]
  exact ENNReal.ofReal_le_ofReal hreal

private theorem decomp_enorm_sq_le {c : ℝ} {d v₀ v_sh v_dil : CVec3}
    (hd : d = (c : ℂ) • v_dil) :
    ‖v_sh - v₀‖ₑ ^ (2 : ℝ) ≤
      3 * ‖d - v₀‖ₑ ^ (2 : ℝ) +
        3 * ‖((1 - c : ℝ) : ℂ) • v_sh‖ₑ ^ (2 : ℝ) +
        3 * ‖(c : ℂ) • (v_sh - v_dil)‖ₑ ^ (2 : ℝ) := by
  have hdecomp : v_sh - v₀ =
      (d - v₀) + ((1 - c : ℝ) : ℂ) • v_sh + (c : ℂ) • (v_sh - v_dil) := by
    rw [hd, Complex.coe_smul, Complex.coe_smul, Complex.coe_smul, sub_smul, one_smul, smul_sub]
    abel
  rw [hdecomp]
  exact three_term_enorm_sq_le _ _ _

private theorem setLIntegral_phaseAdd_smul_sq_le {P : ℝ} [Fact (0 < P)]
    (θ_t : AddCircle P) (S : Set Space) (r : ℝ) (V₀ : AddCircle P × Space → CVec3) :
    ∫⁻ z in univ ×ˢ S, ‖(r : ℂ) • V₀ (z.1 + θ_t, z.2)‖ₑ ^ (2 : ℝ) ∂(phaseVol P) ≤
      ENNReal.ofReal (|r| ^ 2) * ∫⁻ z, ‖V₀ z‖ₑ ^ (2 : ℝ) ∂(phaseVol P) := by
  let e : AddCircle P × Space ≃ᵐ AddCircle P × Space :=
    (MeasurableEquiv.addRight θ_t).prodCongr (MeasurableEquiv.refl Space)
  have he_apply : ∀ z : AddCircle P × Space, e z = (z.1 + θ_t, z.2) := fun ⟨_, _⟩ => rfl
  have he_eq : (e : AddCircle P × Space → AddCircle P × Space) = fun z => (z.1 + θ_t, z.2) :=
    funext he_apply
  have hmp_e : MeasurePreserving e (phaseVol P) (phaseVol P) := by
    rw [he_eq]
    exact measurePreserving_phaseAdd θ_t
  calc ∫⁻ z in univ ×ˢ S, ‖(r : ℂ) • V₀ (z.1 + θ_t, z.2)‖ₑ ^ (2 : ℝ) ∂(phaseVol P)
      ≤ ∫⁻ z, ‖(r : ℂ) • V₀ (z.1 + θ_t, z.2)‖ₑ ^ (2 : ℝ) ∂(phaseVol P) :=
        setLIntegral_le_lintegral _ _
    _ = ∫⁻ z, ‖(r : ℂ) • V₀ (e z)‖ₑ ^ (2 : ℝ) ∂(phaseVol P) := by
        refine lintegral_congr fun z => ?_
        rw [he_apply]
    _ = ∫⁻ z, ‖(r : ℂ) • V₀ z‖ₑ ^ (2 : ℝ) ∂(phaseVol P) :=
        hmp_e.lintegral_comp_emb e.measurableEmbedding
          (fun z => ‖(r : ℂ) • V₀ z‖ₑ ^ (2 : ℝ))
    _ = ENNReal.ofReal (|r| ^ 2) * ∫⁻ z, ‖V₀ z‖ₑ ^ (2 : ℝ) ∂(phaseVol P) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun z => ?_
        rw [Complex.coe_smul, ← ofReal_norm, norm_smul, Real.norm_eq_abs,
          ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _)) (by norm_num),
          Real.rpow_two, mul_pow, ENNReal.ofReal_mul (sq_nonneg _),
          ← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]

private theorem setLIntegral_phaseAdd_diff_sq_eq {P : ℝ} [Fact (0 < P)]
    (θ_t : AddCircle P) (S : Set Space) {r : ℝ} (hr : 0 ≤ r) (α : ℝ)
    (V₀ : AddCircle P × Space → CVec3) :
    ∫⁻ z in univ ×ˢ S,
        ‖(r : ℂ) • (V₀ (z.1 + θ_t, z.2) - V₀ (z.1 + θ_t, α • z.2))‖ₑ ^ (2 : ℝ) ∂(phaseVol P) =
      ENNReal.ofReal (r ^ 2) *
        ∫⁻ w in univ ×ˢ S, ‖V₀ (w.1, α • w.2) - V₀ w‖ₑ ^ (2 : ℝ) ∂(phaseVol P) := by
  let e : AddCircle P × Space ≃ᵐ AddCircle P × Space :=
    (MeasurableEquiv.addRight θ_t).prodCongr (MeasurableEquiv.refl Space)
  have he_apply : ∀ z : AddCircle P × Space, e z = (z.1 + θ_t, z.2) := fun ⟨_, _⟩ => rfl
  have he_eq : (e : AddCircle P × Space → AddCircle P × Space) = fun z => (z.1 + θ_t, z.2) :=
    funext he_apply
  have hmp_e : MeasurePreserving e (phaseVol P) (phaseVol P) := by
    rw [he_eq]
    exact measurePreserving_phaseAdd θ_t
  have hpre_e : e ⁻¹' ((univ : Set (AddCircle P)) ×ˢ S) = univ ×ˢ S := by
    ext z
    rw [mem_preimage, he_apply]
    simp
  let g₃ : AddCircle P × Space → ℝ≥0∞ :=
    fun w => ‖(r : ℂ) • (V₀ w - V₀ (w.1, α • w.2))‖ₑ ^ (2 : ℝ)
  have hcongr_a₃ : ∫⁻ z in univ ×ˢ S,
      ‖(r : ℂ) • (V₀ (z.1 + θ_t, z.2) - V₀ (z.1 + θ_t, α • z.2))‖ₑ ^ (2 : ℝ) ∂(phaseVol P) =
      ∫⁻ z in univ ×ˢ S, g₃ (e z) ∂(phaseVol P) := by
    refine lintegral_congr fun z => ?_
    dsimp only [g₃]
    rw [he_apply]
  have hsh : ∫⁻ z in univ ×ˢ S,
      ‖(r : ℂ) • (V₀ (z.1 + θ_t, z.2) - V₀ (z.1 + θ_t, α • z.2))‖ₑ ^ (2 : ℝ) ∂(phaseVol P) =
      ∫⁻ w in univ ×ˢ S, g₃ w ∂(phaseVol P) := by
    rw [hcongr_a₃, ← hpre_e]
    exact hmp_e.setLIntegral_comp_preimage_emb e.measurableEmbedding g₃ (univ ×ˢ S)
  rw [hsh, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun w => ?_
  dsimp only [g₃]
  rw [Complex.coe_smul, ← ofReal_norm, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hr, norm_sub_rev (V₀ w),
    ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hr (norm_nonneg _)) (by norm_num),
    Real.rpow_two, mul_pow, ENNReal.ofReal_mul (sq_nonneg _),
    ← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]

private theorem lintegral_phaseVol_three_term_le {P : ℝ} [Fact (0 < P)]
    (S : Set Space) (t : ℝ) (V₀ D_t : AddCircle P × Space → CVec3)
    (hV₀_asm : AEStronglyMeasurable V₀ (phaseVol P))
    (hDt_asm : AEStronglyMeasurable D_t (phaseVol P))
    (hD_ae : D_t =ᵐ[phaseVol P] fun q =>
      (Real.exp (-(3 / 4) * t) : ℂ) •
        V₀ (q.1 + (t : AddCircle P), Real.exp (-(t / 2)) • q.2)) :
    ∫⁻ z in univ ×ˢ S, ‖V₀ (z.1 + (t : AddCircle P), z.2) - V₀ z‖ₑ ^ (2 : ℝ) ∂(phaseVol P) ≤
      3 * ∫⁻ z, ‖D_t z - V₀ z‖ₑ ^ (2 : ℝ) ∂(phaseVol P) +
      3 * (ENNReal.ofReal (|1 - Real.exp (-(3 / 4) * t)| ^ 2) *
        ∫⁻ z, ‖V₀ z‖ₑ ^ (2 : ℝ) ∂(phaseVol P)) +
      3 * (ENNReal.ofReal (Real.exp (-(3 / 4) * t) ^ 2) *
        ∫⁻ w in univ ×ˢ S,
          ‖V₀ (w.1, Real.exp (-(t / 2)) • w.2) - V₀ w‖ₑ ^ (2 : ℝ) ∂(phaseVol P)) := by
  set θ_t : AddCircle P := (t : AddCircle P)
  set α : ℝ := Real.exp (-(t / 2))
  have hae_pt : ∀ᵐ z ∂((phaseVol P).restrict (univ ×ˢ S)),
      ‖V₀ (z.1 + θ_t, z.2) - V₀ z‖ₑ ^ (2 : ℝ) ≤
        3 * ‖D_t z - V₀ z‖ₑ ^ (2 : ℝ) +
          3 * ‖((1 - Real.exp (-(3 / 4) * t) : ℝ) : ℂ) • V₀ (z.1 + θ_t, z.2)‖ₑ ^ (2 : ℝ) +
          3 * ‖(Real.exp (-(3 / 4) * t) : ℂ) •
            (V₀ (z.1 + θ_t, z.2) - V₀ (z.1 + θ_t, α • z.2))‖ₑ ^ (2 : ℝ) := by
    refine ae_restrict_of_ae ?_
    filter_upwards [hD_ae] with z hD
    exact decomp_enorm_sq_le hD
  have hm₁ : AEMeasurable (fun z => 3 * ‖D_t z - V₀ z‖ₑ ^ (2 : ℝ))
      ((phaseVol P).restrict (univ ×ˢ S)) :=
    (((hDt_asm.sub hV₀_asm).enorm.pow_const (2 : ℝ)).const_mul 3).restrict
  have hm₂ : AEMeasurable
      (fun z => 3 * ‖((1 - Real.exp (-(3 / 4) * t) : ℝ) : ℂ) • V₀ (z.1 + θ_t, z.2)‖ₑ ^ (2 : ℝ))
      ((phaseVol P).restrict (univ ×ˢ S)) :=
    ((((hV₀_asm.comp_quasiMeasurePreserving
      (measurePreserving_phaseAdd θ_t).quasiMeasurePreserving).const_smul
      ((1 - Real.exp (-(3 / 4) * t) : ℝ) : ℂ)).enorm.pow_const (2 : ℝ)).const_mul 3).restrict
  have hsplit : ∫⁻ z in univ ×ˢ S, ‖V₀ (z.1 + θ_t, z.2) - V₀ z‖ₑ ^ (2 : ℝ) ∂(phaseVol P) ≤
      3 * ∫⁻ z in univ ×ˢ S, ‖D_t z - V₀ z‖ₑ ^ (2 : ℝ) ∂(phaseVol P) +
      3 * ∫⁻ z in univ ×ˢ S,
        ‖((1 - Real.exp (-(3 / 4) * t) : ℝ) : ℂ) • V₀ (z.1 + θ_t, z.2)‖ₑ ^ (2 : ℝ) ∂(phaseVol P) +
      3 * ∫⁻ z in univ ×ˢ S,
        ‖(Real.exp (-(3 / 4) * t) : ℂ) •
          (V₀ (z.1 + θ_t, z.2) - V₀ (z.1 + θ_t, α • z.2))‖ₑ ^ (2 : ℝ) ∂(phaseVol P) := by
    calc ∫⁻ z in univ ×ˢ S, ‖V₀ (z.1 + θ_t, z.2) - V₀ z‖ₑ ^ (2 : ℝ) ∂(phaseVol P)
        ≤ ∫⁻ z in univ ×ˢ S,
            (3 * ‖D_t z - V₀ z‖ₑ ^ (2 : ℝ) +
              3 * ‖((1 - Real.exp (-(3 / 4) * t) : ℝ) : ℂ) • V₀ (z.1 + θ_t, z.2)‖ₑ ^ (2 : ℝ) +
              3 * ‖(Real.exp (-(3 / 4) * t) : ℂ) •
                (V₀ (z.1 + θ_t, z.2) - V₀ (z.1 + θ_t, α • z.2))‖ₑ ^ (2 : ℝ))
            ∂(phaseVol P) := lintegral_mono_ae hae_pt
      _ = 3 * ∫⁻ z in univ ×ˢ S, ‖D_t z - V₀ z‖ₑ ^ (2 : ℝ) ∂(phaseVol P) +
          3 * ∫⁻ z in univ ×ˢ S,
            ‖((1 - Real.exp (-(3 / 4) * t) : ℝ) : ℂ) • V₀ (z.1 + θ_t, z.2)‖ₑ ^ (2 : ℝ)
            ∂(phaseVol P) +
          3 * ∫⁻ z in univ ×ˢ S,
            ‖(Real.exp (-(3 / 4) * t) : ℂ) •
              (V₀ (z.1 + θ_t, z.2) - V₀ (z.1 + θ_t, α • z.2))‖ₑ ^ (2 : ℝ) ∂(phaseVol P) := by
          rw [lintegral_add_left' (show AEMeasurable (fun z =>
              3 * ‖D_t z - V₀ z‖ₑ ^ (2 : ℝ) +
                3 * ‖((1 - Real.exp (-(3 / 4) * t) : ℝ) : ℂ) • V₀ (z.1 + θ_t, z.2)‖ₑ ^ (2 : ℝ))
              ((phaseVol P).restrict (univ ×ˢ S)) from hm₁.add hm₂),
            lintegral_add_left' hm₁,
            lintegral_const_mul' 3 _ (by norm_num),
            lintegral_const_mul' 3 _ (by norm_num),
            lintegral_const_mul' 3 _ (by norm_num)]
  refine hsplit.trans (add_le_add (add_le_add ?_ ?_) ?_)
  · exact mul_le_mul_of_nonneg_left (setLIntegral_le_lintegral _ _) zero_le
  · exact mul_le_mul_of_nonneg_left (setLIntegral_phaseAdd_smul_sq_le θ_t S _ V₀) zero_le
  · rw [setLIntegral_phaseAdd_diff_sq_eq θ_t S (Real.exp_pos _).le α V₀]

private theorem phaseDilation_sub_lintegral_le {P ε h : ℝ} [Fact (0 < P)]
    {v w_hd : Yq P 2} (hw : (FreeStress.phaseC0 P).HasPow (1 / 2) v w_hd) :
    ∫⁻ z, ‖(prodLpEquiv.symm (FreeStress.phaseDilation P (2 * ε * h) v) :
            AddCircle P × Space → CVec3) z -
          (prodLpEquiv.symm v : AddCircle P × Space → CVec3) z‖ₑ ^ (2 : ℝ) ∂(phaseVol P) ≤
      ENNReal.ofReal ((2 * Real.sqrt |ε * h| * ‖w_hd‖) ^ 2) := by
  have heq : ∫⁻ z, ‖(prodLpEquiv.symm (FreeStress.phaseDilation P (2 * ε * h) v) :
          AddCircle P × Space → CVec3) z -
        (prodLpEquiv.symm v : AddCircle P × Space → CVec3) z‖ₑ ^ (2 : ℝ) ∂(phaseVol P) =
      ENNReal.ofReal (‖FreeStress.phaseDilation P (2 * ε * h) v - v‖ ^ 2) := by
    unfold phaseVol
    rw [lintegral_enorm_sub_sq_eq_ofReal_norm_sub_sq
      (prodLpEquiv.symm (FreeStress.phaseDilation P (2 * ε * h) v)) (prodLpEquiv.symm v),
      ← LinearIsometryEquiv.map_sub, prodLpEquiv.symm.norm_map]
  rw [heq]
  exact ENNReal.ofReal_le_ofReal
    (pow_le_pow_left₀ (norm_nonneg _) (norm_phaseDilation_two_eps_mul_sub_le hw ε h) 2)

/-- Pure real-number scalar consolidation for the three commuting-flow pieces. -/
private theorem phaseShift_scalar_consolidation {ε σ L1 h nv nwhd gd_sq N_W : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hσ : 0 < σ) (hL1 : 0 ≤ L1)
    (hh : h ∈ Icc (-1 : ℝ) 1)
    (hnv0 : 0 ≤ nv) (hnwhd0 : 0 ≤ nwhd) (hgd0 : 0 ≤ gd_sq)
    (hnv : nv ≤ N_W) (hnwhd : nwhd ≤ N_W) (hgd : gd_sq ≤ N_W ^ 2) :
    3 * ENNReal.ofReal ((2 * Real.sqrt |ε * h| * nwhd) ^ 2) +
      3 * (ENNReal.ofReal (|1 - Real.exp (-(3 / 4) * (2 * ε * h))| ^ 2) *
        ENNReal.ofReal (nv ^ 2)) +
      3 * (ENNReal.ofReal (Real.exp (-(3 / 4) * (2 * ε * h)) ^ 2) *
        ENNReal.ofReal
          (3 * Real.exp 3 *
            ((ε⁻¹ * (1 + L1) * (Real.sqrt σ)⁻¹) *
              |Real.exp (-((2 * ε * h) / 2)) - 1|) ^ 2 * gd_sq)) ≤
      ENNReal.ofReal
        ((4 * Real.exp 5 *
            (|h| * ((1 + L1) * (Real.sqrt σ)⁻¹) + Real.sqrt |ε * h| + |ε * h|) * N_W) ^ 2) := by
  set t : ℝ := 2 * ε * h
  set α : ℝ := Real.exp (-(t / 2))
  set R : ℝ := ε⁻¹ * (1 + L1) * (Real.sqrt σ)⁻¹
  have hR0 : 0 ≤ R := by positivity
  have hh1 : |h| ≤ 1 := abs_le_one_of_mem_Icc hh
  have hεh_le1 : |ε * h| ≤ 1 := by
    rw [abs_mul, abs_of_pos hε]
    calc ε * |h| ≤ 1 * 1 := mul_le_mul hε1 hh1 (abs_nonneg h) zero_le_one
      _ = 1 := one_mul 1
  have ht2_eq : -(t / 2) = -(ε * h) := by dsimp only [t]; ring
  have ht2_abs : |-(t / 2)| ≤ 1 := by rw [ht2_eq, abs_neg]; exact hεh_le1
  have hexp1_5 : 1 ≤ Real.exp 5 := Real.one_le_exp (by norm_num)
  have hexp2_5 : Real.exp 2 ≤ Real.exp 5 := Real.exp_le_exp.2 (by norm_num)
  have ht34_abs : |-(3 / 4) * t| ≤ 2 := by
    have heq : -(3 / 4) * t = -((3 / 2 : ℝ) * (ε * h)) := by dsimp only [t]; ring
    rw [heq, abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    linarith
  have h1_sub_exp : |1 - Real.exp (-(3 / 4) * t)| ≤ 2 * Real.exp 5 * |ε * h| := by
    rw [abs_sub_comm]
    have hmvt := abs_exp_sub_one_le (by norm_num : (0 : ℝ) ≤ 2) ht34_abs
    have heq : |-(3 / 4) * t| = (3 / 2 : ℝ) * |ε * h| := by
      have h1 : -(3 / 4) * t = -((3 / 2 : ℝ) * (ε * h)) := by dsimp only [t]; ring
      rw [h1, abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    rw [heq] at hmvt
    calc |Real.exp (-(3 / 4) * t) - 1|
        ≤ Real.exp 2 * ((3 / 2 : ℝ) * |ε * h|) := hmvt
      _ ≤ Real.exp 5 * (2 * |ε * h|) :=
          mul_le_mul hexp2_5 (by linarith [abs_nonneg (ε * h)]) (by positivity) (Real.exp_pos 5).le
      _ = 2 * Real.exp 5 * |ε * h| := by ring
  have hRα_le : R * |α - 1| ≤ Real.exp 1 * (|h| * ((1 + L1) * (Real.sqrt σ)⁻¹)) := by
    have hα1 := abs_exp_sub_one_le (by norm_num : (0 : ℝ) ≤ 1) ht2_abs
    have heq : |-(t / 2)| = ε * |h| := by
      rw [ht2_eq, abs_neg, abs_mul, abs_of_pos hε]
    rw [heq] at hα1
    calc R * |α - 1|
        ≤ R * (Real.exp 1 * (ε * |h|)) := mul_le_mul_of_nonneg_left hα1 hR0
      _ = Real.exp 1 * (|h| * ((1 + L1) * (Real.sqrt σ)⁻¹)) := by
          dsimp only [R]
          have hε0 : ε ≠ 0 := hε.ne'
          field_simp
  have hexp_t34_le : Real.exp (-(3 / 4) * t) ≤ Real.exp 2 :=
    Real.exp_le_exp.2 ((le_abs_self _).trans ht34_abs)
  have hb₁ : (2 * Real.sqrt |ε * h| * nwhd) ^ 2 ≤
      (2 * Real.exp 5 * Real.sqrt |ε * h| * N_W) ^ 2 := by
    refine pow_le_pow_left₀ (by positivity) ?_ 2
    calc 2 * Real.sqrt |ε * h| * nwhd
        ≤ 2 * 1 * Real.sqrt |ε * h| * N_W := by nlinarith [Real.sqrt_nonneg |ε * h|]
      _ ≤ 2 * Real.exp 5 * Real.sqrt |ε * h| * N_W := by
          have hNW0 : 0 ≤ N_W := hnv0.trans hnv
          gcongr
  have hb₂ : |1 - Real.exp (-(3 / 4) * t)| ^ 2 * nv ^ 2 ≤
      (2 * Real.exp 5 * |ε * h| * N_W) ^ 2 := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ 2
    calc |1 - Real.exp (-(3 / 4) * t)| * nv
        ≤ (2 * Real.exp 5 * |ε * h|) * N_W :=
          mul_le_mul h1_sub_exp hnv hnv0 (by positivity)
      _ = 2 * Real.exp 5 * |ε * h| * N_W := by ring
  have hb₃ : Real.exp (-(3 / 4) * t) ^ 2 *
        (3 * Real.exp 3 * (R * |α - 1|) ^ 2 * gd_sq) ≤
      (2 * Real.exp 5 * (|h| * ((1 + L1) * (Real.sqrt σ)⁻¹)) * N_W) ^ 2 := by
    have hexp3_4 : 3 * Real.exp 3 ≤ (2 * Real.exp 2) ^ 2 := by
      have h1 : Real.exp 3 ≤ Real.exp 4 := Real.exp_le_exp.2 (by norm_num)
      have h2 : Real.exp 4 = Real.exp 2 ^ 2 := by
        rw [sq, ← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos 3]
    have hprod_exp : Real.exp 2 * (2 * Real.exp 2) * Real.exp 1 = 2 * Real.exp 5 := by
      have h1 : Real.exp 2 * Real.exp 2 * Real.exp 1 = Real.exp 5 := by
        rw [← Real.exp_add, ← Real.exp_add]; norm_num
      linarith
    have hsq_Rα : (R * |α - 1|) ^ 2 ≤
        (Real.exp 1 * (|h| * ((1 + L1) * (Real.sqrt σ)⁻¹))) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hRα_le 2
    have hexp_sq : Real.exp (-(3 / 4) * t) ^ 2 ≤ Real.exp 2 ^ 2 :=
      pow_le_pow_left₀ (Real.exp_pos _).le hexp_t34_le 2
    calc Real.exp (-(3 / 4) * t) ^ 2 *
            (3 * Real.exp 3 * (R * |α - 1|) ^ 2 * gd_sq)
        ≤ Real.exp 2 ^ 2 *
            ((2 * Real.exp 2) ^ 2 *
              (Real.exp 1 * (|h| * ((1 + L1) * (Real.sqrt σ)⁻¹))) ^ 2 * N_W ^ 2) := by
          gcongr
      _ = ((Real.exp 2 * (2 * Real.exp 2) * Real.exp 1) *
            (|h| * ((1 + L1) * (Real.sqrt σ)⁻¹)) * N_W) ^ 2 := by ring
      _ = (2 * Real.exp 5 * (|h| * ((1 + L1) * (Real.sqrt σ)⁻¹)) * N_W) ^ 2 := by
          rw [hprod_exp]
  have hreal_tot :
      3 * (2 * Real.exp 5 * Real.sqrt |ε * h| * N_W) ^ 2 +
        3 * (2 * Real.exp 5 * |ε * h| * N_W) ^ 2 +
        3 * (2 * Real.exp 5 * (|h| * ((1 + L1) * (Real.sqrt σ)⁻¹)) * N_W) ^ 2 ≤
      (4 * Real.exp 5 *
        (|h| * ((1 + L1) * (Real.sqrt σ)⁻¹) + Real.sqrt |ε * h| + |ε * h|) * N_W) ^ 2 := by
    have hA1 : 0 ≤ |h| * ((1 + L1) * (Real.sqrt σ)⁻¹) := by positivity
    have hA2 : 0 ≤ Real.sqrt |ε * h| := Real.sqrt_nonneg _
    have hA3 : 0 ≤ |ε * h| := abs_nonneg _
    have hsum_sq : 3 * (Real.sqrt |ε * h|) ^ 2 + 3 * |ε * h| ^ 2 +
        3 * (|h| * ((1 + L1) * (Real.sqrt σ)⁻¹)) ^ 2 ≤
        4 * (|h| * ((1 + L1) * (Real.sqrt σ)⁻¹) + Real.sqrt |ε * h| + |ε * h|) ^ 2 := by
      nlinarith [mul_nonneg hA1 hA2, mul_nonneg hA1 hA3, mul_nonneg hA2 hA3,
        sq_nonneg (|h| * ((1 + L1) * (Real.sqrt σ)⁻¹)),
        sq_nonneg (Real.sqrt |ε * h|), sq_nonneg |ε * h|]
    calc 3 * (2 * Real.exp 5 * Real.sqrt |ε * h| * N_W) ^ 2 +
            3 * (2 * Real.exp 5 * |ε * h| * N_W) ^ 2 +
            3 * (2 * Real.exp 5 * (|h| * ((1 + L1) * (Real.sqrt σ)⁻¹)) * N_W) ^ 2
        = (2 * Real.exp 5 * N_W) ^ 2 *
            (3 * (Real.sqrt |ε * h|) ^ 2 + 3 * |ε * h| ^ 2 +
              3 * (|h| * ((1 + L1) * (Real.sqrt σ)⁻¹)) ^ 2) := by ring
      _ ≤ (2 * Real.exp 5 * N_W) ^ 2 *
            (4 * (|h| * ((1 + L1) * (Real.sqrt σ)⁻¹) + Real.sqrt |ε * h| + |ε * h|) ^ 2) :=
          mul_le_mul_of_nonneg_left hsum_sq (sq_nonneg _)
      _ = (4 * Real.exp 5 *
            (|h| * ((1 + L1) * (Real.sqrt σ)⁻¹) + Real.sqrt |ε * h| + |ε * h|) * N_W) ^ 2 := by
          ring
  have h3_ofReal : ∀ x : ℝ, 0 ≤ x → (3 : ℝ≥0∞) * ENNReal.ofReal x = ENNReal.ofReal (3 * x) :=
    fun x _ => by rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  rw [← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (sq_nonneg _)]
  calc 3 * ENNReal.ofReal ((2 * Real.sqrt |ε * h| * nwhd) ^ 2) +
          3 * ENNReal.ofReal (|1 - Real.exp (-(3 / 4) * t)| ^ 2 * nv ^ 2) +
          3 * ENNReal.ofReal
            (Real.exp (-(3 / 4) * t) ^ 2 * (3 * Real.exp 3 * (R * |α - 1|) ^ 2 * gd_sq))
      ≤ 3 * ENNReal.ofReal ((2 * Real.exp 5 * Real.sqrt |ε * h| * N_W) ^ 2) +
          3 * ENNReal.ofReal ((2 * Real.exp 5 * |ε * h| * N_W) ^ 2) +
          3 * ENNReal.ofReal
            ((2 * Real.exp 5 * (|h| * ((1 + L1) * (Real.sqrt σ)⁻¹)) * N_W) ^ 2) :=
        add_le_add
          (add_le_add
            (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hb₁) zero_le)
            (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hb₂) zero_le))
          (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hb₃) zero_le)
    _ = ENNReal.ofReal
          (3 * (2 * Real.exp 5 * Real.sqrt |ε * h| * N_W) ^ 2 +
            3 * (2 * Real.exp 5 * |ε * h| * N_W) ^ 2 +
            3 * (2 * Real.exp 5 * (|h| * ((1 + L1) * (Real.sqrt σ)⁻¹)) * N_W) ^ 2) := by
        rw [h3_ofReal _ (sq_nonneg _), h3_ofReal _ (sq_nonneg _), h3_ofReal _ (sq_nonneg _),
          ← ENNReal.ofReal_add (mul_nonneg (by norm_num) (sq_nonneg _))
            (mul_nonneg (by norm_num) (sq_nonneg _)),
          ← ENNReal.ofReal_add
            (add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
              (mul_nonneg (by norm_num) (sq_nonneg _)))
            (mul_nonneg (by norm_num) (sq_nonneg _))]
    _ ≤ ENNReal.ofReal
          ((4 * Real.exp 5 *
            (|h| * ((1 + L1) * (Real.sqrt σ)⁻¹) + Real.sqrt |ε * h| + |ε * h|) * N_W) ^ 2) :=
        ENNReal.ofReal_le_ofReal hreal_tot

/-- Three-term commuting-flow bound on `phaseVol P` for pure phase shift `2 * ε * h` restricted to
`univ ×ˢ spaceBox ε σ H1 L1`. -/
private theorem lintegral_phaseVol_phaseShift_sub_sq_le {P ε σ L1 : ℝ} (H1 : ℝ) [Fact (0 < P)]
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hσ : 0 < σ) (hL1 : 0 ≤ L1)
    {v w_hd : Yq P 2} {g_diss : Fin 3 → Yq P 2}
    (hw : (FreeStress.phaseC0 P).HasPow (1 / 2) v w_hd)
    (hg : HasGrad v g_diss)
    {h : ℝ} (hh : h ∈ Icc (-1 : ℝ) 1) :
    ∫⁻ z in univ ×ˢ spaceBox ε σ H1 L1,
        ‖(prodLpEquiv.symm v : AddCircle P × Space → CVec3)
            (z.1 + ((2 * ε * h : ℝ) : AddCircle P), z.2) -
          (prodLpEquiv.symm v : AddCircle P × Space → CVec3) z‖ₑ ^ (2 : ℝ) ∂(phaseVol P) ≤
      ENNReal.ofReal
        ((4 * Real.exp 5 *
            (|h| * ((1 + L1) * (Real.sqrt σ)⁻¹) + Real.sqrt |ε * h| + |ε * h|) *
            (‖v‖ + ‖w_hd‖ + ∑ j : Fin 3, ‖g_diss j‖)) ^ 2) := by
  have hmS : MeasurableSet (spaceBox ε σ H1 L1) := measurableSet_spaceBox ε σ H1 L1
  have h3 := lintegral_phaseVol_three_term_le (spaceBox ε σ H1 L1) (2 * ε * h)
    (prodLpEquiv.symm v) (prodLpEquiv.symm (FreeStress.phaseDilation P (2 * ε * h) v))
    (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
    (FreeStress.phaseDilation_ae P (2 * ε * h) v)
  have hJ₁ := phaseDilation_sub_lintegral_le hw (ε := ε) (h := h)
  have hv_lint : ∫⁻ z,
      ‖(prodLpEquiv.symm v : AddCircle P × Space → CVec3) z‖ₑ ^ (2 : ℝ) ∂(phaseVol P) =
      ENNReal.ofReal (‖v‖ ^ 2) := by
    unfold phaseVol
    rw [lintegral_enorm_sq_eq_ofReal_norm_sq, prodLpEquiv.symm.norm_map]
  have hh1 : |h| ≤ 1 := abs_le_one_of_mem_Icc hh
  have ht2_abs : |-((2 * ε * h) / 2)| ≤ 1 := by
    have heq : -((2 * ε * h) / 2) = -(ε * h) := by ring
    rw [heq, abs_neg, abs_mul, abs_of_pos hε]
    calc ε * |h| ≤ 1 * 1 := mul_le_mul hε1 hh1 (abs_nonneg h) zero_le_one
      _ = 1 := one_mul 1
  have hα_bounds : Real.exp (-1) ≤ Real.exp (-((2 * ε * h) / 2)) ∧
      Real.exp (-((2 * ε * h) / 2)) ≤ Real.exp 1 := by
    obtain ⟨hl, hu⟩ := abs_le.1 ht2_abs
    exact ⟨Real.exp_le_exp.2 hl, Real.exp_le_exp.2 hu⟩
  have hJ₃ := lintegral_phaseVol_smul_sub_sq_le hg hmS
    (R := ε⁻¹ * (1 + L1) * (Real.sqrt σ)⁻¹) (α := Real.exp (-((2 * ε * h) / 2)))
    (by positivity) (spaceBox_subset_closedBall hε hε1 hσ hL1) hα_bounds.1 hα_bounds.2
  have hsum_nn : 0 ≤ ∑ j : Fin 3, ‖g_diss j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
  have hg_sq : ∑ j : Fin 3, ‖g_diss j‖ ^ 2 ≤
      (‖v‖ + ‖w_hd‖ + ∑ j : Fin 3, ‖g_diss j‖) ^ 2 := by
    have h1 := sum_norm_sq_le_sq_sum g_diss
    have h2 : ∑ j : Fin 3, ‖g_diss j‖ ≤ ‖v‖ + ‖w_hd‖ + ∑ j : Fin 3, ‖g_diss j‖ := by
      linarith [norm_nonneg v, norm_nonneg w_hd]
    exact h1.trans (pow_le_pow_left₀ hsum_nn h2 2)
  rw [hv_lint] at h3
  refine (h3.trans (add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left hJ₁ zero_le) (le_refl _))
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hJ₃ zero_le) zero_le))).trans ?_
  exact phaseShift_scalar_consolidation hε hε1 hσ hL1 hh
    (norm_nonneg v) (norm_nonneg w_hd) (Finset.sum_nonneg fun j _ => sq_nonneg _)
    (by linarith [norm_nonneg w_hd]) (by linarith [norm_nonneg v]) hg_sq

/-- Pure real-number consolidation of the shifted-profile and cutoff-commutator bounds into
`((|h| + √|ε h| + |ε h|) * (10 * e^5 * Gam^4 * N_W))^2`. -/
private theorem cutoffShiftQ_ennreal_consolidation {Gam H1 L1 σ cN nW N_W ε h : ℝ}
    (hG1 : 1 ≤ Gam) (hσ : 0 < σ) (hσH : σ ≤ H1) (hL1 : 0 ≤ L1)
    (h1H1 : 1 + H1 ≤ Gam) (h1L1 : 1 + L1 ≤ Gam)
    (hσ_sqrt : (Real.sqrt σ)⁻¹ ≤ Gam) (hcN0 : 0 ≤ cN) (hcN : cN ≤ Gam)
    (hnW0 : 0 ≤ nW) (hnW : nW ≤ N_W) (hNW0 : 0 ≤ N_W) :
    2 * (ENNReal.ofReal (((1 + H1) * cN) ^ 2) *
          ENNReal.ofReal
            ((4 * Real.exp 5 *
                (|h| * ((1 + L1) * (Real.sqrt σ)⁻¹) + Real.sqrt |ε * h| + |ε * h|) *
                N_W) ^ 2)) +
      2 * ENNReal.ofReal (((1 + H1) * (cN * |h|) * nW) ^ 2) ≤
      ENNReal.ofReal
        (((|h| + Real.sqrt |ε * h| + |ε * h|) * (10 * Real.exp 5 * Gam ^ 4 * N_W)) ^ 2) := by
  have hG0 : 0 ≤ Gam := zero_le_one.trans hG1
  have hG2_ge1 : 1 ≤ Gam ^ 2 := one_le_pow₀ hG1
  have hH1_pos : 0 < H1 := lt_of_lt_of_le hσ hσH
  set F_h : ℝ := |h| + Real.sqrt |ε * h| + |ε * h|
  have hFh0 : 0 ≤ F_h := by positivity
  have hbox_G2 : (1 + L1) * (Real.sqrt σ)⁻¹ ≤ Gam ^ 2 := by
    calc (1 + L1) * (Real.sqrt σ)⁻¹
        ≤ Gam * Gam := mul_le_mul h1L1 hσ_sqrt (by positivity) hG0
      _ = Gam ^ 2 := (sq Gam).symm
  have hcut_G2 : (1 + H1) * cN ≤ Gam ^ 2 := by
    calc (1 + H1) * cN
        ≤ Gam * Gam := mul_le_mul h1H1 hcN hcN0 hG0
      _ = Gam ^ 2 := (sq Gam).symm
  have hA_le : |h| * ((1 + L1) * (Real.sqrt σ)⁻¹) + Real.sqrt |ε * h| + |ε * h| ≤
      F_h * Gam ^ 2 := by
    have t1 : |h| * ((1 + L1) * (Real.sqrt σ)⁻¹) ≤ |h| * Gam ^ 2 :=
      mul_le_mul_of_nonneg_left hbox_G2 (abs_nonneg h)
    have t2 : Real.sqrt |ε * h| ≤ Real.sqrt |ε * h| * Gam ^ 2 :=
      le_mul_of_one_le_right (Real.sqrt_nonneg _) hG2_ge1
    have t3 : |ε * h| ≤ |ε * h| * Gam ^ 2 :=
      le_mul_of_one_le_right (abs_nonneg _) hG2_ge1
    dsimp only [F_h]
    linarith
  have h1_scalar : (1 + H1) * cN *
      (4 * Real.exp 5 *
        (|h| * ((1 + L1) * (Real.sqrt σ)⁻¹) + Real.sqrt |ε * h| + |ε * h|) * N_W) ≤
      F_h * (4 * Real.exp 5 * Gam ^ 4 * N_W) := by
    have h0_inner : 0 ≤ 4 * Real.exp 5 *
        (|h| * ((1 + L1) * (Real.sqrt σ)⁻¹) + Real.sqrt |ε * h| + |ε * h|) * N_W := by positivity
    calc (1 + H1) * cN *
            (4 * Real.exp 5 *
              (|h| * ((1 + L1) * (Real.sqrt σ)⁻¹) + Real.sqrt |ε * h| + |ε * h|) * N_W)
        ≤ Gam ^ 2 * (4 * Real.exp 5 * (F_h * Gam ^ 2) * N_W) := by
          refine mul_le_mul hcut_G2 ?_ h0_inner (sq_nonneg Gam)
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hA_le (by positivity)) hNW0
      _ = F_h * (4 * Real.exp 5 * Gam ^ 4 * N_W) := by ring
  have h2_scalar : (1 + H1) * (cN * |h|) * nW ≤
      F_h * (Real.exp 5 * Gam ^ 4 * N_W) := by
    have hexp5_1 : 1 ≤ Real.exp 5 := Real.one_le_exp (by norm_num)
    have hh_Fh : |h| ≤ F_h := by
      dsimp only [F_h]
      linarith [Real.sqrt_nonneg |ε * h|, abs_nonneg (ε * h)]
    have hG2_G4 : Gam ^ 2 ≤ Gam ^ 4 := pow_le_pow_right₀ hG1 (by norm_num)
    calc (1 + H1) * (cN * |h|) * nW
        = ((1 + H1) * cN) * |h| * nW := by ring
      _ ≤ Gam ^ 2 * F_h * N_W := by
          refine mul_le_mul (mul_le_mul hcut_G2 hh_Fh (abs_nonneg h) (sq_nonneg Gam)) hnW
            hnW0 (mul_nonneg (sq_nonneg Gam) hFh0)
      _ = F_h * (1 * Gam ^ 2 * N_W) := by ring
      _ ≤ F_h * (Real.exp 5 * Gam ^ 4 * N_W) := by
          refine mul_le_mul_of_nonneg_left ?_ hFh0
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul hexp5_1 hG2_G4 (sq_nonneg Gam) (Real.exp_pos 5).le) hNW0
  have h1_sq : ((1 + H1) * cN) ^ 2 *
      (4 * Real.exp 5 *
        (|h| * ((1 + L1) * (Real.sqrt σ)⁻¹) + Real.sqrt |ε * h| + |ε * h|) * N_W) ^ 2 ≤
      (F_h * (4 * Real.exp 5 * Gam ^ 4 * N_W)) ^ 2 := by
    rw [← mul_pow]
    have h0_lhs : 0 ≤ (1 + H1) * cN *
        (4 * Real.exp 5 *
          (|h| * ((1 + L1) * (Real.sqrt σ)⁻¹) + Real.sqrt |ε * h| + |ε * h|) * N_W) :=
      mul_nonneg (mul_nonneg (by linarith) hcN0) (by positivity)
    exact pow_le_pow_left₀ h0_lhs h1_scalar 2
  have h2_sq : ((1 + H1) * (cN * |h|) * nW) ^ 2 ≤
      (F_h * (Real.exp 5 * Gam ^ 4 * N_W)) ^ 2 := by
    have h0_lhs : 0 ≤ (1 + H1) * (cN * |h|) * nW :=
      mul_nonneg (mul_nonneg (by linarith) (mul_nonneg hcN0 (abs_nonneg h))) hnW0
    exact pow_le_pow_left₀ h0_lhs h2_scalar 2
  have hcomb_real :
      2 * (F_h * (4 * Real.exp 5 * Gam ^ 4 * N_W)) ^ 2 +
        2 * (F_h * (Real.exp 5 * Gam ^ 4 * N_W)) ^ 2 ≤
      (F_h * (10 * Real.exp 5 * Gam ^ 4 * N_W)) ^ 2 := by
    nlinarith [sq_nonneg (F_h * (Real.exp 5 * Gam ^ 4 * N_W))]
  have h2_ofReal : ∀ x : ℝ, 0 ≤ x → (2 : ℝ≥0∞) * ENNReal.ofReal x = ENNReal.ofReal (2 * x) :=
    fun x _ => by rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  calc 2 * ENNReal.ofReal
          (((1 + H1) * cN) ^ 2 *
            (4 * Real.exp 5 *
              (|h| * ((1 + L1) * (Real.sqrt σ)⁻¹) + Real.sqrt |ε * h| + |ε * h|) * N_W) ^ 2) +
        2 * ENNReal.ofReal (((1 + H1) * (cN * |h|) * nW) ^ 2)
      ≤ 2 * ENNReal.ofReal ((F_h * (4 * Real.exp 5 * Gam ^ 4 * N_W)) ^ 2) +
          2 * ENNReal.ofReal ((F_h * (Real.exp 5 * Gam ^ 4 * N_W)) ^ 2) :=
        add_le_add
          (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal h1_sq) zero_le)
          (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal h2_sq) zero_le)
    _ = ENNReal.ofReal
          (2 * (F_h * (4 * Real.exp 5 * Gam ^ 4 * N_W)) ^ 2 +
            2 * (F_h * (Real.exp 5 * Gam ^ 4 * N_W)) ^ 2) := by
        rw [h2_ofReal _ (sq_nonneg _), h2_ofReal _ (sq_nonneg _),
          ← ENNReal.ofReal_add (mul_nonneg zero_le_two (sq_nonneg _))
            (mul_nonneg zero_le_two (sq_nonneg _))]
    _ ≤ ENNReal.ofReal ((F_h * (10 * Real.exp 5 * Gam ^ 4 * N_W)) ^ 2) :=
        ENNReal.ofReal_le_ofReal hcomb_real

/-- Proof of the commuting-flow leaf `PhaseCommutingFlowCutoffShiftQ`. -/
theorem phaseCommutingFlowCutoffShiftQ : PhaseCommutingFlowCutoffShiftQ := by
  refine ⟨4, 10 * Real.exp 5, by positivity, ?_⟩
  intro ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ hM hχ _hχ1 hm _B _hB ε hε hε1 P _ hP _hP1
    U hU W w_hd g_diss hw hg h hh
  have hG1 := one_le_gamma χ χ1 hν hc hσ hσH hL1 hγ hM
  have hW_norm : ‖W‖ = ‖U (B0223.liftVec hε hc hP W)‖ :=
    (norm_phaseLift_liftVec hε hc hP U W).symm
  have hsum_nn : 0 ≤ ∑ j : Fin 3, ‖g_diss j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
  have hW_le_NW : ‖W‖ ≤ ‖U (B0223.liftVec hε hc hP W)‖ + ‖w_hd‖ + ∑ j : Fin 3, ‖g_diss j‖ := by
    rw [hW_norm]
    exact (le_add_of_nonneg_right (norm_nonneg w_hd)).trans (le_add_of_nonneg_right hsum_nn)
  have hNW0 : 0 ≤ ‖U (B0223.liftVec hε hc hP W)‖ + ‖w_hd‖ + ∑ j : Fin 3, ‖g_diss j‖ :=
    (norm_nonneg W).trans hW_le_NW
  have hBt0 : 0 ≤ (|h| + Real.sqrt |ε * h| + |ε * h|) *
      (10 * Real.exp 5 * Gamma ν c σ H1 L1 M γs χ χ1 ^ 4 *
        (‖U (B0223.liftVec hε hc hP W)‖ + ‖w_hd‖ + ∑ j : Fin 3, ‖g_diss j‖)) :=
    mul_nonneg (by positivity)
      (mul_nonneg
        (mul_nonneg (by positivity) (pow_nonneg (zero_le_one.trans hG1) 4))
        hNW0)
  have hf_meas : Measurable
      (fun p => flatStressCutRep c χ W (shiftQ h p) - flatStressCutRep c χ W p) :=
    ((measurable_flatStressCutRep c hm W).comp (measurable_shiftQ h)).sub
      (measurable_flatStressCutRep c hm W)
  refine cellL2Norm_le_of_lintegral_le hBt0 hf_meas ?_
  have hsplit := lintegral_flatStressCutRep_shift_sub_sq_le_split hm (measurable_shiftQ h) W
  let ψ : Profile → ℝ := fun q => χ (shiftQ h q) - χ q
  have hψ_m : Measurable ψ := (hm.comp (measurable_shiftQ h)).sub hm
  have hψ_bd : ∀ q, |ψ q| ≤ cNorm8 χ * |h| := fun q => by
    calc |χ (shiftQ h q) - χ q|
        ≤ cNorm8 χ * ‖shiftQ h q - q‖ := abs_cutoff_sub_le hc hχ q (shiftQ h q)
      _ = cNorm8 χ * |h| := by rw [norm_shiftQ_sub]
  have hψ_supp : ∀ q, ψ q ≠ 0 → σ ≤ q.1 ∧ q.1 ≤ H1 := fun q hq => by
    by_cases h1 : χ (shiftQ h q) = 0
    · have h2 : χ q ≠ 0 := fun h0 => hq (by simp [ψ, h1, h0])
      exact ⟨(hχ.support q h2).1, (hχ.support q h2).2.1⟩
    · exact ⟨(hχ.support (shiftQ h q) h1).1, (hχ.support (shiftQ h q) h1).2.1⟩
  have hI₂ := lintegral_bounded_smul_periodize_sq_le hc hσ hσH hψ_m hψ_bd hψ_supp W
  have hb_meas : Measurable (periodize c (W : Profile → MeridC)) :=
    measurable_periodize_any c (Lp.stronglyMeasurable W).measurable
  have hg_meas : Measurable fun p : Profile =>
      periodize c (W : Profile → MeridC) (shiftQ h p) -
        periodize c (W : Profile → MeridC) p :=
    (hb_meas.comp (measurable_shiftQ h)).sub hb_meas
  have hφ_bd : ∀ p, |χ (shiftQ h p)| ≤ cNorm8 χ :=
    fun p => abs_le_cNorm8_of_nearCutoff hc hχ (shiftQ h p)
  have hφ_supp : ∀ p, χ (shiftQ h p) ≠ 0 → p ∈ profileBox σ H1 L1 := fun p hp =>
    hχ.support (shiftQ h p) hp
  have hI₁_loc := lintegral_cutoff_smul_sq_le_profileBox (c := c) hσ hσH hφ_bd hφ_supp hg_meas
  rw [lintegral_profileBox_shiftQ_sub_sq_eq hε hc hP U hU W σ H1 L1 h] at hI₁_loc
  have hphase := lintegral_phaseVol_phaseShift_sub_sq_le H1 hε hε1 hσ hL1 hw hg hh
  have hI₁ := hI₁_loc.trans (mul_le_mul_of_nonneg_left hphase zero_le)
  refine (hsplit.trans
    (add_le_add (mul_le_mul_of_nonneg_left hI₁ zero_le)
      (mul_le_mul_of_nonneg_left hI₂ zero_le))).trans ?_
  exact cutoffShiftQ_ennreal_consolidation
    hG1 hσ hσH hL1
    (one_add_H1_le_gamma χ χ1 hν hc hσ hL1 hγ hM)
    (one_add_L1_le_gamma χ χ1 hν hc hσ hσH hγ hM)
    (inv_sqrt_sigma_le_gamma χ χ1 hν hc hσ hσH hL1 hγ hM)
    (cNorm8_nonneg χ)
    (cNorm8_le_gamma χ χ1 hν hc hσ hσH hL1 hγ hM)
    (norm_nonneg W)
    hW_le_NW
    hNW0

theorem stressEpsCommutingFlowShiftQ : UnforcedLeray.Short.PartIIa.StressEpsCommutingFlowShiftQ :=
  stressEpsCommutingFlowShiftQ_of phaseCommutingFlowCutoffShiftQ

end UnforcedLeray.Short.PartIIa
