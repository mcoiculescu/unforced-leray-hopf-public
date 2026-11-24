import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2WeakEq.Design
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2WeakEq.FramePairing1
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.WeakFTC
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.WeakFTC.CutFTC.Smooth.PerGramSmooth
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.WeakFTC.CutFTC.Smooth.PhysFrameLam0Smooth
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.DirectError.HeatError.HeatDecomp
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_3_1

/-!
# Unconditional time-integrability of `a(q)⁻² * movH0 κ tr q i (movingW ν w q)`

Used by `Leaf2WeakEq` to apply Fubini integration by parts to `hAmplFTC` without requiring `ν ≤ ν₀`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace ComplFreeRateSub

namespace Leaf2WeakEqAmplInt

open CutFTCSmooth CutFTCDual CutFTCAux ComplCouplingHeat WeakFTCSub

private lemma nu_le_one_of_theta {ν b r : ℝ} (hν : 0 < ν) (hb : 1 ≤ b) (hr : 0 ≤ r)
    (hθ : b ≤ clockTheta ν r) : ν ≤ 1 := by
  have ha1 : 1 ≤ clockA ν r := one_le_clockA hν.le hr
  have ha0 : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one ha1
  have hθ1 : 1 ≤ clockTheta ν r := hb.trans hθ
  have hle : clockTheta ν r ≤ ν⁻¹ := by
    unfold clockTheta
    exact inv_anti₀ hν (le_mul_of_one_le_right hν.le ha1)
  have h1 : (1 : ℝ) ≤ ν⁻¹ := hθ1.trans hle
  rw [← inv_inv ν]
  exact inv_le_one_of_one_le₀ h1

private lemma dd_ge_one_of_theta {ν b r : ℝ} (hν : 0 < ν) (hb : 1 ≤ b) (hr : 0 ≤ r)
    (hθ : b ≤ clockTheta ν r) : 1 ≤ dd ν r := by
  have ha1 : 1 ≤ clockA ν r := one_le_clockA hν.le hr
  have ha0 : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one ha1
  have hν1 : ν ≤ 1 := nu_le_one_of_theta hν hb hr hθ
  have hsq_le : Real.sqrt (clockA ν r) ≤ clockA ν r := by
    calc Real.sqrt (clockA ν r)
        ≤ Real.sqrt (clockA ν r * clockA ν r) :=
          Real.sqrt_le_sqrt (le_mul_of_one_le_right ha0.le ha1)
      _ = clockA ν r := Real.sqrt_mul_self ha0.le
  have htheta_le : clockTheta ν r ≤ ν⁻¹ * clockTheta ν r :=
    le_mul_of_one_le_left (by unfold clockTheta; positivity) ((one_le_inv₀ hν).mpr hν1)
  have hcl : ν⁻¹ * clockTheta ν r ≤ dd ν r := by
    unfold dd cellLen clockTheta
    have hpow : ν ^ (-2 : ℝ) = ν⁻¹ * ν⁻¹ := by
      rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hν.le, Real.rpow_natCast, sq,
        mul_inv]
    rw [hpow, div_eq_mul_inv, mul_inv, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (inv_anti₀ (Real.sqrt_pos.2 ha0) hsq_le) (inv_nonneg.2 hν.le))
      (inv_nonneg.2 hν.le)
  exact (hb.trans hθ).trans (htheta_le.trans hcl)

private theorem perGram_det_ne_zero_of_perFrameFacts
    (κ : PlanarFrameKernels) (hκ : IsSeedKernels κ)
    {ν m b K : ℝ} (hν : 0 < ν) (hm : 8 < m) (hb : 1 ≤ b)
    (hF : PerFrameFacts κ ν m b K) {r : ℝ} (hr : 0 ≤ r) (hθ : b ≤ clockTheta ν r) :
    (perGram κ (dd ν r)).det ≠ 0 := by
  set d : ℝ := dd ν r
  have hd1 : 1 ≤ d := dd_ge_one_of_theta hν hb hr hθ
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  have hprod : (perGram κ d)⁻¹ * perGram κ d = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    have hbij := hF.1 r hr hθ i j
    have hint : ∀ k : Fin 2,
        IntegrableOn (fun x => perLam0 κ d k x * perE κ d j x) (B0579.cell d) := by
      intro k
      obtain ⟨_, _, hlam0⟩ := ComplCouplingHeat.memLp_and_xNorm_perLam0_neg κ (by linarith : 1 < m)
      have hlam : MemLp (perLam0 κ d k) 2 (B0579.cellMeasure d (-m)) := (hlam0 d hd1 k).1
      obtain ⟨_, _, hE0⟩ := DirectHeatDecomp.perE_memLp_cellMeasure κ hm
      have hE : MemLp (perE κ d j) 2 (B0579.cellMeasure d m) := (hE0 hd1 j).1
      exact (CutLimitAux.integrable_complex hE hlam).congr (ae_of_all _ fun _ => mul_comm _ _)
    have heq : (fun x => perLam κ d i x * perE κ d j x) =
        fun x => ∑ k : Fin 2, (perGram κ d)⁻¹ i k * (perLam0 κ d k x * perE κ d j x) := by
      funext x
      unfold perLam
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    change (∫ x in B0579.cell d, perLam κ d i x * perE κ d j x) = if i = j then 1 else 0 at hbij
    rw [heq, integral_finsetSum _ (fun k _ => (hint k).const_mul _)] at hbij
    simp_rw [integral_const_mul] at hbij
    rw [← hbij]
    rfl
  have hdet : ((perGram κ d)⁻¹).det * (perGram κ d).det = 1 := by
    rw [← Matrix.det_mul, hprod, Matrix.det_one]
  exact right_ne_zero_of_mul_eq_one hdet

private theorem contDiffOn_perGram_inv_Icc
    (κ : PlanarFrameKernels) (hκ : IsSeedKernels κ)
    {ν m b K t₁ s : ℝ} (hν : 0 < ν) (hm : 8 < m) (hb : 1 ≤ b)
    (hF : PerFrameFacts κ ν m b K) (ht₁ : 0 ≤ t₁) (hts : t₁ ≤ s) (hθs : b ≤ clockTheta ν s)
    (i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun r : ℝ => (perGram κ (dd ν r))⁻¹ i j) (Icc t₁ s) := by
  have hG : ∀ a' b' : Fin 2, ContDiffOn ℝ ∞ (fun d : ℝ => perGram κ d a' b') (Ici 1) :=
    perGramSmooth κ hκ
  have hdd_cd : ContDiffOn ℝ ∞ (fun r : ℝ => dd ν r) (Icc t₁ s) :=
    (contDiffOn_cellLen_clockA (ν ^ (-2 : ℝ)) hν.le).mono fun r hr => ht₁.trans hr.1
  have hdd_ge : MapsTo (fun r : ℝ => dd ν r) (Icc t₁ s) (Ici 1) := by
    intro r hr
    have hr0 : 0 ≤ r := ht₁.trans hr.1
    have hθr : b ≤ clockTheta ν r := hθs.trans (theta_anti hν hr0 hr.2)
    exact dd_ge_one_of_theta hν hb hr0 hθr
  have hG_r : ∀ a' b' : Fin 2, ContDiffOn ℝ ∞ (fun r : ℝ => perGram κ (dd ν r) a' b') (Icc t₁ s) :=
    fun a' b' => (hG a' b').comp hdd_cd hdd_ge
  have hdet : ContDiffOn ℝ ∞ (fun r : ℝ => (perGram κ (dd ν r)).det) (Icc t₁ s) := by
    have heq : (fun r : ℝ => (perGram κ (dd ν r)).det) =
        fun r => perGram κ (dd ν r) 0 0 * perGram κ (dd ν r) 1 1 -
          perGram κ (dd ν r) 0 1 * perGram κ (dd ν r) 1 0 := by
      funext r; exact Matrix.det_fin_two _
    rw [heq]
    exact ((hG_r 0 0).mul (hG_r 1 1)).sub ((hG_r 0 1).mul (hG_r 1 0))
  have hdet_ne : ∀ r ∈ Icc t₁ s, (perGram κ (dd ν r)).det ≠ 0 := by
    intro r hr
    have hr0 : 0 ≤ r := ht₁.trans hr.1
    have hθr : b ≤ clockTheta ν r := hθs.trans (theta_anti hν hr0 hr.2)
    exact perGram_det_ne_zero_of_perFrameFacts κ hκ hν hm hb hF hr0 hθr
  have hdet_inv : ContDiffOn ℝ ∞ (fun r : ℝ => ((perGram κ (dd ν r)).det)⁻¹) (Icc t₁ s) :=
    hdet.inv hdet_ne
  fin_cases i <;> fin_cases j
  · change ContDiffOn ℝ ∞ (fun r : ℝ => (perGram κ (dd ν r))⁻¹ 0 0) (Icc t₁ s)
    have hentry : (fun r : ℝ => (perGram κ (dd ν r))⁻¹ 0 0) =
        fun r => ((perGram κ (dd ν r)).det)⁻¹ * perGram κ (dd ν r) 1 1 := by
      funext r; rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]; rfl
    rw [hentry]; exact hdet_inv.mul (hG_r 1 1)
  · change ContDiffOn ℝ ∞ (fun r : ℝ => (perGram κ (dd ν r))⁻¹ 0 1) (Icc t₁ s)
    have hentry : (fun r : ℝ => (perGram κ (dd ν r))⁻¹ 0 1) =
        fun r => ((perGram κ (dd ν r)).det)⁻¹ * (-perGram κ (dd ν r) 0 1) := by
      funext r; rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]; rfl
    rw [hentry]; exact hdet_inv.mul (hG_r 0 1).neg
  · change ContDiffOn ℝ ∞ (fun r : ℝ => (perGram κ (dd ν r))⁻¹ 1 0) (Icc t₁ s)
    have hentry : (fun r : ℝ => (perGram κ (dd ν r))⁻¹ 1 0) =
        fun r => ((perGram κ (dd ν r)).det)⁻¹ * (-perGram κ (dd ν r) 1 0) := by
      funext r; rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]; rfl
    rw [hentry]; exact hdet_inv.mul (hG_r 1 0).neg
  · change ContDiffOn ℝ ∞ (fun r : ℝ => (perGram κ (dd ν r))⁻¹ 1 1) (Icc t₁ s)
    have hentry : (fun r : ℝ => (perGram κ (dd ν r))⁻¹ 1 1) =
        fun r => ((perGram κ (dd ν r)).det)⁻¹ * perGram κ (dd ν r) 0 0 := by
      funext r; rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]; rfl
    rw [hentry]; exact hdet_inv.mul (hG_r 0 0)

private theorem contDiffOn_physFrameLam_Ico
    (κ : PlanarFrameKernels) (hκ : IsSeedKernels κ)
    {ν m b K t₁ s : ℝ} (hν : 0 < ν) (hm : 8 < m) (hb : 1 ≤ b)
    (hF : PerFrameFacts κ ν m b K) (ht₁ : 0 ≤ t₁) (hts : t₁ ≤ s) (hθs : b ≤ clockTheta ν s)
    (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => physFrameLam κ ν p.1 i p.2) (Ico t₁ s ×ˢ univ) := by
  have hLam0 := physFrameLam0Smooth κ hκ hν ht₁
  have hGinv : ∀ j : Fin 2,
      ContDiffOn ℝ ∞ (fun r : ℝ => (perGram κ (dd ν r))⁻¹ i j) (Icc t₁ s) :=
    contDiffOn_perGram_inv_Icc κ hκ hν hm hb hF ht₁ hts hθs i
  have hsub : Ico t₁ s ×ˢ (univ : Set (ℝ × ℝ)) ⊆ Ici t₁ ×ˢ univ :=
    prod_mono Ico_subset_Ici_self Subset.rfl
  have hterm : ∀ j : Fin 2,
      ContDiffOn ℝ ∞
        (fun p : ℝ × (ℝ × ℝ) =>
          (perGram κ (dd ν p.1))⁻¹ i j *
            perSum (ν ^ (-2 : ℝ)) (physAdj (clockA ν p.1) (κ.lamP j)) p.2)
        (Ico t₁ s ×ˢ univ) := fun j =>
    ((hGinv j).comp contDiff_fst.contDiffOn (fun p hp => Ico_subset_Icc_self hp.1)).mul
      ((hLam0 j).mono hsub)
  refine ((hterm 0).add (hterm 1)).congr fun p hp => ?_
  have hp0 : 0 ≤ p.1 := ht₁.trans hp.1.1
  rw [physFrameLam_eq_sum_perGram_inv κ ν p.1 i p.2, Fin.sum_univ_two]
  congr 1
  · rw [physFrameLam0_eq_perSum_physAdj κ hν hp0 0 p.2]
  · rw [physFrameLam0_eq_perSum_physAdj κ hν hp0 1 p.2]

private theorem perPhys_bdd_on_cell {ν t₁ s : ℝ} (hν : 0 < ν) (ht₁ : 0 ≤ t₁) (hts : t₁ ≤ s)
    {L : ℝ × ℝ → ℂ} (hL : LamJetInf.Good L) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r ∈ Icc t₁ s, ∀ x ∈ B0579.cell (ν ^ (-2 : ℝ)),
      ‖LamJetInf.perPhys ν (ν ^ (-2 : ℝ)) L (r, x)‖ ≤ B := by
  set c : ℝ := ν ^ (-2 : ℝ)
  have hc0 : 0 < c := Real.rpow_pos_of_pos hν _
  obtain ⟨C, hC0, hC⟩ := hL.norm_le
  have ha_s : 1 ≤ clockA ν s := one_le_clockA hν.le (ht₁.trans hts)
  have hS_pos : 0 < 4 * max 1 (clockA ν s) := by positivity
  -- Bound `∑' n : ℤ, ((1 + |x.1 + n * c|) ^ 2)⁻¹` uniformly for `x.1 ∈ [0, c]`
  have hsum_nat : Summable (fun n : ℕ => ((1 + (n : ℝ) * c) ^ 2)⁻¹) := by
    have hpow2 : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹) := by
      have h := (Real.summable_nat_pow_inv.2 one_lt_two).comp_injective Nat.succ_injective
      simpa [Function.comp_def, Nat.cast_succ] using h
    refine Summable.of_norm_bounded (hpow2.mul_left ((min 1 c) ^ 2)⁻¹) fun n => ?_
    rw [Real.norm_of_nonneg (by positivity)]
    have hmc : 0 < min 1 c := lt_min zero_lt_one hc0
    have hle : min 1 c * ((n : ℝ) + 1) ≤ 1 + (n : ℝ) * c := by
      have h1 : min 1 c ≤ 1 := min_le_left _ _
      have h2 : min 1 c ≤ c := min_le_right _ _
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hsq : (min 1 c * ((n : ℝ) + 1)) ^ 2 ≤ (1 + (n : ℝ) * c) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hle 2
    calc ((1 + (n : ℝ) * c) ^ 2)⁻¹ ≤ ((min 1 c * ((n : ℝ) + 1)) ^ 2)⁻¹ :=
          inv_anti₀ (by positivity) hsq
      _ = ((min 1 c) ^ 2)⁻¹ * (((n : ℝ) + 1) ^ 2)⁻¹ := by rw [mul_pow, mul_inv]
  set S_nat : ℝ := ∑' n : ℕ, ((1 + (n : ℝ) * c) ^ 2)⁻¹
  have hS_nat0 : 0 ≤ S_nat := tsum_nonneg fun _ => by positivity
  set B : ℝ := clockA ν s * (C * (4 * max 1 (clockA ν s)) * (2 * S_nat + 1))
  refine ⟨B, by positivity, fun r hr x hx => ?_⟩
  have hr0 : 0 ≤ r := ht₁.trans hr.1
  have ha_r : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le hr0)
  have ha_rs : clockA ν r ≤ clockA ν s := clockA_mono hν.le hr.2
  rw [LamJetInf.perPhys_eq]
  have hsumm := LamJetInf.summable_good_shift (ν := ν) hc0.ne' hL (p := (r, x)) ha_r
  have hterm_eq : ∀ n : ℤ,
      LamJetInf.physTerm ν L ((r, x) + LamJetInf.shiftV c n) =
        ((clockA ν r : ℝ) : ℂ) * L (LamJetInf.iotaP ν ((r, x) + LamJetInf.shiftV c n)) := by
    intro n
    rw [LamJetInf.physTerm_eq]
    dsimp only
    rw [LamJetInf.shiftV_fst]
    rfl
  have htsum : ‖∑' n : ℤ, LamJetInf.physTerm ν L ((r, x) + LamJetInf.shiftV c n)‖ ≤
      clockA ν s * ∑' n : ℤ, C * (4 * max 1 (clockA ν s)) * ((1 + |x.1 + n * c|) ^ 2)⁻¹ := by
    calc ‖∑' n : ℤ, LamJetInf.physTerm ν L ((r, x) + LamJetInf.shiftV c n)‖
        ≤ ∑' n : ℤ, ‖LamJetInf.physTerm ν L ((r, x) + LamJetInf.shiftV c n)‖ := by
          refine norm_tsum_le_tsum_norm ?_
          simp_rw [hterm_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg ha_r.le]
          exact hsumm.norm.mul_left _
      _ ≤ ∑' n : ℤ, clockA ν s * (C * (4 * max 1 (clockA ν s)) * ((1 + |x.1 + n * c|) ^ 2)⁻¹) := by
          refine Summable.tsum_le_tsum (fun n => ?_) ?_ ?_
          · rw [hterm_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg ha_r.le]
            have h1 := hC (LamJetInf.iotaP ν ((r, x) + LamJetInf.shiftV c n))
            have hp : 0 < (1 + ‖LamJetInf.iotaP ν ((r, x) + LamJetInf.shiftV c n)‖) ^ 2 := by positivity
            have h2 : ‖L (LamJetInf.iotaP ν ((r, x) + LamJetInf.shiftV c n))‖ ≤
                C * ((1 + ‖LamJetInf.iotaP ν ((r, x) + LamJetInf.shiftV c n)‖) ^ 2)⁻¹ := by
              rw [← div_eq_mul_inv, le_div_iff₀ hp]; exact h1
            have hι := LamJetInf.inv_sq_iota_le (ν := ν) (q := (r, x) + LamJetInf.shiftV c n)
              (x₀ := x.1 + n * c) (A := clockA ν s)
              (by rw [LamJetInf.shiftV_fst]; exact ha_r)
              (by rw [LamJetInf.shiftV_fst]; exact ha_rs)
              (by rw [LamJetInf.shiftV_snd_fst]; simp)
            calc clockA ν r * ‖L (LamJetInf.iotaP ν ((r, x) + LamJetInf.shiftV c n))‖
                ≤ clockA ν s * (C * (4 * max 1 (clockA ν s) * ((1 + |x.1 + n * c|) ^ 2)⁻¹)) := by
                  gcongr
                  exact h2.trans (mul_le_mul_of_nonneg_left hι hC0)
              _ = clockA ν s * (C * (4 * max 1 (clockA ν s)) * ((1 + |x.1 + n * c|) ^ 2)⁻¹) := by ring
          · simp_rw [hterm_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg ha_r.le]
            exact hsumm.norm.mul_left _
          · exact ((LamJetInf.summable_inv_sq_shift hc0.ne' x.1).mul_left _).mul_left _
      _ = clockA ν s * ∑' n : ℤ, C * (4 * max 1 (clockA ν s)) * ((1 + |x.1 + n * c|) ^ 2)⁻¹ :=
          tsum_mul_left
  refine htsum.trans ?_
  rw [tsum_mul_left]
  have hZ : (∑' n : ℤ, ((1 + |x.1 + (n : ℝ) * c|) ^ 2)⁻¹) ≤ 2 * S_nat + 1 := by
    have hxn : -(c / 2) ≤ x.1 := hx.1.1
    have hxp : x.1 < c / 2 := hx.1.2
    have hsumZ := LamJetInf.summable_inv_sq_shift hc0.ne' x.1
    have hs_pos : Summable (fun n : ℕ => ((1 + |x.1 + (n : ℝ) * c|) ^ 2)⁻¹) :=
      hsumZ.comp_injective Nat.cast_injective
    have hs_neg : Summable (fun n : ℕ => ((1 + |x.1 + ((-(n + 1 : ℕ) : ℤ) : ℝ) * c|) ^ 2)⁻¹) :=
      hsumZ.comp_injective fun a b h => by omega
    have hsplit : (∑' n : ℤ, ((1 + |x.1 + (n : ℝ) * c|) ^ 2)⁻¹) =
        (∑' n : ℕ, ((1 + |x.1 + (n : ℝ) * c|) ^ 2)⁻¹) +
          (∑' n : ℕ, ((1 + |x.1 + ((-(n + 1 : ℕ) : ℤ) : ℝ) * c|) ^ 2)⁻¹) := by
      have hh := (hs_pos.hasSum.int_rec hs_neg.hasSum).tsum_eq
      rw [← hh]
      refine tsum_congr fun b => ?_
      cases b <;> rfl
    rw [hsplit]
    have hpos : (∑' n : ℕ, ((1 + |x.1 + (n : ℝ) * c|) ^ 2)⁻¹) ≤ S_nat + 1 := by
      rw [hs_pos.tsum_eq_zero_add]
      have h0 : ((1 + |x.1 + ((0 : ℕ) : ℝ) * c|) ^ 2)⁻¹ ≤ 1 := by
        rw [inv_le_one_iff₀]; right
        have : 0 ≤ |x.1 + ((0 : ℕ) : ℝ) * c| := abs_nonneg _
        nlinarith
      have hsucc : (∑' n : ℕ, ((1 + |x.1 + ((n + 1 : ℕ) : ℝ) * c|) ^ 2)⁻¹) ≤ S_nat := by
        refine Summable.tsum_le_tsum (fun n => ?_) ?_ hsum_nat
        · gcongr
          have hnn : 0 ≤ x.1 + ((n + 1 : ℕ) : ℝ) * c := by
            push_cast
            have hn0 : 0 ≤ (n : ℝ) * c := mul_nonneg (Nat.cast_nonneg n) hc0.le
            linarith
          rw [abs_of_nonneg hnn]
          push_cast; linarith
        · exact hs_pos.comp_injective Nat.succ_injective
      linarith
    have hneg : (∑' n : ℕ, ((1 + |x.1 + ((-(n + 1 : ℕ) : ℤ) : ℝ) * c|) ^ 2)⁻¹) ≤ S_nat := by
      refine Summable.tsum_le_tsum (fun n => ?_) hs_neg hsum_nat
      gcongr
      have h1 : x.1 + ((-(n + 1 : ℕ) : ℤ) : ℝ) * c ≤ -(n : ℝ) * c := by
        push_cast; linarith
      calc (n : ℝ) * c = -(-(n : ℝ) * c) := by ring
        _ ≤ -(x.1 + ((-(n + 1 : ℕ) : ℤ) : ℝ) * c) := neg_le_neg h1
        _ ≤ |x.1 + ((-(n + 1 : ℕ) : ℤ) : ℝ) * c| := neg_le_abs _
    linarith
  have hpos1 : 0 ≤ clockA ν s := ha_s.trans' zero_le_one
  have hpos1 : 0 ≤ clockA ν s := ha_s.trans' zero_le_one
  have hpos2 : 0 ≤ C * (4 * max 1 (clockA ν s)) := by positivity
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hZ hpos2) hpos1

private theorem memLp_and_xNorm_cell_bdd_of_cont {m c B : ℝ} (hm : 1 < m) (hB0 : 0 ≤ B)
    {F : ℝ × ℝ → ℂ} (hFc : Continuous F) (hB : ∀ y ∈ B0579.cell c, ‖F y‖ ≤ B) :
    MemLp F 2 (B0579.cellMeasure c (-m)) ∧
    xNorm c (-m) F ≤ ENNReal.ofReal ((B0592.weightConst m).toReal * B) :=
  ComplCouplingHeat.memLp_and_xNorm_neg_le_of_cell_bdd hm hB0
    hFc.aestronglyMeasurable.restrict hB

theorem integrableOn_amplRate_and_dual
    (κ : PlanarFrameKernels) (hκ : IsSeedKernels κ)
    {ν m b K : ℝ} (hm : 8 < m) (hν : 0 < ν) (hb : 1 ≤ b)
    (hF : PerFrameFacts κ ν m b K)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (_htr : PartI.IsBUCTrain tr)
    (hBddAll : ∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C)
    {t₁ t₂ s : ℝ} (ht₁ : 0 ≤ t₁) (hs : s ∈ Icc t₁ t₂) (hbt₂ : b ≤ clockTheta ν t₂)
    {f : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u)
    (hf0 : HasZeroCirculation (ν ^ (-2 : ℝ)) f) (i : Fin 2) :
    IntegrableOn
      (fun q => (((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) * movH0 κ tr q i (movingW ν w q))
      (Ioc t₁ s) ∧
    (∀ ρ ∈ Ioo t₁ s, MemLp (physLamDual κ tr ρ i) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))) := by
  rcases eq_or_lt_of_le hs.1 with rfl | ht₁s
  · exact ⟨by simp, fun ρ hρ => False.elim (lt_asymm hρ.1 hρ.2)⟩
  have hs0 : 0 ≤ s := ht₁.trans hs.1
  have hbs : b ≤ clockTheta ν s := hbt₂.trans (theta_anti hν hs0 hs.2)
  have hν1 : ν ≤ 1 := nu_le_one_of_theta hν hb hs0 hbs
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc1 : 1 ≤ c := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by norm_num)
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  obtain ⟨C_tr, hBdd⟩ := hBddAll s hs0
  have hC_tr0 : 0 ≤ C_tr :=
    le_trans (abs_nonneg _) ((hBdd s ⟨hs0, le_rfl⟩ (0, 0) ⟨⟨by linarith, by linarith⟩, trivial⟩).1 0)
  have hwc : ContinuousOn (fun ρ => (xNorm c m (w ρ)).toReal) (Ici t₁) :=
    RateBoundAux.contOn_norm w (fun ρ h => hw.memX ρ h) (fun ρ h => hw.strongCont ρ h)
  obtain ⟨A_w, hA_w0, hA_w⟩ :=
    RateBoundAux.bdd_of_cont (hwc.mono (Icc_subset_Ici_self : Icc t₁ s ⊆ Ici t₁))
  obtain ⟨Cl, hCl⟩ := ladVelLip m hm ν c tr t₁ f w u hc1 hf0 hw
  have hu2 : ∀ ρ, t₁ ≤ ρ → ∀ j : Fin 2,
      MemLp (fun x => u ρ x j) 2 (volume.restrict (B0579.cell c)) :=
    fun ρ h j => (hw.biotSavart ρ h).1 j
  have hAe : ∀ ρ ∈ Icc t₁ s, xNorm c m (w ρ) ≤ ENNReal.ofReal A_w := fun ρ hρ =>
    RateBoundAux.ofReal_toReal_le (hw.memX ρ hρ.1).eLpNorm_ne_top hA_w0 (hA_w ρ hρ)
  have hU : ∀ ρ ∈ Icc t₁ s, ∀ j : Fin 2,
      eLpNorm (fun x => u ρ x j) 2 (volume.restrict (B0579.cell c)) ≤
        ENNReal.ofReal Cl * (ENNReal.ofReal A_w + ENNReal.ofReal A_w) +
          eLpNorm (fun x => u t₁ x j) 2 (volume.restrict (B0579.cell c)) := by
    intro ρ hρ j
    have h1 := eLpNorm_add_le (p := 2) (μ := volume.restrict (B0579.cell c))
      ((hu2 ρ hρ.1 j).1.sub (hu2 t₁ le_rfl j).1) (hu2 t₁ le_rfl j).1 one_le_two
    rw [sub_add_cancel] at h1
    have h2 : eLpNorm ((fun x => u ρ x j) - fun x => u t₁ x j) 2
        (volume.restrict (B0579.cell c)) ≤ ENNReal.ofReal Cl * xNorm c m (w ρ - w t₁) :=
      hCl ρ t₁ hρ.1 le_rfl j
    have h3 : xNorm c m (w ρ - w t₁) ≤ xNorm c m (w ρ) + xNorm c m (w t₁) :=
      eLpNorm_sub_le (hw.memX ρ hρ.1).1 (hw.memX t₁ le_rfl).1 one_le_two
    have h4 : xNorm c m (w ρ - w t₁) ≤ ENNReal.ofReal A_w + ENNReal.ofReal A_w :=
      h3.trans (add_le_add (hAe ρ hρ) (hAe t₁ ⟨le_rfl, hs.1⟩))
    exact h1.trans (add_le_add (h2.trans (mul_le_mul' le_rfl h4)) le_rfl)
  set Fe : ℝ≥0∞ := ENNReal.ofReal C_tr *
    ((ENNReal.ofReal Cl * (ENNReal.ofReal A_w + ENNReal.ofReal A_w) +
        eLpNorm (fun x => u t₁ x 0) 2 (volume.restrict (B0579.cell c))) +
      (ENNReal.ofReal Cl * (ENNReal.ofReal A_w + ENNReal.ofReal A_w) +
        eLpNorm (fun x => u t₁ x 1) 2 (volume.restrict (B0579.cell c))))
  have hFe : Fe ≠ ⊤ := by
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.2 ⟨?_, ?_⟩) <;>
      exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩),
        (hu2 t₁ le_rfl _).eLpNorm_ne_top⟩
  have hforce : ∀ ρ ∈ Icc t₁ s, MemLp (ladForce tr (u ρ) ρ) 2 (B0579.cellMeasure c m) ∧
      (xNorm c m (ladForce tr (u ρ) ρ)).toReal ≤ Fe.toReal := by
    intro ρ hρ
    obtain ⟨h1, h2⟩ := ladForceMemX m ν c tr s C_tr ρ hBdd ⟨ht₁.trans hρ.1, hρ.2⟩ (u ρ)
      (fun j => hu2 ρ hρ.1 j)
    exact ⟨h1, ENNReal.toReal_mono hFe
      (h2.trans (mul_le_mul' le_rfl (add_le_add (hU ρ hρ 0) (hU ρ hρ 1))))⟩
  -- Smoothness of `physFrameLam` on `Ico t₁ s ×ˢ univ`
  have hSmooth : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => physFrameLam κ ν p.1 i p.2)
      (Ico t₁ s ×ˢ univ) :=
    contDiffOn_physFrameLam_Ico κ hκ hν hm hb hF ht₁ hs.1 hbs i
  -- Gram-inverse and its derivative bounds on `Icc t₁ s` / `Ioo t₁ s`
  have hGinv_bd : ∃ M_G : ℝ, 0 ≤ M_G ∧ ∀ ρ ∈ Icc t₁ s, ∀ j : Fin 2,
      ‖(perGram κ (dd ν ρ))⁻¹ i j‖ ≤ M_G := by
    have h0 : ContinuousOn (fun ρ => ‖(perGram κ (dd ν ρ))⁻¹ i 0‖) (Icc t₁ s) :=
      (contDiffOn_perGram_inv_Icc κ hκ hν hm hb hF ht₁ hs.1 hbs i 0).continuousOn.norm
    have h1 : ContinuousOn (fun ρ => ‖(perGram κ (dd ν ρ))⁻¹ i 1‖) (Icc t₁ s) :=
      (contDiffOn_perGram_inv_Icc κ hκ hν hm hb hF ht₁ hs.1 hbs i 1).continuousOn.norm
    obtain ⟨B0, hB0⟩ := isCompact_Icc.bddAbove_image h0
    obtain ⟨B1, hB1⟩ := isCompact_Icc.bddAbove_image h1
    refine ⟨max (max B0 B1) 0, le_max_right _ _, fun ρ hρ j => ?_⟩
    fin_cases j
    · exact (hB0 ⟨ρ, hρ, rfl⟩).trans ((le_max_left _ _).trans (le_max_left _ _))
    · exact (hB1 ⟨ρ, hρ, rfl⟩).trans ((le_max_right _ _).trans (le_max_left _ _))
  obtain ⟨M_G, hM_G0, hGinv⟩ := hGinv_bd
  have hGder_bd : ∃ M_Gd : ℝ, 0 ≤ M_Gd ∧ ∀ ρ ∈ Ioo t₁ s, ∀ j : Fin 2,
      ‖derivWithin (fun r' => (perGram κ (dd ν r'))⁻¹ i j) (Ici ρ) ρ‖ ≤ M_Gd := by
    have hfd : ∀ j : Fin 2, ContinuousOn
        (fun ρ => ‖fderivWithin ℝ (fun r' => (perGram κ (dd ν r'))⁻¹ i j) (Icc t₁ s) ρ 1‖)
        (Icc t₁ s) := by
      intro j
      have hcd := (contDiffOn_perGram_inv_Icc κ hκ hν hm hb hF ht₁ hs.1 hbs i j).continuousOn_fderivWithin
        (uniqueDiffOn_Icc ht₁s) (by simp)
      exact (hcd.clm_apply continuousOn_const).norm
    obtain ⟨B0, hB0⟩ := isCompact_Icc.bddAbove_image (hfd 0)
    obtain ⟨B1, hB1⟩ := isCompact_Icc.bddAbove_image (hfd 1)
    refine ⟨max (max B0 B1) 0, le_max_right _ _, fun ρ hρ j => ?_⟩
    have hρ_Icc : ρ ∈ Icc t₁ s := Ioo_subset_Icc_self hρ
    have hcd := (contDiffOn_perGram_inv_Icc κ hκ hν hm hb hF ht₁ hs.1 hbs i j).differentiableOn
      (by simp)
    have hd_at : DifferentiableAt ℝ (fun r' => (perGram κ (dd ν r'))⁻¹ i j) ρ :=
      hcd.differentiableAt (Icc_mem_nhds hρ.1 hρ.2)
    have h_eq : derivWithin (fun r' => (perGram κ (dd ν r'))⁻¹ i j) (Ici ρ) ρ =
        fderivWithin ℝ (fun r' => (perGram κ (dd ν r'))⁻¹ i j) (Icc t₁ s) ρ 1 := by
      rw [hd_at.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici ρ),
        hd_at.hasDerivAt.hasFDerivAt.hasFDerivWithinAt.fderivWithin (uniqueDiffOn_Icc ht₁s ρ hρ_Icc)]
      simp
    rw [h_eq]
    fin_cases j
    · exact (hB0 ⟨ρ, hρ_Icc, rfl⟩).trans ((le_max_left _ _).trans (le_max_left _ _))
    · exact (hB1 ⟨ρ, hρ_Icc, rfl⟩).trans ((le_max_right _ _).trans (le_max_left _ _))
  obtain ⟨M_Gd, hM_Gd0, hGder⟩ := hGder_bd
  -- Uniform cell bounds for `perPhys` of `κ.lamP` and its first/second derivatives and `eulerK`
  have hGood : ∀ j : Fin 2, LamJetInf.Good (κ.lamP j) := fun j => LamJetInf.good_lamP hκ j
  have hB0 : ∀ j : Fin 2, ∃ B, 0 ≤ B ∧ ∀ r ∈ Icc t₁ s, ∀ x ∈ B0579.cell c,
      ‖LamJetInf.perPhys ν c (κ.lamP j) (r, x)‖ ≤ B :=
    fun j => perPhys_bdd_on_cell hν ht₁ hs.1 (hGood j)
  have hB1 : ∀ j k : Fin 2, ∃ B, 0 ≤ B ∧ ∀ r ∈ Icc t₁ s, ∀ x ∈ B0579.cell c,
      ‖LamJetInf.perPhys ν c (fun z => fderiv ℝ (κ.lamP j) z (B0579.dir k)) (r, x)‖ ≤ B :=
    fun j k => perPhys_bdd_on_cell hν ht₁ hs.1 ((hGood j).fderiv_apply (B0579.dir k))
  have hB2 : ∀ j k : Fin 2, ∃ B, 0 ≤ B ∧ ∀ r ∈ Icc t₁ s, ∀ x ∈ B0579.cell c,
      ‖LamJetInf.perPhys ν c
        (fun z => fderiv ℝ (fun z' => fderiv ℝ (κ.lamP j) z' (B0579.dir k)) z (B0579.dir k))
        (r, x)‖ ≤ B :=
    fun j k => perPhys_bdd_on_cell hν ht₁ hs.1
      (((hGood j).fderiv_apply (B0579.dir k)).fderiv_apply (B0579.dir k))
  have hBE : ∀ j : Fin 2, ∃ B, 0 ≤ B ∧ ∀ r ∈ Icc t₁ s, ∀ x ∈ B0579.cell c,
      ‖LamJetInf.perPhys ν c (LamJetInf.eulerK (κ.lamP j)) (r, x)‖ ≤ B :=
    fun j => perPhys_bdd_on_cell hν ht₁ hs.1 (hGood j).eulerK
  choose B0 hB0_pos hB0_le using hB0
  choose B1 hB1_pos hB1_le using hB1
  choose B2 hB2_pos hB2_le using hB2
  choose BE hBE_pos hBE_le using hBE
  set B_lam : ℝ := M_G * (B0 0 + B0 1)
  set B_g : ℝ := M_G * (max (B1 0 0) (B1 0 1) + max (B1 1 0) (B1 1 1))
  set B_lap : ℝ := M_G * ((B2 0 0 + B2 0 1) + (B2 1 0 + B2 1 1))
  set B_dt : ℝ := M_G * (|ν| * (BE 0 + BE 1)) + M_Gd * (B0 0 + B0 1)
  set B_tr : ℝ := 2 * C_tr * B_g
  have hB_lam0 : 0 ≤ B_lam := mul_nonneg hM_G0 (add_nonneg (hB0_pos 0) (hB0_pos 1))
  have hB_g0 : 0 ≤ B_g := mul_nonneg hM_G0 (add_nonneg (le_max_of_le_left (hB1_pos 0 0)) (le_max_of_le_left (hB1_pos 1 0)))
  have hB_lap0 : 0 ≤ B_lap := mul_nonneg hM_G0 (add_nonneg (add_nonneg (hB2_pos 0 0) (hB2_pos 0 1)) (add_nonneg (hB2_pos 1 0) (hB2_pos 1 1)))
  have hB_dt0 : 0 ≤ B_dt := add_nonneg (mul_nonneg hM_G0 (mul_nonneg (abs_nonneg ν) (add_nonneg (hBE_pos 0) (hBE_pos 1)))) (mul_nonneg hM_Gd0 (add_nonneg (hB0_pos 0) (hB0_pos 1)))
  have hB_tr0 : 0 ≤ B_tr := mul_nonneg (mul_nonneg (by norm_num) hC_tr0) hB_g0
  set W_c : ℝ := (B0592.weightConst m).toReal
  have hW_c0 : 0 ≤ W_c := ENNReal.toReal_nonneg
  set M_φ : ℝ := W_c * B_lam
  set M_g : ℝ := W_c * B_g
  have hM_φ0 : 0 ≤ M_φ := mul_nonneg hW_c0 hB_lam0
  have hM_g0 : 0 ≤ M_g := mul_nonneg hW_c0 hB_g0
  obtain ⟨M_ker, hM_ker0, hKerAll⟩ := kerAdj_memLp_and_transposition (K_Φ := M_φ)
    hm hc1 hC_tr0 hM_φ0 hBdd
  set M_ND : ℝ := W_c * (B_dt + |ν| * B_lap + B_tr) + M_ker
  have hM_ND0 : 0 ≤ M_ND := add_nonneg (mul_nonneg hW_c0 (add_nonneg (add_nonneg hB_dt0 (mul_nonneg (abs_nonneg ν) hB_lap0)) hB_tr0)) hM_ker0
  let φ : ℝ → ℝ × ℝ → ℂ := fun r' x' => physFrameLam κ ν r' i x'
  have hφ_smooth : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t₁ s ×ˢ univ) :=
    hSmooth
  have hφ_per : ∀ ρ ∈ Ico t₁ s, ∀ x : ℝ × ℝ, φ ρ (x.1 + c, x.2) = φ ρ x := fun ρ hρ x =>
    physFrameLam_periodic κ hν (ht₁.trans hρ.1) i x
  obtain ⟨K_cut, hK_cut0, hK_cut⟩ := ladCutProps
  have hprod_r' : ∀ r' ∈ Ico t₁ s, ∀ R : ℝ, 0 < R →
      IntervalIntegrable (ladRate tr w u φ R) volume t₁ r' := by
    intro r' hr' R hR
    exact (ladProductRule ν c m tr t₁ s f w u φ hν hc0 ht₁ ht₁s hw ⟨Cl, hCl⟩
      hφ_smooth hφ_per R hR r' hr').1
  -- Pointwise bounds on `physFrameLam`, `pdCx`, and `physLamDual` for `ρ ∈ Ioo t₁ s`
  have hLam_bd : ∀ ρ ∈ Ioo t₁ s,
      MemLp (physFrameLam κ ν ρ i) 2 (B0579.cellMeasure c (-m)) ∧
      xNorm c (-m) (physFrameLam κ ν ρ i) ≤ ENNReal.ofReal M_φ := by
    intro ρ hρ
    have hρ_Icc : ρ ∈ Icc t₁ s := Ioo_subset_Icc_self hρ
    have hρ0 : 0 ≤ ρ := ht₁.trans hρ_Icc.1
    have hslice : ContDiff ℝ ∞ (physFrameLam κ ν ρ i) :=
      RateSplitAux.contDiff_slice (φ := fun r' x' => physFrameLam κ ν r' i x')
        (Ioo_subset_Ico_self hρ) hSmooth
    refine memLp_and_xNorm_cell_bdd_of_cont (by linarith) (by positivity)
      hslice.continuous fun x hx => ?_
    rw [physFrameLam_eq_sum_perGram_inv κ ν ρ i x, Fin.sum_univ_two]
    have h0 : ComplCouplingHeat.physFrameLam0 κ ν ρ 0 x = LamJetInf.perPhys ν c (κ.lamP 0) (ρ, x) :=
      physFrameLam0_eq_perSum_physAdj κ hν hρ0 0 x
    have h1 : ComplCouplingHeat.physFrameLam0 κ ν ρ 1 x = LamJetInf.perPhys ν c (κ.lamP 1) (ρ, x) :=
      physFrameLam0_eq_perSum_physAdj κ hν hρ0 1 x
    rw [h0, h1]
    calc ‖(perGram κ (dd ν ρ))⁻¹ i 0 * LamJetInf.perPhys ν c (κ.lamP 0) (ρ, x) +
          (perGram κ (dd ν ρ))⁻¹ i 1 * LamJetInf.perPhys ν c (κ.lamP 1) (ρ, x)‖
        ≤ ‖(perGram κ (dd ν ρ))⁻¹ i 0‖ * ‖LamJetInf.perPhys ν c (κ.lamP 0) (ρ, x)‖ +
          ‖(perGram κ (dd ν ρ))⁻¹ i 1‖ * ‖LamJetInf.perPhys ν c (κ.lamP 1) (ρ, x)‖ :=
          (norm_add_le _ _).trans (by rw [norm_mul, norm_mul])
      _ ≤ M_G * B0 0 + M_G * B0 1 := by
          gcongr
          · exact hGinv ρ hρ_Icc 0
          · exact hB0_le 0 ρ hρ_Icc x hx
          · exact hGinv ρ hρ_Icc 1
          · exact hB0_le 1 ρ hρ_Icc x hx
      _ = B_lam := by ring
  have hpd_bd : ∀ ρ ∈ Ioo t₁ s, ∀ k : Fin 2,
      MemLp (pdCx k (physFrameLam κ ν ρ i)) 2 (B0579.cellMeasure c (-m)) ∧
      xNorm c (-m) (pdCx k (physFrameLam κ ν ρ i)) ≤ ENNReal.ofReal M_g := by
    intro ρ hρ k
    have hρ_Icc : ρ ∈ Icc t₁ s := Ioo_subset_Icc_self hρ
    have hρ0 : 0 ≤ ρ := ht₁.trans hρ_Icc.1
    have ha_r : 0 < clockA ν ρ := lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le hρ0)
    have ha_inv_sqrt : (Real.sqrt (clockA ν ρ))⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (one_le_clockA hν.le hρ0))
    have hslice : ContDiff ℝ ∞ (physFrameLam κ ν ρ i) :=
      RateSplitAux.contDiff_slice (φ := fun r' x' => physFrameLam κ ν r' i x')
        (Ioo_subset_Ico_self hρ) hSmooth
    refine memLp_and_xNorm_cell_bdd_of_cont (by linarith) (by positivity)
      (RateSplitAux.contDiff_pdCx hslice k).continuous fun x hx => ?_
    have hsum_fn : physFrameLam κ ν ρ i = fun x' =>
        (perGram κ (dd ν ρ))⁻¹ i 0 * LamJetInf.perPhys ν c (κ.lamP 0) (ρ, x') +
        (perGram κ (dd ν ρ))⁻¹ i 1 * LamJetInf.perPhys ν c (κ.lamP 1) (ρ, x') := by
      funext x'
      rw [physFrameLam_eq_sum_perGram_inv κ ν ρ i x', Fin.sum_univ_two,
        physFrameLam0_eq_perSum_physAdj κ hν hρ0 0 x',
        physFrameLam0_eq_perSum_physAdj κ hν hρ0 1 x']
      rfl
    have hcd_lam : ∀ j : Fin 2, Differentiable ℝ (fun x' => LamJetInf.perPhys ν c (κ.lamP j) (ρ, x')) := by
      intro j x'
      have hd := ((LamJetInf.contDiffOn_perPhys hν hc0.ne' (hGood j)).differentiableOn
        (by simp)).differentiableAt ((LamJetInf.isOpen_physU ν).mem_nhds
          (show (ρ, x') ∈ LamJetInf.physU ν from ha_r))
      exact hd.comp x' (differentiableAt_const ρ |>.prodMk differentiableAt_id)
    rw [hsum_fn, RateSplitAux.pdCx_add k ((hcd_lam 0 x).const_mul _) ((hcd_lam 1 x).const_mul _),
      pdCx_const_mul _ _ k x (hcd_lam 0 x), pdCx_const_mul _ _ k x (hcd_lam 1 x)]
    have hpd_per : ∀ j : Fin 2,
        pdCx k (fun x' => LamJetInf.perPhys ν c (κ.lamP j) (ρ, x')) x =
          ((Real.sqrt (clockA ν ρ)⁻¹ : ℝ) : ℂ) *
            LamJetInf.perPhys ν c (fun z => fderiv ℝ (κ.lamP j) z (B0579.dir k)) (ρ, x) := by
      intro j
      have hd := ((LamJetInf.contDiffOn_perPhys hν hc0.ne' (hGood j)).differentiableOn
        (by simp)).differentiableAt ((LamJetInf.isOpen_physU ν).mem_nhds
          (show (ρ, x) ∈ LamJetInf.physU ν from ha_r))
      have hfd : pdCx k (fun x' => LamJetInf.perPhys ν c (κ.lamP j) (ρ, x')) x =
          fderiv ℝ (LamJetInf.perPhys ν c (κ.lamP j)) (ρ, x) (0, B0579.dir k) := by
        unfold pdCx
        have hcomp : HasFDerivAt (fun x' => LamJetInf.perPhys ν c (κ.lamP j) (ρ, x'))
            ((fderiv ℝ (LamJetInf.perPhys ν c (κ.lamP j)) (ρ, x)).comp
              (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) x :=
          hd.hasFDerivAt.comp x (hasFDerivAt_const ρ x |>.prodMk (hasFDerivAt_id x))
        rw [hcomp.fderiv]; rfl
      rw [hfd, LamJetInf.fderiv_perPhys_apply hν hc0.ne' (hGood j) ha_r]
      simp only [mul_zero, zero_mul, Complex.ofReal_zero, zero_add, Real.sqrt_inv]
      congr 2
      field_simp [(Real.sqrt_pos.2 ha_r).ne']
      rw [Real.sq_sqrt ha_r.le]
    rw [hpd_per 0, hpd_per 1]
    have hnorm0 : ‖((Real.sqrt (clockA ν ρ)⁻¹ : ℝ) : ℂ) *
        LamJetInf.perPhys ν c (fun z => fderiv ℝ (κ.lamP 0) z (B0579.dir k)) (ρ, x)‖ ≤
        max (B1 0 0) (B1 0 1) := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), Real.sqrt_inv]
      calc (Real.sqrt (clockA ν ρ))⁻¹ * _
          ≤ 1 * B1 0 k := mul_le_mul ha_inv_sqrt (hB1_le 0 k ρ hρ_Icc x hx) (norm_nonneg _) zero_le_one
        _ ≤ max (B1 0 0) (B1 0 1) := by fin_cases k <;> simp [le_max_left, le_max_right]
    have hnorm1 : ‖((Real.sqrt (clockA ν ρ)⁻¹ : ℝ) : ℂ) *
        LamJetInf.perPhys ν c (fun z => fderiv ℝ (κ.lamP 1) z (B0579.dir k)) (ρ, x)‖ ≤
        max (B1 1 0) (B1 1 1) := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), Real.sqrt_inv]
      calc (Real.sqrt (clockA ν ρ))⁻¹ * _
          ≤ 1 * B1 1 k := mul_le_mul ha_inv_sqrt (hB1_le 1 k ρ hρ_Icc x hx) (norm_nonneg _) zero_le_one
        _ ≤ max (B1 1 0) (B1 1 1) := by fin_cases k <;> simp [le_max_left, le_max_right]
    calc ‖(perGram κ (dd ν ρ))⁻¹ i 0 * _ + (perGram κ (dd ν ρ))⁻¹ i 1 * _‖
        ≤ ‖(perGram κ (dd ν ρ))⁻¹ i 0‖ * ‖_‖ + ‖(perGram κ (dd ν ρ))⁻¹ i 1‖ * ‖_‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ M_G * max (B1 0 0) (B1 0 1) + M_G * max (B1 1 0) (B1 1 1) :=
          add_le_add (mul_le_mul (hGinv ρ hρ_Icc 0) hnorm0 (norm_nonneg _) hM_G0)
            (mul_le_mul (hGinv ρ hρ_Icc 1) hnorm1 (norm_nonneg _) hM_G0)
      _ = B_g := by ring
  have hDual_bd : ∀ ρ ∈ Ioo t₁ s,
      MemLp (physLamDual κ tr ρ i) 2 (B0579.cellMeasure c (-m)) ∧
      xNorm c (-m) (physLamDual κ tr ρ i) ≤ ENNReal.ofReal M_ND := by
    intro ρ hρ
    have hρ_Icc : ρ ∈ Icc t₁ s := Ioo_subset_Icc_self hρ
    have hρ0 : 0 ≤ ρ := ht₁.trans hρ_Icc.1
    have hρS : ρ ∈ Icc (0 : ℝ) s := ⟨hρ0, hρ_Icc.2⟩
    have ha_r : 0 < clockA ν ρ := lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le hρ0)
    have ha_inv_le : (clockA ν ρ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_clockA hν.le hρ0)
    have hslice : ContDiff ℝ ∞ (physFrameLam κ ν ρ i) :=
      RateSplitAux.contDiff_slice (φ := fun r' x' => physFrameLam κ ν r' i x')
        (Ioo_subset_Ico_self hρ) hSmooth
    -- Split `physLamDual = (ladDt + ν * ladLapCx + ladTransport) - kerAdj`
    have hKer := hKerAll hρS (hLam_bd ρ hρ).1 (hLam_bd ρ hρ).2
    have hL_good : ∀ j : Fin 2, Differentiable ℝ (κ.lamP j) := fun j =>
      ((LamJetInf.good_lamP hκ j).1.differentiable (by simp))
    have hL_cont2 : ∀ j : Fin 2, ContDiff ℝ 2 (κ.lamP j) := fun j =>
      (LamJetInf.good_lamP hκ j).1.of_le (by simp)
    -- Use `memLp_and_xNorm_cell_bdd_of_cont` for `ladDt + ν * ladLapCx` and `ladTransport`
    have hMain_cont : Continuous (fun x =>
        ladDt (fun r' x' => physFrameLam κ ν r' i x') ρ x +
          (ν : ℂ) * ladLapCx (physFrameLam κ ν ρ i) x) := by
      have hU : IsOpen (Ioo t₁ s ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioo.prod isOpen_univ
      have hsub : Ioo t₁ s ×ˢ (univ : Set (ℝ × ℝ)) ⊆ Ico t₁ s ×ˢ univ :=
        prod_mono Ioo_subset_Ico_self Subset.rfl
      have hdt_cont : Continuous (fun x => ladDt (fun r' x' => physFrameLam κ ν r' i x') ρ x) := by
        have hcd := ((hSmooth.mono hsub).continuousOn_fderiv_of_isOpen hU (by simp))
        have heq : (fun x => ladDt (fun r' x' => physFrameLam κ ν r' i x') ρ x) =
            fun x => fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => physFrameLam κ ν p.1 i p.2) (ρ, x) (1, 0) := by
          funext x
          have hd := ((hSmooth.mono hsub).differentiableOn (by simp)).differentiableAt
            (hU.mem_nhds (show (ρ, x) ∈ Ioo t₁ s ×ˢ (univ : Set (ℝ × ℝ)) from ⟨hρ, mem_univ _⟩))
          have h1 : HasDerivAt (fun r' => physFrameLam κ ν r' i x)
              (fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => physFrameLam κ ν p.1 i p.2) (ρ, x) (1, 0)) ρ := by
            have hl : HasDerivAt (fun r' : ℝ => (r', x)) ((1 : ℝ), (0 : ℝ × ℝ)) ρ :=
              (hasDerivAt_id ρ).prodMk (hasDerivAt_const ρ x)
            exact hd.hasFDerivAt.comp_hasDerivAt ρ hl
          exact h1.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici ρ)
        rw [heq]
        exact (hcd.clm_apply continuousOn_const).comp_continuous (continuous_const.prodMk continuous_id)
          fun x => ⟨hρ, mem_univ x⟩
      have hlap_cont : Continuous (ladLapCx (physFrameLam κ ν ρ i)) :=
        (RateSplitAux.contDiff_pdCx (RateSplitAux.contDiff_pdCx hslice 0) 0).continuous.add
          (RateSplitAux.contDiff_pdCx (RateSplitAux.contDiff_pdCx hslice 1) 1).continuous
      exact hdt_cont.add (continuous_const.mul hlap_cont)
    have hMain_bd : ∀ x ∈ B0579.cell c,
        ‖ladDt (fun r' x' => physFrameLam κ ν r' i x') ρ x +
          (ν : ℂ) * ladLapCx (physFrameLam κ ν ρ i) x‖ ≤ B_dt + |ν| * B_lap := by
      intro x hx
      have hcd_per : ∀ j : Fin 2, Differentiable ℝ
          (fun x' => LamJetInf.perPhys ν c (κ.lamP j) (ρ, x')) := by
        intro j x'
        have hd := ((LamJetInf.contDiffOn_perPhys hν hc0.ne' (hGood j)).differentiableOn
          (by simp)).differentiableAt ((LamJetInf.isOpen_physU ν).mem_nhds
            (show (ρ, x') ∈ LamJetInf.physU ν from ha_r))
        exact hd.comp x' (differentiableAt_const ρ |>.prodMk differentiableAt_id)
      have hcd_per1 : ∀ j k : Fin 2, Differentiable ℝ
          (fun x' => LamJetInf.perPhys ν c (fun z => fderiv ℝ (κ.lamP j) z (B0579.dir k)) (ρ, x')) := by
        intro j k x'
        have hd := ((LamJetInf.contDiffOn_perPhys hν hc0.ne'
          ((hGood j).fderiv_apply (B0579.dir k))).differentiableOn
          (by simp)).differentiableAt ((LamJetInf.isOpen_physU ν).mem_nhds
            (show (ρ, x') ∈ LamJetInf.physU ν from ha_r))
        exact hd.comp x' (differentiableAt_const ρ |>.prodMk differentiableAt_id)
      have hdt_eq : ladDt (fun r' x' => physFrameLam κ ν r' i x') ρ x =
          ∑ j : Fin 2,
            (deriv (fun r' => (perGram κ (dd ν r'))⁻¹ i j) ρ *
              LamJetInf.perPhys ν c (κ.lamP j) (ρ, x) +
            (perGram κ (dd ν ρ))⁻¹ i j *
              (((ν * (clockA ν ρ)⁻¹ : ℝ) : ℂ) *
                LamJetInf.perPhys ν c (LamJetInf.eulerK (κ.lamP j)) (ρ, x))) := by
        have ht_nhds : Ioo t₁ s ∈ 𝓝 ρ := Ioo_mem_nhds hρ.1 hρ.2
        have hfn_ev : (fun r' => physFrameLam κ ν r' i x) =ᶠ[𝓝 ρ] fun r' =>
            ∑ j : Fin 2, (perGram κ (dd ν r'))⁻¹ i j * LamJetInf.perPhys ν c (κ.lamP j) (r', x) := by
          refine Filter.eventually_of_mem ht_nhds fun r' hr' => ?_
          dsimp only [dd]
          rw [physFrameLam_eq_sum_perGram_inv κ ν r' i x]
          refine Finset.sum_congr rfl fun j _ => ?_
          have h0 : ComplCouplingHeat.physFrameLam0 κ ν r' j x =
              LamJetInf.perPhys ν c (κ.lamP j) (r', x) :=
            physFrameLam0_eq_perSum_physAdj κ hν (ht₁.trans hr'.1.le) j x
          rw [h0]
        have hdG : ∀ j : Fin 2, DifferentiableAt ℝ (fun r' => (perGram κ (dd ν r'))⁻¹ i j) ρ := by
          intro j
          have hcd := (contDiffOn_perGram_inv_Icc κ hκ hν hm hb hF ht₁ hs.1 hbs i j).differentiableOn
            (by simp)
          exact hcd.differentiableAt (Icc_mem_nhds hρ.1 hρ.2)
        have hdP : ∀ j : Fin 2, HasDerivAt (fun r' => LamJetInf.perPhys ν c (κ.lamP j) (r', x))
            (((ν * (clockA ν ρ)⁻¹ : ℝ) : ℂ) *
              LamJetInf.perPhys ν c (LamJetInf.eulerK (κ.lamP j)) (ρ, x)) ρ := by
          intro j
          have hd := ((LamJetInf.contDiffOn_perPhys hν hc0.ne' (hGood j)).differentiableOn
            (by simp)).differentiableAt ((LamJetInf.isOpen_physU ν).mem_nhds
              (show (ρ, x) ∈ LamJetInf.physU ν from ha_r))
          have hcomp := hd.hasFDerivAt.comp_hasDerivAt ρ
            ((hasDerivAt_id ρ).prodMk (hasDerivAt_const ρ x))
          have hfd := LamJetInf.fderiv_perPhys_apply hν hc0.ne' (hGood j) (p := (ρ, x)) ha_r (1, (0 : ℝ × ℝ))
          have h0_per : LamJetInf.perPhys ν c (fun _ : ℝ × ℝ => (0 : ℂ)) (ρ, x) = 0 := by
            simp [LamJetInf.perPhys, perSum, physAdj]
          simp only [mul_one, map_zero, h0_per, mul_zero, add_zero] at hfd
          rw [hfd] at hcomp
          exact hcomp
        have hsum_der : HasDerivAt (fun r' =>
            ∑ j : Fin 2, (perGram κ (dd ν r'))⁻¹ i j * LamJetInf.perPhys ν c (κ.lamP j) (r', x))
            (∑ j : Fin 2,
              (deriv (fun r' => (perGram κ (dd ν r'))⁻¹ i j) ρ *
                LamJetInf.perPhys ν c (κ.lamP j) (ρ, x) +
              (perGram κ (dd ν ρ))⁻¹ i j *
                (((ν * (clockA ν ρ)⁻¹ : ℝ) : ℂ) *
                  LamJetInf.perPhys ν c (LamJetInf.eulerK (κ.lamP j)) (ρ, x)))) ρ := by
          have := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin 2))) fun j _ =>
            (hdG j).hasDerivAt.mul (hdP j)
          exact this
        unfold ladDt
        exact (hsum_der.congr_of_eventuallyEq hfn_ev).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici ρ)
      have hdt_bd : ‖ladDt (fun r' x' => physFrameLam κ ν r' i x') ρ x‖ ≤ B_dt := by
        rw [hdt_eq, Fin.sum_univ_two]
        have hGder' : ∀ j : Fin 2, ‖deriv (fun r' => (perGram κ (dd ν r'))⁻¹ i j) ρ‖ ≤ M_Gd := by
          intro j
          have hcd := (contDiffOn_perGram_inv_Icc κ hκ hν hm hb hF ht₁ hs.1 hbs i j).differentiableOn
            (by simp)
          have hd_at := hcd.differentiableAt (Icc_mem_nhds hρ.1 hρ.2)
          have hdw : derivWithin (fun r' => (perGram κ (dd ν r'))⁻¹ i j) (Ici ρ) ρ =
              deriv (fun r' => (perGram κ (dd ν r'))⁻¹ i j) ρ :=
            hd_at.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici ρ)
          rw [← hdw]
          exact hGder ρ hρ j
        have hνa : ‖((ν * (clockA ν ρ)⁻¹ : ℝ) : ℂ)‖ ≤ |ν| := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (inv_nonneg.2 ha_r.le)]
          exact mul_le_of_le_one_right (abs_nonneg ν) ha_inv_le
        have ht0 : ‖deriv (fun r' => (perGram κ (dd ν r'))⁻¹ i 0) ρ *
              LamJetInf.perPhys ν c (κ.lamP 0) (ρ, x) +
            (perGram κ (dd ν ρ))⁻¹ i 0 * (((ν * (clockA ν ρ)⁻¹ : ℝ) : ℂ) *
              LamJetInf.perPhys ν c (LamJetInf.eulerK (κ.lamP 0)) (ρ, x))‖ ≤
            M_Gd * B0 0 + M_G * (|ν| * BE 0) := by
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [norm_mul]
            exact mul_le_mul (hGder' 0) (hB0_le 0 ρ hρ_Icc x hx) (norm_nonneg _) hM_Gd0
          · rw [norm_mul, norm_mul]
            exact mul_le_mul (hGinv ρ hρ_Icc 0)
              (mul_le_mul hνa (hBE_le 0 ρ hρ_Icc x hx) (norm_nonneg _) (abs_nonneg ν))
              (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hM_G0
        have ht1 : ‖deriv (fun r' => (perGram κ (dd ν r'))⁻¹ i 1) ρ *
              LamJetInf.perPhys ν c (κ.lamP 1) (ρ, x) +
            (perGram κ (dd ν ρ))⁻¹ i 1 * (((ν * (clockA ν ρ)⁻¹ : ℝ) : ℂ) *
              LamJetInf.perPhys ν c (LamJetInf.eulerK (κ.lamP 1)) (ρ, x))‖ ≤
            M_Gd * B0 1 + M_G * (|ν| * BE 1) := by
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [norm_mul]
            exact mul_le_mul (hGder' 1) (hB0_le 1 ρ hρ_Icc x hx) (norm_nonneg _) hM_Gd0
          · rw [norm_mul, norm_mul]
            exact mul_le_mul (hGinv ρ hρ_Icc 1)
              (mul_le_mul hνa (hBE_le 1 ρ hρ_Icc x hx) (norm_nonneg _) (abs_nonneg ν))
              (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hM_G0
        calc ‖_ + _‖ ≤ _ + _ := norm_add_le _ _
          _ ≤ (M_Gd * B0 0 + M_G * (|ν| * BE 0)) + (M_Gd * B0 1 + M_G * (|ν| * BE 1)) :=
              add_le_add ht0 ht1
          _ = B_dt := by ring
      have hlap_bd : ‖ladLapCx (physFrameLam κ ν ρ i) x‖ ≤ B_lap := by
        have ha_inv_sqrt : (Real.sqrt (clockA ν ρ))⁻¹ ≤ 1 :=
          inv_le_one_of_one_le₀ (by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (one_le_clockA hν.le hρ0))
        have hsum_fn : physFrameLam κ ν ρ i = fun x' =>
            (perGram κ (dd ν ρ))⁻¹ i 0 * LamJetInf.perPhys ν c (κ.lamP 0) (ρ, x') +
            (perGram κ (dd ν ρ))⁻¹ i 1 * LamJetInf.perPhys ν c (κ.lamP 1) (ρ, x') := by
          funext x'
          rw [physFrameLam_eq_sum_perGram_inv κ ν ρ i x', Fin.sum_univ_two,
            physFrameLam0_eq_perSum_physAdj κ hν hρ0 0 x',
            physFrameLam0_eq_perSum_physAdj κ hν hρ0 1 x']
          rfl
        have hpd_per : ∀ (L : ℝ × ℝ → ℂ) (hL : LamJetInf.Good L) (k : Fin 2) (x' : ℝ × ℝ),
            pdCx k (fun y => LamJetInf.perPhys ν c L (ρ, y)) x' =
              ((Real.sqrt (clockA ν ρ)⁻¹ : ℝ) : ℂ) *
                LamJetInf.perPhys ν c (fun z => fderiv ℝ L z (B0579.dir k)) (ρ, x') := by
          intro L hL k x'
          have hd := ((LamJetInf.contDiffOn_perPhys hν hc0.ne' hL).differentiableOn
            (by simp)).differentiableAt ((LamJetInf.isOpen_physU ν).mem_nhds
              (show (ρ, x') ∈ LamJetInf.physU ν from ha_r))
          have hfd : pdCx k (fun y => LamJetInf.perPhys ν c L (ρ, y)) x' =
              fderiv ℝ (LamJetInf.perPhys ν c L) (ρ, x') (0, B0579.dir k) := by
            unfold pdCx
            have hcomp : HasFDerivAt (fun y => LamJetInf.perPhys ν c L (ρ, y))
                ((fderiv ℝ (LamJetInf.perPhys ν c L) (ρ, x')).comp
                  (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) x' :=
              hd.hasFDerivAt.comp x' (hasFDerivAt_const ρ x' |>.prodMk (hasFDerivAt_id x'))
            rw [hcomp.fderiv]; rfl
          rw [hfd, LamJetInf.fderiv_perPhys_apply hν hc0.ne' hL ha_r]
          simp only [mul_zero, zero_mul, Complex.ofReal_zero, zero_add, Real.sqrt_inv]
          congr 2
          field_simp [(Real.sqrt_pos.2 ha_r).ne']
          rw [Real.sq_sqrt ha_r.le]
        have hpd2_bd : ∀ k : Fin 2,
            ‖pdCx k (pdCx k (physFrameLam κ ν ρ i)) x‖ ≤ M_G * (B2 0 k + B2 1 k) := by
          intro k
          have hpd1_fn : pdCx k (physFrameLam κ ν ρ i) = fun x' =>
              ((perGram κ (dd ν ρ))⁻¹ i 0 * ((Real.sqrt (clockA ν ρ)⁻¹ : ℝ) : ℂ)) *
                LamJetInf.perPhys ν c (fun z => fderiv ℝ (κ.lamP 0) z (B0579.dir k)) (ρ, x') +
              ((perGram κ (dd ν ρ))⁻¹ i 1 * ((Real.sqrt (clockA ν ρ)⁻¹ : ℝ) : ℂ)) *
                LamJetInf.perPhys ν c (fun z => fderiv ℝ (κ.lamP 1) z (B0579.dir k)) (ρ, x') := by
            funext x'
            rw [hsum_fn, RateSplitAux.pdCx_add k ((hcd_per 0 x').const_mul _) ((hcd_per 1 x').const_mul _),
              pdCx_const_mul _ _ k x' (hcd_per 0 x'), pdCx_const_mul _ _ k x' (hcd_per 1 x'),
              hpd_per _ (hGood 0) k x', hpd_per _ (hGood 1) k x', mul_assoc, mul_assoc]
          rw [hpd1_fn,
            RateSplitAux.pdCx_add k ((hcd_per1 0 k x).const_mul _) ((hcd_per1 1 k x).const_mul _),
            pdCx_const_mul _ _ k x (hcd_per1 0 k x), pdCx_const_mul _ _ k x (hcd_per1 1 k x),
            hpd_per _ ((hGood 0).fderiv_apply (B0579.dir k)) k x,
            hpd_per _ ((hGood 1).fderiv_apply (B0579.dir k)) k x]
          have hsc : ‖((Real.sqrt (clockA ν ρ)⁻¹ : ℝ) : ℂ)‖ ≤ 1 := by
            rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), Real.sqrt_inv]
            exact ha_inv_sqrt
          have h0 : ‖((perGram κ (dd ν ρ))⁻¹ i 0 * ((Real.sqrt (clockA ν ρ)⁻¹ : ℝ) : ℂ)) *
              (((Real.sqrt (clockA ν ρ)⁻¹ : ℝ) : ℂ) *
                LamJetInf.perPhys ν c
                  (fun z => fderiv ℝ (fun z' => fderiv ℝ (κ.lamP 0) z' (B0579.dir k)) z (B0579.dir k))
                  (ρ, x))‖ ≤ M_G * B2 0 k := by
            rw [norm_mul, norm_mul, norm_mul]
            calc ‖(perGram κ (dd ν ρ))⁻¹ i 0‖ * ‖((Real.sqrt (clockA ν ρ)⁻¹ : ℝ) : ℂ)‖ *
                  (‖((Real.sqrt (clockA ν ρ)⁻¹ : ℝ) : ℂ)‖ * ‖_‖)
                ≤ M_G * 1 * (1 * B2 0 k) :=
                  mul_le_mul (mul_le_mul (hGinv ρ hρ_Icc 0) hsc (norm_nonneg _) hM_G0)
                    (mul_le_mul hsc (hB2_le 0 k ρ hρ_Icc x hx) (norm_nonneg _) zero_le_one)
                    (by positivity) (by positivity)
              _ = M_G * B2 0 k := by ring
          have h1 : ‖((perGram κ (dd ν ρ))⁻¹ i 1 * ((Real.sqrt (clockA ν ρ)⁻¹ : ℝ) : ℂ)) *
              (((Real.sqrt (clockA ν ρ)⁻¹ : ℝ) : ℂ) *
                LamJetInf.perPhys ν c
                  (fun z => fderiv ℝ (fun z' => fderiv ℝ (κ.lamP 1) z' (B0579.dir k)) z (B0579.dir k))
                  (ρ, x))‖ ≤ M_G * B2 1 k := by
            rw [norm_mul, norm_mul, norm_mul]
            calc ‖(perGram κ (dd ν ρ))⁻¹ i 1‖ * ‖((Real.sqrt (clockA ν ρ)⁻¹ : ℝ) : ℂ)‖ *
                  (‖((Real.sqrt (clockA ν ρ)⁻¹ : ℝ) : ℂ)‖ * ‖_‖)
                ≤ M_G * 1 * (1 * B2 1 k) :=
                  mul_le_mul (mul_le_mul (hGinv ρ hρ_Icc 1) hsc (norm_nonneg _) hM_G0)
                    (mul_le_mul hsc (hB2_le 1 k ρ hρ_Icc x hx) (norm_nonneg _) zero_le_one)
                    (by positivity) (by positivity)
              _ = M_G * B2 1 k := by ring
          calc ‖_ + _‖ ≤ _ + _ := norm_add_le _ _
            _ ≤ M_G * B2 0 k + M_G * B2 1 k := add_le_add h0 h1
            _ = M_G * (B2 0 k + B2 1 k) := by ring
        unfold ladLapCx
        calc ‖pdCx 0 (pdCx 0 (physFrameLam κ ν ρ i)) x +
              pdCx 1 (pdCx 1 (physFrameLam κ ν ρ i)) x‖
            ≤ ‖pdCx 0 (pdCx 0 (physFrameLam κ ν ρ i)) x‖ +
              ‖pdCx 1 (pdCx 1 (physFrameLam κ ν ρ i)) x‖ := norm_add_le _ _
          _ ≤ M_G * (B2 0 0 + B2 1 0) + M_G * (B2 0 1 + B2 1 1) :=
              add_le_add (hpd2_bd 0) (hpd2_bd 1)
          _ = B_lap := by ring
      calc ‖ladDt (fun r' x' => physFrameLam κ ν r' i x') ρ x +
            (ν : ℂ) * ladLapCx (physFrameLam κ ν ρ i) x‖
          ≤ ‖ladDt (fun r' x' => physFrameLam κ ν r' i x') ρ x‖ +
            ‖(ν : ℂ)‖ * ‖ladLapCx (physFrameLam κ ν ρ i) x‖ := by
              rw [← norm_mul]; exact norm_add_le _ _
        _ ≤ B_dt + |ν| * B_lap := by
            rw [Complex.norm_real, Real.norm_eq_abs]
            exact add_le_add hdt_bd (mul_le_mul_of_nonneg_left hlap_bd (abs_nonneg ν))
    have hMain_mem : MemLp (fun x => ladDt (fun r' x' => physFrameLam κ ν r' i x') ρ x +
          (ν : ℂ) * ladLapCx (physFrameLam κ ν ρ i) x) 2 (B0579.cellMeasure c (-m)) ∧
        xNorm c (-m) (fun x => ladDt (fun r' x' => physFrameLam κ ν r' i x') ρ x +
          (ν : ℂ) * ladLapCx (physFrameLam κ ν ρ i) x) ≤
          ENNReal.ofReal (W_c * (B_dt + |ν| * B_lap)) :=
      memLp_and_xNorm_cell_bdd_of_cont (by linarith) (by positivity) hMain_cont hMain_bd
    have hTr_mem : MemLp (ladTransport tr ρ (physFrameLam κ ν ρ i)) 2 (B0579.cellMeasure c (-m)) ∧
        xNorm c (-m) (ladTransport tr ρ (physFrameLam κ ν ρ i)) ≤ ENNReal.ofReal (W_c * B_tr) := by
      have hv_cd : ContDiff ℝ ∞ (tr.v ρ) := UnforcedLeray.B0238.contDiff_Vc tr hρ0
      have hv_cont : ∀ k : Fin 2, Continuous (fun x => tr.v ρ x k) := fun k =>
        ((EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hv_cd).continuous
      have hTr_cont : Continuous (ladTransport tr ρ (physFrameLam κ ν ρ i)) := by
        have hsum_tr : ladTransport tr ρ (physFrameLam κ ν ρ i) =
            fun x => ((tr.v ρ x 0 : ℝ) : ℂ) * pdCx 0 (physFrameLam κ ν ρ i) x +
              ((tr.v ρ x 1 : ℝ) : ℂ) * pdCx 1 (physFrameLam κ ν ρ i) x := by
          funext x; unfold ladTransport; rfl
        rw [hsum_tr]
        exact ((Complex.continuous_ofReal.comp (hv_cont 0)).mul
            (RateSplitAux.contDiff_pdCx hslice 0).continuous).add
          ((Complex.continuous_ofReal.comp (hv_cont 1)).mul
            (RateSplitAux.contDiff_pdCx hslice 1).continuous)
      refine memLp_and_xNorm_cell_bdd_of_cont (by linarith) (by positivity) hTr_cont fun x hx => ?_
      have hpd0 := hpd_bd ρ hρ 0
      -- Use pointwise `B_g` bound from `hB1_le` via `pdCx`
      have hpd_pt : ∀ k : Fin 2, ‖pdCx k (physFrameLam κ ν ρ i) x‖ ≤ B_g := by
        intro k
        have ha_inv_sqrt : (Real.sqrt (clockA ν ρ))⁻¹ ≤ 1 :=
          inv_le_one_of_one_le₀ (by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (one_le_clockA hν.le hρ0))
        have hcd_lam : ∀ j : Fin 2, Differentiable ℝ (fun x' => LamJetInf.perPhys ν c (κ.lamP j) (ρ, x')) := by
          intro j x'
          have hd := ((LamJetInf.contDiffOn_perPhys hν hc0.ne' (hGood j)).differentiableOn
            (by simp)).differentiableAt ((LamJetInf.isOpen_physU ν).mem_nhds
              (show (ρ, x') ∈ LamJetInf.physU ν from ha_r))
          exact hd.comp x' (differentiableAt_const ρ |>.prodMk differentiableAt_id)
        have hsum_fn : physFrameLam κ ν ρ i = fun x' =>
            (perGram κ (dd ν ρ))⁻¹ i 0 * LamJetInf.perPhys ν c (κ.lamP 0) (ρ, x') +
            (perGram κ (dd ν ρ))⁻¹ i 1 * LamJetInf.perPhys ν c (κ.lamP 1) (ρ, x') := by
          funext x'
          rw [physFrameLam_eq_sum_perGram_inv κ ν ρ i x', Fin.sum_univ_two,
            physFrameLam0_eq_perSum_physAdj κ hν hρ0 0 x',
            physFrameLam0_eq_perSum_physAdj κ hν hρ0 1 x']
          rfl
        have hpd_per : ∀ j : Fin 2,
            pdCx k (fun x' => LamJetInf.perPhys ν c (κ.lamP j) (ρ, x')) x =
              ((Real.sqrt (clockA ν ρ)⁻¹ : ℝ) : ℂ) *
                LamJetInf.perPhys ν c (fun z => fderiv ℝ (κ.lamP j) z (B0579.dir k)) (ρ, x) := by
          intro j
          have hd := ((LamJetInf.contDiffOn_perPhys hν hc0.ne' (hGood j)).differentiableOn
            (by simp)).differentiableAt ((LamJetInf.isOpen_physU ν).mem_nhds
              (show (ρ, x) ∈ LamJetInf.physU ν from ha_r))
          have hfd : pdCx k (fun x' => LamJetInf.perPhys ν c (κ.lamP j) (ρ, x')) x =
              fderiv ℝ (LamJetInf.perPhys ν c (κ.lamP j)) (ρ, x) (0, B0579.dir k) := by
            unfold pdCx
            have hcomp : HasFDerivAt (fun x' => LamJetInf.perPhys ν c (κ.lamP j) (ρ, x'))
                ((fderiv ℝ (LamJetInf.perPhys ν c (κ.lamP j)) (ρ, x)).comp
                  (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) x :=
              hd.hasFDerivAt.comp x (hasFDerivAt_const ρ x |>.prodMk (hasFDerivAt_id x))
            rw [hcomp.fderiv]; rfl
          rw [hfd, LamJetInf.fderiv_perPhys_apply hν hc0.ne' (hGood j) ha_r]
          simp only [mul_zero, zero_mul, Complex.ofReal_zero, zero_add, Real.sqrt_inv]
          congr 2
          field_simp [(Real.sqrt_pos.2 ha_r).ne']
          rw [Real.sq_sqrt ha_r.le]
        rw [hsum_fn, RateSplitAux.pdCx_add k ((hcd_lam 0 x).const_mul _) ((hcd_lam 1 x).const_mul _),
          pdCx_const_mul _ _ k x (hcd_lam 0 x), pdCx_const_mul _ _ k x (hcd_lam 1 x),
          hpd_per 0, hpd_per 1]
        have hnorm0 : ‖((Real.sqrt (clockA ν ρ)⁻¹ : ℝ) : ℂ) *
            LamJetInf.perPhys ν c (fun z => fderiv ℝ (κ.lamP 0) z (B0579.dir k)) (ρ, x)‖ ≤
            max (B1 0 0) (B1 0 1) := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), Real.sqrt_inv]
          calc (Real.sqrt (clockA ν ρ))⁻¹ * _
              ≤ 1 * B1 0 k := mul_le_mul ha_inv_sqrt (hB1_le 0 k ρ hρ_Icc x hx) (norm_nonneg _) zero_le_one
            _ ≤ max (B1 0 0) (B1 0 1) := by fin_cases k <;> simp [le_max_left, le_max_right]
        have hnorm1 : ‖((Real.sqrt (clockA ν ρ)⁻¹ : ℝ) : ℂ) *
            LamJetInf.perPhys ν c (fun z => fderiv ℝ (κ.lamP 1) z (B0579.dir k)) (ρ, x)‖ ≤
            max (B1 1 0) (B1 1 1) := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), Real.sqrt_inv]
          calc (Real.sqrt (clockA ν ρ))⁻¹ * _
              ≤ 1 * B1 1 k := mul_le_mul ha_inv_sqrt (hB1_le 1 k ρ hρ_Icc x hx) (norm_nonneg _) zero_le_one
            _ ≤ max (B1 1 0) (B1 1 1) := by fin_cases k <;> simp [le_max_left, le_max_right]
        calc ‖(perGram κ (dd ν ρ))⁻¹ i 0 * _ + (perGram κ (dd ν ρ))⁻¹ i 1 * _‖
            ≤ ‖(perGram κ (dd ν ρ))⁻¹ i 0‖ * ‖_‖ + ‖(perGram κ (dd ν ρ))⁻¹ i 1‖ * ‖_‖ :=
              (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
          _ ≤ M_G * max (B1 0 0) (B1 0 1) + M_G * max (B1 1 0) (B1 1 1) :=
              add_le_add (mul_le_mul (hGinv ρ hρ_Icc 0) hnorm0 (norm_nonneg _) hM_G0)
                (mul_le_mul (hGinv ρ hρ_Icc 1) hnorm1 (norm_nonneg _) hM_G0)
          _ = B_g := by ring
      unfold ladTransport
      have hv0 : ‖((tr.v ρ x 0 : ℝ) : ℂ)‖ ≤ C_tr := by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact (hBdd ρ hρS x hx).1 0
      have hv1 : ‖((tr.v ρ x 1 : ℝ) : ℂ)‖ ≤ C_tr := by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact (hBdd ρ hρS x hx).1 1
      calc ‖((tr.v ρ x 0 : ℝ) : ℂ) * pdCx 0 (physFrameLam κ ν ρ i) x +
            ((tr.v ρ x 1 : ℝ) : ℂ) * pdCx 1 (physFrameLam κ ν ρ i) x‖
          ≤ ‖((tr.v ρ x 0 : ℝ) : ℂ)‖ * ‖pdCx 0 (physFrameLam κ ν ρ i) x‖ +
            ‖((tr.v ρ x 1 : ℝ) : ℂ)‖ * ‖pdCx 1 (physFrameLam κ ν ρ i) x‖ :=
            (norm_add_le _ _).trans (by rw [norm_mul, norm_mul])
        _ ≤ C_tr * B_g + C_tr * B_g :=
            add_le_add (mul_le_mul hv0 (hpd_pt 0) (norm_nonneg _) hC_tr0)
              (mul_le_mul hv1 (hpd_pt 1) (norm_nonneg _) hC_tr0)
        _ = B_tr := by ring
    obtain ⟨hMainTr_mem, hMainTr_x⟩ :=
      ComplCouplingHeat.memLp_and_xNorm_add_le (by positivity) (by positivity)
        hMain_mem.1 hTr_mem.1 hMain_mem.2 hTr_mem.2
    have hDual_eq : physLamDual κ tr ρ i =
        fun x => (ladDt (fun r' x' => physFrameLam κ ν r' i x') ρ x +
            (ν : ℂ) * ladLapCx (physFrameLam κ ν ρ i) x +
            ladTransport tr ρ (physFrameLam κ ν ρ i) x) -
          kerAdj c (fun k y => physFrameLam κ ν ρ i y *
            ((B0579.pd k (UnforcedLeray.B0238.Ec tr ρ) y : ℝ) : ℂ)) x := by
      funext x
      unfold physLamDual
      rfl
    rw [hDual_eq]
    refine ⟨hMainTr_mem.sub hKer.1.1, ?_⟩
    have hsub_le : xNorm c (-m) ((fun x => ladDt (fun r' x' => physFrameLam κ ν r' i x') ρ x +
          (ν : ℂ) * ladLapCx (physFrameLam κ ν ρ i) x +
          ladTransport tr ρ (physFrameLam κ ν ρ i) x) -
        kerAdj c (fun k y => physFrameLam κ ν ρ i y *
          ((B0579.pd k (UnforcedLeray.B0238.Ec tr ρ) y : ℝ) : ℂ))) ≤
        xNorm c (-m) (fun x => ladDt (fun r' x' => physFrameLam κ ν r' i x') ρ x +
          (ν : ℂ) * ladLapCx (physFrameLam κ ν ρ i) x +
          ladTransport tr ρ (physFrameLam κ ν ρ i) x) +
        xNorm c (-m) (kerAdj c (fun k y => physFrameLam κ ν ρ i y *
          ((B0579.pd k (UnforcedLeray.B0238.Ec tr ρ) y : ℝ) : ℂ))) :=
      eLpNorm_sub_le hMainTr_mem.1 hKer.1.1.1 one_le_two
    refine hsub_le.trans ((add_le_add hMainTr_x hKer.1.2).trans (le_of_eq ?_))
    rw [← ENNReal.ofReal_add (by positivity) hM_ker0]
    congr 1
    ring
  -- Now prove `IntegrableOn` of `g ρ := ∫ x in cell c, w ρ x * physLamDual κ tr ρ i x` on `Ioc t₁ s`
  set g : ℝ → ℂ := fun ρ => ∫ x in B0579.cell c, w ρ x * physLamDual κ tr ρ i x
  have hAe : ∀ ρ ∈ Ioo t₁ s, (xNorm c m (w ρ)).toReal ≤ A_w := fun ρ hρ =>
    hA_w ρ (Ioo_subset_Icc_self hρ)
  let F_u : ℝ := Fe.toReal
  have hF_u0 : 0 ≤ F_u := ENNReal.toReal_nonneg
  have hFu : ∀ ρ ∈ Ioo t₁ s,
      MemLp (ladForce tr (u ρ) ρ) 2 (B0579.cellMeasure c m) ∧
      (xNorm c m (ladForce tr (u ρ) ρ)).toReal ≤ F_u := fun ρ hρ =>
    hforce ρ (Ioo_subset_Icc_self hρ)
  set M_rate : ℝ := A_w * (M_ND + M_ker) + F_u * M_φ +
    (3 * |ν| * K_cut + 2 * C_tr * K_cut) * (A_w * M_φ + 2 * (A_w * M_g))
  have hTendsto_and_bd : ∀ ρ ∈ Ioo t₁ s,
      (∀ R : ℝ, 1 ≤ R → ‖ladRate tr w u φ R ρ‖ ≤ M_rate) ∧
      Tendsto (fun R : ℝ => ladRate tr w u φ R ρ) atTop (𝓝 (g ρ)) := by
    intro ρ hρ
    have hρ_Icc : ρ ∈ Icc t₁ s := Ioo_subset_Icc_self hρ
    have hρ0 : 0 ≤ ρ := ht₁.trans hρ_Icc.1
    have hρS : ρ ∈ Icc (0 : ℝ) s := ⟨hρ0, hρ_Icc.2⟩
    have hv : ∀ x ∈ B0579.cell c, ∀ j : Fin 2, |tr.v ρ x j| ≤ C_tr :=
      fun x hx j => (hBdd ρ hρS x hx).1 j
    have hw_mem := hw.memX ρ hρ_Icc.1
    have hw_norm := hAe ρ hρ
    obtain ⟨hforce_mem, hforce_norm⟩ := hFu ρ hρ
    obtain ⟨hLam_mem, hLam_x⟩ := hLam_bd ρ hρ
    obtain ⟨hDual_mem, hDual_x⟩ := hDual_bd ρ hρ
    have hφ_mem : MemLp (φ ρ) 2 (B0579.cellMeasure c (-m)) := hLam_mem
    have hφ_norm : (xNorm c (-m) (φ ρ)).toReal ≤ M_φ :=
      ENNReal.toReal_le_of_le_ofReal hM_φ0 hLam_x
    have hND_norm : (xNorm c (-m) (physLamDual κ tr ρ i)).toReal ≤ M_ND :=
      ENNReal.toReal_le_of_le_ofReal hM_ND0 hDual_x
    have hgrad_mem : ∀ k : Fin 2, MemLp (pdCx k (φ ρ)) 2 (B0579.cellMeasure c (-m)) :=
      fun k => (hpd_bd ρ hρ k).1
    have hgrad_norm : ∀ k : Fin 2, (xNorm c (-m) (pdCx k (φ ρ))).toReal ≤ M_g :=
      fun k => ENNReal.toReal_le_of_le_ofReal hM_g0 (hpd_bd ρ hρ k).2
    have hKer := hKerAll hρS hLam_mem hLam_x
    have hKer_mem : MemLp (kerAdj c (fun k y => φ ρ y *
        ((B0579.pd k (UnforcedLeray.B0238.Ec tr ρ) y : ℝ) : ℂ))) 2 (B0579.cellMeasure c (-m)) :=
      hKer.1.1
    have hKer_norm : (xNorm c (-m) (kerAdj c (fun k y => φ ρ y *
        ((B0579.pd k (UnforcedLeray.B0238.Ec tr ρ) y : ℝ) : ℂ)))).toReal ≤ M_ker :=
      ENNReal.toReal_le_of_le_ofReal hM_ker0 hKer.1.2
    have hchi_eq : ladChi tr φ ρ = fun x => physLamDual κ tr ρ i x +
        kerAdj c (fun k y => φ ρ y * ((B0579.pd k (UnforcedLeray.B0238.Ec tr ρ) y : ℝ) : ℂ)) x := by
      funext x
      unfold ladChi physLamDual
      ring
    have hχ_mem : MemLp (ladChi tr φ ρ) 2 (B0579.cellMeasure c (-m)) := by
      rw [hchi_eq]; exact hDual_mem.add hKer_mem
    have hχ_norm : (xNorm c (-m) (ladChi tr φ ρ)).toReal ≤ M_ND + M_ker := by
      rw [hchi_eq]
      have hadd_x : xNorm c (-m) (fun x => physLamDual κ tr ρ i x +
            kerAdj c (fun k y => φ ρ y * ((B0579.pd k (UnforcedLeray.B0238.Ec tr ρ) y : ℝ) : ℂ)) x) ≤
          xNorm c (-m) (physLamDual κ tr ρ i) +
            xNorm c (-m) (kerAdj c (fun k y => φ ρ y *
              ((B0579.pd k (UnforcedLeray.B0238.Ec tr ρ) y : ℝ) : ℂ))) :=
        eLpNorm_add_le hDual_mem.1 hKer_mem.1 one_le_two
      have hto : (xNorm c (-m) (fun x => physLamDual κ tr ρ i x +
            kerAdj c (fun k y => φ ρ y * ((B0579.pd k (UnforcedLeray.B0238.Ec tr ρ) y : ℝ) : ℂ)) x)).toReal ≤
          (xNorm c (-m) (physLamDual κ tr ρ i)).toReal +
            (xNorm c (-m) (kerAdj c (fun k y => φ ρ y *
              ((B0579.pd k (UnforcedLeray.B0238.Ec tr ρ) y : ℝ) : ℂ)))).toReal := by
        calc _ ≤ (xNorm c (-m) (physLamDual κ tr ρ i) +
              xNorm c (-m) (kerAdj c (fun k y => φ ρ y *
                ((B0579.pd k (UnforcedLeray.B0238.Ec tr ρ) y : ℝ) : ℂ)))).toReal :=
              ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hDual_mem.eLpNorm_ne_top, hKer_mem.eLpNorm_ne_top⟩) hadd_x
          _ = _ := ENNReal.toReal_add hDual_mem.eLpNorm_ne_top hKer_mem.eLpNorm_ne_top
      linarith
    obtain ⟨hcomm_bd, hcomm_lim⟩ := ladComm_bound_and_vanish hc0 hC_tr0 hA_w0 hM_φ0 hM_g0
      hv hw_mem hw_norm hφ_mem hφ_norm hgrad_mem hgrad_norm hK_cut0
      (fun R hR => (hK_cut R hR).2.2.2.2.1) (fun R hR => (hK_cut R hR).2.2.2.2.2)
    refine ⟨fun R hR1 => ?_, ?_⟩
    · have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR1
      rw [ladRateSplit ν c m tr t₁ s f w u φ hc0 ht₁ ht₁s hw hφ_smooth R hR0 ρ hρ]
      have hcut := hK_cut R hR0
      have hcont : Continuous (ladCut R) := (hcut.1 c).continuous
      have hcb : ∀ x, |ladCut R x| ≤ 1 := fun x => by
        rw [abs_of_nonneg (hcut.2.1 x).1]; exact (hcut.2.1 x).2
      have ea : ‖∫ x in B0579.cell c, w ρ x * ((ladCut R x : ℂ) * ladChi tr φ ρ x)‖ ≤
          A_w * (M_ND + M_ker) :=
        (RateBoundAux.cs_cut c m hcont hcb hw_mem hχ_mem).trans
          (mul_le_mul hw_norm hχ_norm ENNReal.toReal_nonneg hA_w0)
      have eb : ‖∫ x in B0579.cell c, ladForce tr (u ρ) ρ x * ladCutPhi φ R ρ x‖ ≤
          F_u * M_φ :=
        (RateBoundAux.cs_cut c m hcont hcb hforce_mem hφ_mem).trans
          (mul_le_mul hforce_norm hφ_norm ENNReal.toReal_nonneg hF_u0)
      have ec := hcomm_bd R hR1
      have hsub := norm_add_le
        ((∫ x in B0579.cell c, w ρ x * ((ladCut R x : ℂ) * ladChi tr φ ρ x)) -
          ∫ x in B0579.cell c, ladForce tr (u ρ) ρ x * ladCutPhi φ R ρ x)
        (ladComm tr w φ R ρ)
      have hsub2 := norm_sub_le
        (∫ x in B0579.cell c, w ρ x * ((ladCut R x : ℂ) * ladChi tr φ ρ x))
        (∫ x in B0579.cell c, ladForce tr (u ρ) ρ x * ladCutPhi φ R ρ x)
      unfold M_rate
      linarith [hsub, hsub2, ea, eb, ec]
    · have hsplit_ev : (fun R : ℝ => ladRate tr w u φ R ρ) =ᶠ[atTop] fun R : ℝ =>
          (∫ x in B0579.cell c, w ρ x * ((ladCut R x : ℂ) * ladChi tr φ ρ x)) -
            (∫ x in B0579.cell c, ladForce tr (u ρ) ρ x * ladCutPhi φ R ρ x) +
              ladComm tr w φ R ρ :=
        Filter.eventually_atTop.2 ⟨1, fun R hR =>
          ladRateSplit ν c m tr t₁ s f w u φ hc0 ht₁ ht₁s hw hφ_smooth R (by linarith) ρ hρ⟩
      have hlim1 := ladCutLimit c m (w ρ) (ladChi tr φ ρ) hw_mem hχ_mem
      have hlim2 : Tendsto (fun R : ℝ => ∫ x in B0579.cell c,
          ladForce tr (u ρ) ρ x * ladCutPhi φ R ρ x) atTop
          (𝓝 (∫ x in B0579.cell c, ladForce tr (u ρ) ρ x * φ ρ x)) := by
        have hcut_eq : ∀ R, (fun x => ladForce tr (u ρ) ρ x * ladCutPhi φ R ρ x) =
            fun x => ladForce tr (u ρ) ρ x * ((ladCut R x : ℂ) * φ ρ x) := by
          intro R; funext x; unfold ladCutPhi; rfl
        simp_rw [hcut_eq]
        exact ladCutLimit c m (ladForce tr (u ρ) ρ) (φ ρ) hforce_mem hφ_mem
      have hTransp : ∫ x in B0579.cell c, w ρ x *
            kerAdj c (fun k y => φ ρ y * ((B0579.pd k (UnforcedLeray.B0238.Ec tr ρ) y : ℝ) : ℂ)) x =
          ∫ x in B0579.cell c, ladForce tr (u ρ) ρ x * φ ρ x := by
        have hz_ρ : HasZeroCirculation c (w ρ) :=
          ladFlowZeroCirc m (by linarith) ν c tr t₁ f w u hc1 hf0 hw ρ hρ_Icc.1
        exact hKer.2 (w ρ) (u ρ) hw_mem hz_ρ (hw.biotSavart ρ hρ_Icc.1)
      have hlim_sub : (∫ x in B0579.cell c, w ρ x * ladChi tr φ ρ x) -
          (∫ x in B0579.cell c, ladForce tr (u ρ) ρ x * φ ρ x) + 0 = g ρ := by
        have hsum_int : ∫ x in B0579.cell c, w ρ x * ladChi tr φ ρ x =
            (∫ x in B0579.cell c, w ρ x * physLamDual κ tr ρ i x) +
              (∫ x in B0579.cell c, w ρ x *
                kerAdj c (fun k y => φ ρ y * ((B0579.pd k (UnforcedLeray.B0238.Ec tr ρ) y : ℝ) : ℂ)) x) := by
          have hi1 := CommVanishAux.integrableOn_cell_norm_mul c m hw_mem hDual_mem
          have hi2 := CommVanishAux.integrableOn_cell_norm_mul c m hw_mem hKer_mem
          have hm1 : IntegrableOn (fun x => w ρ x * physLamDual κ tr ρ i x) (B0579.cell c) :=
            hi1.mono' ((hw_mem.1.mono_ac (B0579.ac_cellMeasure c m)).mul
              (hDual_mem.1.mono_ac (B0579.ac_cellMeasure c (-m))))
              (Filter.Eventually.of_forall fun x => by rw [norm_mul])
          have hm2 : IntegrableOn (fun x => w ρ x *
              kerAdj c (fun k y => φ ρ y * ((B0579.pd k (UnforcedLeray.B0238.Ec tr ρ) y : ℝ) : ℂ)) x)
              (B0579.cell c) :=
            hi2.mono' ((hw_mem.1.mono_ac (B0579.ac_cellMeasure c m)).mul
              (hKer_mem.1.mono_ac (B0579.ac_cellMeasure c (-m))))
              (Filter.Eventually.of_forall fun x => by rw [norm_mul])
          have hfn : (fun x => w ρ x * ladChi tr φ ρ x) =
              fun x => w ρ x * physLamDual κ tr ρ i x +
                w ρ x * kerAdj c (fun k y => φ ρ y *
                  ((B0579.pd k (UnforcedLeray.B0238.Ec tr ρ) y : ℝ) : ℂ)) x := by
            funext x; rw [hchi_eq, mul_add]
          rw [hfn, integral_add hm1 hm2]
        rw [hsum_int, hTransp]
        change g ρ + _ - _ + 0 = g ρ
        ring
      rw [← hlim_sub]
      exact ((hlim1.sub hlim2).add hcomm_lim).congr' hsplit_ev.symm
  have hg_meas_k : ∀ k : ℕ,
      AEStronglyMeasurable g (volume.restrict (Ioo t₁ (s - (s - t₁) / ((k : ℝ) + 2)))) := by
    intro k
    set rk : ℝ := s - (s - t₁) / ((k : ℝ) + 2)
    have hrk_mem : rk ∈ Ico t₁ s := by
      have hk0 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
      have hk1 : (1 : ℝ) < (k : ℝ) + 2 := by linarith
      have hdiv_lt : (s - t₁) / ((k : ℝ) + 2) < s - t₁ :=
        div_lt_self (sub_pos.2 ht₁s) hk1
      have hdiv_pos : 0 < (s - t₁) / ((k : ℝ) + 2) := div_pos (sub_pos.2 ht₁s) hk0
      exact ⟨by linarith, by linarith⟩
    have hrk_le : rk ≤ s := hrk_mem.2.le
    have hmeas_n : ∀ n : ℕ, AEStronglyMeasurable (ladRate tr w u φ ((n : ℝ) + 1))
        (volume.restrict (Ioo t₁ rk)) := fun n =>
      ((hprod_r' rk hrk_mem ((n : ℝ) + 1) (by positivity)).1.mono_set Ioo_subset_Ioc_self).aestronglyMeasurable
    have hlim_ae : ∀ᵐ ρ ∂(volume.restrict (Ioo t₁ rk)),
        Tendsto (fun n : ℕ => ladRate tr w u φ ((n : ℝ) + 1) ρ) atTop (𝓝 (g ρ)) := by
      rw [ae_restrict_iff' measurableSet_Ioo]
      refine Filter.Eventually.of_forall fun ρ hρ => ?_
      have hρs : ρ ∈ Ioo t₁ s := ⟨hρ.1, hρ.2.trans_le hrk_le⟩
      exact (hTendsto_and_bd ρ hρs).2.comp
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    exact aestronglyMeasurable_of_tendsto_ae atTop hmeas_n hlim_ae
  have hg_meas : AEStronglyMeasurable g (volume.restrict (Ioo t₁ s)) := by
    have hunion : Ioo t₁ s = ⋃ k : ℕ, Ioo t₁ (s - (s - t₁) / ((k : ℝ) + 2)) := by
      ext ρ
      simp only [mem_iUnion, mem_Ioo]
      constructor
      · rintro ⟨h1, h2⟩
        obtain ⟨k, hk⟩ := exists_nat_gt ((s - t₁) / (s - ρ))
        refine ⟨k, h1, ?_⟩
        have hsr : 0 < s - ρ := sub_pos.2 h2
        have hk0 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
        have hk2 : (s - t₁) / (s - ρ) < (k : ℝ) + 2 := hk.trans (by linarith)
        have hdiv : (s - t₁) / ((k : ℝ) + 2) < s - ρ :=
          (div_lt_comm₀ hsr hk0).1 hk2
        linarith
      · rintro ⟨k, h1, h2⟩
        have hdiv_pos : 0 < (s - t₁) / ((k : ℝ) + 2) := div_pos (sub_pos.2 ht₁s) (by positivity)
        exact ⟨h1, by linarith⟩
    rw [hunion, aestronglyMeasurable_iUnion_iff]
    exact hg_meas_k
  have hg_int_Ioo : IntegrableOn g (Ioo t₁ s) := by
    refine IntegrableOn.of_bound measure_Ioo_lt_top hg_meas M_rate ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    refine Filter.Eventually.of_forall fun ρ hρ => ?_
    have h1 := (hTendsto_and_bd ρ hρ).1
    have hlim : Tendsto (fun R : ℝ => ‖ladRate tr w u φ R ρ‖) atTop (𝓝 ‖g ρ‖) :=
      (hTendsto_and_bd ρ hρ).2.norm
    exact le_of_tendsto hlim (Filter.eventually_atTop.2 ⟨1, h1⟩)
  have hg_int_Ioc : IntegrableOn g (Ioc t₁ s) :=
    hg_int_Ioo.congr_set_ae Ioo_ae_eq_Ioc.symm
  refine ⟨hg_int_Ioc.congr_fun (fun q hq => ?_) measurableSet_Ioc, fun ρ hρ => (hDual_bd ρ hρ).1⟩
  have hq0 : 0 ≤ q := ht₁.trans hq.1.le
  exact FrameAmplSub.physLamDual_pairing_eq_movH0 κ hν hq0 tr w i

theorem integrableOn_amplRate
    (κ : PlanarFrameKernels) (hκ : IsSeedKernels κ) {ν m b K : ℝ} (hm : 8 < m) (hν : 0 < ν)
    (hb : 1 ≤ b) (hF : PerFrameFacts κ ν m b K)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    (hBddAll : ∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C)
    {t₁ t₂ s : ℝ} (ht₁ : 0 ≤ t₁) (hs : s ∈ Icc t₁ t₂) (hbt₂ : b ≤ clockTheta ν t₂)
    {f : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u)
    (hf0 : HasZeroCirculation (ν ^ (-2 : ℝ)) f) (i : Fin 2) :
    IntegrableOn (fun q => (((clockA ν q) ^ (-2 : ℝ) : ℝ) : ℂ) * movH0 κ tr q i (movingW ν w q))
      (Ioc t₁ s) :=
  (integrableOn_amplRate_and_dual κ hκ hm hν hb hF tr htr hBddAll ht₁ hs hbt₂ hw hf0 i).1

end Leaf2WeakEqAmplInt

end ComplFreeRateSub

end UnforcedLeray.Short.IIIa
