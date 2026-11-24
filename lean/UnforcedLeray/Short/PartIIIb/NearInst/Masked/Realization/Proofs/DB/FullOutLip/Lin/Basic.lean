import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_18_3_2
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.DB.FullOutLip.GradKL1
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.T8_1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L4

/-!
# Helpers for `FullOutSubLin` (source 3604-3621): entry bounds, support, kernel sup bound
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ENNReal

open UnforcedLeray
open UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.LinAux

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Masked
  UnforcedLeray.Short.PartIIIb.Concrete.T8_1

theorem psiM_sub (ν : ℝ) (i : Fin 3) (T1 T2 : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (p : (ℝ × Space) × ℝ) (z : Space) :
    PsiM ν i (fun τ' w => T1 τ' w - T2 τ' w) p z = PsiM ν i T1 p z - PsiM ν i T2 p z := by
  simp only [PsiM, Matrix.sub_apply, Complex.ofReal_sub, mul_sub, Finset.sum_sub_distrib]

theorem nsSym_sub' (T S : Ten3) :
    NearInst.nsSym (T - S) = NearInst.nsSym T - NearInst.nsSym S := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [NearInst.nsSym, NearInst.symRZ] <;> ring

theorem cartLift_sub (R c : ℝ) (f g : Chart → Ten3) (τ : ℝ) (z : Space) :
    NearInst.cartLift R c (fun p => f p - g p) τ z =
      NearInst.cartLift R c f τ z - NearInst.cartLift R c g τ z := by
  unfold NearInst.cartLift
  simp only [nsSym_sub', smul_sub, Matrix.mul_sub, Matrix.sub_mul]

theorem abs_entry_le_tensorNorm (M : Matrix (Fin 3) (Fin 3) ℝ) (a b : Fin 3) :
    |M a b| ≤ UnforcedLeray.Short.IIIa.tensorNorm M := by
  unfold UnforcedLeray.Short.IIIa.tensorNorm
  have h1 : M a b ^ 2 ≤ ∑ j, M a j ^ 2 :=
    Finset.single_le_sum (f := fun j => M a j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ b)
  have h2 : ∑ j, M a j ^ 2 ≤ ∑ i, ∑ j, M i j ^ 2 :=
    Finset.single_le_sum (f := fun i => ∑ j, M i j ^ 2)
      (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _) (Finset.mem_univ a)
  exact Real.abs_le_sqrt (h1.trans h2)

theorem cartLift_entry_le (R c : ℝ) (f : Chart → Ten3) (τ : ℝ) (z : Space) (a b : Fin 3) :
    |NearInst.cartLift R c f τ z a b| ≤
      (NearInst.chartOf R c z τ).1 * ‖f (NearInst.chartOf R c z τ)‖ :=
  (abs_entry_le_tensorNorm _ a b).trans (Concrete.cartLiftFrobBound R c f τ z)

theorem chart_band_ball (R c τ s1 L : ℝ) (hR : 0 < R) (hs1 : 0 < s1) (z : Space)
    (h : s1 ≤ (NearInst.chartOf R c z τ).1 ∧ |(NearInst.chartOf R c z τ).2.2| ≤ L) :
    ‖z‖ ≤ Real.sqrt ((R ^ 2 + L ^ 2) / s1) := by
  obtain ⟨hA, hB⟩ := h
  have e1 : (NearInst.chartOf R c z τ).1 = R ^ 2 / NearInst.hRad z ^ 2 := rfl
  have e2 : (NearInst.chartOf R c z τ).2.2 = R * z 2 / NearInst.hRad z := rfl
  have hR2 : NearInst.hRad z ^ 2 = z 0 ^ 2 + z 1 ^ 2 := by
    unfold NearInst.hRad
    exact Real.sq_sqrt (by positivity)
  have hne : NearInst.hRad z ≠ 0 := by
    intro h0
    have h' := hA
    rw [e1, h0] at h'
    simp at h'
    linarith
  have hpos : 0 < NearInst.hRad z := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hne)
  have h1 : s1 * NearInst.hRad z ^ 2 ≤ R ^ 2 := by
    have h' := hA
    rw [e1, le_div_iff₀ (pow_pos hpos 2)] at h'
    exact h'
  rw [e2] at hB
  have hsq : (R * z 2 / NearInst.hRad z) ^ 2 ≤ L ^ 2 :=
    sq_le_sq' (abs_le.mp hB).1 (abs_le.mp hB).2
  have h2 : (R * z 2) ^ 2 ≤ L ^ 2 * NearInst.hRad z ^ 2 := by
    rw [div_pow, div_le_iff₀ (pow_pos hpos 2)] at hsq
    exact hsq
  have h4 : R ^ 2 * (s1 * z 2 ^ 2) ≤ R ^ 2 * L ^ 2 := by
    have a1 := mul_le_mul_of_nonneg_left h2 hs1.le
    have a2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg L)
    nlinarith [a1, a2]
  have h3 : s1 * z 2 ^ 2 ≤ L ^ 2 := le_of_mul_le_mul_left h4 (by positivity)
  have hn : ‖z‖ ^ 2 = z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  have hQ : ‖z‖ ^ 2 * s1 ≤ R ^ 2 + L ^ 2 := by
    rw [hn, ← hR2]
    nlinarith [h1, h3]
  have hfin : ‖z‖ ^ 2 ≤ (R ^ 2 + L ^ 2) / s1 := by
    rw [le_div_iff₀ hs1]
    exact hQ
  have := Real.abs_le_sqrt hfin
  rwa [abs_of_nonneg (norm_nonneg _)] at this

theorem cartLift_good (R c : ℝ) (hR : 0 < R) (f : Chart → Ten3) (hf : IsBoxTensor f) :
    (∀ j k : Fin 3, Measurable fun s : ℝ × Space => NearInst.cartLift R c f s.1 s.2 j k) ∧
    (∃ M0 : ℝ, ∀ (τ' : ℝ) (z : Space) (a b : Fin 3),
      |NearInst.cartLift R c f τ' z a b| ≤ M0) ∧
    (∃ ρ : ℝ, ∀ (τ' : ℝ) (z : Space), ρ < ‖z‖ → NearInst.cartLift R c f τ' z = 0) := by
  obtain ⟨B, hB⟩ := hf.bounded
  obtain ⟨s1, s2, L, hs1, hband⟩ := hf.band
  refine ⟨fun j k => measurable_cartLift_entry R c f hf.measurable j k,
    ⟨|s2| * |B|, fun τ' z a b => ?_⟩, ⟨Real.sqrt ((R ^ 2 + L ^ 2) / s1), fun τ' z hz => ?_⟩⟩
  · by_cases hp : f (NearInst.chartOf R c z τ') = 0
    · have h0 := cartLift_entry_le R c f τ' z a b
      rw [hp, norm_zero, mul_zero] at h0
      exact h0.trans (by positivity)
    · obtain ⟨h1, h2, _⟩ := hband _ hp
      have hs : 0 ≤ (NearInst.chartOf R c z τ').1 := by
        change 0 ≤ R ^ 2 / NearInst.hRad z ^ 2
        positivity
      have h0 := cartLift_entry_le R c f τ' z a b
      calc |NearInst.cartLift R c f τ' z a b|
          ≤ (NearInst.chartOf R c z τ').1 * ‖f (NearInst.chartOf R c z τ')‖ := h0
        _ ≤ |s2| * |B| :=
          mul_le_mul (h2.trans (le_abs_self s2)) ((hB _).trans (le_abs_self B))
            (norm_nonneg _) (abs_nonneg _)
  · have hf0 : f (NearInst.chartOf R c z τ') = 0 := by
      by_contra hp
      obtain ⟨h1, _, h3⟩ := hband _ hp
      have := chart_band_ball R c τ' s1 L hR hs1 z ⟨h1, h3⟩
      linarith
    refine Matrix.ext fun a b => ?_
    have h0 := cartLift_entry_le R c f τ' z a b
    rw [hf0, norm_zero, mul_zero] at h0
    simpa using abs_nonpos_iff.mp h0

theorem gk1_cont_t (t : ℝ) (ht : 0 < t) : Continuous (gk1Sum t) := by
  unfold gk1Sum
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    continuous_finsetSum _ fun k _ => ?_
  have hd : Continuous (fun w : Space =>
      fderiv ℝ (fun x => UnforcedLeray.Short.IIIa.heatLerayK t i j x) w) :=
    (UnforcedLeray.Short.PartIIIb.Concrete.heatLerayKSmooth t ht i j).continuous_fderiv
      (by norm_num)
  exact continuous_abs.comp (hd.clm_apply continuous_const)

theorem gk1_sup : ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 < t → ∀ x : Space,
    0 ≤ gk1Sum t x ∧ gk1Sum t x ≤ K * (t ^ 2)⁻¹ := by
  obtain ⟨K, hK, hb⟩ := gk1_bound
  refine ⟨K, hK, fun t ht x => ⟨?_, ?_⟩⟩
  · unfold gk1Sum
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      Finset.sum_nonneg fun k _ => abs_nonneg _
  · rw [gk1_gsum_scale t ht x]
    have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
    have hst : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
    have h4 : Real.sqrt t ^ 4 = t ^ 2 := by
      calc Real.sqrt t ^ 4 = (Real.sqrt t ^ 2) ^ 2 := by ring
        _ = t ^ 2 := by rw [hst]
    have hcoef : ((Real.sqrt t)⁻¹ ^ 3 * (Real.sqrt t)⁻¹) = (t ^ 2)⁻¹ := by
      rw [← h4]
      field_simp
    rw [hcoef]
    have h1 : gk1Sum 1 ((Real.sqrt t)⁻¹ • x) ≤ K := by
      refine (hb _).trans ?_
      have hone : 1 ≤ (1 + ‖(Real.sqrt t)⁻¹ • x‖) ^ 4 :=
        one_le_pow₀ (by linarith [norm_nonneg ((Real.sqrt t)⁻¹ • x)])
      have : ((1 + ‖(Real.sqrt t)⁻¹ • x‖) ^ 4)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hone
      nlinarith
    have hc : 0 ≤ (t ^ 2)⁻¹ := by positivity
    nlinarith

theorem Gm_sum_le (t : ℝ) (x : Space) (i : Fin 3) :
    ∑ j : Fin 3, ∑ k : Fin 3, |Gm k i j (t, x)| ≤ gk1Sum t x := by
  have hsingle := Finset.single_le_sum (f := fun i' : Fin 3 => ∑ j : Fin 3, ∑ k : Fin 3,
      |fderiv ℝ (fun y => UnforcedLeray.Short.IIIa.heatLerayK t i' j y) x (coordinateVector k)|)
      (fun i' _ => Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => abs_nonneg _)
      (Finset.mem_univ i)
  have hL : ∑ j : Fin 3, ∑ k : Fin 3, |Gm k i j (t, x)| ≤
      ∑ j : Fin 3, ∑ k : Fin 3,
        |fderiv ℝ (fun y => UnforcedLeray.Short.IIIa.heatLerayK t i j y) x (coordinateVector k)| := by
    by_cases hx : x = 0
    · subst hx
      have h0 : ∀ j k : Fin 3, Gm k i j (t, 0) = 0 := fun j k => by simp [Gm]
      simp only [h0, abs_zero, Finset.sum_const_zero]
      exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => abs_nonneg _
    · refine le_of_eq (Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_)
      rw [Gm_eq k i j t hx]
  unfold gk1Sum
  exact hL.trans hsingle

theorem lint_affine (y : Space) (l : ℝ) (hl : 0 < l) (F : Space → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ z, F (y - l • z) = ENNReal.ofReal ((l ^ 3)⁻¹) * ∫⁻ v, F v := by
  have hG : Measurable fun w : Space => F (y - w) :=
    hF.comp (measurable_const.sub measurable_id)
  have h1 := gk1_lintegral_comp_smul l hl (fun w => F (y - w)) hG
  have h2 : ∫⁻ v, F (y - v) = ∫⁻ v, F v := lintegral_sub_left_eq_self F y
  calc ∫⁻ z, F (y - l • z) = ENNReal.ofReal ((l ^ 3)⁻¹) * ∫⁻ v, F (y - v) := h1
    _ = ENNReal.ofReal ((l ^ 3)⁻¹) * ∫⁻ v, F v := by rw [h2]

theorem measurable_gradKNorm (t : ℝ) (ht : 0 < t) : Measurable (gradKNorm t) :=
  ENNReal.measurable_ofReal.comp (gk1_cont_t t ht).measurable

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.LinAux
