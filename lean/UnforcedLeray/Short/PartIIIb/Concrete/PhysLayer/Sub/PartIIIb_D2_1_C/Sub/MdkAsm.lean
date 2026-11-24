import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjMollLocInt
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_2_1_2

/-!
# Assembly of the divergence identity `DivIdentity` from S2-S5

Source: `the November 2 reference manuscript`,
lines 1351-1362. Uses the Props `DyMollP`, `FoldCell`, `DyPerK`, `PhaseIntCell` of the defs file.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

lemma mdkasm_reflK_contDiff (ρ : ContDiffBump (0 : ℝ × Space)) (x : ℝ × Space) :
    ContDiff ℝ ∞ (reflK ρ x) := by
  unfold reflK
  exact Complex.ofRealCLM.contDiff.comp (ρ.contDiff_normed.comp (contDiff_const.sub contDiff_id))

lemma mdkasm_reflK_hasCompactSupport (ρ : ContDiffBump (0 : ℝ × Space)) (x : ℝ × Space) :
    HasCompactSupport (reflK ρ x) := by
  have h1 : HasCompactSupport (fun w : ℝ × Space => ρ.normed volume (x - w)) :=
    (ρ.hasCompactSupport_normed (μ := volume)).comp_homeomorph (Homeomorph.subLeft x)
  unfold reflK
  exact h1.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)

lemma mdkasm_dyK_continuous (ρ : ContDiffBump (0 : ℝ × Space)) (x : ℝ × Space) (j : Fin 3) :
    Continuous (dy j (reflK ρ x)) := by
  have h := (mdkasm_reflK_contDiff ρ x).continuous_fderiv (by simp)
  exact h.clm_apply continuous_const

lemma mdkasm_dyK_hasCompactSupport (ρ : ContDiffBump (0 : ℝ × Space)) (x : ℝ × Space) (j : Fin 3) :
    HasCompactSupport (dy j (reflK ρ x)) :=
  (mdkasm_reflK_hasCompactSupport ρ x).fderiv_apply ℝ _

lemma mdkasm_dyK_bound (ρ : ContDiffBump (0 : ℝ × Space)) (x : ℝ × Space) (j : Fin 3) :
    ∃ R : ℝ, ∀ z : ℝ × Space, R < ‖z‖ → dy j (reflK ρ x) z = 0 := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ × Space)).1
    (mdkasm_dyK_hasCompactSupport ρ x j).isCompact.isBounded
  refine ⟨R, fun z hz => ?_⟩
  by_contra hne
  have hmem : z ∈ tsupport (dy j (reflK ρ x)) := subset_tsupport _ (Function.mem_support.2 hne)
  have := hR hmem
  rw [Metric.mem_closedBall, dist_zero_right] at this
  linarith

lemma mdkasm_integrable_dyK_smul (ρ : ContDiffBump (0 : ℝ × Space)) (x : ℝ × Space) (j : Fin 3)
    {Φ : ℝ × Space → CVec3} (hli : LocallyIntegrable Φ volume) :
    Integrable (fun w => dy j (reflK ρ x) w • Φ w) volume := by
  have hL : LocallyIntegrable (fun w => dy j (reflK ρ x) w • Φ w) volume :=
    LocallyIntegrable.continuous_smul (mdkasm_dyK_continuous ρ x j) hli
  have hsupp : Function.support (fun w => dy j (reflK ρ x) w • Φ w) ⊆
      tsupport (dy j (reflK ρ x)) := by
    intro w hw
    refine subset_tsupport _ (Function.mem_support.2 fun h0 => ?_)
    exact (Function.mem_support.1 hw) (by simp [h0])
  exact (integrableOn_iff_integrable_of_support_subset hsupp).1
    (hL.integrableOn_isCompact (mdkasm_dyK_hasCompactSupport ρ x j).isCompact)

lemma mdkasm_gradT_apply (φ : ℝ × Space → ℂ) (w : ℝ × Space) (i : Fin 3) :
    gradT φ w i = dy i φ w := by
  simp [gradT, Pi.single_apply, mul_ite]

/-- Integrable periodisation on the base cell: a compactly supported integrable `G` has a
finitely supported periodisation on `(0,P] × ℝ³`. -/
lemma mdkasm_periodize_integrableOn {G : ℝ × Space → ℂ} {P : ℝ} (hP : 0 < P)
    (hGi : Integrable G volume) {R : ℝ} (hR : ∀ z : ℝ × Space, R < ‖z‖ → G z = 0) :
    IntegrableOn (fun w : ℝ × Space => ∑' k : ℤ, G (w + ((k : ℝ) * P, (0 : Space))))
      (cellBase P) volume := by
  obtain ⟨N, hN⟩ := exists_nat_ge ((R + P) / P)
  have hNP : R + P ≤ (N : ℝ) * P := by
    have := (div_le_iff₀ hP).1 hN
    linarith
  have hfin : ∀ w ∈ cellBase P, ∑' k : ℤ, G (w + ((k : ℝ) * P, (0 : Space)))
      = ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), G (w + ((k : ℝ) * P, (0 : Space))) := by
    intro w hw
    refine tsum_eq_sum (fun k hk => hR _ ?_)
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hk
    have hk' : (N : ℝ) + 1 ≤ |(k : ℝ)| := by
      rcases hk with hk | hk
      · have h1 : (k : ℤ) + 1 ≤ -(N : ℤ) := by omega
        have h2 : (k : ℝ) + 1 ≤ -(N : ℝ) := by exact_mod_cast h1
        exact le_abs.2 (Or.inr (by linarith))
      · have h1 : (N : ℤ) + 1 ≤ k := by omega
        have h2 : (N : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast h1
        exact le_abs.2 (Or.inl (by linarith))
    have hA : ((N : ℝ) + 1) * P ≤ |(k : ℝ) * P| := by
      rw [abs_mul, abs_of_pos hP]
      nlinarith
    have hw1 : |w.1| ≤ P := by
      have h0 : 0 < w.1 := hw.1.1
      have h1 : w.1 ≤ P := hw.1.2
      exact abs_le.2 ⟨by linarith, h1⟩
    have htri : |(k : ℝ) * P| ≤ |w.1 + (k : ℝ) * P| + |w.1| := by
      have h := abs_add_le (w.1 + (k : ℝ) * P) (-w.1)
      rw [abs_neg] at h
      have e : w.1 + (k : ℝ) * P + -w.1 = (k : ℝ) * P := by ring
      rwa [e] at h
    refine lt_of_lt_of_le ?_ (norm_fst_le _)
    show R < ‖w.1 + (k : ℝ) * P‖
    rw [Real.norm_eq_abs]
    linarith
  have hfinInt : IntegrableOn
      (fun w : ℝ × Space => ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), G (w + ((k : ℝ) * P, (0 : Space))))
      (cellBase P) volume := by
    refine (integrable_finsetSum _ fun k _ => ?_).integrableOn
    exact hGi.comp_add_right _
  exact hfinInt.congr_fun (fun w hw => (hfin w hw).symm) (measurableSet_cellBase P)

theorem divIdentity_of (h2 : DyMollP) (h3 : FoldCell) (h4 : DyPerK) (h5 : PhaseIntCell) :
    DivIdentity := by
  intro ρ x P hP Φ hli _hsupp hper
  -- a.e. invariance of Φ under all integer shifts
  have hshift : ∀ᵐ w : ℝ × Space, ∀ k : ℤ, Φ (w + ((k : ℝ) * P, (0 : Space))) = Φ w := by
    filter_upwards [ae_all_iff.2 (fun k => ae_shift_int hper k)] with w hw k
    rw [show w + ((k : ℝ) * P, (0 : Space)) = (w.1 + (k : ℝ) * P, w.2) from
      Prod.ext (by simp) (by simp)]
    exact hw k
  -- integrability of the component integrands
  have hGint : ∀ j : Fin 3, Integrable (fun w => -(dy j (reflK ρ x) w) * Φ w j) volume := by
    intro j
    have h1 := ContinuousLinearMap.integrable_comp (EuclideanSpace.proj j : CVec3 →L[ℂ] ℂ)
      (mdkasm_integrable_dyK_smul ρ x j hli)
    refine (h1.neg).congr (Filter.Eventually.of_forall fun w => ?_)
    simp
  -- the periodised cell integrands
  have hSint : ∀ j : Fin 3, IntegrableOn
      (fun w : ℝ × Space => ∑' k : ℤ, -(dy j (reflK ρ x)) (w + ((k : ℝ) * P, (0 : Space))) *
        Φ (w + ((k : ℝ) * P, (0 : Space))) j) (cellBase P) volume := by
    intro j
    obtain ⟨R, hR⟩ := mdkasm_dyK_bound ρ x j
    exact mdkasm_periodize_integrableOn hP (hGint j) (R := R) fun z hz => by
      simp [hR z hz]
  -- pointwise a.e. identification of the periodised integrand with the periodised kernel
  have hae : ∀ j : Fin 3, ∀ᵐ w : ℝ × Space,
      (∑' k : ℤ, -(dy j (reflK ρ x)) (w + ((k : ℝ) * P, (0 : Space))) *
        Φ (w + ((k : ℝ) * P, (0 : Space))) j) = -(dy j (perK ρ x P) w) * Φ w j := by
    intro j
    filter_upwards [hshift] with w hw
    simp only [hw]
    rw [tsum_mul_right, tsum_neg, h4 ρ x hP j w]
  have hHint : ∀ j : Fin 3, IntegrableOn (fun w => -(dy j (perK ρ x P) w) * Φ w j)
      (cellBase P) volume := fun j => (hSint j).congr_fun_ae (ae_restrict_of_ae (hae j))
  -- each component of the left side in terms of the cell integral
  have hL : ∀ j : Fin 3, dy j (mollP ρ Φ) x j =
      ∫ w in cellBase P, -(dy j (perK ρ x P) w) * Φ w j := by
    intro j
    rw [h2 ρ Φ hli x j, h3 hP (hGint j)]
    exact setIntegral_congr_ae (measurableSet_cellBase P) ((hae j).mono fun w hw _ => hw)
  have hsum : ∑ j : Fin 3, dy j (mollP ρ Φ) x j =
      ∫ w in cellBase P, ∑ j : Fin 3, -(dy j (perK ρ x P) w) * Φ w j := by
    rw [integral_finsetSum _ (fun j _ => hHint j)]
    exact Finset.sum_congr rfl fun j _ => hL j
  -- pointwise identity of the summed integrand with the dotL pairing
  have hpt : ∀ w : ℝ × Space, ∑ j : Fin 3, -(dy j (perK ρ x P) w) * Φ w j =
      -(dotL (gradT (perK ρ x P) w) (Φ w)) := by
    intro w
    rw [dotL_apply, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mdkasm_gradT_apply]
    ring
  have hIcell : IntegrableOn (fun w => ∑ j : Fin 3, -(dy j (perK ρ x P) w) * Φ w j)
      (cellBase P) volume :=
    integrable_finsetSum _ fun j _ => hHint j
  have hGint' : IntegrableOn (fun w => dotL (gradT (perK ρ x P) w) (Φ w)) (cellBase P) volume := by
    refine (hIcell.neg).congr_fun (fun w _ => ?_) (measurableSet_cellBase P)
    show -(∑ j : Fin 3, -(dy j (perK ρ x P) w) * Φ w j) = dotL (gradT (perK ρ x P) w) (Φ w)
    rw [hpt w, neg_neg]
  have hfun : (fun w => ∑ j : Fin 3, -(dy j (perK ρ x P) w) * Φ w j) =
      fun w => -(dotL (gradT (perK ρ x P) w) (Φ w)) := funext hpt
  have hPc : (P : ℂ) ≠ 0 := by exact_mod_cast hP.ne'
  have hpairF : pairF P (gradT (perK ρ x P)) Φ =
      phaseInt P (fun w => dotL (gradT (perK ρ x P) w) (Φ w)) := rfl
  rw [hsum, hfun, integral_neg, hpairF, h5 hP _ hGint', Complex.real_smul]
  push_cast
  field_simp

end UnforcedLeray.Short.PartIIIb.Concrete
