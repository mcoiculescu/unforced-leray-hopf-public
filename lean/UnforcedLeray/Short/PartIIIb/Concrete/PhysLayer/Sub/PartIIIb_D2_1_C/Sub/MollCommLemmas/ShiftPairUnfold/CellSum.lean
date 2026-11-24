import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_2_4_org_3
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjMollLocInt

/-!
# `ShiftPairCellSum`: exchanging the periodising sum with the cell integral

Source `the November 2 reference manuscript` lines 1351-1362, 1556-1583.
The kernel `κ` has compact support, so there is one finite window `Finset.Icc (-N) N` of
indices `k` such that `κ(x - w + (kP,0)) = 0` for every `w` in the base cell `(0,P] × ℝ³`.
On the cell the periodised sum is therefore a finite sum, which is exchanged with the cell
integral (Fubini on `Ioc ×ˢ univ`, `integral_prod`) and with the integral over the cell of each
term (`integral_finset_sum`); the terms with `k` outside the window vanish on the cell.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem sc_dot_real (e : CVec3) (r : ℝ) (v : CVec3) : dotL e (r • v) = (r : ℂ) * dotL e v := by
  rw [show r • v = (r : ℂ) • v from (Complex.coe_smul r v).symm, map_smul, smul_eq_mul]

/-- `w ↦ g(w) e·F(w)` is integrable for a locally integrable `F` and a continuous kernel `g` with
compact support. -/
theorem sc_int_kernel {F : ℝ × Space → CVec3} (hF : LocallyIntegrable F volume) (e : CVec3)
    {g : ℝ × Space → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun w => ((g w : ℝ) : ℂ) * dotL e (F w)) volume := by
  have h1 : Integrable (fun w => g w • F w) volume :=
    hF.integrable_smul_left_of_hasCompactSupport hg hgc
  have h2 := (dotL e).integrable_comp h1
  have h3 : (fun w => ((g w : ℝ) : ℂ) * dotL e (F w)) = fun w => dotL e (g w • F w) := by
    funext w
    rw [sc_dot_real]
  rw [h3]
  exact h2

/-- Unfolding the integral over the product cell `(0,P] ×ˢ ℝ³` as an iterated integral. -/
theorem sc_prod_cell {g : ℝ × Space → ℂ} {P : ℝ}
    (hg : IntegrableOn g (Ioc (0 : ℝ) P ×ˢ (univ : Set Space))) :
    ∫ w in Ioc (0 : ℝ) P ×ˢ (univ : Set Space), g w
      = ∫ t in Ioc (0 : ℝ) P, ∫ y : Space, g (t, y) := by
  have hmeas : (volume : Measure (ℝ × Space)).restrict (Ioc (0 : ℝ) P ×ˢ (univ : Set Space))
      = (volume.restrict (Ioc (0 : ℝ) P)).prod (volume.restrict (univ : Set Space)) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  have h : Integrable g ((volume.restrict (Ioc (0 : ℝ) P)).prod
      (volume.restrict (univ : Set Space))) := by
    rw [← hmeas]
    exact hg
  rw [hmeas, integral_prod g h]
  simp only [Measure.restrict_univ]

theorem shiftPairCellSum : ShiftPairCellSum := by
  intro P hP κ hκ hcs F hF x e
  have hloc : LocallyIntegrable F volume := locInt_of_isInYr hP hF
  obtain ⟨R, hR⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : ℝ × Space)).mp hcs.isCompact.isBounded
  have hsupp : ∀ z : ℝ × Space, κ z ≠ 0 → ‖z‖ ≤ R := fun z hz =>
    mem_closedBall_zero_iff.mp (hR (subset_tsupport κ (Function.mem_support.mpr hz)))
  -- one finite window of indices serves the whole base cell
  obtain ⟨N, key⟩ : ∃ N : ℤ, ∀ w : ℝ × Space, w.1 ∈ Ioc (0 : ℝ) P → ∀ k : ℤ,
      κ (x - w + ((k : ℝ) * P, (0 : Space))) ≠ 0 → k ∈ Finset.Icc (-N) N := by
    refine ⟨⌈(R + |x.1| + P) / P⌉, fun w hw k hk => ?_⟩
    obtain ⟨hw0, hwP⟩ := hw
    have h3 : ‖(x - w + ((k : ℝ) * P, (0 : Space))).1‖ ≤ R :=
      (norm_fst_le _).trans (hsupp _ hk)
    simp only [Prod.fst_add, Prod.fst_sub, Real.norm_eq_abs] at h3
    have hb := abs_le.mp h3
    have hA : |(k : ℝ) * P| ≤ R + |x.1| + P :=
      abs_le.mpr ⟨by linarith [hb.1, hw0, le_abs_self x.1, hP],
        by linarith [hb.2, neg_le_abs x.1, hwP]⟩
    have hC : |(k : ℝ)| * P ≤ R + |x.1| + P := by
      have h4 := hA
      rw [abs_mul, abs_of_pos hP] at h4
      exact h4
    have hkabs : |(k : ℝ)| ≤ (R + |x.1| + P) / P := (le_div_iff₀ hP).mpr hC
    have hkN : |(k : ℝ)| ≤ ((⌈(R + |x.1| + P) / P⌉ : ℤ) : ℝ) := hkabs.trans (Int.le_ceil _)
    have hkZ : |k| ≤ ⌈(R + |x.1| + P) / P⌉ := by
      have h5 : ((|k| : ℤ) : ℝ) ≤ ((⌈(R + |x.1| + P) / P⌉ : ℤ) : ℝ) := by
        rw [Int.cast_abs]
        exact hkN
      exact_mod_cast h5
    exact Finset.mem_Icc.mpr (abs_le.mp hkZ)
  have hwin : ∀ w : ℝ × Space, w.1 ∈ Ioc (0 : ℝ) P → ∀ k : ℤ, k ∉ Finset.Icc (-N) N →
      κ (x - w + ((k : ℝ) * P, (0 : Space))) = 0 :=
    fun w hw k hk => by
      by_contra h
      exact hk (key w hw k h)
  -- each translated term is integrable on the whole space
  have hφ : ∀ k : ℤ, Integrable (fun w : ℝ × Space =>
      ((κ (x - w + ((k : ℝ) * P, (0 : Space))) : ℝ) : ℂ) * dotL e (F w)) volume := by
    intro k
    have hg : Continuous (fun w : ℝ × Space => κ (x - w + ((k : ℝ) * P, (0 : Space)))) :=
      hκ.continuous.comp ((continuous_const.sub continuous_id).add continuous_const)
    have hgc : HasCompactSupport (fun w : ℝ × Space => κ (x - w + ((k : ℝ) * P, (0 : Space)))) := by
      have := hcs.comp_homeomorph
        ((Homeomorph.subLeft x).trans (Homeomorph.addRight ((k : ℝ) * P, (0 : Space))))
      exact this
    exact sc_int_kernel hloc e hg hgc
  -- pointwise on the base cell: the periodising sum is a finite sum
  have hpt : ∀ w : ℝ × Space, w.1 ∈ Ioc (0 : ℝ) P →
      (((∑' k : ℤ, κ (x - w + ((k : ℝ) * P, (0 : Space)))) : ℝ) : ℂ) * dotL e (F w)
        = ∑ k ∈ Finset.Icc (-N) N,
            ((κ (x - w + ((k : ℝ) * P, (0 : Space))) : ℝ) : ℂ) * dotL e (F w) := by
    intro w hw
    rw [tsum_eq_sum (s := Finset.Icc (-N) N) (fun k hk => hwin w hw k hk), Complex.ofReal_sum,
      Finset.sum_mul]
  have hL : ∫ t in Ioc (0 : ℝ) P, ∫ y : Space,
      (((∑' k : ℤ, κ (x - (t, y) + ((k : ℝ) * P, (0 : Space)))) : ℝ) : ℂ) * dotL e (F (t, y))
      = ∫ t in Ioc (0 : ℝ) P, ∫ y : Space,
          ∑ k ∈ Finset.Icc (-N) N,
            ((κ (x - (t, y) + ((k : ℝ) * P, (0 : Space))) : ℝ) : ℂ) * dotL e (F (t, y)) := by
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => hpt (t, y) ht)
  have hprodInt : IntegrableOn (fun w : ℝ × Space =>
      ∑ k ∈ Finset.Icc (-N) N, ((κ (x - w + ((k : ℝ) * P, (0 : Space))) : ℝ) : ℂ) * dotL e (F w))
      (Ioc (0 : ℝ) P ×ˢ (univ : Set Space)) :=
    (integrable_finsetSum _ fun k _ => hφ k).integrableOn
  have hcellSum : ∫ w in Ioc (0 : ℝ) P ×ˢ (univ : Set Space),
      ∑ k ∈ Finset.Icc (-N) N, ((κ (x - w + ((k : ℝ) * P, (0 : Space))) : ℝ) : ℂ) * dotL e (F w)
      = ∑ k ∈ Finset.Icc (-N) N, ∫ w in Ioc (0 : ℝ) P ×ˢ (univ : Set Space),
          ((κ (x - w + ((k : ℝ) * P, (0 : Space))) : ℝ) : ℂ) * dotL e (F w) :=
    integral_finsetSum _ fun k _ => (hφ k).integrableOn
  have hRHS : ∑' k : ℤ, ∫ w in Ioc (0 : ℝ) P ×ˢ (univ : Set Space),
      ((κ (x - w + ((k : ℝ) * P, (0 : Space))) : ℝ) : ℂ) * dotL e (F w)
      = ∑ k ∈ Finset.Icc (-N) N, ∫ w in Ioc (0 : ℝ) P ×ˢ (univ : Set Space),
          ((κ (x - w + ((k : ℝ) * P, (0 : Space))) : ℝ) : ℂ) * dotL e (F w) := by
    refine tsum_eq_sum (s := Finset.Icc (-N) N) (fun k hk => ?_)
    exact setIntegral_eq_zero_of_forall_eq_zero fun w hw => by
      simp [hwin w hw.1 k hk]
  exact hL.trans ((sc_prod_cell hprodInt).symm.trans (hcellSum.trans hRHS.symm))

end UnforcedLeray.Short.PartIIIb.Concrete
