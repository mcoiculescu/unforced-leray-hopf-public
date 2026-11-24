import UnforcedLeray.Short.PartIIb.Sub.T22_1_10_1
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.HeatCont

/-!


Proves `DParamCont` (`Sub/T22_1_10_1.lean`). For `r < τ` the heat semigroup and the derivative
kernel are rescaled by `a = ν(τ-r)`, which turns them into integrals over a fixed kernel `heatK 1`
with `r`-dependent shifts and (for the derivative) `r`-dependent coefficients. On `[s, τ₁]` with
`τ₁ < τ` these are dominated uniformly; a localisation argument then gives continuity on `[s, τ)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb.CylPDE

namespace DPC

/-- Localisation: continuity on `Icc s τ₁ × univ` for every `τ₁ < τ` gives continuity on
`Ico s τ × univ`. -/
lemma contOn_Ico_of_Icc {f : ℝ × Pl → ℝ} {s τ : ℝ}
    (h : ∀ τ1 : ℝ, τ1 < τ → ContinuousOn f (Icc s τ1 ×ˢ univ)) :
    ContinuousOn f (Ico s τ ×ˢ univ) := by
  intro p hp
  obtain ⟨τ1, hlt, hlt2⟩ : ∃ τ1 : ℝ, p.1 < τ1 ∧ τ1 < τ :=
    ⟨(p.1 + τ) / 2, by linarith [hp.1.2], by linarith [hp.1.2]⟩
  have hU : Iio τ1 ×ˢ (univ : Set Pl) ∈ 𝓝 p :=
    (isOpen_Iio.prod isOpen_univ).mem_nhds ⟨hlt, mem_univ _⟩
  have hmem : (Icc s τ1 ×ˢ (univ : Set Pl)) ∈ 𝓝[Ico s τ ×ˢ univ] p := by
    refine Filter.mem_of_superset (inter_mem_nhdsWithin _ hU) ?_
    rintro q ⟨hq, hqU⟩
    exact ⟨⟨hq.1.1, le_of_lt hqU.1⟩, mem_univ _⟩
  exact ((h τ1 hlt2) p ⟨⟨hp.1.1, hlt.le⟩, mem_univ _⟩).mono_of_mem_nhdsWithin hmem

/-- Dominated continuity of a parametric integral on `Icc s τ₁ × univ`. -/
lemma contOn_param_int {s τ1 T : ℝ} (hτ1 : τ1 ≤ T) (g : ℝ → Pl → ℝ)
    (hg : ContinuousOn (fun z : ℝ × Pl => g z.1 z.2) (Icc s T ×ˢ univ))
    (M : ℝ) (hM : ∀ r ∈ Icc s T, ∀ z : Pl, |g r z| ≤ M)
    (S : ℝ → ℝ) (hS : ContinuousOn S (Icc s τ1))
    (K : ℝ → Pl → ℝ) (hK : ContinuousOn (fun z : ℝ × Pl => K z.1 z.2) (Icc s τ1 ×ˢ univ))
    (kb : Pl → ℝ) (hkb : Integrable kb) (hKb : ∀ r ∈ Icc s τ1, ∀ w : Pl, |K r w| ≤ kb w) :
    ContinuousOn (fun z : ℝ × Pl => ∫ w : Pl, K z.1 w * g z.1 (z.2 - S z.1 • w))
      (Icc s τ1 ×ˢ univ) := by
  have hgr : ∀ r ∈ Icc s T, Continuous (fun z : Pl => g r z) := fun r hr =>
    hg.comp_continuous (continuous_const.prodMk continuous_id) (fun z => ⟨hr, mem_univ _⟩)
  refine continuousOn_of_dominated (F := fun z : ℝ × Pl => fun w : Pl =>
      K z.1 w * g z.1 (z.2 - S z.1 • w)) (bound := fun w => kb w * M) ?_ ?_ (hkb.mul_const M) ?_
  · rintro z hz
    have hr' : z.1 ∈ Icc s T := ⟨hz.1.1, hz.1.2.trans hτ1⟩
    have hKw : Continuous (fun w : Pl => K z.1 w) :=
      hK.comp_continuous (continuous_const.prodMk continuous_id) (fun w => ⟨hz.1, mem_univ _⟩)
    have hgw : Continuous (fun w : Pl => g z.1 (z.2 - S z.1 • w)) :=
      (hgr z.1 hr').comp (continuous_const.sub (continuous_id.const_smul (S z.1)))
    exact (hKw.mul hgw).aestronglyMeasurable
  · rintro z hz
    refine ae_of_all _ (fun w => ?_)
    have hr : z.1 ∈ Icc s τ1 := hz.1
    have hr' : z.1 ∈ Icc s T := ⟨hr.1, hr.2.trans hτ1⟩
    show ‖K z.1 w * g z.1 (z.2 - S z.1 • w)‖ ≤ kb w * M
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hKb z.1 hr w) (hM z.1 hr' _) (abs_nonneg _)
      ((abs_nonneg _).trans (hKb z.1 hr w))
  · refine ae_of_all _ (fun w => ?_)
    have hKz : ContinuousOn (fun z : ℝ × Pl => K z.1 w) (Icc s τ1 ×ˢ univ) :=
      hK.comp (continuousOn_fst.prodMk continuousOn_const) (fun z hz => ⟨hz.1, mem_univ _⟩)
    have hmap : ContinuousOn (fun z : ℝ × Pl => (z.1, z.2 - S z.1 • w)) (Icc s τ1 ×ˢ univ) :=
      continuousOn_fst.prodMk (continuousOn_snd.sub
        ((hS.comp continuousOn_fst (fun z hz => hz.1)).smul continuousOn_const))
    have hgz : ContinuousOn (fun z : ℝ × Pl => g z.1 (z.2 - S z.1 • w)) (Icc s τ1 ×ˢ univ) :=
      hg.comp hmap (fun z hz => ⟨⟨hz.1.1, hz.1.2.trans hτ1⟩, mem_univ _⟩)
    exact hKz.mul hgz

/-- Derivative of the scaled heat semigroup: `∂_i K_a * g = ∫ (-(w_i)/(2√a)) K_1(w) g(x - √a w)`. -/
lemma heatSGd_pos_eq {a : ℝ} (ha : 0 < a) (i : Fin 2) (g : Pl → ℝ) (x : Pl) :
    heatSGd i a g x = ∫ w : Pl,
      (-(![w.1, w.2] i) / (2 * Real.sqrt a)) * heatK 1 w * g (x - Real.sqrt a • w) := by
  unfold heatSGd
  have h1 : ∫ y : Pl, heatKd i a (x - y) * g y = ∫ u : Pl, heatKd i a u * g (x - u) := by
    rw [← integral_sub_left_eq_self (fun u : Pl => heatKd i a u * g (x - u)) volume x]
    congr 1
    funext y
    simp
  have h2 := MeasureTheory.Measure.integral_comp_smul (volume : Measure Pl)
    (fun u : Pl => heatKd i a u * g (x - u)) (Real.sqrt a)
  rw [HC.finrank_pl] at h2
  have hs : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  rw [hs, abs_of_pos (inv_pos.2 ha), smul_eq_mul] at h2
  have hpt : ∀ w : Pl, a * (heatKd i a (Real.sqrt a • w) * g (x - Real.sqrt a • w)) =
      (-(![w.1, w.2] i) / (2 * Real.sqrt a)) * heatK 1 w * g (x - Real.sqrt a • w) := by
    intro w
    have hsc := HC.heatK_scale ha w
    have hvec : ![(Real.sqrt a • w).1, (Real.sqrt a • w).2] i = Real.sqrt a * ![w.1, w.2] i := by
      fin_cases i <;> simp
    have hsq : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha.le
    have hsqpos : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
    unfold heatKd
    rw [hvec, ← hsc]
    generalize heatK a (Real.sqrt a • w) = K
    obtain ⟨s, hs_eq⟩ : ∃ s, s = Real.sqrt a := ⟨_, rfl⟩
    have hsa : a = s * s := by rw [hs_eq, hsq]
    have hspos : s ≠ 0 := by rw [hs_eq]; exact hsqpos.ne'
    rw [← hs_eq, hsa]
    field_simp
  rw [h1]
  calc ∫ u : Pl, heatKd i a u * g (x - u)
      = a * ∫ w : Pl, heatKd i a (Real.sqrt a • w) * g (x - Real.sqrt a • w) := by
        rw [h2, ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]
    _ = ∫ w : Pl, a * (heatKd i a (Real.sqrt a • w) * g (x - Real.sqrt a • w)) :=
        (integral_const_mul _ _).symm
    _ = ∫ w : Pl, (-(![w.1, w.2] i) / (2 * Real.sqrt a)) * heatK 1 w * g (x - Real.sqrt a • w) := by
        congr 1
        funext w
        exact hpt w

end DPC

open DPC in
/-- **`PartII-b:T22/1/10/1/1`** Parametric continuity of the heat integrands (`DParamCont`). -/
theorem dParamCont : UnforcedLeray.Short.IIb.CylPDE.DParamCont := by
  intro ν s T hν hsT g b hH τ hτ
  obtain ⟨hgc, hbc, hb0, hgb⟩ := hH
  obtain ⟨M0, hM0⟩ := (isCompact_Icc (a := s) (b := T)).exists_bound_of_continuousOn hbc
  have hM' : ∀ r ∈ Icc s T, |b r| ≤ M0 := fun r hr => by
    have := hM0 r hr
    rwa [Real.norm_eq_abs] at this
  have hgM : ∀ r ∈ Icc s T, ∀ z : Pl, |g r z| ≤ M0 := by
    intro r hr z
    have h1 := hgb r hr z
    have h2 : 1 ≤ Real.cosh z.2 := Real.one_le_cosh _
    have h3 := hM' r hr
    have h4 := le_abs_self (b r)
    nlinarith [abs_nonneg (g r z), mul_nonneg (abs_nonneg (g r z)) (sub_nonneg.2 h2)]
  have hτT : τ ≤ T := hτ.2
  have hpos : ∀ τ1 : ℝ, τ1 < τ → ∀ r ∈ Icc s τ1, 0 < ν * (τ - r) :=
    fun τ1 h1 r hr => mul_pos hν (by linarith [hr.2])
  have hpw : ∀ w : Pl, 0 < heatK 1 w := fun w => (heatKernelMoments 1 one_pos).1 w
  have hI1 : Integrable (heatK 1) := (heatKernelMoments 1 one_pos).2.1
  have hv : ∀ i : Fin 2, Continuous (fun w : Pl => ![w.1, w.2] i) := by
    intro i
    fin_cases i <;> simp [continuous_fst, continuous_snd]
  have hK1c : Continuous (heatK 1) := HC.heatK1_continuous
  refine ⟨?_, fun i => ?_⟩
  · apply contOn_Ico_of_Icc (f := fun z : ℝ × Pl => heatSG (ν * (τ - z.1)) (g z.1) z.2)
    intro τ1 hτ1
    have hτ1T : τ1 ≤ T := hτ1.le.trans hτT
    have hS : ContinuousOn (fun r : ℝ => Real.sqrt (ν * (τ - r))) (Icc s τ1) :=
      (Real.continuous_sqrt.comp (continuous_const.mul (continuous_const.sub continuous_id))).continuousOn
    have hK : ContinuousOn (fun z : ℝ × Pl => heatK 1 z.2) (Icc s τ1 ×ˢ univ) :=
      (hK1c.comp continuous_snd).continuousOn
    have hKb : ∀ r ∈ Icc s τ1, ∀ w : Pl, |heatK 1 w| ≤ heatK 1 w :=
      fun r _ w => le_of_eq (abs_of_pos (hpw w))
    refine ContinuousOn.congr (contOn_param_int hτ1T g hgc M0 hgM
      (fun r => Real.sqrt (ν * (τ - r))) hS (fun _ w => heatK 1 w) hK (heatK 1) hI1 hKb) ?_
    intro z hz
    exact HC.heatSG_pos_eq (hpos τ1 hτ1 z.1 hz.1) (g z.1) z.2
  · apply contOn_Ico_of_Icc (f := fun z : ℝ × Pl => heatSGd i (ν * (τ - z.1)) (g z.1) z.2)
    intro τ1 hτ1
    have hτ1T : τ1 ≤ T := hτ1.le.trans hτT
    have hS : ContinuousOn (fun r : ℝ => Real.sqrt (ν * (τ - r))) (Icc s τ1) :=
      (Real.continuous_sqrt.comp (continuous_const.mul (continuous_const.sub continuous_id))).continuousOn
    have hden : ContinuousOn (fun z : ℝ × Pl => 2 * Real.sqrt (ν * (τ - z.1)))
        (Icc s τ1 ×ˢ univ) :=
      (continuous_const.mul (Real.continuous_sqrt.comp
        (continuous_const.mul (continuous_const.sub continuous_fst)))).continuousOn
    have hne : ∀ z ∈ Icc s τ1 ×ˢ (univ : Set Pl), 2 * Real.sqrt (ν * (τ - z.1)) ≠ 0 :=
      fun z hz => (mul_pos two_pos (Real.sqrt_pos.2 (hpos τ1 hτ1 z.1 hz.1))).ne'
    have hnum : ContinuousOn (fun z : ℝ × Pl => -(![z.2.1, z.2.2] i)) (Icc s τ1 ×ˢ univ) :=
      (((hv i).comp continuous_snd).neg).continuousOn
    have hK : ContinuousOn (fun z : ℝ × Pl =>
        (-(![z.2.1, z.2.2] i) / (2 * Real.sqrt (ν * (τ - z.1)))) * heatK 1 z.2)
        (Icc s τ1 ×ˢ univ) :=
      (hnum.div hden hne).mul ((hK1c.comp continuous_snd).continuousOn)
    have hρ : 0 < Real.sqrt (ν * (τ - τ1)) := Real.sqrt_pos.2 (mul_pos hν (by linarith))
    have hKb : ∀ r ∈ Icc s τ1, ∀ w : Pl,
        |(-(![w.1, w.2] i) / (2 * Real.sqrt (ν * (τ - r)))) * heatK 1 w|
          ≤ |heatKd i 1 w| / Real.sqrt (ν * (τ - τ1)) := by
      intro r hr w
      have hra : Real.sqrt (ν * (τ - τ1)) ≤ Real.sqrt (ν * (τ - r)) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (by linarith [hr.2]) hν.le)
      have hra0 : 0 < Real.sqrt (ν * (τ - r)) := Real.sqrt_pos.2 (hpos τ1 hτ1 r hr)
      have hd : |heatKd i 1 w| = |![w.1, w.2] i| / (2 * 1) * heatK 1 w := by
        unfold heatKd
        rw [abs_mul, abs_div, abs_neg, abs_of_pos (hpw w)]
        simp
      rw [abs_mul, abs_div, abs_neg, abs_of_pos (hpw w), abs_of_pos (mul_pos two_pos hra0), hd]
      have h1 : |![w.1, w.2] i| / (2 * Real.sqrt (ν * (τ - r))) * heatK 1 w
          ≤ |![w.1, w.2] i| / (2 * Real.sqrt (ν * (τ - τ1))) * heatK 1 w := by
        apply mul_le_mul_of_nonneg_right _ (hpw w).le
        apply div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
        linarith
      have h2 : |![w.1, w.2] i| / (2 * Real.sqrt (ν * (τ - τ1))) * heatK 1 w
          = |![w.1, w.2] i| / (2 * 1) * heatK 1 w / Real.sqrt (ν * (τ - τ1)) := by
        field_simp
      linarith [h1, h2]
    have hkbi : Integrable (fun w : Pl => |heatKd i 1 w| / Real.sqrt (ν * (τ - τ1))) := by
      have hc : Continuous (heatKd i 1) := by
        unfold heatKd heatK
        exact (((hv i).neg).div_const (2 * 1)).mul (by fun_prop)
      have hint := ((heatKernelMoments 1 one_pos).2.2.2.2.2 i).1
      have hmeas : AEStronglyMeasurable (fun w : Pl => |heatKd i 1 w|) volume :=
        (continuous_abs.comp hc).aestronglyMeasurable
      have hI : Integrable (fun w : Pl => |heatKd i 1 w|) :=
        Integrable.mono' hint hmeas (ae_of_all _ fun w => by
          rw [Real.norm_eq_abs, abs_abs]
          exact le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_cosh _))
      exact hI.div_const _
    refine ContinuousOn.congr (contOn_param_int hτ1T g hgc M0 hgM
      (fun r => Real.sqrt (ν * (τ - r))) hS
      (fun r w => (-(![w.1, w.2] i) / (2 * Real.sqrt (ν * (τ - r)))) * heatK 1 w) hK
      (fun w => |heatKd i 1 w| / Real.sqrt (ν * (τ - τ1))) hkbi hKb) ?_
    intro z hz
    exact heatSGd_pos_eq (hpos τ1 hτ1 z.1 hz.1) i (g z.1) z.2

end UnforcedLeray.Short.IIb.CylPDE
