import UnforcedLeray.Units.B0104.Dyson
import Mathlib.MeasureTheory.Integral.Prod
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org_1_b_org

/-!
# Dyson iterates are defined under joint measurability (SP 2920-2982)

Helper lemmas for `dysonDefined_of_measurable`: the Dyson iterates are a.e. strongly measurable
in the time variable, and the iterated integrands are interval integrable.
-/

set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped Nat
open TopologicalSpace (SeparableSpace)

namespace UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [SeparableSpace H]

theorem dj_sm_pair (F : ℝ → ℝ → H →L[ℂ] H)
    (hFj : UnforcedLeray.Short.IIIa.DysonJointMeas.FJointMeas F)
    {z : ℝ → H} (hz : StronglyMeasurable z) :
    StronglyMeasurable (fun p : ℝ × ℝ => F p.1 p.2 (z p.2)) := by
  borelize H
  have hG : StronglyMeasurable
      (Function.uncurry (fun (y : H) (p : ℝ × ℝ) => F p.1 p.2 y)) :=
    stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
      (fun p => (F p.1 p.2).continuous) hFj
  have hpair : Measurable (fun p : ℝ × ℝ => (z p.2, p)) :=
    (hz.measurable.comp measurable_snd).prodMk measurable_id
  exact hG.comp_measurable hpair

theorem dj_sm_slice (F : ℝ → ℝ → H →L[ℂ] H)
    (hFj : UnforcedLeray.Short.IIIa.DysonJointMeas.FJointMeas F)
    {z : ℝ → H} (hz : StronglyMeasurable z) (t : ℝ) :
    StronglyMeasurable (fun r : ℝ => F t r (z r)) :=
  (dj_sm_pair F hFj hz).comp_measurable
    (measurable_const.prodMk measurable_id : Measurable fun r : ℝ => (t, r))

theorem dj_sm_param (F : ℝ → ℝ → H →L[ℂ] H)
    (hFj : UnforcedLeray.Short.IIIa.DysonJointMeas.FJointMeas F)
    {z : ℝ → H} (hz : StronglyMeasurable z) (s : ℝ) :
    StronglyMeasurable (fun r : ℝ => ∫ u in s..r, F r u (z u)) := by
  have hΦ := dj_sm_pair F hFj hz
  have hS1 : MeasurableSet {p : ℝ × ℝ | s < p.2 ∧ p.2 ≤ p.1} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst)
  have hS2 : MeasurableSet {p : ℝ × ℝ | p.1 < p.2 ∧ p.2 ≤ s} :=
    (measurableSet_lt measurable_fst measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)
  have m1 := MeasureTheory.StronglyMeasurable.integral_prod_right' (ν := volume)
    (hΦ.indicator hS1)
  have m2 := MeasureTheory.StronglyMeasurable.integral_prod_right' (ν := volume)
    (hΦ.indicator hS2)
  have e1 : ∀ r : ℝ, (∫ u, {p : ℝ × ℝ | s < p.2 ∧ p.2 ≤ p.1}.indicator
      (fun p : ℝ × ℝ => F p.1 p.2 (z p.2)) (r, u)) = ∫ u in Ioc s r, F r u (z u) := by
    intro r
    rw [← integral_indicator measurableSet_Ioc]
    congr 1
  have e2 : ∀ r : ℝ, (∫ u, {p : ℝ × ℝ | p.1 < p.2 ∧ p.2 ≤ s}.indicator
      (fun p : ℝ × ℝ => F p.1 p.2 (z p.2)) (r, u)) = ∫ u in Ioc r s, F r u (z u) := by
    intro r
    rw [← integral_indicator measurableSet_Ioc]
    congr 1
  have key : ∀ r : ℝ, (∫ u in s..r, F r u (z u)) =
      (∫ u, {p : ℝ × ℝ | s < p.2 ∧ p.2 ≤ p.1}.indicator
        (fun p : ℝ × ℝ => F p.1 p.2 (z p.2)) (r, u)) -
      (∫ u, {p : ℝ × ℝ | p.1 < p.2 ∧ p.2 ≤ s}.indicator
        (fun p : ℝ × ℝ => F p.1 p.2 (z p.2)) (r, u)) := by
    intro r
    rw [e1 r, e2 r]
    by_cases h : s ≤ r
    · have hz0 : ∫ u in Ioc r s, F r u (z u) = 0 := by
        rw [Set.Ioc_eq_empty (not_lt.2 h)]
        simp
      rw [intervalIntegral.integral_of_le h, hz0, sub_zero]
    · push Not at h
      have hz0 : ∫ u in Ioc s r, F r u (z u) = 0 := by
        rw [Set.Ioc_eq_empty (not_lt.2 h.le)]
        simp
      rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le h.le, hz0, zero_sub]
  have hfun : (fun r : ℝ => ∫ u in s..r, F r u (z u)) = fun r : ℝ =>
      (∫ u, {p : ℝ × ℝ | s < p.2 ∧ p.2 ≤ p.1}.indicator
        (fun p : ℝ × ℝ => F p.1 p.2 (z p.2)) (r, u)) -
      (∫ u, {p : ℝ × ℝ | p.1 < p.2 ∧ p.2 ≤ s}.indicator
        (fun p : ℝ × ℝ => F p.1 p.2 (z p.2)) (r, u)) := funext key
  rw [hfun]
  exact m1.sub m2

theorem dj_norm_bound (F : ℝ → ℝ → H →L[ℂ] H) (A : ℝ → H →L[ℂ] H) (M K : ℝ)
    (hM : 0 ≤ M) (hA : ∀ r, ‖A r‖ ≤ K) (t r : ℝ) (hFr : ‖F t r‖ ≤ M) (v : H) :
    ‖F t r (A r v)‖ ≤ M * (K * ‖v‖) := by
  refine ((F t r).le_opNorm _).trans ?_
  exact mul_le_mul hFr (((A r).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (hA r) (norm_nonneg _))) (norm_nonneg _) hM

theorem dj_ae_A (A : ℝ → H →L[ℂ] H)
    (hAm : ∀ x : H, AEStronglyMeasurable (fun r => A r x) volume)
    {z : ℝ → H} (hz : StronglyMeasurable z) :
    ∃ a : ℝ → H, StronglyMeasurable a ∧ (fun r => A r (z r)) =ᵐ[volume] a := by
  have hsimple : ∀ f : SimpleFunc ℝ H, AEStronglyMeasurable (fun r => A r (f r)) volume := by
    intro f
    refine SimpleFunc.induction (motive := fun f : SimpleFunc ℝ H =>
      AEStronglyMeasurable (fun r => A r (f r)) volume) ?_ ?_ f
    · intro c s hs
      refine AEStronglyMeasurable.congr ((hAm c).indicator hs)
        (Filter.Eventually.of_forall fun r => ?_)
      by_cases hr : r ∈ s <;> simp [hr]
    · intro f g _ hf hg
      refine AEStronglyMeasurable.congr (hf.add hg)
        (Filter.Eventually.of_forall fun r => ?_)
      simp [map_add]
  have hw : AEStronglyMeasurable (fun r => A r (z r)) volume := by
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n r => A r ((hz.approx n) r)) (fun n => hsimple (hz.approx n))
      (Filter.Eventually.of_forall fun r => ?_)
    exact ((A r).continuous.tendsto (z r)).comp (hz.tendsto_approx r)
  exact ⟨hw.mk _, hw.stronglyMeasurable_mk, hw.ae_eq_mk⟩

theorem dj_interval (F : ℝ → ℝ → H →L[ℂ] H) (A : ℝ → H →L[ℂ] H) (M K : ℝ)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hA : ∀ r, ‖A r‖ ≤ K)
    (hFj : UnforcedLeray.Short.IIIa.DysonJointMeas.FJointMeas F)
    (hAm : ∀ x : H, AEStronglyMeasurable (fun r => A r x) volume)
    (s t : ℝ) (hst : s ≤ t) (hFt : ∀ r, s ≤ r → r ≤ t → ‖F t r‖ ≤ M)
    (V : ℝ → H) (C0 : ℝ) (hC : ∀ r, s ≤ r → r ≤ t → ‖V r‖ ≤ C0)
    (g : ℝ → H) (hg : StronglyMeasurable g) (hV : ∀ᵐ r ∂(volume : Measure ℝ), V r = g r) :
    IntervalIntegrable (fun r => F t r (A r (V r))) volume s t := by
  obtain ⟨a, ha, haeq⟩ := dj_ae_A A hAm hg
  have hae : (fun r => F t r (a r)) =ᵐ[volume.restrict (Ioc s t)]
      (fun r => F t r (A r (V r))) := by
    refine ae_restrict_of_ae ?_
    filter_upwards [hV, haeq] with r hr1 hr2
    have hr2' : A r (g r) = a r := hr2
    rw [hr1, hr2']
  have hmeas : AEStronglyMeasurable (fun r => F t r (A r (V r)))
      (volume.restrict (Ioc s t)) :=
    (dj_sm_slice F hFj ha t).aestronglyMeasurable.congr hae
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hst]
  have hconst : IntegrableOn (fun _ : ℝ => M * (K * C0)) (Ioc s t) volume :=
    integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  refine Integrable.mono' hconst hmeas ?_
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun r hr => ?_)
  have hr1 : s ≤ r := hr.1.le
  calc ‖F t r (A r (V r))‖ ≤ M * (K * ‖V r‖) :=
        dj_norm_bound F A M K hM hA t r (hFt r hr1 hr.2) (V r)
    _ ≤ M * (K * C0) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hC r hr1 hr.2) hK) hM

theorem dysonDefined_of_measurable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [SeparableSpace H] (B M K : ℝ) (F : ℝ → ℝ → H →L[ℂ] H)
    (A : ℝ → H →L[ℂ] H)
    (hF : ∀ s t : ℝ, s ≤ t → t ≤ s + B → ‖F t s‖ ≤ M)
    (hA : ∀ r : ℝ, ‖A r‖ ≤ K)
    (hFm : ∀ (t : ℝ) (x : H), AEStronglyMeasurable (fun σ => F t σ x) volume)
    (hFj : UnforcedLeray.Short.IIIa.DysonJointMeas.FJointMeas F)
    (hAm : ∀ x : H, AEStronglyMeasurable (fun r => A r x) volume) :
    UnforcedLeray.B0104.DysonDefined (ι := Unit) B (fun _ => F) (fun _ => A) := by
  unfold UnforcedLeray.B0104.DysonDefined
  have key : ∀ k : ℕ, ∀ s : ℝ, ∀ x : H, ∃ g : ℝ → H, StronglyMeasurable g ∧
      ∀ᵐ r ∂(volume : Measure ℝ),
        UnforcedLeray.B0104.dysonTerm (fun _ : Unit => F) (fun _ : Unit => A) k () r s x = g r := by
    intro k
    induction k with
    | zero =>
      intro s x
      have h1 : StronglyMeasurable (fun p : ℝ × ℝ => F p.1 p.2 x) := hFj x
      exact ⟨fun r => F r s x,
        h1.comp_measurable (measurable_id.prodMk measurable_const : Measurable fun r : ℝ => (r, s)),
        Filter.Eventually.of_forall fun r => rfl⟩
    | succ k ih =>
      intro s x
      obtain ⟨g, hg, hgeq⟩ := ih s x
      obtain ⟨a, ha, haeq⟩ := dj_ae_A A hAm hg
      refine ⟨fun r => ∫ u in s..r, F r u (a u), dj_sm_param F hFj ha s,
        Filter.Eventually.of_forall fun r => ?_⟩
      show (∫ u in s..r, F r u (A u (UnforcedLeray.B0104.dysonTerm
          (fun _ : Unit => F) (fun _ : Unit => A) k () u s x))) = ∫ u in s..r, F r u (a u)
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hgeq, haeq] with u hu1 hu2
      intro _
      have hu2' : A u (g u) = a u := hu2
      rw [hu1, hu2']
  intro k p s t hst htB x
  cases p
  have hBnn : 0 ≤ B := by linarith
  have hM : 0 ≤ M := (norm_nonneg _).trans (hF s s le_rfl (by linarith))
  have hK : 0 ≤ K := (norm_nonneg _).trans (hA 0)
  have hMK : 0 ≤ M * K := mul_nonneg hM hK
  have hC : ∀ r, s ≤ r → r ≤ t →
      ‖UnforcedLeray.B0104.dysonTerm (fun _ : Unit => F) (fun _ : Unit => A) k () r s x‖
        ≤ M * ((M * K * (t - s)) ^ k / k !) * ‖x‖ := by
    intro r h1 h2
    have hV := UnforcedLeray.B0104.norm_dysonTerm_le (B := B) (M := M) (K := K)
      (F := fun _ : Unit => F) (A := fun _ : Unit => A)
      (fun _ t' s' h3 h4 => hF s' t' h3 h4) (fun _ r' => hA r') k () r s h1 (by linarith) x
    refine hV.trans ?_
    have hx : 0 ≤ ‖x‖ := norm_nonneg _
    have h0 : 0 ≤ M * K * (r - s) := mul_nonneg hMK (by linarith)
    have h1' : M * K * (r - s) ≤ M * K * (t - s) := mul_le_mul_of_nonneg_left (by linarith) hMK
    have hp := pow_le_pow_left₀ h0 h1' k
    have hq : (M * K * (r - s)) ^ k / (k ! : ℝ) ≤ (M * K * (t - s)) ^ k / (k ! : ℝ) :=
      div_le_div_of_nonneg_right hp (by positivity)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq hM) hx
  obtain ⟨g, hg, hgeq⟩ := key k s x
  exact dj_interval F A M K hM hK hA hFj hAm s t hst
    (fun r _ h2 => hF r t h2 (by linarith))
    (fun r => UnforcedLeray.B0104.dysonTerm (fun _ : Unit => F) (fun _ : Unit => A) k () r s x)
    _ hC g hg hgeq
