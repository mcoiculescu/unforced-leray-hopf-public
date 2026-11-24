import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.OutPrimRep

/-!
# Measurability of the phase-lag kernels in the source variable

Source `the November 2 reference manuscript` 3611-3621, 4171, 4180-4186.
`e ↦ xKer ν μ (τ - e.1) (y - λ e.2) (T e)` and the outward primitive `sKer` are measurable, given
that a vanishing translated argument forces a vanishing tensor (so the junk value of the gradient
at the origin never matters).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped Classical

namespace UnforcedLeray.Short.PartIIIb.Concrete

lemma yr_xKer_eq_C (ν μ h : ℝ) (W : Space) (M : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3)
    (hz : W = 0 → M = 0) :
    xKer ν μ h W M i = -(pdLam h ^ (2 * μ + 3) - pdLam h ^ (2 * μ + 5)) *
      ∑ j : Fin 3, ∑ k : Fin 3, T8_1.Gm k i j (ν * (1 - pdLam h ^ 2), W) * M j k := by
  rw [xKer_apply]
  congr 1
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  by_cases hW : W = 0
  · rw [hz hW]; simp
  · rw [T8_1.Gm_eq k i j _ hW]

lemma yr_xKer_meas {β : Type*} [MeasurableSpace β] (ν μ : ℝ) (S : Set β) (hS : MeasurableSet S)
    (h : β → ℝ) (hh : Measurable h) (W : β → Space) (hW : Measurable W)
    (M : β → Matrix (Fin 3) (Fin 3) ℝ) (hM : ∀ i j, Measurable fun b => M b i j)
    (hz : ∀ b ∈ S, W b = 0 → M b = 0) :
    Measurable fun b => if b ∈ S then xKer ν μ (h b) (W b) (M b) else 0 := by
  classical
  have hlam : Measurable fun b => pdLam (h b) := by unfold pdLam; fun_prop
  have hτ1 : Measurable fun b => ν * (1 - pdLam (h b) ^ 2) :=
    measurable_const.mul (measurable_const.sub (hlam.pow_const 2))
  have hcomp : ∀ i : Fin 3, Measurable fun b => if b ∈ S then
      -(pdLam (h b) ^ (2 * μ + 3) - pdLam (h b) ^ (2 * μ + 5)) *
        ∑ j : Fin 3, ∑ k : Fin 3, T8_1.Gm k i j (ν * (1 - pdLam (h b) ^ 2), W b) * M b j k
      else 0 := by
    intro i
    refine Measurable.ite hS ?_ measurable_const
    refine Measurable.mul (Measurable.neg ((hlam.pow_const _).sub (hlam.pow_const _))) ?_
    refine Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun k _ => ?_
    exact ((T8_1.measurable_Gm k i j).comp (hτ1.prodMk hW)).mul (hM j k)
  have : (fun b => if b ∈ S then xKer ν μ (h b) (W b) (M b) else 0) = fun b =>
      (WithLp.toLp 2 (fun i : Fin 3 => if b ∈ S then
      -(pdLam (h b) ^ (2 * μ + 3) - pdLam (h b) ^ (2 * μ + 5)) *
        ∑ j : Fin 3, ∑ k : Fin 3, T8_1.Gm k i j (ν * (1 - pdLam (h b) ^ 2), W b) * M b j k
      else 0) : Space) := by
    funext b
    by_cases hb : b ∈ S
    · ext i
      simp only [if_pos hb]
      exact yr_xKer_eq_C ν μ (h b) (W b) (M b) i (hz b hb)
    · ext i
      simp [hb]
  rw [this]
  exact (WithLp.measurable_toLp 2 (Fin 3 → ℝ)).comp (measurable_pi_lambda _ hcomp)

lemma yr_varrho_lam_le {l : ℝ} (hl0 : 0 < l) (hl1 : l ≤ 1) (z : Space) : ϱ (l • z) ≤ ϱ z := by
  rw [ϱ_smul, abs_of_pos hl0]
  nlinarith [ϱ_nonneg z]

lemma yr_pdLam_le_one {h : ℝ} (hh : 0 < h) : pdLam h ≤ 1 := by
  unfold pdLam
  rw [Real.exp_le_one_iff]; linarith

/-- If `ϱ z < ϱ x` whenever the tensor is nonzero, a vanishing translated argument forces a
vanishing tensor. -/
lemma yr_zero_of_eq {x z : Space} {h : ℝ} (hh : 0 < h) (hx : x = pdLam h • z)
    (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : M ≠ 0 → ϱ z < ϱ x) : M = 0 := by
  by_contra hne
  have := hM hne
  have h2 := yr_varrho_lam_le (Real.exp_pos (-(h / 2))) (yr_pdLam_le_one hh) z
  rw [hx] at this
  exact absurd this (not_lt.2 h2)

lemma yr_meas_oldPhys_entry (R c : ℝ) (g : Chart → Ten3) (hg : Measurable g) (i j : Fin 3) :
    Measurable fun e : ℝ × Space => oldPhys R c g e.1 e.2 i j :=
  T8_1.measurable_oldPhys_entry R c g hg i j

lemma yr_sKer_meas (ν μ R c : ℝ) (g : Chart → Ten3) (hg : Measurable g) (τ r y3 : ℝ)
    (hr : ∀ σ z, oldPhys R c g σ z ≠ 0 → ϱ z < r) :
    Measurable fun e : ℝ × Space =>
      if e.1 < τ then sKer ν μ (τ - e.1) r y3 e.2 (oldPhys R c g e.1 e.2) else 0 := by
  classical
  obtain ⟨S, hS⟩ : ∃ S : Set ((ℝ × Space) × ℝ), S = {q | q.1.1 < τ ∧ r < q.2} := ⟨_, rfl⟩
  have hmem : ∀ q : (ℝ × Space) × ℝ, q ∈ S ↔ q.1.1 < τ ∧ r < q.2 := by
    intro q; rw [hS]; rfl
  have hSm : MeasurableSet S := by
    rw [hS]
    exact (measurableSet_lt (measurable_fst.comp (measurable_fst)) measurable_const).inter
      (measurableSet_lt measurable_const measurable_snd)
  have hP : Measurable fun q : (ℝ × Space) × ℝ => (!₂[q.2, 0, y3] : Space) :=
    (pdOR_P_meas y3).comp measurable_snd
  have hlam : Measurable fun q : (ℝ × Space) × ℝ => pdLam (τ - q.1.1) := by
    unfold pdLam; fun_prop
  have hW : Measurable fun q : (ℝ × Space) × ℝ =>
      (!₂[q.2, 0, y3] : Space) - pdLam (τ - q.1.1) • q.1.2 :=
    hP.sub (hlam.smul (measurable_snd.comp measurable_fst))
  have hM : ∀ i j : Fin 3, Measurable fun q : (ℝ × Space) × ℝ => oldPhys R c g q.1.1 q.1.2 i j :=
    fun i j => (yr_meas_oldPhys_entry R c g hg i j).comp measurable_fst
  have hz : ∀ q ∈ S, (!₂[q.2, 0, y3] : Space) - pdLam (τ - q.1.1) • q.1.2 = 0 →
      oldPhys R c g q.1.1 q.1.2 = 0 := by
    intro q hq hq0
    rw [hmem] at hq
    have hx : (!₂[q.2, 0, y3] : Space) = pdLam (τ - q.1.1) • q.1.2 := sub_eq_zero.mp hq0
    refine yr_zero_of_eq (sub_pos.2 hq.1) hx _ (fun hne => ?_)
    have h1 := hr _ _ hne
    have h0 : 0 ≤ q.2 := by linarith [ϱ_nonneg q.1.2, hq.2]
    rw [pdOR_varrho h0]
    exact lt_trans h1 hq.2
  have hxm := yr_xKer_meas ν μ S hSm (fun q : (ℝ × Space) × ℝ => τ - q.1.1)
    (measurable_const.sub (measurable_fst.comp measurable_fst)) _ hW _ hM hz
  have h2 : Measurable fun q : (ℝ × Space) × ℝ => if q ∈ S then
      q.2 * (xKer ν μ (τ - q.1.1) ((!₂[q.2, 0, y3] : Space) - pdLam (τ - q.1.1) • q.1.2)
        (oldPhys R c g q.1.1 q.1.2)) 2 else 0 := by
    have : (fun q : (ℝ × Space) × ℝ => if q ∈ S then
      q.2 * (xKer ν μ (τ - q.1.1) ((!₂[q.2, 0, y3] : Space) - pdLam (τ - q.1.1) • q.1.2)
        (oldPhys R c g q.1.1 q.1.2)) 2 else 0) = fun q => q.2 *
        ((fun b => if b ∈ S then xKer ν μ (τ - b.1.1)
          ((!₂[b.2, 0, y3] : Space) - pdLam (τ - b.1.1) • b.1.2) (oldPhys R c g b.1.1 b.1.2)
          else 0) q) 2 := by
      funext q; by_cases hq : q ∈ S <;> simp [hq]
    rw [this]
    exact measurable_snd.mul ((EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).continuous.measurable.comp hxm)
  have hint := (h2.stronglyMeasurable).integral_prod_right' (ν := volume.restrict (Ioi r))
  have : (fun e : ℝ × Space => if e.1 < τ then sKer ν μ (τ - e.1) r y3 e.2 (oldPhys R c g e.1 e.2)
      else 0) = fun e => -∫ ρ in Ioi r, (fun q : (ℝ × Space) × ℝ => if q ∈ S then
      q.2 * (xKer ν μ (τ - q.1.1) ((!₂[q.2, 0, y3] : Space) - pdLam (τ - q.1.1) • q.1.2)
        (oldPhys R c g q.1.1 q.1.2)) 2 else 0) (e, ρ) := by
    funext e
    by_cases he : e.1 < τ
    · rw [if_pos he, sKer]
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioi fun ρ hρ => ?_
      have : ((e, ρ) : (ℝ × Space) × ℝ) ∈ S := (hmem _).2 ⟨he, hρ⟩
      simp [this]
    · rw [if_neg he]
      have : ∀ ρ : ℝ, ((e, ρ) : (ℝ × Space) × ℝ) ∉ S := fun ρ h => he ((hmem _).1 h).1
      simp [this]
  rw [this]
  exact hint.measurable.neg

end UnforcedLeray.Short.PartIIIb.Concrete

end
