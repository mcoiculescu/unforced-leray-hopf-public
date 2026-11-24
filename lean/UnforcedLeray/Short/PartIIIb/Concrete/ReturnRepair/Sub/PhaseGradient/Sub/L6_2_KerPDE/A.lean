import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L2

/-!
# Joint `C³` regularity of `K_t(x)` on `t > 0` (source 3598-3610)

Scaling `a = t b` gives `∫_t^∞ G_a(x) da = t^{-1/2} Ψ₁(|x|²/(4t))` with `Ψ₁ = L2hkPsi 1 0`
smooth (`L2_psi_contDiff`); hence `(t,x) ↦ heatTail t x` is jointly `C⁵` on `t > 0`, and the
second partials (slice derivatives) are jointly `C³`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Joint form of `heatTail`. -/
def kjTail (p : ℝ × Space) : ℝ := p.1 ^ (-1 / 2 : ℝ) * L2hkPsi 1 0 (‖p.2‖ ^ 2 / (4 * p.1))

lemma kj_heatTail_eq (t : ℝ) (ht : 0 < t) (x : Space) :
    IIIa.heatTail t x = kjTail (t, x) := by
  unfold IIIa.heatTail kjTail L2hkPsi
  have h := integral_comp_mul_left_Ioi
    (fun a : ℝ => IIIa.heatG a x) 1 ht
  rw [mul_one] at h
  have h2 : ∫ a in Ioi t, IIIa.heatG a x = t * ∫ b in Ioi (1 : ℝ), IIIa.heatG (t * b) x := by
    rw [h, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul]
  rw [h2]
  have h3 : ∀ b : ℝ, b ∈ Ioi (1 : ℝ) → IIIa.heatG (t * b) x =
      t ^ (-3 / 2 : ℝ) * L2hkG 0 b (‖x‖ ^ 2 / (4 * t)) := by
    intro b hb
    have hb0 : 0 < b := lt_trans one_pos hb
    unfold IIIa.heatG L2hkG
    rw [pow_zero, one_mul, show 4 * Real.pi * (t * b) = t * (4 * Real.pi * b) by ring,
      Real.mul_rpow ht.le (by positivity)]
    have e : -‖x‖ ^ 2 / (4 * (t * b)) = -(‖x‖ ^ 2 / (4 * t)) / b := by
      field_simp
    rw [e]; ring
  rw [setIntegral_congr_fun measurableSet_Ioi h3, integral_const_mul]
  have : t * t ^ (-3 / 2 : ℝ) = t ^ (-1 / 2 : ℝ) := by
    rw [show (-1 / 2 : ℝ) = 1 + (-3 / 2) by norm_num, Real.rpow_add ht, Real.rpow_one]
  rw [← mul_assoc, this]

lemma kjTail_contDiffOn : ContDiffOn ℝ 5 kjTail {p : ℝ × Space | 0 < p.1} := by
  intro p hp
  have hp1 : 0 < p.1 := hp
  apply ContDiffAt.contDiffWithinAt
  have h1 : ContDiffAt ℝ 5 (fun q : ℝ × Space => q.1 ^ (-1 / 2 : ℝ)) p :=
    ContDiffAt.rpow_const_of_ne contDiffAt_fst hp1.ne'
  have h2 : ContDiffAt ℝ 5 (fun q : ℝ × Space => ‖q.2‖ ^ 2 / (4 * q.1)) p := by
    refine ContDiffAt.div ?_ ?_ (by positivity)
    · exact (contDiff_norm_sq ℝ).comp contDiff_snd |>.contDiffAt
    · exact (contDiff_const.mul contDiff_fst).contDiffAt
  exact h1.mul ((L2_psi_contDiff 1 one_pos).contDiffAt.comp p h2)

lemma kj_slice_fderiv {F : ℝ × Space → ℝ} {U : Set (ℝ × Space)} (hU : IsOpen U)
    (hF : ∀ p ∈ U, DifferentiableAt ℝ F p) (t : ℝ) (v : Space)
    (hsl : ∀ y : Space, (t, y) ∈ U) (x : Space) :
    fderiv ℝ (fun y => F (t, y)) x v = fderiv ℝ F (t, x) (0, v) := by
  have hi : HasFDerivAt (fun y : Space => ((t, y) : ℝ × Space))
      ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space)) x :=
    (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
  have := ((hF (t, x) (hsl x)).hasFDerivAt.comp x hi).fderiv
  change fderiv ℝ (F ∘ Prod.mk t) x v = _
  rw [this]; rfl

lemma kj_deriv_contDiffOn {F : ℝ × Space → ℝ} {n : ℕ} (hF : ContDiffOn ℝ (n + 1) F {p : ℝ × Space | 0 < p.1})
    (v : Space) :
    ContDiffOn ℝ n (fun p => fderiv ℝ F p (0, v)) {p : ℝ × Space | 0 < p.1} := by
  have hU : IsOpen {p : ℝ × Space | 0 < p.1} := isOpen_lt continuous_const continuous_fst
  have := hF.fderiv_of_isOpen (m := n) hU (by simp)
  exact this.clm_apply contDiffOn_const

theorem heatLerayK_jointC3 : HeatLerayKJointC3 := by
  intro i j
  have hU : IsOpen {p : ℝ × Space | 0 < p.1} := isOpen_lt continuous_const continuous_fst
  have hT := kjTail_contDiffOn
  have hdiff : ∀ p ∈ {p : ℝ × Space | 0 < p.1}, DifferentiableAt ℝ kjTail p := fun p hp =>
    (hT.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hp)
  set ej : Space := UnforcedLeray.coordinateVector j
  set ei : Space := UnforcedLeray.coordinateVector i
  have hG1 : ContDiffOn ℝ 4 (fun p => fderiv ℝ kjTail p (0, ej)) {p : ℝ × Space | 0 < p.1} :=
    kj_deriv_contDiffOn (n := 4) hT ej
  have hG1d : ∀ p ∈ {p : ℝ × Space | 0 < p.1},
      DifferentiableAt ℝ (fun p => fderiv ℝ kjTail p (0, ej)) p := fun p hp =>
    (hG1.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hp)
  have hG2 : ContDiffOn ℝ 3 (fun p => fderiv ℝ (fun q => fderiv ℝ kjTail q (0, ej)) p (0, ei))
      {p : ℝ × Space | 0 < p.1} := kj_deriv_contDiffOn (n := 3) hG1 ei
  have hG : ContDiffOn ℝ 3 (fun p : ℝ × Space => IIIa.heatG p.1 p.2)
      {p : ℝ × Space | 0 < p.1} := by
    intro p hp
    apply ContDiffAt.contDiffWithinAt
    have hp1 : 0 < p.1 := hp
    unfold IIIa.heatG
    refine ContDiffAt.mul ?_ ?_
    · exact ContDiffAt.rpow_const_of_ne (by fun_prop) (by positivity)
    · refine Real.contDiff_exp.contDiffAt.comp p ?_
      refine ContDiffAt.div ?_ ?_ (by positivity)
      · exact (((contDiff_norm_sq ℝ).comp contDiff_snd).neg).contDiffAt
      · exact (contDiff_const.mul contDiff_fst).contDiffAt
  have hpart : ∀ t : ℝ, 0 < t → ∀ x : Space, IIIa.part2 (IIIa.heatTail t) i j x =
      fderiv ℝ (fun q => fderiv ℝ kjTail q (0, ej)) (t, x) (0, ei) := by
    intro t ht x
    have hsl : ∀ y : Space, (t, y) ∈ {p : ℝ × Space | 0 < p.1} := fun y => ht
    have hfun : IIIa.heatTail t = fun y => kjTail (t, y) := funext fun y => kj_heatTail_eq t ht y
    unfold IIIa.part2
    rw [hfun]
    have e1 : (fun y => fderiv ℝ (fun y' => kjTail (t, y')) y ej) =
        fun y => fderiv ℝ kjTail (t, y) (0, ej) :=
      funext fun y => kj_slice_fderiv hU hdiff t ej hsl y
    rw [e1]
    exact kj_slice_fderiv hU hG1d t ei hsl x
  have hsum : ContDiffOn ℝ 3 (fun p : ℝ × Space =>
      (if i = j then IIIa.heatG p.1 p.2 else 0) +
      fderiv ℝ (fun q => fderiv ℝ kjTail q (0, ej)) p (0, ei)) {p : ℝ × Space | 0 < p.1} := by
    refine ContDiffOn.add ?_ hG2
    by_cases h : i = j
    · simpa [h] using hG
    · simpa [h] using contDiffOn_const
  refine hsum.congr ?_
  intro p hp
  have hp1 : 0 < p.1 := hp
  unfold IIIa.heatLerayK
  rw [hpart p.1 hp1 p.2]
