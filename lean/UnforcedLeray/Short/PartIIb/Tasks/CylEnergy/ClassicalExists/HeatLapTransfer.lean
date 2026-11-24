import UnforcedLeray.Short.PartIIb.Sub.T22_1_8
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.HeatCommute
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.HeatTimeDeriv

/-!


Proves `HeatLapTransfer` (`Sub/T22_1_8.lean`): `K_a * Δg = (ΔK_a) * g` for `a > 0`.
Source: `the November 2 reference manuscript`, lines 2074-2093 and 2103-2105.

Route: two integrations by parts per coordinate, `∫ K · ∂_j ψ(x - ·) = ∫ ∂_j K · ψ(x - ·)`
(Mathlib `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`), applied once with `ψ = ∂_j g` and
once with `ψ = g`, after which the integrand is `∂_j∂_j K · g(x - ·)`; then change of variables.
Gaussian integrability uses `|z|² e^{-|z|²/(4a)} ≤ 8a e^{-|z|²/(8a)}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb.CylPDE

namespace HLT

/-- Chain rule for `z ↦ ψ (x - z)`. -/
lemma chain_sub (ψ : Pl → ℝ) (hψ : Differentiable ℝ ψ) (x z v : Pl) :
    fderiv ℝ (fun w : Pl => ψ (x - w)) z v = -(fderiv ℝ ψ (x - z) v) := by
  have h1 : HasFDerivAt (fun w : Pl => x - w) (-ContinuousLinearMap.id ℝ Pl) z :=
    (hasFDerivAt_id z).const_sub x
  have h2 : HasFDerivAt (fun w : Pl => ψ (x - w))
      ((fderiv ℝ ψ (x - z)).comp (-ContinuousLinearMap.id ℝ Pl)) z :=
    (hψ (x - z)).hasFDerivAt.comp z h1
  rw [h2.fderiv]
  simp

/-- Integration by parts in the convolution variable:
`∫ K(z) ∂_v ψ(x - z) dz = ∫ ∂_v K(z) ψ(x - z) dz`. -/
lemma ibp_conv {K ψ : Pl → ℝ} (hK : Differentiable ℝ K) (hψ : Differentiable ℝ ψ) (x v : Pl)
    (hi1 : Integrable (fun z : Pl => fderiv ℝ K z v * ψ (x - z)))
    (hi2 : Integrable (fun z : Pl => K z * fderiv ℝ ψ (x - z) v))
    (hi3 : Integrable (fun z : Pl => K z * ψ (x - z))) :
    ∫ z : Pl, K z * fderiv ℝ ψ (x - z) v = ∫ z : Pl, fderiv ℝ K z v * ψ (x - z) := by
  have hdiff : Differentiable ℝ (fun w : Pl => ψ (x - w)) :=
    hψ.comp ((differentiable_const x).sub differentiable_id)
  have hfd : ∀ z : Pl, fderiv ℝ (fun w : Pl => ψ (x - w)) z v = -(fderiv ℝ ψ (x - z) v) :=
    fun z => chain_sub ψ hψ x z v
  have e1 : (fun z : Pl => K z * fderiv ℝ (fun w : Pl => ψ (x - w)) z v) =
      fun z : Pl => -(K z * fderiv ℝ ψ (x - z) v) := by
    funext z
    rw [hfd z]
    ring
  have hfg' : Integrable (fun z : Pl => K z * fderiv ℝ (fun w : Pl => ψ (x - w)) z v) := by
    rw [e1]
    exact hi2.neg
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := K)
    (g := fun w : Pl => ψ (x - w)) (v := v) hi1 hfg' hi3 (fun z _ => hK z) (fun z _ => hdiff z)
  rw [e1, integral_neg] at key
  beta_reduce at key
  linarith

/-- `s e^{-s} ≤ 1` for `s ≥ 0`. -/
lemma exp_mul_le (s : ℝ) : s * Real.exp (-s) ≤ 1 := by
  have h1 := Real.add_one_le_exp s
  have h2 : Real.exp (-s) * Real.exp s = 1 := by
    rw [← Real.exp_add]; simp
  have h3 := Real.exp_pos (-s)
  nlinarith [mul_le_mul_of_nonneg_left h1 h3.le]

/-- Pointwise Gaussian majorant: `|z|² K_a(z) ≤ (2/π) e^{-|z|²/(8a)}`. -/
lemma Q_heatK_le {a : ℝ} (ha : 0 < a) (z : Pl) :
    (z.1 ^ 2 + z.2 ^ 2) * heatK a z ≤ (2 / Real.pi) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (8 * a)) := by
  have hQ : 0 ≤ z.1 ^ 2 + z.2 ^ 2 := by positivity
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = (z.1 ^ 2 + z.2 ^ 2) / (8 * a) := ⟨_, rfl⟩
  have hs : 0 ≤ s := by
    rw [hs_def]; exact div_nonneg hQ (by positivity)
  have hQs : z.1 ^ 2 + z.2 ^ 2 = 8 * a * s := by
    rw [hs_def]; field_simp
  have hexp4 : -(z.1 ^ 2 + z.2 ^ 2) / (4 * a) = -s + -s := by
    rw [hs_def]; field_simp; ring
  have hK : heatK a z = 1 / (4 * Real.pi * a) * (Real.exp (-s) * Real.exp (-s)) := by
    unfold heatK
    rw [hexp4, Real.exp_add]
  have hgoal : Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (8 * a)) = Real.exp (-s) := by
    rw [hs_def, neg_div]
  rw [hgoal, hK]
  have hE := exp_mul_le s
  have hE0 := Real.exp_pos (-s)
  have key : (z.1 ^ 2 + z.2 ^ 2) * (1 / (4 * Real.pi * a) * (Real.exp (-s) * Real.exp (-s))) =
      (2 / Real.pi) * ((s * Real.exp (-s)) * Real.exp (-s)) := by
    rw [hQs]
    have ha0 : a ≠ 0 := ha.ne'
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  rw [key]
  have h2 : (s * Real.exp (-s)) * Real.exp (-s) ≤ Real.exp (-s) := by
    nlinarith [mul_le_mul_of_nonneg_right hE hE0.le]
  exact mul_le_mul_of_nonneg_left h2 (by positivity)

/-- Gaussian integrability: `e^{-|z|²/c}` is integrable for `c > 0`. -/
lemma integrable_gauss_exp {c : ℝ} (hc : 0 < c) :
    Integrable (fun z : Pl => Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / c)) := by
  have h := ((heatKernelMoments (c / 4) (by linarith)).2.1).const_mul (Real.pi * c)
  refine h.congr (ae_of_all _ fun z => ?_)
  show Real.pi * c * heatK (c / 4) z = Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / c)
  unfold heatK
  have hc4 : (4:ℝ) * (c / 4) = c := by ring
  have hpc : Real.pi * c ≠ 0 := by positivity
  have hm : 4 * Real.pi * (c / 4) = Real.pi * c := by ring
  rw [hc4, hm, ← mul_assoc, mul_one_div_cancel hpc, one_mul]

/-- `|z|² K_a` is integrable. -/
lemma integrable_Q_heatK {a : ℝ} (ha : 0 < a) :
    Integrable (fun z : Pl => (z.1 ^ 2 + z.2 ^ 2) * heatK a z) := by
  have hI := (integrable_gauss_exp (c := 8 * a) (by linarith)).const_mul (2 / Real.pi)
  refine Integrable.mono' hI ?_ (ae_of_all _ fun z => ?_)
  · exact ((by fun_prop : Continuous (fun w : Pl => w.1 ^ 2 + w.2 ^ 2)).mul
      (HTD.heatK_cont a)).aestronglyMeasurable
  · have hK0 : 0 ≤ heatK a z := (HM.heatK_pos ha z).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) hK0)]
    exact Q_heatK_le ha z

/-- Multiplying an integrable function by a bounded continuous one stays integrable. -/
lemma int_mul_bdd {F h : Pl → ℝ} {B : ℝ} (hF : Integrable F) (hh : Continuous h)
    (hB : ∀ z, |h z| ≤ B) : Integrable (fun z => F z * h z) := by
  refine Integrable.mono' (hF.norm.mul_const B)
    (hF.aestronglyMeasurable.mul hh.aestronglyMeasurable) (ae_of_all _ fun z => ?_)
  simp only [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hB z) (abs_nonneg _)

/-- Second derivative of the Gaussian in direction `0`. -/
lemma pd00_heatK {a : ℝ} (ha : 0 < a) (z : Pl) :
    B0579.pd 0 (B0579.pd 0 (heatK a)) z = (-1 / (2 * a) + z.1 ^ 2 / (4 * a ^ 2)) * heatK a z := by
  have ha0 : a ≠ 0 := ha.ne'
  have hd0 : B0579.pd 0 (heatK a) = fun w : Pl => -(w.1) / (2 * a) * heatK a w :=
    funext (HTD.pd0_heatK ha)
  have hg0 : Differentiable ℝ (fun w : Pl => -(w.1) / (2 * a) * heatK a w) := by
    have : Differentiable ℝ (fun w : Pl => -(w.1) / (2 * a)) := by fun_prop
    exact this.mul (HTD.heatK_diff a)
  have hA0 : HasDerivAt (fun t : ℝ => -(z.1 + t) / (2 * a)) (-1 / (2 * a)) 0 := by
    have h := (((hasDerivAt_id' (0:ℝ)).const_add z.1).neg).div_const (2 * a)
    exact h.congr_deriv (by ring)
  have hL0 : HasDerivAt (fun t : ℝ => (-(z.1 + t) / (2 * a)) * heatK a (z + t • B0579.dir 0))
      (B0579.pd 0 (fun w : Pl => -(w.1) / (2 * a) * heatK a w) z) 0 :=
    (HTD.line_deriv hg0 z 0).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by
      simp only [HTD.line0])
  have hp0 := hL0.unique (hA0.mul (HTD.heatK_line0 ha z))
  rw [hd0, hp0]
  simp only [zero_smul, add_zero]
  field_simp
  ring

/-- Second derivative of the Gaussian in direction `1`. -/
lemma pd11_heatK {a : ℝ} (ha : 0 < a) (z : Pl) :
    B0579.pd 1 (B0579.pd 1 (heatK a)) z = (-1 / (2 * a) + z.2 ^ 2 / (4 * a ^ 2)) * heatK a z := by
  have ha0 : a ≠ 0 := ha.ne'
  have hd1 : B0579.pd 1 (heatK a) = fun w : Pl => -(w.2) / (2 * a) * heatK a w :=
    funext (HTD.pd1_heatK ha)
  have hg1 : Differentiable ℝ (fun w : Pl => -(w.2) / (2 * a) * heatK a w) := by
    have : Differentiable ℝ (fun w : Pl => -(w.2) / (2 * a)) := by fun_prop
    exact this.mul (HTD.heatK_diff a)
  have hA1 : HasDerivAt (fun t : ℝ => -(z.2 + t) / (2 * a)) (-1 / (2 * a)) 0 := by
    have h := (((hasDerivAt_id' (0:ℝ)).const_add z.2).neg).div_const (2 * a)
    exact h.congr_deriv (by ring)
  have hL1 : HasDerivAt (fun t : ℝ => (-(z.2 + t) / (2 * a)) * heatK a (z + t • B0579.dir 1))
      (B0579.pd 1 (fun w : Pl => -(w.2) / (2 * a) * heatK a w) z) 0 :=
    (HTD.line_deriv hg1 z 1).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by
      simp only [HTD.line1])
  have hp1 := hL1.unique (hA1.mul (HTD.heatK_line1 ha z))
  rw [hd1, hp1]
  simp only [zero_smul, add_zero]
  field_simp
  ring

/-- Integrability of `∂_0 K_a`, `∂_0∂_0 K_a`. -/
lemma facts0 {a : ℝ} (ha : 0 < a) :
    Differentiable ℝ (B0579.pd 0 (heatK a)) ∧
      Integrable (fun z : Pl => B0579.pd 0 (heatK a) z) ∧
      Integrable (fun z : Pl => B0579.pd 0 (B0579.pd 0 (heatK a)) z) := by
  have hfun : B0579.pd 0 (heatK a) = fun w : Pl => -(w.1) / (2 * a) * heatK a w :=
    funext (HTD.pd0_heatK ha)
  have hfun2 : B0579.pd 0 (B0579.pd 0 (heatK a)) =
      fun z : Pl => (-1 / (2 * a) + z.1 ^ 2 / (4 * a ^ 2)) * heatK a z :=
    funext (pd00_heatK ha)
  have hK := (heatKernelMoments a ha).2.1
  have hQK := integrable_Q_heatK ha
  have ha0 : a ≠ 0 := ha.ne'
  refine ⟨?_, ?_, ?_⟩
  · rw [hfun]
    have : Differentiable ℝ (fun w : Pl => -(w.1) / (2 * a)) := by fun_prop
    exact this.mul (HTD.heatK_diff a)
  · rw [hfun]
    refine Integrable.mono' ((hK.add hQK).div_const (2 * a))
      ((by fun_prop : Continuous (fun w : Pl => -(w.1) / (2 * a))).mul
        (HTD.heatK_cont a)).aestronglyMeasurable (ae_of_all _ fun z => ?_)
    dsimp only
    simp only [Pi.add_apply]
    have hK0 : 0 ≤ heatK a z := (HM.heatK_pos ha z).le
    have hz1 : |z.1| ≤ 1 + (z.1 ^ 2 + z.2 ^ 2) := by
      nlinarith [sq_abs z.1, sq_nonneg (|z.1| - 1), sq_nonneg z.2, abs_nonneg z.1]
    have hmul := mul_le_mul_of_nonneg_right hz1 hK0
    have h2a : (0:ℝ) < 2 * a := by linarith
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_neg, abs_of_pos h2a, abs_of_nonneg hK0,
      div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ h2a.le
    nlinarith [hmul]
  · rw [hfun2]
    refine Integrable.mono' ((hK.const_mul (1 / (2 * a))).add (hQK.const_mul (1 / (4 * a ^ 2))))
      ((by fun_prop : Continuous (fun w : Pl => (-1 / (2 * a) + w.1 ^ 2 / (4 * a ^ 2)))).mul
        (HTD.heatK_cont a)).aestronglyMeasurable (ae_of_all _ fun z => ?_)
    dsimp only
    have hK0 : 0 ≤ heatK a z := (HM.heatK_pos ha z).le
    have hcabs : |-1 / (2 * a) + z.1 ^ 2 / (4 * a ^ 2)| ≤
        1 / (2 * a) + (z.1 ^ 2 + z.2 ^ 2) / (4 * a ^ 2) := by
      have h1 : 0 ≤ 1 / (2 * a) := by positivity
      have h2 : 0 ≤ z.1 ^ 2 / (4 * a ^ 2) := by positivity
      have h3 : z.1 ^ 2 / (4 * a ^ 2) ≤ (z.1 ^ 2 + z.2 ^ 2) / (4 * a ^ 2) :=
        div_le_div_of_nonneg_right (by linarith [sq_nonneg z.2]) (by positivity)
      have h4 : -1 / (2 * a) = -(1 / (2 * a)) := by ring
      have h5 : 0 ≤ (z.1 ^ 2 + z.2 ^ 2) / (4 * a ^ 2) := by positivity
      rw [abs_le, h4]
      constructor <;> linarith
    have hm := mul_le_mul_of_nonneg_right hcabs hK0
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hK0]
    calc |-1 / (2 * a) + z.1 ^ 2 / (4 * a ^ 2)| * heatK a z
        ≤ (1 / (2 * a) + (z.1 ^ 2 + z.2 ^ 2) / (4 * a ^ 2)) * heatK a z := hm
      _ = 1 / (2 * a) * heatK a z + 1 / (4 * a ^ 2) * ((z.1 ^ 2 + z.2 ^ 2) * heatK a z) := by
        ring

/-- Integrability of `∂_1 K_a`, `∂_1∂_1 K_a`. -/
lemma facts1 {a : ℝ} (ha : 0 < a) :
    Differentiable ℝ (B0579.pd 1 (heatK a)) ∧
      Integrable (fun z : Pl => B0579.pd 1 (heatK a) z) ∧
      Integrable (fun z : Pl => B0579.pd 1 (B0579.pd 1 (heatK a)) z) := by
  have hfun : B0579.pd 1 (heatK a) = fun w : Pl => -(w.2) / (2 * a) * heatK a w :=
    funext (HTD.pd1_heatK ha)
  have hfun2 : B0579.pd 1 (B0579.pd 1 (heatK a)) =
      fun z : Pl => (-1 / (2 * a) + z.2 ^ 2 / (4 * a ^ 2)) * heatK a z :=
    funext (pd11_heatK ha)
  have hK := (heatKernelMoments a ha).2.1
  have hQK := integrable_Q_heatK ha
  have ha0 : a ≠ 0 := ha.ne'
  refine ⟨?_, ?_, ?_⟩
  · rw [hfun]
    have : Differentiable ℝ (fun w : Pl => -(w.2) / (2 * a)) := by fun_prop
    exact this.mul (HTD.heatK_diff a)
  · rw [hfun]
    refine Integrable.mono' ((hK.add hQK).div_const (2 * a))
      ((by fun_prop : Continuous (fun w : Pl => -(w.2) / (2 * a))).mul
        (HTD.heatK_cont a)).aestronglyMeasurable (ae_of_all _ fun z => ?_)
    dsimp only
    simp only [Pi.add_apply]
    have hK0 : 0 ≤ heatK a z := (HM.heatK_pos ha z).le
    have hz2 : |z.2| ≤ 1 + (z.1 ^ 2 + z.2 ^ 2) := by
      nlinarith [sq_abs z.2, sq_nonneg (|z.2| - 1), sq_nonneg z.1, abs_nonneg z.2]
    have hmul := mul_le_mul_of_nonneg_right hz2 hK0
    have h2a : (0:ℝ) < 2 * a := by linarith
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_neg, abs_of_pos h2a, abs_of_nonneg hK0,
      div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ h2a.le
    nlinarith [hmul]
  · rw [hfun2]
    refine Integrable.mono' ((hK.const_mul (1 / (2 * a))).add (hQK.const_mul (1 / (4 * a ^ 2))))
      ((by fun_prop : Continuous (fun w : Pl => (-1 / (2 * a) + w.2 ^ 2 / (4 * a ^ 2)))).mul
        (HTD.heatK_cont a)).aestronglyMeasurable (ae_of_all _ fun z => ?_)
    dsimp only
    have hK0 : 0 ≤ heatK a z := (HM.heatK_pos ha z).le
    have hcabs : |-1 / (2 * a) + z.2 ^ 2 / (4 * a ^ 2)| ≤
        1 / (2 * a) + (z.1 ^ 2 + z.2 ^ 2) / (4 * a ^ 2) := by
      have h1 : 0 ≤ 1 / (2 * a) := by positivity
      have h2 : 0 ≤ z.2 ^ 2 / (4 * a ^ 2) := by positivity
      have h3 : z.2 ^ 2 / (4 * a ^ 2) ≤ (z.1 ^ 2 + z.2 ^ 2) / (4 * a ^ 2) :=
        div_le_div_of_nonneg_right (by linarith [sq_nonneg z.1]) (by positivity)
      have h4 : -1 / (2 * a) = -(1 / (2 * a)) := by ring
      have h5 : 0 ≤ (z.1 ^ 2 + z.2 ^ 2) / (4 * a ^ 2) := by positivity
      rw [abs_le, h4]
      constructor <;> linarith
    have hm := mul_le_mul_of_nonneg_right hcabs hK0
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hK0]
    calc |-1 / (2 * a) + z.2 ^ 2 / (4 * a ^ 2)| * heatK a z
        ≤ (1 / (2 * a) + (z.1 ^ 2 + z.2 ^ 2) / (4 * a ^ 2)) * heatK a z := hm
      _ = 1 / (2 * a) * heatK a z + 1 / (4 * a ^ 2) * ((z.1 ^ 2 + z.2 ^ 2) * heatK a z) := by
        ring

/-- One coordinate of the transfer: `∫ K ∂_j∂_j g(x - ·) = ∫ ∂_j∂_j K · g(x - ·)`. -/
lemma step_gen (j : Fin 2) {B : ℝ} {g : Pl → ℝ} (hg : ContDiff ℝ 2 g) (hW : WB B g)
    (hW1 : ∀ k : Fin 2, WB B (B0579.pd k g))
    (hW2 : ∀ i k : Fin 2, WB B (B0579.pd i (B0579.pd k g)))
    {a : ℝ} (ha : 0 < a) (x : Pl)
    (hKd : Differentiable ℝ (B0579.pd j (heatK a)))
    (hKi1 : Integrable (fun z : Pl => B0579.pd j (heatK a) z))
    (hKi2 : Integrable (fun z : Pl => B0579.pd j (B0579.pd j (heatK a)) z)) :
    ∫ z : Pl, heatK a z * B0579.pd j (B0579.pd j g) (x - z)
      = ∫ z : Pl, B0579.pd j (B0579.pd j (heatK a)) z * g (x - z) := by
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hpg : ContDiff ℝ 1 (B0579.pd j g) := pd_contDiff_one hg j
  have hpgd : Differentiable ℝ (B0579.pd j g) := hpg.differentiable one_ne_zero
  have hgc : Continuous g := hg.continuous
  have hpgc : Continuous (B0579.pd j g) := hpg.continuous
  have hppc : Continuous (B0579.pd j (B0579.pd j g)) :=
    (hpg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hKi0 : Integrable (fun z : Pl => heatK a z) := (heatKernelMoments a ha).2.1
  have cg : Continuous (fun z : Pl => g (x - z)) := hgc.comp (continuous_const.sub continuous_id)
  have cpg : Continuous (fun z : Pl => B0579.pd j g (x - z)) :=
    hpgc.comp (continuous_const.sub continuous_id)
  have cppg : Continuous (fun z : Pl => B0579.pd j (B0579.pd j g) (x - z)) :=
    hppc.comp (continuous_const.sub continuous_id)
  have hbg : ∀ z : Pl, |g (x - z)| ≤ B := fun z => abs_le_of_WB_aux hW (x - z)
  have hbpg : ∀ z : Pl, |B0579.pd j g (x - z)| ≤ B := fun z => abs_le_of_WB_aux (hW1 j) (x - z)
  have hbppg : ∀ z : Pl, |B0579.pd j (B0579.pd j g) (x - z)| ≤ B :=
    fun z => abs_le_of_WB_aux (hW2 j j) (x - z)
  have s1 : ∫ z : Pl, heatK a z * B0579.pd j (B0579.pd j g) (x - z)
      = ∫ z : Pl, B0579.pd j (heatK a) z * B0579.pd j g (x - z) :=
    ibp_conv (HTD.heatK_diff a) hpgd x (B0579.dir j)
      (int_mul_bdd hKi1 cpg hbpg) (int_mul_bdd hKi0 cppg hbppg) (int_mul_bdd hKi0 cpg hbpg)
  have s2 : ∫ z : Pl, B0579.pd j (heatK a) z * B0579.pd j g (x - z)
      = ∫ z : Pl, B0579.pd j (B0579.pd j (heatK a)) z * g (x - z) :=
    ibp_conv hKd hgd x (B0579.dir j)
      (int_mul_bdd hKi2 cg hbg) (int_mul_bdd hKi1 cpg hbpg) (int_mul_bdd hKi1 cg hbg)
  rw [s1, s2]


/-- **`PartII-b:T22/1/8/2`** The Laplacian transfers onto the kernel:
`K_a * Δg = (ΔK_a) * g` for `a > 0`. -/
theorem heatLapTransfer : UnforcedLeray.Short.IIb.CylPDE.HeatLapTransfer := by
  intro B g hg hW hW1 hW2 a ha x
  have hgc : Continuous g := hg.continuous
  have cg : Continuous (fun z : Pl => g (x - z)) := hgc.comp (continuous_const.sub continuous_id)
  have hbg : ∀ z : Pl, |g (x - z)| ≤ B := fun z => abs_le_of_WB_aux hW (x - z)
  have hKi0 : Integrable (fun z : Pl => heatK a z) := (heatKernelMoments a ha).2.1
  have hpg0 : ContDiff ℝ 1 (B0579.pd 0 g) := pd_contDiff_one hg 0
  have hpg1 : ContDiff ℝ 1 (B0579.pd 1 g) := pd_contDiff_one hg 1
  have hpp0 : Continuous (B0579.pd 0 (B0579.pd 0 g)) :=
    (hpg0.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hpp1 : Continuous (B0579.pd 1 (B0579.pd 1 g)) :=
    (hpg1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have c00 : Continuous (fun z : Pl => B0579.pd 0 (B0579.pd 0 g) (x - z)) :=
    hpp0.comp (continuous_const.sub continuous_id)
  have c11 : Continuous (fun z : Pl => B0579.pd 1 (B0579.pd 1 g) (x - z)) :=
    hpp1.comp (continuous_const.sub continuous_id)
  have b00 : ∀ z : Pl, |B0579.pd 0 (B0579.pd 0 g) (x - z)| ≤ B :=
    fun z => abs_le_of_WB_aux (hW2 0 0) (x - z)
  have b11 : ∀ z : Pl, |B0579.pd 1 (B0579.pd 1 g) (x - z)| ≤ B :=
    fun z => abs_le_of_WB_aux (hW2 1 1) (x - z)
  have i00 : Integrable (fun z : Pl => heatK a z * B0579.pd 0 (B0579.pd 0 g) (x - z)) :=
    int_mul_bdd hKi0 c00 b00
  have i11 : Integrable (fun z : Pl => heatK a z * B0579.pd 1 (B0579.pd 1 g) (x - z)) :=
    int_mul_bdd hKi0 c11 b11
  have j0 : Integrable (fun z : Pl => B0579.pd 0 (B0579.pd 0 (heatK a)) z * g (x - z)) :=
    int_mul_bdd (facts0 ha).2.2 cg hbg
  have j1 : Integrable (fun z : Pl => B0579.pd 1 (B0579.pd 1 (heatK a)) z * g (x - z)) :=
    int_mul_bdd (facts1 ha).2.2 cg hbg
  have step0 := step_gen 0 hg hW hW1 hW2 ha x (facts0 ha).1 (facts0 ha).2.1 (facts0 ha).2.2
  have step1 := step_gen 1 hg hW hW1 hW2 ha x (facts1 ha).1 (facts1 ha).2.1 (facts1 ha).2.2
  rw [heatSG_eq_conv_aux a ha]
  have e : (fun z : Pl => heatK a z * lapP g (x - z)) = fun z : Pl =>
      heatK a z * B0579.pd 0 (B0579.pd 0 g) (x - z) +
        heatK a z * B0579.pd 1 (B0579.pd 1 g) (x - z) := by
    funext z
    unfold lapP
    ring
  rw [e, integral_add i00 i11, step0, step1]
  have e2 : (∫ z : Pl, B0579.pd 0 (B0579.pd 0 (heatK a)) z * g (x - z))
      + (∫ z : Pl, B0579.pd 1 (B0579.pd 1 (heatK a)) z * g (x - z))
      = ∫ z : Pl, lapP (heatK a) z * g (x - z) := by
    rw [← integral_add j0 j1]
    congr 1
    funext z
    beta_reduce
    unfold lapP
    ring
  rw [e2]
  have h2 := integral_sub_left_eq_self (fun w : Pl => lapP (heatK a) (x - w) * g w) volume x
  simp only [sub_sub_cancel] at h2
  exact h2

end HLT

end UnforcedLeray.Short.IIb.CylPDE
