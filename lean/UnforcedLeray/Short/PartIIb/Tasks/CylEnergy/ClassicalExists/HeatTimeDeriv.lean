import UnforcedLeray.Short.PartIIb.Sub.T22_1_8
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.HeatCommute

/-!


Proves `HeatTimeDeriv` (`Sub/T22_1_8.lean`), the time derivative of the heat semigroup
under the integral sign. Source: `the November 2 reference manuscript`,
lines 2074-2093 and 2103-2105.

Route: `heatSG b g x = ∫ K_b(z) g(x - z) dz` for `b > 0`; `∂_b K_b(z) = (-1/b + |z|²/(4b²)) K_b(z)`
pointwise; this equals `ΔK_b(z)` (`lapP_heatK`); differentiation under the integral sign on the
neighbourhood `(a/2, 3a/2)` with a Gaussian majorant; change of variables `z ↦ x - y`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb.CylPDE

namespace HTD

lemma heatK_cont (b : ℝ) : Continuous (heatK b) := by
  unfold heatK
  fun_prop

lemma heatK_diff (b : ℝ) : Differentiable ℝ (heatK b) := by
  unfold heatK
  fun_prop

lemma line0 (w : Pl) (t : ℝ) : w + t • B0579.dir 0 = (w.1 + t, w.2) := by
  ext <;> simp [B0579.dir]

lemma line1 (w : Pl) (t : ℝ) : w + t • B0579.dir 1 = (w.1, w.2 + t) := by
  ext <;> simp [B0579.dir]

/-- The derivative of `t ↦ φ (w + t e_j)` at `0` is `pd j φ w`. -/
lemma line_deriv {φ : Pl → ℝ} (hφ : Differentiable ℝ φ) (w : Pl) (j : Fin 2) :
    HasDerivAt (fun t : ℝ => φ (w + t • B0579.dir j)) (B0579.pd j φ w) 0 := by
  have hL : HasDerivAt (fun t : ℝ => w + t • B0579.dir j) (B0579.dir j) 0 := by
    simpa using ((hasDerivAt_id' (0:ℝ)).smul_const (B0579.dir j)).const_add w
  have hc := (hφ (w + (0:ℝ) • B0579.dir j)).hasFDerivAt.comp_hasDerivAt (0:ℝ) hL
  rw [zero_smul, add_zero] at hc
  exact hc

/-- Derivative of `c ↦ K_c(z)` at `c = b > 0`. -/
lemma heatK_hasDerivAt_b {b : ℝ} (hb : 0 < b) (z : Pl) :
    HasDerivAt (fun c : ℝ => heatK c z)
      ((-1 / b + (z.1 ^ 2 + z.2 ^ 2) / (4 * b ^ 2)) * heatK b z) b := by
  have hb0 : b ≠ 0 := hb.ne'
  have hc : HasDerivAt (fun c : ℝ => 1 / (4 * Real.pi * c)) (-(1 / (4 * Real.pi * b ^ 2))) b := by
    have h := (hasDerivAt_const b (1:ℝ)).div ((hasDerivAt_id' b).const_mul (4 * Real.pi))
      (by positivity)
    exact h.congr_deriv (by field_simp; ring)
  have hq : HasDerivAt (fun c : ℝ => -(z.1 ^ 2 + z.2 ^ 2) / (4 * c))
      ((z.1 ^ 2 + z.2 ^ 2) / (4 * b ^ 2)) b := by
    have h := (hasDerivAt_const b (-(z.1 ^ 2 + z.2 ^ 2))).div
      ((hasDerivAt_id' b).const_mul 4) (by positivity)
    exact h.congr_deriv (by field_simp; ring)
  have h := hc.mul hq.exp
  unfold heatK
  refine h.congr_deriv ?_
  field_simp

/-- Derivative of `t ↦ K_a(w + t e_0)` at `0`. -/
lemma heatK_line0 {a : ℝ} (ha : 0 < a) (w : Pl) :
    HasDerivAt (fun t : ℝ => heatK a (w + t • B0579.dir 0))
      (-(w.1) / (2 * a) * heatK a w) 0 := by
  have hfun : (fun t : ℝ => heatK a (w + t • B0579.dir 0)) =
      fun t : ℝ => 1 / (4 * Real.pi * a) * Real.exp (-((w.1 + t) ^ 2 + w.2 ^ 2) / (4 * a)) := by
    funext t
    rw [line0]
    rfl
  have hp : HasDerivAt (fun t : ℝ => -((w.1 + t) ^ 2 + w.2 ^ 2) / (4 * a))
      (-(2 * w.1) / (4 * a)) 0 := by
    have h := ((((hasDerivAt_id' (0:ℝ)).const_add w.1).pow 2).add_const (w.2 ^ 2)).neg.div_const
      (4 * a)
    exact h.congr_deriv (by norm_num)
  have hE := (hp.exp).const_mul (1 / (4 * Real.pi * a))
  rw [hfun]
  refine hE.congr_deriv ?_
  unfold heatK
  simp only [add_zero]
  have ha0 : a ≠ 0 := ha.ne'
  field_simp
  ring

/-- Derivative of `t ↦ K_a(w + t e_1)` at `0`. -/
lemma heatK_line1 {a : ℝ} (ha : 0 < a) (w : Pl) :
    HasDerivAt (fun t : ℝ => heatK a (w + t • B0579.dir 1))
      (-(w.2) / (2 * a) * heatK a w) 0 := by
  have hfun : (fun t : ℝ => heatK a (w + t • B0579.dir 1)) =
      fun t : ℝ => 1 / (4 * Real.pi * a) * Real.exp (-((w.1) ^ 2 + (w.2 + t) ^ 2) / (4 * a)) := by
    funext t
    rw [line1]
    rfl
  have hp : HasDerivAt (fun t : ℝ => -((w.1) ^ 2 + (w.2 + t) ^ 2) / (4 * a))
      (-(2 * w.2) / (4 * a)) 0 := by
    have h := ((((hasDerivAt_id' (0:ℝ)).const_add w.2).pow 2).const_add (w.1 ^ 2)).neg.div_const
      (4 * a)
    exact h.congr_deriv (by norm_num)
  have hE := (hp.exp).const_mul (1 / (4 * Real.pi * a))
  rw [hfun]
  refine hE.congr_deriv ?_
  unfold heatK
  simp only [add_zero]
  have ha0 : a ≠ 0 := ha.ne'
  field_simp
  ring

lemma pd0_heatK {a : ℝ} (ha : 0 < a) (w : Pl) :
    B0579.pd 0 (heatK a) w = -(w.1) / (2 * a) * heatK a w :=
  (line_deriv (heatK_diff a) w 0).unique (heatK_line0 ha w)

lemma pd1_heatK {a : ℝ} (ha : 0 < a) (w : Pl) :
    B0579.pd 1 (heatK a) w = -(w.2) / (2 * a) * heatK a w :=
  (line_deriv (heatK_diff a) w 1).unique (heatK_line1 ha w)

/-- The Laplacian of the Gaussian: `Δ K_a = (-1/a + |z|²/(4a²)) K_a`. -/
lemma lapP_heatK {a : ℝ} (ha : 0 < a) (z : Pl) :
    lapP (heatK a) z = (-1 / a + (z.1 ^ 2 + z.2 ^ 2) / (4 * a ^ 2)) * heatK a z := by
  have ha0 : a ≠ 0 := ha.ne'
  have hd0 : B0579.pd 0 (heatK a) = fun w : Pl => -(w.1) / (2 * a) * heatK a w :=
    funext (pd0_heatK ha)
  have hd1 : B0579.pd 1 (heatK a) = fun w : Pl => -(w.2) / (2 * a) * heatK a w :=
    funext (pd1_heatK ha)
  have hg0 : Differentiable ℝ (fun w : Pl => -(w.1) / (2 * a) * heatK a w) := by
    have : Differentiable ℝ (fun w : Pl => -(w.1) / (2 * a)) := by fun_prop
    exact this.mul (heatK_diff a)
  have hg1 : Differentiable ℝ (fun w : Pl => -(w.2) / (2 * a) * heatK a w) := by
    have : Differentiable ℝ (fun w : Pl => -(w.2) / (2 * a)) := by fun_prop
    exact this.mul (heatK_diff a)
  have hA0 : HasDerivAt (fun t : ℝ => -(z.1 + t) / (2 * a)) (-1 / (2 * a)) 0 := by
    have h := (((hasDerivAt_id' (0:ℝ)).const_add z.1).neg).div_const (2 * a)
    exact h.congr_deriv (by ring)
  have hA1 : HasDerivAt (fun t : ℝ => -(z.2 + t) / (2 * a)) (-1 / (2 * a)) 0 := by
    have h := (((hasDerivAt_id' (0:ℝ)).const_add z.2).neg).div_const (2 * a)
    exact h.congr_deriv (by ring)
  have hL0 : HasDerivAt (fun t : ℝ => (-(z.1 + t) / (2 * a)) * heatK a (z + t • B0579.dir 0))
      (B0579.pd 0 (fun w : Pl => -(w.1) / (2 * a) * heatK a w) z) 0 :=
    (line_deriv hg0 z 0).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by
      simp only [line0])
  have hL1 : HasDerivAt (fun t : ℝ => (-(z.2 + t) / (2 * a)) * heatK a (z + t • B0579.dir 1))
      (B0579.pd 1 (fun w : Pl => -(w.2) / (2 * a) * heatK a w) z) 0 :=
    (line_deriv hg1 z 1).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by
      simp only [line1])
  have hp0 : B0579.pd 0 (fun w : Pl => -(w.1) / (2 * a) * heatK a w) z
      = (-1 / (2 * a)) * heatK a z + (-(z.1) / (2 * a)) * (-(z.1) / (2 * a) * heatK a z) := by
    rw [hL0.unique (hA0.mul (heatK_line0 ha z))]
    simp
  have hp1 : B0579.pd 1 (fun w : Pl => -(w.2) / (2 * a) * heatK a w) z
      = (-1 / (2 * a)) * heatK a z + (-(z.2) / (2 * a)) * (-(z.2) / (2 * a) * heatK a z) := by
    rw [hL1.unique (hA1.mul (heatK_line1 ha z))]
    simp
  unfold lapP
  rw [hd0, hd1, hp0, hp1]
  field_simp
  ring

lemma coef_bound {a b Q : ℝ} (ha : 0 < a) (hb1 : a / 2 < b) (hb2 : b < 3 * a / 2) (hQ : 0 ≤ Q) :
    |-1 / b + Q / (4 * b ^ 2)| ≤ 2 / a + Q / a ^ 2 := by
  have hb : 0 < b := lt_trans (half_pos ha) hb1
  have h1 : 1 / b ≤ 2 / a := by
    rw [div_le_iff₀ hb, div_mul_eq_mul_div, le_div_iff₀ ha]
    linarith
  have h2 : Q / (4 * b ^ 2) ≤ Q / a ^ 2 :=
    div_le_div_of_nonneg_left hQ (by positivity) (by nlinarith)
  have h3 : 0 ≤ Q / (4 * b ^ 2) := div_nonneg hQ (by positivity)
  have h4 : 0 ≤ Q / a ^ 2 := div_nonneg hQ (by positivity)
  have e : -1 / b = -(1 / b) := by ring
  have h5 : 0 ≤ 1 / b := by positivity
  have h6 : 0 ≤ 2 / a := by positivity
  rw [abs_le]
  constructor
  · rw [e]; linarith
  · rw [e]; linarith

lemma exp_key (u : ℝ) (hu : 0 ≤ u) :
    (2 + 12 * u) * Real.exp (-(2 * u)) ≤ 12 * Real.exp (-u) := by
  have hE := Real.exp_pos (-u)
  have e1 : Real.exp (-u) * Real.exp u = 1 := by
    rw [← Real.exp_add]; simp
  have hadd := Real.add_one_le_exp u
  have h1 : Real.exp (-u) * (1 + u) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hadd hE.le
    nlinarith
  have e2 : Real.exp (-(2 * u)) = Real.exp (-u) * Real.exp (-u) := by
    rw [← Real.exp_add]; ring_nf
  have h2 : (2 + 12 * u) * Real.exp (-u) ≤ 12 := by nlinarith
  have h3 := mul_le_mul_of_nonneg_right h2 hE.le
  rw [e2]
  nlinarith

lemma bound_key {a Q : ℝ} (ha : 0 < a) (hQ : 0 ≤ Q) :
    (2 / a + Q / a ^ 2) * ((1 / (2 * Real.pi * a)) * Real.exp (-Q / (6 * a))) ≤
      (12 / a) * ((1 / (2 * Real.pi * a)) * Real.exp (-Q / (12 * a))) := by
  have ha0 : a ≠ 0 := ha.ne'
  have hu0 : 0 ≤ Q / (12 * a) := div_nonneg hQ (by positivity)
  have e1 : 2 / a + Q / a ^ 2 = (2 + 12 * (Q / (12 * a))) / a := by
    field_simp
  have e2 : -Q / (6 * a) = -(2 * (Q / (12 * a))) := by
    field_simp
    ring
  have e3 : -Q / (12 * a) = -(Q / (12 * a)) := by ring
  rw [e1, e2, e3]
  have hk := exp_key (Q / (12 * a)) hu0
  have hp : 0 ≤ (1 / a) * (1 / (2 * Real.pi * a)) := by positivity
  have h4 := mul_le_mul_of_nonneg_left hk hp
  calc (2 + 12 * (Q / (12 * a))) / a * ((1 / (2 * Real.pi * a)) *
        Real.exp (-(2 * (Q / (12 * a)))))
      = (1 / a) * (1 / (2 * Real.pi * a)) *
          ((2 + 12 * (Q / (12 * a))) * Real.exp (-(2 * (Q / (12 * a))))) := by ring
    _ ≤ (1 / a) * (1 / (2 * Real.pi * a)) * (12 * Real.exp (-(Q / (12 * a)))) := h4
    _ = (12 / a) * ((1 / (2 * Real.pi * a)) * Real.exp (-(Q / (12 * a)))) := by ring

lemma heatK_upper {a b : ℝ} (ha : 0 < a) (hb1 : a / 2 < b) (hb2 : b < 3 * a / 2) (z : Pl) :
    heatK b z ≤ (1 / (2 * Real.pi * a)) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (6 * a)) := by
  have hb : 0 < b := lt_trans (half_pos ha) hb1
  have hQ : 0 ≤ z.1 ^ 2 + z.2 ^ 2 := by positivity
  unfold heatK
  have h1 : 1 / (4 * Real.pi * b) ≤ 1 / (2 * Real.pi * a) := by
    apply one_div_le_one_div_of_le
    · positivity
    · nlinarith [Real.pi_pos]
  have hq := div_le_div_of_nonneg_left hQ (by positivity : (0:ℝ) < 4 * b)
    (by linarith : 4 * b ≤ 6 * a)
  have h2 : Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * b)) ≤
      Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (6 * a)) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div]
    linarith
  exact mul_le_mul h1 h2 (Real.exp_nonneg _) (by positivity)

end HTD

open HTD in
/-- **`PartII-b:T22/1/8/1`** The time derivative of the heat semigroup under the integral sign. -/
theorem heatTimeDeriv : UnforcedLeray.Short.IIb.CylPDE.HeatTimeDeriv := by
  intro B g hgc hW a ha x
  have ha0 : a ≠ 0 := ha.ne'
  have hs : Ioo (a / 2) (3 * a / 2) ∈ 𝓝 a := Ioo_mem_nhds (by linarith) (by linarith)
  have hgcont : Continuous (fun z : Pl => g (x - z)) :=
    hgc.comp (continuous_const.sub continuous_id)
  have hF_cont : ∀ b : ℝ, Continuous (fun z : Pl => heatK b z * g (x - z)) :=
    fun b => (heatK_cont b).mul hgcont
  have hcoef : Continuous (fun z : Pl => -1 / a + (z.1 ^ 2 + z.2 ^ 2) / (4 * a ^ 2)) := by
    fun_prop
  have hF'_cont : Continuous (fun z : Pl =>
      (-1 / a + (z.1 ^ 2 + z.2 ^ 2) / (4 * a ^ 2)) * heatK a z * g (x - z)) :=
    (hcoef.mul (heatK_cont a)).mul hgcont
  have hM := heatKernelMoments a ha
  have hF_int : Integrable (fun z : Pl => heatK a z * g (x - z)) volume := by
    refine Integrable.mono' (hM.2.1.mul_const B) (hF_cont a).aestronglyMeasurable
      (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (HM.heatK_pos ha z)]
    exact mul_le_mul_of_nonneg_left (abs_le_of_WB_aux hW (x - z)) (HM.heatK_pos ha z).le
  -- pointwise bound on the neighbourhood
  have hbd : ∀ b ∈ Ioo (a / 2) (3 * a / 2), ∀ z : Pl,
      ‖(-1 / b + (z.1 ^ 2 + z.2 ^ 2) / (4 * b ^ 2)) * heatK b z * g (x - z)‖ ≤
        ((12 / a) * (1 / (2 * Real.pi * a)) * B) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (12 * a)) := by
    intro b hb z
    have hb1 := hb.1
    have hb2 := hb.2
    have hb0 : 0 < b := lt_trans (half_pos ha) hb1
    have hQ : 0 ≤ z.1 ^ 2 + z.2 ^ 2 := by positivity
    have hc := coef_bound ha hb1 hb2 hQ
    have hk := heatK_upper ha hb1 hb2 z
    have hgB := abs_le_of_WB_aux hW (x - z)
    have hK0 : 0 ≤ heatK b z := (HM.heatK_pos hb0 z).le
    have hBnn : 0 ≤ B := (abs_nonneg _).trans hgB
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hK0]
    calc |-1 / b + (z.1 ^ 2 + z.2 ^ 2) / (4 * b ^ 2)| * heatK b z * |g (x - z)|
        ≤ (2 / a + (z.1 ^ 2 + z.2 ^ 2) / a ^ 2) * ((1 / (2 * Real.pi * a)) *
            Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (6 * a))) * B :=
          mul_le_mul (mul_le_mul hc hk hK0 (by positivity)) hgB (abs_nonneg _) (by positivity)
      _ ≤ (12 / a) * ((1 / (2 * Real.pi * a)) *
            Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (12 * a))) * B :=
          mul_le_mul_of_nonneg_right (bound_key ha hQ) hBnn
      _ = ((12 / a) * (1 / (2 * Real.pi * a)) * B) *
            Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (12 * a)) := by ring
  -- integrable majorant: exp(-|z|²/(12a)) = 12πa · K_{3a}(z)
  have hI : Integrable (fun z : Pl => Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (12 * a))) := by
    have h3 := ((heatKernelMoments (3 * a) (by linarith)).2.1).const_mul
      (4 * Real.pi * (3 * a))
    refine h3.congr (ae_of_all _ fun z => ?_)
    show (4 * Real.pi * (3 * a)) * heatK (3 * a) z = Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (12 * a))
    unfold heatK
    have h12 : (4:ℝ) * (3 * a) = 12 * a := by ring
    have hne : (4 * Real.pi * (3 * a)) ≠ 0 := by positivity
    rw [h12]
    field_simp
  have hG := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := a)
    (F := fun b z => heatK b z * g (x - z))
    (F' := fun b z => (-1 / b + (z.1 ^ 2 + z.2 ^ 2) / (4 * b ^ 2)) * heatK b z * g (x - z))
    (bound := fun z : Pl =>
      ((12 / a) * (1 / (2 * Real.pi * a)) * B) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (12 * a)))
    (s := Ioo (a / 2) (3 * a / 2)) hs
    (Filter.Eventually.of_forall fun b => (hF_cont b).aestronglyMeasurable)
    hF_int
    hF'_cont.aestronglyMeasurable
    (ae_of_all _ fun z b hb => hbd b hb z)
    (hI.const_mul ((12 / a) * (1 / (2 * Real.pi * a)) * B))
    (ae_of_all _ fun z b hb =>
      (heatK_hasDerivAt_b (lt_trans (half_pos ha) hb.1) z).mul_const (g (x - z)))
  have hcongr : (fun b => heatSG b g x) =ᶠ[𝓝 a]
      (fun b => ∫ z : Pl, heatK b z * g (x - z)) := by
    filter_upwards [hs] with b hb
    exact heatSG_eq_conv_aux b (lt_trans (half_pos ha) hb.1) g x
  have hfin : HasDerivAt (fun b => heatSG b g x)
      (∫ z : Pl, (-1 / a + (z.1 ^ 2 + z.2 ^ 2) / (4 * a ^ 2)) * heatK a z * g (x - z)) a :=
    hG.2.congr_of_eventuallyEq hcongr
  have hval : (∫ z : Pl, (-1 / a + (z.1 ^ 2 + z.2 ^ 2) / (4 * a ^ 2)) * heatK a z * g (x - z))
      = ∫ y : Pl, lapP (heatK a) (x - y) * g y := by
    have h1 : (fun z : Pl => (-1 / a + (z.1 ^ 2 + z.2 ^ 2) / (4 * a ^ 2)) * heatK a z * g (x - z))
        = fun z : Pl => lapP (heatK a) z * g (x - z) := by
      funext z
      rw [lapP_heatK ha z]
    rw [h1]
    have h2 := integral_sub_left_eq_self (fun w : Pl => lapP (heatK a) (x - w) * g w) volume x
    simp only [sub_sub_cancel] at h2
    exact h2
  rw [hval] at hfin
  exact hfin

end UnforcedLeray.Short.IIb.CylPDE
