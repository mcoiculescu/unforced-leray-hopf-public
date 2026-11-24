import UnforcedLeray.Short.PartIIb.Sub.T22_1.Stages
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.HeatMoments
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.HeatGrad

/-!


Proves `HeatCommute` (`Sub/T22_1/Stages.lean`). For `a ≤ 0` the semigroup is the identity. For
`a > 0`, `heatSG a g y = ∫ K_a(z) g(y - z) dz` (translation of the convolution integral). The
partial derivative `∂_j` of this integral is taken under the integral sign (dominated convergence,
the dominating function `K_a(z) B` with `|∂_j g| ≤ B` from `WB B (∂_j g)`), which gives
`∫ K_a(z) (∂_j g)(y - z) dz = heatSG a (∂_j g) y`. Differentiability of `heatSG a g` (needed to
identify the partial derivative with the directional derivative along `dir j`) comes from
`heatGradFormula` (`HeatGrad.lean`). Source `the November 2 reference manuscript`,
lines 2074-2093 and 2103-2105.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.IIb.CylPDE

/-- A weighted bound `|h| cosh η ≤ B` gives the sup bound `|h| ≤ B`. -/
lemma abs_le_of_WB_aux {B : ℝ} {h : Pl → ℝ} (hB : WB B h) (y : Pl) : |h y| ≤ B :=
  (le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_cosh _)).trans (hB y)

/-- The convolution form of the semigroup: `e^{aΔ} h (y) = ∫ K_a(z) h(y - z) dz` for `a > 0`. -/
lemma heatSG_eq_conv_aux (a : ℝ) (ha : 0 < a) (h : Pl → ℝ) (y : Pl) :
    heatSG a h y = ∫ z : Pl, heatK a z * h (y - z) := by
  have hs := integral_sub_left_eq_self (fun w : Pl => heatK a (y - w) * h w) volume y
  simp only [sub_sub_cancel] at hs
  unfold heatSG
  rw [if_neg (not_le.mpr ha)]
  exact hs.symm

/-- Differentiation under the integral sign in the translation variable `t ↦ x + t • dir j`. -/
lemma hasDerivAt_conv_aux (a : ℝ) (ha : 0 < a) (B : ℝ) (g : Pl → ℝ) (hg : ContDiff ℝ 1 g)
    (hB : WB B g) (j : Fin 2) (hpB : WB B (B0579.pd j g)) (x : Pl) :
    HasDerivAt (fun t : ℝ => ∫ z : Pl, heatK a z * g (x + t • B0579.dir j - z))
      (∫ z : Pl, heatK a z * B0579.pd j g (x - z)) 0 := by
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hgc : Continuous g := hg.continuous
  have hpc : Continuous (B0579.pd j g) := by
    unfold B0579.pd
    exact (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hM := heatKernelMoments a ha
  have hKc : Continuous (heatK a) := by
    unfold heatK
    fun_prop
  have hKpos : ∀ z : Pl, 0 < heatK a z := hM.1
  have hKint : Integrable (heatK a) := hM.2.1
  have hcont : ∀ (c : Pl) (h : Pl → ℝ), Continuous h →
      Continuous (fun z : Pl => heatK a z * h (c - z)) :=
    fun c h hh => hKc.mul (hh.comp (continuous_const.sub continuous_id))
  have hdiff : ∀ (z : Pl) (t : ℝ), HasDerivAt (fun t : ℝ => heatK a z * g (x + t • B0579.dir j - z))
      (heatK a z * B0579.pd j g (x + t • B0579.dir j - z)) t := by
    intro z t
    have hline : HasDerivAt (fun s : ℝ => x + s • B0579.dir j - z) (B0579.dir j) t := by
      have h0 := (((hasDerivAt_id' t).smul_const (B0579.dir j)).const_add x).sub_const z
      simpa using h0
    have hc := (hgd (x + t • B0579.dir j - z)).hasFDerivAt.comp_hasDerivAt t hline
    exact hc.const_mul (heatK a z)
  have hbd : ∀ (z : Pl) (t : ℝ), ‖heatK a z * B0579.pd j g (x + t • B0579.dir j - z)‖ ≤ heatK a z * B := by
    intro z t
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hKpos z)]
    exact mul_le_mul_of_nonneg_left (abs_le_of_WB_aux hpB _) (hKpos z).le
  have hG := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := (0 : ℝ))
    (F := fun t z => heatK a z * g (x + t • B0579.dir j - z))
    (F' := fun t z => heatK a z * B0579.pd j g (x + t • B0579.dir j - z))
    (bound := fun z => heatK a z * B) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun t => (hcont (x + t • B0579.dir j) g hgc).aestronglyMeasurable)
    (by
      refine Integrable.mono' (hKint.mul_const B) (hcont _ g hgc).aestronglyMeasurable
        (ae_of_all _ fun z => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hKpos z)]
      exact mul_le_mul_of_nonneg_left (abs_le_of_WB_aux hB _) (hKpos z).le)
    (hcont _ _ hpc).aestronglyMeasurable
    (ae_of_all _ fun z t _ => hbd z t)
    (hKint.mul_const B)
    (ae_of_all _ fun z t _ => hdiff z t)
  simpa only [zero_smul, add_zero] using hG.2

/-- **`PartII-b:T22/1/7`** The heat semigroup commutes with partial derivatives. -/
theorem heatCommute : UnforcedLeray.Short.IIb.CylPDE.HeatCommute := by
  intro B g hg hB hpB a j x
  by_cases ha : 0 < a
  · have hsgd : Differentiable ℝ (heatSG a g) :=
      (heatGradFormula B g hg.continuous hB a ha).1
    have hL : HasDerivAt (fun t : ℝ => x + t • B0579.dir j) (B0579.dir j) 0 := by
      simpa using ((hasDerivAt_id' (0 : ℝ)).smul_const (B0579.dir j)).const_add x
    have hf : HasFDerivAt (heatSG a g) (fderiv ℝ (heatSG a g) (x + (0 : ℝ) • B0579.dir j))
        (x + (0 : ℝ) • B0579.dir j) := by
      rw [zero_smul, add_zero]
      exact (hsgd x).hasFDerivAt
    have h1 := hf.comp_hasDerivAt (0 : ℝ) hL
    rw [zero_smul, add_zero] at h1
    have hfun : (fun t : ℝ => heatSG a g (x + t • B0579.dir j)) =
        fun t : ℝ => ∫ z : Pl, heatK a z * g (x + t • B0579.dir j - z) := by
      funext t
      exact heatSG_eq_conv_aux a ha g _
    have h2 : HasDerivAt (fun t : ℝ => heatSG a g (x + t • B0579.dir j))
        (fderiv ℝ (heatSG a g) x (B0579.dir j)) 0 := h1
    rw [hfun] at h2
    have h3 := h2.unique (hasDerivAt_conv_aux a ha B g hg hB j (hpB j) x)
    show fderiv ℝ (heatSG a g) x (B0579.dir j) = heatSG a (B0579.pd j g) x
    rw [h3, heatSG_eq_conv_aux a ha]
  · have ha' : a ≤ 0 := not_lt.mp ha
    have e1 : ∀ h : Pl → ℝ, heatSG a h = h := fun h =>
      funext fun y => by
        unfold heatSG
        rw [if_pos ha']
    rw [e1, e1]

end UnforcedLeray.Short.IIb.CylPDE
