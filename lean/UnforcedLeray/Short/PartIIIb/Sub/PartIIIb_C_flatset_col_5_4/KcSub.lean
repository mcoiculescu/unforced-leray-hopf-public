import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5_4

/-!
# `FcvKcSub`: the Biot-Savart velocity `kcC` is a.e. additive on `X_{m,c}`

Source 4610-4612.  `kcLp ξ = realBiotSavart (reX ξ)` and `reX` is additive; `realBiotSavart`
is additive on zero-circulation data (`realBiotSavart_add`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem reX_sub_aux {c m : ℝ} [Fact (1 < m)] (x y : XAmb c m) :
    reX (x - y) = reX x - reX y := by
  apply Lp.ext
  filter_upwards [coeFn_reX (x - y), Lp.coeFn_sub x y, coeFn_reX x, coeFn_reX y,
    Lp.coeFn_sub (reX x) (reX y)] with p h1 h2 h3 h4 h5
  simp only [h1, h5, h3, h4, h2, Pi.sub_apply, Complex.sub_re]

theorem rbs_congr_aux {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m) {a b : B0579.X c m}
    (ha : ∫ x in B0579.cell c, a x = 0) (hb : ∫ x in B0579.cell c, b x = 0) (h : a = b) :
    UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.realBiotSavart hm a ha =
      UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.realBiotSavart hm b hb := by
  subst h
  rfl

theorem kcLp_sub_aux {c m : ℝ} [Fact (1 < m)] [Fact (0 < c)] (ω₁ ω₂ : Xmc c m) :
    kcLp (ω₁ - ω₂) = kcLp ω₁ - kcLp ω₂ := by
  have e : (ω₁ - ω₂).1 = ω₁.1 - ω₂.1 := rfl
  have hsplit : reX (ω₁ - ω₂).1 + reX ω₂.1 = reX ω₁.1 := by
    rw [e, reX_sub_aux]
    abel
  have hsum : ∫ x in B0579.cell c, (reX (ω₁ - ω₂).1 + reX ω₂.1) x = 0 := by
    rw [hsplit]
    exact reX_circ ω₁
  have hrbs : kcLp ω₁ = kcLp (ω₁ - ω₂) + kcLp ω₂ := by
    calc kcLp ω₁
        = UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.realBiotSavart one_le_of_fact
            (reX ω₁.1) (reX_circ ω₁) := rfl
      _ = UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.realBiotSavart one_le_of_fact
            (reX (ω₁ - ω₂).1 + reX ω₂.1) hsum :=
          rbs_congr_aux one_le_of_fact _ _ hsplit.symm
      _ = UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.realBiotSavart one_le_of_fact
            (reX (ω₁ - ω₂).1) (reX_circ (ω₁ - ω₂)) +
          UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.realBiotSavart one_le_of_fact
            (reX ω₂.1) (reX_circ ω₂) :=
          UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.realBiotSavart_add one_le_of_fact
            _ _ (reX_circ (ω₁ - ω₂)) (reX_circ ω₂) hsum
      _ = kcLp (ω₁ - ω₂) + kcLp ω₂ := rfl
  have : kcLp (ω₁ - ω₂) = kcLp ω₁ - (kcLp ω₂) := by
    rw [hrbs]
    abel
  exact this

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray in
open UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst in
theorem fcvKcSub : UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FcvKcSub := by
  unfold FcvKcSub
  intro c m hm hc ω₁ ω₂ j
  have hcoe : (kcLp (ω₁ - ω₂) : ℝ × ℝ → Merid) =ᵐ[volume.restrict (B0579.cell c)]
      ((kcLp ω₁ : ℝ × ℝ → Merid) - (kcLp ω₂ : ℝ × ℝ → Merid)) := by
    rw [kcLp_sub_aux ω₁ ω₂]
    exact Lp.coeFn_sub _ _
  filter_upwards [kcMer_ae (ω₁ - ω₂), kcMer_ae ω₁, kcMer_ae ω₂, hcoe] with x h1 h2 h3 h4
  show ((kcMer (ω₁ - ω₂) x j : ℝ) : ℂ) = ((kcMer ω₁ x j : ℝ) : ℂ) - ((kcMer ω₂ x j : ℝ) : ℂ)
  rw [h1, h2, h3, h4, Pi.sub_apply]
  exact Complex.ofReal_sub _ _
