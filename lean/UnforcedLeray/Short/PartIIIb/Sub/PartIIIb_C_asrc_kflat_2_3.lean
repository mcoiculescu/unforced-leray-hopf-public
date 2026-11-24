import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_2

/-!
# `PartIII-b:C/asrc/kflat/2/3` : linearity of `K_c` on the cell (`kcMer`)

Source of record: `the November 2 reference manuscript` (lines 4610-4612).
`kcMer ξ` is the Lebesgue value of `kcLp ξ = realBiotSavart (reX ξ)`; `reX` is real-linear on
`Xmc`, and `realBiotSavart` is additive and real-homogeneous on zero-circulation data.
The equality of `Lp` classes is transferred to `Cyl.avgμ c = ofReal c⁻¹ • cellμ c`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open FlatSettingInst

/-- `realBiotSavart` depends only on the field (the circulation proofs are propositions). -/
theorem kcMerLinear_rbs_congr {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)
    {ω ω' : B0579.X c m} (h : ω = ω') {h0 : ∫ x in B0579.cell c, ω x = 0}
    {h0' : ∫ x in B0579.cell c, ω' x = 0} :
    UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.realBiotSavart hm ω h0 =
      UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.realBiotSavart hm ω' h0' := by
  subst h
  rfl

/-- Transfer of a.e. equality from the cell to the averaged cylinder measure. -/
theorem kcMerLinear_ae_avg {c : ℝ} (hc : 0 < c) {E : Type*} {f g : ℝ × ℝ → E}
    (h : f =ᵐ[volume.restrict (B0579.cell c)] g) : f =ᵐ[Cyl.avgμ c] g := by
  have hcell : Cyl.cell c = B0579.cell c := by
    simp only [Cyl.cell, B0579.cell, neg_div]
  have hne : ENNReal.ofReal c⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 hc)).ne'
  unfold Cyl.avgμ Cyl.cellμ
  rw [hcell]
  unfold Filter.EventuallyEq
  rw [Measure.ae_ennreal_smul_measure_eq hne]
  exact h

/-- `reX` is additive on `Xmc`. -/
theorem kcMerLinear_reX_add {c m : ℝ} [Fact (1 < m)] (ξ ξ' : Xmc c m) :
    reX (ξ + ξ').1 = reX ξ.1 + reX ξ'.1 := by
  apply Lp.ext
  filter_upwards [coeFn_reX (ξ + ξ').1, Lp.coeFn_add (reX ξ.1) (reX ξ'.1), coeFn_reX ξ.1,
    coeFn_reX ξ'.1, Lp.coeFn_add ξ.1 ξ'.1] with x h1 h2 h3 h4 h5
  rw [h1, h2, Pi.add_apply, h3, h4]
  have h5x : (ξ + ξ').1 x = ξ.1 x + ξ'.1 x := by
    have : (ξ + ξ').1 = ξ.1 + ξ'.1 := rfl
    rw [this, h5, Pi.add_apply]
  rw [h5x, Complex.add_re]

/-- `reX` is real-homogeneous on `Xmc`. -/
theorem kcMerLinear_reX_smul {c m : ℝ} [Fact (1 < m)] (r : ℝ) (ξ : Xmc c m) :
    reX ((r : ℂ) • ξ).1 = r • reX ξ.1 := by
  apply Lp.ext
  have hsm : ((r : ℂ) • ξ).1 = (r : ℂ) • ξ.1 := rfl
  filter_upwards [coeFn_reX ((r : ℂ) • ξ).1, Lp.coeFn_smul r (reX ξ.1), coeFn_reX ξ.1,
    Lp.coeFn_smul (r : ℂ) ξ.1] with x h1 h2 h3 h4
  rw [h1, h2, Pi.smul_apply, h3, hsm, h4]
  simp

/-- **Linearity of `K_c` on the cell (source 4610-4612).** -/
theorem kcMerLinear (m : ℝ) [Fact (1 < m)] : KcMerLinearProp m := by
  intro ν hν
  have : Fact (0 < cOf ν) := ⟨cOf_pos hν⟩
  intro ξ ξ' r
  have hm : 1 ≤ m := one_le_of_fact
  -- additivity of `kcLp`
  have hK_add : kcLp (ξ + ξ') = kcLp ξ + kcLp ξ' := by
    have hsum : ∫ x in B0579.cell (cOf ν), (reX ξ.1 + reX ξ'.1) x = 0 := by
      rw [← kcMerLinear_reX_add]
      exact reX_circ (ξ + ξ')
    calc kcLp (ξ + ξ')
        = UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.realBiotSavart hm
            (reX (ξ + ξ').1) (reX_circ (ξ + ξ')) := rfl
      _ = UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.realBiotSavart hm
            (reX ξ.1 + reX ξ'.1) hsum :=
          kcMerLinear_rbs_congr hm (kcMerLinear_reX_add ξ ξ')
      _ = UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.realBiotSavart hm (reX ξ.1)
            (reX_circ ξ) + UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.realBiotSavart hm
            (reX ξ'.1) (reX_circ ξ') :=
          UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.realBiotSavart_add hm
            (reX ξ.1) (reX ξ'.1) (reX_circ ξ) (reX_circ ξ') hsum
      _ = kcLp ξ + kcLp ξ' := rfl
  -- homogeneity of `kcLp`
  have hK_smul : kcLp ((r : ℂ) • ξ) = r • kcLp ξ := by
    have hsm : ∫ x in B0579.cell (cOf ν), (r • reX ξ.1) x = 0 := by
      rw [← kcMerLinear_reX_smul]
      exact reX_circ ((r : ℂ) • ξ)
    calc kcLp ((r : ℂ) • ξ)
        = UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.realBiotSavart hm
            (reX ((r : ℂ) • ξ).1) (reX_circ ((r : ℂ) • ξ)) := rfl
      _ = UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.realBiotSavart hm
            (r • reX ξ.1) hsm :=
          kcMerLinear_rbs_congr hm (kcMerLinear_reX_smul r ξ)
      _ = r • UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.realBiotSavart hm (reX ξ.1)
            (reX_circ ξ) :=
          UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.realBiotSavart_smul hm r
            (reX ξ.1) (reX_circ ξ) hsm
      _ = r • kcLp ξ := rfl
  constructor
  · have e1 := kcMer_ae (ξ + ξ')
    have e2 := kcMer_ae ξ
    have e3 := kcMer_ae ξ'
    have e5 := Lp.coeFn_add (kcLp ξ) (kcLp ξ')
    refine kcMerLinear_ae_avg (cOf_pos hν) ?_
    filter_upwards [e1, e2, e3, e5] with x h1 h2 h3 h5
    rw [h1, hK_add, Pi.add_apply, h2, h3, h5]
    rfl
  · have e1 := kcMer_ae ((r : ℂ) • ξ)
    have e2 := kcMer_ae ξ
    have e5 := Lp.coeFn_smul r (kcLp ξ)
    refine kcMerLinear_ae_avg (cOf_pos hν) ?_
    filter_upwards [e1, e2, e5] with x h1 h2 h5
    rw [h1, hK_smul, Pi.smul_apply, h2, h5]
    rfl

end UnforcedLeray.Short.PartIIIb.Concrete
