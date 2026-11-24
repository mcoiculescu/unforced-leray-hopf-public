import UnforcedLeray.Loc.L01Coefficient.Operators

/-!
# Step L1, helpers: `div(U ⊗ g + g ⊗ U) ∈ H¹` for `g ∈ Z`

Support for `Loc/L01Coefficient.lean` (step L1, `paper/main.tex` lines 284–290,
`loc:eq:coefficient-maps`, blueprint unit B0711: "the second follows from the `H²` algebra
for `r_heat f` and the bounded derivatives of the heat profile").

For a consistent coefficient `c = (U, ∇U, ∇²U)` and `g ∈ Z = H²_div`, the field
`Gop c g = div(U ⊗ g + g ⊗ U)` has weak derivative `GkOp E k c g` in every direction
(`Gop_GkOp_mem`). The proof applies the weak product rule (`Leibniz.lean`) to each of the
four terms of `∂ⱼ𝕋_{·j}`, with the `H¹` factor `g` or `∂ⱼg`. The `L^∞` bound of `g` enters
through a map `E : H² → C₀` representing `H²` classes (the Sobolev embedding, a hypothesis
of the main file).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Blueprint.L01

open SobolevGraph SobolevEmbedding

/-- Second order, column `j`: `(∂ⱼ𝕋_{·j}, ∂ₖ∂ⱼ𝕋_{·j})` is in the weak derivative graph. -/
theorem dcolX_dT_mem {c : Coef} (hc : IsConsistentCoef c)
    {E : H2 →L[ℝ] ZeroAtInftyContinuousMap Space Space}
    (hE : ∀ F : H2, (E F : SpatialField) =ᵐ[volume] (F.value : SpatialField))
    (j k : Fin 3) (g : Z) : (dcolX j j c (ιZ g), dT E j k c g) ∈ derivativeGraph k := by
  have e1 : (dcolX j j c (ιZ g), dT E j k c g) =
      ((fc j (xd j) πv c (ιZ g), fc j (zd6 j) (πw k) c g + fc j (zdd j k) πv c g) +
       (fc j x6 (πw j) c (ιZ g), fc j (zinf E) (πy j k) c g + fc j (zd6 k) (πw j) c g)) +
      ((cf j (πw j) x6 c (ιZ g), cf j (πy j k) (zinf E) c g + cf j (πw j) (zd6 k) c g) +
       (cf j πv (xd j) c (ιZ g), cf j (πw k) (zd6 j) c g + cf j πv (zdd j k) c g)) := by
    simp only [dcolX, dT, add_apply, Prod.mk_add_mk]
    congr 1 <;> abel
  have hz := coeFn_zinf E hE g
  rw [e1]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) (Submodule.add_mem _ ?_ ?_)
  · -- `(∂ⱼg)_j U`: `B = P_j.flip`, coefficient `U`, `H¹` factor `∂ⱼg`
    refine graph_of_leibniz (prodJ j).flip k (hc.dv k) (locL2_Linf c.1) (locL2_L3 _)
      (h2FirstToH1 j g.toH2) ?_ ?_
    · filter_upwards [coeFn_fc j (xd j) πv c (ιZ g)] with x hx
      simp only [hx, πv_apply, xd_apply, ιZ_toH1_derivative, h2FirstToH1_value, flip_prodJ_apply,
        prodJ_apply]
    · filter_upwards [Lp.coeFn_add (fc j (zd6 j) (πw k) c g) (fc j (zdd j k) πv c g),
        coeFn_fc j (zd6 j) (πw k) c g, coeFn_fc j (zdd j k) πv c g, coeFn_zd6 j g]
        with x h0 h1 h2 h3
      simp only [h0, Pi.add_apply, h1, h2, h3, πv_apply, πw_apply, zdd_apply, h2FirstToH1_value,
        h2FirstToH1_derivative, flip_prodJ_apply, flip_prodJ_apply, prodJ_apply, prodJ_apply]
  · -- `g_j ∂ⱼU`: `B = P_j.flip`, coefficient `∂ⱼU`, `H¹` factor `g`
    refine graph_of_leibniz (prodJ j).flip k (hc.dw j k) (locL2_L3 _) (locL2_L2 _)
      (ιZ g).toH1 ?_ ?_
    · filter_upwards [coeFn_fc j x6 (πw j) c (ιZ g), coeFn_x6 (ιZ g)] with x hx h6
      simp only [hx, h6, πw_apply, flip_prodJ_apply, prodJ_apply, Xval, Xclass]
    · filter_upwards [Lp.coeFn_add (fc j (zinf E) (πy j k) c g) (fc j (zd6 k) (πw j) c g),
        coeFn_fc j (zinf E) (πy j k) c g, coeFn_fc j (zd6 k) (πw j) c g, coeFn_zd6 k g, hz]
        with x h0 h1 h2 h3 h4
      simp only [h0, Pi.add_apply, h1, h2, h3, h4, πy_apply, πw_apply, ιZ_toH1_value,
        ιZ_toH1_derivative, flip_prodJ_apply, flip_prodJ_apply, prodJ_apply, prodJ_apply]
  · -- `(∂ⱼU)_j g`: `B = P_j`, coefficient `∂ⱼU`, `H¹` factor `g`
    refine graph_of_leibniz (prodJ j) k (hc.dw j k) (locL2_L3 _) (locL2_L2 _)
      (ιZ g).toH1 ?_ ?_
    · filter_upwards [coeFn_cf j (πw j) x6 c (ιZ g), coeFn_x6 (ιZ g)] with x hx h6
      simp only [hx, h6, πw_apply, Xval, Xclass]
    · filter_upwards [Lp.coeFn_add (cf j (πy j k) (zinf E) c g) (cf j (πw j) (zd6 k) c g),
        coeFn_cf j (πy j k) (zinf E) c g, coeFn_cf j (πw j) (zd6 k) c g, coeFn_zd6 k g, hz]
        with x h0 h1 h2 h3 h4
      simp only [h0, Pi.add_apply, h1, h2, h3, h4, πy_apply, πw_apply, ιZ_toH1_value,
        ιZ_toH1_derivative]
  · -- `U_j ∂ⱼg`: `B = P_j`, coefficient `U`, `H¹` factor `∂ⱼg`
    refine graph_of_leibniz (prodJ j) k (hc.dv k) (locL2_Linf c.1) (locL2_L3 _)
      (h2FirstToH1 j g.toH2) ?_ ?_
    · filter_upwards [coeFn_cf j πv (xd j) c (ιZ g)] with x hx
      simp only [hx, πv_apply, xd_apply, ιZ_toH1_derivative, h2FirstToH1_value]
    · filter_upwards [Lp.coeFn_add (cf j (πw k) (zd6 j) c g) (cf j πv (zdd j k) c g),
        coeFn_cf j (πw k) (zd6 j) c g, coeFn_cf j πv (zdd j k) c g, coeFn_zd6 j g]
        with x h0 h1 h2 h3
      simp only [h0, Pi.add_apply, h1, h2, h3, πv_apply, πw_apply, zdd_apply, h2FirstToH1_value,
        h2FirstToH1_derivative]

/-- `(div(U ⊗ g + g ⊗ U), ∂ₖ div(U ⊗ g + g ⊗ U))` is in the weak derivative graph. -/
theorem Gop_GkOp_mem {c : Coef} (hc : IsConsistentCoef c)
    {E : H2 →L[ℝ] ZeroAtInftyContinuousMap Space Space}
    (hE : ∀ F : H2, (E F : SpatialField) =ᵐ[volume] (F.value : SpatialField))
    (k : Fin 3) (g : Z) : (Gop c (ιZ g), GkOp E k c g) ∈ derivativeGraph k := by
  have e : (Gop c (ιZ g), GkOp E k c g) =
      ∑ j : Fin 3, (dcolX j j c (ιZ g), dT E j k c g) := by
    refine Prod.ext ?_ ?_
    · simp only [Gop, sum_apply, Prod.fst_sum]
    · simp only [GkOp, sum_apply, Prod.snd_sum]
  rw [e]
  exact Submodule.sum_mem _ (fun j _ => dcolX_dT_mem hc hE j k g)

end UnforcedLeray.Blueprint.L01
