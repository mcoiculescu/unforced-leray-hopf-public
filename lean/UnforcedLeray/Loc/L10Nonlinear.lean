import UnforcedLeray.Loc.L10Nonlinear.Multiplier

/-!
# Step L10 `NonlinearStep`: `𝓝`, `𝓒(K_loc,·)`, `G_*` and their bounds (lines 462–491)

`paper/main.tex` lines 462–491 (`loc:eq:force-bound`), with the bounds used at lines 504–505;
blueprint units B0721 (`unlabeled:463`, the operators) and B0722 (`loc:eq:force-bound`); the
step is `UnforcedLeray.Blueprint.NonlinearStep` (`Blueprint/Localization/Nonlinear.lean`,
line 124).

## What is proved here

For every package `D` and every datum `u₀` with `IsCompactDatum D u₀` we build
`𝓝 : Z × Z → X`, `𝓒(K_loc(τ),·) : Z → X` and `G_*(τ) ∈ X` with the literal weak `-𝔓 div`
characterizations of `IsNonlinearMaps`:

* `𝓒(K,·)` (lines 465, 504–505) is proved outright. By `loc:eq:heat-correction`
  (`IsCompactDatum.tail_bound`), `K_loc(τ)` is smooth with `|K|, |DK|, |D²K| ≤ Ce^{τ/2}`; the
  Leibniz rule for weak derivatives (`L10Nonlinear/WeakProduct.lean`) puts the columns of
  `K ⊗ g + g ⊗ K` in `H²` with norm `≤ 13‖B‖Ce^{τ/2}‖g‖_{H²}`, and the compiled `h1Projection`
  gives `-𝔓 div(K ⊗ g + g ⊗ K) ∈ X` (`L10Nonlinear/Pairing.lean`). This is the operator
  `mulOp` of `L10Nonlinear/Multiplier.lean`, and `‖𝓒(K(τ),·)‖ ≤ mulConst · C e^{τ/2}`.
* The `r_heat` part of `G_*` (lines 473–474): `U_* = H_h[u_dss] + r_heat` (line 167), and
  `-𝔓 div(r_heat ⊗ K + K ⊗ r_heat) = mulOp K (r_heat)` has norm
  `≤ mulConst · C e^{τ/2} sup ‖r_heat‖_{H²}` (`r_heat` is continuous and periodic, hence bounded).
* The algebra: `G_* = G_res + mulOp K(r_heat)`, the column identity
  `U ⊗ K + K ⊗ U + K ⊗ K = (H ⊗ K + K ⊗ H + K ⊗ K) + (r ⊗ K + K ⊗ r)` a.e., the bilinearity
  and boundedness of `𝓝` from the column bound, continuity of `𝓒(K(τ),·)` and `G_*` in `τ`.

## What is assumed (`nonlinearStep_of`)

Three named hypotheses, each a precise theorem not available in the library:

* `H2ProductBound`: the `H²(ℝ³)` algebra (line 504, "the `H²` product bound"), used for `𝓝`.
  It needs `H² ⊂ L^∞` in three dimensions (Morrey or Fourier), which the library lacks.
* `HeatTailW2Continuous`: `τ ↦ K_loc(τ)` is continuous into `W^{2,∞}` on `τ ≤ 0`. The
  manuscript does not state it; it is the continuity needed for `G_*` and `𝓒(K,·)` to be
  continuous (blueprint note on B0722: "Continuity of `G_*` in `H¹` in `τ` ... is implicit").
* `ResidualForce`: the physical-residual estimate of lines 476–491 for
  `-𝔓 div(H ⊗ K + K ⊗ H + K ⊗ K)`, `H = H_h[u_dss]`, in similarity variables, with its
  continuity in `τ`. It needs pointwise Gaussian estimates for heat flows of `|x|⁻¹` data
  (INF04, INF22), which the library lacks.

Main declarations: `H2ProductBound`, `HeatTailW2Continuous`, `ResidualForce`,
`nonlinearStep_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Blueprint.L10

open SobolevGraph

/-! ## The missing theorems -/

/-- **Missing theorem: the `H²(ℝ³)` algebra** (`paper/main.tex` line 504, "the `H²` product
bound"; blueprint B1021, INF11). There is `C` such that for all `f, g ∈ H²(ℝ³;ℝ³)` and every
`j`, the field `g_j f` (column `j` of `f ⊗ g`, line 107) is in `H²` with
`‖g_j f‖_{H²} ≤ C ‖f‖_{H²} ‖g‖_{H²}`. Standard (via `H² ⊂ L^∞` and `H¹ ⊂ L⁴` in three
dimensions and the Leibniz rule for products of Sobolev functions); used only for `𝓝`. -/
def H2ProductBound : Prop :=
  ∃ C : ℝ, ∀ (f g : H2) (j : Fin 3), ∃ P : H2,
    (P.value : SpatialField) =ᵐ[volume]
      tensorColumns (f.value : SpatialField) (g.value : SpatialField) j ∧
    ‖P‖ ≤ C * ‖f‖ * ‖g‖

/-- **Missing theorem: the heat tail is continuous into `W^{2,∞}`** (blueprint B0720, B0722;
`paper/main.tex` lines 446–461). For a package `D` and a datum `u₀` satisfying
`IsCompactDatum D u₀`, the profile `K_loc(τ) = H_h[u₀ - u_dss](τ)` depends continuously on
`τ ≤ 0` in the sup norms of the field and its first two derivatives. True because
`d_loc = u₀ - u_dss` is smooth with `|D^k d_loc| ≤ C⟨x⟩^{-1-k}` (`k ≤ 4`, line 155, and
`d_loc = 0` near `0`), so that `∂_τ K = hΔK + ½ y·∇K + ½ K` is bounded in `W^{2,∞}` locally
uniformly in `τ`. -/
def HeatTailW2Continuous : Prop :=
  ∀ D : BackgroundData, IsUnstableBackground D → ∀ u₀ : SpatialField, IsCompactDatum D u₀ →
    ∀ τ : ℝ, τ ≤ 0 → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ τ' : ℝ, τ' ≤ 0 → |τ' - τ| < δ →
      ∀ y : Space,
        ‖heatTail D u₀ τ' y - heatTail D u₀ τ y‖ ≤ ε ∧
        ‖fderiv ℝ (heatTail D u₀ τ') y - fderiv ℝ (heatTail D u₀ τ) y‖ ≤ ε ∧
        ‖iteratedFDeriv ℝ 2 (heatTail D u₀ τ') y - iteratedFDeriv ℝ 2 (heatTail D u₀ τ) y‖ ≤ ε

/-- **Missing theorem: the physical residual** (`paper/main.tex` lines 474–491, blueprint
B0722 ingredient (2); INF04, INF22, INF27). With `H = H_h[u_dss]` (line 160) and
`K = K_loc` (line 446), the field `G_res(τ) = -𝔓 div(H ⊗ K + K ⊗ H + K ⊗ K)(τ)` (the
similarity form `t^{3/2} F_loc(√t y, t)` of the manuscript's `F_loc`) exists in `X = H¹_div`
for `τ ≤ 0`, depends continuously on `τ ≤ 0`, and `‖G_res(τ)‖_{H¹} ≤ C e^{τ/2}`. The manuscript
gives the stronger `L²` and gradient bounds `Ct^{3/4}`, `Ct^{5/4}`, `t = e^τ`; continuity in
`τ` is implicit there (blueprint note on B0722). -/
def ResidualForce : Prop :=
  ∀ D : BackgroundData, IsUnstableBackground D → ∀ u₀ : SpatialField, IsCompactDatum D u₀ →
    ∃ (Gres : ℝ → X) (C : ℝ), ContinuousOn Gres (Iic 0) ∧ ∀ τ : ℝ, τ ≤ 0 →
      IsMinusLerayDiv
        (addColumns (symTensorColumns (heatProfile D.h D.udss τ) (heatTail D u₀ τ))
          (tensorColumns (heatTail D u₀ τ) (heatTail D u₀ τ)))
        (Xclass (Gres τ)) ∧
      ‖Gres τ‖ ≤ C * Real.exp ((1 / 2) * τ)

/-! ## `𝓝` from the product bound -/

theorem Zval_add_ae (f f' : Z) : Zval (f + f') =ᵐ[volume] fun z => Zval f z + Zval f' z := by
  have e : Zclass (f + f') = Zclass f + Zclass f' := Zclass_add f f'
  unfold Zval
  rw [e]
  exact Lp.coeFn_add _ _

theorem Zval_smul_ae (a : ℝ) (f : Z) : Zval (a • f) =ᵐ[volume] fun z => a • Zval f z := by
  have e : Zclass (a • f) = a • Zclass f := Zclass_smul a f
  unfold Zval
  rw [e]
  exact Lp.coeFn_smul _ _

/-- `𝓝(f,g) = -𝔓 div(f ⊗ g)` as a bounded bilinear map `Z × Z → X` (lines 464–465). -/
theorem exists_N (hA : H2ProductBound) :
    ∃ N : Z →L[ℝ] Z →L[ℝ] X,
      ∀ f g : Z, IsMinusLerayDiv (tensorColumns (Zval f) (Zval g)) (Xclass (N f g)) := by
  obtain ⟨CN, hCN⟩ := hA
  refine exists_clm₂ (fun f g : Z => tensorColumns (Zval f) (Zval g)) ?_ ?_ ?_ ?_
    (C := 3 * max CN 0) (mul_nonneg (by norm_num) (le_max_right _ _)) ?_
  · intro f f' g j
    filter_upwards [Zval_add_ae f f'] with z hz
    simp only [tensorColumns, hz, smul_add]
  · intro a f g j
    filter_upwards [Zval_smul_ae a f] with z hz
    simp only [tensorColumns, hz]
    rw [smul_comm]
  · intro f g g' j
    filter_upwards [Zval_add_ae g g'] with z hz
    simp only [tensorColumns, hz, PiLp.add_apply, add_smul]
  · intro a f g j
    filter_upwards [Zval_smul_ae a g] with z hz
    simp only [tensorColumns, hz, PiLp.smul_apply, smul_eq_mul, mul_smul]
  · intro f g
    choose P hP hPn using fun j => hCN f.toH2 g.toH2 j
    refine ⟨minusLerayDivX P, isMinusLerayDiv_minusLerayDivX P _ hP, ?_⟩
    have hb : ∀ j, ‖P j‖ ≤ max CN 0 * ‖f‖ * ‖g‖ := by
      intro j
      refine (hPn j).trans ?_
      rw [norm_toH2, norm_toH2]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (norm_nonneg _)) (norm_nonneg _)
    calc ‖minusLerayDivX P‖ ≤ ∑ j : Fin 3, ‖P j‖ := norm_minusLerayDivX_le P
      _ ≤ ∑ _j : Fin 3, max CN 0 * ‖f‖ * ‖g‖ := Finset.sum_le_sum fun j _ => hb j
      _ = 3 * max CN 0 * ‖f‖ * ‖g‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-! ## The step -/

/-- The package fields of the heat tail: `K_loc(τ)` is `W^{2,∞}` with bound `Ce^{τ/2}`. -/
theorem heatTail_isW2Bounded {D : BackgroundData} {u₀ : SpatialField} (hu : IsCompactDatum D u₀)
    {C : ℝ} (hC : ∀ τ : ℝ, τ ≤ 0 → ∀ y : Space,
      ‖heatTail D u₀ τ y‖ ≤ C * Real.exp ((1 / 2) * τ) ∧
      ‖fderiv ℝ (heatTail D u₀ τ) y‖ ≤ C * Real.exp ((1 / 2) * τ) ∧
      ‖iteratedFDeriv ℝ 2 (heatTail D u₀ τ) y‖ ≤ C * Real.exp ((1 / 2) * τ))
    {τ : ℝ} (hτ : τ ≤ 0) : IsW2Bounded (heatTail D u₀ τ) (C * Real.exp ((1 / 2) * τ)) :=
  ⟨hu.tail_smooth τ, hC τ hτ⟩

/-- Continuity of `τ ↦ -𝔓 div(K_loc(τ) ⊗ · + · ⊗ K_loc(τ))` in operator norm on `τ ≤ 0`. -/
theorem continuousOn_mulOp_heatTail (hT : HeatTailW2Continuous) {D : BackgroundData}
    (hD : IsUnstableBackground D) {u₀ : SpatialField} (hu : IsCompactDatum D u₀) :
    ContinuousOn (fun τ => mulOp (heatTail D u₀ τ)) (Iic 0) := by
  obtain ⟨Ct, hCt⟩ := hu.tail_bound
  refine (Metric.continuousOn_iff (β := H2 →L[ℝ] X)
    (f := fun τ => mulOp (heatTail D u₀ τ)) (s := Iic 0)).mpr fun τ hτ ε hε => ?_
  have hc0 := mulConst_nonneg
  obtain ⟨δ, hδ, hδ'⟩ := hT D hD u₀ hu τ hτ (ε / (2 * (mulConst + 1))) (by positivity)
  refine ⟨δ, hδ, fun τ' hτ' hd => ?_⟩
  refine lt_of_eq_of_lt (dist_eq_norm (mulOp (heatTail D u₀ τ')) (mulOp (heatTail D u₀ τ))) ?_
  have hsub := isW2Bounded_sub (hu.tail_smooth τ') (hu.tail_smooth τ)
    (hδ' τ' hτ' (by rwa [Real.dist_eq] at hd))
  rw [mulOp_sub (heatTail_isW2Bounded hu hCt hτ') (heatTail_isW2Bounded hu hCt hτ) hsub]
  calc ‖mulOp (fun y => heatTail D u₀ τ' y - heatTail D u₀ τ y)‖
      ≤ mulConst * (ε / (2 * (mulConst + 1))) := norm_mulOp_le hsub
    _ < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [mul_nonneg hc0 hε.le]

/-- **Step L10, conditional form.** From the `H²` algebra, the `W^{2,∞}` continuity of the
heat tail and the physical-residual estimate, `NonlinearStep` holds (`paper/main.tex`
lines 462–491, blueprint B0721, B0722). Everything else is proved: the `W^{2,∞}`
multiplier bound for `𝓒(K_loc,·)`, the `r_heat` part of `G_*`, the algebra and the
continuity. -/
theorem nonlinearStep_of (hA : H2ProductBound) (hT : HeatTailW2Continuous)
    (hR : ResidualForce) : NonlinearStep := by
  intro D hD u₀ hu
  obtain ⟨Ct, hCt⟩ := hu.tail_bound
  have hW : ∀ {τ : ℝ}, τ ≤ 0 → IsW2Bounded (heatTail D u₀ τ) (Ct * Real.exp ((1 / 2) * τ)) :=
    fun hτ => heatTail_isW2Bounded hu hCt hτ
  have hTc := continuousOn_mulOp_heatTail hT hD hu
  obtain ⟨N, hN⟩ := exists_N hA
  obtain ⟨Gres, Cr, hGc, hG⟩ := hR D hD u₀ hu
  have hB := hD.background
  obtain ⟨R, hRb⟩ : ∃ R : ℝ, ∀ τ : ℝ, ‖D.rheat τ‖ ≤ R := by
    have hbd := hB.rheat_periodic.isBounded_of_continuous hB.period_pos.ne' hB.rheat_continuous
    obtain ⟨R, hRr⟩ := isBounded_iff_forall_norm_le.mp hbd
    exact ⟨R, fun τ => hRr _ (Set.mem_range_self τ)⟩
  refine ⟨⟨N, fun τ => -((mulOp (heatTail D u₀ τ)).comp Zincl),
    fun τ => Gres τ + mulOp (heatTail D u₀ τ) (D.rheat τ)⟩, ?_⟩
  refine ⟨hN, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `CK_weak`
    intro τ hτ g
    have h := mulOp_spec (hW hτ) (Zincl g)
    simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply, Xclass_neg,
      neg_neg]
    exact h
  · -- `Gstar_weak`
    intro τ hτ
    have h := IsMinusLerayDiv.add (hG τ hτ).1 (mulOp_spec (hW hτ) (D.rheat τ))
    show IsMinusLerayDiv _ (Xclass (Gres τ + mulOp (heatTail D u₀ τ) (D.rheat τ)))
    rw [Xclass_add]
    refine IsMinusLerayDiv.congr h (fun j => ?_)
    filter_upwards [hB.Ustar_decomposition τ] with y hy
    simp only [addColumns, symTensorColumns, tensorColumns, Pi.add_apply]
    rw [hy]
    simp only [PiLp.add_apply, smul_add, add_smul]
    abel
  · -- `CK_continuous`
    exact (hTc.clm_comp continuousOn_const).neg
  · -- `Gstar_continuous`
    exact hGc.add (hTc.clm_apply hB.rheat_continuous.continuousOn)
  · -- `force_bound`
    refine ⟨Cr + mulConst * Ct * R, fun τ hτ => ?_⟩
    have h1 := (hG τ hτ).2
    have h2 := norm_mulOp_le (hW hτ)
    have h3 : ‖mulOp (heatTail D u₀ τ) (D.rheat τ)‖ ≤
        mulConst * (Ct * Real.exp ((1 / 2) * τ)) * R :=
      ((mulOp (heatTail D u₀ τ)).le_opNorm _).trans
        (mul_le_mul h2 (hRb τ) (norm_nonneg _)
          ((norm_nonneg (mulOp (heatTail D u₀ τ))).trans h2))
    show ‖Gres τ + mulOp (heatTail D u₀ τ) (D.rheat τ)‖ ≤ _
    calc ‖Gres τ + mulOp (heatTail D u₀ τ) (D.rheat τ)‖
        ≤ ‖Gres τ‖ + ‖mulOp (heatTail D u₀ τ) (D.rheat τ)‖ := norm_add_le _ _
      _ ≤ Cr * Real.exp ((1 / 2) * τ) + mulConst * (Ct * Real.exp ((1 / 2) * τ)) * R :=
        add_le_add h1 h3
      _ = (Cr + mulConst * Ct * R) * Real.exp ((1 / 2) * τ) := by ring
  · -- `CK_bound`
    refine ⟨mulConst * Ct, fun τ hτ => ?_⟩
    show ‖-((mulOp (heatTail D u₀ τ)).comp Zincl)‖ ≤ _
    rw [norm_neg]
    calc ‖(mulOp (heatTail D u₀ τ)).comp Zincl‖
        ≤ ‖mulOp (heatTail D u₀ τ)‖ * ‖Zincl‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ mulConst * (Ct * Real.exp ((1 / 2) * τ)) * 1 :=
        mul_le_mul (norm_mulOp_le (hW hτ)) (Submodule.norm_subtypeL_le Zsub) (norm_nonneg Zincl)
          ((norm_nonneg (mulOp (heatTail D u₀ τ))).trans (norm_mulOp_le (hW hτ)))
      _ = mulConst * Ct * Real.exp ((1 / 2) * τ) := by ring

/-! Axiom audit (expected `[propext, Classical.choice, Quot.sound]`). -/
#print axioms nonlinearStep_of

end UnforcedLeray.Blueprint.L10
