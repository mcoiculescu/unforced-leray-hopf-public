import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.YoungW2.RawProfileSmooth
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.YoungW2.InletProfileJetsAt
import UnforcedLeray.Cons.L2.BackgroundConcrete.GraphResolventIsContRep
import UnforcedLeray.Units.B0449.GraphResolventRealBound
import UnforcedLeray.Units.B0276

/-!
# `BgCorrYoungJets` from its leaves (source 1515-1531, 2525-2562, 2607-2609)

Source of record: `the November 2 reference manuscript` (73 pages).

Task `PartIII-b:C/ward/12/3/org`.  `BgCorrYoungJets` (`YoungW2/Defs.lean`) bounds the repair
`r_b = p.corr z` of an exact split (`IIb.ExactSplitII`, `z` a solution of the projected equation)
with its first two spatial derivatives at the young points `ϱ ≥ R√ν`.

## The argument

The source proves it by the qualitative bootstrap of 2525-2562 ("No second unstable inverse is
needed for spatial regularity"): with `V = V₀ + E_εα`, `A₀w = f - 𝐏(V·∇w + w·∇V + w·∇w)`;
`∂_jA₀w = (A₀ - ½)∂_jw`, `‖Dw‖²_{Y_{2p}} ≤ C‖w‖_∞‖D²w‖_{Y_p}`, and the rewritten equation
`A₀D_jw = f_j + ½D_jw` with the maximal graph at shift zero give `Dw ∈ X̃_p` (2531-2537); the
induction "if derivatives through order `k` are in the graph, all factors through order `k` are
bounded and derivatives through order `k+2` are in `Y_p`" (2552-2559) gives `D²w` in the graph.
No smallness enters: the bootstrap uses `w ∈ X_p` (`z ∈ p.Z`) and `w ∈ L^∞` (`p = 11/4 > 5/2`,
`bg:supremum-embedding`), not the contraction ball.  The graph elements are bounded with a jointly
continuous representative (`bg:supremum-embedding`, 1515-1531), and 2607-2609 reads the derivatives
of `w` as "their uniform supremum bounds".

In Lean the two source steps are stated on the phase space (`B0411.D` is the maximal graph
`D_p = {u ∈ Y_p : νΔu, T₀u ∈ Y_p}`, `HasPhaseOp (-∂_j)` the distributional derivative), and the
passage to the pointwise derivatives of the representative `p.corr z = contRep (p.wOf z)` uses
the following facts:

* `BgCorrGradGraph` (source 2525-2541): the distributional derivatives `∂_jw` lie in `D_p`;
* `BgCorrHessGraph` (source 2542-2559, the induction step at `k = 1`): the distributional
  derivatives `∂_l∂_jw` lie in `D_p`;
* `BgContRepGraph` (source 1515-1531, `bg:supremum-embedding`, the B0449 continuous chart
  representative): the representative `contRep u` of `u ∈ D_p` is jointly continuous and bounded
  (proved here, `bgContRepGraph`);
* `BgContRepWeakSlice` (the meaning of a distributional derivative, read on the representatives):
  if `∂_ju = g` in `Y_p` with `u, g ∈ D_p`, every phase slice of `contRep u` has the slice of
  `contRep g` as weak `j`-th derivative (`HasWeakSpatialDerivative`);
* `WeakDerivClassicalOn`: on an open set where a field is `C¹`, a continuous weak derivative is the
  classical one;
* proved here: `‖DF‖ ≤ Σ_j |∂_jF|`, `‖D²F‖ ≤ Σ_{j,l} |∂_j∂_lF|` (`bgCorr_normIterOne`,
  `bgCorr_normIterTwo`).

At a young point (off the axis) `r_b(τ, ·) = U(τ, ·) - V(τ, ·)` is `C²` (`IsExactProfile.smoothU`,
the raw lift `C^∞` off the axis by `bgRawProfileSmooth`, the inlet columns `C²` by
`bgInletColumnJets_of bgInletProfileJetsAt`), so its classical partials of order `≤ 2` are the
representatives of the graph derivatives, which are bounded.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace
open UnforcedLeray.Cons.C03.Concrete (Params contRep)

/-! ## 1. The leaves -/

/-- **The first derivatives of the repair lie in the maximal graph** (source 2525-2541: "No second
unstable inverse is needed for spatial regularity. Write `V = V₀ + E_εα` and
`A₀w = f - 𝐏(V·∇w + w·∇V + w·∇w)`. ... Since `∂_jA₀w = (A₀ - 1/2)∂_jw` and
`‖Dw‖²_{Y_{2p}} ≤ C‖w‖_∞‖D²w‖_{Y_p}`, every differentiated term is in `Y_p`. Also `Dw ∈ Y_p` is
already known. Rewrite the differentiated equation as `A₀D_jw = f_j + ½D_jw`, with the entire
right side in `Y_p`, and apply the maximal graph at shift zero. ... Thus `Dw ∈ X̃_p`"; the complete
source `f` is in `W^{k,Y_p}`, 2542-2551): for the growing eigenpair `q = p.mode` there is `ν₀ > 0`
such that at every level of the regime with `ν ≤ ν₀`, every solution `z = (w, A) ∈ p.Z` of the
projected equation has distributional derivatives `∂_jw = g_j` (`HasPhaseOp (-∂_j)`) with
`g_j ∈ D_p = B0411.D P ν q₀` (`p = q₀ = 11/4`).  No bound on `‖z‖_Z` is used: `w ∈ L^∞` follows
from `w ∈ X_p` (`bg:supremum-embedding`, `p > 5/2`). -/
def BgCorrGradGraph : Prop :=
  ∀ (lam : ℂ) (q : UnforcedLeray.Blueprint.Planar.Profile),
    UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      p.mode = q → ∀ z : p.Z, UnforcedLeray.Short.IIb.ProjectedEquation p z →
        ∃ g : Fin 3 → UnforcedLeray.B0411.D p.period p.ν UnforcedLeray.B0412.q0E,
          ∀ j : Fin 3, HasPhaseOp (fun Φ => -dy j Φ) (p.wOf z)
            (g j : Yq p.period UnforcedLeray.B0412.q0E)

/-- **The second derivatives of the repair lie in the maximal graph** (source 2542-2559, the
induction step at `k = 1`: "For any fixed derivative order, the train and inlet complete sources
belong to the corresponding `W^{k,Y_p}`. ... Inductively, if derivatives through order `k` are in
the graph, all factors through order `k` are bounded and derivatives through order `k+2` are in
`Y_p`. In each order-`(k+1)` derivative of `w·∇w`, one factor has order at most `k`. Put it in
`L^∞` and the other in `Y_p`, then apply the maximal graph to the differentiated equation"): in the
situation of `BgCorrGradGraph`, if `∂_jw = g_j ∈ D_p` for every `j`, then `∂_lg_j = h_{jl}` with
`h_{jl} ∈ D_p` for all `j, l`. -/
def BgCorrHessGraph : Prop :=
  ∀ (lam : ℂ) (q : UnforcedLeray.Blueprint.Planar.Profile),
    UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      p.mode = q → ∀ z : p.Z, UnforcedLeray.Short.IIb.ProjectedEquation p z →
      ∀ g : Fin 3 → UnforcedLeray.B0411.D p.period p.ν UnforcedLeray.B0412.q0E,
        (∀ j : Fin 3, HasPhaseOp (fun Φ => -dy j Φ) (p.wOf z)
          (g j : Yq p.period UnforcedLeray.B0412.q0E)) →
        ∃ h : Fin 3 → Fin 3 → UnforcedLeray.B0411.D p.period p.ν UnforcedLeray.B0412.q0E,
          ∀ j l : Fin 3, HasPhaseOp (fun Φ => -dy l Φ)
            (g j : Yq p.period UnforcedLeray.B0412.q0E)
            (h j l : Yq p.period UnforcedLeray.B0412.q0E)

/-- **The representative of a graph element is continuous and bounded** (source 1515-1531,
`bg:supremum-embedding`: for `r > 5/2`, `w ∈ D_r` has a representative continuous in `(τ, y)` with
`‖w‖_{L^∞_{τ,y}} ≤ C_rν^{-3/(2r)}‖w‖_{D_r}`; here `r = q₀ = 11/4`): for `0 < P ≤ 1`, `ν > 0` and
`u ∈ D_{q₀}`, the selected real representative `contRep u` (`Operators.lean`) is jointly continuous
on `ℝ × ℝ³` and bounded. -/
def BgContRepGraph : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ ν : ℝ, 0 < ν →
    ∀ u : UnforcedLeray.B0411.D P ν UnforcedLeray.B0412.q0E,
      Continuous (fun x : ℝ × Space => contRep (u : Yq P UnforcedLeray.B0412.q0E) x.1 x.2) ∧
        ∃ M : ℝ, ∀ (τ : ℝ) (y : Space), ‖contRep (u : Yq P UnforcedLeray.B0412.q0E) τ y‖ ≤ M

/-- **A distributional derivative is the weak derivative of every slice of the representatives**
(the meaning of `∂_ju = g` in `Y_p`, source 1343-1349 and 2531-2537, read on the continuous
representatives of `bg:supremum-embedding`, 1515-1531): for `0 < P ≤ 1`, `ν > 0`, `u, g ∈ D_{q₀}`
with `∂_ju = g` (`HasPhaseOp (-∂_j) u g`: `⟪-∂_jΦ, u⟫ = ⟪Φ, g⟫` for every phase test `Φ`), at
every phase `τ` the field `contRep g(τ, ·)` is the weak `j`-th derivative of `contRep u(τ, ·)`. -/
def BgContRepWeakSlice : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ ν : ℝ, 0 < ν →
    ∀ (u g : UnforcedLeray.B0411.D P ν UnforcedLeray.B0412.q0E) (j : Fin 3),
      HasPhaseOp (fun Φ => -dy j Φ) (u : Yq P UnforcedLeray.B0412.q0E)
        (g : Yq P UnforcedLeray.B0412.q0E) →
      ∀ τ : ℝ, UnforcedLeray.HasWeakSpatialDerivative j
        (contRep (u : Yq P UnforcedLeray.B0412.q0E) τ) (contRep (g : Yq P UnforcedLeray.B0412.q0E) τ)

/-- **A continuous weak derivative is the classical derivative where the field is `C¹`**
(integration by parts against tests supported in `O`, and the fundamental lemma on the open set
`O`): if `g` is continuous and the weak `i`-th derivative of `f`, and `f` is `C¹` on the open set
`O`, then `∂_if = g` on `O`. -/
def WeakDerivClassicalOn : Prop :=
  ∀ (i : Fin 3) (f g : Space → Space) (O : Set Space),
    UnforcedLeray.HasWeakSpatialDerivative i f g → Continuous g → IsOpen O →
      ContDiffOn ℝ 1 f O → ∀ y ∈ O, physPd f i y = g y

/-! ## 2. Elementary facts -/

local instance bgCorr_fact_q0 : Fact (1 ≤ ENNReal.ofReal UnforcedLeray.B0281.q0) :=
  ⟨by norm_num [UnforcedLeray.B0281.q0]⟩

private theorem bgCorr_q0_holder : UnforcedLeray.B0281.q0.HolderConjugate (11 / 7 : ℝ) := by
  rw [UnforcedLeray.B0281.q0_eq]
  exact UnforcedLeray.B0276.holderConjugate

private theorem bgCorr_q0_gt : 5 / 2 < UnforcedLeray.B0281.q0 := by
  norm_num [UnforcedLeray.B0281.q0]

/-- **`BgContRepGraph`** (source 1515-1531): the B0449 continuous chart representative of a graph
element (`graph_globalRealChartRep_isContRep`) is the selected `contRep` (uniqueness of continuous
representatives), and it is uniformly bounded (`exists_globalRealChartRep_uniform_bound`). -/
theorem bgContRepGraph : BgContRepGraph := by
  intro P _ hP1 ν hν u
  have hTime := UnforcedLeray.B0411.hasPhaseOp_T0D u
  have hLap := UnforcedLeray.B0411.hasPhaseOp_nuLapD u
  let F : ℝ → SpatialField := UnforcedLeray.B0449.globalRealChartRep hP1 bgCorr_q0_holder
    bgCorr_q0_gt hν hTime hLap
  have hF : UnforcedLeray.Cons.C03.Concrete.IsContRep (u : Yq P UnforcedLeray.B0412.q0E) F :=
    UnforcedLeray.Cons.C03.Concrete.graph_globalRealChartRep_isContRep hP1 bgCorr_q0_holder
      bgCorr_q0_gt hν hTime hLap
  have hc := UnforcedLeray.Cons.C03.Concrete.contRep_spec ⟨F, hF⟩
  have hEq : (fun x : ℝ × Space => contRep (u : Yq P UnforcedLeray.B0412.q0E) x.1 x.2) =
      fun x => F x.1 x.2 :=
    (Continuous.ae_eq_iff_eq volume hc.1 hF.1).mp (hc.2.trans hF.2.symm)
  obtain ⟨M, -, hM⟩ := UnforcedLeray.B0449.exists_globalRealChartRep_uniform_bound hP1
    bgCorr_q0_holder bgCorr_q0_gt hν hTime hLap
  refine ⟨hc.1, M, fun τ y => ?_⟩
  have h := congrFun hEq (τ, y)
  simp only at h
  rw [h]
  exact hM τ y

/-- A linear map on `ℝ³` is bounded by the sum of its values on the coordinate vectors. -/
theorem bgCorr_norm_clm_le_sum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : Space →L[ℝ] F) : ‖L‖ ≤ ∑ j : Fin 3, ‖L (UnforcedLeray.coordinateVector j)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun v => ?_
  have hv := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v
  simp only [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] at hv
  have hL : L v = ∑ j : Fin 3, v j • L (UnforcedLeray.coordinateVector j) := by
    conv_lhs => rw [← hv]
    simp [map_sum, map_smul, UnforcedLeray.coordinateVector]
  rw [hL, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le v j) (norm_nonneg _)

/-- `‖DF(y)‖ ≤ Σ_j |∂_jF(y)|`. -/
theorem bgCorr_normIterOne (f : Space → Space) (y : Space) :
    ‖iteratedFDeriv ℝ 1 f y‖ ≤ ∑ j : Fin 3, ‖physPd f j y‖ := by
  rw [norm_iteratedFDeriv_one]
  exact bgCorr_norm_clm_le_sum _

/-- `‖D²F(y)‖ ≤ Σ_{j,l} |∂_j∂_lF(y)|` for `F` `C²` near `y` (`∂_j∂_lF(y) = D(DF)(y) e_j e_l`). -/
theorem bgCorr_normIterTwo (f : Space → Space) (y : Space) (hf : ContDiffAt ℝ 2 f y) :
    ‖iteratedFDeriv ℝ 2 f y‖ ≤ ∑ j : Fin 3, ∑ l : Fin 3, ‖physPd2 f j l y‖ := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) y :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have key : ∀ j l : Fin 3, physPd2 f j l y =
      fderiv ℝ (fderiv ℝ f) y (UnforcedLeray.coordinateVector j)
        (UnforcedLeray.coordinateVector l) := by
    intro j l
    have hfd : HasFDerivAt (fun y' => fderiv ℝ f y' (UnforcedLeray.coordinateVector l))
        ((fderiv ℝ f y).comp (0 : Space →L[ℝ] Space) +
          (fderiv ℝ (fderiv ℝ f) y).flip (UnforcedLeray.coordinateVector l)) y :=
      hd.hasFDerivAt.clm_apply (hasFDerivAt_const (UnforcedLeray.coordinateVector l) y)
    simp only [physPd2, physPd]
    rw [hfd.fderiv]
    simp
  have e2 : ‖iteratedFDeriv ℝ 2 f y‖ = ‖fderiv ℝ (fderiv ℝ f) y‖ := by
    show ‖iteratedFDeriv ℝ (1 + 1) f y‖ = _
    rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]
  rw [e2]
  refine (bgCorr_norm_clm_le_sum _).trans (Finset.sum_le_sum fun j _ => ?_)
  refine (bgCorr_norm_clm_le_sum _).trans (le_of_eq (Finset.sum_congr rfl fun l _ => ?_))
  rw [key]

/-- `P = 2εc ≤ 1` once `ν ≤ d₋³/12` (`ε = e^{-d/ν}`, `c = ν⁻²`, `e^x ≥ x³/6`; the argument of
`IIIa.period_le_one_of_small`). -/
theorem bgCorr_period_le_one {p : Params} {d dm dp : ℝ}
    (hreg : UnforcedLeray.Short.IIb.BgRegime p d dm dp) (hν : p.ν ≤ dm ^ 3 / 12) :
    p.period ≤ 1 := by
  have hν0 := p.ν_pos
  have hdm := hreg.dm_pos
  have hd : 0 < d := lt_of_lt_of_le hdm hreg.dm_le
  have hx : 0 ≤ d / p.ν := by positivity
  have he := Real.pow_div_factorial_le_exp (d / p.ν) hx 3
  have h6 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [h6] at he
  have hd3 : dm ^ 3 ≤ d ^ 3 := pow_le_pow_left₀ hdm.le hreg.dm_le 3
  have hνne : p.ν ≠ 0 := hν0.ne'
  have key : (d / p.ν) ^ 3 / 6 * p.ν ^ 2 = d ^ 3 / (6 * p.ν) := by
    field_simp
  have h2 : 2 ≤ d ^ 3 / (6 * p.ν) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hE : 0 < Real.exp (d / p.ν) := Real.exp_pos _
  have hEν : 2 ≤ Real.exp (d / p.ν) * p.ν ^ 2 :=
    calc (2 : ℝ) ≤ d ^ 3 / (6 * p.ν) := h2
      _ = (d / p.ν) ^ 3 / 6 * p.ν ^ 2 := key.symm
      _ ≤ Real.exp (d / p.ν) * p.ν ^ 2 := mul_le_mul_of_nonneg_right he (by positivity)
  unfold Params.period
  rw [hreg.eps_eq, hreg.c_eq, neg_div, Real.exp_neg]
  rw [show 2 * (Real.exp (d / p.ν))⁻¹ * (p.ν ^ 2)⁻¹ = 2 / (Real.exp (d / p.ν) * p.ν ^ 2) by
    rw [mul_assoc, ← mul_inv, ← div_eq_mul_inv]]
  rw [div_le_one (by positivity)]
  exact hEν

/-- Partials agree for fields that agree near the point. -/
theorem bgCorr_physPd_congr_nhds {f₁ f₂ : Space → Space} {y : Space} (h : f₁ =ᶠ[𝓝 y] f₂)
    (j : Fin 3) : physPd f₁ j y = physPd f₂ j y := by
  unfold physPd
  rw [h.fderiv_eq]

/-- The slice of a jointly continuous field is continuous. -/
theorem bgCorr_continuous_slice {F : ℝ → Space → Space}
    (hF : Continuous fun x : ℝ × Space => F x.1 x.2) (τ : ℝ) : Continuous (F τ) :=
  hF.comp (continuous_const.prodMk continuous_id)

/-- **The repair is `C²` off the axis** at every level of the regime with `ν ≤ 1` and `p.mode = q`:
`r_b(τ, ·) = U(τ, ·) - V(τ, ·)` with `U` jointly `C^∞` (`IsExactProfile.smoothU`),
`V = U_raw + Σᵢ αᵢE_i`, `U_raw` `C^∞` off the axis (`bgRawProfileSmooth`, `contDiffOn_Nv_of`),
`E_i` `C²` (`bgInletColumnJets_of bgInletProfileJetsAt`). -/
theorem bgCorr_contDiffOn_offAxis {lam : ℂ} {q : UnforcedLeray.Blueprint.Planar.Profile}
    (hq : UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair lam q) {p : Params} {d dm dp : ℝ}
    (hreg : UnforcedLeray.Short.IIb.BgRegime p d dm dp) (hν : p.ν ≤ 1) (hmode : p.mode = q)
    (z : p.Z) {V : ℝ → SpatialField} {pres : ℝ → Space → ℝ}
    (hV : ∀ τ y, V τ y = p.raw τ y + ∑ i : Fin 2, p.coord z i • p.inlet i τ y)
    (hex : IsExactProfile p.ν p.period (fun τ y => V τ y + p.corr z τ y) pres) (τ : ℝ) :
    ContDiffOn ℝ 2 (p.corr z τ) axisᶜ := by
  have hRaw : ContDiffOn ℝ 2 (p.raw τ) axisᶜ :=
    ((contDiffOn_Nv_of p.R_pos.ne' (bgRawProfileSmooth p d dm dp hreg) τ).of_le
      (by simp)).congr (fun y hy => p.raw_eq_off_axis τ y hy)
  have hInl : ∀ i : Fin 2, ContDiff ℝ 2 (p.inlet i τ) := fun i =>
    (bgInletColumnJets_of bgInletProfileJetsAt lam q hq p d dm dp hreg hν hmode i).1 τ
  have hSum : ContDiff ℝ 2 (fun y => ∑ i : Fin 2, p.coord z i • p.inlet i τ y) :=
    ContDiff.sum fun i _ => (hInl i).const_smul (p.coord z i)
  have hVo : ContDiffOn ℝ 2 (V τ) axisᶜ := by
    have e : V τ = fun y => p.raw τ y + ∑ i : Fin 2, p.coord z i • p.inlet i τ y :=
      funext (hV τ)
    rw [e]
    exact hRaw.add hSum.contDiffOn
  have hU : ContDiff ℝ 2 (fun y => V τ y + p.corr z τ y) := by
    have h := hex.smoothU.comp (contDiff_const.prodMk contDiff_id :
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y' : Space => ((τ, y') : ℝ × Space)))
    exact h.of_le (by simp)
  exact (hU.contDiffOn.sub hVo).congr (fun y _ => by simp)

/-! ## 3. The combination -/

/-- **`BgCorrYoungJets`** from the two graph steps of the bootstrap (`BgCorrGradGraph`,
`BgCorrHessGraph`), the continuous bounded representative of graph elements (`bgContRepGraph`,
proved above), the slice reading of distributional derivatives (`BgContRepWeakSlice`), the classical/weak
identification (`WeakDerivClassicalOn`); the norm bounds by partials are `bgCorr_normIterOne`,
`bgCorr_normIterTwo`. -/
theorem bgCorrYoungJets_of (h1 : BgCorrGradGraph) (h2 : BgCorrHessGraph)
    (h4 : BgContRepWeakSlice) (h5 : WeakDerivClassicalOn) : BgCorrYoungJets := by
  have h3 : BgContRepGraph := bgContRepGraph
  intro lam q hq dm dp hdm
  obtain ⟨ν₁, hν₁, H1⟩ := h1 lam q hq dm dp hdm
  obtain ⟨ν₂, hν₂, H2⟩ := h2 lam q hq dm dp hdm
  refine ⟨min (min ν₁ ν₂) (min 1 (dm ^ 3 / 12)),
    lt_min (lt_min hν₁ hν₂) (lt_min one_pos (by positivity)), ?_⟩
  intro p d ρb S_in V rb pres hreg hν hmode hsplit hex
  have hνa : p.ν ≤ ν₁ := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hνb : p.ν ≤ ν₂ := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hνc : p.ν ≤ 1 := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hνd : p.ν ≤ dm ^ 3 / 12 := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hP1 : p.period ≤ 1 := bgCorr_period_le_one hreg hνd
  obtain ⟨z, hPE, hV, hrb, -⟩ := hsplit.state
  subst hrb
  obtain ⟨g, hg⟩ := H1 p d hreg hνa hmode z hPE
  obtain ⟨h, hh⟩ := H2 p d hreg hνb hmode z hPE g hg
  -- the correction as an element of the maximal graph
  let w0 : UnforcedLeray.B0411.D p.period p.ν UnforcedLeray.B0412.q0E :=
    ⟨p.wOf z, UnforcedLeray.B0412.X_le_D (UnforcedLeray.Cons.C03.Concrete.cw_mem_X z)⟩
  obtain ⟨-, M0, hM0⟩ := h3 p.period hP1 p.ν p.ν_pos w0
  choose hG1c M1 hM1 using fun j => h3 p.period hP1 p.ν p.ν_pos (g j)
  choose hG2c M2 hM2 using fun j l => h3 p.period hP1 p.ν p.ν_pos (h j l)
  have hW1 : ∀ (j : Fin 3) (τ : ℝ), UnforcedLeray.HasWeakSpatialDerivative j (p.corr z τ)
      (contRep (g j : Yq p.period UnforcedLeray.B0412.q0E) τ) :=
    fun j τ => h4 p.period hP1 p.ν p.ν_pos w0 (g j) j (hg j) τ
  have hW2 : ∀ (j l : Fin 3) (τ : ℝ), UnforcedLeray.HasWeakSpatialDerivative l
      (contRep (g j : Yq p.period UnforcedLeray.B0412.q0E) τ)
      (contRep (h j l : Yq p.period UnforcedLeray.B0412.q0E) τ) :=
    fun j l τ => h4 p.period hP1 p.ν p.ν_pos (g j) (h j l) l (hh j l) τ
  have hFs : ∀ τ, ContDiffOn ℝ 2 (p.corr z τ) axisᶜ := fun τ =>
    bgCorr_contDiffOn_offAxis hq hreg hνc hmode z hV hex τ
  have hO : IsOpen (axisᶜ : Set Space) := isOpen_compl_axis
  -- first partials
  have hD1 : ∀ (τ : ℝ) (j : Fin 3), ∀ y ∈ (axisᶜ : Set Space),
      physPd (p.corr z τ) j y = contRep (g j : Yq p.period UnforcedLeray.B0412.q0E) τ y :=
    fun τ j y hy => h5 j (p.corr z τ) _ axisᶜ (hW1 j τ)
      (bgCorr_continuous_slice (hG1c j) τ) hO ((hFs τ).of_le (by norm_num)) y hy
  -- the first partials are `C¹` off the axis
  have hG1C1 : ∀ (τ : ℝ) (l : Fin 3),
      ContDiffOn ℝ 1 (contRep (g l : Yq p.period UnforcedLeray.B0412.q0E) τ) axisᶜ := by
    intro τ l
    have hd : ContDiffOn ℝ 1 (fun y => fderiv ℝ (p.corr z τ) y) axisᶜ :=
      (hFs τ).fderiv_of_isOpen hO (by norm_num)
    have hd' : ContDiffOn ℝ 1 (fun y => physPd (p.corr z τ) l y) axisᶜ :=
      hd.clm_apply contDiffOn_const
    exact hd'.congr (fun y hy => (hD1 τ l y hy).symm)
  -- second partials
  have hD2 : ∀ (τ : ℝ) (j l : Fin 3), ∀ y ∈ (axisᶜ : Set Space),
      physPd2 (p.corr z τ) j l y = contRep (h l j : Yq p.period UnforcedLeray.B0412.q0E) τ y := by
    intro τ j l y hy
    have hev : (fun y' => physPd (p.corr z τ) l y') =ᶠ[𝓝 y]
        contRep (g l : Yq p.period UnforcedLeray.B0412.q0E) τ :=
      Filter.eventuallyEq_of_mem (hO.mem_nhds hy) (fun y' hy' => hD1 τ l y' hy')
    have e1 : physPd2 (p.corr z τ) j l y =
        physPd (contRep (g l : Yq p.period UnforcedLeray.B0412.q0E) τ) j y :=
      bgCorr_physPd_congr_nhds hev j
    rw [e1]
    exact h5 j _ _ axisᶜ (hW2 l j τ) (bgCorr_continuous_slice (hG2c l j) τ) hO (hG1C1 τ l) y hy
  -- the bounds are nonnegative
  have hM1n : ∀ j, 0 ≤ M1 j := fun j => (norm_nonneg _).trans (hM1 j 0 0)
  have hM2n : ∀ j l, 0 ≤ M2 j l := fun j l => (norm_nonneg _).trans (hM2 j l 0 0)
  have hS1 : 0 ≤ ∑ j : Fin 3, M1 j := Finset.sum_nonneg fun j _ => hM1n j
  have hS2 : 0 ≤ ∑ j : Fin 3, ∑ l : Fin 3, M2 l j :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun l _ => hM2n l j
  have hM0n : 0 ≤ M0 := (norm_nonneg _).trans (hM0 0 0)
  refine ⟨M0 + ∑ j : Fin 3, M1 j + ∑ j : Fin 3, ∑ l : Fin 3, M2 l j,
    fun τ y hy n hn => ?_⟩
  have hyax : y ∈ (axisᶜ : Set Space) := young_not_mem_axis p.R_pos p.ν_pos hy
  interval_cases n
  · rw [norm_iteratedFDeriv_zero]
    have := hM0 τ y
    change ‖p.corr z τ y‖ ≤ M0 at this
    linarith
  · have hb : ∑ j : Fin 3, ‖physPd (p.corr z τ) j y‖ ≤ ∑ j : Fin 3, M1 j := by
      refine Finset.sum_le_sum fun j _ => ?_
      rw [hD1 τ j y hyax]
      exact hM1 j τ y
    have := (bgCorr_normIterOne (p.corr z τ) y).trans hb
    linarith
  · have hC2 : ContDiffAt ℝ 2 (p.corr z τ) y := (hFs τ).contDiffAt (hO.mem_nhds hyax)
    have hb : ∑ j : Fin 3, ∑ l : Fin 3, ‖physPd2 (p.corr z τ) j l y‖ ≤
        ∑ j : Fin 3, ∑ l : Fin 3, M2 l j := by
      refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ => ?_
      rw [hD2 τ j l y hyax]
      exact hM2 l j τ y
    have := (bgCorr_normIterTwo (p.corr z τ) y hC2).trans hb
    linarith

#print axioms bgCorrYoungJets_of

end UnforcedLeray.Short.PartIIIb.Concrete
