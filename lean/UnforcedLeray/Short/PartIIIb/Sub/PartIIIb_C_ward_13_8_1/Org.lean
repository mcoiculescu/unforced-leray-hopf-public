import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_8_1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.PresY2.L9
import UnforcedLeray.Lib.HeatR3.SimEquation
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Module

/-!
# `D₀U ∈ L²` at the ball levels from the heat remainder (task `PartIII-b:C/ward/13/8/1/1/org`)

Source of record: `the November 2 reference manuscript` (73 pages).

`BgDmuMemL2` (`Sub/PartIII-b_C_ward_13_8_1.lean`) asks, at the levels of the contraction-ball
background, that `D₀U(τ) ∈ L²(ℝ³)` for `U = V + r_b`.  The source argument (2584-2585,
2610-2635):

* the background of `short-bg:result` has a datum `a` and a heat remainder
  `Q = U − H_a ∈ C_per H²` (2563-2633): `BgBallRemainder`;
* `Q` solves `A₀Q = −𝐏 div 𝕋`, `𝕋 = U ⊗ U ∈ C_per H²`, and
  `(∂_τ − y·∇/2)Q = νΔQ + Q/2 − 𝐏 div 𝕋 ∈ C_per L²` (2612-2632), i.e. `D₀Q = −𝐏 div 𝕋` with
  `div 𝕋 = U·∇U`: `BgRemainderEvol`;
* `H_a` is a free solution, `D₀H_a = 0` (2584-2585, 2614-2617, 4140-4141): `HeatProfileDmuZero`,
  proved here (`heatProfileDmuZero_proved`) from `Heat.simHeat_equation`.

Hence `D₀U = D₀(U − H_a) + D₀H_a = −𝐏(U·∇U) ∈ L²` wherever `U·∇U ∈ L²`, which holds at every
phase by `BgUL4` (2607-2612) and `prodL2OfL4_proved`: `bgDmuMemL2_of_org`.  The route does not use
the pressure (`BgPresLeray` is derived from `BgDmuL2Sol`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (Params)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. The three source facts -/

/-- **The datum and heat remainder of the ball background** (source 2563-2643; `short-bg:raw-heat`
at 2601; 2610-2633 "`Q = U − H_a ∈ X_p` ... Thus `Q ∈ C_per H²`"; the ball 2505-2524): at the
ball levels, the exact background `U = V + r_b` has a datum `a` and a heat remainder `Q` with the
clauses of Theorem B3 (`Blueprint.IsB3Core`): `a` nonzero, solenoidal, smooth off `0`, DSS with
factor `e^{P/2}`, `|D^k a(x)| ≤ C|x|^{-1-k}` (`k ≤ 4`), axisymmetric without swirl (2563-2583);
`U` periodic, solenoidal, symmetric, with bounded `U, ∇U` (2519-2541); `Q(τ) = U(τ) − H_ν[a](τ)`
a.e., `Q ∈ C_per H²` (2584-2633).  This is `IIb.BackgroundOutput` at the ball state: the source
builds the datum and the heat remainder for the state `z` of `short-bg:result` (2519-2524, 2601),
which is the state of the ball split (`IsBallSplit`, `isBallSplit_bgField`), whereas
`IIb.BackgroundOutput` only provides some state.  (The Part II-b statements `datum_facts`,
`heat_remainder_H2` of PartII-b:B2, B3, at the ball state.) -/
def BgBallRemainder : Prop :=
  AtBallLevels fun p V rb _ => ∃ (a : SpatialField) (Q : ℝ → UnforcedLeray.SobolevGraph.H2),
    UnforcedLeray.Blueprint.IsB3Core p.ν p.period a (fun t y => V t y + rb t y) Q

/-- **The evolution identity of the heat remainder** (source 2610-2632: `𝕋 = U ⊗ U ∈ C_per H²`,
"`Q = U − H_a ∈ X_p` solves `A₀Q = −𝐏 div 𝕋`", "`(∂_τ − y·∇/2)Q = νΔQ + Q/2 − 𝐏 div 𝕋 ∈
C_per L²`"; 2521-2522, the projected equation `A₀U + 𝐏(U·∇U) = 0` with zero residual): at the
ball levels, for every datum `a` and remainder `Q` with the B3 clauses, the smooth representative
`U − H_ν[a]` of `Q` (`IsB3Core.remainder`) satisfies, at every phase where `U·∇U ∈ L²`,
`D₀(U − H_ν[a]) = −𝐏(U·∇U)` a.e., `D₀ = ∂_τ − ½y·∇ − νΔ − ½` (`physDmu ν 0`, 4140-4141).  This
is the source identity rearranged, `D₀Q = (∂_τ − y·∇/2)Q − νΔQ − Q/2 = −𝐏 div 𝕋`, with
`div 𝕋 = div(U ⊗ U) = U·∇U` since `div U = 0` (`(div T)_i = ∂_jT_ij`, 117); `𝐏` is the `L²` Leray
projection. -/
def BgRemainderEvol : Prop :=
  AtBallLevels fun p V rb _ => ∀ (a : SpatialField) (Q : ℝ → UnforcedLeray.SobolevGraph.H2),
    UnforcedLeray.Blueprint.IsB3Core p.ν p.period a (fun t y => V t y + rb t y) Q → ∀ τ : ℝ,
    MemLp (fun y => fderiv ℝ (fun y' => V τ y' + rb τ y') y (V τ y + rb τ y)) 2 volume →
      physDmu p.ν 0 (fun t y => V t y + rb t y - UnforcedLeray.Blueprint.heatProfile p.ν a t y) τ
        =ᵐ[volume]
        ⇑(-(UnforcedLeray.Leray.projection (UnforcedLeray.toL2
            (fun y => fderiv ℝ (fun y' => V τ y' + rb τ y') y (V τ y + rb τ y)))))

/-- **The heat profile is a free solution** (source 2584-2585: `a_τ(y) = e^{τ/2}a(e^{τ/2}y)`,
`H_a(τ) = e^{νΔ}a_τ`; 2614-2617 the free semigroup, so `A₀H_a = 0` and `D₀H_a = 0`; 159-163 the
profile `H_h[u](y, τ) = e^{τ/2}[e^{he^τΔ}u](e^{τ/2}y)`; 4140-4141 `D_μ`): for `ν > 0` and `a` in
the inverse-distance class `𝒦₂(C)` (`Heat.InvDistClass 2 C a`: `C²` off `0`,
`|D^ja(x)| ≤ C|x|^{-1-j}` for `j ≤ 2`, the bounds of the datum, 2575-2577), `H = heatProfile ν a`
is `C²` in `y` and differentiable in `τ`, and `D₀H = 0` at every `(τ, y)` (no singular set: the
heat time `νe^τ` is positive). -/
def HeatProfileDmuZero : Prop :=
  ∀ (ν C : ℝ) (a : SpatialField), 0 < ν → UnforcedLeray.Heat.InvDistClass 2 C a →
    (∀ τ : ℝ, ContDiff ℝ 2 (UnforcedLeray.Blueprint.heatProfile ν a τ)) ∧
    (∀ (τ : ℝ) (y : Space),
      DifferentiableAt ℝ (fun t => UnforcedLeray.Blueprint.heatProfile ν a t y) τ) ∧
    ∀ (τ : ℝ) (y : Space), physDmu ν 0 (UnforcedLeray.Blueprint.heatProfile ν a) τ y = 0

/-! ## 2. Calculus helpers (namespace `Ward1381Org`, specific to this file) -/

namespace Ward1381Org

/-- For `f ∈ C²`, the physical Laplacian is the iterated-derivative Laplacian `Heat.vlap`. -/
theorem physLap_eq_vlap (f : Space → Space) (hf : ContDiff ℝ 2 f) (y : Space) :
    physLap f y = UnforcedLeray.Heat.vlap f y := by
  unfold physLap physPd2 physPd UnforcedLeray.Heat.vlap
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hc : DifferentiableAt ℝ (fderiv ℝ f) y :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) y
  rw [fderiv_clm_apply hc (differentiableAt_const (coordinateVector j))]
  simp

/-- `Heat.vlap` of a difference of `C²` fields. -/
theorem vlap_sub' (f g : Space → Space) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (y : Space) :
    UnforcedLeray.Heat.vlap (fun x => f x - g x) y =
      UnforcedLeray.Heat.vlap f y - UnforcedLeray.Heat.vlap g y := by
  unfold UnforcedLeray.Heat.vlap
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (fun x => f x - g x) = f - g from rfl,
    iteratedFDeriv_sub_apply hf.contDiffAt hg.contDiffAt]
  rfl

/-- `D_μ` of a difference, for fields differentiable in the phase and `C²` in space. -/
theorem physDmu_sub (ν μ : ℝ) (X Y : ℝ → Space → Space) (τ : ℝ) (y : Space)
    (hXt : DifferentiableAt ℝ (fun t => X t y) τ) (hYt : DifferentiableAt ℝ (fun t => Y t y) τ)
    (hXs : ContDiff ℝ 2 (X τ)) (hYs : ContDiff ℝ 2 (Y τ)) :
    physDmu ν μ (fun t y => X t y - Y t y) τ y = physDmu ν μ X τ y - physDmu ν μ Y τ y := by
  have hXd : DifferentiableAt ℝ (X τ) y := (hXs.differentiable (by norm_num)) y
  have hYd : DifferentiableAt ℝ (Y τ) y := (hYs.differentiable (by norm_num)) y
  have hsub : ContDiff ℝ 2 (fun x => X τ x - Y τ x) := hXs.sub hYs
  have hL : physLap (fun x => X τ x - Y τ x) y = physLap (X τ) y - physLap (Y τ) y := by
    rw [physLap_eq_vlap _ hsub, physLap_eq_vlap _ hXs, physLap_eq_vlap _ hYs,
      vlap_sub' _ _ hXs hYs]
  unfold physDmu
  beta_reduce
  rw [deriv_fun_sub hXt hYt, fderiv_fun_sub hXd hYd, hL]
  simp only [FunLike.coe_sub, Pi.sub_apply]
  module

/-- The datum of the B3 clauses is in the inverse-distance class `𝒦₂` (2575-2577). -/
theorem invDist_of_core {ν P : ℝ} {a : SpatialField} {U : ℝ → SpatialField}
    {Q : ℝ → UnforcedLeray.SobolevGraph.H2} (h : UnforcedLeray.Blueprint.IsB3Core ν P a U Q) :
    ∃ C : ℝ, UnforcedLeray.Heat.InvDistClass 2 C a := by
  obtain ⟨C0, h0⟩ := h.datum_bounds 0 (by norm_num)
  obtain ⟨C1, h1⟩ := h.datum_bounds 1 (by norm_num)
  obtain ⟨C2, h2⟩ := h.datum_bounds 2 (by norm_num)
  refine ⟨max C0 (max C1 C2), ⟨h.datum_smooth.of_le (by first | exact le_top | simp), ?_⟩⟩
  intro j hj x hx
  have hx' : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have key : ‖iteratedFDeriv ℝ j a x‖ * ‖x‖ ^ (j + 1) ≤ max C0 (max C1 C2) := by
    interval_cases j
    · exact (h0 x hx).trans (le_max_left _ _)
    · exact (h1 x hx).trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact (h2 x hx).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hp : (0 : ℝ) < ‖x‖ ^ (j + 1) := pow_pos hx' _
  have hr : ‖x‖ ^ (-(1 + j : ℝ)) = (‖x‖ ^ (j + 1))⁻¹ := by
    rw [Real.rpow_neg hx'.le, show (1 + (j : ℝ)) = ((j + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
  rw [hr, ← div_eq_mul_inv, le_div_iff₀ hp]
  exact key

end Ward1381Org

/-! ## 3. `D₀H_a = 0` -/

/-- **`HeatProfileDmuZero`**, from the similarity heat equation `Heat.simHeat_equation`
(`∂_τH = νΔH + ½DH·y + ½H`) and `Heat.simHeat_contDiff`. -/
theorem heatProfileDmuZero_proved : HeatProfileDmuZero := by
  intro ν C a hν ha
  have hfun : UnforcedLeray.Blueprint.heatProfile ν a = UnforcedLeray.Heat.simHeat ν a := rfl
  have hs : ∀ τ, ContDiff ℝ 2 (UnforcedLeray.Heat.simHeat ν a τ) := fun τ =>
    (UnforcedLeray.Heat.simHeat_contDiff hν ha.heatAdmissible τ).of_le
      (by first | exact le_top | simp)
  rw [hfun]
  refine ⟨hs, fun τ y => (UnforcedLeray.Heat.simHeat_equation hν ha τ y).differentiableAt,
    fun τ y => ?_⟩
  have hd := (UnforcedLeray.Heat.simHeat_equation hν ha τ y).deriv
  unfold physDmu
  rw [hd, Ward1381Org.physLap_eq_vlap _ (hs τ)]
  module

/-! ## 4. Composition -/

/-- **`BgDmuMemL2` from the heat remainder** (source 2584-2585, 2607-2635): `D₀U = D₀(U − H_a)`
since `D₀H_a = 0`, and `D₀(U − H_a) = −𝐏(U·∇U)` is an `L²` field. -/
theorem bgDmuMemL2_of_org (h1 : BgBallRemainder) (h2 : BgRemainderEvol)
    (h3 : HeatProfileDmuZero) (h4 : BgUL4) : BgDmuMemL2 := by
  refine AtBallLevels.mono' (AtBallLevels.and (AtBallLevels.and h1 h2) h4) ?_
  intro p V rb pres hU hall τ
  obtain ⟨⟨⟨a, Q, hcore⟩, hev⟩, ⟨C, hC⟩⟩ := hall
  have hsm := hU.smoothU
  have hUτ : ContDiff ℝ 2 (fun y => V τ y + rb τ y) :=
    (hsm.comp (contDiff_const.prodMk contDiff_id)).of_le (by first | exact le_top | simp)
  have hG := (prodL2OfL4_proved (fun y => V τ y + rb τ y) C (hUτ.of_le (by norm_num))
    (hC τ).1 (hC τ).2).1
  have hE := hev a Q hcore τ hG
  have hM : MemLp (physDmu p.ν 0
      (fun t y => V t y + rb t y - UnforcedLeray.Blueprint.heatProfile p.ν a t y) τ) 2 volume :=
    (Lp.memLp _).ae_eq hE.symm
  obtain ⟨Ca, hca⟩ := Ward1381Org.invDist_of_core hcore
  obtain ⟨hHs, hHt, hH0⟩ := h3 p.ν Ca a p.ν_pos hca
  have heq : physDmu p.ν 0 (fun t y => V t y + rb t y) τ = physDmu p.ν 0
      (fun t y => V t y + rb t y - UnforcedLeray.Blueprint.heatProfile p.ν a t y) τ := by
    funext y
    have hUt : DifferentiableAt ℝ (fun t => V t y + rb t y) τ := by
      have hd : DifferentiableAt ℝ (fun x : ℝ × Space => V x.1 x.2 + rb x.1 x.2) (τ, y) :=
        hsm.differentiable (by simp) _
      have hi : DifferentiableAt ℝ (fun t : ℝ => ((t, y) : ℝ × Space)) τ :=
        differentiableAt_id.prodMk (differentiableAt_const y)
      have hc := hd.comp τ hi
      exact hc
    rw [Ward1381Org.physDmu_sub p.ν 0 (fun t y => V t y + rb t y)
      (UnforcedLeray.Blueprint.heatProfile p.ν a) τ y hUt (hHt τ y) hUτ (hHs τ), hH0 τ y,
      sub_zero]
  rw [heq]
  exact hM

end UnforcedLeray.Short.PartIIIb.Concrete
