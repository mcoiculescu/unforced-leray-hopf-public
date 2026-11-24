import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_8_1.Org
import UnforcedLeray.Short.PartIIb.Sub.B3

/-!
# Ward's background facts from `PartII-b:B3` (`ORG:ward/bg-output`)

Source of record: `the November 2 reference manuscript` (73 pages).

The ward step `PartIII-b:C/ward/13` (`BgPresY2B`) needs, at the levels of the contraction-ball
background (`AtBallLevels`), three facts that the source proves once, in the subsection "The
datum, heat remainder, and pressure" of Part II-b (SP 2563-2643), for the state `z` of
`short-bg:result` (SP 2505-2524):

* `BgUL4`: `D^jU ∈ C_per L⁴` for `j ≤ 1` (SP 2607-2610);
* `BgBallRemainder`: the datum and the heat remainder `Q = U − H_a ∈ C_per H²` with the clauses
  of Theorem B3 (SP 2563-2628);
* `BgRemainderEvol`: `D₀(U − H_a) = −𝐏(U·∇U)` for every such datum (SP 2610-2632).

All three are read off `IIb.BallHeatRemainder` (`Short/PartII-b/Sub/B3.lean`, the statement of
`PartII-b:B3`): a ball split `(V, r_b)` (`IsBallSplit`) is `V = U_raw + Σᵢαᵢ Eᵢ`, `r_b = w` for a
state `z` of the ball, so `V + r_b = bgField p z` (`isBallSplit_bgField`).  For `BgRemainderEvol`
the datum `a` is arbitrary among those with the B3 clauses: `D₀H_a = 0` for every datum in the
inverse-distance class (`heatProfileDmuZero_proved`), so `D₀(U − H_a) = D₀U = D₀(U − H_{a₀})`
with `a₀ = p.datum (p.coord z)`, and `B3Stmt.Evol` is the latter with `Δ = Heat.vlap`
(`Ward1381Org.physLap_eq_vlap`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (Params)

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace WardB3Bridge

/-- A property of the ball states (`IIb.B3Stmt.AtBallStates`) gives a property at the ball levels
(`AtBallLevels`): the ball split is `V = U_raw + Σᵢαᵢ Eᵢ`, `r_b = corr z` for a ball state `z`. -/
theorem of_atBallStates {Φ : (p : Params) → p.Z → Prop}
    {Ψ : Params → (ℝ → SpatialField) → (ℝ → SpatialField) → (ℝ → Space → ℝ) → Prop}
    (h : UnforcedLeray.Short.IIb.B3Stmt.AtBallStates Φ)
    (hΦ : ∀ (p : Params) (z : p.Z) (pres : ℝ → Space → ℝ),
      IsExactProfile p.ν p.period (UnforcedLeray.Short.IIb.bgField p z) pres → Φ p z →
      Ψ p (fun τ y => p.raw τ y + ∑ i : Fin 2, p.coord z i • p.inlet i τ y) (p.corr z) pres) :
    AtBallLevels Ψ := by
  intro Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₀, hν₀, H⟩ := h Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  refine ⟨ν₀, hν₀, fun p d hreg hν hS hq' V rb pres hb hU => ?_⟩
  obtain ⟨z, hz, hV, hrb, hzn⟩ := hb
  have hVf : V = fun τ y => p.raw τ y + ∑ i : Fin 2, p.coord z i • p.inlet i τ y :=
    funext fun τ => funext fun y => hV τ y
  subst hVf hrb
  exact hΦ p z pres hU (H p d hreg hν hS hq' z hz hzn)

end WardB3Bridge

/-- **`BgUL4` from `PartII-b:B3`** (SP 2607-2610): the `L⁴` bounds of `U` and `DU` of
`B3Stmt.UL4` at the ball state of the split. -/
theorem bgUL4_of_ballHeatRemainder (h : UnforcedLeray.Short.IIb.BallHeatRemainder) : BgUL4 := by
  refine WardB3Bridge.of_atBallStates h ?_
  intro p z pres _ hz
  obtain ⟨⟨C, hC⟩, -, -⟩ := hz
  exact ⟨C, fun τ => ⟨(hC τ).1, (hC τ).2.1⟩⟩

/-- **`BgBallRemainder` from `PartII-b:B3`** (SP 2563-2628): the datum `p.datum (p.coord z)` and
the heat remainder of `B3Stmt.Core` at the ball state of the split. -/
theorem bgBallRemainder_of_ballHeatRemainder (h : UnforcedLeray.Short.IIb.BallHeatRemainder) :
    BgBallRemainder := by
  refine WardB3Bridge.of_atBallStates h ?_
  intro p z pres _ hz
  obtain ⟨-, ⟨Q, hQ⟩, -⟩ := hz
  exact ⟨p.datum (p.coord z), Q, hQ⟩

/-- **`BgRemainderEvol` from `PartII-b:B3`** (SP 2610-2632, 4140-4141): for any datum `a` with
the B3 clauses, `D₀(U − H_a) = D₀(U − H_{a₀})` since `D₀H_a = D₀H_{a₀} = 0`
(`heatProfileDmuZero_proved`), and the latter is `B3Stmt.Evol`. -/
theorem bgRemainderEvol_of_ballHeatRemainder (h : UnforcedLeray.Short.IIb.BallHeatRemainder) :
    BgRemainderEvol := by
  refine WardB3Bridge.of_atBallStates h ?_
  intro p z pres hU hz a Q hcore τ _
  obtain ⟨-, ⟨Q₀, hQ₀⟩, hev⟩ := hz
  change physDmu p.ν 0 (fun t y => UnforcedLeray.Short.IIb.bgField p z t y -
      UnforcedLeray.Blueprint.heatProfile p.ν a t y) τ =ᵐ[volume]
    ⇑(-(UnforcedLeray.Leray.projection (UnforcedLeray.toL2
      (fun y => fderiv ℝ (UnforcedLeray.Short.IIb.bgField p z τ) y
        (UnforcedLeray.Short.IIb.bgField p z τ y)))))
  have hcore' : UnforcedLeray.Blueprint.IsB3Core p.ν p.period a
      (UnforcedLeray.Short.IIb.bgField p z) Q := hcore
  set U := UnforcedLeray.Short.IIb.bgField p z with hUdef
  set a₀ := p.datum (p.coord z) with ha₀
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => U x.1 x.2) := hU.smoothU
  have hUs : ∀ t, ContDiff ℝ 2 (U t) := fun t =>
    (hsm.comp (contDiff_const.prodMk contDiff_id)).of_le (by first | exact le_top | simp)
  have hUt : ∀ (t : ℝ) (y : Space), DifferentiableAt ℝ (fun s => U s y) t := by
    intro t y
    have hd : DifferentiableAt ℝ (fun x : ℝ × Space => U x.1 x.2) (t, y) :=
      hsm.differentiable (by simp) _
    have hi : DifferentiableAt ℝ (fun s : ℝ => ((s, y) : ℝ × Space)) t :=
      differentiableAt_id.prodMk (differentiableAt_const y)
    have hc := hd.comp t hi
    exact hc
  obtain ⟨Ca, hca⟩ := Ward1381Org.invDist_of_core hcore'
  obtain ⟨Cb, hcb⟩ := Ward1381Org.invDist_of_core hQ₀
  obtain ⟨hHs, hHt, hH0⟩ := heatProfileDmuZero_proved p.ν Ca a p.ν_pos hca
  obtain ⟨hGs, hGt, hG0⟩ := heatProfileDmuZero_proved p.ν Cb a₀ p.ν_pos hcb
  have key : physDmu p.ν 0 (fun t y => U t y - UnforcedLeray.Blueprint.heatProfile p.ν a t y) τ =
      physDmu p.ν 0 (fun t y => U t y - UnforcedLeray.Blueprint.heatProfile p.ν a₀ t y) τ := by
    funext y
    rw [Ward1381Org.physDmu_sub p.ν 0 U (UnforcedLeray.Blueprint.heatProfile p.ν a) τ y
        (hUt τ y) (hHt τ y) (hUs τ) (hHs τ),
      Ward1381Org.physDmu_sub p.ν 0 U (UnforcedLeray.Blueprint.heatProfile p.ν a₀) τ y
        (hUt τ y) (hGt τ y) (hUs τ) (hGs τ), hH0 τ y, hG0 τ y]
  refine (Filter.EventuallyEq.of_eq ?_).trans (hev τ).2
  rw [key]
  funext y
  unfold physDmu
  beta_reduce
  rw [Ward1381Org.physLap_eq_vlap _ ((hUs τ).sub (hGs τ))]
  module

end UnforcedLeray.Short.PartIIIb.Concrete
