import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.PresY2.Defs

/-!
# `BgPresLeray` from two Part II facts (task `PartIII-b:C/ward/13/8`)

Source of record: `the November 2 reference manuscript` (73 pages).

The exact profile equation (4138-4141) gives pointwise `D₀U + U·∇U + ∇p = 0`.  Hence, when
`U·∇U ∈ L²`, `∇p = -(D₀U + U·∇U)`.  Two facts at the ball levels finish it:

* `BgDmuL2Sol` (2612-2635): `D₀U = D₀Q ∈ L²` (`Q = U - H_a ∈ C_per H²`, `(∂_τ - y·∇/2)Q ∈ C_per L²`,
  `D₀H_a = 0`) and it is solenoidal, `𝐏 D₀U = D₀U` (the projected equation `A₀U + 𝐏(U·∇U) = 0`,
  2521-2523);
* `BgPresGradClosure` (117-118, 2641-2642): the pressure `p = Σ R_iR_k(u_iu_k)` has `∇p` in the
  gradient closure, i.e. `𝐏 ∇p = 0` whenever `∇p ∈ L²`.

Then `𝐏(U·∇U) = -D₀U` and `∇p = -(I - 𝐏)(U·∇U)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (Params)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`D₀U` is an `L²` solenoidal field at the ball levels** (source 2612-2635: `D₀U = D₀Q` with
`Q ∈ C_per H²`, `(∂_τ - y·∇/2)Q ∈ C_per L²`, `D₀H_a = 0`; 2521-2523: the projected equation
`A₀U + 𝐏(U·∇U) = 0` puts `A₀U = D₀U` in the range of `𝐏`): for every phase, `D₀U(τ) ∈ L²` and
`𝐏 D₀U(τ) = D₀U(τ)`. -/
def BgDmuL2Sol : Prop :=
  AtBallLevels fun p V rb _ => ∀ τ : ℝ,
    MemLp (physDmu p.ν 0 (fun t y => V t y + rb t y) τ) 2 volume ∧
      UnforcedLeray.Leray.projection
          (UnforcedLeray.toL2 (physDmu p.ν 0 (fun t y => V t y + rb t y) τ)) =
        UnforcedLeray.toL2 (physDmu p.ν 0 (fun t y => V t y + rb t y) τ)

/-- **The pressure gradient of the exact background is a gradient in `L²`** (source 117-118: "The
pressure is the global choice `p = Σ R_iR_k(u_iu_k)`"; 2641-2642: `p_U ∈ C_per L²` "recovers the
discarded gradient part"): at every phase where `∇p ∈ L²`, `𝐏 ∇p = 0`
(`Leray.projection_eq_zero_iff_mem_gradientClosure`). -/
def BgPresGradClosure : Prop :=
  AtBallLevels fun _ _ _ pres => ∀ τ : ℝ, MemLp (physGrad (pres τ)) 2 volume →
    UnforcedLeray.Leray.projection (UnforcedLeray.toL2 (physGrad (pres τ))) = 0

theorem bgPresLeray_of (hA : BgDmuL2Sol) (hB : BgPresGradClosure) : BgPresLeray := by
  refine AtBallLevels.mono' (AtBallLevels.and hA hB) ?_
  intro p V rb pres hU ⟨hA', hB'⟩ τ hG
  obtain ⟨hD, hPD⟩ := hA' τ
  set D : SpatialField := physDmu p.ν 0 (fun t y => V t y + rb t y) τ with hDdef
  set Gf : SpatialField :=
    (fun y => fderiv ℝ (fun y' => V τ y' + rb τ y') y (V τ y + rb τ y)) with hGdef
  have heq : physGrad (pres τ) = -(D + Gf) := by
    funext y
    have h := hU.equation τ y
    exact eq_neg_of_add_eq_zero_right h
  have hg : MemLp (physGrad (pres τ)) 2 volume := by
    rw [heq]; exact (hD.add hG).neg
  have h0 := hB' τ hg
  have hgL : UnforcedLeray.toL2 (physGrad (pres τ)) =
      -(UnforcedLeray.toL2 D + UnforcedLeray.toL2 Gf) := by
    rw [heq, UnforcedLeray.toL2_of_memLp (hD.add hG).neg, UnforcedLeray.toL2_of_memLp hD,
      UnforcedLeray.toL2_of_memLp hG, ← MemLp.toLp_add hD hG, MemLp.toLp_neg]
  rw [hgL, map_neg, map_add, hPD] at h0
  have hPG : UnforcedLeray.Leray.projection (UnforcedLeray.toL2 Gf) = -UnforcedLeray.toL2 D := by
    have : UnforcedLeray.toL2 D + UnforcedLeray.Leray.projection (UnforcedLeray.toL2 Gf) = 0 :=
      neg_eq_zero.mp h0
    exact eq_neg_of_add_eq_zero_right this
  have hel : -(UnforcedLeray.toL2 Gf - UnforcedLeray.Leray.projection (UnforcedLeray.toL2 Gf)) =
      UnforcedLeray.toL2 (physGrad (pres τ)) := by
    rw [hgL, hPG]; abel
  rw [hel, UnforcedLeray.toL2_of_memLp hg]
  exact (MemLp.coeFn_toLp hg).symm

end UnforcedLeray.Short.PartIIIb.Concrete
