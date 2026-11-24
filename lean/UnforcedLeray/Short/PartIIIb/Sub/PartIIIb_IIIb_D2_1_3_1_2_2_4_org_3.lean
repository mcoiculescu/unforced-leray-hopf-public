import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollCommDefs

/-!
# `ShiftPairUnfold` decomposed into three source facts

Source `the November 2 reference manuscript` lines 1351-1362, 1556-1583.
The pairing of the periodised translate `w ↦ (∑ₖ κ(x - w + (kP, 0))) e` with `F ∈ Y_2` unfolds in
three steps: (A) the tiling of `ℝ × ℝ³` by the translated phase cells (using the a.e.
`P`-periodicity of `F`), (B) exchange of the finite (compact-support) sum with the cell integral
(Fubini on the cell), (C) the change of variables `w ↦ x - w` and pulling `dotL e` out of the
Bochner integral.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt)

/-- (A) Tiling by phase cells: for `F ∈ Y_2` (a.e. `P`-periodic in `τ`) and compactly supported
smooth `κ`, `∫_{ℝ×ℝ³} κ(x - w) e·F(w) dw = ∑ₖ ∫_{(0,P]×ℝ³} κ(x - w + (kP,0)) e·F(w) dw`
(`IsAddFundamentalDomain` for `ℤ·(P,0)` with cell `Ioc 0 P ×ˢ univ`, integrable integrand since
`F` is locally integrable, shift `w ↦ w + (kP,0)` and `F(w + (kP,0)) = F w` a.e.). -/
def ShiftPairTiling : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ κ : ℝ × Space → ℝ, ContDiff ℝ ∞ κ → HasCompactSupport κ →
    ∀ F : ℝ × Space → CVec3, UnforcedLeray.Short.IIb.IsInYr P 2 F →
      ∀ (x : ℝ × Space) (e : CVec3),
        ∫ w, ((κ (x - w) : ℝ) : ℂ) * dotL e (F w) =
          ∑' k : ℤ, ∫ w in Ioc (0 : ℝ) P ×ˢ (univ : Set Space),
            ((κ (x - w + ((k : ℝ) * P, 0)) : ℝ) : ℂ) * dotL e (F w)

/-- (B) Sum/cell exchange: on the cell `τ ∈ (0, P]` the periodised sum is locally uniformly a
finite window sum (compact support of `κ`), so the iterated cell integral of
`(∑ₖ κ(x - w + (kP,0))) e·F(w)` equals the sum over `k` of the cell integrals (Fubini on the cell
for the locally integrable `F`; each term is integrable). -/
def ShiftPairCellSum : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ κ : ℝ × Space → ℝ, ContDiff ℝ ∞ κ → HasCompactSupport κ →
    ∀ F : ℝ × Space → CVec3, UnforcedLeray.Short.IIb.IsInYr P 2 F →
      ∀ (x : ℝ × Space) (e : CVec3),
        ∫ t in Ioc (0 : ℝ) P, ∫ y : Space,
            ((∑' k : ℤ, κ (x - (t, y) + ((k : ℝ) * P, 0)) : ℝ) : ℂ) * dotL e (F (t, y)) =
          ∑' k : ℤ, ∫ w in Ioc (0 : ℝ) P ×ˢ (univ : Set Space),
            ((κ (x - w + ((k : ℝ) * P, 0)) : ℝ) : ℂ) * dotL e (F w)

/-- (C) Change of variables `z = x - w` (Haar measure is invariant under `w ↦ x - w`) and
`dotL e (∫ κ z • F(x - z)) = ∫ κ z · dotL e (F(x - z))` (bounded linear map commutes with the
Bochner integral; `κ z • F(x - z)` integrable as `F` is locally integrable and `κ` is
continuous with compact support). -/
def ShiftPairSubst : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ κ : ℝ × Space → ℝ, ContDiff ℝ ∞ κ → HasCompactSupport κ →
    ∀ F : ℝ × Space → CVec3, UnforcedLeray.Short.IIb.IsInYr P 2 F →
      ∀ (x : ℝ × Space) (e : CVec3),
        dotL e (∫ z, κ z • F (x - z)) = ∫ w, ((κ (x - w) : ℝ) : ℂ) * dotL e (F w)

theorem shiftPairUnfold_of (hA : ShiftPairTiling) (hB : ShiftPairCellSum) (hC : ShiftPairSubst) :
    ShiftPairUnfold := by
  intro P hP κ hκ hcs F hF x e
  have hdot : ∀ (r : ℝ) (v : CVec3), dotL (r • e) v = (r : ℂ) * dotL e v := by
    intro r v
    rw [show r • e = (r : ℂ) • e from (Complex.coe_smul r e).symm, map_smul]
    simp
  unfold pairF phaseInt shiftKer
  simp only [hdot]
  rw [hB P hP κ hκ hcs F hF x e, ← hA P hP κ hκ hcs F hF x e, ← hC P hP κ hκ hcs F hF x e,
    Complex.real_smul]
  push_cast
  simp [Complex.ofReal_inv]

end UnforcedLeray.Short.PartIIIb.Concrete
