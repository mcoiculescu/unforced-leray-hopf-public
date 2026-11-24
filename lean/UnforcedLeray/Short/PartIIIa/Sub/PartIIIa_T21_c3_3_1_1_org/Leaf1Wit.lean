import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2_2

/-!
# Leaf (a) of `PartIII-a:T21/c3/3/1/1`, part 1: witnesses (pairs of cylinder data with flows)

Source `the November 2 reference manuscript` (SP) lines 2937-2958.
A witness is a pair of real cylinder test data with free cylinder flows; it represents the complex
datum `movCx` and the free flow `movCx` of the flows.  Witnesses form a `ℂ`-module (up to the
pointwise formulas below), and the free energy bound gives `‖out‖ ≤ C ‖in‖` (Pythagoras in `X_{m,d}`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

namespace ComplFreeRateSub

namespace Leaf1Aux

theorem isCylTest_add' {c : ℝ} {φ ψ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest c φ)
    (hψ : B0579.IsCylTest c ψ) : B0579.IsCylTest c (fun x => φ x + ψ x) where
  smooth := hφ.smooth.add hψ.smooth
  periodic := fun x => by simp only [hφ.periodic x, hψ.periodic x]
  band := by
    obtain ⟨R, hR⟩ := hφ.band
    obtain ⟨R', hR'⟩ := hψ.band
    refine ⟨max R R', fun x hx => ?_⟩
    rw [hR x (lt_of_le_of_lt (le_max_left _ _) hx), hR' x (lt_of_le_of_lt (le_max_right _ _) hx)]
    ring

theorem isCylTest_smul' {c : ℝ} (a : ℝ) {φ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest c φ) :
    B0579.IsCylTest c (fun x => a * φ x) where
  smooth := contDiff_const.mul hφ.smooth
  periodic := fun x => by simp only [hφ.periodic x]
  band := by
    obtain ⟨R, hR⟩ := hφ.band
    exact ⟨R, fun x hx => by rw [hR x hx]; ring⟩

theorem isCylTest_zero' (c : ℝ) : B0579.IsCylTest c (fun _ => (0 : ℝ)) where
  smooth := contDiff_const
  periodic := fun _ => rfl
  band := ⟨0, fun _ _ => rfl⟩

theorem isFreeCylFlow_zero {ν c m : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (t₀ : ℝ) :
    UnforcedLeray.Short.IIb.IsFreeCylFlow m tr t₀ (fun _ => (0 : ℝ)) (fun _ _ => (0 : ℝ)) where
  initial := Filter.EventuallyEq.rfl
  memX := fun _ _ => MemLp.zero
  strongCont := fun s _ => by simpa using tendsto_const_nhds
  integrable := fun φ _ r _ => by
    have : UnforcedLeray.Short.IIb.cylFreeIntegrand tr (fun _ : B0579.Plane => (0 : ℝ)) r φ =
        fun _ => 0 := by
      funext x; simp [UnforcedLeray.Short.IIb.cylFreeIntegrand]
    rw [this]; exact integrableOn_zero
  timeIntegrable := fun φ _ s _ => by
    simp [UnforcedLeray.Short.IIb.cylFreeIntegrand]
  weak := fun φ _ s _ => by
    simp [UnforcedLeray.Short.IIb.cylFreeIntegrand]

/-- A witness: two cylinder test data at age `s₁` with free cylinder flows. -/
structure Wit (ν m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (s₁ : ℝ) where
  f₁ : B0579.Plane → ℝ
  f₂ : B0579.Plane → ℝ
  ω₁ : ℝ → B0579.Plane → ℝ
  ω₂ : ℝ → B0579.Plane → ℝ
  hf₁ : B0579.IsCylTest (ν ^ (-2 : ℝ)) f₁
  hf₂ : B0579.IsCylTest (ν ^ (-2 : ℝ)) f₂
  hω₁ : UnforcedLeray.Short.IIb.IsFreeCylFlow m tr s₁ f₁ ω₁
  hω₂ : UnforcedLeray.Short.IIb.IsFreeCylFlow m tr s₁ f₂ ω₂

variable {ν m : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))} {s₁ : ℝ}

/-- Input function of a witness. -/
def Wit.inp (W : Wit ν m tr s₁) : ℝ × ℝ → ℂ := movCx (clockA ν s₁) W.f₁ W.f₂

/-- Output function of a witness at age `s₂`. -/
def Wit.out (W : Wit ν m tr s₁) (s₂ : ℝ) : ℝ × ℝ → ℂ :=
  movCx (clockA ν s₂) (W.ω₁ s₂) (W.ω₂ s₂)

/-- Sum of witnesses. -/
def Wit.add (W W' : Wit ν m tr s₁) : Wit ν m tr s₁ where
  f₁ := fun x => W.f₁ x + W'.f₁ x
  f₂ := fun x => W.f₂ x + W'.f₂ x
  ω₁ := fun t x => W.ω₁ t x + W'.ω₁ t x
  ω₂ := fun t x => W.ω₂ t x + W'.ω₂ t x
  hf₁ := isCylTest_add' W.hf₁ W'.hf₁
  hf₂ := isCylTest_add' W.hf₂ W'.hf₂
  hω₁ := W.hω₁.add W'.hω₁
  hω₂ := W.hω₂.add W'.hω₂

/-- Complex scalar multiple of a witness: `(α + iβ)(f₁ + i f₂) = (α f₁ - β f₂) + i(β f₁ + α f₂)`. -/
def Wit.smul (c : ℂ) (W : Wit ν m tr s₁) : Wit ν m tr s₁ where
  f₁ := fun x => c.re * W.f₁ x + (-c.im) * W.f₂ x
  f₂ := fun x => c.im * W.f₁ x + c.re * W.f₂ x
  ω₁ := fun t x => c.re * W.ω₁ t x + (-c.im) * W.ω₂ t x
  ω₂ := fun t x => c.im * W.ω₁ t x + c.re * W.ω₂ t x
  hf₁ := isCylTest_add' (isCylTest_smul' _ W.hf₁) (isCylTest_smul' _ W.hf₂)
  hf₂ := isCylTest_add' (isCylTest_smul' _ W.hf₁) (isCylTest_smul' _ W.hf₂)
  hω₁ := (W.hω₁.smul _).add (W.hω₂.smul _)
  hω₂ := (W.hω₁.smul _).add (W.hω₂.smul _)

/-- The zero witness. -/
def Wit.zero (ν m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (s₁ : ℝ) :
    Wit ν m tr s₁ where
  f₁ := fun _ => 0
  f₂ := fun _ => 0
  ω₁ := fun _ _ => 0
  ω₂ := fun _ _ => 0
  hf₁ := isCylTest_zero' _
  hf₂ := isCylTest_zero' _
  hω₁ := isFreeCylFlow_zero tr s₁
  hω₂ := isFreeCylFlow_zero tr s₁

theorem movCx_add (a : ℝ) (f₁ f₂ g₁ g₂ : B0579.Plane → ℝ) (y : ℝ × ℝ) :
    movCx a (fun x => f₁ x + g₁ x) (fun x => f₂ x + g₂ x) y = movCx a f₁ f₂ y + movCx a g₁ g₂ y := by
  simp only [movCx, JscaleInv]
  push_cast
  ring

theorem movCx_smul (a : ℝ) (c : ℂ) (f₁ f₂ : B0579.Plane → ℝ) (y : ℝ × ℝ) :
    movCx a (fun x => c.re * f₁ x + (-c.im) * f₂ x) (fun x => c.im * f₁ x + c.re * f₂ x) y =
      c * movCx a f₁ f₂ y := by
  simp only [movCx, JscaleInv]
  apply Complex.ext <;> simp <;> ring

theorem movCx_zero (a : ℝ) (y : ℝ × ℝ) :
    movCx a (fun _ => 0) (fun _ => 0) y = 0 := by
  simp [movCx, JscaleInv]

theorem Wit.inp_add (W W' : Wit ν m tr s₁) : (W.add W').inp = fun y => W.inp y + W'.inp y := by
  funext y; exact movCx_add _ _ _ _ _ _

theorem Wit.out_add (W W' : Wit ν m tr s₁) (s₂ : ℝ) :
    (W.add W').out s₂ = fun y => W.out s₂ y + W'.out s₂ y := by
  funext y; exact movCx_add _ _ _ _ _ _

theorem Wit.inp_smul (c : ℂ) (W : Wit ν m tr s₁) : (W.smul c).inp = fun y => c * W.inp y := by
  funext y; exact movCx_smul _ _ _ _ _

theorem Wit.out_smul (c : ℂ) (W : Wit ν m tr s₁) (s₂ : ℝ) :
    (W.smul c).out s₂ = fun y => c * W.out s₂ y := by
  funext y; exact movCx_smul _ _ _ _ _

theorem Wit.inp_zero : (Wit.zero ν m tr s₁).inp = 0 := by
  funext y; exact movCx_zero _ _

theorem Wit.out_zero (s₂ : ℝ) : (Wit.zero ν m tr s₁).out s₂ = 0 := by
  funext y; exact movCx_zero _ _

end Leaf1Aux

end ComplFreeRateSub

end UnforcedLeray.Short.IIIa
