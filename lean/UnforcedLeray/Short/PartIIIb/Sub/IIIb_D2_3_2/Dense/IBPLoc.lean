import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_8
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_8_1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_8_2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_8_3
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_8_4
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_8_5
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_8_6

/-!
# `WardIBPLoc`: integration by parts against phase tests, without decay (source 4268-4270)

Source: `the November 2 reference manuscript`.

`WardIBPLoc` (`Ward3.lean`) is `WardIBP` without its decay and growth hypotheses.  The Ward
fields of the separated kernel decay only like `|y|^{-4}` (`sep:kernel`, 3604-3610), so the weak
equation needs this form.  A phase test has bounded spatial support (`IsPhaseTest.bounded_support`),
and the proof `wardIBP_of` of `Sub/IIIb-D2_3_2_8.lean` never uses the decay or growth
hypotheses; it is repeated here from the same six facts (`PartIII-b:IIIb-D2/3/2/8/1`-`/6`, all
proved).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

theorem wardIBPLoc_of (hA : IBPAdjoint) (hB : IBPBridge) (hD : IBPDiv) (hG : IBPGrad)
    (hL : IBPLin) (hC : IBPCont) (ν μ P : ℝ) (hP : 0 < P) : WardIBPLoc ν μ P := by
  intro U H Y E q hU _ hq hF hid Φ hΦ
  have hH : ContDiff ℝ ∞ (fun x : ℝ × Space => H x.1 x.2) := (hF H (by simp)).1
  have hY : ContDiff ℝ ∞ (fun x : ℝ × Space => Y x.1 x.2) := (hF Y (by simp)).1
  have hE : ContDiff ℝ ∞ (fun x : ℝ × Space => E x.1 x.2) := (hF E (by simp)).1
  have hHp : ∀ τ y, H (τ + P) y = H τ y := (hF H (by simp)).2
  have hW : ContDiff ℝ ∞ (fun x : ℝ × Space => (Y x.1 x.2 + H x.1 x.2)) := hY.add hH
  have hslice : ∀ (F : ℝ → Space → Space),
      ContDiff ℝ ∞ (fun x : ℝ × Space => F x.1 x.2) → ∀ τ,
      Differentiable ℝ (F τ) := by
    intro F hF' τ
    have : ContDiff ℝ ∞ (fun y : Space => F τ y) :=
      hF'.comp (contDiff_const.prodMk contDiff_id)
    exact this.differentiable (by simp)
  have hpt : ∀ τ y, physDmu ν μ H τ y =
      E τ y + physGrad (q τ) y - physDivSym (U τ) (fun y' => Y τ y' + H τ y') y := by
    intro τ y
    have h1 := hid τ y
    rw [physDivSym_add (hslice U hU τ) (hslice Y hY τ) (hslice H hH τ) y]
    ext i
    have hi := congrArg (fun v => v i) h1
    simp only [PiLp.add_apply, PiLp.sub_apply] at hi ⊢
    linarith
  have hfun : physDmu ν μ H = fun τ y =>
      (E τ y + physGrad (q τ) y) - physDivSym (U τ) (fun y' => Y τ y' + H τ y') y := by
    funext τ y; exact hpt τ y
  have hΦt : IsPhaseTest P Φ := hΦ.1
  have hu : ContDiff ℝ ∞ (realCf H) := contDiff_realCf hH
  have hup : ∀ x : ℝ × Space, realCf H (x.1 + P, x.2) = realCf H x := by
    intro x; simp only [realCf, hHp]
  show pairF P (fun x => L0T ν Φ x + (μ : ℂ) • Φ x) (realCf H) =
    pairF P Φ (realCf E) + _
  have s1 := hA P ν μ hP (realCf H) hu hup Φ hΦt
  have s2 : (fun x => L0 ν (realCf H) x + (μ : ℂ) • realCf H x) =
      realCf (physDmu ν μ H) := funext (hB ν μ H hH)
  rw [s2, hfun] at s1
  rw [s1]
  have cE : Continuous (realCf E) := (contDiff_realCf hE).continuous
  have cG := hC.1 q hq
  have cD := hC.2 U (fun τ y => Y τ y + H τ y) hU hW
  have cEG : Continuous (fun x => realCf E x + realCf (fun τ y => physGrad (q τ) y) x) :=
    cE.add cG
  rw [show realCf (fun τ y => (E τ y + physGrad (q τ) y) -
      physDivSym (U τ) (fun y' => Y τ y' + H τ y') y) = fun x =>
      (realCf E x + realCf (fun τ y => physGrad (q τ) y) x) -
        realCf (fun τ y => physDivSym (U τ) (fun y' => Y τ y' + H τ y') y) x by
    rw [realCf_sub, realCf_add]]
  rw [(hL P Φ hΦt _ _ cEG cD).2, (hL P Φ hΦt _ _ cE cG).1, hG P q hq Φ hΦ,
    hD P U (fun τ y => Y τ y + H τ y) hU hW Φ hΦt]
  simp

/-- `WardIBPLoc` holds for every positive period (the six facts are proved). -/
theorem wardIBPLoc_proved (ν μ P : ℝ) (hP : 0 < P) : WardIBPLoc ν μ P :=
  wardIBPLoc_of ibpAdjoint_proved ibpBridge_proved ibpDiv_proved ibpGrad_proved
    ibpLin_proved ibpCont_proved ν μ P hP

end UnforcedLeray.Short.PartIIIb.Concrete
