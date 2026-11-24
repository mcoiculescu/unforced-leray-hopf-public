import UnforcedLeray.Short.PartI.Sub.S13a
import UnforcedLeray.Units.B0062

/-!
# Part I, task `PartI:S13a`, group step: `FreeFlowGroup j` for every `j`

Source of record: `the November 2 reference manuscript`, lines 841-852
(the free transport `T(t)f(r,ϑ) = f(r, ϑ - Ω(r)t)` is a group).

Proof. The flow `Φ_t y = e^{-itΩ(|y|)} y` of the unit `B0062` satisfies `Φ_s ∘ Φ_t = Φ_{s+t}`
(`B0062.flow_flow`, `B0062.flow_zero`), and `freeFlow t f = f ∘ Φ_t` pointwise. Composition with
`Φ_s` preserves a.e. equality (`B0062.ae_comp_flow`, since `Φ_s` is volume preserving). Hence for a
family `T` representing the free flow, `T(s+t)F` and `T(s)(T(t)F)` have a.e. equal values, and
`HjM.ext` with `B0062.L2w_eq_of_ae` gives equality of the elements. Likewise `T 0 F = F`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-- The free flow in pointwise form: `freeFlow t f y = f (Φ_t y)`, `Φ_t = B0062.flow t`. -/
theorem freeFlow_apply_grp (t : ℝ) (f : ℂ → ℂ) (y : ℂ) :
    freeFlow t f y = f (UnforcedLeray.B0062.flow t y) := by
  have hO : B0009.Omega y = UnforcedLeray.B0062.Omega ‖y‖ := rfl
  have hm : -(t * B0009.Omega y) = -(UnforcedLeray.B0062.Omega ‖y‖ * t) := by
    rw [hO]
    ring
  simp only [freeFlow, UnforcedLeray.B0062.flow, UnforcedLeray.B0062.phase,
    UnforcedLeray.B0062.gexp, hm]

/-- The free flow at time `0` is the identity. -/
theorem freeFlow_zero_grp (f : ℂ → ℂ) : freeFlow 0 f = f := by
  funext y
  rw [freeFlow_apply_grp, UnforcedLeray.B0062.flow_zero]

/-- Group law for the free flow on functions: `freeFlow s (freeFlow t f) = freeFlow (s + t) f`. -/
theorem freeFlow_comp_grp (s t : ℝ) (f : ℂ → ℂ) :
    freeFlow s (freeFlow t f) = freeFlow (s + t) f := by
  funext y
  rw [freeFlow_apply_grp, freeFlow_apply_grp, freeFlow_apply_grp,
    UnforcedLeray.B0062.flow_flow, add_comm t s]

/-- The free flow respects almost-everywhere equality (volume preservation of `Φ_t`). -/
theorem freeFlow_ae_grp (t : ℝ) {f g : ℂ → ℂ} (h : f =ᵐ[volume] g) :
    freeFlow t f =ᵐ[volume] freeFlow t g := by
  have h2 : (fun y => f (UnforcedLeray.B0062.flow t y)) =ᵐ[volume]
      fun y => g (UnforcedLeray.B0062.flow t y) :=
    UnforcedLeray.B0062.ae_comp_flow t h
  have e1 : freeFlow t f = fun y => f (UnforcedLeray.B0062.flow t y) :=
    funext (freeFlow_apply_grp t f)
  have e2 : freeFlow t g = fun y => g (UnforcedLeray.B0062.flow t y) :=
    funext (freeFlow_apply_grp t g)
  rw [e1, e2]
  exact h2

/-- **The free transport group on `H^j_M`** (source lines 841-852): every family `T` of bounded
operators representing the free flow satisfies `T(s+t) = T(s) T(t)` and `T(0) = 1`. -/
theorem freeFlowGroup (j : ℕ) : FreeFlowGroup j := by
  unfold FreeFlowGroup
  intro M _hM T hrep
  have hzero : T 0 = 1 := by
    ext1 F
    show T 0 F = F
    apply UnforcedLeray.B0008.HjM.ext
    apply UnforcedLeray.B0062.L2w_eq_of_ae
    filter_upwards [hrep 0 F] with y e1
    rw [e1, freeFlow_zero_grp]
  refine ⟨fun s t => ?_, hzero⟩
  ext1 F
  show T (s + t) F = T s (T t F)
  apply UnforcedLeray.B0008.HjM.ext
  apply UnforcedLeray.B0062.L2w_eq_of_ae
  filter_upwards [hrep (s + t) F, hrep s (T t F), freeFlow_ae_grp s (hrep t F)] with y e1 e2 e3
  rw [e1, e2, e3, freeFlow_comp_grp]

end UnforcedLeray.Short.PartI
