import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2.R0Invariant_of
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_1.ComplexAdjoint

/-!
# `T0SolenoidalInvariant` from the adjoint gradient-preservation (decomposition of
`PartIII-b:C/flatset/col/7/1/1/2/6/1/1/2/1/1`)

Source `the November 2 reference manuscript`
1640-1656: `T0(t)* = e^{-t/2} e^{νs(eᵗ-1)Δ_{q,η}} f(s eᵗ)` maps the gradient tests
`(D_0Φ, ∂_ηΦ)` into the closed span of gradient tests (heat is constant coefficient and
commutes with the gradient, the `s`-dilation preserves the form).  Dually `T0(t)` preserves
the orthogonal complement `solenoidalHC 0 c`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)

/-- **Lemma (adjoint preserves gradient closure).** For `t > 0`, `T0(t)*` maps every generator
`toLp (cgrad 0 Φ)` of the span defining `solenoidalHC 0 c` into the closure of that span, i.e.
into `(solenoidalHC 0 c)ᗮ` (source 1650-1656: `heat(∇Φ) = ∇(heat Φ)`, dilation in `s`; the
image is the gradient of a Gaussian-decaying smooth profile, approximated by compactly
supported tests by a Gaussian cut-off in `η`). -/
def T0adjGradPres : Prop :=
  ∀ (c ν : ℝ) (hc : 0 < c) (t : ℝ), 0 < t →
    ∀ (Φ : UnforcedLeray.B0226.ProfileTest c)
      (h : MemLp (UnforcedLeray.Short.PartIIa.cgrad 0 Φ.1) 2 (measureH c)),
      UnforcedLeray.B0224.T0adj hc ν t (h.toLp _) ∈
        (UnforcedLeray.Short.PartIIa.solenoidalHC 0 c)ᗮ

theorem t0SolenoidalInvariant_of (hA : T0ComplexAdjoint) (hG : T0adjGradPres) :
    T0SolenoidalInvariant := by
  intro c ν hc t ht u hu
  unfold UnforcedLeray.Short.PartIIa.solenoidalHC at hu ⊢
  rw [Submodule.mem_orthogonal]
  intro g hg
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨Φ, h, rfl⟩ := hg
    rw [hA c ν hc t _ u]
    have := hG c ν hc t ht Φ h
    unfold UnforcedLeray.Short.PartIIa.solenoidalHC at this
    exact Submodule.inner_left_of_mem_orthogonal hu this
  | zero => simp
  | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
  | smul a x _ hx => rw [inner_smul_left, hx, mul_zero]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
