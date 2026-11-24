import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1

/-!
# `WardX0FarBound` decomposed (`PartIII-b:IIIb-D2/3/1/3/1/1`)

Source `the November 2 reference manuscript`
4155-4186, 3604-3621.  Far-field decay of the separated resolvent field `W_μ` of a periodic
source supported in `|z'| ≤ r_o` with finite `L²_τ L²_z` moment (`SepMoment`, 4155-4156).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- **Far-field decay of `sepW`** (4177-4179, 3604-3621): for a separated source, at each `τ`,
`|W_μ|` and `|∇W_μ|` are `≤ C ϱ^{-3}` on `{2 r_o ≤ ϱ}`.  (`IIIa.sepKernelBounds` for
`|D^j∇K| ≤ C|x|^{-4-j}`; on the cylinder `|z'| ≤ r_o`, `|y-λz|² ≥ (ϱ y/2)² + (y₃-λz₃)²`, so
Cauchy–Schwarz in `z` against the `L²_z` norm gives `‖|y-λ·|^{-4-j}‖_{L²(cyl)} ≲ r_o λ^{-1/2}
ϱ^{-7/2-j}`; then the `λ`-integral of `λ^{2Re μ+3/2}‖T(τ+2log λ)‖_{L²_z}` by Cauchy–Schwarz on
each period and the periodic sum.) -/
def SepFarDecay : Prop :=
  ∀ (ν : ℝ) (μ : ℂ) (rOut P : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ),
    0 < ν → -(1 / 4) < μ.re → 0 ≤ rOut → 0 < P → IIIa.IsSepSource P rOut T → SepMoment P T →
    ∀ τ : ℝ, ∃ C : ℝ, ∀ (i : Fin 3) (y : Space), 2 * rOut ≤ ϱ y →
      ‖IIIa.sepW ν μ T y τ i‖ ≤ C * ϱ y ^ (-3 : ℝ) ∧
      ‖fderiv ℝ (fun y => IIIa.sepW ν μ T y τ i) y‖ ≤ C * ϱ y ^ (-3 : ℝ)

end UnforcedLeray.Short.PartIIIb.Concrete
