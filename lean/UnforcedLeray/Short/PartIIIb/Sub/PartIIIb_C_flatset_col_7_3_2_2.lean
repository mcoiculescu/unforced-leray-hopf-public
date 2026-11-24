import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3.Of
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2

/-!
# Right-continuity at `0` of `t ↦ ⟨T₀(t)g, ζ⟩_H`, reduced to strong continuity of `T₀`

Source `the November 2 reference manuscript` 1650-1656.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped InnerProductSpace

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIa (IsMeridTest)

/-- Strong right-continuity at `0` of the `H`-semigroup `T₀` (source 1650-1656; uniform bound
`‖T₀(t)‖ = e^{-t/4}` plus convergence on a dense class). -/
def T0StrongContZero : Prop :=
  ∀ (c ν : ℝ) (hc : 0 < c) (g : HSpace c MeridC),
    Tendsto (fun s : ℝ => UnforcedLeray.B0224.T0 hc ν s g) (𝓝[≥] 0) (𝓝 g)

theorem t0_contZero_of (hS : T0StrongContZero)
    (c ν : ℝ) (hc : 0 < c) (g : HSpace c MeridC) (ζ : Profile → MeridC) (hζ : IsMeridTest c ζ) :
    ContinuousWithinAt
      (fun s : ℝ => pairH c (UnforcedLeray.B0224.T0 hc ν s g : Profile → MeridC) ζ) (Set.Ici 0) 0 := by
  obtain ⟨hZm, -⟩ := memLp_test_A0adj c ν ζ hζ
  set Z : HSpace c MeridC := hZm.toLp ζ with hZdef
  have hZ : (Z : Profile → MeridC) =ᵐ[measureH c] ζ := hZm.coeFn_toLp
  have hfun : (fun s : ℝ => pairH c (UnforcedLeray.B0224.T0 hc ν s g : Profile → MeridC) ζ) =
      fun s : ℝ => inner ℂ Z (UnforcedLeray.B0224.T0 hc ν s g) := by
    funext s
    exact pairH_eq_inner _ Z hZ
  rw [hfun]
  have h0 : UnforcedLeray.B0224.T0 hc ν 0 g = g := by
    rw [UnforcedLeray.B0224.T0_zero_eq]; rfl
  have := (hS c ν hc g)
  unfold ContinuousWithinAt
  show Tendsto _ _ (𝓝 (inner ℂ Z (UnforcedLeray.B0224.T0 hc ν 0 g)))
  rw [h0]
  exact ((continuous_const.inner continuous_id).continuousAt.tendsto).comp this

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
