import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEqSub
import UnforcedLeray.Cons.L2.BackgroundConcrete.PhasePairF

/-!
# `PartIII-b:C/ward/12/3/1/2/5` : decomposition of `GEInlet`

Source `the November 2 reference manuscript`
lines 2385-2387, 2542-2551, 1206-1222, 2563-2569.  `GEInlet` splits into
* `GEInletIBP` : the inlet integration by parts, producing a pointwise field `Fn` in `L^{q0E}`
  of the phase measure with `⟨L₀ᵗ∂_jΦ,E_i⟩ + ⟨conv ∂_jΦ,E_i⟩ = ⟨Φ,Fn⟩`;
* `InletRepYq` : an `L^{q0E}` periodic field is the representative of an element of `Y_p`.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.PhaseSpace MeasureTheory Set
open UnforcedLeray.Cons.C03.Concrete (Params IsSolTest pairF convT advT rep)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Integration by parts for the inlet columns (source 2385-2387, 2542-2551): the inlet cutoff
vanishes near the axis, `E_i` decays like `ρ^{-3-k}(1+|y₃|/ρ)^{-N}` (2563-2569), and `raw` obeys
the derivative bounds 1206-1222, so
`⟨L₀ᵗ∂_jΦ,E_i⟩ + ⟨conv_raw ∂_jΦ,E_i⟩ = ⟨Φ,F_n⟩` with `F_n = -∂_j(L₀E_i + B_raw E_i) ∈ L^{q0E}`. -/
def GEInletIBP : Prop := GERegime fun p _ _ =>
  ∀ (i : Fin 2) (j : Fin 3), ∃ Fn : ℝ × UnforcedLeray.Space → CVec3,
    MemLp Fn UnforcedLeray.B0412.q0E
        ((volume.restrict (Ioc (0 : ℝ) p.period)).prod volume) ∧
    ∀ Φ, IsSolTest p.period Φ →
      pairF p.period (UnforcedLeray.B0411.L0T p.ν (dy j Φ)) (p.Efun i) +
          pairF p.period (convT p.raw (dy j Φ)) (p.Efun i) = pairF p.period Φ Fn

/-- Every phase `L^q`-field is represented by an element of `Y_p` (for a.e. slice `t`; the conclusion cannot be for every `t`, since `Fn` may be non-measurable on a null set of `t`). -/
def InletRepYq (P : ℝ) [Fact (0 < P)] : Prop :=
  ∀ Fn : ℝ × UnforcedLeray.Space → CVec3,
    MemLp Fn UnforcedLeray.B0412.q0E ((volume.restrict (Ioc (0 : ℝ) P)).prod volume) →
    ∃ F : Yq P UnforcedLeray.B0412.q0E, ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) P)),
      ∀ᵐ y ∂(volume : Measure UnforcedLeray.Space), rep F t y = Fn (t, y)

theorem gEInlet_of (h1 : GEInletIBP) (h2 : ∀ (p : Params), InletRepYq p.period) : GEInlet := by
  intro lam q hq dm dp hdm
  obtain ⟨ν₀, hν₀, H⟩ := h1 lam q hq dm dp hdm
  refine ⟨ν₀, hν₀, fun p d hreg hν hm z g hg i j => ?_⟩
  obtain ⟨Fn, hFn, hid⟩ := H p d hreg hν hm z g hg i j
  obtain ⟨F, hF⟩ := h2 p Fn hFn
  refine ⟨F, fun Φ hΦ => ?_⟩
  rw [hid Φ hΦ, UnforcedLeray.Cons.C03.Concrete.phasePair_eq_pairF_rep hΦ.1 F]
  unfold pairF UnforcedLeray.Cons.C03.Concrete.phaseInt
  congr 1
  refine setIntegral_congr_ae measurableSet_Ioc ?_
  filter_upwards [(ae_restrict_iff' measurableSet_Ioc).1 hF] with t ht' ht
  refine integral_congr_ae ?_
  filter_upwards [ht' ht] with y hy
  rw [hy]

end UnforcedLeray.Short.PartIIIb.Concrete
