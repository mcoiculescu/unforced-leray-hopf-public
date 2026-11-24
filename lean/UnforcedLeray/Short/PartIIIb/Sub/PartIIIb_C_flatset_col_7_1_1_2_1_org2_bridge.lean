import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.Duhamel

/-!
# `DuhamelBridge` from three leaves

Source `the November 2 reference manuscript` 1650-1656, 1684-1689.
The chain: lift `g` to an `H`-representative `f'` (leaf `BridgeLift`); `T₀ f' = R₀ (P₀ f')` is the
Duhamel integral of `G` in `H` (leaf `BridgeCausal`: `P₀ f' = M_s Gh` and
`B0225.R0_Ms_ae_causalHeat`, Fubini identification `causalHeat = duhamel`); transfer of the a.e.
identity from `Profile` with `measureH` to `Chart` with `ageμ c (-3/2)` (leaf `BridgeTransfer`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- A smooth force has an `H`-representative (complexified, cell-recentred). -/
def BridgeLift : Prop :=
  ∀ (c : ℝ) (_hc : 0 < c) (g : Hsp c), IsSmoothForce c g →
    ∃ f' : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC,
      (f' : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
        =ᵐ[UnforcedLeray.B0220.measureH c] (fun p => NearInst.merC (g (NearInst.cellPt c p)))

/-- `R₀ (P₀ f')` is the Duhamel integral of the driving `G` (`P₀ f' = s • G`, `G ∈ H_g`,
`B0225.R0_Ms_ae_causalHeat`, `causalHeat = duhamel` by Fubini and `q`-periodicity of `G`). -/
def BridgeCausal : Prop :=
  ∀ (c ν μ : ℝ) (hc : 0 < c) (G : Chart → Fin 2 → ℝ),
    0 < ν → 0 < μ + 1 / 4 → IsDriving c G →
    ∀ f' : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC,
      ((UnforcedLeray.Short.PartIIa.PepsC 0 c f' : UnforcedLeray.B0220.HSpace c
          UnforcedLeray.B0223.MeridC) : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
        =ᵐ[UnforcedLeray.B0220.measureH c]
        (fun p => WithLp.toLp 2 (fun i : Fin 2 => ((p.1 * G (NearInst.cellPt c p) i : ℝ) : ℂ))) →
      ((UnforcedLeray.B0225.R0 hc ν (μ : ℂ) (UnforcedLeray.Short.PartIIa.PepsC 0 c f') :
          UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC) :
          UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
        =ᵐ[UnforcedLeray.B0220.measureH c]
        (fun p => WithLp.toLp 2 (fun i : Fin 2 => duhamel ν μ G (NearInst.cellPt c p) i))

/-- Transfer of an a.e. identity from `(Profile, measureH c)` via `cellPt` to `(Chart, ageμ c (-3/2))`
(`cellPt` is the recentring of the cell; `ageμ` lives on the cell). -/
def BridgeTransfer : Prop :=
  ∀ (c : ℝ) (_hc : 0 < c) (b : Chart → Merid) (F : Chart → Fin 2 → ℂ),
    (fun p : UnforcedLeray.B0220.Profile => NearInst.merC (b (NearInst.cellPt c p)))
        =ᵐ[UnforcedLeray.B0220.measureH c]
        (fun p => WithLp.toLp 2 (fun i : Fin 2 => F (NearInst.cellPt c p) i)) →
      NearInst.velC b =ᵐ[ageμ c (-3 / 2)] F

theorem duhamelBridge_of (h1 : BridgeLift) (h2 : BridgeCausal) (h3 : BridgeTransfer) :
    DuhamelBridge := by
  intro c ν μ hc R0 g G hctx hG hP
  obtain ⟨hν, hμ, hT, hg⟩ := hctx
  obtain ⟨f', hf'⟩ := h1 c hc g hg
  have e1 := hT g f' hf'
  have e2 := h2 c ν μ hc G hν hμ hG f' (hP f' hf')
  refine h3 c hc (R0 g) (fun p i => duhamel ν μ G p i) ?_
  have e3 : ((UnforcedLeray.Short.PartIIa.T0flat hc ν (μ : ℂ) f' :
      UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC) :
      UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) =ᵐ[UnforcedLeray.B0220.measureH c]
      (fun p => NearInst.merC (R0 g (NearInst.cellPt c p))) := e1
  exact e3.symm.trans e2

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
