import UnforcedLeray.Short.PartIIb.Sub.G4_3_org
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T09_4

/-!
# Part II-b, task `PartII-b:G4/3/5` (`ProfileUnique`): decomposition

Source of record: `the November 2 reference manuscript` (SP) lines 1902-1906
(`dm = s^{-5/2} ds dq/c dη`, `Mb = √s b`), 2370-2384.  Same route as `DivVanish`
(`Sub/PartII-b_T09_4.lean`): window tests `χ` pull back to phase tests `φ` (`ChartWindowTest`),
`Φ = φ e_r` and `Φ = φ e_z` are phase tests (`φ` vanishes near the axis), the pairing of `Φ` with
`N_v g` is `(πR²/c) ∫ χ s^{-5/2} √s g_j` (`ChartWindowIntegral`), then `FundWindow` and periodicity.

Proved here: `profileUnique_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace

/-- **Window vanishing** (SP 1902-1906, 2370-2384): if two `H_p` profiles have equal phase
pairings of their ring lifts, then every window integral of `√s (b - b')_j` vanishes, `j = r, z`.
(Take `Φ = φ·realC(e_r)` resp. `φ·realC(e_z)`, `φ` the phase test of a window test `χ`
(`ChartWindowTest`, accepted); `Φ` is a phase test since `φ` vanishes near the axis; by linearity
`⟪Φ, N_v(b - b')⟫ = 0`, with the pairing integrable by `phase_holder_bound`
(`Tasks/DriftNvC/PairCont/HolderBound.lean`) after periodic representatives as in `pairCont_rep`;
`dotL(Φ, N_v g) = φ √s g_j(chart)` and `ChartWindowIntegral` (proof in
`Sub/PartII-b_T09_4_2.lean`) turn the pairing into `(πR²/c) wInt χ (√s g_j)`.) -/
def ProfileWindowZero : Prop :=
  ∀ (c ε : ℝ) (b b' : CProf), 0 < c → 0 < ε → InHr c bgp b → InHr c bgp b' →
    (∀ Φ : ℝ × Space → CVec3, IsPhaseTest (2 * ε * c) Φ →
      pairF (2 * ε * c) Φ (NvC ε⁻¹ b) = pairF (2 * ε * c) Φ (NvC ε⁻¹ b')) →
    ∀ χ : Coord → ℝ, IsWinTest c χ → ∀ j : Fin 2,
      wInt χ (fun x => ((Real.sqrt x.1 : ℝ) : ℂ) * (b x j - b' x j)) = 0

/-- **Local integrability of `√s b_j`** on `s > 0` for `b ∈ H_p` (`p = 11/4 > 2`; on compact
subsets of `s > 0` the weight `s^{p/2-5/2}` is bounded above and below, so `b ∈ L^p_loc ⊆ L¹_loc`;
`q`-periodicity handles unbounded `q`), as in `DivLocInt`. -/
def ProfileLocInt : Prop :=
  ∀ (c : ℝ) (b : CProf), 0 < c → InHr c bgp b → ∀ j : Fin 2,
    LocallyIntegrableOn (fun x : Coord => ((Real.sqrt x.1 : ℝ) : ℂ) * b x j)
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) volume

/-- **From the window strip to all of `H_p`'s measure** (as `DivPeriodicExtend`): a.e. vanishing of
`√s (b - b')_j` on `s > 0, |q| < c/2` for `j = r, z`, together with `c`-periodicity in `q` of
`b, b'` (`InHr.periodic`) and translation invariance of Lebesgue measure, gives `b = b'`
`hMeas c bgp`-a.e. (`hMeas = Axi.ageμ`, the measure `s^{p/2-5/2} ds dq/c dη` on `s > 0`;
`Axi.ae_ageμ_mem`). -/
def ProfileStripExtend : Prop :=
  ∀ (c : ℝ) (b b' : CProf), 0 < c → InHr c bgp b → InHr c bgp b' →
    (∀ j : Fin 2, ∀ᵐ x ∂(volume.restrict
        (Ioi (0 : ℝ) ×ˢ (Ioo (-c / 2) (c / 2) ×ˢ (univ : Set ℝ)))),
      ((Real.sqrt x.1 : ℝ) : ℂ) * (b x j - b' x j) = 0) →
    b =ᵐ[hMeas c bgp] b'

/-- **`ProfileUnique` from the three leaves and `FundWindow`.** -/
theorem profileUnique_of (h1 : ProfileWindowZero) (h2 : ProfileLocInt) (h3 : ProfileStripExtend)
    (h4 : FundWindow) : ProfileUnique := by
  intro c ε hc hε b b' hb hb' hpair
  refine h3 c b b' hc hb hb' ?_
  intro j
  have e : (fun x : Coord => ((Real.sqrt x.1 : ℝ) : ℂ) * (b x j - b' x j)) =
      fun x => ((Real.sqrt x.1 : ℝ) : ℂ) * b x j - ((Real.sqrt x.1 : ℝ) : ℂ) * b' x j := by
    funext x; ring
  refine h4 c (fun x : Coord => ((Real.sqrt x.1 : ℝ) : ℂ) * (b x j - b' x j)) hc ?_ ?_
  · rw [e]; exact (h2 c b hc hb j).sub (h2 c b' hc hb' j)
  · exact fun χ hχ => h1 c ε b b' hc hε hb hb' hpair χ hχ j

end UnforcedLeray.Short.IIb
