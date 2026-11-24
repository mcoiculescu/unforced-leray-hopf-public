import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_2
import UnforcedLeray.Lib.LerayC.Complex
import UnforcedLeray.Lib.PhaseSpace.Pairing

/-!
# `PartII-b:T10/org/2/3` (`SolSepSpatial`): decomposition

Source `the November 2 reference manuscript` (SP, the solenoidal-separation step,
cf. the Leray projection and density of compactly supported solenoidal fields in `L^{q'}_σ`).
Route: `∫ Ψ·w = 0` for all `SpatialSolTest Ψ`; `w = 𝐏w`; `⟨F, 𝐏w⟩ = ⟨𝐏F, w⟩`; `𝐏F` for smooth
compactly supported `F` is an `L^{q'}`-limit of `SpatialSolTest`s; hence `⟨F, w⟩ = 0` for all smooth
compactly supported `F`, so `w = 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.B0414 UnforcedLeray.RieszLp

/-- **Complex solenoidal fixed point** (`1 < p < ∞`): a distributionally solenoidal `w ∈ L^p(ℝ³;ℂ³)`
satisfies `𝐏w = w` (`RieszLp.lerayLp_eq_self` on `Re w`, `Im w` via `isSolenoidalC_iff`). -/
def LerayCFixed : Prop :=
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (h1 : 1 < p) (h2 : p ≠ ⊤) (w : Lp CVec3 p (volume : Measure Space)),
    IsSolenoidalC (w : Space → CVec3) → lerayC p h1 h2 w = w

/-- **Complex symmetry of `𝐏`** (`1 < p < ∞`): `∫ G·𝐏F = ∫ 𝐏G·F` for `G ∈ L^{p'}`, `F ∈ L^p`
(`RieszLp.integral_inner_lerayLp_symm` on real and imaginary parts, cf. `LerayCTranspose`). -/
def LerayCSymm : Prop :=
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (h1 : 1 < p) (h2 : p ≠ ⊤)
    (h1' : 1 < conjExp p) (h2' : conjExp p ≠ ⊤)
    (G : Lp CVec3 (conjExp p) (volume : Measure Space)) (F : Lp CVec3 p (volume : Measure Space)),
    innerPair p G (lerayC p h1 h2 F) = innerPair p (lerayC (conjExp p) h1' h2' G) F

/-- **Compact-to-Leray density** (`1 < r < ∞`): for smooth compactly supported `F : ℝ³ → ℂ³`,
`𝐏F` lies in the `L^r`-closure of the `SpatialSolTest`s.  Route: `𝐏F = curl A` with `A` the
projected Newton potential, `A = O(|x|^{-2})`; the cutoffs `curl(χ_R A)` are `SpatialSolTest`s and
converge to `curl A` in `L^r` (cf. `Cons.C03.Concrete.isSolTest_projectedPotentialCurlCutoff`). -/
def LerayCDensity : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)] (h1 : 1 < r) (h2 : r ≠ ⊤) (F : Space → CVec3),
    ContDiff ℝ ∞ F → HasCompactSupport F → ∀ hF : MemLp F r (volume : Measure Space),
      lerayC r h1 h2 (hF.toLp F) ∈
        closure {x : Lp CVec3 r (volume : Measure Space) |
          ∃ (Ψ : Space → CVec3) (hΨ : MemLp Ψ r (volume : Measure Space)),
            SpatialSolTest Ψ ∧ hΨ.toLp Ψ = x}

/-- **Fundamental lemma** (`1 ≤ q`): `w ∈ L^q(ℝ³;ℂ³)` with `∫ F·w = 0` for all smooth compactly
supported `F` vanishes (componentwise, real and imaginary parts, `ae_eq_zero_of_integral_contDiff_smul_eq_zero`). -/
def FundLemmaC : Prop :=
  ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)] (w : Lp CVec3 q (volume : Measure Space)),
    (∀ F : Space → CVec3, ContDiff ℝ ∞ F → HasCompactSupport F →
      ∀ hF : MemLp F (conjExp q) (volume : Measure Space), innerPair q (hF.toLp F) w = 0) → w = 0

/-- `1 < p'` when `p < ∞`. -/
theorem one_lt_conjExp_of_ne_top {p : ℝ≥0∞} (hp : p ≠ ⊤) : 1 < conjExp p := by
  unfold conjExp
  have h0 : p⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hp
  have h1 : 1 - p⁻¹ < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero h0
  exact ENNReal.one_lt_inv.2 h1

theorem solSepSpatial_of (hF : LerayCFixed) (hS : LerayCSymm) (hD : LerayCDensity)
    (hL : FundLemmaC) : UnforcedLeray.Short.IIb.SolSepSpatial := by
  intro q _ hq1 hq w hsol horth
  have h1' : 1 < conjExp q := one_lt_conjExp_of_ne_top hq
  have h2' : conjExp q ≠ ⊤ := conjExp_ne_top hq1
  refine hL q w ?_
  intro F hFs hFc hFm
  have hfix := hF q hq1 hq w hsol
  have hsymm := hS q hq1 hq h1' h2' (hFm.toLp F) w
  rw [hfix] at hsymm
  rw [hsymm]
  -- the continuous functional `g ↦ ⟨g, w⟩` vanishes on the solenoidal tests, hence on the closure
  have hcont : Continuous fun g : Lp CVec3 (conjExp q) (volume : Measure Space) =>
      innerPair q g w := (innerPair q).flip w |>.continuous
  have hclosed : IsClosed {g : Lp CVec3 (conjExp q) (volume : Measure Space) | innerPair q g w = 0} :=
    isClosed_eq hcont continuous_const
  have hsub : {x : Lp CVec3 (conjExp q) (volume : Measure Space) |
        ∃ (Ψ : Space → CVec3) (hΨ : MemLp Ψ (conjExp q) (volume : Measure Space)),
          SpatialSolTest Ψ ∧ hΨ.toLp Ψ = x} ⊆
      {g | innerPair q g w = 0} := by
    rintro x ⟨Ψ, hΨ, hΨs, rfl⟩
    show innerPair q _ w = 0
    rw [innerPair_apply]
    refine (integral_congr_ae ?_).trans (horth Ψ hΨs)
    filter_upwards [hΨ.coeFn_toLp] with y hy
    rw [hy]
  exact (closure_minimal hsub hclosed) (hD (conjExp q) h1' h2' F hFs hFc hFm)

end UnforcedLeray.Short.IIb
