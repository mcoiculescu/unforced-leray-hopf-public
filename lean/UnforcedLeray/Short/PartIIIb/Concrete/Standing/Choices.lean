import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Estimates
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Seq
import UnforcedLeray.Short.PartIIIb.Concrete.SourceCutoffBridge

/-!
# The choices and the per-level facts of the standing hypotheses (`ORG:C/standing` (c))

Source of record: `the November 2 reference manuscript` (73 pages).

`SeqData.RepairStanding` (`Concrete/ReturnRepair/Estimates.lean`) collects three kinds of
hypotheses on a sequence datum `D`:

* the reference and the fixed choices, made in the order of choice of source 5835-5859 (with
  `a_s` at 5878-5880 and `σ₀, K` at 5922-5950): first the planar reference (`γ = Re λ > 0`,
  `ω ≠ 0`), `σ₀ ∈ (0, 1/4)` and its window, `m_Z > 3/2` and the loss window `[d₋, d₊]`; then the
  integer `K₀` of `near:deltaN` (3927-3942, "a fixed integer `K`, chosen before `a, b`"); then
  `a, b_win` with `K₀(a+b_win) < 1/100`, then `δ, m₀` with `δ < log(12/11)`,
  `η_δ, m₀ < min{ϑd₀/16, γ/1000}`, `d₀ = γ/3` (5843-5856), the transverse-tail accuracy `D_⊥`
  (5855), the background constant `C₀` of `ρ_b = C₀ν^{-k₀}e^{m₀/ν}ε^{3/11}` (2706-2713) with the
  contraction condition `2m₀ < 3d₋/11` (2510-2512, "The background construction realizes this
  `m₀`", 5856-5857), and last `a_s < γ/16` (5878-5880, 4738-4740); the cutoff profiles
  `χ̂_o, χ̂_y, χ̂_f` (4161-4166, 4750-4757, 4955-4956) are fixed with the constants.
  `SeqData.StandingChoices D Kint dm` is the part chosen after the integer `Kint`.
* the per-level facts of the exact background (`SeqData.StandingBridge`, the bridge of
  `ORG:D5/skeleton` step 3): actual levels (2026-2713, 4139-4141), inlet support below the output
  cut `S = ε^{-b}` (2316-2318, 3905-3912), and the repair derivative bounds (5134-5139);
* the pinned operators and the invertible near layer (`RegimePins`, `NearAt`), produced in
  `Concrete/Standing/Producer.lean`.

## Contents

* `outwardCutoffStd`, `isOutwardCutoff_std`; `isYoungCutoff_iff_isStreamCutoff` (the two
  stream-cutoff predicates `IsStreamCutoff`, `SourceL.lean:55`, and `IsYoungCutoff`,
  `PhysLayer.lean:261`, have the same body; `IsSourceCutoff ↔ IsSourceCutoffC` is
  `isSourceCutoffC_iff`, `SourceCutoffBridge.lean`); `exists_cutoffs`.
* `SeqData.StandingChoices`, `SeqData.StandingChoices.mono` (a smaller integer keeps the choice).
* `SeqData.StandingBridge`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData IsPlanarReference)

/-! ## 1. The cutoff profiles (source 4161-4166, 4750-4757, 4955-4956) -/

/-- A standard outward cutoff profile, `t ↦ smoothTransition ((10t - 12)/3)`: zero for
`t ≤ 6/5`, one for `t ≥ 3/2`. -/
def outwardCutoffStd (t : ℝ) : ℝ := Real.smoothTransition ((10 * t - 12) / 3)

/-- `IsOutwardCutoff` is satisfiable (source 4163-4166, 5148-5150). -/
theorem isOutwardCutoff_std : IsOutwardCutoff outwardCutoffStd where
  smooth := Real.smoothTransition.contDiff.comp
    (((contDiff_const.mul contDiff_id).sub contDiff_const).div_const _)
  zero t ht := Real.smoothTransition.zero_of_nonpos (by
    rw [div_nonpos_iff]; right; constructor <;> linarith)
  one t ht := Real.smoothTransition.one_of_one_le (by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]; linarith)
  range t := ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-- The young stream cutoff of the Ward fields (`IsYoungCutoff`, source 4164) and the stream
cutoff of the source maps (`IsStreamCutoff`, source 4755-4757) are the same profile `χ̂_y`. -/
theorem isYoungCutoff_iff_isStreamCutoff (χ : ℝ → ℝ) : IsYoungCutoff χ ↔ IsStreamCutoff χ :=
  ⟨fun h => ⟨h.smooth, h.one, h.zero, h.range⟩, fun h => ⟨h.smooth, h.one, h.zero, h.range⟩⟩

/-- The stream cutoff is a young cutoff (the hypothesis `hχy` of the Ward fields). -/
theorem IsStreamCutoff.isYoungCutoff {χ : ℝ → ℝ} (h : IsStreamCutoff χ) : IsYoungCutoff χ :=
  (isYoungCutoff_iff_isStreamCutoff χ).2 h

/-- **The cutoff profiles exist** (source 4161-4166, 4750-4757, 4955-4956): an outward profile
`χ̂_o`, a stream profile `χ̂_y` and a source profile `χ̂_f`. -/
theorem exists_cutoffs : ∃ χo χy χf : ℝ → ℝ,
    IsOutwardCutoff χo ∧ IsStreamCutoff χy ∧ IsSourceCutoffC χf :=
  ⟨outwardCutoffStd, streamCutoffStd, sourceCutoffStd, isOutwardCutoff_std, isStreamCutoff_std,
    isSourceCutoffC_std⟩

/-! ## 2. The choices after the integer of the near layer (source 5835-5859, 5878-5880) -/

/-- **The fixed choices of the return after the integer `Kint` of the near layer** (source
5835-5859, 5878-5880, 2706-2713, 2510-2512): the near parameter choice `NearChoice` (`a, b_win`
with `Kint(a+b_win) < 1/100`, `δ, m₀ > 0`, `m₀ < 3d₋/11`, `η_δ, m₀ < ϑd₀/8`, `D_⊥ > η_δ + ϑd₀`,
`C₀ > 0`; the source asks `ϑd₀/16`, 5853, which implies it), `δ < log(12/11)` (5852),
the contraction condition `2m₀ < 3d₋/11` of the background construction realizing `m₀`
(2510-2512, 5856-5857), `m₀ < γ/1000` (5853), `0 < a_s < γ/16` (5878-5880), and the stream and
source cutoff profiles (4750-4757, 4955-4956; the outward profile is the field `hχo` of
`ReturnConsts`).  The reference `D.Pl`, `σ₀`, `m_Z` and `[d₋, d₊]` are fixed before `Kint`. -/
structure SeqData.StandingChoices (D : SeqData) (Kint : ℕ) (dm : ℝ) : Prop where
  near : NearInst.NearChoice Kint (gRate D.Pl) dm D.K.b D.K.δ D.K.m0 D.K.C0
  δ_lt : D.K.δ < Real.log (12 / 11)
  m0_ball : 2 * D.K.m0 < 3 * dm / 11
  m0_small : D.K.m0 < gRate D.Pl / 1000
  as_pos : 0 < D.K.as
  as_lt : D.K.as < gRate D.Pl / 16
  chiY : IsStreamCutoff D.K.χy
  chiF : IsSourceCutoffC D.K.χf

namespace Standing

/-- A smaller integer keeps the near parameter choice (`K(a+b) < 1/100` is antitone in `K`). -/
theorem nearChoice_mono {K K' : ℕ} (hK : K' ≤ K) {γ dm b δ m0 C0 : ℝ}
    (h : NearInst.NearChoice K γ dm b δ m0 C0) : NearInst.NearChoice K' γ dm b δ m0 C0 := by
  obtain ⟨a, Dp, ha, hb, hb1, hKab, hrest⟩ := h
  exact ⟨a, Dp, ha, hb, hb1, NearInst.seq_nat_mul_lt (by linarith) hK hKab, hrest⟩

end Standing

/-- A smaller integer keeps the choices. -/
theorem SeqData.StandingChoices.mono {D : SeqData} {K K' : ℕ} {dm : ℝ} (hK : K' ≤ K)
    (h : D.StandingChoices K dm) : D.StandingChoices K' dm :=
  ⟨Standing.nearChoice_mono hK h.near, h.δ_lt, h.m0_ball, h.m0_small, h.as_pos, h.as_lt, h.chiY,
    h.chiF⟩

/-- The positivity facts carried by the near parameter choice. -/
theorem SeqData.StandingChoices.pos {D : SeqData} {K : ℕ} {dm : ℝ} (h : D.StandingChoices K dm) :
    0 < D.K.b ∧ D.K.b < 1 ∧ 0 < D.K.δ ∧ 0 < D.K.m0 ∧ D.K.m0 < 3 * dm / 11 ∧ 0 < D.K.C0 := by
  obtain ⟨a, Dp, -, hb, hb1, -, hδ, hm0, hm0d, -, -, -, hC0⟩ := h.near
  exact ⟨hb, hb1, hδ, hm0, hm0d, hC0⟩

/-! ## 3. The per-level facts of the exact background (the bridge of `ORG:D5/skeleton` step 3) -/

/-- **The per-level background facts of the sequence** (source 2026-2037, 2505-2524, 2664-2713,
4139-4141, 5134-5139, 5926-5950): for large `n` the level is actual (`IsActualLevel`: regime with
loss exponent in `[d₋, d₊]`, exact split with `ρ_b`, exact profile with the global pressure,
contraction-ball state, BUC train), the inlet support lies below the output cut `S = ε_n^{-b}`
(2316-2318, 3905-3912), and the repair `r_b` has the derivative bounds `P_νρ` of 5134-5139.
This is the one hypothesis that the exact-background construction supplies at every large level
(`ORG:D5/skeleton` step 3). -/
structure SeqData.StandingBridge (D : SeqData) (dm dp : ℝ) : Prop where
  actual : ∀ᶠ n : ℕ in atTop, D.IsActualLevel dm dp n
  inlet : ∀ᶠ n : ℕ in atTop, D.Sin n ≤ retEps D.Pl D.σ₀ n ^ (-D.K.b)
  repairDeriv : ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, RepairDerivBound D.K (D.level n) C k

/-- The standing hypotheses contain the per-level background facts. -/
theorem SeqData.RepairStanding.bridge {D : SeqData} {dm dp : ℝ} (h : D.RepairStanding dm dp) :
    D.StandingBridge dm dp :=
  ⟨h.actual, h.inlet, h.repairDeriv⟩

end UnforcedLeray.Short.PartIIIb.Concrete
