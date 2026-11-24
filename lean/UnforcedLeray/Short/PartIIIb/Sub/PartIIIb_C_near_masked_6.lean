import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Lemmas

/-!
# Sub-lemmas for `PartIII-b:C/near/masked/6` (`TensorTestDense`, source 1678)

Smooth tensor tests are dense in `H_T = L²(measureHT c)` ("the tensor map means completion from
smooth tensors").  Route:

* `SmoothCellDense` : `F ∈ H_T` is approximated by smooth `M` whose support lies in a compact box
  `s ∈ [s₀, s₁]`, `q ∈ (a, b) ⊂ (0, c)`, `|η| ≤ L` (`s₀ > 0`); the density `s^{-1/2}` is locally
  bounded there, so this is the standard density of `C_c^∞` of an open set in `L²`, after
  multiplying by `s^{1/4}`.
* `PeriodizeIsTensorTest` : the `q`-periodization of such an `M` is a tensor test (smooth because
  `M` vanishes near `q = 0` and `q = c`; periodic by construction; the band is inherited).
* `periodize_ae_measureHT` (proved here) : on the cell `reduceIoc c q = q`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

/-- **Density with support in the open cell** (source 1678): approximants are smooth, band
supported, with `q`-support in a compact subinterval of `(0, c)`. -/
def SmoothCellDense : Prop :=
  ∀ c : ℝ, 0 < c → ∀ (F : UnforcedLeray.Short.PartIIa.HTSpace c) (ε : ℝ), 0 < ε →
    ∃ M : UnforcedLeray.B0220.Profile → UnforcedLeray.Short.PartIIa.TensorVal,
      ContDiff ℝ ∞ M ∧
      (∃ s0 s1 L : ℝ, 0 < s0 ∧ ∀ p, M p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) ∧
      (∃ a b : ℝ, 0 < a ∧ a < b ∧ b < c ∧ ∀ p, M p ≠ 0 → p.2.1 ∈ Ioo a b) ∧
      ∃ hM : MemLp M 2 (UnforcedLeray.Short.PartIIa.measureHT c), ‖F - hM.toLp M‖ < ε

/-- **Periodization of a `q`-compactly supported smooth band function is a tensor test**
(smooth: near `q ∈ cℤ` the periodization vanishes, elsewhere it is a translate of `g`). -/
def PeriodizeIsTensorTest : Prop :=
  ∀ c : ℝ, 0 < c → ∀ g : UnforcedLeray.B0220.Profile → UnforcedLeray.Short.PartIIa.TensorVal,
    ContDiff ℝ ∞ g →
    (∃ s0 s1 L : ℝ, 0 < s0 ∧ ∀ p, g p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) →
    (∃ a b : ℝ, 0 < a ∧ a < b ∧ b < c ∧ ∀ p, g p ≠ 0 → p.2.1 ∈ Ioo a b) →
    UnforcedLeray.Short.PartIIa.IsTensorTest c (UnforcedLeray.B0220.periodize c g)

/-- On the cell `reduceIoc c q = q`, so the periodization agrees a.e. with `g`. -/
theorem periodize_ae_measureHT {c : ℝ} (hc : 0 < c)
    (g : UnforcedLeray.B0220.Profile → UnforcedLeray.Short.PartIIa.TensorVal) :
    UnforcedLeray.B0220.periodize c g =ᵐ[UnforcedLeray.Short.PartIIa.measureHT c] g := by
  have hac : UnforcedLeray.Short.PartIIa.measureHT c ≪ UnforcedLeray.B0220.cellMeasure c :=
    withDensity_absolutelyContinuous _ _
  have hmem : ∀ᵐ p ∂(UnforcedLeray.B0220.cellMeasure c), p ∈ UnforcedLeray.B0220.cell c :=
    ae_restrict_mem (UnforcedLeray.B0220.measurableSet_cell c)
  filter_upwards [hac hmem] with p hp
  exact UnforcedLeray.B0220.periodize_of_mem hc g hp

/-- `TensorTestDense` from the two leaves. -/
theorem tensorTestDense_of (h1 : SmoothCellDense) (h2 : PeriodizeIsTensorTest) :
    TensorTestDense := by
  intro c hc F η hη
  obtain ⟨M, hsm, hband, hq, hM, hlt⟩ := h1 c hc F η hη
  have hM' : MemLp (UnforcedLeray.B0220.periodize c M) 2
      (UnforcedLeray.Short.PartIIa.measureHT c) := hM.ae_eq (periodize_ae_measureHT hc M).symm
  refine ⟨UnforcedLeray.B0220.periodize c M, h2 c hc M hsm hband hq, hM', ?_⟩
  rw [MemLp.toLp_congr hM' hM (periodize_ae_measureHT hc M)]
  exact hlt

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
