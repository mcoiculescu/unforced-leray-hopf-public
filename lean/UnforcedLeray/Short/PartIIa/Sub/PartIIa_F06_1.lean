import UnforcedLeray.Short.PartIIa.Sub.F06

/-!
# Part II-a, task `PartII-a:F06/1`: the quantitative body diffusion bound (decomposition)

Source of record: `the November 2 reference manuscript`, lines 1431-1441
(window estimate) and 1470-1480 (averaging over the centres, "no inverse-period factor").

`BodyLaplacianBound` is derived (`bodyLaplacianBound_of`) from:

* `GlobalFieldWindowBound` (P1): the global window Laplacian `Λ` of `F04` satisfies the window
  estimate of `LocalWindowEstimate` for every centre (by uniqueness of the weak Laplacian on a
  window, `Λ = Λ_{τ₀}` a.e. there);
* `PeriodAverageAE` (P2a) and `PeriodAverageBound` (P2b): averaging over the centres
  (`B0425.lintegral_center_average`) gives `∫₀^P∫‖Λ‖^r ≤ 2 C^r ∫₀^P (‖f‖^r + (1+|μ|)^r ‖w‖^r)`;
* `SliceIntegralYq` (P3): `∫₀^P (‖f(τ)‖^r + m^r ‖w(τ)‖^r) dτ = P (‖f‖^r + m^r ‖w‖^r)` (Haar
  normalisation of `Y_r`);
* `LaplacianFieldToYRep` (P4): the field-to-`Y_r` step of `F04`, also returning that `Λ`
  represents `a`;
* `YqRepNorm` (P5): `P ‖a‖_{Y_r}^r = ∫₀^P ∫ ‖Λ‖^r` when `a` is represented by `Λ`;
* `NormFromPower` (P6): arithmetic, `‖a‖^s ≤ 2 K^s (‖f‖^s + m^s ‖w‖^s)` gives
  `‖a‖ ≤ K' (‖f‖ + m ‖w‖)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.Short.PartIIa.Rep

/-- **P1 (global field with the window bound at every centre; lines 1470-1480).** -/
def GlobalFieldWindowBound : Prop :=
  LocalWindowEstimate → ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], 1 < r → r ≠ ⊤ → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ ν : ℝ, 0 < ν → ∀ (μ : ℂ) (f w : Yq P r),
      HasPhaseOp (fun Φ => μ • Φ + L0T ν Φ) w f → ∀ W : ℝ × Space → CVec3, IsRep w W →
        ∃ Λ : ℝ × Space → CVec3, StronglyMeasurable Λ ∧
          (∀ τ₀ : ℝ, IsWindowLaplacian ν τ₀ W Λ) ∧
          (∀ᵐ τ : ℝ, (fun y => Λ (τ + P, y)) =ᵐ[volume] fun y => Λ (τ, y)) ∧
          ∀ τ₀ : ℝ, ∫⁻ τ in Ioo (τ₀ - 1) (τ₀ + 1), ∫⁻ y, ‖Λ (τ, y)‖ₑ ^ r.toReal ≤
            ENNReal.ofReal C ^ r.toReal * ∫⁻ τ in Ioo (τ₀ - 2) (τ₀ + 2),
              (‖f (τ : AddCircle P)‖ₑ ^ r.toReal +
                ENNReal.ofReal (1 + ‖μ‖) ^ r.toReal * ‖w (τ : AddCircle P)‖ₑ ^ r.toReal)

/-- **P2a (centre averaging for a.e.-periodic densities).** `B0425.lintegral_center_average`
without everywhere-periodicity or measurability: `h` a.e. measurable and a.e. `P`-periodic
(`∀ᵐ τ, h (τ + P) = h τ`). (Replace `h` by `τ ↦ h'(τ - P ⌊τ/P⌋)` for a measurable `h' =ᵐ h`, or by
the `P`-periodisation; the two sides only see `h` a.e.) -/
def PeriodAverageAE : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ h : ℝ → ℝ≥0∞, AEMeasurable h volume → (∀ᵐ τ : ℝ, h (τ + P) = h τ) →
    ∀ I : Set ℝ, MeasurableSet I →
      ∫⁻ τ₀ in Ioc 0 P, ∫⁻ t in I, h (τ₀ + t) = volume I * ∫⁻ τ in Ioc 0 P, h τ

/-- **P2b (averaging the window bound over the centres, lines 1470-1480).** If `Λ` is strongly
measurable and a.e. `P`-periodic in `τ` and satisfies the window bound at every centre `τ₀`,
against the (periodic) right side of `f, w ∈ Y_r`, then
`∫₀^P ∫ ‖Λ‖^r ≤ 2 C^r ∫₀^P (right side)`: apply P2a to `g(τ) = ∫⁻ y, ‖Λ(τ,y)‖^r` with
`I = (-1,1)` (`|I| = 2`) and to the right side with `I = (-2,2)` (`|I| = 4`), then swap with
`lintegral_lintegral_swap`/`lintegral_mono`. -/
def PeriodAverageBound : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → ∀ (P : ℝ) [Fact (0 < P)] (C : ℝ) (μ : ℂ) (f w : Yq P r)
    (Λ : ℝ × Space → CVec3), StronglyMeasurable Λ →
    (∀ᵐ τ : ℝ, (fun y => Λ (τ + P, y)) =ᵐ[volume] fun y => Λ (τ, y)) →
    (∀ τ₀ : ℝ, ∫⁻ τ in Ioo (τ₀ - 1) (τ₀ + 1), ∫⁻ y, ‖Λ (τ, y)‖ₑ ^ r.toReal ≤
      ENNReal.ofReal C ^ r.toReal * ∫⁻ τ in Ioo (τ₀ - 2) (τ₀ + 2),
        (‖f (τ : AddCircle P)‖ₑ ^ r.toReal +
          ENNReal.ofReal (1 + ‖μ‖) ^ r.toReal * ‖w (τ : AddCircle P)‖ₑ ^ r.toReal)) →
      ∫⁻ τ in Ioc 0 P, ∫⁻ y, ‖Λ (τ, y)‖ₑ ^ r.toReal ≤
        2 * ENNReal.ofReal C ^ r.toReal * ∫⁻ τ in Ioc 0 P,
          (‖f (τ : AddCircle P)‖ₑ ^ r.toReal +
            ENNReal.ofReal (1 + ‖μ‖) ^ r.toReal * ‖w (τ : AddCircle P)‖ₑ ^ r.toReal)

/-- **P3 (period integral of slice norms is `P` times the `Y_r` norm).** The `Y_r` norm is the
`L^r` norm for the Haar probability measure on `AddCircle P` (`lintegral_enorm_rpow_Yq` of
`Lib/PhaseSpace/Charts.lean`); `∫_{Ioc 0 P} G(τ) dτ = P ∫ G(↑τ) d haar` for the circle measure
(`AddCircle.volume_eq_smul_haarAddCircle`, `AddCircle.lintegral_preimage`). -/
def SliceIntegralYq : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → ∀ (P : ℝ) [Fact (0 < P)] (μ : ℂ) (f w : Yq P r),
    ∫⁻ τ in Ioc 0 P, (‖f (τ : AddCircle P)‖ₑ ^ r.toReal +
        ENNReal.ofReal (1 + ‖μ‖) ^ r.toReal * ‖w (τ : AddCircle P)‖ₑ ^ r.toReal) =
      ENNReal.ofReal P * (‖f‖ₑ ^ r.toReal +
        ENNReal.ofReal (1 + ‖μ‖) ^ r.toReal * ‖w‖ₑ ^ r.toReal)

/-- **P4 (`LaplacianFieldToY`, with the representative).** As `LaplacianFieldToY`
(`Sub/PartIIa_F04.lean`, proved as `laplacianFieldToY` by `laplacianFieldToY_of` from the five
leaves `periodicFieldToYq_proof`, ...) but the produced `a` also represents `Λ`: `IsRep a Λ`.
Proof: copy the proof of `laplacianFieldToY_of` (`Sub/PartIIa_F04_2.lean`), which already
obtains `a` with `IsRep a Λ` from `PeriodicFieldToYq`. -/
def LaplacianFieldToYRep : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → ∀ (P : ℝ) [Fact (0 < P)] (ν : ℝ) (w : Yq P r)
    (W : ℝ × Space → CVec3), IsRep w W → ∀ Λ : ℝ × Space → CVec3, StronglyMeasurable Λ →
      (∀ τ₀ : ℝ, IsWindowLaplacian ν τ₀ W Λ) →
      (∀ᵐ τ : ℝ, (fun y => Λ (τ + P, y)) =ᵐ[volume] fun y => Λ (τ, y)) →
      ∫⁻ τ in Ioc 0 P, ∫⁻ y, ‖Λ (τ, y)‖ₑ ^ r.toReal < ⊤ →
        ∃ a : Yq P r, IsRep a Λ ∧ HasPhaseOp (nuLapT ν) w a

/-- **P5 (norm of a represented element).** `a ∈ Y_r` represented by `Λ` has
`P ‖a‖^r = ∫₀^P ∫ ‖Λ‖^r` (as P3, with `lintegral_rep` of `Sub/F03Rep.lean`/`IsRep`). -/
def YqRepNorm : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → ∀ (P : ℝ) [Fact (0 < P)] (a : Yq P r)
    (Λ : ℝ × Space → CVec3), IsRep a Λ →
      ENNReal.ofReal P * ‖a‖ₑ ^ r.toReal = ∫⁻ τ in Ioc 0 P, ∫⁻ y, ‖Λ (τ, y)‖ₑ ^ r.toReal

/-- **P6 (from a power bound to a norm bound).** For `s > 1` and `K ≥ 0` there is `K' ≥ 0` with:
`a^s ≤ 2 K^s (f^s + m^s w^s)` (in `ℝ≥0∞`, via `ofReal` of nonnegative reals) implies
`a ≤ K' (f + m w)`. (Take `K' = 2K`: `(x+y)^{1/s} ≤ x^{1/s} + y^{1/s}` and `2^{1/s} ≤ 2`;
`ENNReal.rpow_le_rpow_iff`, `ENNReal.rpow_add_le...`/`Real.add_rpow_le_rpow_add`.) -/
def NormFromPower : Prop :=
  ∀ s : ℝ, 1 < s → ∀ K : ℝ, 0 ≤ K → ∃ K' : ℝ, 0 ≤ K' ∧ ∀ a f w m : ℝ, 0 ≤ a → 0 ≤ f → 0 ≤ w → 0 ≤ m →
    ENNReal.ofReal a ^ s ≤
      2 * ENNReal.ofReal K ^ s * (ENNReal.ofReal f ^ s + ENNReal.ofReal m ^ s * ENNReal.ofReal w ^ s) →
      a ≤ K' * (f + m * w)

/-- `BodyLaplacianBound` from the leaves (given the local window estimate). -/
theorem bodyLaplacianBound_of (hloc : LocalWindowEstimate) (h1 : GlobalFieldWindowBound)
    (h2 : PeriodAverageBound) (h3 : SliceIntegralYq) (h4 : LaplacianFieldToYRep)
    (h5 : YqRepNorm) (h6 : NormFromPower) : BodyLaplacianBound := by
  intro r _ hr1 hr3
  have hrt : r ≠ ⊤ := ne_top_of_lt hr3
  obtain ⟨C, hC0, hC⟩ := h1 hloc r hr1 hrt
  have hs : 1 < r.toReal := by
    have := (ENNReal.toReal_lt_toReal (by simp) hrt).2 hr1
    simpa using this
  obtain ⟨K', hK0, hK'⟩ := h6 r.toReal hs C hC0
  refine ⟨K', hK0, ?_⟩
  intro P _ hP ν hν μ f w hf
  obtain ⟨W, hW⟩ := exists_isRep hrt w
  obtain ⟨Λ, hm, hwin, hper, hbd⟩ := hC P hP ν hν μ f w hf W hW
  have hav := h2 r hrt P C μ f w Λ hm hper hbd
  have hP3 := h3 r hrt P μ f w
  set R : ℝ≥0∞ := ‖f‖ₑ ^ r.toReal +
    ENNReal.ofReal (1 + ‖μ‖) ^ r.toReal * ‖w‖ₑ ^ r.toReal with hR
  have hRtop : R < ⊤ := by
    rw [hR]
    exact ENNReal.add_lt_top.2 ⟨ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg
        enorm_ne_top, ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg
        ENNReal.ofReal_ne_top) (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg
        enorm_ne_top)⟩
  have hfin : ∫⁻ τ in Ioc 0 P, ∫⁻ y, ‖Λ (τ, y)‖ₑ ^ r.toReal < ⊤ := by
    refine lt_of_le_of_lt hav ?_
    rw [hP3]
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) (ENNReal.rpow_lt_top_of_nonneg
      ENNReal.toReal_nonneg ENNReal.ofReal_ne_top)) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hRtop)
  obtain ⟨a, haR, haOp⟩ := h4 r hrt P ν w W hW Λ hm hwin hper hfin
  refine ⟨a, haOp, ?_⟩
  have h5' := h5 r hrt P a Λ haR
  have key : ‖a‖ₑ ^ r.toReal ≤ 2 * ENNReal.ofReal C ^ r.toReal * R := by
    have hle : ENNReal.ofReal P * ‖a‖ₑ ^ r.toReal ≤
        ENNReal.ofReal P * (2 * ENNReal.ofReal C ^ r.toReal * R) := by
      rw [h5']
      calc _ ≤ 2 * ENNReal.ofReal C ^ r.toReal * (ENNReal.ofReal P * R) := by
            rw [← hP3]; exact hav
        _ = _ := by ring
    exact (ENNReal.mul_le_mul_iff_right
      (by simpa using Fact.out (p := 0 < P)) ENNReal.ofReal_ne_top).1 hle
  have := hK' ‖a‖ ‖f‖ ‖w‖ (1 + ‖μ‖) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (by positivity)
  refine this ?_
  simp only [ofReal_norm]
  exact key

end UnforcedLeray.Short.PartIIa
