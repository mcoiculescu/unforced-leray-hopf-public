import UnforcedLeray.Short.PartIIa.Sub.F03
import UnforcedLeray.Short.PartIIa.Tasks.F03aWindowEquation
import UnforcedLeray.Short.PartIIa.Tasks.F03bWindowNorms
import UnforcedLeray.Short.PartIIa.Tasks.F03cWindowBackEquation
import UnforcedLeray.Short.PartIIa.Tasks.F03dWindowBackNorm
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F06_1
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F04_1
import UnforcedLeray.Short.PartIIa.Tasks.F04aGlobalField.WindowLapAEMeas
import UnforcedLeray.Short.PartIIa.Tasks.F04aGlobalField.WindowLapLocInt
import UnforcedLeray.Short.PartIIa.Tasks.F04aGlobalField.WindowRhsFinite
import UnforcedLeray.Short.PartIIa.Tasks.F04aGlobalField.WindowLapUnique
import UnforcedLeray.Short.PartIIa.Tasks.F04aGlobalField.WindowLapGlue
import UnforcedLeray.Short.PartIIa.Tasks.F04aGlobalField.WindowLapPoU
import UnforcedLeray.Short.PartIIa.Tasks.F04aGlobalField.WindowLapPeriodic
import UnforcedLeray.Short.PartIIa.Tasks.F06aBodyLaplacian.PeriodAverageBound
import UnforcedLeray.Short.PartIIa.Tasks.F06aBodyLaplacian.SliceIntegralYq
import UnforcedLeray.Short.PartIIa.Tasks.F06aBodyLaplacian.LaplacianFieldToYRep
import UnforcedLeray.Short.PartIIa.Tasks.F06aBodyLaplacian.YqRepNorm
import UnforcedLeray.Short.PartIIa.Tasks.F06aBodyLaplacian.NormFromPower

/-!
# Part II-a, `PartII-a:F14/1/1/org`: the body graph bound for every period `P > 0`

Source of record: `the November 2 reference manuscript`, lines 1356-1366
(lemma `bg:common-body-graph`, "All these estimates are independent of `P`") and the proof
1426-1443 (fixed window `|t| < 2`, averaging over the centres "with no inverse-period factor").

`D2CoreDense` (`Sub/F14_1.lean`) is stated for every period `P > 0`, while the proved
`CommonBodyGraphBound` and its chain (`LocalWindowEstimate`, `GlobalFieldWindowBound`,
`BodyLaplacianBound`) carry the paper's standing assumption `P ≤ 1`. None of those proofs uses
`P ≤ 1`: it is only passed along. This file re-runs the same proofs without it:

* `localWindowEstimateAllP`: copy of `localWindowEstimate_of` (`Sub/F03.lean`) applied to the
  proved leaves `windowEquation`, `windowNorms`, `windowBackEquation`, `windowBackNorm`;
* `globalFieldWindowBoundAllP`: copy of `globalFieldWindowBound`
  (`Tasks/F06aBodyLaplacian/GlobalFieldWindowBound.lean`);
* `bodyLaplacianBoundAllP`: copy of `bodyLaplacianBound_of` (`Sub/PartIIa_F06_1.lean`) with the
  proved leaves `periodAverageBound`, `sliceIntegralYq`, `laplacianFieldToYRep`, `yqRepNorm`,
  `normFromPower`;
* `bodyGraphBoundAllP`: the graph-norm part of `commonBodyGraphBound_of` (`Sub/F06.lean`):
  `‖w‖_{D_r} ≤ C_r [1 + (1+|μ|)/a_r] ‖(μ+L)w‖_{Y_r}`.

All four are proved here; nothing in this file is conditional.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.Parabolic
  UnforcedLeray.Short.PartIIa.Rep

/-- `LocalWindowEstimate` (`Sub/F03.lean`, lines 1426-1436) for every period `P > 0`. -/
def LocalWindowEstimateAllP : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], 1 < r → r ≠ ⊤ → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (P : ℝ) [Fact (0 < P)], ∀ ν : ℝ, 0 < ν → ∀ (μ : ℂ) (f w : Yq P r),
      HasPhaseOp (fun Φ => μ • Φ + L0T ν Φ) w f → ∀ W : ℝ × Space → CVec3, IsRep w W →
        ∀ τ₀ : ℝ, ∃ Λ : ℝ × Space → CVec3, IsWindowLaplacian ν τ₀ W Λ ∧
          ∫⁻ τ in Ioo (τ₀ - 1) (τ₀ + 1), ∫⁻ y, ‖Λ (τ, y)‖ₑ ^ r.toReal ≤
            ENNReal.ofReal C ^ r.toReal * ∫⁻ τ in Ioo (τ₀ - 2) (τ₀ + 2),
              (‖f (τ : AddCircle P)‖ₑ ^ r.toReal +
                ENNReal.ofReal (1 + ‖μ‖) ^ r.toReal * ‖w (τ : AddCircle P)‖ₑ ^ r.toReal)

/-- `GlobalFieldWindowBound` (`Sub/PartIIa_F06_1.lean`, lines 1437-1443) for every period. -/
def GlobalFieldWindowBoundAllP : Prop :=
  LocalWindowEstimateAllP → ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], 1 < r → r ≠ ⊤ → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (P : ℝ) [Fact (0 < P)], ∀ ν : ℝ, 0 < ν → ∀ (μ : ℂ) (f w : Yq P r),
      HasPhaseOp (fun Φ => μ • Φ + L0T ν Φ) w f → ∀ W : ℝ × Space → CVec3, IsRep w W →
        ∃ Λ : ℝ × Space → CVec3, StronglyMeasurable Λ ∧
          (∀ τ₀ : ℝ, IsWindowLaplacian ν τ₀ W Λ) ∧
          (∀ᵐ τ : ℝ, (fun y => Λ (τ + P, y)) =ᵐ[volume] fun y => Λ (τ, y)) ∧
          ∀ τ₀ : ℝ, ∫⁻ τ in Ioo (τ₀ - 1) (τ₀ + 1), ∫⁻ y, ‖Λ (τ, y)‖ₑ ^ r.toReal ≤
            ENNReal.ofReal C ^ r.toReal * ∫⁻ τ in Ioo (τ₀ - 2) (τ₀ + 2),
              (‖f (τ : AddCircle P)‖ₑ ^ r.toReal +
                ENNReal.ofReal (1 + ‖μ‖) ^ r.toReal * ‖w (τ : AddCircle P)‖ₑ ^ r.toReal)

/-- `BodyLaplacianBound` (`Sub/F06.lean`, lines 1426-1443) for every period `P > 0`. -/
def BodyLaplacianBoundAllP : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], 1 < r → r < 3 → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (P : ℝ) [Fact (0 < P)], ∀ ν : ℝ, 0 < ν → ∀ (μ : ℂ) (f w : Yq P r),
      HasPhaseOp (fun Φ => μ • Φ + L0T ν Φ) w f →
        ∃ a : Yq P r, HasPhaseOp (nuLapT ν) w a ∧ ‖a‖ ≤ C * (‖f‖ + (1 + ‖μ‖) * ‖w‖)

/-- **The body graph bound for every period** (lines 1356-1366, "independent of `P`"): for
`1 < r < 3` there is `C` with `‖w‖_{D_r} ≤ C [1 + (1+|μ|)/a_r] ‖(μ+L)w‖_{Y_r}` for all `P > 0`,
`ν > 0`, `a_r = Re μ + γ_r > 0`, `w ∈ D_r`. -/
def BodyGraphBoundAllP : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], 1 < r → r < 3 → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (P : ℝ) [Fact (0 < P)], ∀ ν : ℝ, 0 < ν → ∀ μ : ℂ, 0 < μ.re + gammaR r →
      ∀ w : D P ν r,
        graphNormD w ≤ C * (1 + (1 + ‖μ‖) / (μ.re + gammaR r)) * ‖bodyOp P ν r μ w‖

/-- Copy of `localWindowEstimate_of` (`Sub/F03.lean`) without `P ≤ 1`, from the proved leaves. -/
theorem localWindowEstimateAllP : LocalWindowEstimateAllP := by
  have h1 := windowEquation
  have h2 := windowNorms
  have h3 := windowBackEquation
  have h4 := windowBackNorm
  intro r _ hr1 hrt
  have hq : 1 < r.toReal := by
    have := ENNReal.toReal_strict_mono hrt hr1
    simpa using this
  have hq0 : 0 ≤ r.toReal := by linarith
  obtain ⟨χ, hχ⟩ := windowCutoff_exists
  obtain ⟨K, hK0, hK⟩ := h2 r hr1 hrt χ hχ
  obtain ⟨K', hK'0, hK'⟩ := h4 r.toReal hq
  obtain ⟨Ch, hCh⟩ := B0423.heat_estimate_complex_laplacian (d := 3) hq
  set q := r.toReal with hqdef
  have h3pos : (0 : ℝ) ≤ (3 : ℝ) ^ (1 / q) := by positivity
  refine ⟨(3 : ℝ) ^ (1 / q) * K' * Ch * K, by positivity, ?_⟩
  intro P _ ν hν μ f w hw W hW τ₀
  obtain ⟨Fr, hFr⟩ := exists_isRep hrt f
  have heq := h1 r hrt P ν μ f w hw W Fr hW hFr χ hχ τ₀
  have hmem := fun c => hK P μ f w W Fr hW hFr τ₀ c
  have hheat := fun c => hCh ν hν (windowField χ τ₀ W c) (windowForce μ χ τ₀ W Fr c)
    (hmem c).1 (hmem c).2.1 (heq c)
  choose D2 Dt hD2 hDt hDtw hb hbt using hheat
  refine ⟨windowLap ν τ₀ fun c X => ∑ i, D2 c i i X,
    h3 r hrt P ν w W hW χ hχ τ₀ D2 fun c i j => hD2 c i j, ?_⟩
  set R : ℝ≥0∞ := ∫⁻ τ in Ioo (τ₀ - 2) (τ₀ + 2),
    (‖f (τ : AddCircle P)‖ₑ ^ q + ENNReal.ofReal (1 + ‖μ‖) ^ q * ‖w (τ : AddCircle P)‖ₑ ^ q)
    with hR
  have hmeas : ∀ c, AEStronglyMeasurable (fun X : PS 3 => ∑ i, D2 c i i X) volume := fun c =>
    Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hD2 c i i).1.1
  refine (hK' ν τ₀ (fun c X => ∑ i, D2 c i i X) hmeas).trans ?_
  have hterm : ∀ c, eLpNorm (fun X : PS 3 => (ν : ℂ) * ∑ i, D2 c i i X) (ENNReal.ofReal q)
      volume ^ q ≤ (Ch : ℝ≥0∞) ^ q * (ENNReal.ofReal K ^ q * R) := fun c => by
    calc eLpNorm (fun X : PS 3 => (ν : ℂ) * ∑ i, D2 c i i X) (ENNReal.ofReal q) volume ^ q
        ≤ ((Ch : ℝ≥0∞) * eLpNorm (windowForce μ χ τ₀ W Fr c) (ENNReal.ofReal q) volume) ^ q :=
          ENNReal.rpow_le_rpow (hb c) hq0
      _ = (Ch : ℝ≥0∞) ^ q * eLpNorm (windowForce μ χ τ₀ W Fr c) (ENNReal.ofReal q) volume ^ q :=
          ENNReal.mul_rpow_of_nonneg _ _ hq0
      _ ≤ (Ch : ℝ≥0∞) ^ q * (ENNReal.ofReal K ^ q * R) :=
          mul_le_mul' le_rfl (hmem c).2.2
  have hsum : ∑ c : Fin 3, eLpNorm (fun X : PS 3 => (ν : ℂ) * ∑ i, D2 c i i X)
      (ENNReal.ofReal q) volume ^ q ≤ 3 * ((Ch : ℝ≥0∞) ^ q * (ENNReal.ofReal K ^ q * R)) := by
    calc ∑ c : Fin 3, eLpNorm (fun X : PS 3 => (ν : ℂ) * ∑ i, D2 c i i X)
          (ENNReal.ofReal q) volume ^ q
        ≤ ∑ _c : Fin 3, (Ch : ℝ≥0∞) ^ q * (ENNReal.ofReal K ^ q * R) :=
          Finset.sum_le_sum fun c _ => hterm c
      _ = 3 * ((Ch : ℝ≥0∞) ^ q * (ENNReal.ofReal K ^ q * R)) := by
          simp [Finset.sum_const]
  refine (mul_le_mul' le_rfl hsum).trans (le_of_eq ?_)
  have hC : ENNReal.ofReal ((3 : ℝ) ^ (1 / q) * K' * Ch * K) ^ q =
      ENNReal.ofReal K' ^ q * (3 * ((Ch : ℝ≥0∞) ^ q * ENNReal.ofReal K ^ q)) := by
    have h1' : ENNReal.ofReal ((3 : ℝ) ^ (1 / q) * K' * Ch * K) =
        ENNReal.ofReal ((3 : ℝ) ^ (1 / q)) * ENNReal.ofReal K' * (Ch : ℝ≥0∞) *
          ENNReal.ofReal K := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_mul h3pos, ENNReal.ofReal_coe_nnreal]
    rw [h1', ENNReal.mul_rpow_of_nonneg _ _ hq0, ENNReal.mul_rpow_of_nonneg _ _ hq0,
      ENNReal.mul_rpow_of_nonneg _ _ hq0, ENNReal.ofReal_rpow_of_nonneg h3pos hq0,
      ← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ (by linarith), Real.rpow_one]
    have h33 : ENNReal.ofReal (3 : ℝ) = 3 := by simp
    rw [h33]
    ring
  rw [hC]
  ring

/-- Copy of `globalFieldWindowBound` (`Tasks/F06aBodyLaplacian/GlobalFieldWindowBound.lean`)
without `P ≤ 1`. -/
theorem globalFieldWindowBoundAllP : GlobalFieldWindowBoundAllP := by
  intro hloc r _ hr1 hrt
  obtain ⟨C, hC0, hC⟩ := hloc r hr1 hrt
  refine ⟨C, hC0, ?_⟩
  intro P hP ν hν μ f w hf W hW
  have hCP := hC P ν hν μ f w hf W hW
  choose Λk hΛk hbd using fun k : ℤ => hCP (k : ℝ)
  have hfin2 : ∀ k : ℤ, ∫⁻ τ in Ioo ((k : ℝ) - 1) ((k : ℝ) + 1), ∫⁻ y, ‖Λk k (τ, y)‖ₑ ^ r.toReal
      < ⊤ := by
    intro k
    refine lt_of_le_of_lt (hbd k) (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg
      ENNReal.toReal_nonneg ENNReal.ofReal_ne_top) (windowRhsFinite r hrt P μ f w (k : ℝ)))
  have hmeas : ∀ k : ℤ, AEStronglyMeasurable (Λk k) (volume.restrict (winSet (k : ℝ))) :=
    fun k => windowLapAEMeas ν (k : ℝ) W (Λk k) (hΛk k)
  have hli : ∀ k : ℤ, LocallyIntegrableOn (Λk k) (winSet (k : ℝ)) :=
    fun k => windowLapLocInt r hrt _ _ (Λk k) (hmeas k) (hfin2 k)
  have hover : ∀ k l : ℤ, Λk k =ᵐ[volume.restrict (winSet (k : ℝ) ∩ winSet (l : ℝ))] Λk l := by
    intro k l
    have hset : winSet (k : ℝ) ∩ winSet (l : ℝ) =
        Ioo (max ((k : ℝ) - 1) ((l : ℝ) - 1)) (min ((k : ℝ) + 1) ((l : ℝ) + 1)) ×ˢ
          (univ : Set Space) := by
      unfold winSet
      rw [Set.prod_inter_prod, Set.inter_univ, Set.Ioo_inter_Ioo]
    rw [hset]
    exact windowLapUnique ν k l _ _ W (Λk k) (Λk l) (le_max_left _ _) (min_le_left _ _)
      (le_max_right _ _) (min_le_right _ _) (hΛk k) (hΛk l)
      ((hli k).mono_set (by rw [← hset]; exact Set.inter_subset_left))
      ((hli l).mono_set (by rw [← hset]; exact Set.inter_subset_right))
  obtain ⟨Λ, hΛm, hΛeq⟩ := windowLapGlue Λk hmeas hover
  have hwin : ∀ τ₀ : ℝ, IsWindowLaplacian ν τ₀ W Λ := windowLapPoU ν W Λ Λk hΛk hΛeq
  have hli' : ∀ k : ℤ, LocallyIntegrableOn Λ (winSet (k : ℝ)) :=
    fun k => (hli k).congr (hΛeq k).symm
  have hWper : ∀ᵐ τ : ℝ, (fun y => W (τ + P, y)) =ᵐ[volume] fun y => W (τ, y) := by
    filter_upwards [hW.slice, hW.slice_shift P] with t h1 h2
    have e : ((P + t : ℝ) : AddCircle P) = (t : AddCircle P) := by
      rw [add_comm]; exact AddCircle.coe_add_period P t
    rw [e] at h2
    rw [add_comm t P]
    exact h2.trans h1.symm
  have hperΛ : ∀ᵐ τ : ℝ, (fun y => Λ (τ + P, y)) =ᵐ[volume] fun y => Λ (τ, y) :=
    windowLapPeriodic_of windowLapUnique P ν hP.out W Λ hW.meas hΛm hWper hwin hli'
  have hcongrW : ∀ (a b : ℝ) (Λ₁ Λ₂ : ℝ × Space → CVec3),
      Λ₁ =ᵐ[volume.restrict (Ioo a b ×ˢ (univ : Set Space))] Λ₂ →
      ∫⁻ τ in Ioo a b, ∫⁻ y, ‖Λ₁ (τ, y)‖ₑ ^ r.toReal =
        ∫⁻ τ in Ioo a b, ∫⁻ y, ‖Λ₂ (τ, y)‖ₑ ^ r.toReal := by
    intro a b Λ₁ Λ₂ h
    have h' : Λ₁ =ᵐ[((volume : Measure ℝ).restrict (Ioo a b)).prod (volume : Measure Space)] Λ₂ := by
      rw [Measure.restrict_prod_eq_prod_univ]; exact h
    apply lintegral_congr_ae
    filter_upwards [Measure.ae_ae_of_ae_prod h'] with τ hτ
    apply lintegral_congr_ae
    filter_upwards [hτ] with y hy
    rw [hy]
  have hfinW : ∀ k : ℤ, ∫⁻ τ in Ioo ((k : ℝ) - 1) ((k : ℝ) + 1), ∫⁻ y, ‖Λ (τ, y)‖ₑ ^ r.toReal < ⊤ := by
    intro k
    rw [hcongrW ((k : ℝ) - 1) ((k : ℝ) + 1) Λ (Λk k) (hΛeq k)]
    exact hfin2 k
  have hLIΛ : ∀ τ₀ : ℝ, LocallyIntegrableOn Λ (Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space)) := by
    intro τ₀
    apply windowLapLocInt r hrt (τ₀ - 1) (τ₀ + 1) Λ hΛm.aestronglyMeasurable
    have hk1 := Int.floor_le τ₀
    have hk2 := Int.lt_floor_add_one τ₀
    have hsub : Ioo (τ₀ - 1) (τ₀ + 1) ⊆
        Ioo (((⌊τ₀⌋ : ℤ) : ℝ) - 1) (((⌊τ₀⌋ : ℤ) : ℝ) + 1) ∪
          Ioo ((((⌊τ₀⌋ + 1 : ℤ)) : ℝ) - 1) ((((⌊τ₀⌋ + 1 : ℤ)) : ℝ) + 1) := by
      intro t ht
      simp only [Set.mem_union, Set.mem_Ioo, Int.cast_add, Int.cast_one] at ht ⊢
      by_cases hkt : t < ((⌊τ₀⌋ : ℤ) : ℝ) + 1
      · left
        constructor <;> linarith [ht.1, ht.2]
      · right
        push_neg at hkt
        constructor <;> linarith [ht.1, ht.2]
    refine lt_of_le_of_lt (lintegral_mono_set hsub) ?_
    refine lt_of_le_of_lt (lintegral_union_le _ _ _) ?_
    exact ENNReal.add_lt_top.2 ⟨hfinW _, hfinW _⟩
  refine ⟨Λ, hΛm, hwin, hperΛ, ?_⟩
  intro τ₀
  obtain ⟨Λ₀, hΛ₀, hbd₀⟩ := hCP τ₀
  have hli₀ : LocallyIntegrableOn Λ₀ (Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space)) := by
    refine windowLapLocInt r hrt (τ₀ - 1) (τ₀ + 1) Λ₀ (windowLapAEMeas ν τ₀ W Λ₀ hΛ₀) ?_
    exact lt_of_le_of_lt hbd₀ (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg
      ENNReal.toReal_nonneg ENNReal.ofReal_ne_top) (windowRhsFinite r hrt P μ f w τ₀))
  have hae : Λ =ᵐ[volume.restrict (Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space))] Λ₀ :=
    windowLapUnique ν τ₀ τ₀ (τ₀ - 1) (τ₀ + 1) W Λ Λ₀ le_rfl le_rfl le_rfl le_rfl (hwin τ₀) hΛ₀
      (hLIΛ τ₀) hli₀
  rw [hcongrW (τ₀ - 1) (τ₀ + 1) Λ Λ₀ hae]
  exact hbd₀

/-- Copy of `bodyLaplacianBound_of` (`Sub/PartIIa_F06_1.lean`) without `P ≤ 1`, from the proved
leaves. -/
theorem bodyLaplacianBoundAllP : BodyLaplacianBoundAllP := by
  have hloc := localWindowEstimateAllP
  have h1 := globalFieldWindowBoundAllP
  have h2 := periodAverageBound
  have h3 := sliceIntegralYq
  have h4 := laplacianFieldToYRep
  have h5 := yqRepNorm
  have h6 := normFromPower
  intro r _ hr1 hr3
  have hrt : r ≠ ⊤ := ne_top_of_lt hr3
  obtain ⟨C, hC0, hC⟩ := h1 hloc r hr1 hrt
  have hs : 1 < r.toReal := by
    have := (ENNReal.toReal_lt_toReal (by simp) hrt).2 hr1
    simpa using this
  obtain ⟨K', hK0, hK'⟩ := h6 r.toReal hs C hC0
  refine ⟨K', hK0, ?_⟩
  intro P _ ν hν μ f w hf
  obtain ⟨W, hW⟩ := exists_isRep hrt w
  obtain ⟨Λ, hm, hwin, hper, hbd⟩ := hC P ν hν μ f w hf W hW
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

/-- **The body graph bound for every period** (copy of the graph-norm part of
`commonBodyGraphBound_of`, `Sub/F06.lean`, from `bodyLaplacianBoundAllP`). -/
theorem bodyGraphBoundAllP : BodyGraphBoundAllP := by
  intro r _ h1 h3
  obtain ⟨C, hC0, hC⟩ := bodyLaplacianBoundAllP r h1 h3
  refine ⟨7 / 2 + 6 * C, by positivity, ?_⟩
  intro P _ ν hν μ hμ w
  set a : ℝ := μ.re + gammaR r with ha
  set f : Yq P r := bodyOp P ν r μ w with hf
  have hw : HasPhaseOp (fun Φ => μ • Φ + L0T ν Φ) (w : Yq P r) f :=
    hasPhaseOp_body_of_D w
  obtain ⟨Rm, hRm, hRf⟩ := bodyResolvent_exists r h1 h3 P ν hν μ hμ
  have hsol := bodyResolvent_solves r h1 h3 P ν hν μ hμ Rm hRf f
  have hz : HasPhaseOp (fun Φ => μ • Φ + L0T ν Φ) ((w : Yq P r) - Rm f) 0 := by
    intro Φ hΦ
    rw [map_sub, hw Φ hΦ, hsol Φ hΦ, sub_self, map_zero]
  have hwR : (w : Yq P r) = Rm f := sub_eq_zero.1 (bodyOp_uniqueness r h1 h3 P ν hν μ hμ _ hz)
  have hwn : ‖(w : Yq P r)‖ ≤ a⁻¹ * ‖f‖ := by
    rw [hwR]; exact (Rm.le_opNorm f).trans (mul_le_mul_of_nonneg_right hRm (norm_nonneg _))
  have ha0 : 0 < a := hμ
  obtain ⟨Λ, hΛ, hΛn⟩ := hC P ν hν μ f w hw
  have hΛeq : nuLapD w = Λ := nuLapD_eq hΛ
  have hdr := hasPhaseOp_drift_of hw hΛ
  have hTeq : T0D w = f - μ • (w : Yq P r) + Λ + (1 / 2 : ℂ) • (w : Yq P r) := T0D_eq hdr
  set K : ℝ := ‖f‖ with hK
  set S : ℝ := 1 + (1 + ‖μ‖) / a with hS
  set X : ℝ := K * S with hX
  have hK0 : 0 ≤ K := norm_nonneg _
  have hS1 : 1 ≤ S := by
    have : 0 ≤ (1 + ‖μ‖) / a := by positivity
    linarith
  have hX0 : 0 ≤ X := by positivity
  have hKX : K ≤ X := by nlinarith
  have hwX : ‖(w : Yq P r)‖ ≤ X := by
    have h1' : ‖(w : Yq P r)‖ ≤ a⁻¹ * K := hwn
    have : a⁻¹ * K ≤ (1 + ‖μ‖) / a * K := by
      rw [div_eq_inv_mul]
      have : a⁻¹ * 1 ≤ a⁻¹ * (1 + ‖μ‖) := by
        gcongr; linarith [norm_nonneg μ]
      nlinarith [mul_le_mul_of_nonneg_right this hK0]
    have h2 : (1 + ‖μ‖) / a * K ≤ X := by
      rw [hX, hS]; nlinarith
    linarith
  have hμw : ‖μ‖ * ‖(w : Yq P r)‖ ≤ X := by
    have : ‖μ‖ * ‖(w : Yq P r)‖ ≤ ‖μ‖ * (a⁻¹ * K) := by gcongr
    have h2 : ‖μ‖ * (a⁻¹ * K) ≤ (1 + ‖μ‖) / a * K := by
      rw [div_eq_inv_mul]
      nlinarith [mul_nonneg (inv_nonneg.2 ha0.le) hK0, norm_nonneg μ]
    have h3' : (1 + ‖μ‖) / a * K ≤ X := by rw [hX, hS]; nlinarith
    linarith
  have hΛX' : ‖Λ‖ ≤ 3 * C * X := by
    have hs : K + (1 + ‖μ‖) * ‖(w : Yq P r)‖ ≤ 3 * X := by
      have : (1 + ‖μ‖) * ‖(w : Yq P r)‖ = ‖(w : Yq P r)‖ + ‖μ‖ * ‖(w : Yq P r)‖ := by ring
      linarith
    calc ‖Λ‖ ≤ C * (K + (1 + ‖μ‖) * ‖(w : Yq P r)‖) := hΛn
      _ ≤ C * (3 * X) := mul_le_mul_of_nonneg_left hs hC0
      _ = 3 * C * X := by ring
  have hTn : ‖T0D w‖ ≤ X + X + 3 * C * X + X / 2 := by
    rw [hTeq]
    have e1 := norm_add_le (f - μ • (w : Yq P r) + Λ) ((1 / 2 : ℂ) • (w : Yq P r))
    have e2 := norm_add_le (f - μ • (w : Yq P r)) Λ
    have e3 := norm_sub_le f (μ • (w : Yq P r))
    have e4 : ‖μ • (w : Yq P r)‖ = ‖μ‖ * ‖(w : Yq P r)‖ := norm_smul _ _
    have e5 : ‖(1 / 2 : ℂ) • (w : Yq P r)‖ ≤ ‖(w : Yq P r)‖ / 2 := by
      rw [norm_smul]; simp [div_eq_inv_mul]
    linarith
  have hG : graphNormD w ≤ (7 / 2 + 6 * C) * X := by
    unfold graphNormD
    rw [hΛeq]
    linarith
  calc graphNormD w ≤ (7 / 2 + 6 * C) * X := hG
    _ = (7 / 2 + 6 * C) * (1 + (1 + ‖μ‖) / (μ.re + gammaR r)) * ‖bodyOp P ν r μ w‖ := by
      rw [hX, hS, hK]; ring

end UnforcedLeray.Short.PartIIa
