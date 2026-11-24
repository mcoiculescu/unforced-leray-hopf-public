import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.Hess.Defs
import UnforcedLeray.Short.PartIIa.Tasks.F03aWindowEquation
import UnforcedLeray.Short.PartIIa.Tasks.F03bWindowNorms
import UnforcedLeray.Short.PartIIa.Tasks.F03dWindowBackNorm
import UnforcedLeray.Short.PartIIa.Tasks.F04aGlobalField.WindowLapLocInt
import UnforcedLeray.Short.PartIIa.Tasks.F04aGlobalField.WindowRhsFinite
import UnforcedLeray.Short.PartIIa.Tasks.F04aGlobalField.WindowLapGlue
import UnforcedLeray.Short.PartIIa.Tasks.F04bFieldToY.PeriodicFieldToYq
import UnforcedLeray.Short.PartIIa.Tasks.F04bFieldToY.PeriodPartition
import UnforcedLeray.Short.PartIIa.Tasks.F04bFieldToY.PeriodUnfold
import UnforcedLeray.Short.PartIIa.Tasks.F04bFieldToY.PhasePairSliceIntegrable

/-!
# Composition of the window Hessian leaves (source 1377-1442)

Task `PartIII-b:C/ward/12/3/1/2/2/org`.  Source of record
`the November 2 reference manuscript`.

* `localWindowHess_of` (source 1426-1436): the window pull-back and its equation and norms
  (`windowEquation`, `windowNorms`, proved in Part II-a) with the componentwise free heat
  estimate `B0423.heat_estimate_complex` (`‖ν∂_i∂_ju‖_q ≤ C‖F‖_q`, source 1377-1424) and the
  transport-back norm `windowBackNorm`; the only new input is `WindowBackHess`.  (Proof of
  `PartIIa.localWindowEstimate_of` with the component `D2 c j k` in place of `∑ᵢ D2 c i i`.)
* `globalHessFieldWindowBound_of` (source 1437-1441): gluing over integer centres, as
  `PartIIa.globalFieldWindowBound`, with the operator-free leaves `windowLapLocInt`,
  `windowRhsFinite`, `windowLapGlue` and the four Hessian leaves.
* `hessFieldToYRep_of`: as `PartIIa.laplacianFieldToYRep`, with `WindowTestIdentityHess`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.Short.PartIIa.Rep
open UnforcedLeray.Parabolic (PS)
open UnforcedLeray.Short.PartIIa (WindowCutoff windowField windowForce windowLap winSet)

/-- **`LocalWindowHess` from the transport back** (source 1426-1436). -/
theorem localWindowHess_of (h3 : WindowBackHess) : LocalWindowHess := by
  intro r _ hr1 hrt
  have hq : 1 < r.toReal := by
    have := ENNReal.toReal_strict_mono hrt hr1
    simpa using this
  have hq0 : 0 ≤ r.toReal := by linarith
  obtain ⟨χ, hχ⟩ := UnforcedLeray.Short.PartIIa.windowCutoff_exists
  obtain ⟨K, hK0, hK⟩ := UnforcedLeray.Short.PartIIa.windowNorms r hr1 hrt χ hχ
  obtain ⟨K', hK'0, hK'⟩ := UnforcedLeray.Short.PartIIa.windowBackNorm r.toReal hq
  obtain ⟨Ch, hCh⟩ := UnforcedLeray.B0423.heat_estimate_complex (d := 3) hq
  set q := r.toReal with hqdef
  have h3pos : (0 : ℝ) ≤ (3 : ℝ) ^ (1 / q) := by positivity
  refine ⟨(3 : ℝ) ^ (1 / q) * K' * Ch * K, by positivity, ?_⟩
  intro P _ hP1 ν hν μ f w hw W hW j k τ₀
  obtain ⟨Fr, hFr⟩ := exists_isRep hrt f
  have heq := UnforcedLeray.Short.PartIIa.windowEquation r hrt P ν μ f w hw W Fr hW hFr χ hχ τ₀
  have hmem := fun c => hK P μ f w W Fr hW hFr τ₀ c
  have hheat := fun c => hCh ν hν (windowField χ τ₀ W c) (windowForce μ χ τ₀ W Fr c)
    (hmem c).1 (hmem c).2.1 (heq c)
  choose D2 Dt hD2 hDt hDtw hb hbt using hheat
  refine ⟨windowLap ν τ₀ fun c X => D2 c j k X,
    h3 r hrt P ν w W hW χ hχ τ₀ D2 (fun c i l => hD2 c i l) j k, ?_⟩
  set R : ℝ≥0∞ := ∫⁻ τ in Ioo (τ₀ - 2) (τ₀ + 2),
    (‖f (τ : AddCircle P)‖ₑ ^ q + ENNReal.ofReal (1 + ‖μ‖) ^ q * ‖w (τ : AddCircle P)‖ₑ ^ q)
    with hR
  have hmeas : ∀ c, AEStronglyMeasurable (fun X : PS 3 => D2 c j k X) volume := fun c =>
    (hD2 c j k).1.1
  refine (hK' ν τ₀ (fun c X => D2 c j k X) hmeas).trans ?_
  have hterm : ∀ c, eLpNorm (fun X : PS 3 => (ν : ℂ) * D2 c j k X) (ENNReal.ofReal q)
      volume ^ q ≤ (Ch : ℝ≥0∞) ^ q * (ENNReal.ofReal K ^ q * R) := fun c => by
    calc eLpNorm (fun X : PS 3 => (ν : ℂ) * D2 c j k X) (ENNReal.ofReal q) volume ^ q
        ≤ ((Ch : ℝ≥0∞) * eLpNorm (windowForce μ χ τ₀ W Fr c) (ENNReal.ofReal q) volume) ^ q :=
          ENNReal.rpow_le_rpow (hb c j k) hq0
      _ = (Ch : ℝ≥0∞) ^ q * eLpNorm (windowForce μ χ τ₀ W Fr c) (ENNReal.ofReal q) volume ^ q :=
          ENNReal.mul_rpow_of_nonneg _ _ hq0
      _ ≤ (Ch : ℝ≥0∞) ^ q * (ENNReal.ofReal K ^ q * R) :=
          mul_le_mul' le_rfl (hmem c).2.2
  have hsum : ∑ c : Fin 3, eLpNorm (fun X : PS 3 => (ν : ℂ) * D2 c j k X)
      (ENNReal.ofReal q) volume ^ q ≤ 3 * ((Ch : ℝ≥0∞) ^ q * (ENNReal.ofReal K ^ q * R)) := by
    calc ∑ c : Fin 3, eLpNorm (fun X : PS 3 => (ν : ℂ) * D2 c j k X)
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

/-- **`GlobalHessFieldWindowBound` from the gluing leaves** (source 1437-1441). -/
theorem globalHessFieldWindowBound_of (hAE : WindowHessAEMeas) (hUn : WindowHessUnique)
    (hPoU : WindowHessPoU) (hPer : WindowHessPeriodic) : GlobalHessFieldWindowBound := by
  intro hloc r _ hr1 hrt
  obtain ⟨C, hC0, hC⟩ := hloc r hr1 hrt
  refine ⟨C, hC0, ?_⟩
  intro P hP hP1 ν hν μ f w hf W hW j k
  have hCP := fun τ₀ : ℝ => hC P hP1 ν hν μ f w hf W hW j k τ₀
  choose Hk hHk hbd using fun n : ℤ => hCP (n : ℝ)
  have hfin2 : ∀ n : ℤ, ∫⁻ τ in Ioo ((n : ℝ) - 1) ((n : ℝ) + 1), ∫⁻ y, ‖Hk n (τ, y)‖ₑ ^ r.toReal
      < ⊤ := by
    intro n
    refine lt_of_le_of_lt (hbd n) (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg
      ENNReal.toReal_nonneg ENNReal.ofReal_ne_top) (windowRhsFinite r hrt P μ f w (n : ℝ)))
  have hmeas : ∀ n : ℤ, AEStronglyMeasurable (Hk n) (volume.restrict (winSet (n : ℝ))) :=
    fun n => hAE ν (n : ℝ) j k W (Hk n) (hHk n)
  have hli : ∀ n : ℤ, LocallyIntegrableOn (Hk n) (winSet (n : ℝ)) :=
    fun n => windowLapLocInt r hrt _ _ (Hk n) (hmeas n) (hfin2 n)
  have hover : ∀ n m : ℤ, Hk n =ᵐ[volume.restrict (winSet (n : ℝ) ∩ winSet (m : ℝ))] Hk m := by
    intro n m
    have hset : winSet (n : ℝ) ∩ winSet (m : ℝ) =
        Ioo (max ((n : ℝ) - 1) ((m : ℝ) - 1)) (min ((n : ℝ) + 1) ((m : ℝ) + 1)) ×ˢ
          (univ : Set Space) := by
      unfold winSet
      rw [Set.prod_inter_prod, Set.inter_univ, Set.Ioo_inter_Ioo]
    rw [hset]
    exact hUn ν n m _ _ j k W (Hk n) (Hk m) (le_max_left _ _) (min_le_left _ _)
      (le_max_right _ _) (min_le_right _ _) (hHk n) (hHk m)
      ((hli n).mono_set (by rw [← hset]; exact Set.inter_subset_left))
      ((hli m).mono_set (by rw [← hset]; exact Set.inter_subset_right))
  obtain ⟨H, hHm, hHeq⟩ := UnforcedLeray.Short.PartIIa.windowLapGlue Hk hmeas hover
  have hwin : ∀ τ₀ : ℝ, IsWindowHess ν τ₀ j k W H := hPoU ν j k W H Hk hHk hHeq
  have hli' : ∀ n : ℤ, LocallyIntegrableOn H (winSet (n : ℝ)) :=
    fun n => (hli n).congr (hHeq n).symm
  have hWper : ∀ᵐ τ : ℝ, (fun y => W (τ + P, y)) =ᵐ[volume] fun y => W (τ, y) := by
    filter_upwards [hW.slice, hW.slice_shift P] with t h1 h2
    have e : ((P + t : ℝ) : AddCircle P) = (t : AddCircle P) := by
      rw [add_comm]; exact AddCircle.coe_add_period P t
    rw [e] at h2
    rw [add_comm t P]
    exact h2.trans h1.symm
  have hperH : ∀ᵐ τ : ℝ, (fun y => H (τ + P, y)) =ᵐ[volume] fun y => H (τ, y) :=
    hPer P ν hP.out j k W H hW.meas hHm hWper hwin hli'
  have hcongrW : ∀ (a b : ℝ) (H₁ H₂ : ℝ × Space → CVec3),
      H₁ =ᵐ[volume.restrict (Ioo a b ×ˢ (univ : Set Space))] H₂ →
      ∫⁻ τ in Ioo a b, ∫⁻ y, ‖H₁ (τ, y)‖ₑ ^ r.toReal =
        ∫⁻ τ in Ioo a b, ∫⁻ y, ‖H₂ (τ, y)‖ₑ ^ r.toReal := by
    intro a b H₁ H₂ h
    have h' : H₁ =ᵐ[((volume : Measure ℝ).restrict (Ioo a b)).prod (volume : Measure Space)] H₂ := by
      rw [Measure.restrict_prod_eq_prod_univ]; exact h
    apply lintegral_congr_ae
    filter_upwards [Measure.ae_ae_of_ae_prod h'] with τ hτ
    apply lintegral_congr_ae
    filter_upwards [hτ] with y hy
    rw [hy]
  have hfinW : ∀ n : ℤ, ∫⁻ τ in Ioo ((n : ℝ) - 1) ((n : ℝ) + 1), ∫⁻ y, ‖H (τ, y)‖ₑ ^ r.toReal
      < ⊤ := by
    intro n
    rw [hcongrW ((n : ℝ) - 1) ((n : ℝ) + 1) H (Hk n) (hHeq n)]
    exact hfin2 n
  have hLIH : ∀ τ₀ : ℝ, LocallyIntegrableOn H (Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space)) := by
    intro τ₀
    apply windowLapLocInt r hrt (τ₀ - 1) (τ₀ + 1) H hHm.aestronglyMeasurable
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
  refine ⟨H, hHm, hwin, hperH, ?_⟩
  intro τ₀
  obtain ⟨H₀, hH₀, hbd₀⟩ := hCP τ₀
  have hli₀ : LocallyIntegrableOn H₀ (Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space)) := by
    refine windowLapLocInt r hrt (τ₀ - 1) (τ₀ + 1) H₀ (hAE ν τ₀ j k W H₀ hH₀) ?_
    exact lt_of_le_of_lt hbd₀ (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg
      ENNReal.toReal_nonneg ENNReal.ofReal_ne_top) (windowRhsFinite r hrt P μ f w τ₀))
  have hae : H =ᵐ[volume.restrict (Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space))] H₀ :=
    hUn ν τ₀ τ₀ (τ₀ - 1) (τ₀ + 1) j k W H H₀ le_rfl le_rfl le_rfl le_rfl (hwin τ₀) hH₀
      (hLIH τ₀) hli₀
  rw [hcongrW (τ₀ - 1) (τ₀ + 1) H H₀ hae]
  exact hbd₀

/-- **`HessFieldToYRep` from the window test identity** (proof of
`PartIIa.laplacianFieldToYRep`). -/
theorem hessFieldToYRep_of (h5 : WindowTestIdentityHess) : HessFieldToYRep := by
  intro r _ hr P hP ν j k w W hW H hm hwin hper hfin
  obtain ⟨a, ha⟩ := UnforcedLeray.Short.PartIIa.periodicFieldToYq_proof r hr P H hm hper hfin
  refine ⟨a, ha, ?_⟩
  intro Φ hΦ
  obtain ⟨n, c, η, hpart⟩ := UnforcedLeray.Short.PartIIa.periodPartition_proof P hP.out
  have hΨ : IsPhaseTest P (nuHessT ν j k Φ) := isPhaseTest_nuHessT hΦ ν j k
  rw [phasePair_eq_periodIntegral hΨ w, phasePair_eq_periodIntegral hΦ a, zero_add]
  congr 1
  have unfold : ∀ (Ψ' : ℝ × Space → CVec3), IsPhaseTest P Ψ' → ∀ v : Yq P r,
      ∫ t in Ioc (0 : ℝ) P, ∫ y, dotL (Ψ' (t, y)) ((v (t : AddCircle P) : Space → CVec3) y) =
        ∑ i, ∫ t, (η i t : ℂ) *
          ∫ y, dotL (Ψ' (t, y)) ((v (t : AddCircle P) : Space → CVec3) y) := by
    intro Ψ' hΨ' v
    refine UnforcedLeray.Short.PartIIa.periodUnfold_proof P hP.out n c η hpart _ ?_
      (UnforcedLeray.Short.PartIIa.phasePairSliceIntegrable_proof r P v Ψ' hΨ')
    intro t
    have e : (((t + P : ℝ)) : AddCircle P) = (t : AddCircle P) := AddCircle.coe_add_period P t
    simp only [e, hΨ'.periodic]
  have conv : ∀ (Ψ' : ℝ × Space → CVec3) (v : Yq P r) (V : ℝ × Space → CVec3), IsRep v V →
      ∀ i, ∫ t, (η i t : ℂ) * ∫ y, dotL (Ψ' (t, y)) ((v (t : AddCircle P) : Space → CVec3) y) =
        ∫ t, (η i t : ℂ) * ∫ y, dotL (Ψ' (t, y)) (V (t, y)) := by
    intro Ψ' v V hV i
    refine integral_congr_ae ?_
    filter_upwards [hV.slice] with t ht
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [ht] with y hy
    rw [hy]
  rw [unfold _ hΨ w, unfold _ hΦ a]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [conv _ w W hW i, conv _ a H ha i]
  exact h5 P ν (c i) j k W H (hwin (c i)) (η i) (hpart.1 i).1 (hpart.1 i).2.1
    (hpart.1 i).2.2 Φ hΦ

end UnforcedLeray.Short.PartIIIb.Concrete
