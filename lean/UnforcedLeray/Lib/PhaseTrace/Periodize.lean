import UnforcedLeray.Lib.PhaseSpace.Pairing
import UnforcedLeray.Lib.PhaseSpace.Ops
import UnforcedLeray.Lib.PhaseTrace.Lift

/-!
# Periodizing a test in the phase, and unfolding the phase pairing (block 2F, INF14 T6)

The strong phase trace (tex 7609–7621, unit B0434) tests the drift identity `T₀w = b` of the
free graph against the pullback of a spatial test along the comoving chart. That pullback is
supported in a bounded phase window, not periodic, so it is made into a phase test by
periodization:

  `perT P G (τ, y) = ∑ᶠ k : ℤ, G(τ + kP, y)`.

For `G` smooth with bounded spatial support (`IsPhaseTest 0 G`: periodicity with period `0` is
vacuous) and vanishing for phases outside `[A, B]` (`TimeSupp A B G`):

* `perT P G` is a phase test (`isPhaseTest_perT`);
* the transpose drift commutes with periodization: `driftT (perT P G) = perT P (driftT G)`
  (`driftT_perT`);
* the phase pairing unfolds to a pairing over the whole line (`phasePair_perT`):
  `⟪perT P G, f⟫ = P⁻¹ ∫_ℝ ⟨G(t, ·), f(t)⟩ dt`.

Status: infrastructure for `Lib/PhaseTrace.lean`; no manuscript unit is proved here.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.PhaseTrace

open UnforcedLeray.PhaseSpace

section Periodize

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Periodization in the phase: `perT P G (τ, y) = ∑ᶠ k, G(τ + kP, y)`. -/
def perT (P : ℝ) (G : ℝ × Space → F) : ℝ × Space → F :=
  fun p => ∑ᶠ k : ℤ, G (p.1 + k * P, p.2)

/-- `G` vanishes for phases outside `[A, B]`. -/
def TimeSupp (A B : ℝ) (G : ℝ × Space → F) : Prop :=
  ∀ τ y, τ ∉ Icc A B → G (τ, y) = 0

theorem perT_eq_sum {P : ℝ} {G : ℝ × Space → F} {A B : ℝ} (hG : TimeSupp A B G)
    (s : Finset ℤ) (p : ℝ × Space) (hs : ∀ k : ℤ, p.1 + k * P ∈ Icc A B → k ∈ s) :
    perT P G p = ∑ k ∈ s, G (p.1 + k * P, p.2) := by
  unfold perT
  apply finsum_eq_sum_of_support_subset
  intro k hk
  rw [Function.mem_support] at hk
  refine Finset.mem_coe.mpr (hs k ?_)
  by_contra h
  exact hk (hG _ _ h)

/-- Indices `k` with `σ + kP ∈ [A, B]` for some `σ ∈ [a, b]`. -/
def perIdx (P A B a b : ℝ) : Finset ℤ := Finset.Icc ⌈(A - b) / P⌉ ⌊(B - a) / P⌋

theorem mem_perIdx {P A B a b σ : ℝ} (hP : 0 < P) {k : ℤ} (hσ : σ ∈ Icc a b)
    (hk : σ + k * P ∈ Icc A B) : k ∈ perIdx P A B a b := by
  simp only [perIdx, Finset.mem_Icc]
  constructor
  · rw [Int.ceil_le, div_le_iff₀ hP]; linarith [hσ.2, hk.1]
  · rw [Int.le_floor, le_div_iff₀ hP]; linarith [hσ.1, hk.2]

theorem perT_periodic (P : ℝ) (G : ℝ × Space → F) (τ : ℝ) (y : Space) :
    perT P G (τ + P, y) = perT P G (τ, y) := by
  show ∑ᶠ k : ℤ, G ((τ + P) + k * P, y) = ∑ᶠ k : ℤ, G (τ + k * P, y)
  calc ∑ᶠ k : ℤ, G ((τ + P) + k * P, y)
      = ∑ᶠ k : ℤ, G (τ + ((Equiv.addRight (1 : ℤ) k : ℤ) : ℝ) * P, y) :=
        finsum_congr fun k => by
          rw [show τ + P + k * P = τ + ((Equiv.addRight (1 : ℤ) k : ℤ) : ℝ) * P by
            simp only [Equiv.coe_addRight]; push_cast; ring]
    _ = ∑ᶠ k : ℤ, G (τ + k * P, y) :=
        finsum_comp_equiv (Equiv.addRight (1 : ℤ)) (f := fun k : ℤ => G (τ + k * P, y))

theorem perT_eventuallyEq {P : ℝ} (hP : 0 < P) {G : ℝ × Space → F} {A B : ℝ}
    (hG : TimeSupp A B G) (p₀ : ℝ × Space) :
    perT P G =ᶠ[𝓝 p₀] fun p => ∑ k ∈ perIdx P A B (p₀.1 - 1) (p₀.1 + 1), G (p.1 + k * P, p.2) := by
  have hU : ∀ᶠ p in 𝓝 p₀, p.1 ∈ Icc (p₀.1 - 1) (p₀.1 + 1) :=
    continuous_fst.continuousAt.eventually_mem (Icc_mem_nhds (by linarith) (by linarith))
  filter_upwards [hU] with p hp
  exact perT_eq_sum hG _ p fun k hk => mem_perIdx hP hp hk

theorem contDiff_shift {G : ℝ × Space → F} (hGs : ContDiff ℝ ∞ G) (c : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × Space => G (p.1 + c, p.2)) :=
  hGs.comp ((contDiff_fst.add contDiff_const).prodMk contDiff_snd)

theorem contDiff_perT {P : ℝ} (hP : 0 < P) {G : ℝ × Space → F} {A B : ℝ} (hG : TimeSupp A B G)
    (hGs : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (perT P G) := by
  rw [contDiff_iff_contDiffAt]
  intro p₀
  refine ContDiffAt.congr_of_eventuallyEq ?_ (perT_eventuallyEq hP hG p₀)
  exact (ContDiff.sum fun k _ => contDiff_shift hGs _).contDiffAt

theorem perT_eq_zero {P R : ℝ} {G : ℝ × Space → F} (hR : ∀ τ y, R < ‖y‖ → G (τ, y) = 0)
    (τ : ℝ) (y : Space) (hy : R < ‖y‖) : perT P G (τ, y) = 0 := by
  show ∑ᶠ k : ℤ, G (τ + k * P, y) = 0
  simp [hR _ _ hy]

/-- The periodization of a smooth test with bounded support is a phase test. -/
theorem isPhaseTest_perT {P : ℝ} (hP : 0 < P) {G : ℝ × Space → F} {A B : ℝ}
    (hG : TimeSupp A B G) (hG0 : IsPhaseTest 0 G) : IsPhaseTest P (perT P G) where
  smooth := contDiff_perT hP hG hG0.smooth
  periodic := perT_periodic P G
  bounded_support := by
    obtain ⟨R, hR⟩ := hG0.bounded_support
    exact ⟨R, fun τ y hy => perT_eq_zero hR τ y hy⟩

/-! ### The transpose drift commutes with periodization -/

theorem driftT_congr {Φ Ψ : ℝ × Space → F} {p : ℝ × Space} (h : Φ =ᶠ[𝓝 p] Ψ) :
    driftT Φ p = driftT Ψ p := by
  simp only [driftT, dτ, radialT, dy, h.fderiv_eq, h.eq_of_nhds]

theorem timeSupp_driftT {A B : ℝ} {G : ℝ × Space → F} (hG : TimeSupp A B G) :
    TimeSupp A B (driftT G) := by
  intro τ y hτ
  have hev : G =ᶠ[𝓝 ((τ, y) : ℝ × Space)] fun _ => 0 := by
    have hopen : IsOpen {p : ℝ × Space | p.1 ∉ Icc A B} :=
      isClosed_Icc.isOpen_compl.preimage continuous_fst
    filter_upwards [hopen.mem_nhds (show ((τ, y) : ℝ × Space) ∈ {p : ℝ × Space | p.1 ∉ Icc A B}
      from hτ)] with p hp
    exact hG p.1 p.2 hp
  rw [driftT_congr hev]
  simp [driftT, dτ, radialT, dy]

theorem fderiv_shift {G : ℝ × Space → F} (c : ℝ) (p : ℝ × Space) :
    fderiv ℝ (fun p : ℝ × Space => G (p.1 + c, p.2)) p = fderiv ℝ G (p.1 + c, p.2) := by
  have e : ∀ p : ℝ × Space, p + ((c, 0) : ℝ × Space) = (p.1 + c, p.2) :=
    fun p => Prod.ext (by simp) (by simp)
  have h : (fun p : ℝ × Space => G (p.1 + c, p.2)) = fun p => G (p + ((c, 0) : ℝ × Space)) := by
    funext p
    rw [e]
  rw [h, fderiv_comp_add_right, e]

theorem driftT_sum_shift {G : ℝ × Space → F} (hGs : ContDiff ℝ ∞ G) (s : Finset ℤ) (P : ℝ)
    (p : ℝ × Space) :
    driftT (fun p => ∑ k ∈ s, G (p.1 + k * P, p.2)) p = ∑ k ∈ s, driftT G (p.1 + k * P, p.2) := by
  have hdiff : ∀ k ∈ s, DifferentiableAt ℝ (fun p : ℝ × Space => G (p.1 + k * P, p.2)) p :=
    fun k _ => ((contDiff_shift hGs _).differentiable (by simp)).differentiableAt
  have hF : fderiv ℝ (fun p : ℝ × Space => ∑ k ∈ s, G (p.1 + k * P, p.2)) p =
      ∑ k ∈ s, fderiv ℝ G (p.1 + k * P, p.2) := by
    rw [fderiv_fun_sum hdiff]
    exact Finset.sum_congr rfl fun k _ => fderiv_shift _ p
  have h1 : dτ (fun p : ℝ × Space => ∑ k ∈ s, G (p.1 + k * P, p.2)) p =
      ∑ k ∈ s, dτ G (p.1 + k * P, p.2) := by
    simp only [dτ, hF, ContinuousLinearMap.sum_apply]
  have h2 : ∀ j : Fin 3, dy j (fun p : ℝ × Space => ∑ k ∈ s, G (p.1 + k * P, p.2)) p =
      ∑ k ∈ s, dy j G (p.1 + k * P, p.2) := by
    intro j
    simp only [dy, hF, ContinuousLinearMap.sum_apply]
  have h3 : radialT (fun p : ℝ × Space => ∑ k ∈ s, G (p.1 + k * P, p.2)) p =
      ∑ k ∈ s, radialT G (p.1 + k * P, p.2) := by
    simp only [radialT, h2, Finset.smul_sum]
    exact Finset.sum_comm
  simp only [driftT, h1, h3, Finset.smul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]

/-- **Drift commutes with periodization.** -/
theorem driftT_perT {P : ℝ} (hP : 0 < P) {G : ℝ × Space → F} {A B : ℝ} (hG : TimeSupp A B G)
    (hGs : ContDiff ℝ ∞ G) : driftT (perT P G) = perT P (driftT G) := by
  funext p₀
  rw [driftT_congr (perT_eventuallyEq hP hG p₀), driftT_sum_shift hGs,
    perT_eq_sum (timeSupp_driftT hG) _ p₀
      (fun k hk => mem_perIdx (a := p₀.1 - 1) (b := p₀.1 + 1) hP ⟨by linarith, by linarith⟩ hk)]

end Periodize

/-! ### Unfolding the phase pairing -/

section Unfold

variable {P : ℝ} [hP : Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- The slice `G(t, ·) ∈ L^{q'}` of a smooth test with bounded spatial support. -/
def sliceL {G : ℝ × Space → CVec3} (hG0 : IsPhaseTest 0 G) (q : ℝ≥0∞) [Fact (1 ≤ q)] (t : ℝ) :
    Lp CVec3 (conjExp q) (volume : Measure Space) :=
  sliceMap (hG0.sliceCont (conjExp q)) t

theorem continuous_sliceL {G : ℝ × Space → CVec3} (hG0 : IsPhaseTest 0 G) :
    Continuous (sliceL hG0 q) :=
  (hG0.sliceCont (conjExp q)).continuous

theorem coeFn_sliceL {G : ℝ × Space → CVec3} (hG0 : IsPhaseTest 0 G) (t : ℝ) :
    (sliceL hG0 q t : Space → CVec3) =ᵐ[volume] fun y => G (t, y) :=
  MemLp.coeFn_toLp ((hG0.sliceCont (conjExp q)).memLp t)

theorem sliceL_eq_zero {G : ℝ × Space → CVec3} (hG0 : IsPhaseTest 0 G) {A B : ℝ}
    (hG : TimeSupp A B G) {t : ℝ} (ht : t ∉ Icc A B) : sliceL hG0 q t = 0 := by
  refine Lp.ext ?_
  filter_upwards [coeFn_sliceL (q := q) hG0 t,
    Lp.coeFn_zero CVec3 (conjExp q) (volume : Measure Space)] with y h1 h2
  rw [h1, h2, hG t y ht]
  rfl

/-- The line integrand `H(t) = ∫ G(t, y) · f(t)(y) dy` of the unfolded pairing. -/
def pairH {G : ℝ × Space → CVec3} (hG0 : IsPhaseTest 0 G) (f : Yq P q) (t : ℝ) : ℂ :=
  innerPair q (sliceL hG0 q t) (f (t : AddCircle P))

theorem integrable_dotL {G : ℝ × Space → CVec3} (hG0 : IsPhaseTest 0 G) (σ : ℝ)
    (g : Lp CVec3 q (volume : Measure Space)) :
    Integrable (fun y => dotL (G (σ, y)) ((g : Space → CVec3) y)) := by
  have hint : Integrable (fun y => dotL ((sliceL hG0 q σ : Space → CVec3) y)
      ((g : Space → CVec3) y)) :=
    memLp_one_iff_integrable.mp (dotL.memLp_of_bilin 1 (Lp.memLp _) (Lp.memLp g))
  refine hint.congr ?_
  filter_upwards [coeFn_sliceL (q := q) hG0 σ] with y hy
  rw [hy]

theorem pairH_eq {G : ℝ × Space → CVec3} (hG0 : IsPhaseTest 0 G) (f : Yq P q) (t : ℝ) :
    pairH hG0 f t = ∫ y, dotL (G (t, y)) ((f (t : AddCircle P) : Space → CVec3) y) := by
  rw [pairH, innerPair_apply]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_sliceL (q := q) hG0 t] with y hy
  rw [hy]

theorem pairH_eq_zero {G : ℝ × Space → CVec3} (hG0 : IsPhaseTest 0 G) {A B : ℝ}
    (hG : TimeSupp A B G) (f : Yq P q) {t : ℝ} (ht : t ∉ Icc A B) : pairH hG0 f t = 0 := by
  simp [pairH, sliceL_eq_zero hG0 hG ht]

theorem integrable_pairH {G : ℝ × Space → CVec3} (hG0 : IsPhaseTest 0 G) {A B : ℝ}
    (hAB : A ≤ B) (hG : TimeSupp A B G) (f : Yq P q) : Integrable (pairH hG0 f) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((continuous_sliceL (q := q) hG0).continuousOn (s := Icc A B))
  have hC' : ∀ t, ‖sliceL hG0 q t‖ ≤ max C 0 := by
    intro t
    by_cases ht : t ∈ Icc A B
    · exact (hC t ht).trans (le_max_left _ _)
    · rw [sliceL_eq_zero hG0 hG ht, norm_zero]; exact le_max_right _ _
  have hmeas : AEStronglyMeasurable (pairH hG0 f) volume :=
    (innerPair q).aestronglyMeasurable_comp₂ (continuous_sliceL hG0).aestronglyMeasurable
      (aestronglyMeasurable_comp_mk f)
  have hII : IntervalIntegrable (pairH hG0 f) volume A B := by
    refine IntervalIntegrable.mono_fun' (g := fun t => ‖innerPair q‖ * max C 0 *
      ‖f (t : AddCircle P)‖) ?_ hmeas.restrict ?_
    · exact ((intervalIntegrable_comp_mk f A B).norm).const_mul _
    · refine Eventually.of_forall fun t => ?_
      calc ‖pairH hG0 f t‖ ≤ ‖innerPair q‖ * ‖sliceL hG0 q t‖ * ‖f (t : AddCircle P)‖ :=
            (innerPair q).le_opNorm₂ _ _
        _ ≤ ‖innerPair q‖ * max C 0 * ‖f (t : AddCircle P)‖ := by gcongr; exact hC' t
  have hon : IntegrableOn (pairH hG0 f) (Icc A B) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hAB).mp hII
  exact hon.integrable_of_forall_notMem_eq_zero fun t ht => pairH_eq_zero hG0 hG f ht

/-- **Unfolding.** `⟪perT P G, f⟫ = P⁻¹ ∫_ℝ ⟨G(t, ·), f(t)⟩ dt`. -/
theorem phasePair_perT {G : ℝ × Space → CVec3} (hG0 : IsPhaseTest 0 G) {A B : ℝ}
    (hAB : A ≤ B) (hG : TimeSupp A B G) (f : Yq P q) :
    phasePair P q (perT P G) f = P⁻¹ • ∫ t, pairH hG0 f t := by
  have hP0 := hP.out
  have hΦ := isPhaseTest_perT hP0 hG hG0
  have hHint := integrable_pairH hG0 hAB hG f
  rw [phasePair_eq_periodIntegral hΦ f]
  congr 1
  set m : ℤ := ⌊A / P⌋ - 1 with hm
  set N : ℕ := (⌈B / P⌉ - m).toNat with hN
  set s : Finset ℤ := (Finset.range N).image (fun i : ℕ => m + i) with hs
  have hsmem : ∀ t ∈ Ioc (0 : ℝ) (0 + P), ∀ k : ℤ, t + k * P ∈ Icc A B → k ∈ s := by
    intro t ht k hk
    have hkm : m ≤ k := by
      have h1 : A / P - 1 ≤ k := by
        rw [sub_le_iff_le_add, div_le_iff₀ hP0]; linarith [ht.2, hk.1]
      have h2 : (⌊A / P⌋ : ℝ) ≤ A / P := Int.floor_le _
      have h3 : ((m : ℤ) : ℝ) ≤ k := by rw [hm]; push_cast; linarith
      exact_mod_cast h3
    have hkM : k < ⌈B / P⌉ := by
      have h1 : (k : ℝ) < B / P := by
        rw [lt_div_iff₀ hP0]; linarith [ht.1, hk.2]
      have h2 : B / P ≤ (⌈B / P⌉ : ℝ) := Int.le_ceil _
      exact_mod_cast h1.trans_le h2
    rw [hs, Finset.mem_image]
    refine ⟨(k - m).toNat, ?_, ?_⟩
    · rw [Finset.mem_range, hN]
      exact (Int.toNat_lt_toNat (by omega)).mpr (by omega)
    · rw [Int.toNat_of_nonneg (by omega)]; ring
  have hA : ∀ t ∈ Ioc (0 : ℝ) (0 + P),
      ∫ y, dotL (perT P G (t, y)) ((f (t : AddCircle P) : Space → CVec3) y) =
        ∑ k ∈ s, pairH hG0 f (t + k * P) := by
    intro t ht
    have hp : ∀ y, perT P G (t, y) = ∑ k ∈ s, G (t + k * P, y) :=
      fun y => perT_eq_sum hG s (t, y) (hsmem t ht)
    simp_rw [hp, map_sum, ContinuousLinearMap.sum_apply]
    rw [integral_finsetSum _ fun k _ => integrable_dotL hG0 _ _]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pairH_eq, coe_add_int_mul]
  rw [setIntegral_congr_fun measurableSet_Ioc hA,
    integral_finsetSum _ fun k _ => (hHint.comp_add_right _).integrableOn,
    Finset.sum_image (fun i _ j _ hij => by simpa using hij)]
  have hB : ∀ i : ℕ, ∫ t in Ioc (0 : ℝ) (0 + P), pairH hG0 f (t + ((m + i : ℤ) : ℝ) * P) =
      ∫ t in ((m + i : ℤ) : ℝ) * P..((m + ((i + 1 : ℕ) : ℤ) : ℤ) : ℝ) * P, pairH hG0 f t := by
    intro i
    rw [← intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_comp_add_right]
    congr 1 <;> push_cast <;> ring
  rw [Finset.sum_congr rfl fun i _ => hB i,
    intervalIntegral.sum_integral_adjacent_intervals
      (a := fun i : ℕ => ((m + (i : ℤ) : ℤ) : ℝ) * P) fun k _ => hHint.intervalIntegrable]
  refine intervalIntegral.integral_eq_integral_of_support_subset ?_
  intro t ht
  have htAB : t ∈ Icc A B := by
    by_contra h
    exact ht (pairH_eq_zero hG0 hG f h)
  constructor
  · have h2 : (⌊A / P⌋ : ℝ) ≤ A / P := Int.floor_le _
    have h3 : (⌊A / P⌋ : ℝ) * P ≤ A := by rwa [le_div_iff₀ hP0] at h2
    simp only [Nat.cast_zero, add_zero, hm]
    push_cast
    nlinarith [htAB.1]
  · have hNge : ⌈B / P⌉ ≤ m + (N : ℤ) := by rw [hN]; omega
    have h2 : B / P ≤ (⌈B / P⌉ : ℝ) := Int.le_ceil _
    have h3 : B ≤ (⌈B / P⌉ : ℝ) * P := by rwa [div_le_iff₀ hP0] at h2
    have h4 : (⌈B / P⌉ : ℝ) ≤ ((m + (N : ℤ) : ℤ) : ℝ) := by exact_mod_cast hNge
    calc t ≤ B := htAB.2
      _ ≤ (⌈B / P⌉ : ℝ) * P := h3
      _ ≤ ((m + (N : ℤ) : ℤ) : ℝ) * P := by gcongr

end Unfold

end UnforcedLeray.PhaseTrace
