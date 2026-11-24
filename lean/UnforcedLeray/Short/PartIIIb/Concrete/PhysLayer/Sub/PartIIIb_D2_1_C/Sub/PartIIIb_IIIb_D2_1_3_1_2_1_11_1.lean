import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_11
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.PairCont

/-!
# `WeakLapMul`: weak product rule for `νΔ` with a smooth `c = c(y)`

Source `the November 2 reference manuscript` lines 1334-1337, 1351-1362, 1470-1480.
Proves `weakLapMul : WeakLapMul`. Helpers are local (prefix `wlm_`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-! ### Pointwise facts for `dotL` -/

theorem wlm_dotL_smul_left (r : ℝ) (a b : CVec3) : dotL (r • a) b = (r : ℂ) • dotL a b := by
  simp [dotL_apply, Finset.mul_sum]

theorem wlm_dotL_smul_right (r : ℝ) (a b : CVec3) : dotL a (r • b) = (r : ℂ) • dotL a b := by
  simp [dotL_apply, Finset.mul_sum]

/-! ### Phase tests and `Y_2` -/

theorem wlm_phase_mulT {P : ℝ} {a : Space → ℝ} (ha : ContDiff ℝ ∞ a) {Θ : ℝ × Space → CVec3}
    (hΘ : IsPhaseTest P Θ) : IsPhaseTest P (fun x => a x.2 • Θ x) := by
  refine ⟨contDiff_mulT ha hΘ.smooth, ?_, ?_⟩
  · intro τ y
    simp [hΘ.periodic τ y]
  · obtain ⟨R, hR⟩ := hΘ.bounded_support
    exact ⟨R, fun τ y hy => by simp [hR τ y hy]⟩

theorem wlm_isInYr_cont {P : ℝ} (hP : 0 < P) {Ψ : ℝ × Space → CVec3} (hc : Continuous Ψ)
    (hper : ∀ τ y, Ψ (τ + P, y) = Ψ (τ, y)) {R : ℝ} (hR : ∀ τ y, R < ‖y‖ → Ψ (τ, y) = 0) :
    UnforcedLeray.Short.IIb.IsInYr P 2 Ψ := by
  refine ⟨Filter.Eventually.of_forall fun x => hper x.1 x.2, hc.aestronglyMeasurable, ?_⟩
  have hK : IsCompact (Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) R) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  have hbd : ∀ t ∈ Ioc (0 : ℝ) P, ∀ y : Space,
      ‖Ψ (t, y)‖ₑ ^ (2 : ℝ) ≤
        (Metric.closedBall (0 : Space) R).indicator (fun _ => ENNReal.ofReal C ^ (2 : ℝ)) y := by
    intro t ht y
    by_cases hy : y ∈ Metric.closedBall (0 : Space) R
    · rw [Set.indicator_of_mem hy]
      gcongr
      have := hC (t, y) ⟨⟨ht.1.le, ht.2⟩, hy⟩
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal this
    · rw [Set.indicator_of_notMem hy]
      have : Ψ (t, y) = 0 := hR t y (by simpa [mem_closedBall_zero_iff] using hy)
      simp [this]
  have hfin : ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ‖Ψ (t, y)‖ₑ ^ (2 : ℝ) < ⊤ := by
    calc ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ‖Ψ (t, y)‖ₑ ^ (2 : ℝ)
        ≤ ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space,
            (Metric.closedBall (0 : Space) R).indicator
              (fun _ => ENNReal.ofReal C ^ (2 : ℝ)) y := by
          refine setLIntegral_mono' measurableSet_Ioc fun t ht => ?_
          exact lintegral_mono fun y => hbd t ht y
      _ < ⊤ := by
          simp only [lintegral_indicator_const measurableSet_closedBall, setLIntegral_const]
          refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ?_ measure_closedBall_lt_top) ?_
          · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
          · simp
  show (ENNReal.ofReal P⁻¹ * _) ^ (1 / (2 : ℝ)) < ⊤
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin).ne

theorem wlm_isInYr_test {P : ℝ} (hP : 0 < P) {Θ : ℝ × Space → CVec3} (hΘ : IsPhaseTest P Θ) :
    UnforcedLeray.Short.IIb.IsInYr P 2 Θ := by
  obtain ⟨R, hR⟩ := hΘ.bounded_support
  exact wlm_isInYr_cont hP hΘ.continuous hΘ.periodic hR

theorem wlm_ae_y_ne (P : ℝ) : ∀ᵐ z ∂(muP P), z.2 ≠ 0 := by
  rw [ae_iff]
  have hset : {z : ℝ × Space | ¬ (z.2 ≠ 0)} = (univ : Set ℝ) ×ˢ ({0} : Set Space) := by
    ext z; simp
  rw [hset, muP, Measure.prod_prod, measure_singleton, mul_zero]

/-- Pairing of a phase test with a locally `L²` field is integrable on the phase measure. -/
theorem wlm_integrable {P : ℝ} (hP : 0 < P) {Θ u : ℝ × Space → CVec3} (hΘ : IsPhaseTest P Θ)
    (hu : LocL2 P u) : Integrable (fun z => dotL (Θ z) (u z)) (muP P) := by
  rcases hu with hY | hH
  · exact dot_integrable hP (wlm_isInYr_test hP hΘ) hY
  · obtain ⟨R, hR⟩ := hΘ.bounded_support
    have hYh : UnforcedLeray.Short.IIb.IsInYr P 2 (fun z : ℝ × Space => (‖z.2‖ : ℝ) • Θ z) := by
      refine wlm_isInYr_cont hP ?_ ?_ (R := R) ?_
      · exact (continuous_norm.comp continuous_snd).smul hΘ.continuous
      · intro τ y; simp [hΘ.periodic τ y]
      · intro τ y hy; simp [hR τ y hy]
    have hh := dot_integrable hP hYh hH
    refine hh.congr ?_
    filter_upwards [wlm_ae_y_ne P] with z hz
    have hn : ‖z.2‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    show dotL ((‖z.2‖ : ℝ) • Θ z) ((‖z.2‖⁻¹ : ℝ) • u z) = dotL (Θ z) (u z)
    rw [wlm_dotL_smul_left, wlm_dotL_smul_right, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      ← Complex.ofReal_mul, mul_inv_cancel₀ hn, Complex.ofReal_one, one_mul]

/-- Integrability with a smooth scalar multiplier on the test side: `dotL Θ (s • Y)`. -/
theorem wlm_integrable_scal {P : ℝ} (hP : 0 < P) {s : Space → ℝ} (hs : ContDiff ℝ ∞ s)
    {Θ Y : ℝ × Space → CVec3} (hΘ : IsPhaseTest P Θ) (hY : LocL2 P Y) :
    Integrable (fun z => dotL (Θ z) (s z.2 • Y z)) (muP P) := by
  have h := wlm_integrable hP (wlm_phase_mulT hs hΘ) hY
  refine h.congr (ae_of_all _ fun z => ?_)
  simp only [wlm_dotL_smul_left, wlm_dotL_smul_right]

theorem wlm_integrable_add_right {P : ℝ} {X Y Z : ℝ × Space → CVec3}
    (hY : Integrable (fun z => dotL (X z) (Y z)) (muP P))
    (hZ : Integrable (fun z => dotL (X z) (Z z)) (muP P)) :
    Integrable (fun z => dotL (X z) (Y z + Z z)) (muP P) :=
  (hY.add hZ).congr (ae_of_all _ fun z => by simp [map_add])

/-! ### Pairing identities -/

theorem wlm_pairF_add {P : ℝ} (hP : 0 < P) {X Y u : ℝ × Space → CVec3} (hX : IsPhaseTest P X)
    (hY : IsPhaseTest P Y) (hu : LocL2 P u) :
    pairF P (fun x => X x + Y x) u = pairF P X u + pairF P Y u := by
  have hXY : IsPhaseTest P (fun x => X x + Y x) := hX.add hY
  have iXY := wlm_integrable hP hXY hu
  have iX := wlm_integrable hP hX hu
  have iY := wlm_integrable hP hY hu
  rw [pair_eq_integral P _ _ iXY, pair_eq_integral P _ _ iX, pair_eq_integral P _ _ iY]
  simp only [map_add, add_apply]
  rw [integral_add iX iY, smul_add]

theorem wlm_pairF_sub {P : ℝ} (hP : 0 < P) {X Y u : ℝ × Space → CVec3} (hX : IsPhaseTest P X)
    (hY : IsPhaseTest P Y) (hu : LocL2 P u) :
    pairF P (fun x => X x - Y x) u = pairF P X u - pairF P Y u := by
  have hXY : IsPhaseTest P (fun x => X x - Y x) := hX.sub hY
  have iXY := wlm_integrable hP hXY hu
  have iX := wlm_integrable hP hX hu
  have iY := wlm_integrable hP hY hu
  rw [pair_eq_integral P _ _ iXY, pair_eq_integral P _ _ iX, pair_eq_integral P _ _ iY]
  simp only [map_sub, sub_apply]
  rw [integral_sub iX iY, smul_sub]

theorem wlm_pairF_add_right {P : ℝ} {X Y Z : ℝ × Space → CVec3}
    (hY : Integrable (fun z => dotL (X z) (Y z)) (muP P))
    (hZ : Integrable (fun z => dotL (X z) (Z z)) (muP P)) :
    pairF P X (fun x => Y x + Z x) = pairF P X Y + pairF P X Z := by
  rw [pair_eq_integral P X Y hY, pair_eq_integral P X Z hZ,
    pair_eq_integral P X (fun x => Y x + Z x) (wlm_integrable_add_right hY hZ)]
  simp only [map_add, add_apply]
  rw [integral_add hY hZ, smul_add]

/-- Swapping a real scalar function from the field to the test side (pointwise, no integrability). -/
theorem wlm_pairF_swap (P : ℝ) (s : ℝ × Space → ℝ) (X u : ℝ × Space → CVec3) :
    pairF P X (fun x => s x • u x) = pairF P (fun x => s x • X x) u := by
  simp only [pairF, phaseInt, wlm_dotL_smul_left, wlm_dotL_smul_right]

theorem wlm_pairF_neg (P : ℝ) (X u : ℝ × Space → CVec3) :
    pairF P (-X) u = -pairF P X u := by
  simp only [pairF, phaseInt, Pi.neg_apply, map_neg, ContinuousLinearMap.neg_apply, integral_neg,
    smul_neg]


theorem wlm_pairF_const_smul (P : ℝ) (r : ℝ) (X u : ℝ × Space → CVec3) :
    pairF P (fun x => r • X x) u = (r : ℂ) * pairF P X u := by
  simp only [pairF, phaseInt, wlm_dotL_smul_left, integral_smul, Complex.real_smul]
  ring

theorem wlm_pairF_zero_right (P : ℝ) (X : ℝ × Space → CVec3) : pairF P X 0 = 0 := by
  simp [pairF, phaseInt]

/-! ### Derivatives of scalar functions -/

theorem wlm_sd_const_mul {f : Space → ℝ} (hf : Differentiable ℝ f) (r : ℝ) (j : Fin 3) (y : Space) :
    sd j (fun z => r * f z) y = r * sd j f y := by
  unfold sd
  rw [fderiv_const_mul (hf y)]
  simp

/-- The weak identity for one direction: `⟪a ∂ₖΘ, u⟫ = -⟪aΘ, ∂ₖu⟫ - ⟪(∂ₖa) Θ, u⟫`. -/
theorem wlm_W1 {P : ℝ} (hP : 0 < P) {Θ u du : ℝ × Space → CVec3} {k : Fin 3}
    (hΘ : IsPhaseTest P Θ) (hu : LocL2 P u)
    (hdu : UnforcedLeray.Short.IIb.HasPtwOp P (fun Φ => -dy k Φ) u du)
    {a b : Space → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ∀ y, sd k a y = b y) :
    pairF P (fun x => a x.2 • dy k Θ x) u =
      -pairF P (fun x => a x.2 • Θ x) du - pairF P (fun x => b x.2 • Θ x) u := by
  have hm : IsPhaseTest P (fun x => a x.2 • Θ x) := wlm_phase_mulT ha hΘ
  have hsd : IsPhaseTest P (fun x => sd k a x.2 • Θ x) :=
    wlm_phase_mulT (UnforcedLeray.PhaseSpace.contDiff_sd ha k) hΘ
  have hpt : ∀ x, a x.2 • dy k Θ x = dy k (fun y => a y.2 • Θ y) x - sd k a x.2 • Θ x := by
    intro x
    have h := dy_mulT (ha.differentiable (by simp)) (hΘ.smooth.differentiable (by simp)) k
    have h' : dy k (mulT a Θ) x = a x.2 • dy k Θ x + sd k a x.2 • Θ x := by
      rw [h]
      simp only [mulT, Pi.add_apply]
    show a x.2 • dy k Θ x = dy k (mulT a Θ) x - sd k a x.2 • Θ x
    rw [h']
    abel
  have e1 : (fun x => a x.2 • dy k Θ x) =
      fun x => dy k (fun y => a y.2 • Θ y) x - (fun x => sd k a x.2 • Θ x) x :=
    funext fun x => hpt x
  have hdy : pairF P (dy k (fun y => a y.2 • Θ y)) u =
      -pairF P (fun y => a y.2 • Θ y) du := by
    have h : pairF P (-(dy k (fun y => a y.2 • Θ y))) u =
        pairF P (fun y => a y.2 • Θ y) du := hdu _ hm
    rw [wlm_pairF_neg] at h
    linear_combination -h
  have e3 : pairF P (fun x => sd k a x.2 • Θ x) u = pairF P (fun x => b x.2 • Θ x) u := by
    simp only [hb]
  rw [e1, wlm_pairF_sub hP (hm.dy k) hsd hu, hdy, e3]

/-! ### Main theorem -/

theorem weakLapMul : WeakLapMul := by
  intro P ν hP c hc u a du hu hA hdu hHa hHd
  intro Θ hΘ
  have hcΘ : IsPhaseTest P (fun x => c x.2 • Θ x) := wlm_phase_mulT hc hΘ
  have hsd : ∀ k : Fin 3, ContDiff ℝ ∞ (sd k c) :=
    fun k => UnforcedLeray.PhaseSpace.contDiff_sd hc k
  have hsdd : ∀ k : Fin 3, Differentiable ℝ (sd k c) :=
    fun k => (hsd k).differentiable (by simp)
  have hlap : ContDiff ℝ ∞ (lapS c) := by
    unfold lapS
    exact ContDiff.sum fun j _ =>
      UnforcedLeray.PhaseSpace.contDiff_sd (UnforcedLeray.PhaseSpace.contDiff_sd hc j) j
  have hsk : ∀ k : Fin 3, ContDiff ℝ ∞ (fun y => 2 * ν * sd k c y) :=
    fun k => contDiff_const.mul (hsd k)
  have hbk : ∀ k : Fin 3, ∀ y, sd k (fun y => 2 * ν * sd k c y) y = 2 * ν * sd k (sd k c) y :=
    fun k y => wlm_sd_const_mul (hsdd k) (2 * ν) k y
  have hL1 : pairF P (nuLapT ν Θ) (fun x => c x.2 • u x) =
      pairF P (fun x => c x.2 • nuLapT ν Θ x) u :=
    wlm_pairF_swap P (fun x => c x.2) (nuLapT ν Θ) u
  have key : (fun x => c x.2 • nuLapT ν Θ x) = fun x =>
      nuLapT ν (fun y => c y.2 • Θ y) x - (2 * ν * sd 0 c x.2) • dy 0 Θ x
        - (2 * ν * sd 1 c x.2) • dy 1 Θ x - (2 * ν * sd 2 c x.2) • dy 2 Θ x
        - (ν * lapS c x.2) • Θ x := by
    funext x
    have h1 : lapT (fun y => c y.2 • Θ y) x =
        c x.2 • lapT Θ x + ∑ j : Fin 3, (2 * sd j c x.2) • dy j Θ x + lapS c x.2 • Θ x :=
      lapT_mulT_apply hc hΘ.smooth x
    show c x.2 • (ν • lapT Θ x) = ν • lapT (fun y => c y.2 • Θ y) x
        - (2 * ν * sd 0 c x.2) • dy 0 Θ x - (2 * ν * sd 1 c x.2) • dy 1 Θ x
        - (2 * ν * sd 2 c x.2) • dy 2 Θ x - (ν * lapS c x.2) • Θ x
    rw [h1, Fin.sum_univ_three]
    module
  have hA1 : IsPhaseTest P (nuLapT ν (fun y => c y.2 • Θ y)) := hcΘ.lapT.const_smul ν
  have hk1 : ∀ k : Fin 3, IsPhaseTest P (fun x => (2 * ν * sd k c x.2) • dy k Θ x) :=
    fun k => wlm_phase_mulT (hsk k) (hΘ.dy k)
  have hP1 : IsPhaseTest P (fun x => nuLapT ν (fun y => c y.2 • Θ y) x
      - (2 * ν * sd 0 c x.2) • dy 0 Θ x) := hA1.sub (hk1 0)
  have hP2 : IsPhaseTest P (fun x => nuLapT ν (fun y => c y.2 • Θ y) x
      - (2 * ν * sd 0 c x.2) • dy 0 Θ x - (2 * ν * sd 1 c x.2) • dy 1 Θ x) :=
    hP1.sub (hk1 1)
  have hP3 : IsPhaseTest P (fun x => nuLapT ν (fun y => c y.2 • Θ y) x
      - (2 * ν * sd 0 c x.2) • dy 0 Θ x - (2 * ν * sd 1 c x.2) • dy 1 Θ x
      - (2 * ν * sd 2 c x.2) • dy 2 Θ x) := hP2.sub (hk1 2)
  have hC : IsPhaseTest P (fun x => (ν * lapS c x.2) • Θ x) :=
    wlm_phase_mulT (contDiff_const.mul hlap) hΘ
  rw [hL1, key, wlm_pairF_sub hP hP3 hC hu, wlm_pairF_sub hP hP2 (hk1 2) hu,
    wlm_pairF_sub hP hP1 (hk1 1) hu, wlm_pairF_sub hP hA1 (hk1 0) hu]
  rw [wlm_W1 (k := 0) hP hΘ hu (hHd 0) (a := fun y => 2 * ν * sd 0 c y)
      (b := fun y => 2 * ν * sd 0 (sd 0 c) y) (hsk 0) (hbk 0),
    wlm_W1 (k := 1) hP hΘ hu (hHd 1) (a := fun y => 2 * ν * sd 1 c y)
      (b := fun y => 2 * ν * sd 1 (sd 1 c) y) (hsk 1) (hbk 1),
    wlm_W1 (k := 2) hP hΘ hu (hHd 2) (a := fun y => 2 * ν * sd 2 c y)
      (b := fun y => 2 * ν * sd 2 (sd 2 c) y) (hsk 2) (hbk 2)]
  have eA : pairF P (nuLapT ν (fun y => c y.2 • Θ y)) u = pairF P Θ (fun x => c x.2 • a x) := by
    rw [hHa _ hcΘ]
    exact (wlm_pairF_swap P (fun x => c x.2) Θ a).symm
  have eDa : ∀ k : Fin 3, pairF P (fun x => (2 * ν * sd k c x.2) • Θ x) (du k) =
      pairF P Θ (fun x => (2 * ν * sd k c x.2) • du k x) := fun k =>
    (wlm_pairF_swap P (fun x => 2 * ν * sd k c x.2) Θ (du k)).symm
  have eC : pairF P (fun x => (ν * lapS c x.2) • Θ x) u =
      pairF P Θ (fun x => (ν * lapS c x.2) • u x) :=
    (wlm_pairF_swap P (fun x => ν * lapS c x.2) Θ u).symm
  have hRHS : (fun x => c x.2 • a x + (2 * ν) • ∑ k : Fin 3, sd k c x.2 • du k x
      + (ν * lapS c x.2) • u x) = fun x =>
      ((c x.2 • a x + (2 * ν * sd 0 c x.2) • du 0 x) + (2 * ν * sd 1 c x.2) • du 1 x)
        + (2 * ν * sd 2 c x.2) • du 2 x + (ν * lapS c x.2) • u x := by
    funext x
    simp only [Fin.sum_univ_three]
    module
  have iG0 : Integrable (fun z => dotL (Θ z) (c z.2 • a z)) (muP P) :=
    wlm_integrable_scal hP hc hΘ hA
  have iG1 : ∀ k : Fin 3, Integrable (fun z => dotL (Θ z) ((2 * ν * sd k c z.2) • du k z))
      (muP P) := fun k => wlm_integrable_scal hP (hsk k) hΘ (hdu k)
  have iG4 : Integrable (fun z => dotL (Θ z) ((ν * lapS c z.2) • u z)) (muP P) :=
    wlm_integrable_scal hP (contDiff_const.mul hlap) hΘ hu
  have i_a := wlm_integrable_add_right iG0 (iG1 0)
  have i_b := wlm_integrable_add_right i_a (iG1 1)
  have i_c := wlm_integrable_add_right i_b (iG1 2)
  rw [hRHS, wlm_pairF_add_right i_c iG4, wlm_pairF_add_right i_b (iG1 2),
    wlm_pairF_add_right i_a (iG1 1), wlm_pairF_add_right iG0 (iG1 0), eA, eDa 0, eDa 1, eDa 2, eC]
  have hf0 : IsPhaseTest P (fun x => (2 * ν * sd 0 (sd 0 c) x.2) • Θ x) :=
    wlm_phase_mulT (contDiff_const.mul (UnforcedLeray.PhaseSpace.contDiff_sd
      (hsd 0) 0)) hΘ
  have hf1 : IsPhaseTest P (fun x => (2 * ν * sd 1 (sd 1 c) x.2) • Θ x) :=
    wlm_phase_mulT (contDiff_const.mul (UnforcedLeray.PhaseSpace.contDiff_sd
      (hsd 1) 1)) hΘ
  have hf2 : IsPhaseTest P (fun x => (2 * ν * sd 2 (sd 2 c) x.2) • Θ x) :=
    wlm_phase_mulT (contDiff_const.mul (UnforcedLeray.PhaseSpace.contDiff_sd
      (hsd 2) 2)) hΘ
  have hf01 : IsPhaseTest P (fun x => (2 * ν * sd 0 (sd 0 c) x.2) • Θ x
      + (2 * ν * sd 1 (sd 1 c) x.2) • Θ x) := hf0.add hf1
  have hsumfun : (fun x => (2 * ν * sd 0 (sd 0 c) x.2) • Θ x
      + (2 * ν * sd 1 (sd 1 c) x.2) • Θ x + (2 * ν * sd 2 (sd 2 c) x.2) • Θ x) =
      fun x => (2 : ℝ) • ((ν * lapS c x.2) • Θ x) := by
    funext x
    simp only [lapS, Fin.sum_univ_three]
    module
  have hPb : pairF P (fun x => (2 * ν * sd 0 (sd 0 c) x.2) • Θ x) u
      + pairF P (fun x => (2 * ν * sd 1 (sd 1 c) x.2) • Θ x) u
      + pairF P (fun x => (2 * ν * sd 2 (sd 2 c) x.2) • Θ x) u
      = 2 * pairF P Θ (fun x => (ν * lapS c x.2) • u x) := by
    rw [← wlm_pairF_add hP hf0 hf1 hu, ← wlm_pairF_add hP hf01 hf2 hu, hsumfun,
      wlm_pairF_const_smul, ← eC]
    push_cast
    ring
  linear_combination hPb

end UnforcedLeray.Short.PartIIIb.Concrete
