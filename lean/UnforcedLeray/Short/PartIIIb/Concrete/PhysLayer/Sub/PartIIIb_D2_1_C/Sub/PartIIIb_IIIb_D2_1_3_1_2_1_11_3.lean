import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_11
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.PairCont

/-!
# `WeakLapLin`: linearity of the weak relation `HasPtwOp (nuLapT ν)`

Source `the November 2 reference manuscript` lines 1334-1337, 1351-1362, 1470-1480.
Sums and real multiples follow from the phase-test pairing identities (integrability from
`LocL2`); the cross product uses `lapT (e × Θ) = e × lapT Θ` and `⟪a, e × b⟫ = -⟪e × a, b⟫`.
Helpers are local (prefix `wlq_`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-! ### Scalars and the bilinear pairing -/

theorem wlq_dotL_smul_left (r : ℝ) (a b : CVec3) : dotL (r • a) b = (r : ℂ) • dotL a b := by
  simp [dotL_apply, Finset.mul_sum]

theorem wlq_dotL_smul_right (r : ℝ) (a b : CVec3) : dotL a (r • b) = (r : ℂ) • dotL a b := by
  simp [dotL_apply, Finset.mul_sum]

theorem wlq_dotL_cross (e a b : CVec3) : dotL (crossC e a) b = -dotL a (crossC e b) := by
  simp [dotL_apply, crossC, Fin.sum_univ_three]
  ring

theorem wlq_dotL_cross' (e a b : CVec3) : dotL a (crossC e b) = -dotL (crossC e a) b := by
  rw [wlq_dotL_cross, neg_neg]

/-! ### Linear maps -/

/-- The `ℝ`-linear map `b ↦ a × b` on `ℂ³`. -/
def wlqLin (a : CVec3) : CVec3 →ₗ[ℝ] CVec3 where
  toFun := crossC a
  map_add' b c := by
    ext i
    fin_cases i <;> simp [crossC] <;> ring
  map_smul' r b := by
    ext i
    fin_cases i <;> simp [crossC, Complex.real_smul] <;> ring

/-- The continuous `ℝ`-linear map `b ↦ a × b` on `ℂ³`. -/
def wlqL (a : CVec3) : CVec3 →L[ℝ] CVec3 :=
  { toLinearMap := wlqLin a
    cont := by
      show Continuous (crossC a)
      unfold crossC
      fun_prop }

theorem wlqL_apply (a b : CVec3) : wlqL a b = crossC a b := rfl

theorem wlq_dy_clm {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] {L : CVec3 →L[ℝ] F'}
    {F : ℝ × Space → CVec3} (hF : Differentiable ℝ F) (j : Fin 3) :
    dy j (fun p => L (F p)) = fun p => L (dy j F p) := by
  funext p
  have h := ((L.hasFDerivAt).comp p (hF p).hasFDerivAt).fderiv
  simp only [dy]
  rw [show (fun q => L (F q)) = L ∘ F from rfl, h]
  rfl

theorem wlq_phase_cross (e : CVec3) {P : ℝ} {Θ : ℝ × Space → CVec3} (hΘ : IsPhaseTest P Θ) :
    IsPhaseTest P (fun x => crossC e (Θ x)) :=
  hΘ.clm_comp (wlqL e)

/-! ### `lapT` commutes with the cross product -/

theorem wlq_crossC_sum (e : CVec3) {ι : Type*} (s : Finset ι) (f : ι → CVec3) :
    crossC e (∑ i ∈ s, f i) = ∑ i ∈ s, crossC e (f i) :=
  map_sum (wlqL e) f s

theorem wlq_lapT_crossC {P : ℝ} {Θ : ℝ × Space → CVec3} (hΘ : IsPhaseTest P Θ) (e : CVec3) :
    lapT (fun p => crossC e (Θ p)) = fun p => crossC e (lapT Θ p) := by
  have hΘd : Differentiable ℝ Θ := hΘ.smooth.differentiable (by simp)
  have hd : ∀ j : Fin 3, Differentiable ℝ (dy j Θ) := fun j =>
    (hΘ.dy j).smooth.differentiable (by simp)
  have hd1 : ∀ j : Fin 3, dy j (fun p => crossC e (Θ p)) = fun p => crossC e (dy j Θ p) :=
    fun j => wlq_dy_clm (L := wlqL e) hΘd j
  have hd2 : ∀ j : Fin 3, dy j (fun p => crossC e (dy j Θ p)) =
      fun p => crossC e (dy j (dy j Θ) p) :=
    fun j => wlq_dy_clm (L := wlqL e) (hd j) j
  funext p
  simp only [lapT, hd1, hd2]
  exact (wlq_crossC_sum e _ _).symm

theorem wlq_crossC_nuLapT {P : ℝ} {Θ : ℝ × Space → CVec3} (hΘ : IsPhaseTest P Θ) (e : CVec3)
    (ν : ℝ) :
    (fun x => crossC e (nuLapT ν Θ x)) = nuLapT ν (fun p => crossC e (Θ p)) := by
  funext x
  show crossC e (ν • lapT Θ x) = ν • lapT (fun p => crossC e (Θ p)) x
  rw [wlq_lapT_crossC hΘ e]
  exact map_smul (wlqL e) ν (lapT Θ x)

/-! ### Integrability and pairing identities -/

theorem wlq_isInYr_cont {P : ℝ} (hP : 0 < P) {Ψ : ℝ × Space → CVec3} (hc : Continuous Ψ)
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

theorem wlq_isInYr_test {P : ℝ} (hP : 0 < P) {Θ : ℝ × Space → CVec3} (hΘ : IsPhaseTest P Θ) :
    UnforcedLeray.Short.IIb.IsInYr P 2 Θ := by
  obtain ⟨R, hR⟩ := hΘ.bounded_support
  exact wlq_isInYr_cont hP hΘ.continuous hΘ.periodic hR

theorem wlq_ae_y_ne (P : ℝ) : ∀ᵐ z ∂(muP P), z.2 ≠ 0 := by
  rw [ae_iff]
  have hset : {z : ℝ × Space | ¬ (z.2 ≠ 0)} = (univ : Set ℝ) ×ˢ ({0} : Set Space) := by
    ext z; simp
  rw [hset, muP, Measure.prod_prod, measure_singleton, mul_zero]

/-- Pairing of a phase test with a locally `L²` field is integrable on the phase measure. -/
theorem wlq_integrable {P : ℝ} (hP : 0 < P) {Θ u : ℝ × Space → CVec3} (hΘ : IsPhaseTest P Θ)
    (hu : LocL2 P u) : Integrable (fun z => dotL (Θ z) (u z)) (muP P) := by
  rcases hu with hY | hH
  · exact dot_integrable hP (wlq_isInYr_test hP hΘ) hY
  · obtain ⟨R, hR⟩ := hΘ.bounded_support
    have hYh : UnforcedLeray.Short.IIb.IsInYr P 2 (fun z : ℝ × Space => (‖z.2‖ : ℝ) • Θ z) := by
      refine wlq_isInYr_cont hP ?_ ?_ (R := R) ?_
      · exact (continuous_norm.comp continuous_snd).smul hΘ.continuous
      · intro τ y; simp [hΘ.periodic τ y]
      · intro τ y hy; simp [hR τ y hy]
    have hh := dot_integrable hP hYh hH
    refine hh.congr ?_
    filter_upwards [wlq_ae_y_ne P] with z hz
    have hn : ‖z.2‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    show dotL ((‖z.2‖ : ℝ) • Θ z) ((‖z.2‖⁻¹ : ℝ) • u z) = dotL (Θ z) (u z)
    rw [wlq_dotL_smul_left, wlq_dotL_smul_right, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      ← Complex.ofReal_mul, mul_inv_cancel₀ hn, Complex.ofReal_one, one_mul]

theorem wlq_integrable_add_right {P : ℝ} {X Y Z : ℝ × Space → CVec3}
    (hY : Integrable (fun z => dotL (X z) (Y z)) (muP P))
    (hZ : Integrable (fun z => dotL (X z) (Z z)) (muP P)) :
    Integrable (fun z => dotL (X z) (Y z + Z z)) (muP P) :=
  (hY.add hZ).congr (ae_of_all _ fun z => by simp [map_add])

theorem wlq_pairF_add_right {P : ℝ} {X Y Z : ℝ × Space → CVec3}
    (hY : Integrable (fun z => dotL (X z) (Y z)) (muP P))
    (hZ : Integrable (fun z => dotL (X z) (Z z)) (muP P)) :
    pairF P X (fun x => Y x + Z x) = pairF P X Y + pairF P X Z := by
  rw [pair_eq_integral P X Y hY, pair_eq_integral P X Z hZ,
    pair_eq_integral P X (fun x => Y x + Z x) (wlq_integrable_add_right hY hZ)]
  simp only [map_add, add_apply]
  rw [integral_add hY hZ, smul_add]

theorem wlq_pairF_sub_left {P : ℝ} (hP : 0 < P) {X Y u : ℝ × Space → CVec3}
    (hX : IsPhaseTest P X) (hY : IsPhaseTest P Y) (hu : LocL2 P u) :
    pairF P (fun x => X x + Y x) u = pairF P X u + pairF P Y u := by
  have hXY : IsPhaseTest P (fun x => X x + Y x) := hX.add hY
  have iXY := wlq_integrable hP hXY hu
  have iX := wlq_integrable hP hX hu
  have iY := wlq_integrable hP hY hu
  rw [pair_eq_integral P _ _ iXY, pair_eq_integral P _ _ iX, pair_eq_integral P _ _ iY]
  simp only [map_add, add_apply]
  rw [integral_add iX iY, smul_add]

/-- Swapping a real scalar function from the field to the test side (pointwise). -/
theorem wlq_pairF_swap (P : ℝ) (s : ℝ × Space → ℝ) (X u : ℝ × Space → CVec3) :
    pairF P X (fun x => s x • u x) = pairF P (fun x => s x • X x) u := by
  simp only [pairF, phaseInt, wlq_dotL_smul_left, wlq_dotL_smul_right]

theorem wlq_pairF_const_smul (P : ℝ) (r : ℝ) (X u : ℝ × Space → CVec3) :
    pairF P (fun x => r • X x) u = (r : ℂ) * pairF P X u := by
  simp only [pairF, phaseInt, wlq_dotL_smul_left, integral_smul, Complex.real_smul]
  ring

theorem wlq_pairF_const_smul_right (P : ℝ) (r : ℝ) (X Y : ℝ × Space → CVec3) :
    pairF P X (fun x => r • Y x) = (r : ℂ) * pairF P X Y := by
  simp only [pairF, phaseInt, wlq_dotL_smul_right, integral_smul, Complex.real_smul]
  ring

theorem wlq_pairF_cross_right (P : ℝ) (e : CVec3) (Θ D : ℝ × Space → CVec3) :
    pairF P Θ (fun x => crossC e (D x)) = -pairF P (fun x => crossC e (Θ x)) D := by
  simp only [pairF, phaseInt, wlq_dotL_cross', integral_neg, smul_neg]

/-! ### Main theorem -/

theorem weakLapLin : WeakLapLin := by
  intro P ν hP u1 u2 a1 a2 hu1 hu2 ha1 ha2 hHa1 hHa2
  refine ⟨?_, ?_, ?_⟩
  · intro Θ hΘ
    have hL : IsPhaseTest P (nuLapT ν Θ) := hΘ.lapT.const_smul ν
    rw [wlq_pairF_add_right (wlq_integrable hP hL hu1) (wlq_integrable hP hL hu2),
      wlq_pairF_add_right (wlq_integrable hP hΘ ha1) (wlq_integrable hP hΘ ha2),
      hHa1 Θ hΘ, hHa2 Θ hΘ]
  · intro s Θ hΘ
    have hL : IsPhaseTest P (nuLapT ν Θ) := hΘ.lapT.const_smul ν
    have e1 : pairF P (nuLapT ν Θ) (fun x => s • u1 x) =
        pairF P (fun x => s • nuLapT ν Θ x) u1 :=
      wlq_pairF_swap P (fun _ => s) (nuLapT ν Θ) u1
    rw [e1, wlq_pairF_const_smul, hHa1 Θ hΘ, wlq_pairF_const_smul_right]
  · intro e Θ hΘ
    have hΞ := wlq_phase_cross e hΘ
    rw [wlq_pairF_cross_right P e (nuLapT ν Θ) u1, wlq_crossC_nuLapT hΘ e ν, hHa1 _ hΞ,
      wlq_pairF_cross_right P e Θ a1]

end UnforcedLeray.Short.PartIIIb.Concrete
