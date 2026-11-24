import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_11
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.PairCont

/-!
# `WeakLapPsi`: `νΔψ = -ν ∑ₖ eₖ × ∂ₖΦ` weakly

Source `the November 2 reference manuscript` lines 1334-1337, 1351-1362, 1470-1480.
Proof: `lapT Θ = ∇(div Θ) - curl(curl Θ)` for a phase test `Θ` (symmetry of second `y`-derivatives),
`∇(div Θ)` is killed by the weak solenoidality of `ψ`, `curl(curl Θ)` is moved to `Φ` by the weak
curl relation `curl ψ = Φ`, and `⟪e × ∂ₖΘ, Φ⟫ = -⟪e × Θ, ∂ₖΦ⟫` by the weak gradient of `Φ`.
Helpers are local (prefix `wlp_`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-! ### Scalars and the bilinear pairing -/

theorem wlp_dotL_smul_left (r : ℝ) (a b : CVec3) : dotL (r • a) b = (r : ℂ) • dotL a b := by
  simp [dotL_apply, Finset.mul_sum]

theorem wlp_dotL_smul_right (r : ℝ) (a b : CVec3) : dotL a (r • b) = (r : ℂ) • dotL a b := by
  simp [dotL_apply, Finset.mul_sum]

/-! ### Linear maps -/

/-- The `ℝ`-linear map `b ↦ a × b` on `ℂ³`. -/
def wlpLin (a : CVec3) : CVec3 →ₗ[ℝ] CVec3 where
  toFun := crossC a
  map_add' b c := by
    ext i
    fin_cases i <;> simp [crossC] <;> ring
  map_smul' r b := by
    ext i
    fin_cases i <;> simp [crossC, Complex.real_smul] <;> ring

/-- The continuous `ℝ`-linear map `b ↦ a × b` on `ℂ³`. -/
def wlpL (a : CVec3) : CVec3 →L[ℝ] CVec3 :=
  { toLinearMap := wlpLin a
    cont := by
      show Continuous (crossC a)
      unfold crossC
      fun_prop }

theorem wlpL_apply (a b : CVec3) : wlpL a b = crossC a b := rfl

/-- The `ℝ`-linear map `v ↦ v j` (the `j`-th component). -/
def wlpC (j : Fin 3) : CVec3 →L[ℝ] ℂ :=
  (EuclideanSpace.proj j : CVec3 →L[ℂ] ℂ).restrictScalars ℝ

theorem wlpC_apply (j : Fin 3) (v : CVec3) : wlpC j v = v j := rfl

/-! ### Derivatives commute with continuous linear maps and finite sums -/

theorem wlp_dy_clm {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] {L : CVec3 →L[ℝ] F'}
    {F : ℝ × Space → CVec3} (hF : Differentiable ℝ F) (j : Fin 3) :
    dy j (fun p => L (F p)) = fun p => L (dy j F p) := by
  funext p
  have h := ((L.hasFDerivAt).comp p (hF p).hasFDerivAt).fderiv
  simp only [dy]
  rw [show (fun q => L (F q)) = L ∘ F from rfl, h]
  rfl

theorem wlp_dy_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}
    (s : Finset ι) {G : ι → ℝ × Space → E} (hG : ∀ i ∈ s, Differentiable ℝ (G i)) (j : Fin 3) :
    dy j (fun x => ∑ i ∈ s, G i x) = fun x => ∑ i ∈ s, dy j (G i) x := by
  funext p
  have hf : (fun x => ∑ i ∈ s, G i x) = ∑ i ∈ s, G i := by
    funext x; simp [Finset.sum_apply]
  simp only [dy]
  rw [hf, fderiv_sum fun i hi => (hG i hi) p]
  simp

/-! ### Phase tests -/

theorem wlp_phase_cross (e : CVec3) {P : ℝ} {Θ : ℝ × Space → CVec3} (hΘ : IsPhaseTest P Θ) :
    IsPhaseTest P (fun x => crossC e (Θ x)) :=
  hΘ.clm_comp (wlpL e)

theorem wlp_isPhaseTest_curlT {P : ℝ} {Θ : ℝ × Space → CVec3} (hΘ : IsPhaseTest P Θ) :
    IsPhaseTest P (curlT Θ) := by
  have h : curlT Θ = ∑ k : Fin 3, (fun x => wlpL (EuclideanSpace.single k (1 : ℂ)) (dy k Θ x)) := by
    funext x
    simp [curlT, Finset.sum_apply, wlpL_apply]
  rw [h]
  exact IsPhaseTest.sum Finset.univ fun k _ => (hΘ.dy k).clm_comp _

theorem wlp_isPhaseTest_divC {P : ℝ} {Θ : ℝ × Space → CVec3} (hΘ : IsPhaseTest P Θ) :
    IsPhaseTest P (fun x => ∑ j : Fin 3, wlpC j (dy j Θ x)) := by
  have h := IsPhaseTest.sum (F := ℂ) Finset.univ
    (Φ := fun j x => wlpC j (dy j Θ x)) (fun j _ => (hΘ.dy j).clm_comp (wlpC j))
  rw [Finset.sum_fn] at h
  exact h

/-! ### Algebra -/

theorem wlp_dotL_cross (e a b : CVec3) : dotL (crossC e a) b = -dotL a (crossC e b) := by
  simp [dotL_apply, crossC, Fin.sum_univ_three]
  ring

theorem wlp_dotL_cross' (e a b : CVec3) : dotL a (crossC e b) = -dotL (crossC e a) b := by
  rw [wlp_dotL_cross, neg_neg]

/-- The vector identity `∑ⱼ eⱼ × (∑ₖ eₖ × Mⱼₖ) = ∑ₖ (∑ⱼ (Mⱼₖ)ⱼ) eₖ - ∑ⱼ Mⱼⱼ`. -/
theorem wlp_curl_curl_alg (M : Fin 3 → Fin 3 → CVec3) :
    ∑ j : Fin 3, crossC (EuclideanSpace.single j (1 : ℂ))
        (∑ k : Fin 3, crossC (EuclideanSpace.single k (1 : ℂ)) (M j k))
      = ∑ k : Fin 3, (∑ j : Fin 3, wlpC j (M j k)) • EuclideanSpace.single k (1 : ℂ)
        - ∑ j : Fin 3, M j j := by
  ext i
  fin_cases i <;> simp [crossC, Fin.sum_univ_three, EuclideanSpace.single_apply, wlpC_apply] <;> ring

/-! ### The weak curl of `∂`, and the vector Laplacian identity -/

theorem wlp_dy_curlT {P : ℝ} {Θ : ℝ × Space → CVec3} (hΘ : IsPhaseTest P Θ) (j : Fin 3)
    (x : ℝ × Space) :
    dy j (curlT Θ) x = ∑ k : Fin 3, crossC (EuclideanSpace.single k (1 : ℂ)) (dy j (dy k Θ) x) := by
  have hd : ∀ k : Fin 3, Differentiable ℝ (dy k Θ) := fun k =>
    (hΘ.dy k).smooth.differentiable (by simp)
  have hcurl : curlT Θ = fun x => ∑ k : Fin 3,
      wlpL (EuclideanSpace.single k (1 : ℂ)) (dy k Θ x) := by
    funext x
    simp [curlT, wlpL_apply]
  have h1 : dy j (curlT Θ) = fun x => ∑ k : Fin 3,
      dy j (fun p => wlpL (EuclideanSpace.single k (1 : ℂ)) (dy k Θ p)) x := by
    rw [hcurl, wlp_dy_sum Finset.univ (G := fun k p =>
      wlpL (EuclideanSpace.single k (1 : ℂ)) (dy k Θ p))
      (fun k _ => (wlpL _).differentiable.comp (hd k)) j]
  rw [h1]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [wlp_dy_clm (L := wlpL (EuclideanSpace.single k (1 : ℂ))) (hd k) j]
  rfl

/-- **Vector Laplacian identity** for a phase test:
`ΔΘ = ∇(div Θ) - curl(curl Θ)`, with `div Θ = ∑ⱼ (∂ⱼΘ)ⱼ`. -/
theorem wlp_lapT_identity {P : ℝ} {Θ : ℝ × Space → CVec3} (hΘ : IsPhaseTest P Θ) :
    lapT Θ = fun x => gradT (fun x => ∑ j : Fin 3, wlpC j (dy j Θ x)) x - curlT (curlT Θ) x := by
  funext x
  have hd : ∀ k : Fin 3, Differentiable ℝ (dy k Θ) := fun k =>
    (hΘ.dy k).smooth.differentiable (by simp)
  have hdiv : ∀ k : Fin 3, dy k (fun x => ∑ j : Fin 3, wlpC j (dy j Θ x)) x =
      ∑ j : Fin 3, wlpC j (dy k (dy j Θ) x) := by
    intro k
    rw [wlp_dy_sum Finset.univ (G := fun j p => wlpC j (dy j Θ p))
      (fun j _ => (wlpC j).differentiable.comp (hd j)) k]
    simp only [Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [wlp_dy_clm (L := wlpC j) (hd j) k]
  have hcc : curlT (curlT Θ) x = ∑ j : Fin 3, crossC (EuclideanSpace.single j (1 : ℂ))
      (∑ k : Fin 3, crossC (EuclideanSpace.single k (1 : ℂ)) (dy j (dy k Θ) x)) := by
    show ∑ j : Fin 3, crossC (EuclideanSpace.single j (1 : ℂ)) (dy j (curlT Θ) x) = _
    simp only [wlp_dy_curlT hΘ]
  have hsym : ∀ j k : Fin 3, dy j (dy k Θ) x = dy k (dy j Θ) x := fun j k =>
    congrFun (dy_dy_comm hΘ.smooth j k) x
  rw [hcc, wlp_curl_curl_alg]
  have hgrad : gradT (fun x => ∑ j : Fin 3, wlpC j (dy j Θ x)) x =
      ∑ k : Fin 3, (∑ j : Fin 3, wlpC j (dy k (dy j Θ) x)) • EuclideanSpace.single k (1 : ℂ) := by
    simp only [gradT, hdiv]
  have hM : ∀ k : Fin 3, (∑ j : Fin 3, wlpC j (dy j (dy k Θ) x)) =
      ∑ j : Fin 3, wlpC j (dy k (dy j Θ) x) := fun k =>
    Finset.sum_congr rfl fun j _ => by rw [hsym j k]
  rw [hgrad]
  simp only [hM, sub_sub_cancel, lapT]

/-! ### Integrability and pairing identities -/

theorem wlp_isInYr_cont {P : ℝ} (hP : 0 < P) {Ψ : ℝ × Space → CVec3} (hc : Continuous Ψ)
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

theorem wlp_isInYr_test {P : ℝ} (hP : 0 < P) {Θ : ℝ × Space → CVec3} (hΘ : IsPhaseTest P Θ) :
    UnforcedLeray.Short.IIb.IsInYr P 2 Θ := by
  obtain ⟨R, hR⟩ := hΘ.bounded_support
  exact wlp_isInYr_cont hP hΘ.continuous hΘ.periodic hR

theorem wlp_ae_y_ne (P : ℝ) : ∀ᵐ z ∂(muP P), z.2 ≠ 0 := by
  rw [ae_iff]
  have hset : {z : ℝ × Space | ¬ (z.2 ≠ 0)} = (univ : Set ℝ) ×ˢ ({0} : Set Space) := by
    ext z; simp
  rw [hset, muP, Measure.prod_prod, measure_singleton, mul_zero]

/-- Pairing of a phase test with a locally `L²` field is integrable on the phase measure. -/
theorem wlp_integrable {P : ℝ} (hP : 0 < P) {Θ u : ℝ × Space → CVec3} (hΘ : IsPhaseTest P Θ)
    (hu : LocL2 P u) : Integrable (fun z => dotL (Θ z) (u z)) (muP P) := by
  rcases hu with hY | hH
  · exact dot_integrable hP (wlp_isInYr_test hP hΘ) hY
  · obtain ⟨R, hR⟩ := hΘ.bounded_support
    have hYh : UnforcedLeray.Short.IIb.IsInYr P 2 (fun z : ℝ × Space => (‖z.2‖ : ℝ) • Θ z) := by
      refine wlp_isInYr_cont hP ?_ ?_ (R := R) ?_
      · exact (continuous_norm.comp continuous_snd).smul hΘ.continuous
      · intro τ y; simp [hΘ.periodic τ y]
      · intro τ y hy; simp [hR τ y hy]
    have hh := dot_integrable hP hYh hH
    refine hh.congr ?_
    filter_upwards [wlp_ae_y_ne P] with z hz
    have hn : ‖z.2‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    show dotL ((‖z.2‖ : ℝ) • Θ z) ((‖z.2‖⁻¹ : ℝ) • u z) = dotL (Θ z) (u z)
    rw [wlp_dotL_smul_left, wlp_dotL_smul_right, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      ← Complex.ofReal_mul, mul_inv_cancel₀ hn, Complex.ofReal_one, one_mul]

/-! ### Pairing identities -/

theorem wlp_pairF_zero_of_nonpos {P : ℝ} (X u : ℝ × Space → CVec3) (hP : P ≤ 0) :
    pairF P X u = 0 := by
  simp [pairF, phaseInt, Set.Ioc_eq_empty_of_le hP]

theorem wlp_pairF_sub {P : ℝ} (hP : 0 < P) {X Y u : ℝ × Space → CVec3} (hX : IsPhaseTest P X)
    (hY : IsPhaseTest P Y) (hu : LocL2 P u) :
    pairF P (fun x => X x - Y x) u = pairF P X u - pairF P Y u := by
  have hXY : IsPhaseTest P (fun x => X x - Y x) := hX.sub hY
  have iXY := wlp_integrable hP hXY hu
  have iX := wlp_integrable hP hX hu
  have iY := wlp_integrable hP hY hu
  rw [pair_eq_integral P _ _ iXY, pair_eq_integral P _ _ iX, pair_eq_integral P _ _ iY]
  simp only [map_sub, sub_apply]
  rw [integral_sub iX iY, smul_sub]

theorem wlp_pairF_neg (P : ℝ) (X u : ℝ × Space → CVec3) :
    pairF P (-X) u = -pairF P X u := by
  simp only [pairF, phaseInt, Pi.neg_apply, map_neg, neg_apply, integral_neg, smul_neg]

theorem wlp_pairF_const_smul (P : ℝ) (r : ℝ) (X u : ℝ × Space → CVec3) :
    pairF P (fun x => r • X x) u = (r : ℂ) * pairF P X u := by
  simp only [pairF, phaseInt, wlp_dotL_smul_left, integral_smul, Complex.real_smul]
  ring

theorem wlp_pairF_const_smul_right (P : ℝ) (r : ℝ) (X Y : ℝ × Space → CVec3) :
    pairF P X (fun x => r • Y x) = (r : ℂ) * pairF P X Y := by
  simp only [pairF, phaseInt, wlp_dotL_smul_right, integral_smul, Complex.real_smul]
  ring

theorem wlp_pairF_fsum_left {P : ℝ} (hP : 0 < P) {ι : Type*} (s : Finset ι)
    (X : ι → ℝ × Space → CVec3) (hX : ∀ i ∈ s, IsPhaseTest P (X i)) (u : ℝ × Space → CVec3)
    (hu : LocL2 P u) :
    pairF P (fun x => ∑ i ∈ s, X i x) u = ∑ i ∈ s, pairF P (X i) u := by
  have hsum : IsPhaseTest P (fun x => ∑ i ∈ s, X i x) := by
    have h := IsPhaseTest.sum s hX
    rw [Finset.sum_fn] at h
    exact h
  have hint : ∀ i ∈ s, Integrable (fun z => dotL (X i z) (u z)) (muP P) :=
    fun i hi => wlp_integrable hP (hX i hi) hu
  have hpt : ∀ z, dotL (∑ i ∈ s, X i z) (u z) = ∑ i ∈ s, dotL (X i z) (u z) := fun z => by
    rw [map_sum, ContinuousLinearMap.sum_apply]
  have hpair : ∀ i ∈ s, pairF P (X i) u = P⁻¹ • ∫ z, dotL (X i z) (u z) ∂(muP P) :=
    fun i hi => pair_eq_integral P (X i) u (hint i hi)
  rw [pair_eq_integral P _ u (wlp_integrable hP hsum hu), Finset.sum_congr rfl hpair,
    ← Finset.smul_sum]
  congr 1
  simp only [hpt]
  exact integral_finset_sum s hint

theorem wlp_pairF_fsum_right {P : ℝ} {ι : Type*} (s : Finset ι) {X : ℝ × Space → CVec3}
    (Y : ι → ℝ × Space → CVec3)
    (hY : ∀ i ∈ s, Integrable (fun z => dotL (X z) (Y i z)) (muP P)) :
    pairF P X (fun x => ∑ i ∈ s, Y i x) = ∑ i ∈ s, pairF P X (Y i) := by
  have hpt : ∀ z, dotL (X z) (∑ i ∈ s, Y i z) = ∑ i ∈ s, dotL (X z) (Y i z) := fun z =>
    map_sum _ _ _
  have hint : Integrable (fun z => dotL (X z) (∑ i ∈ s, Y i z)) (muP P) := by
    simp only [hpt]
    exact integrable_finset_sum s hY
  have hpair : ∀ i ∈ s, pairF P X (Y i) = P⁻¹ • ∫ z, dotL (X z) (Y i z) ∂(muP P) :=
    fun i hi => pair_eq_integral P X (Y i) (hY i hi)
  rw [pair_eq_integral P X _ hint, Finset.sum_congr rfl hpair, ← Finset.smul_sum]
  congr 1
  simp only [hpt]
  exact integral_finset_sum s hY

theorem wlp_pairF_cross_right (P : ℝ) (e : CVec3) (Θ D : ℝ × Space → CVec3) :
    pairF P Θ (fun x => crossC e (D x)) = -pairF P (fun x => crossC e (Θ x)) D := by
  simp only [pairF, phaseInt, wlp_dotL_cross', integral_neg, smul_neg]

theorem wlp_integrable_cross {P : ℝ} (hP : 0 < P) {Θ D : ℝ × Space → CVec3}
    (hΘ : IsPhaseTest P Θ) (hD : LocL2 P D) (e : CVec3) :
    Integrable (fun z => dotL (Θ z) (crossC e (D z))) (muP P) := by
  refine ((wlp_integrable hP (wlp_phase_cross e hΘ) hD).neg).congr (ae_of_all _ fun z => ?_)
  exact (wlp_dotL_cross' e (Θ z) (D z)).symm

/-- One direction of the weak curl identity: `⟪e × ∂ₖΘ, Φ⟫ = -⟪e × Θ, ∂ₖΦ⟫`. -/
theorem wlp_step {P : ℝ} {Θ Φ G : ℝ × Space → CVec3} (hΘ : IsPhaseTest P Θ) (k : Fin 3)
    (hdk : UnforcedLeray.Short.IIb.HasPtwOp P (fun Ψ => -dy k Ψ) Φ G) :
    pairF P (fun x => crossC (EuclideanSpace.single k (1 : ℂ)) (dy k Θ x)) Φ =
      -pairF P (fun x => crossC (EuclideanSpace.single k (1 : ℂ)) (Θ x)) G := by
  have hΞ : IsPhaseTest P (fun x => crossC (EuclideanSpace.single k (1 : ℂ)) (Θ x)) :=
    wlp_phase_cross _ hΘ
  have hdyΞ : (fun x => crossC (EuclideanSpace.single k (1 : ℂ)) (dy k Θ x)) =
      dy k (fun x => crossC (EuclideanSpace.single k (1 : ℂ)) (Θ x)) :=
    (wlp_dy_clm (L := wlpL (EuclideanSpace.single k (1 : ℂ)))
      (hΘ.smooth.differentiable (by simp)) k).symm
  have h : pairF P (-(dy k (fun x => crossC (EuclideanSpace.single k (1 : ℂ)) (Θ x)))) Φ =
      pairF P (fun x => crossC (EuclideanSpace.single k (1 : ℂ)) (Θ x)) G := hdk _ hΞ
  rw [wlp_pairF_neg] at h
  rw [hdyΞ]
  linear_combination -h

/-! ### Main theorem -/

theorem weakLapPsi : WeakLapPsi := by
  intro P ν μ D hD Θ hΘ
  rcases le_or_gt P 0 with hP0 | hP
  · rw [wlp_pairF_zero_of_nonpos _ _ hP0, wlp_pairF_zero_of_nonpos _ _ hP0]
  · have hLocψ : LocL2 P D.ψ := Or.inr hD.spΦ.hardy
    have hLocD : ∀ k : Fin 3, LocL2 P (D.DΦ k) := fun k => Or.inl (hD.dΦ k).1
    have hLocΦ : LocL2 P D.Φ := Or.inl hD.dom.mem
    have hdiv := wlp_isPhaseTest_divC hΘ
    have hcT := wlp_isPhaseTest_curlT hΘ
    have hcc := wlp_isPhaseTest_curlT hcT
    have hg : IsPhaseTest P (gradT (fun x => ∑ j : Fin 3, wlpC j (dy j Θ x))) := hdiv.gradT
    have F1 : pairF P (lapT Θ) D.ψ = -pairF P (curlT (curlT Θ)) D.ψ := by
      rw [wlp_lapT_identity hΘ, wlp_pairF_sub hP hg hcc hLocψ, hD.spΦ.sol _ hdiv, zero_sub]
    have F2 : pairF P (curlT (curlT Θ)) D.ψ = pairF P (curlT Θ) D.Φ := hD.spΦ.curl (curlT Θ) hcT
    have hX : ∀ k ∈ (Finset.univ : Finset (Fin 3)),
        IsPhaseTest P (fun x => crossC (EuclideanSpace.single k (1 : ℂ)) (dy k Θ x)) :=
      fun k _ => (hΘ.dy k).clm_comp (wlpL (EuclideanSpace.single k (1 : ℂ)))
    have F3 : pairF P (curlT Θ) D.Φ = -(pairF P (fun x => crossC (EuclideanSpace.single 0 (1 : ℂ)) (Θ x)) (D.DΦ 0)
        + pairF P (fun x => crossC (EuclideanSpace.single 1 (1 : ℂ)) (Θ x)) (D.DΦ 1)
        + pairF P (fun x => crossC (EuclideanSpace.single 2 (1 : ℂ)) (Θ x)) (D.DΦ 2)) := by
      show pairF P (fun x => ∑ k : Fin 3, crossC (EuclideanSpace.single k (1 : ℂ)) (dy k Θ x)) D.Φ = _
      rw [wlp_pairF_fsum_left hP Finset.univ
        (fun k x => crossC (EuclideanSpace.single k (1 : ℂ)) (dy k Θ x)) hX D.Φ hLocΦ,
        Fin.sum_univ_three, wlp_step hΘ 0 (hD.dΦ 0).2, wlp_step hΘ 1 (hD.dΦ 1).2,
        wlp_step hΘ 2 (hD.dΦ 2).2]
      ring
    have cross_k : ∀ k : Fin 3, pairF P Θ (fun x => crossC (EuclideanSpace.single k (1 : ℂ)) (D.DΦ k x))
        = -pairF P (fun x => crossC (EuclideanSpace.single k (1 : ℂ)) (Θ x)) (D.DΦ k) :=
      fun k => wlp_pairF_cross_right P _ Θ (D.DΦ k)
    have hR : pairF P Θ (fun x => -ν • ∑ k : Fin 3, crossC (EuclideanSpace.single k (1 : ℂ)) (D.DΦ k x))
        = ((-ν : ℝ) : ℂ) * (pairF P Θ (fun x => crossC (EuclideanSpace.single 0 (1 : ℂ)) (D.DΦ 0 x))
          + pairF P Θ (fun x => crossC (EuclideanSpace.single 1 (1 : ℂ)) (D.DΦ 1 x))
          + pairF P Θ (fun x => crossC (EuclideanSpace.single 2 (1 : ℂ)) (D.DΦ 2 x))) := by
      rw [wlp_pairF_const_smul_right, wlp_pairF_fsum_right Finset.univ
        (fun k x => crossC (EuclideanSpace.single k (1 : ℂ)) (D.DΦ k x))
        (fun k _ => wlp_integrable_cross hP hΘ (hLocD k) _), Fin.sum_univ_three]
    have hLHS : pairF P (nuLapT ν Θ) D.ψ = (ν : ℂ) * pairF P (lapT Θ) D.ψ :=
      wlp_pairF_const_smul P ν (lapT Θ) D.ψ
    rw [hLHS, F1, F2, F3, hR, cross_k 0, cross_k 1, cross_k 2]
    push_cast
    ring

end UnforcedLeray.Short.PartIIIb.Concrete
