import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellQuadraticGuard
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellAdvTRep

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint
open UnforcedLeray.PhaseSpace
open UnforcedLeray.B0412

private theorem realC_eq_cplxV_fullConvection : realC = UnforcedLeray.Axi.cplxV := by
  funext x
  ext i
  simp [realC_apply, UnforcedLeray.Axi.cplxV_apply]

private theorem norm_realC_fullConvection (x : Space) : ‖realC x‖ = ‖x‖ := by
  rw [realC_eq_cplxV_fullConvection, UnforcedLeray.Axi.norm_cplxV]

def selectedFullConvectionTerm (p : Params) (z : p.Z) :
    Fin 3 → SpaceTime → CVec3
  | 0 => p.Ufun
  | 1 => p.eFun (p.coord z)
  | 2 => fun x => rep (p.wOf z) x.1 x.2

/-- A bounded background restricted to the compact support cylinder of a phase test is in every
finite `L^p` on the phase cell. -/
theorem memLp_boundedBackground_cut_cell {P R : ℝ} [Fact (0 < P)]
    {V : ℝ → SpatialField} (hV : IsBoundedBackground V) :
    MemLp ((Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) R).indicator
      (fun x : SpaceTime => realC (V x.1 x.2))) q0E
      (volume.restrict (phaseCell P)) := by
  let μ : Measure SpaceTime := volume.restrict (phaseCell P)
  let K : Set SpaceTime := Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) R
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hKm : MeasurableSet K := hK.measurableSet
  have hKfinite : μ K < ∞ := by
    rw [Measure.restrict_apply hKm]
    exact lt_of_le_of_lt (measure_mono inter_subset_left) hK.measure_lt_top
  haveI : IsFiniteMeasure (μ.restrict K) := ⟨by simpa using hKfinite⟩
  have hVmeas : AEStronglyMeasurable
      (fun x : SpaceTime => realC (V x.1 x.2)) (μ.restrict K) := by
    have h : AEStronglyMeasurable
        (fun x : SpaceTime => realC (V x.1 x.2)) volume := by
      have hc := UnforcedLeray.Axi.cplxV.continuous.comp_aestronglyMeasurable hV.measurable
      exact hc.congr (ae_of_all _ fun x => by rw [realC_eq_cplxV_fullConvection])
    exact h.mono_measure (Measure.restrict_le_self.trans Measure.restrict_le_self)
  obtain ⟨C, hC⟩ := hV.bounded
  have hbound : ∀ᵐ x ∂(μ.restrict K),
      ‖realC (V x.1 x.2)‖ ≤ C := by
    filter_upwards with x
    rw [norm_realC_fullConvection]
    exact (hC x.1 x.2).1
  rw [memLp_indicator_iff_restrict hKm]
  simpa [μ] using (MemLp.of_bound hVmeas C hbound :
    MemLp (fun x : SpaceTime => realC (V x.1 x.2)) q0E (μ.restrict K))

/-- All nine bilinear terms in the compact-test convection of the full actual background
`U_raw + E_bgα + w` are integrable on one phase cell. The raw and inlet factors are localized by
the test derivative support; the graph factor uses the actual selected joint representative in
`Yq`. This is an integrability statement for the affine scheme field and does not identify it
pointwise with the selected physical `scheme.field` representative. -/
theorem selectedFullBackground_quadraticTerms_integrable {p : Params}
    (hRaw : p.RawLiftRegular) (hInlet : p.InletRegular)
    {B : Budget} {z : (p.scheme B).Z} {Φ : ℝ × Space → CVec3}
    (hΦ : IsPhaseTest p.period Φ) :
    ∀ i j : Fin 3,
      Integrable (fun x : SpaceTime =>
        dotL (advT (selectedFullConvectionTerm p z i) Φ x) (selectedFullConvectionTerm p z j x))
        (volume.restrict (phaseCell p.period)) := by
  let μ : Measure SpaceTime := volume.restrict (phaseCell p.period)
  let V : ℝ → SpatialField := fun τ y =>
    ∑ i : Fin 2, (p.coord z i) • p.inlet i τ y
  have hV : IsBoundedBackground V := isBoundedBackground_affineInlet hInlet (p.coord z)
  let T : Fin 3 → SpaceTime → CVec3 := fun i x =>
    advT (selectedFullConvectionTerm p z i) Φ x
  let W : SpaceTime → CVec3 := fun x => rep (p.wOf z) x.1 x.2
  have hT (i : Fin 3) : MemLp (T i) q0E μ := by
    fin_cases i
    · change MemLp (fun x => advT p.Ufun Φ x) q0E μ
      exact memLp_advT_background_cell hΦ hRaw.1 q0E_ne_top
    · change MemLp (fun x => advT
        (fun x => realC (V x.1 x.2)) Φ x) q0E μ
      exact memLp_advT_background_cell hΦ hV q0E_ne_top
    · change MemLp (fun x => advT W Φ x) q0E μ
      exact memLp_advT_rep_cell hΦ
  obtain ⟨R0, hspace0⟩ := (hΦ.dy 0).bounded_support
  obtain ⟨R1, hspace1⟩ := (hΦ.dy 1).bounded_support
  obtain ⟨R2, hspace2⟩ := (hΦ.dy 2).bounded_support
  let R : ℝ := max R0 (max R1 R2)
  let K : Set SpaceTime := Icc (0 : ℝ) p.period ×ˢ Metric.closedBall (0 : Space) R
  have hKm : MeasurableSet K := (isCompact_Icc.prod (isCompact_closedBall _ _)).measurableSet
  have hGcut (j : Fin 3) : MemLp (K.indicator (selectedFullConvectionTerm p z j)) q0E μ := by
    fin_cases j
    · change MemLp (K.indicator (fun x => p.Ufun x)) q0E μ
      change MemLp (K.indicator
        (fun x : SpaceTime => realC (p.raw x.1 x.2))) q0E μ
      exact memLp_boundedBackground_cut_cell hRaw.1
    · change MemLp (K.indicator
        (fun x : SpaceTime => realC (V x.1 x.2))) q0E μ
      exact memLp_boundedBackground_cut_cell hV
    · change MemLp (K.indicator W) q0E μ
      have hW : MemLp W q0E μ := by
        simpa [W, μ, phaseCell] using memLp_rep_periodCell q0E_ne_top (p.wOf z)
      exact hW.indicator hKm
  have hzero (i : Fin 3) :
      ∀ τ ∈ Ioc (0 : ℝ) p.period, ∀ y : Space, R < ‖y‖ → T i (τ, y) = 0 := by
    intro τ hτ y hy
    have h0 := hspace0 τ y (lt_of_le_of_lt (le_max_left R0 (max R1 R2)) hy)
    have h1 := hspace1 τ y (lt_of_le_of_lt
      (le_trans (le_max_left R1 R2) (le_max_right R0 (max R1 R2))) hy)
    have h2 := hspace2 τ y (lt_of_le_of_lt
      (le_trans (le_max_right R1 R2) (le_max_right R0 (max R1 R2))) hy)
    fin_cases i
    · change advT p.Ufun Φ (τ, y) = 0
      unfold advT
      apply Finset.sum_eq_zero
      intro j hj
      fin_cases j <;> simp [h0, h1, h2]
    · change advT (p.eFun (p.coord z)) Φ (τ, y) = 0
      unfold advT
      apply Finset.sum_eq_zero
      intro j hj
      fin_cases j <;> simp [h0, h1, h2]
    · change advT W Φ (τ, y) = 0
      unfold advT
      apply Finset.sum_eq_zero
      intro j hj
      fin_cases j <;> simp [h0, h1, h2]
  intro i j
  exact integrable_dotL_of_memLp_compactFirst (hT i) (hGcut j) (hzero i)

#print axioms memLp_boundedBackground_cut_cell
#print axioms selectedFullBackground_quadraticTerms_integrable

/-- The full raw-plus-inlet-plus-graph convection pairing has its exact normalized nine-term
expansion on a compact phase test. The finite sums range over the three actual field components;
all nine summands and the total use the integrability theorem above. -/
theorem selectedFullBackground_pairF_quadratic_expand {p : Params}
    (hRaw : p.RawLiftRegular) (hInlet : p.InletRegular)
    {B : Budget} {z : (p.scheme B).Z} {Φ : ℝ × Space → CVec3}
    (hΦ : IsPhaseTest p.period Φ) :
    pairF p.period
      (advT (fun x => ∑ i : Fin 3, selectedFullConvectionTerm p z i x) Φ)
      (fun x => ∑ j : Fin 3, selectedFullConvectionTerm p z j x) =
    ∑ i : Fin 3, ∑ j : Fin 3,
      pairF p.period (advT (selectedFullConvectionTerm p z i) Φ)
        (selectedFullConvectionTerm p z j) := by
  let μ : Measure SpaceTime := volume.restrict (phaseCell p.period)
  let D : Fin 3 → Fin 3 → SpaceTime → ℂ := fun i j x =>
    dotL (advT (selectedFullConvectionTerm p z i) Φ x)
      (selectedFullConvectionTerm p z j x)
  have hD (i j : Fin 3) : Integrable (D i j) μ := by
    simpa [D] using selectedFullBackground_quadraticTerms_integrable hRaw hInlet hΦ i j
  have hInner (i : Fin 3) : Integrable (fun x : SpaceTime => ∑ j : Fin 3, D i j x) μ := by
    apply integrable_finsetSum Finset.univ
    intro j hj
    exact hD i j
  have hSum : Integrable
      (fun x : SpaceTime => ∑ i : Fin 3, ∑ j : Fin 3, D i j x) μ := by
    apply integrable_finsetSum Finset.univ
    intro i hi
    exact hInner i
  have htotalPoint (x : SpaceTime) :
      dotL
        (advT (fun y => ∑ i : Fin 3, selectedFullConvectionTerm p z i y) Φ x)
        (∑ j : Fin 3, selectedFullConvectionTerm p z j x) =
      ∑ i : Fin 3, ∑ j : Fin 3, D i j x := by
    let A : Fin 3 → CVec3 := fun i => advT (selectedFullConvectionTerm p z i) Φ x
    let C : Fin 3 → CVec3 := fun j => selectedFullConvectionTerm p z j x
    have hAdv : advT (fun y => ∑ i : Fin 3, selectedFullConvectionTerm p z i y) Φ x =
        ∑ i : Fin 3, A i := by
      change (∑ k : Fin 3, (∑ i : Fin 3, selectedFullConvectionTerm p z i x k) • dy k Φ x) =
        ∑ i : Fin 3, ∑ k : Fin 3,
          selectedFullConvectionTerm p z i x k • dy k Φ x
      calc
        (∑ k : Fin 3, (∑ i : Fin 3, selectedFullConvectionTerm p z i x k) • dy k Φ x) =
            ∑ k : Fin 3, ∑ i : Fin 3,
              selectedFullConvectionTerm p z i x k • dy k Φ x := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.sum_smul]
        _ = ∑ i : Fin 3, ∑ k : Fin 3,
              selectedFullConvectionTerm p z i x k • dy k Φ x := by
          rw [Finset.sum_comm]
        _ = ∑ i : Fin 3, A i := rfl
    rw [hAdv]
    change dotL (∑ i : Fin 3, A i) (∑ j : Fin 3, C j) =
      ∑ i : Fin 3, ∑ j : Fin 3, dotL (A i) (C j)
    have hfirst : dotL (∑ i : Fin 3, A i) = ∑ i : Fin 3, dotL (A i) := by
      rw [map_sum]
    calc
      dotL (∑ i : Fin 3, A i) (∑ j : Fin 3, C j) =
          (∑ i : Fin 3, dotL (A i)) (∑ j : Fin 3, C j) := by rw [hfirst]
      _ = ∑ i : Fin 3, dotL (A i) (∑ j : Fin 3, C j) := by
        rw [ContinuousLinearMap.sum_apply]
      _ = ∑ i : Fin 3, ∑ j : Fin 3, dotL (A i) (C j) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [map_sum]
  have htotal : Integrable
      (fun x : SpaceTime => dotL
        (advT (fun y => ∑ i : Fin 3, selectedFullConvectionTerm p z i y) Φ x)
        (∑ j : Fin 3, selectedFullConvectionTerm p z j x)) μ :=
    Integrable.congr hSum (ae_of_all _ fun x => (htotalPoint x).symm)
  have hint :
      ∫ x : SpaceTime,
        dotL
          (advT (fun y => ∑ i : Fin 3, selectedFullConvectionTerm p z i y) Φ x)
          (∑ j : Fin 3, selectedFullConvectionTerm p z j x) ∂μ =
      ∑ i : Fin 3, ∑ j : Fin 3, ∫ x : SpaceTime, D i j x ∂μ := by
    calc
      _ = ∫ x : SpaceTime, ∑ i : Fin 3, ∑ j : Fin 3, D i j x ∂μ :=
        integral_congr_ae (ae_of_all _ htotalPoint)
      _ = _ := by
        rw [integral_finsetSum Finset.univ (fun i hi => hInner i)]
        apply Finset.sum_congr rfl
        intro i hi
        rw [integral_finsetSum Finset.univ (fun j hj => hD i j)]
  have hpair (i j : Fin 3) :
      pairF p.period (advT (selectedFullConvectionTerm p z i) Φ)
        (selectedFullConvectionTerm p z j) = p.period⁻¹ • ∫ x, D i j x ∂μ :=
    pairF_eq_restrictedProductIntegral (hD i j)
  have hdouble :
      (∑ i : Fin 3, ∑ j : Fin 3,
        pairF p.period (advT (selectedFullConvectionTerm p z i) Φ)
          (selectedFullConvectionTerm p z j)) =
      p.period⁻¹ • (∑ i : Fin 3, ∑ j : Fin 3, ∫ x : SpaceTime, D i j x ∂μ) := by
    simp_rw [hpair, Finset.smul_sum]
  rw [pairF_eq_restrictedProductIntegral htotal]
  rw [hint]
  exact hdouble.symm

#print axioms selectedFullBackground_pairF_quadratic_expand

/-- The finite component sum is exactly `U_raw + uOf z`; this is the pointwise affine field
identity, without identifying the graph representative with the separate continuous `scheme.field`
representative. -/
theorem selectedFullConvectionTerm_sum_eq_raw_add_state (p : Params) {B : Budget}
    (z : (p.scheme B).Z) :
    (fun x : SpaceTime => ∑ i : Fin 3, selectedFullConvectionTerm p z i x) =
      (fun x => p.Ufun x + p.uOf z x) := by
  funext x
  simp [selectedFullConvectionTerm, Params.uOf, Fin.sum_univ_succ]

/-- The exact normalized nine-term pairing expansion stated directly for `U_raw + uOf z`. -/
theorem selectedFullBackground_rawAddState_pairF_expand {p : Params}
    (hRaw : p.RawLiftRegular) (hInlet : p.InletRegular)
    {B : Budget} {z : (p.scheme B).Z} {Φ : ℝ × Space → CVec3}
    (hΦ : IsPhaseTest p.period Φ) :
    pairF p.period (advT (fun x => p.Ufun x + p.uOf z x) Φ)
      (fun x => p.Ufun x + p.uOf z x) =
    ∑ i : Fin 3, ∑ j : Fin 3,
      pairF p.period (advT (selectedFullConvectionTerm p z i) Φ)
        (selectedFullConvectionTerm p z j) := by
  rw [← selectedFullConvectionTerm_sum_eq_raw_add_state p z]
  exact selectedFullBackground_pairF_quadratic_expand hRaw hInlet hΦ

#print axioms selectedFullConvectionTerm_sum_eq_raw_add_state
#print axioms selectedFullBackground_rawAddState_pairF_expand

end UnforcedLeray.Cons.C03.Concrete
