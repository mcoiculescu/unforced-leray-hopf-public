import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellAdvTRep
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellQuadraticPointwise
import UnforcedLeray.Cons.C03Background.Pieces

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint
open UnforcedLeray.PhaseSpace
open UnforcedLeray.B0412

private theorem realC_eq_cplxV_quadraticGuard : realC = UnforcedLeray.Axi.cplxV := by
  funext x
  ext i
  simp [realC_apply, UnforcedLeray.Axi.cplxV_apply]

private theorem norm_realC_quadraticGuard (x : Space) : ‖realC x‖ = ‖x‖ := by
  rw [realC_eq_cplxV_quadraticGuard, UnforcedLeray.Axi.norm_cplxV]

/-- The affine inlet associated to fixed coordinates is a bounded background, directly from the
actual inlet columns. This is pre-equation regularity and does not use correction regularity. -/
theorem isBoundedBackground_affineInlet {p : Params} (hInlet : p.InletRegular)
    (α : Fin 2 → ℝ) :
    IsBoundedBackground (fun τ y => ∑ i : Fin 2, α i • p.inlet i τ y) := by
  have h0 : IsBoundedBackground (α 0 • p.inlet 0) :=
    UnforcedLeray.Cons.C03.isBoundedBackground_const_smul (hInlet 0).1 (α 0)
  have h1 : IsBoundedBackground (α 1 • p.inlet 1) :=
    UnforcedLeray.Cons.C03.isBoundedBackground_const_smul (hInlet 1).1 (α 1)
  have hsum : IsBoundedBackground ((α 0 • p.inlet 0) + (α 1 • p.inlet 1)) :=
    UnforcedLeray.Cons.C03.isBoundedBackground_add h0 h1
  convert hsum using 1 <;> funext τ y <;> simp [Fin.sum_univ_succ]

/-- At the actual selected scheme state, the compact-test quadratic convection density is
integrable on a period cell. The graph component uses only its `Yq` representative; the affine
inlet uses the explicit bounded inlet columns. In particular, no post-equation `CorrectionRegular`
field is used. -/
theorem selectedState_quadraticConvection_integrable {p : Params} (hInlet : p.InletRegular)
    {B : Budget} {z : (p.scheme B).Z} {Φ : ℝ × Space → CVec3}
    (hΦ : IsPhaseTest p.period Φ) :
    Integrable (fun x : SpaceTime =>
      dotL (advT (p.uOf z) Φ x) (p.uOf z x))
      (volume.restrict (phaseCell p.period)) := by
  let μ : Measure SpaceTime := volume.restrict (phaseCell p.period)
  let V : ℝ → SpatialField := fun τ y =>
    (p.coord z 0) • p.inlet 0 τ y + (p.coord z 1) • p.inlet 1 τ y
  let W : SpaceTime → CVec3 := fun x => rep (p.wOf z) x.1 x.2
  let VC : SpaceTime → CVec3 := fun x => realC (V x.1 x.2)
  let U : SpaceTime → CVec3 := fun x => VC x + W x
  let T : SpaceTime → CVec3 := fun x => advT U Φ x
  obtain ⟨R0, hspace0⟩ := (hΦ.dy 0).bounded_support
  obtain ⟨R1, hspace1⟩ := (hΦ.dy 1).bounded_support
  obtain ⟨R2, hspace2⟩ := (hΦ.dy 2).bounded_support
  let R : ℝ := max R0 (max R1 R2)
  let K : Set SpaceTime := Icc (0 : ℝ) p.period ×ˢ Metric.closedBall (0 : Space) R
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hKm : MeasurableSet K := hK.measurableSet
  have hKfinite : μ K ≠ ∞ := by
    have hlt : μ K < ∞ := by
      rw [Measure.restrict_apply hKm]
      exact lt_of_le_of_lt (measure_mono inter_subset_left) hK.measure_lt_top
    exact ne_of_lt hlt
  have hV : IsBoundedBackground V := by
    have h := isBoundedBackground_affineInlet hInlet (p.coord z)
    convert h using 1 <;> funext τ y <;> simp [V, Fin.sum_univ_succ]
  obtain ⟨CV, hCV⟩ := hV.bounded
  have hWmem : MemLp W q0E μ := by
    simpa [W, μ, phaseCell] using memLp_rep_periodCell q0E_ne_top (p.wOf z)
  have hVmeas : AEStronglyMeasurable VC μ := by
    have h : AEStronglyMeasurable
        (fun x : SpaceTime => realC (V x.1 x.2)) volume := by
      have hc := UnforcedLeray.Axi.cplxV.continuous.comp_aestronglyMeasurable hV.measurable
      exact hc.congr (ae_of_all _ fun x => by rw [realC_eq_cplxV_quadraticGuard])
    exact h.mono_measure Measure.restrict_le_self
  have hVCbound : ∀ᵐ x ∂μ, ‖VC x‖ ≤ CV := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod MeasurableSet.univ)] with x hx
    change ‖realC (V x.1 x.2)‖ ≤ CV
    rw [norm_realC_quadraticGuard]
    exact (hCV x.1 x.2).1
  have hVCcut : MemLp (K.indicator VC) q0E μ := by
    haveI : IsFiniteMeasure (μ.restrict K) := isFiniteMeasure_restrict.mpr hKfinite
    rw [memLp_indicator_iff_restrict hKm]
    have hVmeasK : AEStronglyMeasurable VC (μ.restrict K) :=
      hVmeas.mono_measure Measure.restrict_le_self
    have hVCboundK : ∀ᵐ x ∂(μ.restrict K), ‖VC x‖ ≤ CV := by
      filter_upwards with x
      change ‖realC (V x.1 x.2)‖ ≤ CV
      rw [norm_realC_quadraticGuard]
      exact (hCV x.1 x.2).1
    exact MemLp.of_bound hVmeasK CV hVCboundK
  have hWcut : MemLp (K.indicator W) q0E μ := hWmem.indicator hKm
  have hUcut : MemLp (K.indicator U) q0E μ := by
    have heq : K.indicator U = K.indicator VC + K.indicator W := by
      funext x
      simp [U, Set.indicator_add]
    rw [heq]
    exact hVCcut.add hWcut
  have hTV : MemLp (fun x : SpaceTime => advT VC Φ x) q0E μ := by
    change MemLp (fun x => advT (fun x => realC (V x.1 x.2)) Φ x) q0E μ
    exact memLp_advT_background_cell hΦ hV q0E_ne_top
  have hTW : MemLp (fun x : SpaceTime => advT W Φ x) q0E μ := by
    exact memLp_advT_rep_cell hΦ
  have hT : MemLp T q0E μ := by
    have heq : T = (fun x => advT VC Φ x) + (fun x => advT W Φ x) := by
      funext x
      simp only [T, U, VC, W, advT, Pi.add_apply, PiLp.add_apply,
        Finset.sum_add_distrib, add_smul]
    rw [heq]
    exact hTV.add hTW
  have hTcut : MemLp (K.indicator T) q0E μ := hT.indicator hKm
  have hTsupport : ∀ x, x ∉ K → K.indicator T x = 0 := by
    intro x hx
    simp [Set.indicator_of_notMem hx]
  have hUsupport : ∀ x, x ∉ K → K.indicator U x = 0 := by
    intro x hx
    simp [Set.indicator_of_notMem hx]
  have h2q : (2 : ℝ≥0∞) ≤ q0E := by
    change (2 : ℝ≥0∞) ≤ ENNReal.ofReal (11 / 4 : ℝ)
    norm_num [UnforcedLeray.B0281.q0]
  have hT2 : MemLp (K.indicator T) 2 μ :=
    hTcut.mono_exponent_of_measure_support_ne_top hTsupport hKfinite h2q
  have hU2 : MemLp (K.indicator U) 2 μ :=
    hUcut.mono_exponent_of_measure_support_ne_top hUsupport hKfinite h2q
  haveI : ENNReal.HolderTriple 2 2 1 := ⟨by rw [inv_one, ENNReal.inv_two_add_inv_two]⟩
  have hcutInt : Integrable
      (fun x : SpaceTime => dotL (K.indicator T x) (K.indicator U x)) μ :=
    integrable_dotL_of_memLp_holder hT2 hU2
  have hTzero : ∀ τ ∈ Ioc (0 : ℝ) p.period, ∀ y : Space, R < ‖y‖ → T (τ, y) = 0 := by
    intro τ hτ y hy
    have h0 := hspace0 τ y (lt_of_le_of_lt (le_max_left _ _) hy)
    have h1 := hspace1 τ y (lt_of_le_of_lt
      (le_trans (le_max_left R1 R2) (le_max_right R0 (max R1 R2))) hy)
    have h2 := hspace2 τ y (lt_of_le_of_lt
      (le_trans (le_max_right R1 R2) (le_max_right R0 (max R1 R2))) hy)
    change advT U Φ (τ, y) = 0
    unfold advT
    apply Finset.sum_eq_zero
    intro j hj
    fin_cases j <;> simp [U, VC, W, h0, h1, h2]
  have hae : (fun x : SpaceTime => dotL (T x) (U x)) =ᵐ[μ]
      (fun x => dotL (K.indicator T x) (K.indicator U x)) := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod MeasurableSet.univ)] with x hx
    by_cases hy : ‖x.2‖ ≤ R
    · have hxK : x ∈ K := by
        simp only [K, mem_prod, mem_Icc, Metric.mem_closedBall, dist_zero_right]
        exact ⟨⟨le_of_lt hx.1.1, hx.1.2⟩, hy⟩
      simp [Set.indicator_of_mem hxK]
    · have hfar : R < ‖x.2‖ := lt_of_not_ge hy
      have hzero := hTzero x.1 hx.1 x.2 hfar
      have hxK : x ∉ K := by
        simp only [K, mem_prod, mem_Icc, Metric.mem_closedBall, dist_zero_right]
        intro hxK
        exact hy hxK.2
      simp [Set.indicator_of_notMem hxK, hzero]
  have hInt : Integrable (fun x : SpaceTime => dotL (T x) (U x)) μ :=
    Integrable.congr hcutInt hae.symm
  have hUeq : p.uOf z = U := by
    funext x
    change p.eFun (p.coord z) x + rep (p.wOf z) x.1 x.2 = VC x + W x
    simp [VC, W, V, Params.eFun, Fin.sum_univ_succ]
  simpa [μ, T, U, hUeq] using hInt

#print axioms isBoundedBackground_affineInlet
#print axioms selectedState_quadraticConvection_integrable

/-- A compactly supported first factor and a locally `L^q₀` second factor have an integrable
pairing on a phase cell. The finite measure cutoff lowers both exponents to `L²`, after which
Hölder applies. This helper supports termwise integrability of the actual quadratic expansion. -/
theorem integrable_dotL_of_memLp_compactFirst {P R : ℝ} [Fact (0 < P)]
    {F G : SpaceTime → CVec3}
    (hF : MemLp F q0E (volume.restrict (phaseCell P)))
    (hG : MemLp ((Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) R).indicator G)
      q0E (volume.restrict (phaseCell P)))
    (hzero : ∀ τ ∈ Ioc (0 : ℝ) P, ∀ y : Space, R < ‖y‖ → F (τ, y) = 0) :
    Integrable (fun x : SpaceTime => dotL (F x) (G x))
      (volume.restrict (phaseCell P)) := by
  let μ : Measure SpaceTime := volume.restrict (phaseCell P)
  let K : Set SpaceTime := Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) R
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hKm : MeasurableSet K := hK.measurableSet
  have hKfinite : μ K ≠ ∞ := by
    have hlt : μ K < ∞ := by
      rw [Measure.restrict_apply hKm]
      exact lt_of_le_of_lt (measure_mono inter_subset_left) hK.measure_lt_top
    exact ne_of_lt hlt
  have hFcut : MemLp (K.indicator F) q0E μ := hF.indicator hKm
  have hFsupport : ∀ x, x ∉ K → K.indicator F x = 0 := by
    intro x hx
    simp [Set.indicator_of_notMem hx]
  have h2q : (2 : ℝ≥0∞) ≤ q0E := by
    change (2 : ℝ≥0∞) ≤ ENNReal.ofReal (11 / 4 : ℝ)
    norm_num [UnforcedLeray.B0281.q0]
  have hF2 : MemLp (K.indicator F) 2 μ :=
    hFcut.mono_exponent_of_measure_support_ne_top hFsupport hKfinite h2q
  have hG2 : MemLp (K.indicator G) 2 μ :=
    hG.mono_exponent_of_measure_support_ne_top
      (fun x hx => Set.indicator_of_notMem hx G) hKfinite h2q
  haveI : ENNReal.HolderTriple 2 2 1 := ⟨by rw [inv_one, ENNReal.inv_two_add_inv_two]⟩
  have hcut : Integrable (fun x : SpaceTime =>
      dotL (K.indicator F x) (K.indicator G x)) μ :=
    integrable_dotL_of_memLp_holder hF2 hG2
  have hae : (fun x : SpaceTime => dotL (F x) (G x)) =ᵐ[μ]
      (fun x => dotL (K.indicator F x) (K.indicator G x)) := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod MeasurableSet.univ)] with x hx
    by_cases hy : ‖x.2‖ ≤ R
    · have hxK : x ∈ K := by
        simp only [K, mem_prod, mem_Icc, Metric.mem_closedBall, dist_zero_right]
        exact ⟨⟨le_of_lt hx.1.1, hx.1.2⟩, hy⟩
      simp [Set.indicator_of_mem hxK]
    · have hfar : R < ‖x.2‖ := lt_of_not_ge hy
      have hzero' := hzero x.1 hx.1 x.2 hfar
      have hxK : x ∉ K := by
        simp only [K, mem_prod, mem_Icc, Metric.mem_closedBall, dist_zero_right]
        intro hxK
        exact hy hxK.2
      simp [Set.indicator_of_notMem hxK, hzero']
  exact Integrable.congr hcut hae.symm

#print axioms integrable_dotL_of_memLp_compactFirst

/-- Every term in the pointwise four-term expansion of the selected-state quadratic convection
is integrable on a phase cell. The graph factors use their actual `Yq` representative, while all
inlet factors are restricted to the fixed compact support of the test derivatives. -/
theorem selectedState_quadraticConvection_components_integrable {p : Params}
    (hInlet : p.InletRegular) {B : Budget} {z : (p.scheme B).Z}
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest p.period Φ) :
    Integrable (fun x : SpaceTime =>
      dotL (advT (p.eFun (p.coord z)) Φ x) (p.eFun (p.coord z) x))
        (volume.restrict (phaseCell p.period)) ∧
    Integrable (fun x : SpaceTime =>
      dotL (advT (p.eFun (p.coord z)) Φ x) (rep (p.wOf z) x.1 x.2))
        (volume.restrict (phaseCell p.period)) ∧
    Integrable (fun x : SpaceTime =>
      dotL (advT (fun x => rep (p.wOf z) x.1 x.2) Φ x) (p.eFun (p.coord z) x))
        (volume.restrict (phaseCell p.period)) ∧
    Integrable (fun x : SpaceTime =>
      dotL (advT (fun x => rep (p.wOf z) x.1 x.2) Φ x)
        (rep (p.wOf z) x.1 x.2)) (volume.restrict (phaseCell p.period)) := by
  let μ : Measure SpaceTime := volume.restrict (phaseCell p.period)
  let V : ℝ → SpatialField := fun τ y =>
    (p.coord z 0) • p.inlet 0 τ y + (p.coord z 1) • p.inlet 1 τ y
  let VC : SpaceTime → CVec3 := fun x => realC (V x.1 x.2)
  let W : SpaceTime → CVec3 := fun x => rep (p.wOf z) x.1 x.2
  let T0 : SpaceTime → CVec3 := fun x => advT VC Φ x
  let T1 : SpaceTime → CVec3 := fun x => advT W Φ x
  have hV : IsBoundedBackground V := by
    have h := isBoundedBackground_affineInlet hInlet (p.coord z)
    convert h using 1 <;> funext τ y <;> simp [V, Fin.sum_univ_succ]
  obtain ⟨CV, hCV⟩ := hV.bounded
  have hVmeas : AEStronglyMeasurable VC μ := by
    have h : AEStronglyMeasurable
        (fun x : SpaceTime => realC (V x.1 x.2)) volume := by
      have hc := UnforcedLeray.Axi.cplxV.continuous.comp_aestronglyMeasurable hV.measurable
      exact hc.congr (ae_of_all _ fun x => by rw [realC_eq_cplxV_quadraticGuard])
    exact h.mono_measure Measure.restrict_le_self
  have hVCbound : ∀ᵐ x ∂μ, ‖VC x‖ ≤ CV := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod MeasurableSet.univ)] with x hx
    change ‖realC (V x.1 x.2)‖ ≤ CV
    rw [norm_realC_quadraticGuard]
    exact (hCV x.1 x.2).1
  obtain ⟨R0, hspace0⟩ := (hΦ.dy 0).bounded_support
  obtain ⟨R1, hspace1⟩ := (hΦ.dy 1).bounded_support
  obtain ⟨R2, hspace2⟩ := (hΦ.dy 2).bounded_support
  let R : ℝ := max R0 (max R1 R2)
  let K : Set SpaceTime := Icc (0 : ℝ) p.period ×ˢ Metric.closedBall (0 : Space) R
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hKm : MeasurableSet K := hK.measurableSet
  have hKfinite : μ K ≠ ∞ := by
    have hlt : μ K < ∞ := by
      rw [Measure.restrict_apply hKm]
      exact lt_of_le_of_lt (measure_mono inter_subset_left) hK.measure_lt_top
    exact ne_of_lt hlt
  have hVCcut : MemLp (K.indicator VC) q0E μ := by
    haveI : IsFiniteMeasure (μ.restrict K) := isFiniteMeasure_restrict.mpr hKfinite
    rw [memLp_indicator_iff_restrict hKm]
    have hVmeasK : AEStronglyMeasurable VC (μ.restrict K) :=
      hVmeas.mono_measure Measure.restrict_le_self
    have hVCboundK : ∀ᵐ x ∂(μ.restrict K), ‖VC x‖ ≤ CV := by
      filter_upwards with x
      change ‖realC (V x.1 x.2)‖ ≤ CV
      rw [norm_realC_quadraticGuard]
      exact (hCV x.1 x.2).1
    exact MemLp.of_bound hVmeasK CV hVCboundK
  have hW : MemLp W q0E μ := by
    simpa [W, μ, phaseCell] using memLp_rep_periodCell q0E_ne_top (p.wOf z)
  have hWcut : MemLp (K.indicator W) q0E μ := hW.indicator hKm
  have hT0 : MemLp T0 q0E μ := by
    change MemLp (fun x => advT (fun x => realC (V x.1 x.2)) Φ x) q0E μ
    exact memLp_advT_background_cell hΦ hV q0E_ne_top
  have hT1 : MemLp T1 q0E μ := by
    exact memLp_advT_rep_cell hΦ
  have hzero (F : SpaceTime → CVec3) (hF : F = T0 ∨ F = T1) :
      ∀ τ ∈ Ioc (0 : ℝ) p.period, ∀ y : Space, R < ‖y‖ → F (τ, y) = 0 := by
    intro τ hτ y hy
    have h0 := hspace0 τ y (lt_of_le_of_lt (le_max_left R0 (max R1 R2)) hy)
    have h1 := hspace1 τ y (lt_of_le_of_lt
      (le_trans (le_max_left R1 R2) (le_max_right R0 (max R1 R2))) hy)
    have h2 := hspace2 τ y (lt_of_le_of_lt
      (le_trans (le_max_right R1 R2) (le_max_right R0 (max R1 R2))) hy)
    rcases hF with rfl | rfl
    · change advT VC Φ (τ, y) = 0
      unfold advT
      apply Finset.sum_eq_zero
      intro j hj
      fin_cases j <;> simp [h0, h1, h2]
    · change advT W Φ (τ, y) = 0
      unfold advT
      apply Finset.sum_eq_zero
      intro j hj
      fin_cases j <;> simp [h0, h1, h2]
  have hI00 : Integrable (fun x : SpaceTime => dotL (T0 x) (VC x)) μ :=
    integrable_dotL_of_memLp_compactFirst hT0 hVCcut (hzero T0 (Or.inl rfl))
  have hI01 : Integrable (fun x : SpaceTime => dotL (T0 x) (W x)) μ :=
    integrable_dotL_of_memLp_compactFirst hT0 hWcut (hzero T0 (Or.inl rfl))
  have hI10 : Integrable (fun x : SpaceTime => dotL (T1 x) (VC x)) μ :=
    integrable_dotL_of_memLp_compactFirst hT1 hVCcut (hzero T1 (Or.inr rfl))
  have hI11 : Integrable (fun x : SpaceTime => dotL (T1 x) (W x)) μ :=
    integrable_dotL_of_memLp_compactFirst hT1 hWcut (hzero T1 (Or.inr rfl))
  have he : p.eFun (p.coord z) = VC := by
    funext x
    simp [VC, V, Params.eFun, Fin.sum_univ_succ]
  exact ⟨by simpa [μ, T0, he] using hI00,
    by simpa [μ, T0, W, he] using hI01,
    by simpa [μ, T1, VC, W, he] using hI10,
    by simpa [μ, T1, W] using hI11⟩

#print axioms selectedState_quadraticConvection_components_integrable

/-- The normalized phase-cell pairing of the actual selected-state quadratic convection splits
into its four inlet/graph terms. Every integral is justified by the preceding concrete local-Lp
proofs, rather than by a post-equation smoothness field. -/
theorem selectedState_quadraticConvection_pairF_expand {p : Params}
    (hInlet : p.InletRegular) {B : Budget} {z : (p.scheme B).Z}
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest p.period Φ) :
    pairF p.period (advT (p.uOf z) Φ) (p.uOf z) =
      pairF p.period (advT (p.eFun (p.coord z)) Φ) (p.eFun (p.coord z)) +
      pairF p.period (advT (p.eFun (p.coord z)) Φ)
        (fun x => rep (p.wOf z) x.1 x.2) +
      pairF p.period (advT (fun x => rep (p.wOf z) x.1 x.2) Φ)
        (p.eFun (p.coord z)) +
      pairF p.period (advT (fun x => rep (p.wOf z) x.1 x.2) Φ)
        (fun x => rep (p.wOf z) x.1 x.2) := by
  have htotal := selectedState_quadraticConvection_integrable
    hInlet (B := B) (z := z) hΦ
  obtain ⟨h00, h01, h10, h11⟩ :=
    selectedState_quadraticConvection_components_integrable
      hInlet (B := B) (z := z) hΦ
  let F00 : SpaceTime → ℂ := fun x =>
    dotL (advT (p.eFun (p.coord z)) Φ x) (p.eFun (p.coord z) x)
  let F01 : SpaceTime → ℂ := fun x =>
    dotL (advT (p.eFun (p.coord z)) Φ x) (rep (p.wOf z) x.1 x.2)
  let F10 : SpaceTime → ℂ := fun x =>
    dotL (advT (fun x => rep (p.wOf z) x.1 x.2) Φ x) (p.eFun (p.coord z) x)
  let F11 : SpaceTime → ℂ := fun x =>
    dotL (advT (fun x => rep (p.wOf z) x.1 x.2) Φ x)
      (rep (p.wOf z) x.1 x.2)
  have hpoint (x : SpaceTime) :
      dotL (advT (p.uOf z) Φ x) (p.uOf z x) = F00 x + F01 x + F10 x + F11 x := by
    simpa [F00, F01, F10, F11] using
      selectedState_quadraticConvection_pointwise (p := p) (B := B) (z := z) (Φ := Φ) x
  change Integrable F00 (volume.restrict (phaseCell p.period)) at h00
  change Integrable F01 (volume.restrict (phaseCell p.period)) at h01
  change Integrable F10 (volume.restrict (phaseCell p.period)) at h10
  change Integrable F11 (volume.restrict (phaseCell p.period)) at h11
  have hIntSum :
      ∫ x : SpaceTime,
        dotL (advT (p.uOf z) Φ x) (p.uOf z x) ∂(volume.restrict (phaseCell p.period)) =
      (∫ x : SpaceTime, F00 x ∂(volume.restrict (phaseCell p.period))) +
      (∫ x : SpaceTime, F01 x ∂(volume.restrict (phaseCell p.period))) +
      (∫ x : SpaceTime, F10 x ∂(volume.restrict (phaseCell p.period))) +
      ∫ x : SpaceTime, F11 x ∂(volume.restrict (phaseCell p.period)) := by
    calc
      _ = ∫ x : SpaceTime, F00 x + (F01 x + (F10 x + F11 x))
          ∂(volume.restrict (phaseCell p.period)) := by
            apply integral_congr_ae
            filter_upwards [ae_of_all _ hpoint] with x hx
            simpa only [add_assoc] using hx
      _ = _ := by
        change ∫ x : SpaceTime, (F00 + (F01 + (F10 + F11))) x
          ∂(volume.restrict (phaseCell p.period)) = _
        rw [integral_add' h00 (h01.add (h10.add h11)),
          integral_add' h01 (h10.add h11), integral_add' h10 h11]
        ring
  rw [pairF_eq_restrictedProductIntegral htotal,
      pairF_eq_restrictedProductIntegral h00,
      pairF_eq_restrictedProductIntegral h01,
      pairF_eq_restrictedProductIntegral h10,
      pairF_eq_restrictedProductIntegral h11]
  rw [← smul_add, ← smul_add, ← smul_add]
  exact congrArg (fun a : ℂ => p.period⁻¹ • a) hIntSum

#print axioms selectedState_quadraticConvection_pairF_expand

/-- The actual selected quadratic source supplied by `QuadraticBound` is represented on
solenoidal compact tests by the four integrable inlet/graph terms. -/
theorem selectedState_quadRelation_pairF_expand {p : Params} {B : Budget}
    (hQuad : p.QuadraticBound B) (hInlet : p.InletRegular)
    {z : (p.scheme B).Z} {Φ : ℝ × Space → CVec3}
    (hΦ : IsSolTest p.period Φ) :
    phasePair p.period q0E Φ (p.quad (B.poly p.ν) z z) = -(
      pairF p.period (advT (p.eFun (p.coord z)) Φ) (p.eFun (p.coord z)) +
      pairF p.period (advT (p.eFun (p.coord z)) Φ)
        (fun x => rep (p.wOf z) x.1 x.2) +
      pairF p.period (advT (fun x => rep (p.wOf z) x.1 x.2) Φ)
        (p.eFun (p.coord z)) +
      pairF p.period (advT (fun x => rep (p.wOf z) x.1 x.2) Φ)
        (fun x => rep (p.wOf z) x.1 x.2)) := by
  have hspec := (p.quad_spec hQuad).1 z z
  rw [hspec Φ hΦ]
  rw [selectedState_quadraticConvection_pairF_expand hInlet hΦ.1]

#print axioms selectedState_quadRelation_pairF_expand

end UnforcedLeray.Cons.C03.Concrete
