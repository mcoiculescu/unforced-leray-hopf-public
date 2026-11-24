import UnforcedLeray.Units.B0449.FixedCutoff
import UnforcedLeray.Units.B0448.Distribution
import UnforcedLeray.Lib.HeatR3B.WeakLap

/-!
# Product coordinates for the B0449 resolvent test

The B0448 operator is written on the Euclidean `WithLp` realization of space-time, while the
graph identities are written on the ordinary product `ℝ × Space`. This leaf records the exact
linear-equivalence transport between those test-function operators.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory SchwartzMap LineDeriv Set
open scoped ENNReal NNReal ContDiff SchwartzMap

namespace UnforcedLeray.B0449

open UnforcedLeray.B0448

/-- The product-to-Hilbert coordinate equivalence used by B0448. -/
def productToST : (ℝ × Space) ≃L[ℝ] ST :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ Space).symm

/-- The product-space transpose resolvent, expressed by its coordinate directional derivatives. -/
def productResolventOpT (ψ : 𝓢(ℝ × Space, ℂ)) : 𝓢(ℝ × Space, ℂ) :=
  -∂_{((1 : ℝ), (0 : Space))} ψ -
    ∑ i : Fin 3, ∂_{((0 : ℝ), EuclideanSpace.single i (1 : ℝ))}
      (∂_{((0 : ℝ), EuclideanSpace.single i (1 : ℝ))} ψ) + ψ

theorem productToST_timeDir : productToST (1, 0) = timeDir := by
  simp [productToST, timeDir]

theorem productToST_spaceDir (i : Fin 3) :
    productToST (0, EuclideanSpace.single i (1 : ℝ)) = spaceDir i := by
  simp [productToST, spaceDir]

/-- The B0448 transpose resolvent commutes with conversion to product coordinates. -/
theorem productResolventOpT_comp (ψ : 𝓢(ST, ℂ)) :
    productResolventOpT (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ productToST ψ) =
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ productToST (resolventOpT ψ) := by
  unfold productResolventOpT resolventOpT
  simp_rw [lineDerivOp_compCLMOfContinuousLinearEquiv, productToST_timeDir,
    productToST_spaceDir]
  simp only [map_add, map_neg, map_sub, map_sum]

/-- A continuous compactly supported space-time coefficient supported in a cylinder has the
indicator bound required by the graph identities. -/
theorem exists_compactCylinder_bound {E : Type*} [NormedAddCommGroup E]
    {f : ℝ × Space → E} {a b R : ℝ}
    (hcont : Continuous f) (hcompact : HasCompactSupport f)
    (hsupport : Function.support f ⊆ Icc a b ×ˢ Metric.closedBall (0 : Space) R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t z,
      ‖f (t, z)‖ ≤ M * (Icc a b).indicator (fun _ => (1 : ℝ)) t * ballInd R z := by
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuous hcont
  refine ⟨max 0 C, le_max_left _ _, ?_⟩
  intro t z
  by_cases ht : t ∈ Icc a b
  · by_cases hz : z ∈ Metric.closedBall (0 : Space) R
    · simpa [ballInd, Set.indicator_of_mem ht, Set.indicator_of_mem hz] using
        (hC (t, z)).trans (le_max_right 0 C)
    · have hzero : f (t, z) = 0 := by
        apply Function.notMem_support.mp
        intro hmem
        exact hz ((hsupport hmem).2)
      simp [ballInd, hzero, Set.indicator_of_notMem hz]
  · have hzero : f (t, z) = 0 := by
      apply Function.notMem_support.mp
      intro hmem
      exact ht ((hsupport hmem).1)
    simp [hzero, Set.indicator_of_notMem ht]

/-- Every spatial slice of a compactly supported space-time coefficient is compactly supported. -/
theorem hasCompactSupport_spaceSlice {E : Type*} [NormedAddCommGroup E] {f : ℝ × Space → E}
    (hcompact : HasCompactSupport f) (t : ℝ) :
    HasCompactSupport (fun z : Space => f (t, z)) := by
  let K : Set Space := Prod.snd '' tsupport f
  have hK : IsCompact K := by
    exact hcompact.isCompact.image continuous_snd
  refine HasCompactSupport.intro hK ?_
  intro z hz
  by_contra hne
  apply hz
  exact ⟨(t, z), subset_tsupport f (Function.mem_support.mpr hne), rfl⟩

/-- The spatial projection of the support of a compactly supported space-time coefficient is
contained in some closed ball. -/
theorem exists_spaceRadius_support {E : Type*} [NormedAddCommGroup E]
    {f : ℝ × Space → E} (hcompact : HasCompactSupport f) :
    ∃ R : ℝ, Function.support f ⊆ Set.univ ×ˢ Metric.closedBall (0 : Space) R := by
  let K : Set Space := Prod.snd '' tsupport f
  have hK : IsCompact K := hcompact.isCompact.image continuous_snd
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Space)
  refine ⟨R, ?_⟩
  intro p hp
  refine ⟨Set.mem_univ _, hR ?_⟩
  exact ⟨p, subset_tsupport f hp, rfl⟩

/-- Multiplying a compactly supported spatial test by the fixed time cutoff confines its support
to the unit chart cylinder. -/
theorem support_timeCutoff_mul_subset {φ : ℝ × Space → ℝ} {R : ℝ}
    (hφ : Function.support φ ⊆ Set.univ ×ˢ Metric.closedBall (0 : Space) R) :
    Function.support (fun p : ℝ × Space => resolventTimeCutoff p.1 * φ p) ⊆
      Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Metric.closedBall (0 : Space) R := by
  intro p hp
  have hprod : resolventTimeCutoff p.1 * φ p ≠ 0 := Function.mem_support.mp hp
  have hφne : φ p ≠ 0 := by
    intro hzero
    rw [hzero] at hprod
    exact hprod (by simp)
  have htopen : p.1 ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
    by_contra hnot
    have hχ0 := resolventTimeCutoff_zero_outside_unitStrip hnot
    rw [hχ0] at hprod
    exact hprod (by simp)
  exact ⟨⟨htopen.1.le, htopen.2.le⟩,
    (hφ (Function.mem_support.mpr hφne)).2⟩

/-- The same cylinder support statement for any time multiplier supported in the unit strip. -/
theorem support_timeMul_subset_unitCylinder {κ : ℝ → ℝ} {φ : ℝ × Space → ℝ} {R : ℝ}
    (hκzero : ∀ t, t ∉ Ioo (-(1 / 2 : ℝ)) (1 / 2) → κ t = 0)
    (hφ : Function.support φ ⊆ Set.univ ×ˢ Metric.closedBall (0 : Space) R) :
    Function.support (fun p : ℝ × Space => κ p.1 * φ p) ⊆
      Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Metric.closedBall (0 : Space) R := by
  intro p hp
  have hprod : κ p.1 * φ p ≠ 0 := Function.mem_support.mp hp
  have hφne : φ p ≠ 0 := by
    intro hzero
    rw [hzero] at hprod
    exact hprod (by simp)
  have htopen : p.1 ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
    by_contra hnot
    rw [hκzero p.1 hnot] at hprod
    exact hprod (by simp)
  exact ⟨⟨htopen.1.le, htopen.2.le⟩,
    (hφ (Function.mem_support.mpr hφne)).2⟩

theorem support_timeCutoffDeriv_mul_subset {φ : ℝ × Space → ℝ} {R : ℝ}
    (hφ : Function.support φ ⊆ Set.univ ×ˢ Metric.closedBall (0 : Space) R) :
    Function.support (fun p : ℝ × Space => resolventTimeCutoffDeriv p.1 * φ p) ⊆
      Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Metric.closedBall (0 : Space) R :=
  support_timeMul_subset_unitCylinder
    (fun t ht => resolventTimeCutoffDeriv_zero_outside_unitStrip ht) hφ

/-- The support of a sum remains in a common cylinder. -/
theorem support_add_subset_of_cylinder {f g : ℝ × Space → ℝ} {a b R : ℝ}
    (hf : Function.support f ⊆ Icc a b ×ˢ Metric.closedBall (0 : Space) R)
    (hg : Function.support g ⊆ Icc a b ×ˢ Metric.closedBall (0 : Space) R) :
    Function.support (fun p => f p + g p) ⊆
      Icc a b ×ˢ Metric.closedBall (0 : Space) R := by
  intro p hp
  by_contra hnot
  have hfzero : f p = 0 := by
    apply Function.notMem_support.mp
    intro hmem
    exact hnot (hf hmem)
  have hgzero : g p = 0 := by
    apply Function.notMem_support.mp
    intro hmem
    exact hnot (hg hmem)
  exact (Function.mem_support.mp hp) (by simp [hfzero, hgzero])

/-- The time derivative of a smooth space-time coefficient is the full Fréchet derivative in the
time coordinate direction. -/
theorem hasDerivAt_timeSlice {f : ℝ × Space → ℝ} (hf : ContDiff ℝ 1 f) (t : ℝ) (z : Space) :
    HasDerivAt (fun s : ℝ => f (s, z)) (fderiv ℝ f (t, z) (1, 0)) t := by
  have hdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hF : HasFDerivAt f (fderiv ℝ f (t, z)) (t, z) :=
    (hdiff (t, z)).hasFDerivAt
  have hline := hF.comp t (hasFDerivAt_prodMk_left (𝕜 := ℝ) t z)
  simpa [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply] using hline.hasDerivAt

/-- Spatial Fréchet derivatives of a smooth product coefficient are the full derivatives in
the spatial inclusion directions. -/
theorem hasFDerivAt_spaceSlice {f : ℝ × Space → ℝ} (hf : ContDiff ℝ 1 f)
    (t : ℝ) (z : Space) :
    HasFDerivAt (fun y : Space => f (t, y))
      ((fderiv ℝ f (t, z)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) z := by
  have hdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hF : HasFDerivAt f (fderiv ℝ f (t, z)) (t, z) :=
    (hdiff (t, z)).hasFDerivAt
  exact hF.comp z (hasFDerivAt_prodMk_right (𝕜 := ℝ) t z)

/-- A temporal scalar is constant on each spatial slice, so it commutes with the spatial
Laplacian used in the graph identity. -/
theorem laplacian_timeScalar_mul {c : ℝ} {ψ : Space → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (z : Space) :
    UnforcedLeray.Heat.laplacian (fun y => c * ψ y) z =
      c * UnforcedLeray.Heat.laplacian ψ z := by
  rw [UnforcedLeray.Heat.laplacian_mul contDiff_const hψ]
  simp [UnforcedLeray.PhaseSpace.sd, UnforcedLeray.Heat.laplacian]

/-- The full product-space spatial Laplacian agrees with the Laplacian of each spatial slice. -/
def productSpatialLaplacian (f : ℝ × Space → ℝ) (p : ℝ × Space) : ℝ :=
  ∑ i : Fin 3, fderiv ℝ (fun x => fderiv ℝ f x (0, coordinateVector i)) p
    (0, coordinateVector i)

theorem productSpatialLaplacian_eq {f : ℝ × Space → ℝ}
    (hf : ContDiff ℝ ∞ f) (t : ℝ) (z : Space) :
    productSpatialLaplacian f (t, z) =
      UnforcedLeray.Heat.laplacian (fun y => f (t, y)) z := by
  simp only [productSpatialLaplacian, UnforcedLeray.Heat.laplacian_eq_sum_sd]
  refine Finset.sum_congr rfl ?_
  intro i hi
  let g : ℝ × Space → ℝ := fun x => fderiv ℝ f x (0, coordinateVector i)
  have hg : ContDiff ℝ ∞ g := by
    dsimp [g]
    exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hfirst : (fun y => fderiv ℝ f (t, y) (0, coordinateVector i)) =
      (fun y => fderiv ℝ (fun y => f (t, y)) y (coordinateVector i)) := by
    funext y
    have hF := (hasFDerivAt_spaceSlice (hf.of_le (by norm_num)) t y).fderiv
    have hpoint' := congrArg (fun L : Space →L[ℝ] ℝ => L (coordinateVector i)) hF.symm
    simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] using hpoint'
  have hslice := hasFDerivAt_spaceSlice (hg.of_le (by norm_num)) t z
  have hderiv := hslice.fderiv
  have hpoint := congrArg (fun L : Space →L[ℝ] ℝ => L (coordinateVector i)) hderiv
  change fderiv ℝ (fun x => fderiv ℝ f x (0, coordinateVector i)) (t, z)
      (0, coordinateVector i) =
    fderiv ℝ (fun y => fderiv ℝ (fun y => f (t, y)) y (coordinateVector i)) z
      (coordinateVector i)
  rw [← hfirst]
  simpa [g, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] using hpoint.symm

/-- The integration-by-parts algebra which turns the two cutoff graph identities into the
space-time resolvent identity. The two graph equalities are exactly the outputs of
`chartJ_cutoff_graph_identities`; the listed integrability facts are supplied by its compact
cylinder bounds. -/
theorem cutoff_graph_pairing_to_resolvent
    {U B A : ℝ × Space → ℂ} {χ χt : ℝ → ℝ}
    {φ φt lapφ : ℝ × Space → ℝ}
    (hT : ∫ p, (((χt p.1 * φ p + χ p.1 * φt p : ℝ) : ℂ) * U p) =
      -∫ p, ((χ p.1 * φ p : ℝ) : ℂ) * B p)
    (hS : ∫ p, ((χ p.1 * lapφ p : ℝ) : ℂ) * U p =
      ∫ p, (Real.exp (-p.1) : ℂ) * ((χ p.1 * φ p : ℝ) : ℂ) * A p)
    (hχφU : Integrable (fun p => ((χ p.1 * φ p : ℝ) : ℂ) * U p))
    (hχtφU : Integrable (fun p => ((χt p.1 * φ p : ℝ) : ℂ) * U p))
    (hχφtU : Integrable (fun p => ((χ p.1 * φt p : ℝ) : ℂ) * U p))
    (_hχφB : Integrable (fun p => ((χ p.1 * φ p : ℝ) : ℂ) * B p))
    (hχlapU : Integrable (fun p => ((χ p.1 * lapφ p : ℝ) : ℂ) * U p))
    (_hχφA : Integrable (fun p => (Real.exp (-p.1) : ℂ) *
      ((χ p.1 * φ p : ℝ) : ℂ) * A p)) :
    ∫ p, (((-χ p.1 * φt p - χ p.1 * lapφ p + χ p.1 * φ p : ℝ) : ℂ) * U p) =
      (∫ p, ((χt p.1 * φ p : ℝ) : ℂ) * U p) +
        (∫ p, ((χ p.1 * φ p : ℝ) : ℂ) * B p) -
        (∫ p, (Real.exp (-p.1) : ℂ) * ((χ p.1 * φ p : ℝ) : ℂ) * A p) +
        (∫ p, ((χ p.1 * φ p : ℝ) : ℂ) * U p) := by
  let t1 : ℝ × Space → ℂ := fun p => ((χt p.1 * φ p : ℝ) : ℂ) * U p
  let t2 : ℝ × Space → ℂ := fun p => ((χ p.1 * φt p : ℝ) : ℂ) * U p
  let b1 : ℝ × Space → ℂ := fun p => ((χ p.1 * φ p : ℝ) : ℂ) * B p
  let l1 : ℝ × Space → ℂ := fun p => ((χ p.1 * lapφ p : ℝ) : ℂ) * U p
  let a1 : ℝ × Space → ℂ := fun p =>
    (Real.exp (-p.1) : ℂ) * ((χ p.1 * φ p : ℝ) : ℂ) * A p
  let u1 : ℝ × Space → ℂ := fun p => ((χ p.1 * φ p : ℝ) : ℂ) * U p
  let T1 : ℂ := ∫ p, t1 p
  let T2 : ℂ := ∫ p, t2 p
  let B1 : ℂ := ∫ p, b1 p
  let L1 : ℂ := ∫ p, l1 p
  let A1 : ℂ := ∫ p, a1 p
  let U1 : ℂ := ∫ p, u1 p
  have hT' : ∫ p, t1 p + t2 p = -∫ p, b1 p := by
    calc
      _ = ∫ p, (((χt p.1 * φ p + χ p.1 * φt p : ℝ) : ℂ) * U p) := by
        congr 1
        funext p
        dsimp [t1, t2]
        push_cast
        ring
      _ = -∫ p, b1 p := by simpa [b1] using hT
  have hT'' : T1 + T2 = -B1 := by
    dsimp [T1, T2, B1]
    rw [← integral_add hχtφU hχφtU]
    exact hT'
  have htime : -T2 = T1 + B1 := by
    calc
      _ = -(T1 + T2) + T1 := by abel
      _ = -(-B1) + T1 := by rw [hT'']
      _ = _ := by abel
  have hspace : L1 = A1 := by simpa [L1, A1, l1, a1] using hS
  have hL : ∫ p, (-t2 p - l1 p + u1 p) = -T2 - L1 + U1 := by
    have hneg : Integrable (fun p => -t2 p) := by simpa [t2] using hχφtU.neg
    have hsub : Integrable (fun p => -t2 p - l1 p) := hneg.sub (by simpa [l1] using hχlapU)
    calc
      _ = (∫ p, -t2 p - l1 p) + ∫ p, u1 p :=
        integral_add hsub (by simpa [u1] using hχφU)
      _ = -T2 - L1 + U1 := by
        rw [integral_sub hneg (by simpa [l1] using hχlapU), integral_neg]
  calc
    ∫ p, (((-χ p.1 * φt p - χ p.1 * lapφ p + χ p.1 * φ p : ℝ) : ℂ) * U p)
        = ∫ p, (-(((χ p.1 * φt p : ℝ) : ℂ) * U p) -
          ((χ p.1 * lapφ p : ℝ) : ℂ) * U p +
          ((χ p.1 * φ p : ℝ) : ℂ) * U p) := by
            congr 1
            funext p
            push_cast
            ring
    _ = -T2 - L1 + U1 := hL
    _ = T1 + B1 - A1 + U1 := by rw [htime, hspace]
    _ = _ := by simp [T1, B1, A1, U1, t1, b1, a1, u1, Complex.ofReal_mul]

/-- Recombine the four source terms as the test pairing with the cutoff resolvent right hand side.
This is the final scalar integral step after `cutoff_graph_pairing_to_resolvent`. -/
theorem cutoff_resolvent_rhs_pairing
    {U B A : ℝ × Space → ℂ} {χ χt : ℝ → ℝ} {φ : ℝ × Space → ℝ}
    (hχtφU : Integrable (fun p => ((χt p.1 * φ p : ℝ) : ℂ) * U p))
    (hχφB : Integrable (fun p => ((χ p.1 * φ p : ℝ) : ℂ) * B p))
    (hχφA : Integrable (fun p => (Real.exp (-p.1) : ℂ) *
      ((χ p.1 * φ p : ℝ) : ℂ) * A p))
    (hχφU : Integrable (fun p => ((χ p.1 * φ p : ℝ) : ℂ) * U p)) :
    (∫ p, ((χt p.1 * φ p : ℝ) : ℂ) * U p) +
      (∫ p, ((χ p.1 * φ p : ℝ) : ℂ) * B p) -
      (∫ p, (Real.exp (-p.1) : ℂ) * ((χ p.1 * φ p : ℝ) : ℂ) * A p) +
      (∫ p, ((χ p.1 * φ p : ℝ) : ℂ) * U p) =
    ∫ p, (φ p : ℂ) * ((χt p.1 : ℂ) * U p + (χ p.1 : ℂ) * B p -
      (χ p.1 : ℂ) * (Real.exp (-p.1) : ℂ) * A p + (χ p.1 : ℂ) * U p) := by
  let t1 : ℝ × Space → ℂ := fun p => ((χt p.1 * φ p : ℝ) : ℂ) * U p
  let b1 : ℝ × Space → ℂ := fun p => ((χ p.1 * φ p : ℝ) : ℂ) * B p
  let a1 : ℝ × Space → ℂ := fun p =>
    (Real.exp (-p.1) : ℂ) * ((χ p.1 * φ p : ℝ) : ℂ) * A p
  let u1 : ℝ × Space → ℂ := fun p => ((χ p.1 * φ p : ℝ) : ℂ) * U p
  have ht1 : Integrable t1 := by change Integrable (fun p => ((χt p.1 * φ p : ℝ) : ℂ) * U p); exact hχtφU
  have hb1 : Integrable b1 := by change Integrable (fun p => ((χ p.1 * φ p : ℝ) : ℂ) * B p); exact hχφB
  have ha1 : Integrable a1 := by change Integrable (fun p => (Real.exp (-p.1) : ℂ) *
    ((χ p.1 * φ p : ℝ) : ℂ) * A p); exact hχφA
  have hu1 : Integrable u1 := by change Integrable (fun p => ((χ p.1 * φ p : ℝ) : ℂ) * U p); exact hχφU
  have hAddTB := integral_add ht1 hb1
  have hSubA := integral_sub (ht1.add hb1) ha1
  have hbase : Integrable (fun p => t1 p + b1 p) := ht1.add hb1
  have hbaseA : Integrable (fun p => t1 p + b1 p - a1 p) := hbase.sub ha1
  have hAddU := integral_add hbaseA hu1
  change (∫ p, t1 p) + (∫ p, b1 p) - (∫ p, a1 p) + (∫ p, u1 p) = _
  calc
    _ = ∫ p, t1 p + b1 p - a1 p + u1 p := by
      calc
        _ = ((∫ p, t1 p + b1 p) - (∫ p, a1 p)) + (∫ p, u1 p) := by
          rw [← hAddTB]
        _ = (∫ p, t1 p + b1 p - a1 p) + (∫ p, u1 p) := by
          exact congrArg (fun x : ℂ => x + ∫ p, u1 p) hSubA.symm
        _ = ∫ p, t1 p + b1 p - a1 p + u1 p := hAddU.symm
    _ = ∫ p, (φ p : ℂ) * ((χt p.1 : ℂ) * U p + (χ p.1 : ℂ) * B p -
        (χ p.1 : ℂ) * (Real.exp (-p.1) : ℂ) * A p + (χ p.1 : ℂ) * U p) := by
      congr 1
      funext p
      dsimp [t1, b1, a1, u1]
      push_cast
      ring

end UnforcedLeray.B0449
