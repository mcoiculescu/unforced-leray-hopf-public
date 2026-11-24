import UnforcedLeray.Units.B0449.GraphResolvent
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Compact real tests for the B0449 cutoff resolvent

This leaf begins the actual graph-to-resolvent bridge. It tests the fixed cutoff resolvent against
compactly supported smooth scalar tests and obtains both graph identities from the phase graph
hypotheses.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory SchwartzMap Set
open scoped ENNReal NNReal ContDiff SchwartzMap

namespace UnforcedLeray.B0449

open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace

variable {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- The time derivative in product coordinates. -/
def productTimeDerivative (f : ℝ × Space → ℝ) (p : ℝ × Space) : ℝ :=
  fderiv ℝ f p (1, 0)

theorem contDiff_productTimeDerivative {f : ℝ × Space → ℝ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (productTimeDerivative f) := by
  unfold productTimeDerivative
  exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem hasCompactSupport_productTimeDerivative {f : ℝ × Space → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (productTimeDerivative f) := by
  unfold productTimeDerivative
  exact hf.fderiv_apply ℝ (1, 0)

theorem hasCompactSupport_productSpatialLaplacian {f : ℝ × Space → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (productSpatialLaplacian f) := by
  let g : Fin 3 → ℝ × Space → ℝ := fun i p =>
    fderiv ℝ (fun x => fderiv ℝ f x (0, coordinateVector i)) p (0, coordinateVector i)
  have hg : ∀ i, HasCompactSupport (g i) := by
    intro i
    exact (hf.fderiv_apply ℝ (0, coordinateVector i)).fderiv_apply ℝ
      (0, coordinateVector i)
  have hs : ∀ s : Finset (Fin 3),
      HasCompactSupport (fun p => ∑ i ∈ s, g i p) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp; exact HasCompactSupport.zero
    | @insert i s hi ih => simp [hi]; exact (hg i).add ih
  change HasCompactSupport (fun p => ∑ i ∈ (Finset.univ : Finset (Fin 3)), g i p)
  exact hs Finset.univ

theorem contDiff_productSpatialLaplacian {f : ℝ × Space → ℝ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (productSpatialLaplacian f) := by
  unfold productSpatialLaplacian
  exact ContDiff.sum fun i _ =>
    (((hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).fderiv_right
      (m := ∞) (by simp)).clm_apply contDiff_const

/-- The cutoff graph identities imply the product-coordinate resolvent identity for every
compactly supported smooth real test. -/
theorem chartJ_cutoff_realTest_resolvent {ν : ℝ} (hν : 0 < ν)
    (hq : q ≠ ⊤) (hq1 : 1 < q) {w a b : Yq P q}
    (hTime : HasPhaseOp driftT w b) (hLap : HasPhaseOp (nuLapT ν) w a)
    (τ₀ : ℝ) (e : CVec3) {ψ : 𝓢(ℝ × Space, ℝ)}
    (hψc : HasCompactSupport (ψ : ℝ × Space → ℝ)) :
    ∫ p : ℝ × Space,
      (((-productTimeDerivative ψ p - productSpatialLaplacian ψ p + ψ p : ℝ) : ℂ) *
        ((resolventTimeCutoff p.1 : ℂ) * dotL e (chartJ w ν τ₀ p))) =
    ∫ p, (ψ p : ℂ) * ((resolventTimeCutoffDeriv p.1 : ℂ) *
        dotL e (chartJ w ν τ₀ p) +
      (resolventTimeCutoff p.1 : ℂ) * dotL e (chartJ b ν τ₀ p) -
      (resolventTimeCutoff p.1 : ℂ) * (Real.exp (-p.1) : ℂ) *
        dotL e (chartJ a ν τ₀ p) +
      (resolventTimeCutoff p.1 : ℂ) * dotL e (chartJ w ν τ₀ p)) := by
  let φ : ℝ × Space → ℝ := ψ
  let φt : ℝ × Space → ℝ := productTimeDerivative φ
  let lapφ : ℝ × Space → ℝ := productSpatialLaplacian φ
  let χ : ℝ → ℝ := resolventTimeCutoff
  let χt : ℝ → ℝ := resolventTimeCutoffDeriv
  let U : ℝ × Space → ℂ := fun p => dotL e (chartJ w ν τ₀ p)
  let B : ℝ × Space → ℂ := fun p => dotL e (chartJ b ν τ₀ p)
  let A : ℝ × Space → ℂ := fun p => dotL e (chartJ a ν τ₀ p)
  have hφsmooth : ContDiff ℝ ∞ φ := by exact ψ.smooth ⊤
  have hφc : HasCompactSupport φ := by simpa [φ] using hψc
  have hφtcont : Continuous φt :=
    (contDiff_productTimeDerivative hφsmooth).continuous
  have hlapcont : Continuous lapφ :=
    (contDiff_productSpatialLaplacian hφsmooth).continuous
  have hφtcomp : HasCompactSupport φt := by
    simpa [φt, φ] using hasCompactSupport_productTimeDerivative hψc
  have hlapcomp : HasCompactSupport lapφ := by
    simpa [lapφ, φ] using hasCompactSupport_productSpatialLaplacian hψc
  obtain ⟨Rφ, hRφ⟩ := exists_spaceRadius_support hφc
  obtain ⟨Rt, hRt⟩ := exists_spaceRadius_support hφtcomp
  obtain ⟨Rl, hRl⟩ := exists_spaceRadius_support hlapcomp
  let R : ℝ := max 0 (max Rφ (max Rt Rl))
  have hR0 : 0 ≤ R := le_max_left _ _
  have hRφ' : Function.support φ ⊆ Set.univ ×ˢ Metric.closedBall (0 : Space) R := by
    intro p hp
    have hz := (hRφ hp).2
    exact ⟨Set.mem_univ _, Metric.mem_closedBall.mpr
      (le_trans (Metric.mem_closedBall.mp hz)
        (le_trans (le_max_left Rφ _) (le_max_right 0 _)))⟩
  have hRt' : Function.support φt ⊆ Set.univ ×ˢ Metric.closedBall (0 : Space) R := by
    intro p hp
    have hz := (hRt hp).2
    exact ⟨Set.mem_univ _, Metric.mem_closedBall.mpr
      (le_trans (Metric.mem_closedBall.mp hz)
        (le_trans (le_max_left Rt Rl)
          (le_trans (le_max_right Rφ _) (le_max_right 0 _))))⟩
  have hRl' : Function.support lapφ ⊆ Set.univ ×ˢ Metric.closedBall (0 : Space) R := by
    intro p hp
    have hz := (hRl hp).2
    exact ⟨Set.mem_univ _, Metric.mem_closedBall.mpr
      (le_trans (Metric.mem_closedBall.mp hz)
        (le_trans (le_max_right Rt Rl)
          (le_trans (le_max_right Rφ _) (le_max_right 0 _))))⟩
  let θ : ℝ × Space → ℝ := fun p => χ p.1 * φ p
  let θt : ℝ × Space → ℝ := fun p => χt p.1 * φ p + χ p.1 * φt p
  let θt₁ : ℝ × Space → ℝ := fun p => χt p.1 * φ p
  let θt₂ : ℝ × Space → ℝ := fun p => χ p.1 * φt p
  let θlap : ℝ × Space → ℝ := fun p => χ p.1 * lapφ p
  let θA : ℝ × Space → ℂ := fun p => (Real.exp (-p.1) : ℂ) * (θ p : ℂ)
  have hθcont : Continuous (fun p : ℝ × Space => (θ p : ℂ)) := by
    exact Complex.continuous_ofReal.comp
      ((continuous_resolventTimeCutoff.comp continuous_fst).mul hφsmooth.continuous)
  have hθtcont : Continuous (fun p : ℝ × Space => (θt p : ℂ)) := by
    exact Complex.continuous_ofReal.comp
      (((continuous_resolventTimeCutoffDeriv.comp continuous_fst).mul hφsmooth.continuous).add
        ((continuous_resolventTimeCutoff.comp continuous_fst).mul hφtcont))
  have hθlapcont : Continuous θlap :=
    (continuous_resolventTimeCutoff.comp continuous_fst).mul hlapcont
  have hθRealCont : Continuous θ :=
    (continuous_resolventTimeCutoff.comp continuous_fst).mul hφsmooth.continuous
  have hθtRealCont : Continuous θt :=
    ((continuous_resolventTimeCutoffDeriv.comp continuous_fst).mul hφsmooth.continuous).add
      ((continuous_resolventTimeCutoff.comp continuous_fst).mul hφtcont)
  have hθAcont : Continuous θA := by
    exact (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_neg.comp continuous_fst))).mul hθcont
  have hθc : HasCompactSupport θ := by
    exact hφc.mul_left
  have hθt₁c : HasCompactSupport θt₁ := by
    exact hφc.mul_left
  have hθt₂c : HasCompactSupport θt₂ := by
    exact hφtcomp.mul_left
  have hθtc : HasCompactSupport θt := by
    change HasCompactSupport (θt₁ + θt₂)
    exact hθt₁c.add hθt₂c
  have hθlapc : HasCompactSupport θlap := by
    exact hlapcomp.mul_left
  have hθAc : HasCompactSupport θA := by
    have hθcomplex : HasCompactSupport (fun p => (θ p : ℂ)) :=
      hθc.comp_left Complex.ofReal_zero
    change HasCompactSupport ((fun p : ℝ × Space => (Real.exp (-p.1) : ℂ)) *
      (fun p => (θ p : ℂ)))
    exact hθcomplex.mul_left
  have hθsupport : Function.support θ ⊆
      Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Metric.closedBall (0 : Space) R := by
    simpa [θ, χ] using support_timeCutoff_mul_subset hRφ'
  have hθt₁support : Function.support θt₁ ⊆
      Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Metric.closedBall (0 : Space) R := by
    exact support_timeMul_subset_unitCylinder
      (fun t ht => resolventTimeCutoffDeriv_zero_outside_unitStrip ht) hRφ'
  have hθt₂support : Function.support θt₂ ⊆
      Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Metric.closedBall (0 : Space) R := by
    exact support_timeCutoff_mul_subset hRt'
  have hθtsupport : Function.support θt ⊆
      Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Metric.closedBall (0 : Space) R :=
    support_add_subset_of_cylinder hθt₁support hθt₂support
  have hθlapsupport : Function.support θlap ⊆
      Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Metric.closedBall (0 : Space) R := by
    exact support_timeCutoff_mul_subset hRl'
  have hθAsupport : Function.support θA ⊆
      Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Metric.closedBall (0 : Space) R := by
    intro p hp
    have hθne : θ p ≠ 0 := by
      intro hz
      apply (Function.mem_support.mp hp)
      simp [θA, hz]
    exact hθsupport (Function.mem_support.mpr hθne)
  obtain ⟨Mθ, hMθ, hθrealbound⟩ := exists_compactCylinder_bound
    hθRealCont hθc hθsupport
  have hθbound : ∀ t z, ‖((θ (t, z) : ℝ) : ℂ)‖ ≤
      Mθ * (Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator (fun _ => (1 : ℝ)) t * ballInd R z := by
    intro t z
    simpa only [Complex.norm_real] using hθrealbound t z
  obtain ⟨Mθt, hMθt, hθtrealbound⟩ := exists_compactCylinder_bound
    hθtRealCont hθtc hθtsupport
  have hθtbound : ∀ t z, ‖((θt (t, z) : ℝ) : ℂ)‖ ≤
      Mθt * (Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator (fun _ => (1 : ℝ)) t * ballInd R z := by
    intro t z
    simpa only [Complex.norm_real] using hθtrealbound t z
  obtain ⟨Mθt₁, hMθt₁, hθt₁bound⟩ := exists_compactCylinder_bound
    ((continuous_resolventTimeCutoffDeriv.comp continuous_fst).mul hφsmooth.continuous)
    hθt₁c hθt₁support
  obtain ⟨Mθt₂, hMθt₂, hθt₂bound⟩ := exists_compactCylinder_bound
    ((continuous_resolventTimeCutoff.comp continuous_fst).mul hφtcont)
    hθt₂c hθt₂support
  obtain ⟨ML, hML, hLbound⟩ := exists_compactCylinder_bound
    hθlapcont hθlapc hθlapsupport
  have hLboundC : ∀ t z, ‖((θlap (t, z) : ℝ) : ℂ)‖ ≤
      ML * (Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator (fun _ => (1 : ℝ)) t * ballInd R z := by
    intro t z
    simpa only [Complex.norm_real] using hLbound t z
  obtain ⟨MR, hMR, hRbound⟩ := exists_compactCylinder_bound hθAcont hθAc hθAsupport
  have hθsmooth : ∀ t, ContDiff ℝ ∞ (fun z => χ t * φ (t, z)) := by
    intro t
    exact contDiff_const.mul (hφsmooth.comp (contDiff_const.prodMk contDiff_id))
  have hθsupp : ∀ t, HasCompactSupport (fun z => χ t * φ (t, z)) := by
    intro t
    change HasCompactSupport ((fun _ : Space => χ t) * (fun z => φ (t, z)))
    exact (hasCompactSupport_spaceSlice hφc t).mul_left
  have hθderiv : ∀ t z, HasDerivAt
      (fun s : ℝ => ((χ s * φ (s, z) : ℝ) : ℂ))
      ((((χt t * φ (t, z)) + χ t * φt (t, z) : ℝ) : ℂ)) t := by
    intro t z
    have hχ : HasDerivAt χ (χt t) t := by
      simpa [χ, χt, resolventTimeCutoffDeriv, fderiv_apply_one_eq_deriv] using
        ((contDiff_resolventTimeCutoff.contDiffAt (x := t)).differentiableAt
          (by norm_num)).hasDerivAt
    have hφ : HasDerivAt (fun s : ℝ => φ (s, z)) (φt (t, z)) t := by
      simpa [φt, productTimeDerivative] using
        hasDerivAt_timeSlice (hφsmooth.of_le (by norm_num)) t z
    simpa [mul_add, add_mul] using (hχ.mul hφ).ofReal_comp
  have hglap : ∀ t z,
      UnforcedLeray.Heat.laplacian (fun y => χ t * φ (t, y)) z = χ t * lapφ (t, z) := by
    intro t z
    change UnforcedLeray.Heat.laplacian
      (fun y => χ t * (fun y => φ (t, y)) y) z = χ t * lapφ (t, z)
    rw [laplacian_timeScalar_mul (c := χ t)
      (ψ := fun y => φ (t, y)) (hψ := hφsmooth.comp (contDiff_const.prodMk contDiff_id)) z]
    change χ t * UnforcedLeray.Heat.laplacian (fun y => φ (t, y)) z =
      χ t * productSpatialLaplacian φ (t, z)
    exact congrArg (fun x : ℝ => χ t * x) (productSpatialLaplacian_eq hφsmooth t z).symm
  have hGLeq : (fun p : ℝ × Space =>
      (UnforcedLeray.Heat.laplacian (fun z => χ p.1 * φ (p.1, z)) p.2 : ℂ)) =
      (fun p => (θlap p : ℂ)) := by
    funext p
    rw [hglap p.1 p.2]
  have hGLcont : Continuous (fun p : ℝ × Space =>
      (UnforcedLeray.Heat.laplacian (fun z => χ p.1 * φ (p.1, z)) p.2 : ℂ)) := by
    rw [hGLeq]
    exact (Complex.continuous_ofReal.comp hθlapcont)
  have hGL : StronglyMeasurable (fun p : ℝ × Space =>
      (UnforcedLeray.Heat.laplacian (fun z => χ p.1 * φ (p.1, z)) p.2 : ℂ)) :=
    hGLcont.stronglyMeasurable
  have hGR : StronglyMeasurable (fun p : ℝ × Space =>
      (Real.exp (-p.1) : ℂ) * ((χ p.1 * φ p : ℝ) : ℂ)) := hθAcont.stronglyMeasurable
  have hGLbound : ∀ t z,
      ‖(UnforcedLeray.Heat.laplacian (fun z => χ t * φ (t, z)) z : ℂ)‖ ≤
        ML * (Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator (fun _ => (1 : ℝ)) t * ballInd R z := by
    intro t z
    rw [hglap t z]
    simpa [θlap] using hLboundC t z
  have hGRbound : ∀ t z,
      ‖(Real.exp (-t) : ℂ) * ((χ t * φ (t, z) : ℝ) : ℂ)‖ ≤
        MR * (Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator (fun _ => (1 : ℝ)) t * ballInd R z :=
    hRbound
  have hgraphs := chartJ_cutoff_graph_identities (ν := ν) hν hq hq1 hTime hLap τ₀ e
    (lo := -(1 / 2 : ℝ)) (hi := 1 / 2) (Mθ := Mθ) (Mθt := Mθt)
    (ML := ML) (MR := MR) (R := R)
    hθsmooth hθsupp hθcont hθtcont hθderiv (by norm_num) hθbound hθtbound
    hGL hGR hGLbound hGRbound hMθ hML hMR
  have hT := hgraphs.1
  have hS0 := hgraphs.2
  have hS : ∫ p : ℝ × Space, ((χ p.1 * lapφ p : ℝ) : ℂ) * U p =
      ∫ p, (Real.exp (-p.1) : ℂ) * ((χ p.1 * φ p : ℝ) : ℂ) * A p := by
    calc
      _ = ∫ p, (UnforcedLeray.Heat.laplacian (fun z => χ p.1 * φ (p.1, z)) p.2 : ℂ) * U p := by
        apply integral_congr_ae
        filter_upwards [] with p
        rw [hglap]
      _ = ∫ p, (Real.exp (-p.1) : ℂ) * ((χ p.1 * φ p : ℝ) : ℂ) * A p := by
        simpa [U, A, Complex.real_smul] using hS0
  have hT' : ∫ p : ℝ × Space,
      ((χt p.1 * φ p : ℝ) : ℂ) * U p + ((χ p.1 * φt p : ℝ) : ℂ) * U p =
      -∫ p, ((χ p.1 * φ p : ℝ) : ℂ) * B p := by
    have := hT
    calc
      _ = ∫ p, (((χt p.1 * φ p + χ p.1 * φt p : ℝ) : ℂ) * U p) := by
        apply integral_congr_ae
        filter_upwards [] with p
        push_cast
        ring
      _ = _ := by simpa [U, B] using this
  have hcoeffbound : ∀ t z,
      ‖((χt t * φ (t, z) : ℝ) : ℂ)‖ ≤
        Mθt₁ * (Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator (fun _ => (1 : ℝ)) t * ballInd R z := by
    intro t z
    simpa [χ, χt, θt₁, Function.comp_def, Complex.norm_real] using hθt₁bound t z
  have hcoeff2bound : ∀ t z,
      ‖((χ t * φt (t, z) : ℝ) : ℂ)‖ ≤
        Mθt₂ * (Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator (fun _ => (1 : ℝ)) t * ballInd R z := by
    intro t z
    simpa [χ, χt, θt₂, Function.comp_def, Complex.norm_real] using hθt₂bound t z
  have hJ : MeasurableSet (Icc (-(1 / 2 : ℝ)) (1 / 2)) := measurableSet_Icc
  have hpathU := integrableOn_chartLp (ν := ν) hq w τ₀ (-(1 / 2 : ℝ)) (1 / 2)
  have hpathB := integrableOn_chartLp (ν := ν) hq b τ₀ (-(1 / 2 : ℝ)) (1 / 2)
  have hpathA := integrableOn_chartLp (ν := ν) hq a τ₀ (-(1 / 2 : ℝ)) (1 / 2)
  have hUθ := integrable_scalar_mul_chartJ hν w τ₀ e hJ hpathU
    hθcont.stronglyMeasurable hMθ hθbound
  have hUθt₁ := integrable_scalar_mul_chartJ hν w τ₀ e hJ hpathU
    (Complex.continuous_ofReal.comp
      ((continuous_resolventTimeCutoffDeriv.comp continuous_fst).mul hφsmooth.continuous)).stronglyMeasurable
      hMθt₁ hcoeffbound
  have hUθt₂ := integrable_scalar_mul_chartJ hν w τ₀ e hJ hpathU
    (Complex.continuous_ofReal.comp
      ((continuous_resolventTimeCutoff.comp continuous_fst).mul hφtcont)).stronglyMeasurable
      hMθt₂ hcoeff2bound
  have hUθlap := integrable_scalar_mul_chartJ hν w τ₀ e hJ hpathU
    (Complex.continuous_ofReal.comp hθlapcont).stronglyMeasurable hML hLboundC
  have hBθ := integrable_scalar_mul_chartJ hν b τ₀ e hJ hpathB
    hθcont.stronglyMeasurable hMθ hθbound
  have hAθ := integrable_scalar_mul_chartJ hν a τ₀ e hJ hpathA
    hθAcont.stronglyMeasurable hMR hRbound
  have hTgraph : ∫ p : ℝ × Space,
      (((χt p.1 * φ p + χ p.1 * φt p : ℝ) : ℂ) * U p) =
      -∫ p, ((χ p.1 * φ p : ℝ) : ℂ) * B p := by
    simpa [U, B] using hT
  have hmain := cutoff_graph_pairing_to_resolvent hTgraph hS
    (by simpa [U, θ] using hUθ)
    (by simpa [U, θt₁] using hUθt₁)
    (by simpa [U, θt₂] using hUθt₂)
    (by simpa [B, θ] using hBθ)
    (by simpa [U, θlap] using hUθlap)
    (by simpa [A, θA, θ, χ] using hAθ)
  have hsource := cutoff_resolvent_rhs_pairing
    (by simpa [U, θt₁] using hUθt₁)
    (by simpa [B, θ] using hBθ)
    (by simpa [A, θA, θ, χ] using hAθ)
    (by simpa [U, θ] using hUθ)
  calc
    _ = ∫ p : ℝ × Space,
        (((-χ p.1 * φt p - χ p.1 * lapφ p + χ p.1 * φ p : ℝ) : ℂ) * U p) := by
          apply integral_congr_ae
          filter_upwards [] with p
          simp [productTimeDerivative, productSpatialLaplacian, φ, φt, lapφ, χ, U]
          ring_nf
    _ = (∫ p, ((χt p.1 * φ p : ℝ) : ℂ) * U p) +
          (∫ p, ((χ p.1 * φ p : ℝ) : ℂ) * B p) -
          (∫ p, (Real.exp (-p.1) : ℂ) * ((χ p.1 * φ p : ℝ) : ℂ) * A p) +
          (∫ p, ((χ p.1 * φ p : ℝ) : ℂ) * U p) := hmain
    _ = ∫ p, (φ p : ℂ) *
          ((χt p.1 : ℂ) * U p + (χ p.1 : ℂ) * B p -
            (χ p.1 : ℂ) * (Real.exp (-p.1) : ℂ) * A p + (χ p.1 : ℂ) * U p) := hsource
    _ = _ := by
          apply integral_congr_ae
          filter_upwards [] with p
          simp [U, B, A, χ, χt, φ]

end UnforcedLeray.B0449
