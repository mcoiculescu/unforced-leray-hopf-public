import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.BsCutoff
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.BsTestDense
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.BsSliceL2
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.BsSliceSolFixed

/-!
# A.e. slice solenoidality (BSSliceSol)

Source `the November 2 reference manuscript` lines 1351-1362.

Plan.  A countable family `D` of tests (`bsDense_strong`, built from the separable-space
argument of `BsTestDense`, with the radius of an approximant equal to the radius of the test it
approximates) satisfies `∫ ∇χ' · Φ(t) = 0` for a.e. `t` simultaneously (`ae_ball_iff`).  For an
arbitrary test `χ` with support in `closedBall n`, a `D`-approximant `χ'` with
`sup |∇χ - ∇χ'| ≤ ε` and support in the same ball gives `|∫ ∇χ · Φ(t)| ≤ C ε` with `C` independent
of `ε` (`bs_slice_of_dense`).  The slice is in `L²`, hence `L¹` on the ball.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Countable family of tests with radius-preserving density: every test `χ` supported in
`closedBall n` is approximated in `∇` sup-norm by a member of `D` supported in `closedBall n`. -/
theorem bsDense_strong : ∃ D : Set (Space → ℂ), D.Countable ∧ (∀ χ' ∈ D, ∃ m : ℕ, χ' ∈ bsTn m) ∧
    ∀ (n : ℕ) (χ : Space → ℂ), χ ∈ bsTn n → ∀ ε : ℝ, 0 < ε →
      ∃ χ' ∈ D, χ' ∈ bsTn n ∧ ∀ y : Space, ‖bsGradS χ y - bsGradS χ' y‖ ≤ ε := by
  choose T hTsub hTcount hTdense using bsDense_exists
  refine ⟨⋃ n : ℕ, (bsPick n) '' (T n), Set.countable_iUnion fun n => (hTcount n).image _, ?_, ?_⟩
  · intro χ' hχ'
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hχ'
    obtain ⟨q, _, rfl⟩ := hn
    exact ⟨n, bsPick_mem n q⟩
  · intro n χ hχ ε hε
    have hmem : bsEmb n ⟨χ, hχ⟩ ∈ Set.range (bsEmb n) := ⟨⟨χ, hχ⟩, rfl⟩
    have hclose := hTdense n hmem
    rw [Metric.mem_closure_iff] at hclose
    obtain ⟨q, hqT, hqd⟩ := hclose ε hε
    have hqR : q ∈ Set.range (bsEmb n) := hTsub n hqT
    have hχ'mem : bsPick n q ∈ bsTn n := bsPick_mem n q
    have hemb : bsEmb n ⟨bsPick n q, hχ'mem⟩ = q := bsPick_emb n q hqR
    have hd : dist (bsEmb n ⟨χ, hχ⟩) (bsEmb n ⟨bsPick n q, hχ'mem⟩) < ε := by
      rw [hemb]
      exact hqd
    refine ⟨bsPick n q, Set.mem_iUnion.2 ⟨n, q, hqT, rfl⟩, hχ'mem, fun y => ?_⟩
    by_cases hy : (n : ℝ) < ‖y‖
    · rw [bsGradS_eq_zero_of_outside hχ hy, bsGradS_eq_zero_of_outside hχ'mem hy, sub_zero,
        norm_zero]
      exact hε.le
    · push Not at hy
      have hyb : y ∈ Metric.closedBall (0 : Space) n := by
        rw [mem_closedBall_zero_iff]
        exact hy
      have h1 := ContinuousMap.dist_apply_le_dist (f := bsEmb n ⟨χ, hχ⟩)
        (g := bsEmb n ⟨bsPick n q, hχ'mem⟩) ⟨y, hyb⟩
      have h2 := le_of_lt (lt_of_le_of_lt h1 hd)
      rw [show bsEmb n ⟨χ, hχ⟩ ⟨y, hyb⟩ = (χ y, bsGradS χ y) from rfl,
        show bsEmb n ⟨bsPick n q, hχ'mem⟩ ⟨y, hyb⟩ = (bsPick n q y, bsGradS (bsPick n q) y) from rfl,
        Prod.dist_eq] at h2
      have h3 := le_trans (le_max_right _ _) h2
      rw [dist_eq_norm] at h3
      exact h3

/-- Integrability of `y ↦ g(y) · f(y)` for continuous `g` vanishing outside `closedBall m` and
`f ∈ L²(ℝ³)`. -/
theorem bs_pair_integrable (f : Space → CVec3) (hf : MemLp f 2 volume) (g : Space → CVec3)
    (hg : Continuous g) (m : ℕ) (hg0 : ∀ y : Space, (m : ℝ) < ‖y‖ → g y = 0) :
    Integrable (fun y : Space => dotL (g y) (f y)) volume := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Space) (m : ℝ)).exists_bound_of_continuousOn
    hg.continuousOn
  have hfn : MemLp (fun y : Space => ‖f y‖) 2 volume := hf.norm
  have : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : Space) (m : ℝ))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_closedBall_lt_top (μ := (volume : Measure Space))⟩
  have hIf : Integrable ((Metric.closedBall (0 : Space) (m : ℝ)).indicator
      (fun y : Space => ‖f y‖)) volume := by
    rw [integrable_indicator_iff measurableSet_closedBall]
    exact (hfn.restrict _).integrable (by norm_num)
  refine Integrable.mono' (hIf.const_mul (‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ * M)) ?_ ?_
  · exact (ContinuousLinearMap.continuous₂ (dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)).comp_aestronglyMeasurable₂
      hg.aestronglyMeasurable hf.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun y => ?_
    by_cases hy : y ∈ Metric.closedBall (0 : Space) (m : ℝ)
    · rw [Set.indicator_of_mem hy]
      have h1 := bsDotL_bound (g y) (f y)
      have h2 : ‖g y‖ ≤ M := hM y hy
      calc ‖dotL (g y) (f y)‖ ≤ ‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ * ‖g y‖ * ‖f y‖ := h1
        _ ≤ ‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ * M * ‖f y‖ := by gcongr
    · have hyn : (m : ℝ) < ‖y‖ := lt_of_not_ge (fun h => hy (mem_closedBall_zero_iff.2 h))
      rw [Set.indicator_of_notMem hy, hg0 y hyn]
      simp

/-- Slice-level criterion: an `L²` field orthogonal to every test of a family `D` that
approximates each test `χ` in `∇`-sup-norm with support radius preserved is solenoidal. -/
theorem bs_slice_of_dense (f : Space → CVec3) (hf : MemLp f 2 volume) (D : Set (Space → ℂ))
    (hDt : ∀ χ' ∈ D, ∫ y : Space, dotL (bsGradS χ' y) (f y) = 0)
    (hDapp : ∀ (n : ℕ) (χ : Space → ℂ), χ ∈ bsTn n → ∀ ε : ℝ, 0 < ε →
      ∃ χ' ∈ D, χ' ∈ bsTn n ∧ ∀ y : Space, ‖bsGradS χ y - bsGradS χ' y‖ ≤ ε) :
    BSSliceSolenoidal f := by
  intro χ hχ hχc
  obtain ⟨r, hr⟩ := hχc.isCompact.isBounded.subset_closedBall (0 : Space)
  have hrn : r ≤ ((⌈r⌉₊ : ℕ) : ℝ) := Nat.le_ceil r
  have hχn : χ ∈ bsTn ⌈r⌉₊ := by
    refine ⟨hχ, fun y hy => ?_⟩
    apply image_eq_zero_of_notMem_tsupport
    intro hyt
    have h1 := hr hyt
    rw [mem_closedBall_zero_iff] at h1
    linarith
  set n : ℕ := ⌈r⌉₊ with hn
  have hI : Integrable (fun y : Space => dotL (bsGradS χ y) (f y)) volume :=
    bs_pair_integrable f hf (bsGradS χ) (bsGradS_continuous hχ) n
      (fun y hy => bsGradS_eq_zero_of_outside hχn hy)
  have hfn : MemLp (fun y : Space => ‖f y‖) 2 volume := hf.norm
  have : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : Space) (n : ℝ))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_closedBall_lt_top (μ := (volume : Measure Space))⟩
  have hIf : Integrable ((Metric.closedBall (0 : Space) (n : ℝ)).indicator
      (fun y : Space => ‖f y‖)) volume := by
    rw [integrable_indicator_iff measurableSet_closedBall]
    exact (hfn.restrict _).integrable (by norm_num)
  have hC0 : 0 ≤ ‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ *
      ∫ y : Space, (Metric.closedBall (0 : Space) (n : ℝ)).indicator (fun y : Space => ‖f y‖) y :=
    mul_nonneg (norm_nonneg (dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ))
      (integral_nonneg fun y => Set.indicator_nonneg (fun a _ => norm_nonneg (f a)) y)
  have key : ∀ ε : ℝ, 0 < ε →
      ‖∫ y : Space, dotL (bsGradS χ y) (f y)‖ ≤
        (‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ *
          ∫ y : Space, (Metric.closedBall (0 : Space) (n : ℝ)).indicator
            (fun y : Space => ‖f y‖) y) * ε := by
    intro ε hε
    obtain ⟨χ', hχ'D, hχ'n, hgr⟩ := hDapp n χ hχn ε hε
    have hI' : Integrable (fun y : Space => dotL (bsGradS χ' y) (f y)) volume :=
      bs_pair_integrable f hf (bsGradS χ') (bsGradS_continuous hχ'n.1) n
        (fun y hy => bsGradS_eq_zero_of_outside hχ'n hy)
    have hIg : Integrable (fun y : Space => dotL (bsGradS χ y - bsGradS χ' y) (f y)) volume :=
      bs_pair_integrable f hf _ ((bsGradS_continuous hχ).sub (bsGradS_continuous hχ'n.1)) n
        (fun y hy => by
          rw [bsGradS_eq_zero_of_outside hχn hy, bsGradS_eq_zero_of_outside hχ'n hy]
          simp)
    have hzero : ∫ y : Space, dotL (bsGradS χ' y) (f y) = 0 := hDt χ' hχ'D
    have hsplitI : ∫ y : Space, dotL (bsGradS χ y) (f y)
        = ∫ y : Space, dotL (bsGradS χ y - bsGradS χ' y) (f y) := by
      have h := integral_add hIg hI'
      rw [hzero, add_zero] at h
      rw [← h]
      congr 1
      funext y
      simp [map_sub]
    rw [hsplitI]
    calc ‖∫ y : Space, dotL (bsGradS χ y - bsGradS χ' y) (f y)‖
        ≤ ∫ y : Space, ‖dotL (bsGradS χ y - bsGradS χ' y) (f y)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ y : Space, (‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ * ε) *
            (Metric.closedBall (0 : Space) (n : ℝ)).indicator (fun y : Space => ‖f y‖) y := by
          refine integral_mono hIg.norm (hIf.const_mul _) fun y => ?_
          by_cases hy : y ∈ Metric.closedBall (0 : Space) (n : ℝ)
          · rw [Set.indicator_of_mem hy]
            have h1 := bsDotL_bound (bsGradS χ y - bsGradS χ' y) (f y)
            have h2 := hgr y
            calc ‖dotL (bsGradS χ y - bsGradS χ' y) (f y)‖
                ≤ ‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ * ‖bsGradS χ y - bsGradS χ' y‖ * ‖f y‖ := h1
              _ ≤ ‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ * ε * ‖f y‖ := by gcongr
              _ = (‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ * ε) * ‖f y‖ := by ring
          · have hyn : (n : ℝ) < ‖y‖ := lt_of_not_ge (fun h => hy (mem_closedBall_zero_iff.2 h))
            have h0 : bsGradS χ y - bsGradS χ' y = 0 := by
              rw [bsGradS_eq_zero_of_outside hχn hyn, bsGradS_eq_zero_of_outside hχ'n hyn]
              simp
            rw [Set.indicator_of_notMem hy, h0]
            simp
      _ = (‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ *
          ∫ y : Space, (Metric.closedBall (0 : Space) (n : ℝ)).indicator
            (fun y : Space => ‖f y‖) y) * ε := by
          rw [integral_const_mul]
          ring
  refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun δ hδ => ?_)
  set C : ℝ := ‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ *
    ∫ y : Space, (Metric.closedBall (0 : Space) (n : ℝ)).indicator (fun y : Space => ‖f y‖) y
    with hCdef
  have hε := key (δ / (C + 1)) (div_pos hδ (by linarith))
  have hCle : C * (δ / (C + 1)) ≤ δ := by
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith
  linarith [hε, hCle]

/-- A.e. slice solenoidality (all tests at once). -/
theorem bsSliceSol : BSSliceSol := by
  intro P hP Φ hΦ hsol
  obtain ⟨D, hDc, hDmem, hDapp⟩ := bsDense_strong
  have hall : ∀ᵐ t : ℝ, ∀ χ' (hχ' : χ' ∈ D), ∫ y : Space, dotL (bsGradS χ' y) (Φ (t, y)) = 0 := by
    refine (ae_ball_iff (p := fun (t : ℝ) (χ' : Space → ℂ) (_ : χ' ∈ D) =>
      ∫ y : Space, dotL (bsGradS χ' y) (Φ (t, y)) = 0) hDc).2 ?_
    intro χ' hχ'
    obtain ⟨m, hm⟩ := hDmem χ' hχ'
    exact bsSliceSolFixed P hP Φ hΦ hsol χ' hm.1 (bsTn_hasCompactSupport hm)
  filter_upwards [bsSliceL2 P hP Φ hΦ, hall] with t hL2 hDt
  exact bs_slice_of_dense (fun y : Space => Φ (t, y)) hL2 D (fun χ' hχ' => hDt χ' hχ') hDapp

end UnforcedLeray.Short.PartIIIb.Concrete
