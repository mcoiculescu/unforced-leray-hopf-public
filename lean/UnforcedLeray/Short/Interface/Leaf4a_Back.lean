import UnforcedLeray.Short.Interface.Sub.I15

/-!
# Interface leaf 4a, step W4 (task `Interface:I15`): transport back to `(τ, y)`

`windowTransportBack : WindowTransportBack` (`WindowSteps.lean`), proved unconditionally.

Source of record: `the November 2 reference manuscript`, lines 6071-6075 and
6107-6150 (regularity of the mode, `b ∈ C_per H²`, which the window Laplacian `Δ b ∈ 𝒴₂`
serves), through the window argument of the old manuscript `paper/main.tex` lines 7498-7517
(`eq:free-stress-14`, `-15`: "the distributional form of (11) supplies its derivatives").

Structure (the Props are in `Sub/I15.lean`, where `windowTransportBack_of` reduces the target to
the per-component statement `WindowComponentTransport`):

1. `windowBack_windowU_eq_heatField`: `windowU χ τ₀ w i = heatField χ (w (τ₀ + ·)) i`.
2. `windowBack_isY2_shift`, `windowBack_similarityTest_shift`: time shifts preserve `𝒴₂` and
   the similarity tests.
3. `windowBack_heatField_laplacian`: the tail of `exists_heat_laplacian` (`Window.lean`) with the
   weak second derivatives `D2` given; `windowBack_component_of_lap`: `window_component`
   (`Window.lean`) with the Laplacian given (`Lc(t, y) = e^{3t/2} Lap(e^t, e^{t/2}y)`).
4. `windowBack_componentUnshifted_of`: the unshifted transport for `u_c = windowU χ τ₀ w c`.
5. `windowBack_memLp_shift`, `windowBack_cutoff_laplacian`: the shift of `L²` on slabs and the
   removal of the cutoff on a test supported in the window.
6. `windowBack_componentTransport_of`: shift the phase by `τ₀`, `integral_timeShift`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.Interface

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Cons.C08
open UnforcedLeray.Cons.L2
open UnforcedLeray.Cons.L2.FreeLapReg (timeShift measurePreserving_timeShift)

section HeatLap

open UnforcedLeray.Cons.L2.FreeLapReg
open UnforcedLeray.Parabolic (IsSTTest sLap sD2)

theorem windowBack_heatField_laplacian : HeatFieldLaplacianOfD2 := by
  intro χ W c D hu hD φ hφ
  have hint : ∀ i : Fin 3, Integrable (fun X => heatField χ W c X * sD2 i i φ X) := fun i =>
    hu.integrable_mul ((hφ.sD2 i i).memLp 2)
  have hint' : ∀ i : Fin 3, Integrable (fun X => D i i X * φ X) := fun i =>
    (hD i i).1.integrable_mul (hφ.memLp 2)
  calc ∫ X, heatField χ W c X * sLap φ X
      = ∫ X, ∑ i : Fin 3, heatField χ W c X * sD2 i i φ X := by
        refine integral_congr_ae (Eventually.of_forall fun X => ?_)
        simp only [sLap, Finset.mul_sum]
    _ = ∑ i : Fin 3, ∫ X, heatField χ W c X * sD2 i i φ X :=
        integral_finsetSum _ fun i _ => hint i
    _ = ∑ i : Fin 3, ∫ X, D i i X * φ X := Finset.sum_congr rfl fun i _ => (hD i i).2 φ hφ
    _ = ∫ X, ∑ i : Fin 3, D i i X * φ X := (integral_finsetSum _ fun i _ => hint' i).symm
    _ = ∫ X, (∑ i : Fin 3, D i i X) * φ X := by
        refine integral_congr_ae (Eventually.of_forall fun X => ?_)
        simp only [Finset.sum_mul]

theorem windowBack_component_of_lap : WindowComponentOfLap := by
  intro P W χ c Lap hP hW hχ hχc hLap hLapEq
  have hu := memLp_heatField hP hW hχ hχc c
  refine ⟨fun z => Real.exp (3 / 2 * z.1) * Lap (simE z), fun a b => ?_, fun Ψ hΨ => ?_⟩
  · exact memLp_weight_slab (k := fun t => Real.exp (3 / 2 * t))
      (memLp_slab_of_simMeasure (memLp_comp_simE hLap) a b)
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  set φc := pullTest Ψ c with hφc
  have hφ := isSTTest_pullTest hΨ c
  have hlift : liftTest (fun t => χ t * Real.exp t) φc c =
      fun z => (χ z.1 * Ψ z c) • coordinateVector c := by
    funext z
    simp only [liftTest, hφc, pullTest, push_simE]
    congr 1
    rw [mul_assoc, ← mul_assoc (Real.exp z.1), ← Real.exp_add, add_neg_cancel, Real.exp_zero,
      one_mul]
  have hlap : ∀ z : SpaceTime, χ z.1 * Real.exp z.1 * Real.exp z.1 * sLap φc (simE z) =
      χ z.1 * spatialLaplacian Ψ z.1 z.2 c := by
    intro z
    have h1 := spatialLaplacian_liftTest (a := fun t => χ t * Real.exp t) (c := c) hφ.1 z.1 z.2
    rw [hlift, spatialLaplacian_component hΨ.smooth] at h1
    have h2 := congrArg (fun v : Space => v c) h1
    simp only [coordinateVector_apply_self] at h2
    rw [h2]
  have hvL : ∀ X : SpaceTime, X.1 ≤ 0 → heatField χ W c X * sLap φc X = 0 := fun X hX => by
    rw [heatField, push_of_nonpos _ hX, zero_mul]
  have iL0 : Integrable (fun X => heatField χ W c X * sLap φc X) :=
    hu.integrable_mul ((isSTTest_sLap hφ).memLp 2)
  have ptL : ∀ z : SpaceTime, Real.exp (5 / 2 * z.1) * (heatField χ W c (simE z) *
      sLap φc (simE z)) = W z.1 z.2 c * (χ z.1 * spatialLaplacian Ψ z.1 z.2 c) := by
    intro z
    rw [← hlap z, heatField, push_simE]
    linear_combination (χ z.1 * W z.1 z.2 c * sLap φc (simE z)) * exp_comb_u z.1
  have hvR : ∀ X : SpaceTime, X.1 ≤ 0 → Lap X * φc X = 0 := fun X hX => by
    rw [hφc, pullTest, push_of_nonpos _ hX, mul_zero]
  have iR0 : Integrable (fun X => Lap X * φc X) := hLap.integrable_mul (hφ.memLp 2)
  have ptR : ∀ z : SpaceTime, Real.exp (5 / 2 * z.1) * (Lap (simE z) * φc (simE z)) =
      Real.exp (3 / 2 * z.1) * Lap (simE z) * Ψ z c := by
    intro z
    rw [hφc, pullTest, push_simE]
    linear_combination (Lap (simE z) * Ψ z c) * exp_comb_L z.1
  have iL := integrable_of_vanish hvL iL0
  have iR := integrable_of_vanish hvR iR0
  simp_rw [ptL] at iL
  simp_rw [ptR] at iR
  refine ⟨iL, iR, ?_⟩
  have key := hLapEq φc hφ
  rw [integral_eq_of_vanish hvL, integral_eq_of_vanish hvR] at key
  simp_rw [ptL, ptR] at key
  exact key

end HeatLap
theorem windowBack_windowU_eq_heatField : WindowUEqHeatField := by
  intro χ τ₀ w i
  funext X
  unfold windowU UnforcedLeray.Cons.L2.FreeLapReg.heatField UnforcedLeray.Cons.L2.FreeLapReg.push
  by_cases hX : 0 < X.1
  · simp only [hX, ite_true, chartField, UnforcedLeray.Cons.L2.FreeLapReg.simG]
    simp [PiLp.smul_apply, mul_assoc]
  · simp [hX]

theorem windowBack_similarityTest_shift : SimilarityTestShift := by
  intro Ψ τ₀ hΨ
  refine ⟨?_, ?_⟩
  · exact hΨ.smooth.comp ((contDiff_const.add contDiff_fst).prodMk contDiff_snd)
  · have hhe : Topology.IsClosedEmbedding (fun z : SpaceTime => (τ₀ + z.1, z.2)) :=
      (Homeomorph.prodCongr (Homeomorph.addLeft τ₀) (Homeomorph.refl Space)).isClosedEmbedding
    exact hΨ.compact.comp_isClosedEmbedding hhe

theorem windowBack_memLp_shift : MemLpWindowShift := by
  intro τ₀ Lc hLc
  have hmp : MeasurePreserving (timeShift (-τ₀)) volume volume := measurePreserving_timeShift (-τ₀)
  have h1 := hmp.restrict_preimage_emb (timeShift (-τ₀)).measurableEmbedding (FreeLapReg.slab (-1) 1)
  have h2 := (hLc (-1) 1).comp_measurePreserving h1
  refine MemLp.mono_measure (Measure.restrict_mono ?_ le_rfl) h2
  intro z hz
  obtain ⟨hz1, -⟩ := hz
  simp only [mem_preimage, FreeLapReg.timeShift_apply]
  refine ⟨⟨by linarith [hz1.1], by linarith [hz1.2]⟩, mem_univ _⟩

theorem windowBack_cutoff_laplacian : CutoffLaplacianShift := by
  intro χ τ₀ ψ hχ hψ hsupp t y c
  by_cases ht : t ∈ Icc (-1 : ℝ) 1
  · rw [hχ.one t ht, one_mul]
    rfl
  · have hz : ∀ y' : Space, ψ (τ₀ + t, y') = 0 := by
      intro y'
      by_contra hne
      have h3 : (τ₀ + t, y') ∈ tsupport ψ := subset_tsupport _ hne
      have h4 := hsupp h3
      apply ht
      obtain ⟨h5, -⟩ := h4
      exact ⟨by linarith [h5.1], by linarith [h5.2]⟩
    have h1 : spatialLaplacian ψ (τ₀ + t) y = 0 := by
      unfold spatialLaplacian spatialDerivative
      have : (fun y' => ψ (τ₀ + t, y')) = fun _ => 0 := funext hz
      simp [this]
    have h2 : spatialLaplacian (fun z : SpaceTime => ψ (τ₀ + z.1, z.2)) t y = 0 := h1
    rw [h2, h1]
    simp

theorem windowBack_isY2_shift : IsY2ShiftProp := by
  intro P w τ₀ hP hw
  have hmp := measurePreserving_timeShift τ₀
  have e : (fun z : SpaceTime => w (τ₀ + z.1) z.2) =
      (fun z : SpaceTime => w z.1 z.2) ∘ timeShift τ₀ := by
    funext z
    simp [FreeLapReg.timeShift_apply, add_comm]
  refine ⟨?_, ?_, ?_⟩
  · intro t
    show w (τ₀ + (t + P)) = w (τ₀ + t)
    rw [← add_assoc]
    exact hw.periodic (τ₀ + t)
  · have := hw.measurable.comp_measurePreserving hmp
    rw [← e] at this
    exact this
  · have hs := FreeLapReg.IsY2.memLp_slab hP hw τ₀ (τ₀ + P)
    have h1 := hmp.restrict_preimage_emb (timeShift τ₀).measurableEmbedding
      (FreeLapReg.slab τ₀ (τ₀ + P))
    have h2 := hs.comp_measurePreserving h1
    have hsub : periodSlab P ⊆ timeShift τ₀ ⁻¹' FreeLapReg.slab τ₀ (τ₀ + P) := by
      intro z hz
      obtain ⟨hz1, -⟩ := hz
      simp only [mem_preimage, FreeLapReg.timeShift_apply]
      exact ⟨⟨by linarith [hz1.1], by linarith [hz1.2]⟩, mem_univ _⟩
    have h3 := MemLp.mono_measure (Measure.restrict_mono hsub le_rfl) h2
    rw [← e] at h3
    exact h3

theorem windowBack_componentUnshifted_of (h1 : WindowUEqHeatField) (h2 : IsY2ShiftProp)
    (h4 : HeatFieldLaplacianOfD2) (h5 : WindowComponentOfLap) : WindowComponentUnshifted := by
  intro P w χ τ₀ c hP hw hχ hχc hD2
  obtain ⟨D2, hD2⟩ := hD2
  have hW := h2 P w τ₀ hP hw
  rw [h1 χ τ₀ w c] at hD2
  have hu := FreeLapReg.memLp_heatField hP hW hχ hχc c
  have hLap : MemLp (fun X => ∑ i : Fin 3, D2 i i X) 2 volume :=
    memLp_finsetSum _ fun i _ => (hD2 i i).1
  exact h5 P (fun t => w (τ₀ + t)) χ c _ hP hW hχ hχc hLap (h4 χ _ c D2 hu hD2)

theorem windowBack_componentTransport_of (h3 : SimilarityTestShift) (h6 : WindowComponentUnshifted)
    (h7 : MemLpWindowShift) (h8 : CutoffLaplacianShift) : WindowComponentTransport := by
  intro P w χ τ₀ c hP hw hχ hD2
  obtain ⟨Lc, hLc, hEq⟩ := h6 P w χ τ₀ c hP hw hχ.smooth hχ.compact hD2
  refine ⟨fun z => Lc (z.1 - τ₀, z.2), h7 τ₀ Lc hLc, fun ψ hψ hsupp => ?_⟩
  obtain ⟨i1, i2, i3⟩ := hEq _ (h3 ψ τ₀ hψ)
  have hmp := measurePreserving_timeShift τ₀
  have hemb := (timeShift τ₀).measurableEmbedding
  have hpt : ∀ z : SpaceTime, χ z.1 * spatialLaplacian (fun z : SpaceTime => ψ (τ₀ + z.1, z.2))
      z.1 z.2 c = spatialLaplacian ψ (τ₀ + z.1) z.2 c := fun z =>
    h8 χ τ₀ ψ hχ hψ hsupp z.1 z.2 c
  have e1 : (fun z : SpaceTime => w (τ₀ + z.1) z.2 c * (χ z.1 *
      spatialLaplacian (fun z : SpaceTime => ψ (τ₀ + z.1, z.2)) z.1 z.2 c)) =
      (fun z : SpaceTime => w z.1 z.2 c * spatialLaplacian ψ z.1 z.2 c) ∘ timeShift τ₀ := by
    funext z
    simp only [Function.comp_apply, FreeLapReg.timeShift_apply, hpt z, add_comm z.1 τ₀]
  have e2 : (fun z : SpaceTime => Lc z * (fun z : SpaceTime => ψ (τ₀ + z.1, z.2)) z c) =
      (fun z : SpaceTime => Lc (z.1 - τ₀, z.2) * ψ z c) ∘ timeShift τ₀ := by
    funext z
    simp only [Function.comp_apply, FreeLapReg.timeShift_apply, add_sub_cancel_right,
      add_comm τ₀ z.1, Prod.mk.eta]
  rw [e1] at i1 i3
  rw [e2] at i2
  rw [e2] at i3
  refine ⟨(hmp.integrable_comp_emb hemb).mp i1, (hmp.integrable_comp_emb hemb).mp i2, ?_⟩
  have k1 := FreeLapReg.integral_timeShift
    (fun z : SpaceTime => w z.1 z.2 c * spatialLaplacian ψ z.1 z.2 c) τ₀
  have k2 := FreeLapReg.integral_timeShift (fun z : SpaceTime => Lc (z.1 - τ₀, z.2) * ψ z c) τ₀
  calc ∫ z : SpaceTime, w z.1 z.2 c * spatialLaplacian ψ z.1 z.2 c
      = ∫ z : SpaceTime, (fun z : SpaceTime => w z.1 z.2 c * spatialLaplacian ψ z.1 z.2 c)
          (z.1 + τ₀, z.2) := k1.symm
    _ = ∫ z : SpaceTime, (fun z : SpaceTime => Lc (z.1 - τ₀, z.2) * ψ z c) (z.1 + τ₀, z.2) := i3
    _ = ∫ z : SpaceTime, Lc (z.1 - τ₀, z.2) * ψ z c := k2

theorem windowBack_componentUnshifted : WindowComponentUnshifted :=
  windowBack_componentUnshifted_of windowBack_windowU_eq_heatField windowBack_isY2_shift
    windowBack_heatField_laplacian windowBack_component_of_lap

theorem windowBack_componentTransport : WindowComponentTransport :=
  windowBack_componentTransport_of windowBack_similarityTest_shift
    windowBack_componentUnshifted windowBack_memLp_shift windowBack_cutoff_laplacian

/-- **Step W4** (`paper/main.tex` 7498-7517): from the weak second derivatives of the three
components `u_i = windowU χ τ₀ w i` to the window Laplacian of `w`. -/
theorem windowTransportBack : WindowTransportBack :=
  windowTransportBack_of windowBack_componentTransport

end UnforcedLeray.Short.Interface
