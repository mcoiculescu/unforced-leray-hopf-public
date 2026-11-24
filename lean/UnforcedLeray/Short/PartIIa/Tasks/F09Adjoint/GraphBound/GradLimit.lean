import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F09_3_2
import UnforcedLeray.Units.B0005.Consistency
import UnforcedLeray.Units.B0413
import UnforcedLeray.Lib.PhaseSpace.Graph
import UnforcedLeray.Lib.PhaseSpace.Pairing

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- Per-test gradient identity: `phasePair(-∂ⱼΦ, testElem G) = phasePair(Φ, testElem(∂ⱼG))`
for phase tests `Φ`, `G`, by the slab integration by parts (`B0005.integral_slab_dy`) applied to
the product `dotL Φ G`, with the Leibniz rule `B0005.fderiv_dotL`. -/
theorem phasePair_dy_testElem {P : ℝ} [Fact (0 < P)] {Φ G : ℝ × Space → CVec3}
    (hΦ : IsPhaseTest P Φ) (hG : IsPhaseTest P G) (j : Fin 3) :
    phasePair P 2 (-dy j Φ) (testElem P 2 G) = phasePair P 2 Φ (testElem P 2 (dy j G)) := by
  have hΦ' : IsPhaseTest P (-dy j Φ) := (hΦ.dy j).neg
  have hK : IsPhaseTest P (fun z => dotL (Φ z) (G z)) := B0005.isPhaseTest_dotL hΦ hG
  have hΦd : Differentiable ℝ Φ := hΦ.smooth.differentiable (by simp)
  have hGd : Differentiable ℝ G := hG.smooth.differentiable (by simp)
  have hpt : ∀ z, dotL ((-dy j Φ) z) (G z) =
      -(dy j (fun z => dotL (Φ z) (G z)) z) + dotL (Φ z) (dy j G z) := by
    intro z
    have e := B0005.fderiv_dotL hΦd hGd z (0, coordinateVector j)
    have hdK : dy j (fun z => dotL (Φ z) (G z)) z =
        dotL (dy j Φ z) (G z) + dotL (Φ z) (dy j G z) := e
    rw [hdK]
    simp only [Pi.neg_apply, map_neg, neg_apply]
    ring
  have hconv : ∀ {A B : ℝ × Space → CVec3}, IsPhaseTest P A → IsPhaseTest P B →
      ∫ t in Ioc (0 : ℝ) P, ∫ y, dotL (A (t, y)) (B (t, y)) =
        ∫ z, dotL (A z) (B z) ∂((volume.restrict (Ioc (0 : ℝ) P)).prod (volume : Measure Space)) := by
    intro A B hA hB
    obtain ⟨R, hR⟩ := (B0005.isPhaseTest_dotL hA hB).bounded_support
    exact (integral_prod _ (B0005.integrable_slab (B0005.isPhaseTest_dotL hA hB).continuous hR)).symm
  rw [B0005.phasePair_testElem hΦ' hG, B0005.phasePair_testElem hΦ (hG.dy j),
    hconv hΦ' hG, hconv hΦ (hG.dy j)]
  congr 1
  simp_rw [hpt]
  obtain ⟨R₁, hR₁⟩ := (hK.dy j).bounded_support
  obtain ⟨R₂, hR₂⟩ := (B0005.isPhaseTest_dotL hΦ (hG.dy j)).bounded_support
  have hI1 := B0005.integrable_slab (𝒯 := P) (hK.dy j).continuous hR₁
  have hI2 := B0005.integrable_slab (𝒯 := P) (B0005.isPhaseTest_dotL hΦ (hG.dy j)).continuous hR₂
  have hn : Integrable (fun z => -(dy j (fun z => dotL (Φ z) (G z)) z))
      ((volume.restrict (Ioc (0 : ℝ) P)).prod (volume : Measure Space)) := hI1.neg
  rw [integral_add hn hI2, integral_neg, B0005.integral_slab_dy hK j]
  simp

theorem testElem_sub_loc {P : ℝ} [Fact (0 < P)] {Φ Ψ : ℝ × Space → CVec3}
    (hΦ : IsSliceTest P 2 Φ) (hΨ : IsSliceTest P 2 Ψ) :
    testElem P 2 (Φ - Ψ) = testElem P 2 Φ - testElem P 2 Ψ := by
  have h : Φ - Ψ = Φ + (-1 : ℂ) • Ψ := by
    funext p
    simp [sub_eq_add_neg]
  rw [h, testElem_add hΦ (hΨ.const_smul _), testElem_const_smul hΨ, neg_one_smul, ← sub_eq_add_neg]

/-- Spatial Laplacian is additive-subtractive on smooth data. -/
theorem lapT_sub_phase {P : ℝ} {A B : ℝ × Space → CVec3} (hA : IsPhaseTest P A)
    (hB : IsPhaseTest P B) : lapT (A - B) = lapT A - lapT B := by
  funext p
  have hdA : Differentiable ℝ A := hA.smooth.differentiable (by simp)
  have hdB : Differentiable ℝ B := hB.smooth.differentiable (by simp)
  have h1 : ∀ j, dy j (A - B) = dy j A - dy j B := fun j => B0413.dy_sub' hdA hdB j
  have h2 : ∀ j, dy j (dy j (A - B)) = dy j (dy j A) - dy j (dy j B) := by
    intro j
    rw [h1 j]
    exact B0413.dy_sub' ((hA.dy j).smooth.differentiable (by simp))
      ((hB.dy j).smooth.differentiable (by simp)) j
  simp only [lapT, Pi.sub_apply, h2, ← Finset.sum_sub_distrib]

theorem nuLapT_sub_phase {P : ℝ} (ν : ℝ) {A B : ℝ × Space → CVec3} (hA : IsPhaseTest P A)
    (hB : IsPhaseTest P B) : nuLapT ν (A - B) = nuLapT ν A - nuLapT ν B := by
  simp only [nuLapT, lapT_sub_phase hA hB, smul_sub]

/-- Energy identity on a phase test: `ν Σⱼ ‖∂ⱼ D‖² = -Re ⟨D, νΔD⟩`. -/
theorem energy_testElem {P : ℝ} [Fact (0 < P)] (ν : ℝ) {D : ℝ × Space → CVec3}
    (hD : IsPhaseTest P D) :
    ν * ∑ j, ‖testElem P 2 (dy j D)‖ ^ 2 =
      -(inner ℂ (testElem P 2 D) (testElem P 2 (nuLapT ν D))).re := by
  have hG2 : IsPhaseTest P (nuLapT ν D) := hD.lapT.const_smul ν
  have c2 : (inner ℂ (testElem P 2 D) (testElem P 2 (nuLapT ν D))).re =
      -(ν * ∑ j, ‖testElem P 2 (dy j D)‖ ^ 2) := by
    rw [inner_testElem_two hD hG2, phaseTestLap P ν D hD]
    have e1 : (-(ν : ℂ) * ∑ j : Fin 3, slabInner P (dy j D) (dy j D)).re =
        -(ν * ∑ j : Fin 3, (slabInner P (dy j D) (dy j D)).re) := by
      rw [neg_mul, Complex.neg_re, Complex.re_ofReal_mul, Complex.re_sum]
    rw [Complex.re_ofReal_mul, e1]
    have : ∀ j : Fin 3, ‖testElem P 2 (dy j D)‖ ^ 2 = P⁻¹ * (slabInner P (dy j D) (dy j D)).re :=
      fun j => normSq_testElem (hD.dy j)
    simp only [this, ← Finset.mul_sum]
    ring
  rw [c2]; ring


theorem d2GradLimit : D2GradLimit := by
  intro P _ ν hν w G hG hw hL
  have hGs : ∀ n, IsSliceTest P 2 (G n) := fun n => (hG n).isSliceTest 2
  set e : ℕ → Yq P 2 := fun n => testElem P 2 (G n) with he
  set l : ℕ → Yq P 2 := fun n => testElem P 2 (nuLapT ν (G n)) with hl
  set a : Fin 3 → ℕ → Yq P 2 := fun j n => testElem P 2 (dy j (G n)) with ha
  have hec := hw.cauchySeq
  have hlc := hL.cauchySeq
  rw [cauchySeq_iff_tendsto_dist_atTop_0] at hec hlc
  -- the key estimate
  have key : ∀ n m, ∀ j : Fin 3, ‖a j n - a j m‖ ^ 2 ≤ ν⁻¹ * (dist (e n) (e m) * dist (l n) (l m)) := by
    intro n m j
    have hD : IsPhaseTest P (G n - G m) := (hG n).sub (hG m)
    have en := energy_testElem ν hD
    have t1 : testElem P 2 (G n - G m) = e n - e m := testElem_sub_loc (hGs n) (hGs m)
    have t2 : testElem P 2 (nuLapT ν (G n - G m)) = l n - l m := by
      rw [nuLapT_sub_phase ν (hG n) (hG m)]
      exact testElem_sub_loc (((hG n).lapT.const_smul ν).isSliceTest 2)
        (((hG m).lapT.const_smul ν).isSliceTest 2)
    have t3 : ∀ k : Fin 3, testElem P 2 (dy k (G n - G m)) = a k n - a k m := by
      intro k
      rw [B0413.dy_sub' ((hG n).smooth.differentiable (by simp))
        ((hG m).smooth.differentiable (by simp)) k]
      exact testElem_sub_loc (((hG n).dy k).isSliceTest 2) (((hG m).dy k).isSliceTest 2)
    rw [t1, t2] at en
    simp only [t3] at en
    have hb : -(inner ℂ (e n - e m) (l n - l m)).re ≤ dist (e n) (e m) * dist (l n) (l m) := by
      have h1 := Complex.abs_re_le_norm (inner ℂ (e n - e m) (l n - l m))
      have h2 := norm_inner_le_norm (𝕜 := ℂ) (e n - e m) (l n - l m)
      rw [dist_eq_norm, dist_eq_norm]
      have := neg_abs_le (inner ℂ (e n - e m) (l n - l m)).re
      linarith
    have hj : ‖a j n - a j m‖ ^ 2 ≤ ∑ k, ‖a k n - a k m‖ ^ 2 :=
      Finset.single_le_sum (f := fun k => ‖a k n - a k m‖ ^ 2) (fun k _ => by positivity)
        (Finset.mem_univ j)
    have : ν * ‖a j n - a j m‖ ^ 2 ≤ dist (e n) (e m) * dist (l n) (l m) := by
      nlinarith
    rw [inv_mul_eq_div, le_div_iff₀ hν]
    linarith
  have hprod : Tendsto (fun p : ℕ × ℕ => ν⁻¹ * (dist (e p.1) (e p.2) * dist (l p.1) (l p.2)))
      atTop (𝓝 0) := by
    simpa using (hec.mul hlc).const_mul ν⁻¹
  have hcj : ∀ j, CauchySeq (a j) := by
    intro j
    rw [cauchySeq_iff_tendsto_dist_atTop_0]
    have hs := (Real.continuous_sqrt.tendsto 0).comp hprod
    simp only [Function.comp_def, Real.sqrt_zero] at hs
    refine squeeze_zero (fun p => dist_nonneg) (fun p => ?_) hs
    rw [dist_eq_norm]
    calc ‖a j p.1 - a j p.2‖ = Real.sqrt (‖a j p.1 - a j p.2‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ _ := Real.sqrt_le_sqrt (key p.1 p.2 j)
  choose g hg using fun j => cauchySeq_tendsto_of_complete (hcj j)
  refine ⟨g, ?_, ?_⟩
  · intro j
    have hmem : ∀ n, (e n, a j n) ∈ {x : Yq P 2 × Yq P 2 | HasPhaseOp (fun Φ => -dy j Φ) x.1 x.2} :=
      fun n Φ hΦ => phasePair_dy_testElem hΦ (hG n) j
    have hcl := isClosed_hasPhaseOp (P := P) (q := 2) (fun Φ => -dy j Φ)
    have hT : Tendsto (fun n => (e n, a j n)) atTop (𝓝 ((w : Yq P 2), g j)) :=
      Tendsto.prodMk_nhds hw (hg j)
    have hE : ∀ᶠ n in atTop, (e n, a j n) ∈
        {x : Yq P 2 × Yq P 2 | HasPhaseOp (P := P) (q := 2) (fun Φ => -dy j Φ) x.1 x.2} :=
      Eventually.of_forall hmem
    have hm : ((w : Yq P 2), g j) ∈ {x : Yq P 2 × Yq P 2 |
        HasPhaseOp (P := P) (q := 2) (fun Φ => -dy j Φ) x.1 x.2} := hcl.mem_of_tendsto hT hE
    exact hm
  · exact tendsto_finset_sum _ fun j _ => ((hg j).norm).pow 2

end UnforcedLeray.Short.PartIIa
