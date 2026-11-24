import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.LerayForceProj.Reduction

/-!
# Slicing `∂ⱼF = G` on `Y_q` into the phases, and back (leaves of `PartII-b:G4/4/2/org`)

Source: `the November 2 reference manuscript` lines 2370-2383 (the phase-space
derivative `∂_j` in `W^{1,Y_p}`), 1307-1308.

* `aeSliceDy : AeSliceDy`: one test, almost every phase (product tests `e_n(τ)ψ(y)eᵢ`, Fourier
  uniqueness on `ℝ/Pℤ`; the pattern of `B0428.ae_slice_pair`);
* `aeForallSliceDy : AeForallSliceDy`: one null set for all tests (`1 < q`; a countable family
  dense for the pairings; the pattern of `B0428.ae_forall_pair`);
* `hasPhaseOpDyOfAe : HasPhaseOpDyOfAe`: the slice identities give the phase-space identity
  (each slice of a phase test is a smooth compactly supported test on `ℝ³`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.RieszLp
  UnforcedLeray.B0411 UnforcedLeray.B0412

/-! ## One test, almost every phase -/

/-- **Leaf `AeSliceDy`.** -/
theorem aeSliceDy : AeSliceDy := by
  intro P _ q _ j F G h ψ hψ i
  have hψj : IsSpatialTest (spatialTestDerivative j ψ) := hψ.derivative j
  have hint : Integrable (fun τ => innerPair q (B0428.sT q hψj i) (F τ) +
      innerPair q (B0428.sT q hψ i) (G τ)) (AddCircle.haarAddCircle (T := P)) :=
    ((innerPair q _).integrable_comp (integrable_Yq F)).add
      ((innerPair q _).integrable_comp (integrable_Yq G))
  have hF : ∀ n : ℤ, ∫ τ, fourier n τ * (innerPair q (B0428.sT q hψj i) (F τ) +
      innerPair q (B0428.sT q hψ i) (G τ)) ∂AddCircle.haarAddCircle = 0 := by
    intro n
    have i1 := (innerPair q (B0428.sT q hψj i)).integrable_comp (integrable_fourier_smul F n)
    have i2 := (innerPair q (B0428.sT q hψ i)).integrable_comp (integrable_fourier_smul G n)
    simp only [map_smul, smul_eq_mul] at i1 i2
    have e1 : ∫ τ, fourier n τ * innerPair q (B0428.sT q hψj i) (F τ)
        ∂AddCircle.haarAddCircle =
        innerPair q (B0428.sT q hψj i) (∫ τ, fourier n τ • F τ ∂AddCircle.haarAddCircle) := by
      rw [← (innerPair q (B0428.sT q hψj i)).integral_comp_comm (integrable_fourier_smul F n)]
      simp only [map_smul, smul_eq_mul]
    have e2 : ∫ τ, fourier n τ * innerPair q (B0428.sT q hψ i) (G τ)
        ∂AddCircle.haarAddCircle =
        innerPair q (B0428.sT q hψ i) (∫ τ, fourier n τ • G τ ∂AddCircle.haarAddCircle) := by
      rw [← (innerPair q (B0428.sT q hψ i)).integral_comp_comm (integrable_fourier_smul G n)]
      simp only [map_smul, smul_eq_mul]
    have hd : -dy j (prodTest P n ψ i) = -prodTest P n (spatialTestDerivative j ψ) i := by
      rw [B0428.dy_prodTest n hψ i j]
      rfl
    have hp' : -innerPair q (B0428.sT q hψj i)
        (∫ τ, fourier n τ • F τ ∂AddCircle.haarAddCircle) =
        innerPair q (B0428.sT q hψ i) (∫ τ, fourier n τ • G τ ∂AddCircle.haarAddCircle) := by
      have hp := h _ (isPhaseTest_prodTest n hψ.smooth hψ.compact i)
      have e3 := phasePair_neg (isPhaseTest_prodTest (P := P) n hψj.smooth hψj.compact i) F
      rw [phasePair_prodTest F n hψj.smooth hψj.compact i] at e3
      rw [phasePair_prodTest G n hψ.smooth hψ.compact i] at hp
      change phasePair P q (-dy j (prodTest P n ψ i)) F = _ at hp
      rw [hd, e3] at hp
      exact hp
    simp only [mul_add]
    rw [integral_add i1 i2, e1, e2]
    linear_combination -hp'
  filter_upwards [ae_eq_zero_of_fourier hint hF] with τ hτ
  exact eq_neg_of_add_eq_zero_left hτ

/-! ## A common null set for all tests -/

/-- The pairings `⟪x.2, u⟫ = -⟪x.1, Λ⟫` for all components: a closed condition. -/
def PairCondDy (q : ℝ≥0∞) [Fact (1 ≤ q)] (u Λ : Lp CVec3 q (volume : Measure Space))
    (x : Fin 3 → Lp CVec3 (conjExp q) (volume : Measure Space) ×
      Lp CVec3 (conjExp q) (volume : Measure Space)) : Prop :=
  ∀ i, innerPair q (x i).2 u = -innerPair q (x i).1 Λ

theorem isClosed_pairCondDy {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (u Λ : Lp CVec3 q (volume : Measure Space)) : IsClosed {x | PairCondDy q u Λ x} := by
  have h : {x | PairCondDy q u Λ x} = ⋂ i : Fin 3,
      {x : Fin 3 → Lp CVec3 (conjExp q) (volume : Measure Space) ×
        Lp CVec3 (conjExp q) (volume : Measure Space) |
          innerPair q (x i).2 u = -innerPair q (x i).1 Λ} := by
    ext x; simp [PairCondDy]
  rw [h]
  refine isClosed_iInter fun i => isClosed_eq ?_ ?_
  · exact ((innerPair q).continuous.comp (continuous_snd.comp (continuous_apply i))).clm_apply
      continuous_const
  · exact (((innerPair q).continuous.comp (continuous_fst.comp (continuous_apply i))).clm_apply
      continuous_const).neg

/-- The embedding of a spatial test `ψ ↦ (ψeᵢ, (∂ⱼψ)eᵢ)ᵢ`. -/
def testEmbDy (q : ℝ≥0∞) (j : Fin 3) (ψ : {ψ : Space → ℝ // IsSpatialTest ψ}) :
    Fin 3 → Lp CVec3 (conjExp q) (volume : Measure Space) ×
      Lp CVec3 (conjExp q) (volume : Measure Space) :=
  fun i => (B0428.sT q ψ.2 i, B0428.sT q (ψ.2.derivative j) i)

/-- **Leaf `AeForallSliceDy`.** -/
theorem aeForallSliceDy : AeForallSliceDy := by
  intro P _ q _ hq1 j F G h
  have : Fact (conjExp q ≠ ⊤) := ⟨B0428.conjExp_ne_top hq1⟩
  have h1 : SecondCountableTopology (Lp CVec3 (conjExp q) (volume : Measure Space)) :=
    inferInstance
  have h2 : SecondCountableTopology (Lp CVec3 (conjExp q) (volume : Measure Space) ×
      Lp CVec3 (conjExp q) (volume : Measure Space)) := inferInstance
  have h3 : SecondCountableTopology (Fin 3 → Lp CVec3 (conjExp q) (volume : Measure Space) ×
      Lp CVec3 (conjExp q) (volume : Measure Space)) := inferInstance
  set s := range (testEmbDy q j) with hs
  have hsep : TopologicalSpace.IsSeparable s := TopologicalSpace.IsSeparable.of_separableSpace s
  have := hsep.separableSpace
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense s
  have hsub : s ⊆ closure (Subtype.val '' D) := Subtype.dense_iff.1 hDd
  have : Countable D := hDc.to_subtype
  have hgood : ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)), ∀ d : D,
      PairCondDy q (F τ) (G τ) (d : s) := by
    rw [ae_all_iff]
    intro d
    obtain ⟨ψ, hψ⟩ := (d : s).2
    rw [← hψ]
    have hi : ∀ i : Fin 3, ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)),
        innerPair q (B0428.sT q (ψ.2.derivative j) i) (F τ) =
          -innerPair q (B0428.sT q ψ.2 i) (G τ) := fun i => h ψ.1 ψ.2 i
    filter_upwards [ae_all_iff.2 hi] with τ hτ
    exact hτ
  filter_upwards [hgood] with τ hτ
  intro ψ hψ i
  have hcl : closure (Subtype.val '' D) ⊆ {x | PairCondDy q (F τ) (G τ) x} := by
    refine closure_minimal ?_ (isClosed_pairCondDy _ _)
    rintro _ ⟨d, hd, rfl⟩
    exact hτ ⟨d, hd⟩
  exact hcl (hsub ⟨⟨ψ, hψ⟩, rfl⟩) i

/-! ## From the phases back to the phase space -/

/-- One phase: the slice identity for `u = F(t)`, `v = G(t)` gives
`⟪(-∂ⱼΦ)(t, ·), u⟫ = ⟪Φ(t, ·), v⟫`. -/
theorem innerPair_sliceMap_dy {P : ℝ} {q : ℝ≥0∞} [Fact (1 ≤ q)] {j : Fin 3}
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) (hs : IsSliceTest P (conjExp q) Φ)
    (hs' : IsSliceTest P (conjExp q) (-dy j Φ)) (t : ℝ)
    (u v : Lp CVec3 q (volume : Measure Space))
    (h : ∀ ψ : Space → CVec3, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∫ y, dotL (fderiv ℝ ψ y (coordinateVector j)) (u y) = -∫ y, dotL (ψ y) (v y)) :
    innerPair q (sliceMap hs'.2 t) u = innerPair q (sliceMap hs.2 t) v := by
  have hd : Differentiable ℝ Φ := hΦ.smooth.differentiable (by simp)
  have hψs : ContDiff ℝ ∞ (fun z => Φ (t, z)) :=
    hΦ.smooth.comp (contDiff_const.prodMk contDiff_id)
  have key := h (fun z => Φ (t, z)) hψs (hΦ.hasCompactSupport_slice t)
  rw [innerPair_apply, innerPair_apply]
  have e1 : (fun y => dotL ((sliceMap hs'.2 t : Space → CVec3) y) (u y)) =ᵐ[volume]
      fun y => -dotL (fderiv ℝ (fun z => Φ (t, z)) y (coordinateVector j)) (u y) := by
    filter_upwards [MemLp.coeFn_toLp (hs'.2.memLp t)] with y hy
    simp only [sliceMap]
    rw [hy, Pi.neg_apply, B0428.dy_apply_slice hd j t y, map_neg]
    rfl
  have e2 : (fun y => dotL ((sliceMap hs.2 t : Space → CVec3) y) (v y)) =ᵐ[volume]
      fun y => dotL (Φ (t, y)) (v y) := by
    filter_upwards [MemLp.coeFn_toLp (hs.2.memLp t)] with y hy
    simp only [sliceMap]
    rw [hy]
  rw [integral_congr_ae e1, integral_congr_ae e2, integral_neg, key, neg_neg]

/-- The phase-space identity from the slice identities, for fixed `F, G`. -/
theorem hasPhaseOp_dy_of_ae {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)] {j : Fin 3}
    {F G : Yq P q}
    (h : ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)), ∀ ψ : Space → CVec3, ContDiff ℝ ∞ ψ →
      HasCompactSupport ψ →
        ∫ y, dotL (fderiv ℝ ψ y (coordinateVector j)) ((F τ : Space → CVec3) y) =
          -∫ y, dotL (ψ y) ((G τ : Space → CVec3) y)) :
    HasPhaseOp (fun Φ => -dy j Φ) F G := by
  intro Φ hΦ
  have hs : IsSliceTest P (conjExp q) Φ := hΦ.isSliceTest (conjExp q)
  have hs' : IsSliceTest P (conjExp q) (-dy j Φ) := ((hΦ.dy j).neg).isSliceTest (conjExp q)
  have e1 : phasePair P q (-dy j Φ) F =
      ∫ τ, innerPair q (circleSlice hs' τ) (F τ) ∂AddCircle.haarAddCircle := by
    rw [phasePair, phasePairing_apply, testElem_of hs']
    refine integral_congr_ae ?_
    filter_upwards [ContinuousMap.coeFn_toLp
      (E := Lp CVec3 (conjExp q) (volume : Measure Space))
      (p := conjExp q) (𝕜 := ℂ) AddCircle.haarAddCircle (circleSlice hs')] with τ h1
    rw [h1]
  have e2 : phasePair P q Φ G =
      ∫ τ, innerPair q (circleSlice hs τ) (G τ) ∂AddCircle.haarAddCircle := by
    rw [phasePair, phasePairing_apply, testElem_of hs]
    refine integral_congr_ae ?_
    filter_upwards [ContinuousMap.coeFn_toLp
      (E := Lp CVec3 (conjExp q) (volume : Measure Space))
      (p := conjExp q) (𝕜 := ℂ) AddCircle.haarAddCircle (circleSlice hs)] with τ h1
    rw [h1]
  show phasePair P q (-dy j Φ) F = phasePair P q Φ G
  rw [e1, e2]
  refine integral_congr_ae ?_
  filter_upwards [h] with τ hτ
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective τ
  rw [circleSlice_coe, circleSlice_coe]
  exact innerPair_sliceMap_dy hΦ hs hs' t _ _ hτ

/-- **Leaf `HasPhaseOpDyOfAe`.** -/
theorem hasPhaseOpDyOfAe : HasPhaseOpDyOfAe :=
  fun _ _ _ _ _ _ _ h => hasPhaseOp_dy_of_ae h

#print axioms aeSliceDy
#print axioms aeForallSliceDy
#print axioms hasPhaseOpDyOfAe

end UnforcedLeray.Short.IIb
