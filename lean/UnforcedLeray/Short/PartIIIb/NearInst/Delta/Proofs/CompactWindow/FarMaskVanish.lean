import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Sub.PartIIIb_C_near_delta_8
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.BoxDenseZ

/-!
# `FarMaskVanish` (item `PartIII-b:C/near/delta/8/1`)

Source `the November 2 reference manuscript`
3905-3916: on a box tensor supported in `t < e^δ l` the masked kernel vanishes at output ages
`s ≥ l` (the mask keeps only `t > e^δ s`); extend from the dense box class (`Masked.boxDenseZ`)
by continuity of `1_{bin} S_far 1_{t<e^δ l}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Cons.C03.Concrete

theorem fmv_nsSym_zero : nsSym (0 : Ten3) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nsSym, symRZ]

theorem fmv_sepW_zero (ν : ℝ) (μ : ℂ) (y : Space) (τ : ℝ) :
    UnforcedLeray.Short.IIIa.sepW ν μ (fun _ _ => (0 : Matrix (Fin 3) (Fin 3) ℝ)) y τ = 0 := by
  funext i
  simp [UnforcedLeray.Short.IIIa.sepW]

theorem fmv_merRe_zero : merRe (0 : Fin 3 → ℂ) = 0 := by
  ext i
  fin_cases i <;> simp [merRe]

/-- The far kernel of a tensor supported in `t < e^δ l` vanishes at output age `s ≥ l`. -/
theorem fmv_farOut_zero (R c ν μ δ S l : ℝ) (hδ : 0 ≤ δ) (f : Chart → Ten3)
    (hf : ∀ p : Chart, Real.exp δ * l ≤ p.1 → f p = 0) (x : Chart) (hx : l ≤ x.1) :
    Masked.farOut R c ν μ δ S f x = 0 := by
  unfold Masked.farOut
  split_ifs
  · have hc : (fun (τ' : ℝ) (z : Space) =>
        if Real.exp δ * x.1 < R ^ 2 / (z 0 ^ 2 + z 1 ^ 2) then cartLift R c f τ' z else 0) =
        fun _ _ => (0 : Matrix (Fin 3) (Fin 3) ℝ) := by
      funext τ' z
      split_ifs with h
      · have hs : (chartOf R c z τ').1 = R ^ 2 / (z 0 ^ 2 + z 1 ^ 2) := by
          simp only [chartOf, hRad]
          rw [Real.sq_sqrt (by positivity)]
        have hle : Real.exp δ * l ≤ (chartOf R c z τ').1 := by
          rw [hs]
          have : Real.exp δ * l ≤ Real.exp δ * x.1 :=
            mul_le_mul_of_nonneg_left hx (Real.exp_pos _).le
          linarith
        simp [cartLift, hf _ hle, fmv_nsSym_zero]
      · rfl
    have : sepWfar ν (μ : ℂ) R δ x.1 (cartLift R c f) (chartY R x) (chartTau R x) = 0 := by
      unfold sepWfar
      rw [hc]
      exact fmv_sepW_zero _ _ _ _
    rw [this, neg_zero, fmv_merRe_zero, smul_zero]
  · rfl

theorem farMaskVanish : FarMaskVanish := by
  intro c mZ ρb R ν μ δ S hc hmZ hρ Sf hSf l r L hl hδ
  set B : Set Chart := ageBelow (Real.exp δ * l) with hB
  have hBm : MeasurableSet B := measurableSet_ageBelow _
  set T : Zsp c mZ ρb →L[ℝ] Hsp c :=
    outRestr c (binSet l r L) ∘L Sf ∘L inRestr c mZ ρb B with hT
  have hac1 : ageμ c (-1 / 2) ≪ z1Measure c mZ :=
    Measure.absolutelyContinuous_of_le_smul (Masked.ageμ_le_z1Measure hmZ)
  have hac2 : ageμ c (-1 / 2) ≪ htRhoMeasure c ρb :=
    Measure.absolutelyContinuous_of_le_smul (Masked.ageμ_le_htRho hρ)
  -- vanishing on box inputs
  have hbox : ∀ (F : Zsp c mZ ρb) (f : Chart → Ten3), IsBoxTensor f →
      zsum F =ᵐ[ageμ c (-1 / 2)] f → T F = 0 := by
    intro F f hf hFf
    have hz : zsum (inRestr c mZ ρb B F) =ᵐ[ageμ c (-1 / 2)] B.indicator f := by
      have e1 := hac1 (restrLp_ae hBm (zEquiv c mZ ρb F).1)
      have e2 := hac2 (restrLp_ae hBm (zEquiv c mZ ρb F).2)
      filter_upwards [e1, e2, hFf] with p h1 h2 h3
      change ((restrLp (z1Measure c mZ) Ten3 B (zEquiv c mZ ρb F).1 : Z1sp c mZ) : Chart → Ten3) p +
        ((restrLp (htRhoMeasure c ρb) Ten3 B (zEquiv c mZ ρb F).2 : HTrho c ρb) : Chart → Ten3) p
        = B.indicator f p
      rw [h1, h2]
      have h3' : (F.fst : Chart → Ten3) p + (F.snd : Chart → Ten3) p = f p := h3
      by_cases hp : p ∈ B
      · have hind : ind B p = 1 := by simp [ind, hp]
        show ind B p • ((zEquiv c mZ ρb F).1 : Chart → Ten3) p + ind B p • ((zEquiv c mZ ρb F).2 : Chart → Ten3) p = _
        rw [hind, one_smul, one_smul]
        rw [Set.indicator_of_mem hp]
        exact h3'
      · have hind : ind B p = 0 := by simp [ind, hp]
        show ind B p • ((zEquiv c mZ ρb F).1 : Chart → Ten3) p + ind B p • ((zEquiv c mZ ρb F).2 : Chart → Ten3) p = _
        rw [hind, zero_smul, zero_smul, add_zero]
        exact (Set.indicator_of_notMem hp f).symm
    have hfar := hSf _ _ (Masked.IsBoxTensor.indicator hf hBm) hz
    have hfz : ∀ p : Chart, Real.exp δ * l ≤ p.1 → B.indicator f p = 0 := by
      intro p hp
      exact Set.indicator_of_notMem (by simpa [hB, ageBelow] using hp) f
    have hbm : MeasurableSet (binSet l r L) := measurableSet_binSet l r L
    rw [hT]
    simp only [ContinuousLinearMap.comp_apply]
    apply Lp.ext
    have hz0 := Lp.coeFn_zero (EuclideanSpace ℝ (Fin 2)) 2 (ageμ c (-3 / 2))
    have hr := restrLp_ae hbm (Sf (inRestr c mZ ρb B F))
    filter_upwards [hr, hfar, hz0] with x h1 h2 h0
    change ((outRestr c (binSet l r L) (Sf (inRestr c mZ ρb B F)) : Hsp c) : Chart → Merid) x = _
    unfold outRestr
    rw [h1, h0]
    change ind (binSet l r L) x • (Sf (inRestr c mZ ρb B F) : Chart → Merid) x = (0 : Merid)
    by_cases hx : x ∈ binSet l r L
    · rw [h2]
      have := fmv_farOut_zero R c ν μ δ S l hδ _ hfz x hx.1
      simp only [Masked.farOut] at this
      simp [this]
    · simp [ind, Set.indicator_of_notMem hx]
  -- continuity and density
  refine ContinuousLinearMap.ext fun F => ?_
  show T F = 0
  by_contra hne
  have hpos : 0 < ‖T F‖ := norm_pos_iff.2 (fun h => hne (by simpa using h))
  set η : ℝ := ‖T F‖ / (2 * (‖T‖ + 1)) with hη
  have hηpos : 0 < η := by positivity
  obtain ⟨F', ⟨f, hf, hFf⟩, hlt⟩ := Masked.boxDenseZ c mZ ρb hc hmZ hρ F η hηpos
  have h0 := hbox F' f hf hFf
  have : T F = T (F - F') := by rw [map_sub, h0, sub_zero]
  have hb : ‖T F‖ ≤ ‖T‖ * ‖F - F'‖ := by rw [this]; exact T.le_opNorm _
  have hT0 : 0 ≤ ‖T‖ := norm_nonneg _
  have : ‖T‖ * ‖F - F'‖ ≤ ‖T‖ * η := mul_le_mul_of_nonneg_left hlt.le hT0
  have h2 : ‖T‖ * η < ‖T F‖ := by
    rw [hη]
    have hd : 0 < 2 * (‖T‖ + 1) := by positivity
    rw [mul_div_assoc', div_lt_iff₀ hd]
    nlinarith
  linarith

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
