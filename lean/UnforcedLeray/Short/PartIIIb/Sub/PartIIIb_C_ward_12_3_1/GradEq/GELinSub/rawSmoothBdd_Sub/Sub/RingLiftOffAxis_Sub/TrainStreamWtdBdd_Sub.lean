import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Sub.RingLiftOffAxis_Sub
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations

/-!
# Decomposition of `TrainStreamWtdBdd` (SP 439-467 at the fixed parameters of SP 427-435)

Source of record: `the November 2 reference manuscript`.
With `L(s, q, η) = (s, η)` and `S = meanStream`: `ψ = S ∘ L + ψ̃`.  Two leaf Props, both at one
threshold `ν₀` for `ρ > 1/2` and every age bound `S`:

* `TrainFluctWtdBdd` (SP 440-445, `sct:fluctuation` with weights `⟨η⟩^m`: `≤ P e^{-κνs/c²} ≤ P`
  at every age `s > 0`);
* `TrainMeanWtdBdd` (SP 456-457, `‖η^m ∂_η^b ∂_s^ℓ S(s)‖_∞ ≤ P (1+s)^{(m-b-1)/2-ℓ}`, `s ≥ 0`, in the
  joint derivative form on `0 < s ≤ S`).

`trainStreamWtdBdd_of` is the calculus assembly (split, composition with `L`, `‖L‖ ≤ 1`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open Set Filter Topology
open scoped ContDiff

/-- **Weighted fluctuation bound at bounded ages, fixed parameters** (SP 440-445). -/
def TrainFluctWtdBdd : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν c : ℝ, 0 < ν → ν ≤ ν₀ →
    c = Short.PartI.trainPeriod ρ ν →
    ∀ tr : B0140.TrainSol ν c, Short.PartI.IsBUCTrain tr →
      ∀ (m i : ℕ) (S : ℝ), ∃ C : ℝ, ∀ y : ℝ × (ℝ × ℝ), 0 < y.1 → y.1 ≤ S →
        (1 + |y.2.2|) ^ m *
          ‖iteratedFDeriv ℝ i
            (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2 - Short.PartI.meanStream tr x.1 x.2.2) y‖ ≤ C

/-- **Weighted mean-stream bound at bounded ages, fixed parameters** (SP 456-457, joint form). -/
def TrainMeanWtdBdd : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν c : ℝ, 0 < ν → ν ≤ ν₀ →
    c = Short.PartI.trainPeriod ρ ν →
    ∀ tr : B0140.TrainSol ν c, Short.PartI.IsBUCTrain tr →
      ∀ (m i : ℕ) (S : ℝ), ∃ C : ℝ, ∀ y : ℝ × ℝ, 0 < y.1 → y.1 ≤ S →
        (1 + |y.2|) ^ m *
          ‖iteratedFDeriv ℝ i (fun x : ℝ × ℝ => Short.PartI.meanStream tr x.1 x.2) y‖ ≤ C

theorem trainStreamWtdBdd_of (hF : TrainFluctWtdBdd) (hM : TrainMeanWtdBdd) :
    TrainStreamWtdBdd := by
  intro ρ hρ
  obtain ⟨νF, hνF, hF'⟩ := hF ρ hρ
  obtain ⟨νM, hνM, hM'⟩ := hM ρ hρ
  refine ⟨min νF νM, lt_min hνF hνM, fun ν c hν hle hc tr htr m i S => ?_⟩
  obtain ⟨C1, hC1⟩ := hF' ν c hν (hle.trans (min_le_left _ _)) hc tr htr m i S
  obtain ⟨C2, hC2⟩ := hM' ν c hν (hle.trans (min_le_right _ _)) hc tr htr m i S
  have hc0 : 0 < c := by subst hc; exact Real.rpow_pos_of_pos hν _
  set U : Set (ℝ × (ℝ × ℝ)) := Ioi 0 ×ˢ univ with hUdef
  set U2 : Set (ℝ × ℝ) := Ioi 0 ×ˢ univ with hU2def
  have hUo : IsOpen U := isOpen_Ioi.prod isOpen_univ
  have hU2o : IsOpen U2 := isOpen_Ioi.prod isOpen_univ
  let L : ℝ × (ℝ × ℝ) →L[ℝ] ℝ × ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
  have hL : ∀ x, L x = (x.1, x.2.2) := fun x => rfl
  have hLnorm : ‖L‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => ?_)
    rw [hL, one_mul, Prod.norm_def, Prod.norm_def]
    simp only [Prod.norm_def]
    exact max_le (le_max_left _ _) ((le_max_right _ _).trans' (le_max_right _ _))
  have hLmaps : MapsTo L U U2 := fun x hx => by
    simp only [hL, hUdef, hU2def, mem_prod, mem_Ioi, mem_univ, and_true] at hx ⊢
    exact hx
  have hpre : L ⁻¹' U2 = U := by
    ext x
    simp only [hL, hUdef, hU2def, mem_preimage, mem_prod, mem_Ioi, mem_univ, and_true]
  have hψ : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2) U :=
    Short.PartI.trainStreamSmooth ν _ hν hc0 tr htr
  have hmean : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => Short.PartI.meanStream tr x.1 x.2) U2 :=
    (Short.PartI.trainMeanEquations_proof ν _ hν hc0 tr htr).1
  have hf1 : ContDiffOn ℝ ∞
      ((fun x : ℝ × ℝ => Short.PartI.meanStream tr x.1 x.2) ∘ L) U :=
    hmean.comp L.contDiff.contDiffOn (hpre ▸ subset_rfl : U ⊆ L ⁻¹' U2)
  have hf2 : ContDiffOn ℝ ∞
      (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2 - Short.PartI.meanStream tr x.1 x.2.2) U :=
    hψ.sub hf1
  have hsplit : (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2) =
      ((fun x : ℝ × ℝ => Short.PartI.meanStream tr x.1 x.2) ∘ L) +
        (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2 - Short.PartI.meanStream tr x.1 x.2.2) := by
    funext y
    simp only [Pi.add_apply, Function.comp_apply, hL]
    ring
  refine ⟨C1 + C2, fun y hy0 hyS => ?_⟩
  have hyU : y ∈ U := by
    simp only [hUdef, mem_prod, mem_Ioi, mem_univ, and_true]; exact hy0
  have hyU2 : L y ∈ U2 := hLmaps hyU
  rw [hsplit, ← iteratedFDerivWithin_of_isOpen i hUo hyU,
    iteratedFDerivWithin_add_apply
      ((hf1.contDiffWithinAt hyU).of_le (by exact_mod_cast le_top))
      ((hf2.contDiffWithinAt hyU).of_le (by exact_mod_cast le_top)) hUo.uniqueDiffOn hyU]
  have hcomp := L.iteratedFDerivWithin_comp_right hmean hU2o.uniqueDiffOn
    (hpre ▸ hUo.uniqueDiffOn) hyU2 (i := i) (by exact_mod_cast le_top)
  rw [hpre] at hcomp
  rw [hcomp, iteratedFDerivWithin_of_isOpen i hUo hyU,
    iteratedFDerivWithin_of_isOpen i hU2o hyU2]
  have hw : 0 ≤ (1 + |y.2.2|) ^ m := by positivity
  have hA : ‖(iteratedFDeriv ℝ i
      (fun x : ℝ × ℝ => Short.PartI.meanStream tr x.1 x.2) (L y)).compContinuousLinearMap
        fun _ => L‖ ≤ ‖iteratedFDeriv ℝ i
      (fun x : ℝ × ℝ => Short.PartI.meanStream tr x.1 x.2) (L y)‖ := by
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have h1 : ∏ _i : Fin i, ‖L‖ ≤ 1 := by
      rw [Finset.prod_const]
      exact pow_le_one₀ (norm_nonneg _) hLnorm
    exact (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)).trans (le_of_eq (mul_one _))
  have h2 := hC2 (L y) (by simpa [hL] using hy0) (by simpa [hL] using hyS)
  have h1 := hC1 y hy0 hyS
  simp only [hL] at h2
  have hsum := (norm_add_le
    ((iteratedFDeriv ℝ i (fun x : ℝ × ℝ => Short.PartI.meanStream tr x.1 x.2) (L y)).compContinuousLinearMap
      fun _ => L)
    (iteratedFDeriv ℝ i
      (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2 - Short.PartI.meanStream tr x.1 x.2.2) y))
  have hA' := hA.trans_eq' rfl
  have h3 : (1 + |y.2.2|) ^ m * ‖iteratedFDeriv ℝ i
      (fun x : ℝ × ℝ => Short.PartI.meanStream tr x.1 x.2) (L y)‖ ≤ C2 := by
    simpa [hL] using h2
  calc _ ≤ (1 + |y.2.2|) ^ m * (‖iteratedFDeriv ℝ i
      (fun x : ℝ × ℝ => Short.PartI.meanStream tr x.1 x.2) (L y)‖ + ‖iteratedFDeriv ℝ i
      (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2 - Short.PartI.meanStream tr x.1 x.2.2) y‖) :=
        mul_le_mul_of_nonneg_left (hsum.trans (add_le_add hA le_rfl)) hw
    _ ≤ C1 + C2 := by rw [mul_add]; linarith

end UnforcedLeray.Short.PartIIIb.Concrete
