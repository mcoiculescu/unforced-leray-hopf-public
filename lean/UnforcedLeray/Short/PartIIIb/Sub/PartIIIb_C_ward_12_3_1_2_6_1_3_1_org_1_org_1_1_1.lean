import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_6_1_3_1_org_1_org_1_1
import UnforcedLeray.Short.PartI.Sub.PartI_TrainHeatFixed

/-!
# `PartIII-b:C/ward/12/3/1/2/6/1/3/1/org/1/org/1/1/1`: `TrainFluctWtdFixed`, decomposed

Source `the November 2 reference manuscript`
439-445 (`sct:fluctuation`, weight `<eta>^m`) at fixed parameters 427-435.

The single source leaf is the weighted age-jet decay `WeightedTrainFluctAgeJetFixed` (proof SP
516-526 with the weight). `trainFluctWtdFixed_of` is the calculus reduction: `JointFromAgeJets` is a
pointwise bound at `y`, so the weight `(1+|eta|)^m`, a constant at fixed `y`, passes through it.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.PartI
open UnforcedLeray.Cyl (Plane)

/-- **Source leaf: weighted age-jet decay of the stream fluctuation at fixed parameters**
(SP 439-445 with weight `<eta>^m`, proof SP 516-526, fixed parameters SP 427-435): for `rho > 1/2`
one `nu0`; for every BUC train with `nu <= nu0`, all `m, l, j` there are `C`, `kappa > 0` with
`(1+|eta|)^m || partial_s^l D^j (psi - S)(s, z) || <= C e^{-kappa s}` for all `s > 0` and `z`.
Weighted form of `PartI.TrainFluctAgeJetFixed`. -/
def WeightedTrainFluctAgeJetFixed : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
    ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr → ∀ m ℓ j : ℕ, ∃ C κ : ℝ, 0 < κ ∧
      ∀ s : ℝ, 0 < s → ∀ z : Plane,
        (1 + |z.2|) ^ m *
            ‖ageJet ℓ j (fun r w => tr.ψ r w - hmean (trainPeriod ρ ν) (tr.ψ r) w.2) s z‖ ≤
          C * Real.exp (-(κ * s))

/-- The weighted joint-derivative form from the weighted age jets. -/
theorem trainFluctWtdFixed_of (hS : TrainStreamSmooth) (hM : TrainMeanEquations)
    (hJ : JointFromAgeJets) (hL : WeightedTrainFluctAgeJetFixed) : TrainFluctWtdFixed := by
  intro ρ hρ
  obtain ⟨ν₀, hν₀, hL'⟩ := hL ρ hρ
  refine ⟨ν₀, hν₀, fun ν hν hle tr htr m i => ?_⟩
  have hc0 : 0 < trainPeriod ρ ν := Real.rpow_pos_of_pos hν _
  have hex : ∀ ℓ : ℕ, ∃ C κ : ℝ, 0 < κ ∧ ∀ s : ℝ, 0 < s → ∀ z : Plane,
      (1 + |z.2|) ^ m *
          ‖ageJet ℓ (i - ℓ) (fun r w => tr.ψ r w - hmean (trainPeriod ρ ν) (tr.ψ r) w.2) s z‖ ≤
        C * Real.exp (-(κ * s)) := fun ℓ => hL' ν hν hle tr htr m ℓ (i - ℓ)
  choose Cf κf hκf hbd using hex
  obtain ⟨K, hK0, hKj⟩ := hJ i
  set R := Finset.range (i + 1) with hR
  have hRne : R.Nonempty := ⟨0, by simp [hR]⟩
  set κ := R.inf' hRne κf with hκdef
  have hκ : 0 < κ := (Finset.lt_inf'_iff hRne).2 fun ℓ _ => hκf ℓ
  refine ⟨K * ∑ ℓ ∈ R, |Cf ℓ|, κ, hκ, fun y hy => ?_⟩
  -- smoothness
  set U : Set (ℝ × (ℝ × ℝ)) := Ioi 0 ×ˢ univ with hUdef
  set U2 : Set (ℝ × ℝ) := Ioi 0 ×ˢ univ with hU2def
  let L : ℝ × (ℝ × ℝ) →L[ℝ] ℝ × ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
  have hL : ∀ x, L x = (x.1, x.2.2) := fun x => rfl
  have hLmaps : MapsTo L U U2 := fun x hx => by
    simp only [hL, hUdef, hU2def, mem_prod, mem_Ioi, mem_univ, and_true] at hx ⊢
    exact hx
  have hψ : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2) U := hS ν _ hν hc0 tr htr
  have hmn : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanStream tr x.1 x.2) U2 :=
    (hM ν _ hν hc0 tr htr).1
  have hmeanL : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => meanStream tr x.1 x.2.2) U :=
    hmn.comp L.contDiff.contDiffOn hLmaps
  have hF : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) =>
      (fun r w => tr.ψ r w - hmean (trainPeriod ρ ν) (tr.ψ r) w.2) x.1 x.2) U := hψ.sub hmeanL
  have hy0 : 0 < y.1 := by linarith
  have hyU : y.1 ∈ Ioi (0:ℝ) := hy0
  have h1 := hKj (fun r w => tr.ψ r w - hmean (trainPeriod ρ ν) (tr.ψ r) w.2) hF y hy0
  have hw0 : 0 ≤ (1 + |y.2.2|) ^ m := by positivity
  have hexp : ∀ ℓ ∈ R, (1 + |y.2.2|) ^ m *
      ‖ageJet ℓ (i - ℓ) (fun r w => tr.ψ r w - hmean (trainPeriod ρ ν) (tr.ψ r) w.2) y.1 y.2‖ ≤
      |Cf ℓ| * Real.exp (-(κ * y.1)) := by
    intro ℓ hℓ
    have a := hbd ℓ y.1 hy0 y.2
    have hκl : κ ≤ κf ℓ := Finset.inf'_le _ hℓ
    have he : Real.exp (-(κf ℓ * y.1)) ≤ Real.exp (-(κ * y.1)) :=
      Real.exp_le_exp.2 (by nlinarith)
    calc _ ≤ Cf ℓ * Real.exp (-(κf ℓ * y.1)) := a
      _ ≤ |Cf ℓ| * Real.exp (-(κf ℓ * y.1)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
      _ ≤ _ := mul_le_mul_of_nonneg_left he (abs_nonneg _)
  calc (1 + |y.2.2|) ^ m * ‖iteratedFDeriv ℝ i
          (fun x : ℝ × (ℝ × ℝ) => tr.ψ x.1 x.2 - meanStream tr x.1 x.2.2) y‖
      ≤ (1 + |y.2.2|) ^ m * (K * ∑ ℓ ∈ R,
          ‖ageJet ℓ (i - ℓ) (fun r w => tr.ψ r w - hmean (trainPeriod ρ ν) (tr.ψ r) w.2)
            y.1 y.2‖) := mul_le_mul_of_nonneg_left h1 hw0
    _ = K * ∑ ℓ ∈ R, (1 + |y.2.2|) ^ m *
          ‖ageJet ℓ (i - ℓ) (fun r w => tr.ψ r w - hmean (trainPeriod ρ ν) (tr.ψ r) w.2)
            y.1 y.2‖ := by rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]; 
                           exact Finset.sum_congr rfl fun ℓ _ => by ring
    _ ≤ K * ∑ ℓ ∈ R, |Cf ℓ| * Real.exp (-(κ * y.1)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hexp) hK0
    _ = _ := by rw [← Finset.sum_mul]; ring

end UnforcedLeray.Short.PartIIIb.Concrete
