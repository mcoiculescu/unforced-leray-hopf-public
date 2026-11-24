import UnforcedLeray.Short.PartI.Sub.PartI_T20_1.Base
import UnforcedLeray.Short.PartI.Tasks.TrainFixedBandProof.VelAgeJet.HF_1_Aux
import UnforcedLeray.Short.PartI.Sub.T02_3

/-!
# `PartI:T20/1` (`Sub/PartI_T20_1.lean`): Momentum Age-Derivative Induction and Reduction to Pressure Step

Source of record: `the November 2 reference manuscript`, lines 483-526
("The equations now give the age derivatives by finite induction: each fluctuation equation retains
a fluctuation factor, and each differentiated vorticity equation retains a Gaussian vorticity
factor").

In `Tasks/TrainVorticityTail/AgeDeriv.lean`, `trainVorticityGaussianTailAt_succ` proves the inductive
step `ℓ → ℓ + 1` for the vorticity Gaussian tail `TrainVorticityGaussianTailAt (ℓ + 1)` from
`∀ r ≤ ℓ, TrainVorticityGaussianTailAt r` and `∀ r ≤ ℓ, TrainVelocityAgeJetSupBoundAt r`.

Here we prove the corresponding inductive step `ℓ → ℓ + 1` for the velocity age-jet sup bound
`TrainVelocityAgeJetSupBoundAt (ℓ + 1)` along the differentiated momentum equation
`∂_s v = ν Δv - (v · ∇)v - ∇p` (`ageJet_succ_vel_eq`, `norm_ageJet_succ_vel_le`):
1. **Vector norm reconstruction from coordinate projections (`PartI_T20_1.norm_ageJet_vec_le_add_proj`)**:
   for any jointly smooth vector field `V : ℝ → Plane → Vec`,
   `‖ageJet ℓ j V s z‖ ≤ ‖ageJet ℓ j (fun r w => V r w 0) s z‖ + ‖ageJet ℓ j (fun r w => V r w 1) s z‖`.
2. **Spacetime Leibniz bound for the nonlinear advection `Train.advection`
   (`PartI_T20_1.norm_ageJet_advection_le`)**:
   using `PartI_T20.norm_ageJet_mul_le`, if `‖ageJet r i V s z‖ ≤ M` for all `r ≤ ℓ` and
   `i ≤ j + 1`, then
   `‖ageJet ℓ j (fun r w => Train.advection (V r) w) s z‖ ≤ 4 * 2 ^ (ℓ + j) * M * M`.
   (As a corollary, `PartI_T20_1.trainVelAgeStepAdvFixed_proof` proves `TrainVelAgeStepAdvFixed`.)
3. **Spacetime Leibniz bound for the pressure Poisson source `poissonSource`
   (`PartI_T20_1.norm_ageJet_poissonSource_le`)**:
   under the same hypothesis `‖ageJet r i V s z‖ ≤ M` for `r ≤ ℓ` and `i ≤ j + 1`,
   `‖ageJet ℓ j (fun r w => poissonSource (V r) w) s z‖ ≤ 4 * 2 ^ (ℓ + j) * M * M`.
4. **Inductive step for velocity age-jets (`PartI_T20_1.trainVelocityAgeJetSupBoundAt_succ`) and
   simultaneous all-order strong induction (`PartI_T20_1.trainVorticityAndVelocityAgeJet_all`)**:
   reduces `TrainVorticityAgeDerivFromZero` (`PartI:T20/1`) via `trainVorticityAgeDerivFromZero_of_pressure`
   to the single elliptic cylinder-Poisson pressure leaf `TrainPressureAgeJetSupStep` (`PartI:T20/1/1`),
   which bounds `‖ageJet ℓ k tr.p s z‖ ≤ polyP C_p N_p ν c` at age order `ℓ` given `TrainOverlap`,
   `∀ r ≤ ℓ, TrainVorticityGaussianTailAt r`, and `∀ r ≤ ℓ, TrainVelocityAgeJetSupBoundAt r`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartI.VelAgeJetAux
open UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec toVec toVec_zero toVec_one jet)
open UnforcedLeray.Short.IIb (UU isOpen_UU mem_UU Sm vb_slice_contDiffAt)

/-- **Leaf (`PartI:T20/1/1`, `TrainPressureAgeJetSupStep`)**:
source lines 517-526 (and 483-516) of `the November 2 reference manuscript`.
Given `hOv : TrainOverlap` and the age-order `≤ ℓ` inductive hypotheses
`hVort : ∀ r ≤ ℓ, TrainVorticityGaussianTailAt r` and
`hVel : ∀ r ≤ ℓ, TrainVelocityAgeJetSupBoundAt r` (so all mixed jets `ageJet r i tr.v` up to age
order `ℓ` are bounded by `polyP C_v N_v ν c`, and hence by `PartI_T20_1.norm_ageJet_poissonSource_le`
all spatial jets of `∂_s^ℓ (poissonSource tr.v) = -Δ(∂_s^ℓ tr.p)` are bounded by `polyP`),
for every `ρ > 1/2` and spatial order `k : ℕ`, the pressure jet `ageJet ℓ k tr.p s z` at age order `ℓ`
is bounded on `s > 0` × `Plane` by `polyP C_p N_p ν (trainPeriod ρ ν)`.
Composed by `PartI:T20/1` via `trainVorticityAgeDerivFromZero_of_pressure`. -/
def TrainPressureAgeJetSupStep : Prop :=
  TrainOverlap →
    ∀ ℓ : ℕ,
      (∀ r ≤ ℓ, TrainVorticityGaussianTailAt r) →
      (∀ r ≤ ℓ, TrainVelocityAgeJetSupBoundAt r) →
      ∀ ρ : ℝ, 1 / 2 < ρ → ∀ k : ℕ,
        ∃ C_p : ℝ, ∃ N_p : ℕ, ∃ ν₀ : ℝ, 0 < C_p ∧ 0 < ν₀ ∧
          ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
            ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
              ∀ s : ℝ, 0 < s → ∀ z : Plane,
                ‖ageJet ℓ k tr.p s z‖ ≤ polyP C_p N_p ν (trainPeriod ρ ν)

namespace PartI_T20_1

/-! ### 1. Coordinate reconstruction of vector-valued `ageJet ℓ j` -/

/-- Coordinate injection `x ↦ x • single k 1` into `Vec = EuclideanSpace ℝ (Fin 2)`. -/
noncomputable def vecSingleCLM (k : Fin 2) : ℝ →L[ℝ] Vec :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single k (1 : ℝ))

theorem vecSingleCLM_apply (k : Fin 2) (x : ℝ) :
    vecSingleCLM k x = x • EuclideanSpace.single k (1 : ℝ) := rfl

theorem norm_vecSingleCLM_le_one (k : Fin 2) : ‖vecSingleCLM k‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [vecSingleCLM_apply, norm_smul, PiLp.norm_single, norm_one, mul_one, one_mul]

theorem vec_eq_sum_vecSingleCLM (v : Vec) :
    vecSingleCLM 0 (v 0) + vecSingleCLM 1 (v 1) = v := by
  ext i
  fin_cases i <;>
    simp [vecSingleCLM_apply, PiLp.add_apply, PiLp.smul_apply]

/-- For any smooth vector field `u : Plane → Vec`, `‖iteratedFDeriv ℝ j u z‖` is bounded by the sum
of the scalar `j`-jet norms of its two components `u · 0` and `u · 1`. -/
theorem norm_iteratedFDeriv_vec_le_add_proj {u : Plane → Vec} (hu : ContDiff ℝ ∞ u)
    (j : ℕ) (z : Plane) :
    ‖iteratedFDeriv ℝ j u z‖ ≤
      ‖iteratedFDeriv ℝ j (fun w => u w 0) z‖ + ‖iteratedFDeriv ℝ j (fun w => u w 1) z‖ := by
  let u₀ : Plane → ℝ := fun w => u w 0
  let u₁ : Plane → ℝ := fun w => u w 1
  have hu₀ : ContDiff ℝ ∞ u₀ :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hu
  have hu₁ : ContDiff ℝ ∞ u₁ :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hu
  have hF₀ : ContDiff ℝ ∞ (vecSingleCLM 0 ∘ u₀) := (vecSingleCLM 0).contDiff.comp hu₀
  have hF₁ : ContDiff ℝ ∞ (vecSingleCLM 1 ∘ u₁) := (vecSingleCLM 1).contDiff.comp hu₁
  have heq : u = (vecSingleCLM 0 ∘ u₀) + (vecSingleCLM 1 ∘ u₁) :=
    funext fun w => (vec_eq_sum_vecSingleCLM (u w)).symm
  have hc₀ : ContDiffAt ℝ j (vecSingleCLM 0 ∘ u₀) z :=
    (hF₀.of_le (by exact_mod_cast le_top)).contDiffAt
  have hc₁ : ContDiffAt ℝ j (vecSingleCLM 1 ∘ u₁) z :=
    (hF₁.of_le (by exact_mod_cast le_top)).contDiffAt
  have hadd : iteratedFDeriv ℝ j u z =
      iteratedFDeriv ℝ j (vecSingleCLM 0 ∘ u₀) z + iteratedFDeriv ℝ j (vecSingleCLM 1 ∘ u₁) z := by
    rw [heq]
    exact iteratedFDeriv_add_apply hc₀ hc₁
  have hb₀ : ‖iteratedFDeriv ℝ j (vecSingleCLM 0 ∘ u₀) z‖ ≤ ‖iteratedFDeriv ℝ j u₀ z‖ := by
    refine ((vecSingleCLM 0).norm_iteratedFDeriv_comp_left
      hu₀.contDiffAt (by exact_mod_cast le_top)).trans ?_
    exact (mul_le_mul_of_nonneg_right (norm_vecSingleCLM_le_one 0) (norm_nonneg _)).trans (by linarith)
  have hb₁ : ‖iteratedFDeriv ℝ j (vecSingleCLM 1 ∘ u₁) z‖ ≤ ‖iteratedFDeriv ℝ j u₁ z‖ := by
    refine ((vecSingleCLM 1).norm_iteratedFDeriv_comp_left
      hu₁.contDiffAt (by exact_mod_cast le_top)).trans ?_
    exact (mul_le_mul_of_nonneg_right (norm_vecSingleCLM_le_one 1) (norm_nonneg _)).trans (by linarith)
  rw [hadd]
  exact (norm_add_le _ _).trans (add_le_add hb₀ hb₁)

/-- For any jointly smooth vector family `V : ℝ → Plane → Vec`, `‖ageJet ℓ j V s z‖` is bounded by
the sum of the scalar age-jet norms of its two components `V r w 0` and `V r w 1`. -/
theorem norm_ageJet_vec_le_add_proj {V : ℝ → Plane → Vec}
    (hV : Sm (fun x : ℝ × Plane => V x.1 x.2))
    (ℓ j : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    ‖ageJet ℓ j V s z‖ ≤
      ‖ageJet ℓ j (fun r w => V r w 0) s z‖ + ‖ageJet ℓ j (fun r w => V r w 1) s z‖ := by
  have hu : ContDiff ℝ ∞ (fun w : Plane => iteratedDeriv ℓ (fun r => V r w) s) :=
    contDiff_slice_iteratedDeriv_of_contDiffOn V hV ℓ hs
  have hproj0 : (fun w : Plane => (iteratedDeriv ℓ (fun r => V r w) s) 0) =
      fun w => iteratedDeriv ℓ (fun r => V r w 0) s :=
    funext fun w => (PartI_T20.iteratedDeriv_vec_proj_eq hV 0 ℓ hs w).symm
  have hproj1 : (fun w : Plane => (iteratedDeriv ℓ (fun r => V r w) s) 1) =
      fun w => iteratedDeriv ℓ (fun r => V r w 1) s :=
    funext fun w => (PartI_T20.iteratedDeriv_vec_proj_eq hV 1 ℓ hs w).symm
  unfold ageJet jet
  have h := norm_iteratedFDeriv_vec_le_add_proj hu j z
  rwa [hproj0, hproj1] at h

/-! ### 2. Spacetime Leibniz bounds for `Train.advection` and `poissonSource` -/

theorem advection_apply_eq (u : Plane → Vec) (w : Plane) (k : Fin 2) :
    Train.advection u w k =
      u w 0 * Cyl.partialQ (fun x => u x k) w + u w 1 * Cyl.partialEta (fun x => u x k) w := by
  fin_cases k <;> simp [Train.advection, toVec_zero, toVec_one]

/-- Componentwise age-jet bound for `Train.advection (V r) w k`: if `‖ageJet r i V s z‖ ≤ M` for
all `r ≤ ℓ` and `i ≤ j + 1`, then
`‖ageJet ℓ j (fun r w => Train.advection (V r) w k) s z‖ ≤ 2 * 2 ^ (ℓ + j) * M * M`. -/
theorem norm_ageJet_advection_comp_le {V : ℝ → Plane → Vec}
    (hV : Sm (fun x : ℝ × Plane => V x.1 x.2)) (k : Fin 2)
    (ℓ j : ℕ) {s M : ℝ} (hs : 0 < s) (hM : 0 ≤ M) (z : Plane)
    (hbd : ∀ r ≤ ℓ, ∀ i ≤ j + 1, ‖ageJet r i V s z‖ ≤ M) :
    ‖ageJet ℓ j (fun r w => Train.advection (V r) w k) s z‖ ≤
      2 * (2 : ℝ) ^ (ℓ + j) * M * M := by
  have hsm_v0 : PartI_T20.SmR (fun x : ℝ × Plane => V x.1 x.2 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hV
  have hsm_v1 : PartI_T20.SmR (fun x : ℝ × Plane => V x.1 x.2 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hV
  have hsm_vk : PartI_T20.SmR (fun x : ℝ × Plane => V x.1 x.2 k) :=
    (EuclideanSpace.proj k : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hV
  have hsm_Q : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialQ (fun y => V x.1 y k) x.2) :=
    PartI_T20.smR_partialQ (F := fun r w => V r w k) hsm_vk
  have hsm_E : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialEta (fun y => V x.1 y k) x.2) :=
    PartI_T20.smR_partialEta (F := fun r w => V r w k) hsm_vk
  let A₀ : ℝ → Plane → ℝ := fun r w => V r w 0 * Cyl.partialQ (fun y => V r y k) w
  let A₁ : ℝ → Plane → ℝ := fun r w => V r w 1 * Cyl.partialEta (fun y => V r y k) w
  have hfun : (fun r w => Train.advection (V r) w k) = fun r w => A₀ r w + A₁ r w :=
    funext fun r => funext fun w => advection_apply_eq (V r) w k
  rw [hfun, PartI_T20.ageJet_add A₀ A₁ (hsm_v0.mul hsm_Q) (hsm_v1.mul hsm_E) hs ℓ j z]
  have hb₀ : ‖ageJet ℓ j A₀ s z‖ ≤ (2 : ℝ) ^ (ℓ + j) * M * M := by
    refine PartI_T20.norm_ageJet_mul_le hsm_v0 hsm_Q ℓ j hs hM hM z
      (fun r hr i hi => (PartI_T20.norm_ageJet_vec_proj_le hV 0 r i hs z).trans
        (hbd r hr i (by omega)))
      (fun r hr i hi =>
        ((PartI_T20.norm_ageJet_partialQ_le (F := fun t w => V t w k) hsm_vk r i hs z).trans
          (PartI_T20.norm_ageJet_vec_proj_le hV k r (i + 1) hs z)).trans
        (hbd r hr (i + 1) (by omega)))
  have hb₁ : ‖ageJet ℓ j A₁ s z‖ ≤ (2 : ℝ) ^ (ℓ + j) * M * M := by
    refine PartI_T20.norm_ageJet_mul_le hsm_v1 hsm_E ℓ j hs hM hM z
      (fun r hr i hi => (PartI_T20.norm_ageJet_vec_proj_le hV 1 r i hs z).trans
        (hbd r hr i (by omega)))
      (fun r hr i hi =>
        ((PartI_T20.norm_ageJet_partialEta_le (F := fun t w => V t w k) hsm_vk r i hs z).trans
          (PartI_T20.norm_ageJet_vec_proj_le hV k r (i + 1) hs z)).trans
        (hbd r hr (i + 1) (by omega)))
  calc ‖ageJet ℓ j A₀ s z + ageJet ℓ j A₁ s z‖
      ≤ ‖ageJet ℓ j A₀ s z‖ + ‖ageJet ℓ j A₁ s z‖ := norm_add_le _ _
    _ ≤ (2 : ℝ) ^ (ℓ + j) * M * M + (2 : ℝ) ^ (ℓ + j) * M * M := add_le_add hb₀ hb₁
    _ = 2 * (2 : ℝ) ^ (ℓ + j) * M * M := by ring

/-- **Spacetime Leibniz bound for `Train.advection` (`norm_ageJet_advection_le`)**:
for any jointly smooth `V : ℝ → Plane → Vec`, if `‖ageJet r i V s z‖ ≤ M` for all `r ≤ ℓ` and
`i ≤ j + 1` (`0 ≤ M`), then
`‖ageJet ℓ j (fun r w => Train.advection (V r) w) s z‖ ≤ 4 * 2 ^ (ℓ + j) * M * M`. -/
theorem norm_ageJet_advection_le {V : ℝ → Plane → Vec}
    (hV : Sm (fun x : ℝ × Plane => V x.1 x.2))
    (ℓ j : ℕ) {s M : ℝ} (hs : 0 < s) (hM : 0 ≤ M) (z : Plane)
    (hbd : ∀ r ≤ ℓ, ∀ i ≤ j + 1, ‖ageJet r i V s z‖ ≤ M) :
    ‖ageJet ℓ j (fun r w => Train.advection (V r) w) s z‖ ≤
      4 * (2 : ℝ) ^ (ℓ + j) * M * M := by
  have hsm_adv : Sm (fun x : ℝ × Plane => Train.advection (V x.1) x.2) :=
    PartI_T25_1.sm_advection hV
  have hvec := norm_ageJet_vec_le_add_proj (V := fun r w => Train.advection (V r) w) hsm_adv ℓ j hs z
  have h0 := norm_ageJet_advection_comp_le hV 0 ℓ j hs hM z hbd
  have h1 := norm_ageJet_advection_comp_le hV 1 ℓ j hs hM z hbd
  linarith

/-- Unconditional proof of `TrainVelAgeStepAdvFixed` (`PartI:HF/1/1`) as an immediate consequence
of `norm_ageJet_advection_le`. -/
theorem trainVelAgeStepAdvFixed_proof : TrainVelAgeStepAdvFixed := by
  intro ν c _hν _hc tr _htr ℓ hIH j
  have hrect : ∀ L : ℕ, (∀ r ≤ L, VelOrderBoundedFixed tr r) →
      ∀ K : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℝ, 0 < s → ∀ z : Plane,
        ∀ r ≤ L, ∀ i ≤ K, ‖ageJet r i tr.v s z‖ ≤ M := by
    intro L
    induction L with
    | zero =>
      intro hV K
      induction K with
      | zero =>
        obtain ⟨M₀, hM₀⟩ := hV 0 le_rfl 0
        refine ⟨max M₀ 0, le_max_right _ _, fun s hs z r hr i hi => ?_⟩
        have hr0 : r = 0 := Nat.le_zero.mp hr
        have hi0 : i = 0 := Nat.le_zero.mp hi
        subst hr0; subst hi0
        exact (hM₀ s hs z).trans (le_max_left _ _)
      | succ K ihK =>
        obtain ⟨M₁, hM₁_nn, hM₁⟩ := ihK
        obtain ⟨M₂, hM₂⟩ := hV 0 le_rfl (K + 1)
        refine ⟨max M₁ M₂, hM₁_nn.trans (le_max_left _ _), fun s hs z r hr i hi => ?_⟩
        rcases Nat.of_le_succ hi with hiK | rfl
        · exact (hM₁ s hs z r hr i hiK).trans (le_max_left _ _)
        · have hr0 : r = 0 := Nat.le_zero.mp hr
          subst hr0
          exact (hM₂ s hs z).trans (le_max_right _ _)
    | succ L ihL =>
      intro hV K
      obtain ⟨M₁, hM₁_nn, hM₁⟩ := ihL (fun r hr => hV r (Nat.le_succ_of_le hr)) K
      -- bound at r = L + 1 across i ≤ K
      have hL1 : ∃ M₂ : ℝ, 0 ≤ M₂ ∧ ∀ s : ℝ, 0 < s → ∀ z : Plane,
          ∀ i ≤ K, ‖ageJet (L + 1) i tr.v s z‖ ≤ M₂ := by
        clear ihL hM₁ M₁ hM₁_nn
        induction K with
        | zero =>
          obtain ⟨M₀, hM₀⟩ := hV (L + 1) le_rfl 0
          refine ⟨max M₀ 0, le_max_right _ _, fun s hs z i hi => ?_⟩
          have hi0 : i = 0 := Nat.le_zero.mp hi
          subst hi0
          exact (hM₀ s hs z).trans (le_max_left _ _)
        | succ K ihK =>
          obtain ⟨M_a, hMa_nn, hMa⟩ := ihK
          obtain ⟨M_b, hMb⟩ := hV (L + 1) le_rfl (K + 1)
          refine ⟨max M_a M_b, hMa_nn.trans (le_max_left _ _), fun s hs z i hi => ?_⟩
          rcases Nat.of_le_succ hi with hiK | rfl
          · exact (hMa s hs z i hiK).trans (le_max_left _ _)
          · exact (hMb s hs z).trans (le_max_right _ _)
      obtain ⟨M₂, _hM₂_nn, hM₂⟩ := hL1
      refine ⟨max M₁ M₂, hM₁_nn.trans (le_max_left _ _), fun s hs z r hr i hi => ?_⟩
      rcases Nat.of_le_succ hr with hrL | rfl
      · exact (hM₁ s hs z r hrL i hi).trans (le_max_left _ _)
      · exact (hM₂ s hs z i hi).trans (le_max_right _ _)
  obtain ⟨M, hM_nn, hbd⟩ := hrect ℓ hIH (j + 1)
  have hsm_v : Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (Set.prod_mono Set.Ioi_subset_Ici_self Subset.rfl)
  refine ⟨4 * (2 : ℝ) ^ (ℓ + j) * M * M, fun s hs z => ?_⟩
  exact norm_ageJet_advection_le hsm_v ℓ j hs hM_nn z (fun r hr i hi => hbd s hs z r hr i hi)

/-- Joint smoothness of `(r, w) ↦ poissonSource (V r) w` on `UU = Ioi 0 ×ˢ univ`. -/
theorem smR_poissonSource {V : ℝ → Plane → Vec}
    (hV : Sm (fun x : ℝ × Plane => V x.1 x.2)) :
    PartI_T20.SmR (fun x : ℝ × Plane => poissonSource (V x.1) x.2) := by
  have hsm_v0 : PartI_T20.SmR (fun x : ℝ × Plane => V x.1 x.2 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hV
  have hsm_v1 : PartI_T20.SmR (fun x : ℝ × Plane => V x.1 x.2 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hV
  have hQ0 : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialQ (fun w => V x.1 w 0) x.2) :=
    PartI_T20.smR_partialQ (F := fun r w => V r w 0) hsm_v0
  have hQ1 : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialQ (fun w => V x.1 w 1) x.2) :=
    PartI_T20.smR_partialQ (F := fun r w => V r w 1) hsm_v1
  have hE0 : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialEta (fun w => V x.1 w 0) x.2) :=
    PartI_T20.smR_partialEta (F := fun r w => V r w 0) hsm_v0
  have hE1 : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialEta (fun w => V x.1 w 1) x.2) :=
    PartI_T20.smR_partialEta (F := fun r w => V r w 1) hsm_v1
  unfold poissonSource
  exact ((hQ0.pow 2).add (contDiffOn_const.mul (hQ1.mul hE0))).add (hE1.pow 2)

/-- **Spacetime Leibniz bound for `poissonSource` (`norm_ageJet_poissonSource_le`)**:
for any jointly smooth `V : ℝ → Plane → Vec`, if `‖ageJet r i V s z‖ ≤ M` for all `r ≤ ℓ` and
`i ≤ j + 1` (`0 ≤ M`), then
`‖ageJet ℓ j (fun r w => poissonSource (V r) w) s z‖ ≤ 4 * 2 ^ (ℓ + j) * M * M`. -/
theorem norm_ageJet_poissonSource_le {V : ℝ → Plane → Vec}
    (hV : Sm (fun x : ℝ × Plane => V x.1 x.2))
    (ℓ j : ℕ) {s M : ℝ} (hs : 0 < s) (hM : 0 ≤ M) (z : Plane)
    (hbd : ∀ r ≤ ℓ, ∀ i ≤ j + 1, ‖ageJet r i V s z‖ ≤ M) :
    ‖ageJet ℓ j (fun r w => poissonSource (V r) w) s z‖ ≤
      4 * (2 : ℝ) ^ (ℓ + j) * M * M := by
  have hsm_v0 : PartI_T20.SmR (fun x : ℝ × Plane => V x.1 x.2 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hV
  have hsm_v1 : PartI_T20.SmR (fun x : ℝ × Plane => V x.1 x.2 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn hV
  have hQ0 : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialQ (fun w => V x.1 w 0) x.2) :=
    PartI_T20.smR_partialQ (F := fun r w => V r w 0) hsm_v0
  have hQ1 : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialQ (fun w => V x.1 w 1) x.2) :=
    PartI_T20.smR_partialQ (F := fun r w => V r w 1) hsm_v1
  have hE0 : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialEta (fun w => V x.1 w 0) x.2) :=
    PartI_T20.smR_partialEta (F := fun r w => V r w 0) hsm_v0
  have hE1 : PartI_T20.SmR (fun x : ℝ × Plane => Cyl.partialEta (fun w => V x.1 w 1) x.2) :=
    PartI_T20.smR_partialEta (F := fun r w => V r w 1) hsm_v1
  let P₁ : ℝ → Plane → ℝ := fun r w =>
    Cyl.partialQ (fun y => V r y 0) w * Cyl.partialQ (fun y => V r y 0) w
  let P₂ : ℝ → Plane → ℝ := fun r w =>
    Cyl.partialQ (fun y => V r y 1) w * Cyl.partialEta (fun y => V r y 0) w
  let P₃ : ℝ → Plane → ℝ := fun r w =>
    Cyl.partialEta (fun y => V r y 1) w * Cyl.partialEta (fun y => V r y 1) w
  have hsm₁ : PartI_T20.SmR (fun x : ℝ × Plane => P₁ x.1 x.2) := hQ0.mul hQ0
  have hsm₂ : PartI_T20.SmR (fun x : ℝ × Plane => P₂ x.1 x.2) := hQ1.mul hE0
  have hsm₃ : PartI_T20.SmR (fun x : ℝ × Plane => P₃ x.1 x.2) := hE1.mul hE1
  have hfun : (fun r w => poissonSource (V r) w) =
      fun r w => (P₁ r w + (P₂ r w + P₂ r w)) + P₃ r w := by
    funext r w
    unfold poissonSource
    dsimp [P₁, P₂, P₃]
    ring
  have hadd1 := PartI_T20.ageJet_add (fun r w => P₁ r w + (P₂ r w + P₂ r w)) P₃
    (hsm₁.add (hsm₂.add hsm₂)) hsm₃ hs ℓ j z
  have hadd2 := PartI_T20.ageJet_add P₁ (fun r w => P₂ r w + P₂ r w)
    hsm₁ (hsm₂.add hsm₂) hs ℓ j z
  have hadd3 := PartI_T20.ageJet_add P₂ P₂ hsm₂ hsm₂ hs ℓ j z
  have hQ0_bd : ∀ r ≤ ℓ, ∀ i ≤ j,
      ‖ageJet r i (fun t w => Cyl.partialQ (fun y => V t y 0) w) s z‖ ≤ M := fun r hr i hi =>
    ((PartI_T20.norm_ageJet_partialQ_le (F := fun t w => V t w 0) hsm_v0 r i hs z).trans
      (PartI_T20.norm_ageJet_vec_proj_le hV 0 r (i + 1) hs z)).trans (hbd r hr (i + 1) (by omega))
  have hQ1_bd : ∀ r ≤ ℓ, ∀ i ≤ j,
      ‖ageJet r i (fun t w => Cyl.partialQ (fun y => V t y 1) w) s z‖ ≤ M := fun r hr i hi =>
    ((PartI_T20.norm_ageJet_partialQ_le (F := fun t w => V t w 1) hsm_v1 r i hs z).trans
      (PartI_T20.norm_ageJet_vec_proj_le hV 1 r (i + 1) hs z)).trans (hbd r hr (i + 1) (by omega))
  have hE0_bd : ∀ r ≤ ℓ, ∀ i ≤ j,
      ‖ageJet r i (fun t w => Cyl.partialEta (fun y => V t y 0) w) s z‖ ≤ M := fun r hr i hi =>
    ((PartI_T20.norm_ageJet_partialEta_le (F := fun t w => V t w 0) hsm_v0 r i hs z).trans
      (PartI_T20.norm_ageJet_vec_proj_le hV 0 r (i + 1) hs z)).trans (hbd r hr (i + 1) (by omega))
  have hE1_bd : ∀ r ≤ ℓ, ∀ i ≤ j,
      ‖ageJet r i (fun t w => Cyl.partialEta (fun y => V t y 1) w) s z‖ ≤ M := fun r hr i hi =>
    ((PartI_T20.norm_ageJet_partialEta_le (F := fun t w => V t w 1) hsm_v1 r i hs z).trans
      (PartI_T20.norm_ageJet_vec_proj_le hV 1 r (i + 1) hs z)).trans (hbd r hr (i + 1) (by omega))
  have hb₁ := PartI_T20.norm_ageJet_mul_le hQ0 hQ0 ℓ j hs hM hM z hQ0_bd hQ0_bd
  have hb₂ := PartI_T20.norm_ageJet_mul_le hQ1 hE0 ℓ j hs hM hM z hQ1_bd hE0_bd
  have hb₃ := PartI_T20.norm_ageJet_mul_le hE1 hE1 ℓ j hs hM hM z hE1_bd hE1_bd
  rw [hfun, hadd1, hadd2, hadd3]
  have htri1 := norm_add_le
    (ageJet ℓ j P₁ s z + (ageJet ℓ j P₂ s z + ageJet ℓ j P₂ s z)) (ageJet ℓ j P₃ s z)
  have htri2 := norm_add_le (ageJet ℓ j P₁ s z) (ageJet ℓ j P₂ s z + ageJet ℓ j P₂ s z)
  have htri3 := norm_add_le (ageJet ℓ j P₂ s z) (ageJet ℓ j P₂ s z)
  linarith

/-! ### 3. Inductive step `ℓ → ℓ + 1` for `TrainVelocityAgeJetSupBoundAt` and simultaneous induction -/

/-- **Inductive step (`ℓ → ℓ + 1`) for `TrainVelocityAgeJetSupBoundAt`:**
given `hPress : TrainPressureAgeJetSupStep`, `hOv : TrainOverlap`,
`hVort : ∀ r ≤ ℓ, TrainVorticityGaussianTailAt r`, and
`hVel : ∀ r ≤ ℓ, TrainVelocityAgeJetSupBoundAt r`, differentiating the momentum equation
`∂_s v = ν Δv - (v · ∇)v - ∇p` proves `TrainVelocityAgeJetSupBoundAt (ℓ + 1)`. -/
theorem trainVelocityAgeJetSupBoundAt_succ
    (hPress : TrainPressureAgeJetSupStep)
    (hOv : TrainOverlap)
    (ℓ : ℕ)
    (hVort : ∀ r ≤ ℓ, TrainVorticityGaussianTailAt r)
    (hVel : ∀ r ≤ ℓ, TrainVelocityAgeJetSupBoundAt r) :
    TrainVelocityAgeJetSupBoundAt (ℓ + 1) := by
  intro ρ hρ k
  obtain ⟨C_V, N_V, ν_V, hC_V, hν_V, hV_bd⟩ :=
    PartI_T20.uniform_velocity_sup_rect hρ (k + 2) ℓ hVel
  obtain ⟨C_P, N_P, ν_P, hC_P, hν_P, hP_bd⟩ :=
    hPress hOv ℓ hVort hVel ρ hρ (k + 1)
  let C_out : ℝ := 2 * C_V + 4 * (2 : ℝ) ^ (ℓ + k) * C_V * C_V + 2 * C_P
  let N_out : ℕ := max (2 * N_V) N_P
  let ν_out : ℝ := min (min ν_V ν_P) 1
  refine ⟨C_out, N_out, ν_out,
    by dsimp [C_out]; positivity,
    lt_min (lt_min hν_V hν_P) one_pos, ?_⟩
  intro ν hν hν_le tr htr s hs z
  have hν_V_le : ν ≤ ν_V := hν_le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν_P_le : ν ≤ ν_P := hν_le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν1 : ν ≤ 1 := hν_le.trans (min_le_right _ _)
  let c := trainPeriod ρ ν
  have hc0 : 0 ≤ c := Real.rpow_nonneg hν.le _
  let M_V := polyP C_V N_V ν c
  let M_P := polyP C_P N_P ν c
  have hMV_nn : 0 ≤ M_V := by dsimp [M_V, polyP]; positivity
  have hsm_v : Sm (fun x : ℝ × Plane => tr.v x.1 x.2) :=
    tr.isTrain.smooth_v.mono (Set.prod_mono Set.Ioi_subset_Ici_self Subset.rfl)
  -- 1. Viscous term bound: `(2 * ν) * ‖ageJet ℓ (k + 2) tr.v s z‖ ≤ 2 * M_V`
  have hvisc : (2 * ν) * ‖ageJet ℓ (k + 2) tr.v s z‖ ≤ 2 * M_V := by
    calc (2 * ν) * ‖ageJet ℓ (k + 2) tr.v s z‖
        ≤ 2 * ‖ageJet ℓ (k + 2) tr.v s z‖ :=
          mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ ≤ 2 * M_V :=
          mul_le_mul_of_nonneg_left (hV_bd ν hν hν_V_le tr htr s hs z ℓ le_rfl (k + 2) le_rfl)
            (by norm_num)
  -- 2. Advection term bound: `‖ageJet ℓ k (advection tr.v) s z‖ ≤ 4 * 2^(ℓ + k) * M_V * M_V`
  have hadv : ‖ageJet ℓ k (fun r w => Train.advection (tr.v r) w) s z‖ ≤
      4 * (2 : ℝ) ^ (ℓ + k) * M_V * M_V :=
    norm_ageJet_advection_le hsm_v ℓ k hs hMV_nn z
      (fun r hr i hi => hV_bd ν hν hν_V_le tr htr s hs z r hr i (by omega))
  -- 3. Pressure gradient term bound: `‖ageJet ℓ k (gradS tr.p) s z‖ ≤ 2 * M_P`
  have hpress : ‖ageJet ℓ k (fun r w => Train.gradS (tr.p r) w) s z‖ ≤ 2 * M_P := by
    calc ‖ageJet ℓ k (fun r w => Train.gradS (tr.p r) w) s z‖
        ≤ 2 * ‖ageJet ℓ (k + 1) tr.p s z‖ := norm_ageJet_gradS_tr_p_le tr ℓ k hs z
      _ ≤ 2 * M_P :=
          mul_le_mul_of_nonneg_left (hP_bd ν hν hν_P_le tr htr s hs z) (by norm_num)
  -- 4. Combine the three terms
  have htri := norm_ageJet_succ_vel_le tr hν.le ℓ k hs z
  have hX1 : 1 ≤ 1 + c + ν⁻¹ := by
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    linarith
  have hpow_V1 : (1 + c + ν⁻¹) ^ N_V ≤ (1 + c + ν⁻¹) ^ N_out :=
    pow_le_pow_right₀ hX1 ((Nat.le_mul_of_pos_left N_V two_pos).trans (le_max_left _ _))
  have hpow_V2 : (1 + c + ν⁻¹) ^ (2 * N_V) ≤ (1 + c + ν⁻¹) ^ N_out :=
    pow_le_pow_right₀ hX1 (le_max_left _ _)
  have hpow_P : (1 + c + ν⁻¹) ^ N_P ≤ (1 + c + ν⁻¹) ^ N_out :=
    pow_le_pow_right₀ hX1 (le_max_right _ _)
  have hcomb : 2 * M_V + 4 * (2 : ℝ) ^ (ℓ + k) * M_V * M_V + 2 * M_P ≤
      polyP C_out N_out ν c := by
    dsimp [M_V, M_P, C_out, polyP]
    have hmul_V : (1 + c + ν⁻¹) ^ N_V * (1 + c + ν⁻¹) ^ N_V = (1 + c + ν⁻¹) ^ (2 * N_V) := by
      rw [two_mul, pow_add]
    have h1 : 2 * (C_V * (1 + c + ν⁻¹) ^ N_V) ≤ 2 * C_V * (1 + c + ν⁻¹) ^ N_out := by
      nlinarith [mul_le_mul_of_nonneg_left hpow_V1 (by positivity : 0 ≤ 2 * C_V)]
    have h2 : 4 * (2 : ℝ) ^ (ℓ + k) * (C_V * (1 + c + ν⁻¹) ^ N_V) * (C_V * (1 + c + ν⁻¹) ^ N_V) ≤
        4 * (2 : ℝ) ^ (ℓ + k) * C_V * C_V * (1 + c + ν⁻¹) ^ N_out := by
      calc 4 * (2 : ℝ) ^ (ℓ + k) * (C_V * (1 + c + ν⁻¹) ^ N_V) * (C_V * (1 + c + ν⁻¹) ^ N_V)
          = 4 * (2 : ℝ) ^ (ℓ + k) * C_V * C_V * ((1 + c + ν⁻¹) ^ N_V * (1 + c + ν⁻¹) ^ N_V) := by ring
        _ = 4 * (2 : ℝ) ^ (ℓ + k) * C_V * C_V * (1 + c + ν⁻¹) ^ (2 * N_V) := by rw [hmul_V]
        _ ≤ 4 * (2 : ℝ) ^ (ℓ + k) * C_V * C_V * (1 + c + ν⁻¹) ^ N_out :=
            mul_le_mul_of_nonneg_left hpow_V2 (by positivity)
    have h3 : 2 * (C_P * (1 + c + ν⁻¹) ^ N_P) ≤ 2 * C_P * (1 + c + ν⁻¹) ^ N_out := by
      nlinarith [mul_le_mul_of_nonneg_left hpow_P (by positivity : 0 ≤ 2 * C_P)]
    linarith
  exact htri.trans ((add_le_add (add_le_add hvisc hadv) hpress).trans hcomb)

/-- **Simultaneous all-order strong induction (`trainVorticityAndVelocityAgeJet_all`)**:
from `hPress : TrainPressureAgeJetSupStep`, `hOv : TrainOverlap`, and
`hSpatial : TrainVorticitySpatialJetTail`, proves both `TrainVorticityGaussianTailAt ℓ` and
`TrainVelocityAgeJetSupBoundAt ℓ` for every `ℓ : ℕ`. -/
theorem trainVorticityAndVelocityAgeJet_all
    (hPress : TrainPressureAgeJetSupStep)
    (hOv : TrainOverlap)
    (hSpatial : TrainVorticitySpatialJetTail) :
    ∀ ℓ : ℕ, TrainVorticityGaussianTailAt ℓ ∧ TrainVelocityAgeJetSupBoundAt ℓ := by
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      exact ⟨trainVorticityGaussianTailAt_zero hSpatial,
        trainVelocityAgeJetSupBoundAt_zero hOv⟩
    | succ m =>
      have hVort_m : ∀ r ≤ m, TrainVorticityGaussianTailAt r :=
        fun r hr => (ih r (Nat.lt_succ_of_le hr)).1
      have hVel_m : ∀ r ≤ m, TrainVelocityAgeJetSupBoundAt r :=
        fun r hr => (ih r (Nat.lt_succ_of_le hr)).2
      exact ⟨trainVorticityGaussianTailAt_succ m hVort_m hVel_m,
        trainVelocityAgeJetSupBoundAt_succ hPress hOv m hVort_m hVel_m⟩

end PartI_T20_1

/-- **Conditional assembly of `TrainVorticityAgeDerivFromZero` (`PartI:T20/1`)** from the single
cylinder-Poisson pressure leaf `TrainPressureAgeJetSupStep` (`PartI:T20/1/1`). -/
theorem trainVorticityAgeDerivFromZero_of_pressure
    (hPress : TrainPressureAgeJetSupStep) :
    TrainVorticityAgeDerivFromZero := by
  intro hOv hSpatial ρ hρ ℓ j
  exact (PartI_T20_1.trainVorticityAndVelocityAgeJet_all hPress hOv hSpatial ℓ).1 ρ hρ j

end UnforcedLeray.Short.PartI.VelAgeJetAux

end
