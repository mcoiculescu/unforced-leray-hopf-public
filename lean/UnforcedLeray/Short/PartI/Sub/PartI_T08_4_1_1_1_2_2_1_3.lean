import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_1_1_2_2_1

/-!
# Part I, task `PartI:T08/4/1/1/1/2/2/1/3` (`VelZeroUniformL2`): decomposition

Source: `the November 2 reference manuscript` lines 261-288.

`velZeroUniformL2_of` derives the uniform `L²(cell)` bound on the velocity of a `BUC` train on
`[0, S]` from two source leaves:

* `TrainPressureBounded` (line 273-275: "the bounded periodic pressure choice");
* `VelCutoffEnergyIneq` (lines 286-287: "approximation and transverse cutoffs give the velocity
  energy identity"; with the bounded pressure and the `BUC` bound the cutoff energy has bounded
  derivative);

together with the proved `cutoffGronwall_proof` and the leaf `CutoffL2BoundQ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-- The transverse-cutoff velocity energy `s ↦ ∫_cell χ_R |v(s)|²`. -/
def velCutoffEnergy {ν c : ℝ} (tr : B0140.TrainSol ν c) (R s : ℝ) : ℝ :=
  ∫ z in Cyl.cell c, etaCutoff R z.2 * ‖tr.v s z‖ ^ 2

/-- Leaf (source lines 273-275, Gallay-Slijepcevic Theorem 1.1 / Remark 1.3(2)): the periodic
pressure of a `BUC` train, fixed by decay, is bounded on `[0, S] × ℝ²`.  (Pressure is the
`c`-periodic, `η`-decaying solution of `-Δp = ∂_i∂_j (v_i v_j)` with bounded right side.) -/
def TrainPressureBounded : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr →
    ∀ S : ℝ, 0 < S → ∃ P : ℝ, ∀ r ∈ Icc (0 : ℝ) S, ∀ z : Plane, |tr.p r z| ≤ P

/-- Leaf (source lines 286-287, velocity energy identity with transverse cutoffs).  For a `BUC`
train with pressure bounded by `P` on `[0, S]`, there is `C ≥ 0` such that for every `R ≥ 1` the
cutoff energy `E_R = velCutoffEnergy tr R` is continuous on `[0, S]` and at every `s ∈ (0, S)` has
a derivative `D ≤ C`.
Derivation: `∂_s v = νΔv - v·∇v - ∇p`, so `E_R' = -2ν∫χ|∇v|² - 2ν∫ ∂_ηχ v·∂_ηv
+ ∫ ∂_ηχ v_η |v|² + 2∫ ∂_ηχ p v_η`, using `div v = 0`, periodicity in `q`, and `∂_ηχ` supported
in `R ≤ |η| ≤ 2R` (area `2Rc`), `|∂_ηχ| ≤ C₀/R`; each remaining term is `≤ K c (M² + M³ + P M)`.
Continuity and differentiation under the integral as in `Sub/PartI_T08_2_2/EnergyIneq.lean`. -/
def VelCutoffEnergyIneq : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr →
    ∀ S : ℝ, 0 < S → ∀ P : ℝ, (∀ r ∈ Icc (0 : ℝ) S, ∀ z : Plane, |tr.p r z| ≤ P) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
        ContinuousOn (velCutoffEnergy tr R) (Icc 0 S) ∧
        ∀ s ∈ Ioo (0 : ℝ) S, ∃ D : ℝ, HasDerivAt (velCutoffEnergy tr R) D s ∧ D ≤ C

theorem vcu_normsq_cont {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s) :
    Continuous (fun z : Plane => ‖tr.v s z‖ ^ 2) :=
  ((TrainErrorEquation.contDiff_slice tr.isTrain.smooth_v hs).continuous.norm).pow 2

theorem vcu_comp_le_normsq {ν c : ℝ} (tr : B0140.TrainSol ν c) (s : ℝ) (z : Plane) (k : Fin 2) :
    (tr.v s z k) ^ 2 ≤ ‖tr.v s z‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  have := Finset.single_le_sum (f := fun i : Fin 2 => ‖tr.v s z i‖ ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ k)
  simpa [Real.norm_eq_abs, sq_abs] using this

/-- **`VelZeroUniformL2` from the leaves.** -/
theorem velZeroUniformL2_of (hp : TrainPressureBounded) (he : VelCutoffEnergyIneq)
    (hq : CutoffL2BoundQ) : VelZeroUniformL2 := by
  intro ν c hν hc tr htr S hS k
  have hc0 : 0 < c := by linarith
  obtain ⟨P, hP⟩ := hp ν c hν hc tr htr S hS
  obtain ⟨C, hC, hE⟩ := he ν c hν hc tr htr S hS P hP
  have hint0 : Integrable (fun z => ‖tr.v 0 z‖ ^ 2) (volume.restrict (Cyl.cell c)) :=
    tr.isTrain.finite_energy 0 le_rfl
  set D0 := ∫ z in Cyl.cell c, ‖tr.v 0 z‖ ^ 2 with hD0
  have hD0nn : 0 ≤ D0 := integral_nonneg (fun z => sq_nonneg _)
  refine ⟨(D0 + 1) * Real.exp (C * S), fun s hs0 hsS => ?_⟩
  have hbound : ∀ R : ℝ, 1 ≤ R →
      ∫ z in Cyl.cell c, etaCutoff R z.2 * (tr.v s z k) ^ 2 ≤ (D0 + 1) * Real.exp (C * S) := by
    intro R hR
    have hR0 : 0 < R := by linarith
    obtain ⟨hcont, hder⟩ := hE R hR
    have hnn : ∀ t, 0 ≤ velCutoffEnergy tr R t := fun t =>
      integral_nonneg (fun z => mul_nonneg (etaCutoff_nonneg R z.2) (sq_nonneg _))
    have hder' : ∀ t ∈ Ioo (0 : ℝ) S, ∃ D : ℝ, HasDerivAt (velCutoffEnergy tr R) D t ∧
        D ≤ C * velCutoffEnergy tr R t + C := by
      intro t ht
      obtain ⟨D, hD, hDC⟩ := hder t ht
      refine ⟨D, hD, ?_⟩
      have := mul_nonneg hC (hnn t)
      linarith
    have hG := cutoffGronwall_proof (velCutoffEnergy tr R) S C hS hC hcont hder' s ⟨hs0, hsS⟩
    have hz : velCutoffEnergy tr R 0 ≤ D0 := by
      unfold velCutoffEnergy
      apply integral_mono_of_nonneg _ hint0
      · refine Filter.Eventually.of_forall (fun z => ?_)
        have h := cehd_eta_le_one R z.2
        have h' := etaCutoff_nonneg R z.2
        have h2 : 0 ≤ ‖tr.v 0 z‖ ^ 2 := sq_nonneg _
        show etaCutoff R z.2 * ‖tr.v 0 z‖ ^ 2 ≤ ‖tr.v 0 z‖ ^ 2
        nlinarith
      · exact Filter.Eventually.of_forall (fun z =>
          mul_nonneg (etaCutoff_nonneg R z.2) (sq_nonneg _))
    have hexp : Real.exp (C * s) ≤ Real.exp (C * S) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hsS hC)
    have hexp0 : 0 < Real.exp (C * s) := Real.exp_pos _
    have hFs : velCutoffEnergy tr R s ≤ (D0 + 1) * Real.exp (C * S) :=
      calc velCutoffEnergy tr R s ≤ (velCutoffEnergy tr R 0 + 1) * Real.exp (C * s) := hG
        _ ≤ (D0 + 1) * Real.exp (C * s) :=
            mul_le_mul_of_nonneg_right (by linarith) hexp0.le
        _ ≤ (D0 + 1) * Real.exp (C * S) := mul_le_mul_of_nonneg_left hexp (by linarith)
    have hle : ∫ z in Cyl.cell c, etaCutoff R z.2 * (tr.v s z k) ^ 2 ≤ velCutoffEnergy tr R s := by
      unfold velCutoffEnergy
      have hkc : Continuous (fun z : Plane => (tr.v s z k) ^ 2) :=
        (vjl_slice_smooth tr hs0 k).continuous.pow 2
      refine integral_mono (vjl_cutoff_integrable hR0 hkc)
        (vjl_cutoff_integrable hR0 (vcu_normsq_cont tr hs0)) (fun z => ?_)
      exact mul_le_mul_of_nonneg_left (vcu_comp_le_normsq tr s z k) (etaCutoff_nonneg R z.2)
    exact hle.trans hFs
  have hk : Continuous (fun z : Plane => tr.v s z k) := (vjl_slice_smooth tr hs0 k).continuous
  exact (hq c _ (fun z => tr.v s z k) hc0 hk hbound).2

end UnforcedLeray.Short.PartI
