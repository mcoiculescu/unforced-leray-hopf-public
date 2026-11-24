import UnforcedLeray.Lib.TrainB.P0SmoothH3

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology
open UnforcedLeray.Cyl

namespace UnforcedLeray.TrainB

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

abbrev VecH3 (c : ℝ) := Cyl.H ℝ Vec2 c 0 3

/-- Sequential smooth cylinder approximation, with exact W.ofCylSmooth representatives. -/
theorem exists_smoothVecH3_sequence {c : ℝ} (hc : 0 < c) (x : VecH3 c) :
    ∃ xs : ℕ → VecH3 c, ∃ u : ℕ → Plane → Vec2,
      ∃ hu : ∀ n, Sob.IsCylSmooth c (u n),
        (∀ n, xs n = Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
          (𝕜 := ℝ) (F := Vec2) (k := 3) (p := 2) hc (u n) (hu n)) ∧
        Tendsto xs atTop (𝓝 x) := by
  obtain ⟨xs, hrep, hlim⟩ := Sob.W.exists_seq_cylSmooth
    (c := c) (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Vec2)
    (k := 3) (p := 2) hc (by norm_num) x
  choose u hu hae using hrep
  refine ⟨xs, u, hu, ?_, hlim⟩
  intro n
  apply Sob.W.value_injective
  apply Lp.ext
  have haeW := (Sob.ae_eq_wμ_iff (Sob.cylinder c).μ
    (Cyl.ρwW c ^ (0 : ℝ))).mpr (hae n)
  filter_upwards [haeW,
    Sob.W.value_ofCylSmooth (c := c) (ρ := Cyl.ρwW c ^ (0 : ℝ))
      (𝕜 := ℝ) (F := Vec2) (k := 3) (p := 2) hc (u n) (hu n)] with z hz₁ hz₂
  exact hz₁.trans hz₂.symm

/-- For rough H³ data, P₀ has a genuine H³ representative and commutes with every ordered
weak derivative on the centered cell. -/
theorem exists_projectedVecH3 {c : ℝ} (hc : 0 < c) (x : VecH3 c) :
    ∃ y : VecH3 c,
      (∀ α : Sob.Idx 2 3,
        vecH3CellDerivCLM α y = Cyl.P0 c (vecH3CellDerivCLM α x)) ∧
      ‖y‖ ≤ ‖x‖ := by
  obtain ⟨xs, u, hu, hxrep, hxlim⟩ := exists_smoothVecH3_sequence hc x
  let ys : ℕ → VecH3 c := fun n => Classical.choose
    (exists_projectedSmoothVecH3 hc (u n) (hu n))
  have hys (n : ℕ) :
      (∀ α : Sob.Idx 2 3,
        vecH3CellDerivCLM α (ys n) = Cyl.P0 c (vecH3CellDerivCLM α (xs n))) ∧
      ‖ys n‖ ≤ ‖xs n‖ := by
    have hspec := Classical.choose_spec (exists_projectedSmoothVecH3 hc (u n) (hu n))
    refine ⟨?_, ?_⟩
    · intro α
      change vecH3CellDerivCLM α
          (Classical.choose (exists_projectedSmoothVecH3 hc (u n) (hu n))) = _
      rw [hxrep n]
      exact hspec.1 α
    · change ‖Classical.choose (exists_projectedSmoothVecH3 hc (u n) (hu n))‖ ≤ _
      rw [hxrep n]
      exact hspec.2
  -- The sequence is Cauchy because each actual derivative component is projected by the
  -- contractive L² orthogonal projection.
  have hcontract (n m : ℕ) : ‖ys n - ys m‖ ≤ ‖xs n - xs m‖ := by
    have hsq : ‖ys n - ys m‖ ^ 2 ≤ ‖xs n - xs m‖ ^ 2 := by
      rw [Sob.W.norm_sq, Sob.W.norm_sq]
      apply Finset.sum_le_sum
      intro α _
      have hd : vecH3CellDerivCLM α (ys n - ys m) =
          Cyl.P0 c (vecH3CellDerivCLM α (xs n - xs m)) := by
        calc
          vecH3CellDerivCLM α (ys n - ys m) =
              vecH3CellDerivCLM α (ys n) - vecH3CellDerivCLM α (ys m) := map_sub _ _ _
          _ = Cyl.P0 c (vecH3CellDerivCLM α (xs n)) -
              Cyl.P0 c (vecH3CellDerivCLM α (xs m)) := by rw [(hys n).1 α, (hys m).1 α]
          _ = Cyl.P0 c (vecH3CellDerivCLM α (xs n) - vecH3CellDerivCLM α (xs m)) := by
              rw [map_sub]
          _ = Cyl.P0 c (vecH3CellDerivCLM α (xs n - xs m)) :=
              congrArg (Cyl.P0 c)
                (map_sub (vecH3CellDerivCLM α) (xs n) (xs m)).symm
      rw [← (weightedToCellL2Isometry c).norm_map
        (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec2 3 2 α (ys n - ys m)),
        ← (weightedToCellL2Isometry c).norm_map
        (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec2 3 2 α (xs n - xs m))]
      change ‖vecH3CellDerivCLM α (ys n - ys m)‖ ^ 2 ≤
        ‖vecH3CellDerivCLM α (xs n - xs m)‖ ^ 2
      rw [hd]
      have hP : ‖Cyl.P0 c (vecH3CellDerivCLM α (xs n - xs m))‖ ≤
          ‖vecH3CellDerivCLM α (xs n - xs m)‖ := by
        calc
          ‖Cyl.P0 c (vecH3CellDerivCLM α (xs n - xs m))‖ ≤
              ‖Cyl.P0 c‖ * ‖vecH3CellDerivCLM α (xs n - xs m)‖ :=
                (Cyl.P0 c).le_opNorm _
          _ ≤ 1 * ‖vecH3CellDerivCLM α (xs n - xs m)‖ :=
                mul_le_mul_of_nonneg_right Cyl.norm_P0_le (norm_nonneg _)
          _ = _ := one_mul _
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hP
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  have hyCauchy : CauchySeq ys := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hxlim.cauchySeq ε hε
    refine ⟨N, ?_⟩
    intro n hn m hm
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (hcontract n m) (by
      have hh := hN n hn m hm
      simpa only [dist_eq_norm] using hh)
  obtain ⟨y, hylimit⟩ := cauchySeq_tendsto_of_complete hyCauchy
  have hcomponentLimit (α : Sob.Idx 2 3) :
      vecH3CellDerivCLM α y = Cyl.P0 c (vecH3CellDerivCLM α x) := by
    have hleft : Tendsto (fun n => vecH3CellDerivCLM α (ys n)) atTop
        (𝓝 (vecH3CellDerivCLM α y)) :=
      ((vecH3CellDerivCLM α).continuous.tendsto y).comp hylimit
    have hright : Tendsto (fun n => Cyl.P0 c (vecH3CellDerivCLM α (xs n))) atTop
        (𝓝 (Cyl.P0 c (vecH3CellDerivCLM α x))) := by
      exact ((Cyl.P0 c).continuous.tendsto _).comp
        (((vecH3CellDerivCLM α).continuous.tendsto x).comp hxlim)
    exact tendsto_nhds_unique (hleft.congr' (Filter.Eventually.of_forall fun n =>
      (hys n).1 α)) hright
  have hnormLimit : Tendsto (fun n => ‖ys n‖) atTop (𝓝 ‖y‖) :=
    (continuous_norm.tendsto y).comp hylimit
  have hxnormLimit : Tendsto (fun n => ‖xs n‖) atTop (𝓝 ‖x‖) :=
    (continuous_norm.tendsto x).comp hxlim
  have hnorm := le_of_tendsto_of_tendsto hnormLimit hxnormLimit
    (Filter.Eventually.of_forall fun n => (hys n).2)
  exact ⟨y, hcomponentLimit, hnorm⟩

#print axioms UnforcedLeray.TrainB.exists_smoothVecH3_sequence
#print axioms UnforcedLeray.TrainB.exists_projectedVecH3

end UnforcedLeray.TrainB
