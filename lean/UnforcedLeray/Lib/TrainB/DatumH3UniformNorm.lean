import UnforcedLeray.Lib.TrainB.InitialDatumH3Class
import UnforcedLeray.Units.B0141.Datum

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory
open scoped ENNReal ContDiff Topology
open UnforcedLeray.Cyl

namespace UnforcedLeray.TrainB

private def datumUniformJetConstant (j : ℕ) : ℝ :=
  Classical.choose (Train.datum_bounds j 0)

private theorem datumUniformJetConstant_nonneg (j : ℕ) :
    0 ≤ datumUniformJetConstant j :=
  (Classical.choose_spec (Train.datum_bounds j 0)).1

private theorem datumUniformJet_eLpNorm_le {c : ℝ} (hc2 : 2 ≤ c) (j : ℕ) :
    eLpNorm (Train.jet j (Train.datum c)) 2 (Cyl.cellμ c) ≤
      ENNReal.ofReal (datumUniformJetConstant j) := by
  have h := (Classical.choose_spec (Train.datum_bounds j 0)).2 c hc2
  have hnorm := h.2.2
  simpa [datumUniformJetConstant, Train.wCellL2, Train.jap] using hnorm

def datumUniformH3ComponentConstant : ℝ :=
  datumUniformJetConstant 0 + datumUniformJetConstant 1 +
    datumUniformJetConstant 2 + datumUniformJetConstant 3

theorem datumUniformH3ComponentConstant_nonneg :
    0 ≤ datumUniformH3ComponentConstant := by
  dsimp [datumUniformH3ComponentConstant]
  have h0 := datumUniformJetConstant_nonneg 0
  have h1 := datumUniformJetConstant_nonneg 1
  have h2 := datumUniformJetConstant_nonneg 2
  have h3 := datumUniformJetConstant_nonneg 3
  linarith

private theorem datumH3MeasureEqCell (c : ℝ) :
    Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ)) = Cyl.cellμ c := by
  rw [Cyl.wμ_ρwW c (0 : ℝ), Cyl.wμ]
  simp [Cyl.ρw]

private theorem datumUniformJetConstant_le_H3 (j : ℕ) (hj : j ≤ 3) :
    datumUniformJetConstant j ≤ datumUniformH3ComponentConstant := by
  interval_cases j <;>
    dsimp [datumUniformH3ComponentConstant] <;>
    linarith [datumUniformJetConstant_nonneg 0,
      datumUniformJetConstant_nonneg 1, datumUniformJetConstant_nonneg 2,
      datumUniformJetConstant_nonneg 3]

private def datumListDirections (vs : List Plane) : Fin vs.length → Plane := fun i => vs.get i

private theorem datum_norm_cylDir_eq_one (i : Fin 2) : ‖Sob.cylDir i‖ = 1 := by
  fin_cases i <;> simp [Sob.cylDir, Prod.norm_def]

private theorem datum_iterD_eq_iteratedFDeriv (c : ℝ) (hc : c ≠ 0)
    (vs : List Plane) :
    Sob.iterD vs (Train.datum c) = fun z =>
      iteratedFDeriv ℝ vs.length (Train.datum c) z (datumListDirections vs) := by
  induction vs with
  | nil =>
      funext z
      simp [Sob.iterD, iteratedFDeriv_zero_apply]
  | cons v vs ih =>
      funext z
      change fderiv ℝ (Sob.iterD vs (Train.datum c)) z v =
        iteratedFDeriv ℝ (vs.length + 1) (Train.datum c) z
          (datumListDirections (v :: vs))
      have hm : datumListDirections (v :: vs) = Fin.cons v (datumListDirections vs) := by
        funext i
        refine Fin.cases ?_ ?_ i
        · rfl
        · intro j
          rfl
      rw [hm, iteratedFDeriv_succ_apply_left]
      simp only [Fin.cons_zero, Fin.tail_cons]
      rw [ih]
      have hD : ContDiff ℝ ∞ (iteratedFDeriv ℝ vs.length (Train.datum c)) :=
        (Train.datum_contDiff hc).iteratedFDeriv_right (m := ∞) (i := vs.length)
          UnforcedLeray.Kernels.infty_add_nat_le
      have hdiff : DifferentiableAt ℝ
          (iteratedFDeriv ℝ vs.length (Train.datum c)) z :=
        (contDiff_iff_contDiffAt.mp hD z).differentiableAt (by simp)
      exact fderiv_continuousMultilinear_apply_const_apply hdiff
        (datumListDirections vs) v

private theorem datumListDirection_norm_eq_one (vs : List Plane)
    (hvs : ∀ v ∈ vs, ∃ i : Fin 2, v = Sob.cylDir i) :
    ∏ i : Fin vs.length, ‖datumListDirections vs i‖ = 1 := by
  have heach (i : Fin vs.length) : ‖datumListDirections vs i‖ = 1 := by
    obtain ⟨j, hj⟩ := hvs (vs.get i) (List.get_mem vs i)
    change ‖vs.get i‖ = 1
    rw [hj]
    exact datum_norm_cylDir_eq_one j
  calc
    ∏ i : Fin vs.length, ‖datumListDirections vs i‖ =
        ∏ i : Fin vs.length, (1 : ℝ) := by
          apply Finset.prod_congr rfl
          intro i hi
          exact heach i
    _ = 1 := by simp

private theorem datum_word_direction_norms {c : ℝ} (α : Sob.Idx 2 3) :
    ∀ v ∈ (Sob.cylinder c).word α, ∃ i : Fin 2, v = Sob.cylDir i := by
  intro v hv
  have hv' : v ∈ List.ofFn (fun j : Fin α.1.1 => (Sob.cylinder c).dir (α.2 j)) := by
    simpa [Sob.TestDomain.word] using hv
  rcases (List.mem_ofFn' _ _).mp hv' with ⟨j, hj⟩
  refine ⟨α.2 j, ?_⟩
  simpa [Sob.TestDomain.dir] using hj.symm

private theorem datum_iterD_pointwise_norm_le_jet {c : ℝ} (hc2 : 2 ≤ c)
    (α : Sob.Idx 2 3) (z : Plane) :
    ‖Sob.iterD ((Sob.cylinder c).word α) (Train.datum c) z‖ ≤
      ‖Train.jet (((Sob.cylinder c).word α).length) (Train.datum c) z‖ := by
  let vs := (Sob.cylinder c).word α
  let k := vs.length
  rw [datum_iterD_eq_iteratedFDeriv c (by linarith) vs]
  have hbound := (iteratedFDeriv ℝ k (Train.datum c) z).le_opNorm (datumListDirections vs)
  have hprod : ∏ i : Fin k, ‖datumListDirections vs i‖ = 1 :=
    datumListDirection_norm_eq_one vs (datum_word_direction_norms α)
  calc
    ‖iteratedFDeriv ℝ k (Train.datum c) z (datumListDirections vs)‖ ≤
        ‖iteratedFDeriv ℝ k (Train.datum c) z‖ *
          ∏ i : Fin k, ‖datumListDirections vs i‖ := hbound
    _ = ‖Train.jet k (Train.datum c) z‖ := by simp [Train.jet, hprod]

/-- Every centered H³ derivative component of the actual Gaussian datum has one common bound,
uniform for all periods `c ≥ 2`. The coefficient is the sum of the four B0141 uniform jet
constants for orders zero through three. -/
theorem datumVecH3_component_norm_le_uniform {c : ℝ} (hc : 0 < c) (hc2 : 2 ≤ c)
    (α : Sob.Idx 2 3) :
    ‖vecH3CellDerivCLM α (datumVecH3 hc)‖ ≤ datumUniformH3ComponentConstant := by
  let vs := (Sob.cylinder c).word α
  let k := vs.length
  have hk : k ≤ 3 := by
    dsimp [k, vs]
    simp [Sob.TestDomain.word]
    omega
  change ‖(weightedToCellL2Isometry c)
      (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec2 3 2 α
        (datumVecH3 hc))‖ ≤ datumUniformH3ComponentConstant
  rw [(weightedToCellL2Isometry c).norm_map]
  rw [datumVecH3, Sob.W.deriv_ofFields, Lp.norm_toLp]
  rw [datumH3MeasureEqCell c]
  change (eLpNorm (Sob.iterD vs (Train.datum c)) 2 (Cyl.cellμ c)).toReal ≤
    datumUniformH3ComponentConstant
  have hmono := eLpNorm_mono (μ := Cyl.cellμ c) (p := (2 : ℝ≥0∞))
    (datum_iterD_pointwise_norm_le_jet hc2 α)
  have hjet : eLpNorm (Train.jet k (Train.datum c)) 2 (Cyl.cellμ c) ≤
      ENNReal.ofReal (datumUniformJetConstant k) := by
    exact datumUniformJet_eLpNorm_le hc2 k
  have hle := (hmono.trans hjet)
  have hreal := ENNReal.toReal_mono (by finiteness) hle
  rw [ENNReal.toReal_ofReal (datumUniformJetConstant_nonneg k)] at hreal
  exact hreal.trans (datumUniformJetConstant_le_H3 k hk)

/-- The actual initial datum has a single H³ graph norm bound independent of the period for all
`c ≥ 2`, obtained by summing the four B0141 jet constants and counting the fifteen ordered words
of length at most three. -/
theorem datumVecH3_norm_le_uniform {c : ℝ} (hc : 0 < c) (hc2 : 2 ≤ c) :
    ‖datumVecH3 hc‖ ≤ 4 * datumUniformH3ComponentConstant := by
  have hB := datumUniformH3ComponentConstant_nonneg
  have hcard : Fintype.card (Sob.Idx 2 3) = 15 := by
    norm_num [Sob.Idx, Fintype.card_sigma, Fintype.card_fun, Fin.sum_univ_succ]
  have hsq : ‖datumVecH3 hc‖ ^ 2 ≤
      (4 * datumUniformH3ComponentConstant) ^ 2 := by
    rw [Sob.W.norm_sq]
    calc
      (∑ α : Sob.Idx 2 3,
          ‖Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec2 3 2 α
            (datumVecH3 hc)‖ ^ 2) ≤
        ∑ α : Sob.Idx 2 3, datumUniformH3ComponentConstant ^ 2 := by
          apply Finset.sum_le_sum
          intro α hα
          have hαnorm := datumVecH3_component_norm_le_uniform hc hc2 α
          have hαnorm' : ‖vecH3CellDerivCLM α (datumVecH3 hc)‖ ≤
              datumUniformH3ComponentConstant := hαnorm
          rw [← (weightedToCellL2Isometry c).norm_map
            (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec2 3 2 α
              (datumVecH3 hc))]
          change ‖vecH3CellDerivCLM α (datumVecH3 hc)‖ ^ 2 ≤ _
          exact (sq_le_sq₀ (norm_nonneg _) hB).mpr hαnorm'
      _ = 15 * datumUniformH3ComponentConstant ^ 2 := by simp [hcard]
      _ ≤ 16 * datumUniformH3ComponentConstant ^ 2 := by
        nlinarith [sq_nonneg datumUniformH3ComponentConstant]
      _ = (4 * datumUniformH3ComponentConstant) ^ 2 := by ring
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) hB)).mp hsq

#print axioms UnforcedLeray.TrainB.datumVecH3_component_norm_le_uniform
#print axioms UnforcedLeray.TrainB.datumVecH3_norm_le_uniform

end UnforcedLeray.TrainB
