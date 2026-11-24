import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_1_1_2_2
import UnforcedLeray.Short.PartI.Sub.PartI_T08_2_2

/-!
# Part I, task `PartI:T08/4/1/1/1/2/2/1` (`VelJetUniformL2`): decomposition

Source: `the November 2 reference manuscript` lines 261-288.

`velJetUniformL2_of` derives the uniform `L²(cell)` bound on all word derivatives of the train
velocity on `[0, S]` from:

* `TrainDatumWordL2`, `VortJetEnergyIneq`, `TrainVelocityWordLap` (existing leaves, see
  `Sub/PartI_T08_2_2.lean`);
* `CutoffL2BoundQ`: the quantitative form of `CutoffL2OfBound` (Fatou, `R → ∞`);
* `GradL2BoundQ`: the quantitative form of `GradL2OfLapL2` (cutoff integration by parts);
* `VelZeroUniformL2`: the zero-order velocity energy bound, uniform on `[0, S]` (lines 261-288:
  the mild `L²` inequality, with pressure, Gronwall).

Proved here: the vorticity words are bounded in `L²(cell)` uniformly on `[0, S]` (Gronwall with
the datum), and the induction on the word.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-- Leaf: quantitative `CutoffL2OfBound` (lines 286-287; `R → ∞`, Fatou/monotone convergence).
A continuous `f` with `∫_cell χ_R f² ≤ B` for all `R ≥ 1` is in `L²(cell)` with `∫_cell f² ≤ B`.
Route: as `cutoffL2OfBound_proof`, keeping the Fatou inequality
`∫⁻ ofReal (f²) ≤ ofReal B` and converting back with `ofReal_integral_eq_lintegral_ofReal`. -/
def CutoffL2BoundQ : Prop :=
  ∀ (c B : ℝ) (f : Plane → ℝ), 0 < c → Continuous f →
    (∀ R : ℝ, 1 ≤ R → ∫ z in Cyl.cell c, etaCutoff R z.2 * f z ^ 2 ≤ B) →
    MemLp f 2 (Cyl.cellμ c) ∧ ∫ z in Cyl.cell c, f z ^ 2 ≤ B

/-- Leaf: quantitative `GradL2OfLapL2` (lines 286-287, cutoff integration by parts).  There is an
absolute `K ≥ 0` such that for smooth `c`-periodic `h` with `|h|, |∂_q h|, |∂_η h| ≤ M`,
`h, Δh ∈ L²(cell)`, `∫ h² ≤ A`, `∫ (Δh)² ≤ D`, the gradient components are in `L²(cell)` with
`∫ (∂_q h)² ≤ A + D + K c M²` and the same for `∂_η h`.  Route: `∫ χ_R |∇h|² ≤ ‖h‖₂‖Δh‖₂ +
(C₀/R) M² 2Rc` as in `gradL2OfLapL2_proof`, `‖h‖‖Δh‖ ≤ (A + D)/2`, then `R → ∞`. -/
def GradL2BoundQ : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (c : ℝ) (h : Plane → ℝ), 0 < c → ContDiff ℝ ∞ h → Cyl.IsPeriodic c h →
    ∀ M : ℝ, (∀ z : Plane, |h z| ≤ M ∧ |Cyl.partialQ h z| ≤ M ∧ |Cyl.partialEta h z| ≤ M) →
    MemLp h 2 (Cyl.cellμ c) → MemLp (Train.lapS h) 2 (Cyl.cellμ c) →
    ∀ A D : ℝ, (∫ z in Cyl.cell c, h z ^ 2 ≤ A) → (∫ z in Cyl.cell c, (Train.lapS h z) ^ 2 ≤ D) →
      MemLp (Cyl.partialQ h) 2 (Cyl.cellμ c) ∧ MemLp (Cyl.partialEta h) 2 (Cyl.cellμ c) ∧
      ∫ z in Cyl.cell c, (Cyl.partialQ h z) ^ 2 ≤ A + D + K * c * M ^ 2 ∧
      ∫ z in Cyl.cell c, (Cyl.partialEta h z) ^ 2 ≤ A + D + K * c * M ^ 2

/-- Leaf: the zero-order velocity energy is bounded uniformly on `[0, S]` (lines 261-288: the
datum is in `L²`; mild `L²` inequality
`‖v(t)‖₂ ≤ ‖v(0)‖₂ + C ν^{-1/2} sup‖v‖_∞ ∫ (t-r)^{-1/2} ‖v(r)‖₂ dr` continues `L²` membership, or
the energy identity with cutoffs, using the `BUC` bound on `[0, S]`). -/
def VelZeroUniformL2 : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr →
    ∀ S : ℝ, 0 < S → ∀ k : Fin 2, ∃ B : ℝ, ∀ r : ℝ, 0 ≤ r → r ≤ S →
      ∫ z in Cyl.cell c, (tr.v r z k) ^ 2 ≤ B

/-- The vorticity words are bounded in `L²(cell)` uniformly on `[0, S]`. -/
theorem vjl_vortWord_uniform (h1 : TrainDatumWordL2) (h2 : VortJetEnergyIneq)
    (hq : CutoffL2BoundQ) {ν c : ℝ} (hν : 0 < ν) (hc : 1 ≤ c)
    {tr : B0140.TrainSol ν c} (htr : IsBUCTrain tr) {S : ℝ} (hS : 0 < S) (u : List Bool) :
    ∃ B : ℝ, ∀ r : ℝ, 0 ≤ r → r ≤ S →
      MemLp (vortWord tr u r) 2 (Cyl.cellμ c) ∧ ∫ z in Cyl.cell c, vortWord tr u r z ^ 2 ≤ B := by
  have hc0 : 0 < c := by linarith
  obtain ⟨C, hC, hE⟩ := h2 ν c hν hc tr htr u.length S hS
  have hint0 : ∀ u' : List Bool,
      Integrable (fun z => vortWord tr u' 0 z ^ 2) (volume.restrict (Cyl.cell c)) :=
    fun u' => (vjl_datum_vortWord_memLp h1 hc0 tr u').integrable_sq
  have hsum0 : Integrable (fun z => ∑ u' ∈ wordsUpTo u.length, vortWord tr u' 0 z ^ 2)
      (volume.restrict (Cyl.cell c)) :=
    integrable_finset_sum _ (fun u' _ => hint0 u')
  set D0 := ∫ z in Cyl.cell c, ∑ u' ∈ wordsUpTo u.length, vortWord tr u' 0 z ^ 2 with hD0
  have hD0nn : 0 ≤ D0 := integral_nonneg (fun z => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  refine ⟨(D0 + 1) * Real.exp (C * S), fun s hs0 hsS => ?_⟩
  have hbound : ∀ R : ℝ, 1 ≤ R →
      ∫ z in Cyl.cell c, etaCutoff R z.2 * vortWord tr u s z ^ 2 ≤
        (D0 + 1) * Real.exp (C * S) := by
    intro R hR
    have hR0 : 0 < R := by linarith
    obtain ⟨hcont, hder⟩ := hE R hR
    have hG := cutoffGronwall_proof (vortJetEnergy tr u.length R) S C hS hC hcont hder s
      ⟨hs0, hsS⟩
    have hz : vortJetEnergy tr u.length R 0 ≤ D0 := by
      unfold vortJetEnergy
      apply integral_mono_of_nonneg _ hsum0
      · refine Filter.Eventually.of_forall (fun z => ?_)
        have hS' : 0 ≤ ∑ u' ∈ wordsUpTo u.length, vortWord tr u' 0 z ^ 2 :=
          Finset.sum_nonneg (fun _ _ => sq_nonneg _)
        have h := cehd_eta_le_one R z.2
        have h' := etaCutoff_nonneg R z.2
        show etaCutoff R z.2 * ∑ u' ∈ wordsUpTo u.length, vortWord tr u' 0 z ^ 2 ≤
          ∑ u' ∈ wordsUpTo u.length, vortWord tr u' 0 z ^ 2
        nlinarith
      · refine Filter.Eventually.of_forall (fun z => ?_)
        show (0 : ℝ) ≤ etaCutoff R z.2 * ∑ u' ∈ wordsUpTo u.length, vortWord tr u' 0 z ^ 2
        exact mul_nonneg (etaCutoff_nonneg R z.2) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    have hexp : Real.exp (C * s) ≤ Real.exp (C * S) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hsS hC)
    have hexp0 : 0 < Real.exp (C * s) := Real.exp_pos _
    have hFs : vortJetEnergy tr u.length R s ≤ (D0 + 1) * Real.exp (C * S) :=
      calc vortJetEnergy tr u.length R s ≤ (vortJetEnergy tr u.length R 0 + 1) * Real.exp (C * s) :=
            hG
        _ ≤ (D0 + 1) * Real.exp (C * s) :=
            mul_le_mul_of_nonneg_right (by linarith) hexp0.le
        _ ≤ (D0 + 1) * Real.exp (C * S) := mul_le_mul_of_nonneg_left hexp (by linarith)
    have hcs : Continuous (vortWord tr u s) := (vjl_vortWord_contDiff tr hs0 u).continuous
    have hsumc : Continuous (fun z => ∑ u' ∈ wordsUpTo u.length, vortWord tr u' s z ^ 2) :=
      continuous_finset_sum _ (fun u' _ => (vjl_vortWord_contDiff tr hs0 u').continuous.pow 2)
    have hle : ∫ z in Cyl.cell c, etaCutoff R z.2 * vortWord tr u s z ^ 2 ≤
        vortJetEnergy tr u.length R s := by
      unfold vortJetEnergy
      refine integral_mono (vjl_cutoff_integrable hR0 (hcs.pow 2))
        (vjl_cutoff_integrable hR0 hsumc) (fun z => ?_)
      refine mul_le_mul_of_nonneg_left ?_ (etaCutoff_nonneg R z.2)
      exact Finset.single_le_sum (f := fun u' => vortWord tr u' s z ^ 2)
        (fun _ _ => sq_nonneg _) (mem_wordsUpTo.2 le_rfl)
    exact hle.trans hFs
  exact hq c _ (vortWord tr u s) hc0 (vjl_vortWord_contDiff tr hs0 u).continuous hbound

/-- **`VelJetUniformL2` from the leaves.** -/
theorem velJetUniformL2_of (h1 : TrainDatumWordL2) (h2 : VortJetEnergyIneq)
    (h6 : TrainVelocityWordLap) (hq : CutoffL2BoundQ) (hg : GradL2BoundQ)
    (hz : VelZeroUniformL2) : VelJetUniformL2 := by
  intro ν c hν hc tr htr S hS w
  have hc0 : 0 < c := by linarith
  obtain ⟨K, hK, hKb⟩ := hg
  induction w with
  | nil =>
    intro k
    obtain ⟨B, hB⟩ := hz ν c hν hc tr htr S hS k
    exact ⟨B, fun r hr0 hrS => ⟨vjl_base_memLp tr hr0 k, hB r hr0 hrS⟩⟩
  | cons β w' ih =>
    intro k
    -- uniform bounds for the Laplacians and the zero-order words
    have hlap : ∀ k' : Fin 2, ∃ D : ℝ, ∀ r : ℝ, 0 ≤ r → r ≤ S →
        MemLp (Train.lapS (wordComp w' (tr.v r) k')) 2 (Cyl.cellμ c) ∧
        ∫ z in Cyl.cell c, (Train.lapS (wordComp w' (tr.v r) k') z) ^ 2 ≤ D := by
      intro k'
      rcases (show k' = 0 ∨ k' = 1 by fin_cases k' <;> simp) with rfl | rfl
      · obtain ⟨D, hD⟩ := vjl_vortWord_uniform h1 h2 hq hν hc htr hS (false :: w')
        refine ⟨D, fun r hr0 hrS => ?_⟩
        have e : Train.lapS (wordComp w' (tr.v r) 0) =
            fun z => -vortWord tr (false :: w') r z :=
          funext fun z => (h6 ν c hc0 tr r hr0 w' z).1
        obtain ⟨hm, hi⟩ := hD r hr0 hrS
        rw [e]
        refine ⟨hm.neg, ?_⟩
        simpa using hi
      · obtain ⟨D, hD⟩ := vjl_vortWord_uniform h1 h2 hq hν hc htr hS (true :: w')
        refine ⟨D, fun r hr0 hrS => ?_⟩
        have e : Train.lapS (wordComp w' (tr.v r) 1) = vortWord tr (true :: w') r :=
          funext fun z => (h6 ν c hc0 tr r hr0 w' z).2
        rw [e]
        exact hD r hr0 hrS
    obtain ⟨M1, hM1⟩ := vjl_wordBoundedOn htr hS.le w' k
    obtain ⟨M2, hM2⟩ := vjl_wordBoundedOn htr hS.le (true :: w') k
    obtain ⟨M3, hM3⟩ := vjl_wordBoundedOn htr hS.le (false :: w') k
    obtain ⟨D, hD⟩ := hlap k
    obtain ⟨A, hA⟩ := ih k
    refine ⟨A + D + K * c * (max M1 (max M2 M3)) ^ 2, fun r hr0 hrS => ?_⟩
    have hrI : r ∈ Icc (0 : ℝ) S := ⟨hr0, hrS⟩
    have hsm : ContDiff ℝ ∞ (wordComp w' (tr.v r) k) :=
      B0151.contDiff_derivWord (vjl_slice_smooth tr hr0 k) w'
    have hbd : ∀ z : Plane, |wordComp w' (tr.v r) k z| ≤ max M1 (max M2 M3) ∧
        |Cyl.partialQ (wordComp w' (tr.v r) k) z| ≤ max M1 (max M2 M3) ∧
        |Cyl.partialEta (wordComp w' (tr.v r) k) z| ≤ max M1 (max M2 M3) := by
      intro z
      refine ⟨?_, ?_, ?_⟩
      · exact (hM1 r hrI z).trans (le_max_left _ _)
      · exact (hM2 r hrI z).trans ((le_max_left _ _).trans (le_max_right _ _))
      · exact (hM3 r hrI z).trans ((le_max_right _ _).trans (le_max_right _ _))
    obtain ⟨hmA, hiA⟩ := hA r hr0 hrS
    obtain ⟨hmD, hiD⟩ := hD r hr0 hrS
    obtain ⟨hQ, hE, hQb, hEb⟩ := hKb c (wordComp w' (tr.v r) k) hc0 hsm
      (vjl_word_periodic tr hr0 w' k) _ hbd hmA hmD A D hiA hiD
    cases β
    · exact ⟨hE, hEb⟩
    · exact ⟨hQ, hQb⟩

end UnforcedLeray.Short.PartI
