import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2.VelocityJetL2
import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_1_1_2
import UnforcedLeray.Short.PartI.Sub.T05Class

/-!
# Part I, task `PartI:T08/4/1/1/1/2/1` (`VelJetLocalWindow`): decomposition

Source: `the November 2 reference manuscript` lines 261-288 (finite-energy BUC
train; mild `L²` bound; transverse cutoffs give the velocity and vorticity energy identities).

The proof of `TrainVelocityJetL2` is run with a bound uniform in `r ∈ [0, S]`:

* base case `w = []`: the uniform cell energy bound `TrainLocalBoundsBUC` (lines 276-283);
* vorticity words: Gronwall on `[0, S+1]` for the cutoff vorticity jet energy gives a bound uniform
  in `r ∈ [0, S]`, and the quantitative cutoff limit `cutoffL2Quant_proof` (proved here) turns it
  into an `L²` bound (`vortUniform`);
* velocity words, by induction on the word: `Δ ∂_w v = ± ∂ ∂_w ω` (`trainVelocityWordLap_proof`)
  and the quantitative gradient estimate `GradL2Quant` (leaf).

`velJetLocalWindow_of` proves the target from the leaves `TrainLocalBoundsBUC` and `GradL2Quant`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (width)

/-- **Quantitative `R → ∞`** (lines 286-287): a continuous `f` with `∫_cell χ_R f² ≤ B` for all
`R ≥ 1` is in `L²(cell)` with `∫_cell f² ≤ B`. -/
def CutoffL2Quant : Prop :=
  ∀ (c B : ℝ) (f : Plane → ℝ), 0 < c → Continuous f →
    (∀ R : ℝ, 1 ≤ R → ∫ z in Cyl.cell c, etaCutoff R z.2 * f z ^ 2 ≤ B) →
    MemLp f 2 (Cyl.cellμ c) ∧ ∫ z in Cyl.cell c, f z ^ 2 ≤ B

/-- **Leaf (quantitative gradient from the Laplacian)** (lines 286-287, transverse cutoffs).
For `c > 0` and `M` there is `K` such that every smooth `c`-periodic `h` with
`|h|, |∂_q h|, |∂_η h| ≤ M` and `h, Δh ∈ L²(cell)` has `∂_q h, ∂_η h ∈ L²(cell)` and
`∫ (∂_q h)², ∫ (∂_η h)² ≤ ∫ h² + ∫ (Δh)² + K`.  Route: the proof of `gradL2OfLapL2_proof`
(`Tasks/DifferentiatedEnergy/ErrJetL2/VelocityJetL2/GradL2OfLapL2.lean`) gives
`∫ χ_R (q² + η²) ≤ ∫ (h² + d²)/2 + 4 C₀ c M²` for all `R ≥ 1`; apply `cutoffL2Quant_proof` to
`∂_q h` and `∂_η h` (each cutoff integral is at most that bound). -/
def GradL2Quant : Prop :=
  ∀ c : ℝ, 0 < c → ∀ M : ℝ, ∃ K : ℝ, ∀ h : Plane → ℝ, ContDiff ℝ ∞ h → Cyl.IsPeriodic c h →
    (∀ z : Plane, |h z| ≤ M ∧ |Cyl.partialQ h z| ≤ M ∧ |Cyl.partialEta h z| ≤ M) →
    MemLp h 2 (Cyl.cellμ c) → MemLp (Train.lapS h) 2 (Cyl.cellμ c) →
    MemLp (Cyl.partialQ h) 2 (Cyl.cellμ c) ∧ MemLp (Cyl.partialEta h) 2 (Cyl.cellμ c) ∧
    ∫ z in Cyl.cell c, (Cyl.partialQ h z) ^ 2 ≤
      (∫ z in Cyl.cell c, h z ^ 2) + (∫ z in Cyl.cell c, (Train.lapS h z) ^ 2) + K ∧
    ∫ z in Cyl.cell c, (Cyl.partialEta h z) ^ 2 ≤
      (∫ z in Cyl.cell c, h z ^ 2) + (∫ z in Cyl.cell c, (Train.lapS h z) ^ 2) + K

/-- `CutoffL2Quant` (proved): dominated convergence along `R = n + 1`. -/
theorem cutoffL2Quant_proof : CutoffL2Quant := by
  intro c B f hc hf hbound
  have hmem := cutoffL2OfBound_proof c B f hc hf hbound
  refine ⟨hmem, ?_⟩
  have hint2 : Integrable (fun z : Plane => f z ^ 2) (volume.restrict (Cyl.cell c)) :=
    hmem.integrable_sq
  have hlim : Tendsto (fun n : ℕ => ∫ z in Cyl.cell c, etaCutoff ((n : ℝ) + 1) z.2 * f z ^ 2)
      atTop (𝓝 (∫ z in Cyl.cell c, f z ^ 2)) := by
    refine tendsto_integral_of_dominated_convergence (fun z => f z ^ 2)
      (fun n => (vjl_cutoff_integrable (c := c) (R := (n : ℝ) + 1) (by positivity)
        (g := fun z => f z ^ 2) (hf.pow 2)).aestronglyMeasurable) hint2
      (fun n => Filter.Eventually.of_forall (fun z => ?_)) (Filter.Eventually.of_forall (fun z => ?_))
    · have h1 := cehd_eta_le_one ((n : ℝ) + 1) z.2
      have h2 := etaCutoff_nonneg ((n : ℝ) + 1) z.2
      have h3 := sq_nonneg (f z)
      rw [Real.norm_of_nonneg (mul_nonneg h2 h3)]
      nlinarith
    · obtain ⟨N, hN⟩ := exists_nat_ge |z.2|
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop N] with n hn
      have hR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hab : |z.2| ≤ (n : ℝ) + 1 := by linarith
      rw [ecOne ((n : ℝ) + 1) hR z.2 hab, one_mul]
  exact le_of_tendsto' hlim (fun n => hbound _ (by have := Nat.cast_nonneg (α := ℝ) n; linarith))

/-- Uniform `L²` bounds on the vorticity words on `[0, S]`. -/
theorem vortUniform (hQ : CutoffL2Quant) {ν c : ℝ} (hν : 0 < ν) (hc : 1 ≤ c)
    {tr : B0140.TrainSol ν c} (htr : IsBUCTrain tr) {S : ℝ} (hS : 0 < S) (u : List Bool) :
    ∃ B : ℝ, ∀ r : ℝ, 0 ≤ r → r ≤ S →
      MemLp (vortWord tr u r) 2 (Cyl.cellμ c) ∧ ∫ z in Cyl.cell c, vortWord tr u r z ^ 2 ≤ B := by
  have hc0 : 0 < c := by linarith
  obtain ⟨C, hC, hE⟩ := vortJetEnergyIneq_proof ν c hν hc tr htr u.length (S + 1) (by linarith)
  have hint0 : ∀ u' : List Bool,
      Integrable (fun z => vortWord tr u' 0 z ^ 2) (volume.restrict (Cyl.cell c)) :=
    fun u' => (vjl_datum_vortWord_memLp trainDatumWordL2_proof hc0 tr u').integrable_sq
  have hsum0 : Integrable (fun z => ∑ u' ∈ wordsUpTo u.length, vortWord tr u' 0 z ^ 2)
      (volume.restrict (Cyl.cell c)) :=
    integrable_finset_sum _ (fun u' _ => hint0 u')
  set D0 : ℝ := ∫ z in Cyl.cell c, ∑ u' ∈ wordsUpTo u.length, vortWord tr u' 0 z ^ 2 with hD0
  have hD0nn : 0 ≤ D0 := integral_nonneg (fun z => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  refine ⟨(D0 + 1) * Real.exp (C * (S + 1)), fun r hr0 hrS => ?_⟩
  have hbound : ∀ R : ℝ, 1 ≤ R →
      ∫ z in Cyl.cell c, etaCutoff R z.2 * vortWord tr u r z ^ 2 ≤
        (D0 + 1) * Real.exp (C * (S + 1)) := by
    intro R hR
    have hR0 : 0 < R := by linarith
    obtain ⟨hcont, hder⟩ := hE R hR
    have hG := cutoffGronwall_proof (vortJetEnergy tr u.length R) (S + 1) C (by linarith) hC hcont
      hder r ⟨hr0, by linarith⟩
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
    have hexp : Real.exp (C * r) ≤ Real.exp (C * (S + 1)) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith) hC)
    have hFs : vortJetEnergy tr u.length R r ≤ (D0 + 1) * Real.exp (C * (S + 1)) :=
      hG.trans (mul_le_mul (by linarith) hexp (Real.exp_pos _).le (by linarith))
    have hcs : Continuous (vortWord tr u r) := (vjl_vortWord_contDiff tr hr0 u).continuous
    have hsumc : Continuous (fun z => ∑ u' ∈ wordsUpTo u.length, vortWord tr u' r z ^ 2) :=
      continuous_finset_sum _ (fun u' _ => (vjl_vortWord_contDiff tr hr0 u').continuous.pow 2)
    have hle : ∫ z in Cyl.cell c, etaCutoff R z.2 * vortWord tr u r z ^ 2 ≤
        vortJetEnergy tr u.length R r := by
      unfold vortJetEnergy
      refine integral_mono (vjl_cutoff_integrable hR0 (hcs.pow 2))
        (vjl_cutoff_integrable hR0 hsumc) (fun z => ?_)
      refine mul_le_mul_of_nonneg_left ?_ (etaCutoff_nonneg R z.2)
      exact Finset.single_le_sum (f := fun u' => vortWord tr u' r z ^ 2)
        (fun _ _ => sq_nonneg _) (mem_wordsUpTo.2 le_rfl)
    exact hle.trans hFs
  exact hQ c _ (vortWord tr u r) hc0 (vjl_vortWord_contDiff tr hr0 u).continuous hbound

/-- Uniform `L²` bounds on all word derivatives of the train velocity on `[0, S]`. -/
theorem velUniform (hB : TrainLocalBoundsBUC) (hQ : CutoffL2Quant) (hG : GradL2Quant)
    {ν c : ℝ} (hν : 0 < ν) (hc : 1 ≤ c) {tr : B0140.TrainSol ν c} (htr : IsBUCTrain tr)
    {S : ℝ} (hS : 0 < S) :
    ∀ (w : List Bool) (k : Fin 2), ∃ B : ℝ, ∀ r : ℝ, 0 ≤ r → r ≤ S →
      MemLp (wordComp w (tr.v r) k) 2 (Cyl.cellμ c) ∧
      ∫ z in Cyl.cell c, (wordComp w (tr.v r) k z) ^ 2 ≤ B := by
  have hc0 : 0 < c := by linarith
  intro w
  induction w with
  | nil =>
    intro k
    obtain ⟨M, hM⟩ := hB ν c hν hc tr htr S hS.le
    refine ⟨M, fun r hr0 hrS => ⟨vjl_base_memLp tr hr0 k, ?_⟩⟩
    have hmem := vjl_base_memLp tr hr0 k
    have hE : Integrable (fun z => ‖tr.v r z‖ ^ 2) (Cyl.cellμ c) :=
      tr.isTrain.finite_energy r hr0
    have hle : ∫ z in Cyl.cell c, ‖tr.v r z‖ ^ 2 ≤ M := (hM r ⟨hr0, hrS⟩).2.2
    refine le_trans (integral_mono hmem.integrable_sq hE (fun z => ?_)) hle
    have h1 : |tr.v r z k| ≤ ‖tr.v r z‖ := by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (tr.v r z) k
    have h2 : |tr.v r z k| ^ 2 ≤ ‖tr.v r z‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [sq_abs] at h2
    exact h2
  | cons β w' ih =>
    intro k
    obtain ⟨Ba, hBa⟩ := vortUniform hQ hν hc htr hS (false :: w')
    obtain ⟨Bb, hBb⟩ := vortUniform hQ hν hc htr hS (true :: w')
    obtain ⟨M1, hM1⟩ := vjl_wordBoundedOn htr hS.le w' k
    obtain ⟨M2, hM2⟩ := vjl_wordBoundedOn htr hS.le (true :: w') k
    obtain ⟨M3, hM3⟩ := vjl_wordBoundedOn htr hS.le (false :: w') k
    obtain ⟨K, hK⟩ := hG c hc0 (max M1 (max M2 M3))
    obtain ⟨B1, hB1⟩ := ih k
    refine ⟨B1 + max Ba Bb + K, fun r hr0 hrS => ?_⟩
    have hrI : r ∈ Icc (0 : ℝ) S := ⟨hr0, hrS⟩
    have hlap : MemLp (Train.lapS (wordComp w' (tr.v r) k)) 2 (Cyl.cellμ c) ∧
        ∫ z in Cyl.cell c, (Train.lapS (wordComp w' (tr.v r) k) z) ^ 2 ≤ max Ba Bb := by
      rcases (show k = 0 ∨ k = 1 by fin_cases k <;> simp) with rfl | rfl
      · have e : Train.lapS (wordComp w' (tr.v r) 0) = fun z => -vortWord tr (false :: w') r z :=
          funext fun z => (trainVelocityWordLap_proof ν c hc0 tr r hr0 w' z).1
        obtain ⟨hm, hi⟩ := hBa r hr0 hrS
        rw [e]
        refine ⟨hm.neg, ?_⟩
        simp only [neg_sq]
        exact hi.trans (le_max_left _ _)
      · have e : Train.lapS (wordComp w' (tr.v r) 1) = vortWord tr (true :: w') r :=
          funext fun z => (trainVelocityWordLap_proof ν c hc0 tr r hr0 w' z).2
        obtain ⟨hm, hi⟩ := hBb r hr0 hrS
        rw [e]
        exact ⟨hm, hi.trans (le_max_right _ _)⟩
    have hsm : ContDiff ℝ ∞ (wordComp w' (tr.v r) k) :=
      B0151.contDiff_derivWord (vjl_slice_smooth tr hr0 k) w'
    have hbd : ∀ z : Plane, |wordComp w' (tr.v r) k z| ≤ max M1 (max M2 M3) ∧
        |Cyl.partialQ (wordComp w' (tr.v r) k) z| ≤ max M1 (max M2 M3) ∧
        |Cyl.partialEta (wordComp w' (tr.v r) k) z| ≤ max M1 (max M2 M3) := fun z =>
      ⟨(hM1 r hrI z).trans (le_max_left _ _),
        (hM2 r hrI z).trans ((le_max_left _ _).trans (le_max_right _ _)),
        (hM3 r hrI z).trans ((le_max_right _ _).trans (le_max_right _ _))⟩
    obtain ⟨hmh, hih⟩ := hB1 r hr0 hrS
    obtain ⟨hQm, hEm, hQi, hEi⟩ := hK _ hsm (vjl_word_periodic tr hr0 w' k) hbd hmh hlap.1
    have hfin : (∫ z in Cyl.cell c, (wordComp w' (tr.v r) k z) ^ 2) +
        (∫ z in Cyl.cell c, (Train.lapS (wordComp w' (tr.v r) k) z) ^ 2) + K ≤
        B1 + max Ba Bb + K := by linarith [hih, hlap.2]
    cases β
    · exact ⟨hEm, hEi.trans hfin⟩
    · exact ⟨hQm, hQi.trans hfin⟩

/-- **`VelJetLocalWindow` from the leaves** `TrainLocalBoundsBUC` and `GradL2Quant`
(with `ε = s / 2`, `S = 2 s`). -/
theorem velJetLocalWindow_of (hB : TrainLocalBoundsBUC) (hG : GradL2Quant) :
    VelJetLocalWindow := by
  intro ν c hν hc tr htr s hs _hw w k
  obtain ⟨B, hB'⟩ := velUniform hB cutoffL2Quant_proof hG hν hc htr (S := 2 * s)
    (by linarith) w k
  refine ⟨s / 2, by linarith, B, fun r hr hrs => ?_⟩
  have h := abs_lt.1 hrs
  exact hB' r hr.le (by linarith)

end UnforcedLeray.Short.PartI
