import UnforcedLeray.Short.PartI.Sub.PartI_T09_5_org_1.FiniteEnergy
import UnforcedLeray.Short.Spine.Proofs.EstVcRegularity
import UnforcedLeray.Short.PartI.Sub.PartI_T08_1
import UnforcedLeray.Short.PartI.Sub.PartI_T08_7_2

/-!
# `PartI:T09/5/org/1/org/b`: the jet energies of the error tend to `0` from the finite-energy class

Source: `the November 2 reference manuscript`,
lines 281-288 (the BUC solution is the finite-energy solution) and 341-344 (`e = v - V_c^p`,
`E_N^2 = sum (delta a)^j ||D^j e||^2`).

Proof outline.  Since `v(0) = V_c^p(0)` (`trainErr_zero_local`), for `s >= 0` and every word `w`,
component `k`, and point `z`,
`wordComp w (trainErr tr s) k z = D - E` with `D = ∂_w v_k(s) - ∂_w v_k(0)` and
`E = ∂_w V_c,k(s) - ∂_w V_c,k(0)`.  Hence the squared jet density is at most
`2 D^2 + 2 E^2`, and the lower integral of the jet density is bounded by a finite sum of the two
lower integrals `∫⁻ D^2` and `∫⁻ E^2`, each tending to `0` by the two `H^k(cell)`-continuity
hypotheses.  Finally the Bochner integral of the nonnegative density is the `toReal` of its lower
integral (no integrability is needed).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec Vc width)

/-- The jet density `∑_{|w| = j} ∑_k (∂_w f_k)²` on one cell (the integrand of `jetEnergy`). -/
def errSqDensity (c : ℝ) (j : ℕ) (f : Plane → Vec) (z : Plane) : ℝ :=
  ∑ w ∈ wordsOfLength j, ∑ k : Fin 2, wordComp w f k z * wordComp w f k z

/-- The lower integral `∫⁻_cell ((∂_w F_s,k - ∂_w F_0,k))²` appearing in `CellL2ContAt0`. -/
def cellSqLint (c : ℝ) (F : ℝ → Plane → Vec) (w : List Bool) (k : Fin 2) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in Cyl.cell c, ENNReal.ofReal ((wordComp w (F s) k z - wordComp w (F 0) k z) ^ 2)

theorem jetEnergy_eq_errSqDensity (c : ℝ) (j : ℕ) (f : Plane → Vec) :
    jetEnergy c j f = ∫ z in Cyl.cell c, errSqDensity c j f z :=
  rfl

theorem errSqDensity_nonneg (c : ℝ) (j : ℕ) (f : Plane → Vec) (z : Plane) :
    0 ≤ errSqDensity c j f z := by
  unfold errSqDensity
  exact Finset.sum_nonneg fun w _ => Finset.sum_nonneg fun k _ => mul_self_nonneg _

theorem contDiff_slice_v {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s) :
    ContDiff ℝ ∞ (tr.v s) := by
  have hf : ContDiff ℝ ∞ (fun z : Plane => (s, z)) := contDiff_const.prodMk contDiff_id
  have h := tr.isTrain.smooth_v.comp hf.contDiffOn (s := univ)
    (fun z _ => ⟨mem_Ici.2 hs, mem_univ z⟩)
  exact contDiffOn_univ.1 h

theorem contDiff_slice_Vc {ν c : ℝ} (hν : 0 < ν) (hc : 1 ≤ c) {s : ℝ} (hs : 0 ≤ s) :
    ContDiff ℝ ∞ (Vc ν c s) :=
  Spine.vcReg_contDiff_Vc (by linarith) (Spine.vcReg_width_pos hν hs)

theorem errSqDensity_continuous (c : ℝ) (j : ℕ) {f : Plane → Vec} (hf : ContDiff ℝ ∞ f) :
    Continuous (errSqDensity c j f) := by
  unfold errSqDensity
  refine continuous_finsetSum _ fun w _ => continuous_finsetSum _ fun k _ => ?_
  exact ((contDiff_wordComp hf w k).continuous).mul ((contDiff_wordComp hf w k).continuous)

/-- The word derivative of a difference of two smooth fields is the difference of the word
derivatives. -/
theorem wordComp_trainErr {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ}
    (hV : ContDiff ℝ ∞ (tr.v s)) (hW : ContDiff ℝ ∞ (Vc ν c s)) (w : List Bool) (k : Fin 2) :
    wordComp w (trainErr tr s) k = fun z => wordComp w (tr.v s) k z - wordComp w (Vc ν c s) k z := by
  funext z
  exact derivWord_sub_smooth (contDiff_comp_coord hV k) (contDiff_comp_coord hW k) w z

/-- Pointwise: `e_w,k = D - E` once `v(0) = V_c(0)`. -/
theorem wordComp_trainErr_sub {ν c : ℝ} (tr : B0140.TrainSol ν c) (h0 : tr.v 0 = Vc ν c 0)
    {s : ℝ} (hV : ContDiff ℝ ∞ (tr.v s)) (hW : ContDiff ℝ ∞ (Vc ν c s)) (w : List Bool)
    (k : Fin 2) (z : Plane) :
    wordComp w (trainErr tr s) k z =
      (wordComp w (tr.v s) k z - wordComp w (tr.v 0) k z) -
        (wordComp w (Vc ν c s) k z - wordComp w (Vc ν c 0) k z) := by
  have e0 : wordComp w (tr.v 0) k = wordComp w (Vc ν c 0) k := by rw [h0]
  rw [wordComp_trainErr tr hV hW w k, e0]
  ring

/-- Elementary: `(D - E)² ≤ 2 D² + 2 E²` at the level of lower integrals. -/
theorem ofReal_sq_sub_le (x D E : ℝ) (h : x = D - E) :
    ENNReal.ofReal (x * x) ≤ 2 * ENNReal.ofReal (D ^ 2) + 2 * ENNReal.ofReal (E ^ 2) := by
  have h1 : x * x ≤ 2 * D ^ 2 + 2 * E ^ 2 := by
    subst h
    nlinarith [sq_nonneg (D + E)]
  calc ENNReal.ofReal (x * x) ≤ ENNReal.ofReal (2 * D ^ 2 + 2 * E ^ 2) :=
        ENNReal.ofReal_le_ofReal h1
    _ = ENNReal.ofReal (2 * D ^ 2) + ENNReal.ofReal (2 * E ^ 2) :=
        ENNReal.ofReal_add (by positivity) (by positivity)
    _ = 2 * ENNReal.ofReal (D ^ 2) + 2 * ENNReal.ofReal (E ^ 2) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_ofNat]

theorem lintegral_two_add (μ : Measure Plane) {f g : Plane → ℝ≥0∞} (hf : Measurable f)
    (hg : Measurable g) :
    ∫⁻ z, (2 * f z + 2 * g z) ∂μ = 2 * ∫⁻ z, f z ∂μ + 2 * ∫⁻ z, g z ∂μ := by
  rw [lintegral_add_left (hf.const_mul 2), lintegral_const_mul 2 hf, lintegral_const_mul 2 hg]

theorem measurable_sq_ofReal {f g : Plane → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Measurable (fun z => ENNReal.ofReal ((f z - g z) ^ 2)) :=
  ((hf.sub hg).pow 2).measurable.ennreal_ofReal

/-- **The lower-integral bound.** For `s ≥ 0`, the lower integral of the jet density of the error
is at most the finite sum of the two lower integrals of the velocity and of `V_c^p`. -/
theorem lintegral_errSq_le {ν c : ℝ} (hν : 0 < ν) (hc : 1 ≤ c) (tr : B0140.TrainSol ν c)
    (h0 : tr.v 0 = Vc ν c 0) {s : ℝ} (hs : 0 ≤ s) (j : ℕ) :
    ∫⁻ z in Cyl.cell c, ENNReal.ofReal (errSqDensity c j (trainErr tr s) z) ≤
      ∑ w ∈ wordsOfLength j, ∑ k : Fin 2,
        (2 * cellSqLint c tr.v w k s + 2 * cellSqLint c (Vc ν c) w k s) := by
  have hV : ∀ t, 0 ≤ t → ContDiff ℝ ∞ (tr.v t) := fun t ht => contDiff_slice_v tr ht
  have hW : ∀ t, 0 ≤ t → ContDiff ℝ ∞ (Vc ν c t) := fun t ht => contDiff_slice_Vc hν hc ht
  have hV0 : ContDiff ℝ ∞ (tr.v 0) := hV 0 le_rfl
  have hW0 : ContDiff ℝ ∞ (Vc ν c 0) := hW 0 le_rfl
  have hpt : ∀ z, ENNReal.ofReal (errSqDensity c j (trainErr tr s) z) ≤
      ∑ w ∈ wordsOfLength j, ∑ k : Fin 2,
        (2 * ENNReal.ofReal ((wordComp w (tr.v s) k z - wordComp w (tr.v 0) k z) ^ 2) +
          2 * ENNReal.ofReal ((wordComp w (Vc ν c s) k z - wordComp w (Vc ν c 0) k z) ^ 2)) := by
    intro z
    unfold errSqDensity
    rw [ENNReal.ofReal_sum_of_nonneg (fun w _ => Finset.sum_nonneg fun k _ => mul_self_nonneg _)]
    refine Finset.sum_le_sum fun w _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => mul_self_nonneg _)]
    refine Finset.sum_le_sum fun k _ => ?_
    exact ofReal_sq_sub_le _ _ _ (wordComp_trainErr_sub tr h0 (hV s hs) (hW s hs) w k z)
  have hmeas : ∀ w : List Bool, ∀ k : Fin 2,
      Measurable (fun z => 2 * ENNReal.ofReal ((wordComp w (tr.v s) k z - wordComp w (tr.v 0) k z) ^ 2) +
          2 * ENNReal.ofReal ((wordComp w (Vc ν c s) k z - wordComp w (Vc ν c 0) k z) ^ 2)) := by
    intro w k
    have m1 := measurable_sq_ofReal (contDiff_wordComp (hV s hs) w k).continuous
      (contDiff_wordComp hV0 w k).continuous
    have m2 := measurable_sq_ofReal (contDiff_wordComp (hW s hs) w k).continuous
      (contDiff_wordComp hW0 w k).continuous
    exact (m1.const_mul 2).add (m2.const_mul 2)
  calc ∫⁻ z in Cyl.cell c, ENNReal.ofReal (errSqDensity c j (trainErr tr s) z)
      ≤ ∫⁻ z in Cyl.cell c, ∑ w ∈ wordsOfLength j, ∑ k : Fin 2,
        (2 * ENNReal.ofReal ((wordComp w (tr.v s) k z - wordComp w (tr.v 0) k z) ^ 2) +
          2 * ENNReal.ofReal ((wordComp w (Vc ν c s) k z - wordComp w (Vc ν c 0) k z) ^ 2)) :=
        lintegral_mono fun z => hpt z
    _ = ∑ w ∈ wordsOfLength j, ∑ k : Fin 2, ∫⁻ z in Cyl.cell c,
        (2 * ENNReal.ofReal ((wordComp w (tr.v s) k z - wordComp w (tr.v 0) k z) ^ 2) +
          2 * ENNReal.ofReal ((wordComp w (Vc ν c s) k z - wordComp w (Vc ν c 0) k z) ^ 2)) := by
        rw [lintegral_finsetSum _ fun w _ => Finset.measurable_sum _ fun k _ => hmeas w k]
        refine Finset.sum_congr rfl fun w _ => ?_
        exact lintegral_finsetSum _ fun k _ => hmeas w k
    _ = ∑ w ∈ wordsOfLength j, ∑ k : Fin 2,
        (2 * cellSqLint c tr.v w k s + 2 * cellSqLint c (Vc ν c) w k s) := by
        refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun k _ => ?_
        unfold cellSqLint
        have m1 := measurable_sq_ofReal (contDiff_wordComp (hV s hs) w k).continuous
          (contDiff_wordComp hV0 w k).continuous
        have m2 := measurable_sq_ofReal (contDiff_wordComp (hW s hs) w k).continuous
          (contDiff_wordComp hW0 w k).continuous
        exact lintegral_two_add _ m1 m2

/-- The right-hand side of `lintegral_errSq_le` tends to `0` as the age tends to `0` from the right,
once the two `H^k(cell)`-continuity statements hold. -/
theorem tendsto_bound_sum {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (hA : ∀ (w : List Bool) (k : Fin 2),
      Tendsto (cellSqLint c tr.v w k) (nhdsWithin (0 : ℝ) (Ici 0)) (𝓝 0))
    (hB : ∀ (w : List Bool) (k : Fin 2),
      Tendsto (cellSqLint c (Vc ν c) w k) (nhdsWithin (0 : ℝ) (Ici 0)) (𝓝 0))
    (j : ℕ) :
    Tendsto (fun s => ∑ w ∈ wordsOfLength j, ∑ k : Fin 2,
        (2 * cellSqLint c tr.v w k s + 2 * cellSqLint c (Vc ν c) w k s))
      (nhdsWithin (0 : ℝ) (Ici 0)) (𝓝 0) := by
  have key : ∀ (w : List Bool) (k : Fin 2),
      Tendsto (fun s => 2 * cellSqLint c tr.v w k s + 2 * cellSqLint c (Vc ν c) w k s)
        (nhdsWithin (0 : ℝ) (Ici 0)) (𝓝 0) := by
    intro w k
    have h1 := ENNReal.Tendsto.const_mul (hA w k) (Or.inr (show (2 : ℝ≥0∞) ≠ ⊤ by simp))
    have h2 := ENNReal.Tendsto.const_mul (hB w k) (Or.inr (show (2 : ℝ≥0∞) ≠ ⊤ by simp))
    simpa using h1.add h2
  have hsum := tendsto_finsetSum (wordsOfLength j) fun w _ =>
    tendsto_finsetSum (Finset.univ : Finset (Fin 2)) fun k _ => key w k
  simpa using hsum

/-- **Target.** Every jet energy of the train error tends to `0` at age `0` from the right, for
every BUC train, once `V_c^p` and every finite-energy train are `H^k(cell)`-continuous at age `0`. -/
theorem trainJetEnergyToZero_of_cont (hV : VcCellL2Cont) (hF : TrainFiniteEnergyClass) :
    TrainJetEnergyToZero := by
  intro ν c hν hc tr htr j
  have hVc : CellL2ContAt0 c (Vc ν c) := hV ν c hν hc
  have hTr : CellL2ContAt0 c tr.v := (hF ν c hν hc tr htr).cont
  have hA : ∀ (w : List Bool) (k : Fin 2),
      Tendsto (cellSqLint c tr.v w k) (nhdsWithin (0 : ℝ) (Ici 0)) (𝓝 0) :=
    fun w k => hTr w k
  have hB : ∀ (w : List Bool) (k : Fin 2),
      Tendsto (cellSqLint c (Vc ν c) w k) (nhdsWithin (0 : ℝ) (Ici 0)) (𝓝 0) :=
    fun w k => hVc w k
  have h0 : tr.v 0 = Vc ν c 0 := by
    funext z
    have hz : tr.v 0 z - Vc ν c 0 z = 0 := congrFun (trainErr_zero_local tr) z
    exact sub_eq_zero.1 hz
  -- the lower integral of the jet density of the error
  have hΨ : Tendsto (fun s => ∫⁻ z in Cyl.cell c, ENNReal.ofReal (errSqDensity c j (trainErr tr s) z))
      (nhdsWithin (0 : ℝ) (Ici 0)) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_bound_sum tr hA hB j) ?_ ?_
    · exact Eventually.of_forall fun s => by simp
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact lintegral_errSq_le hν hc tr h0 (Set.mem_Ici.1 hs) j
  have hT : Tendsto (fun s => (∫⁻ z in Cyl.cell c, ENNReal.ofReal (errSqDensity c j (trainErr tr s) z)).toReal)
      (nhdsWithin (0 : ℝ) (Ici 0)) (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hΨ
    rw [ENNReal.toReal_zero] at this
    exact this
  refine hT.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : 0 ≤ s := Set.mem_Ici.1 hs
  have hE : ContDiff ℝ ∞ (trainErr tr s) := by
    unfold trainErr
    exact (contDiff_slice_v tr hs').sub (contDiff_slice_Vc hν hc hs')
  rw [jetEnergy_eq_errSqDensity, integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun z => errSqDensity_nonneg c j _ z)
    (errSqDensity_continuous c j hE).aestronglyMeasurable]

end UnforcedLeray.Short.PartI
