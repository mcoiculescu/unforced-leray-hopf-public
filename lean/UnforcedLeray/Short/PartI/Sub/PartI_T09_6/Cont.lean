import UnforcedLeray.Short.PartI.Sub.PartI_T09_6
import UnforcedLeray.Short.PartI.Sub.PartI_T09_6.Bdd
import UnforcedLeray.Short.PartI.Sub.PartI_T09.JetSupBridge
import UnforcedLeray.Short.PartI.Sub.PartI_T09_5.RightCont
import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_2.Instance
import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_2_1.l2SqDiff
import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_2_1.l2SqMeas
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance.TimeDerivLocal

/-!
# Part I, task `PartI:T09/6/2` (`TrainErrGradCont`): continuity of `s ↦ ‖∇e(s)‖_∞`

Source of record: `the November 2 reference manuscript`, lines 270-288 (the train
is the finite-energy `BUC` solution, smooth for positive time) and line 355 (the continuity
argument for `‖∇e‖_∞`).

No pointwise time regularity of the pressure is needed; the argument runs in `L²(cell)` and returns
to sup norms by the cylinder interpolation inequality:

* at an age `s > 0`: the word derivatives of `∂_r e(r)` are in `L²(cell)` with norms bounded near
  `s`, at every age (`TrainTimeDerivJetLocalAllAges`, whose pressure part is the `L²` Leray
  estimate `trainPressureGradLocal_of`); the generic lemma `l2SqDiff` then gives
  `∫_cell (∂_w e_k(r) - ∂_w e_k(s))² ≤ (r - s)² K`, so every jet energy of `e(r) - e(s)` tends
  to `0` as `r → s`;
* at the age `0`: `e(0) = 0` and the jet energies of `e(r)` tend to `0` as `r → 0+`
  (`trainJetEnergyRightCont_proof`);
* the sup bridge (`jetSupBridge_proof`, order `1`) bounds `|∂_β (e(r) - e(s))_k|` uniformly in
  `z` by `supRhs` of the jet energies of orders `1, 2, 3` of `e(r) - e(s)`, which tends to `0`;
* `|‖∇e(r)‖_∞ - ‖∇e(s)‖_∞|` is at most that uniform bound (`trainErrGradBdd_proof` gives the
  finiteness of both suprema).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec Vc width)

/-- The time derivative of the error has locally uniformly `L²` word derivatives at every age
(composition of the proved leaves of `PartI:T08/4/1/1`; no width condition). -/
theorem tgc_timeDerivLocal : TrainTimeDerivJetLocalAllAges :=
  trainTimeDerivJetLocalAllAges_of
    (trainLapLocal_of_err trainErrJetLocalL2_proof)
    (trainAdvLocal_of trainErrJetLocalL2_proof trainErrSupLocal_proof)
    (trainPressureGradLocal_of
      (trainAdvLocal_of trainErrJetLocalL2_proof trainErrSupLocal_proof)
      trainStressDivLocal_proof)
    trainStressDivLocal_proof

/-- A word derivative of a difference of smooth fields. -/
theorem tgc_wordComp_sub {f g : Plane → Vec} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (w : List Bool) (k : Fin 2) (z : Plane) :
    wordComp w (fun x => f x - g x) k z = wordComp w f k z - wordComp w g k z := by
  have hfk : ContDiff ℝ ∞ (fun x => f x k) :=
    (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hf
  have hgk : ContDiff ℝ ∞ (fun x => g x k) :=
    (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hg
  unfold wordComp
  have e : (fun x => (f x - g x) k) = fun x => f x k - g x k :=
    funext fun x => by rw [PiLp.sub_apply]
  rw [e]
  exact derivWord_sub_smooth hfk hgk w z

/-- The class `CellSmoothL2` is closed under differences. -/
theorem tgc_cellSmoothL2_sub {c : ℝ} {f g : Plane → Vec} (hf : CellSmoothL2 c f)
    (hg : CellSmoothL2 c g) : CellSmoothL2 c (fun z => f z - g z) := by
  refine ⟨hf.1.sub hg.1, ?_, ?_⟩
  · intro z
    show f (z.1 + c, z.2) - g (z.1 + c, z.2) = f z - g z
    rw [hf.2.1 z, hg.2.1 z]
  · intro w k
    have e : wordComp w (fun z => f z - g z) k = fun z => wordComp w f k z - wordComp w g k z :=
      funext (tgc_wordComp_sub hf.1 hg.1 w k)
    rw [e]
    exact (hf.2.2 w k).sub (hg.2.2 w k)

/-- The error `e(r)` is smooth, `c`-periodic, with all word derivatives in `L²(cell)`, at every
age `r ≥ 0`. -/
theorem tgc_cellSmoothL2 {ν c : ℝ} (hν : 0 < ν) (hc : 1 ≤ c) (tr : B0140.TrainSol ν c)
    (htr : IsBUCTrain tr) {r : ℝ} (hr : 0 ≤ r) : CellSmoothL2 c (trainErr tr r) := by
  rcases hr.lt_or_eq with hr | hr
  · have hL := trainErrJetLocalL2_proof ν c hν hc tr htr
    refine ⟨hL.1 r hr, ?_, ?_⟩
    · intro z
      show tr.v r (z.1 + c, z.2) - Vc ν c r (z.1 + c, z.2) = tr.v r z - Vc ν c r z
      rw [tr.isTrain.periodic_v r hr.le z, Train.Vc_periodic ν c r z]
    · intro w k
      obtain ⟨ε, hε, K, hK⟩ := hL.2 r hr w k
      exact (hK r hr (by simpa using hε)).1
  · subst hr
    rw [trainErr_zero_local]
    exact cellSmoothL2_zero_local c

/-- A jet energy as a finite sum of cell integrals of squares. -/
theorem tgc_jetEnergy_eq {c : ℝ} {f : Plane → Vec} (j : ℕ)
    (hf : ∀ (w : List Bool) (k : Fin 2), MemLp (wordComp w f k) 2 (Cyl.cellμ c)) :
    jetEnergy c j f = ∑ w ∈ wordsOfLength j, ∑ k : Fin 2,
      ∫ z in Cyl.cell c, (wordComp w f k z) ^ 2 := by
  have hi : ∀ (w : List Bool) (k : Fin 2),
      Integrable (fun z => wordComp w f k z * wordComp w f k z) (volume.restrict (Cyl.cell c)) := by
    intro w k
    have h2 : Integrable (fun z => wordComp w f k z ^ 2) (Cyl.cellμ c) := (hf w k).integrable_sq
    refine h2.congr (Eventually.of_forall fun z => ?_)
    show wordComp w f k z ^ 2 = wordComp w f k z * wordComp w f k z
    ring
  unfold jetEnergy jetPair
  rw [integral_finsetSum _ (fun w _ => integrable_finsetSum _ (fun k _ => hi w k))]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [integral_finsetSum _ (fun k _ => hi w k)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  congr 1
  funext z
  ring

open UnforcedLeray.Short.PartI.TrainWordEnergyInstance in
/-- At an age `s > 0`, each word derivative of `e(r)` converges to that of `e(s)` in `L²(cell)`:
`∫_cell (∂_w e_k(r) - ∂_w e_k(s))² ≤ (r - s)² K` near `s` (`l2SqDiff`). -/
theorem tgc_word_tendsto {ν c : ℝ} (hν : 0 < ν) (hc : 1 ≤ c) (tr : B0140.TrainSol ν c)
    (htr : IsBUCTrain tr) {s : ℝ} (hs : 0 < s) (w : List Bool) (k : Fin 2) :
    Tendsto (fun r => ∫ z in Cyl.cell c,
        (wordComp w (trainErr tr r) k z - wordComp w (trainErr tr s) k z) ^ 2) (𝓝 s) (𝓝 0) := by
  obtain ⟨ε0, hε0, K0, hK⟩ := tgc_timeDerivLocal ν c hν hc tr htr s hs w k
  have hεpos : 0 < min ε0 (s / 4) := lt_min hε0 (by linarith)
  have hC : ∀ z, ContDiff ℝ 1 (fun r => wordComp w (trainErr tr (loc s r)) k z) := fun z =>
    ContDiffOn.comp_contDiff ((wordComp_time_smooth hν hc tr w k z).of_le
      (by exact_mod_cast le_top)) ((contDiff_loc s).of_le (by exact_mod_cast le_top))
      (fun x => loc_pos hs x)
  have hF : MemLp (fun z => wordComp w (trainErr tr (loc s s)) k z) 2 (Cyl.cellμ c) := by
    rw [loc_self]
    exact (tgc_cellSmoothL2 hν hc tr htr hs.le).2.2 w k
  have hD : ∀ r, |r - s| < min ε0 (s / 4) →
      MemLp (fun z => deriv (fun t => wordComp w (trainErr tr (loc s t)) k z) r) 2
        (Cyl.cellμ c) ∧
      ∫ z, (deriv (fun t => wordComp w (trainErr tr (loc s t)) k z) r) ^ 2 ∂(Cyl.cellμ c)
        ≤ K0 := by
    intro r hr
    have hr1 : |r - s| < ε0 := lt_of_lt_of_le hr (min_le_left _ _)
    have hr2 : |r - s| < s / 4 := lt_of_lt_of_le hr (min_le_right _ _)
    have hr34 : 3 * s / 4 < r := by have := (abs_lt.1 hr2).1; linarith
    obtain ⟨hm, hint⟩ := hK r (by linarith) hr1
    simp only [wordComp_loc_deriv hν hc tr w k hs hr34]
    exact ⟨hm, hint⟩
  have hyp : L2SqDeriv.Hyp (μ := Cyl.cellμ c)
      (fun r z => wordComp w (trainErr tr (loc s r)) k z) s (min ε0 (s / 4)) K0 :=
    ⟨hεpos, hC, hF, hD⟩
  have hmeas := l2SqMeas (μ := Cyl.cellμ c) _ s _ K0 hyp
  have hdiff := l2SqDiff (μ := Cyl.cellμ c) _ s _ K0 hyp hmeas
  have hev : ∀ᶠ r in 𝓝 s, ∫ z in Cyl.cell c,
      (wordComp w (trainErr tr r) k z - wordComp w (trainErr tr s) k z) ^ 2 ≤ (r - s) ^ 2 * K0 := by
    filter_upwards [Metric.ball_mem_nhds s hεpos] with r hr
    have hr' : |r - s| < min ε0 (s / 4) := by
      rw [Metric.mem_ball, Real.dist_eq] at hr
      exact hr
    have hr2 : |r - s| < s / 4 := lt_of_lt_of_le hr' (min_le_right _ _)
    have hr34 : 3 * s / 4 < r := by have := (abs_lt.1 hr2).1; linarith
    have h := (hdiff r hr').2
    simp only [loc_eq_id hs hr34, loc_self] at h
    exact h
  have hlim : Tendsto (fun r : ℝ => (r - s) ^ 2 * K0) (𝓝 s) (𝓝 0) := by
    have h : Tendsto (fun r : ℝ => (r - s) ^ 2 * K0) (𝓝 s) (𝓝 ((s - s) ^ 2 * K0)) :=
      (((continuous_id.sub continuous_const).pow 2).mul continuous_const).tendsto s
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ hev
  exact Eventually.of_forall (fun r => integral_nonneg (fun z => sq_nonneg _))

/-- At an age `s > 0`, every jet energy of `e(r) - e(s)` tends to `0` as `r → s`. -/
theorem tgc_jet_tendsto_pos {ν c : ℝ} (hν : 0 < ν) (hc : 1 ≤ c) (tr : B0140.TrainSol ν c)
    (htr : IsBUCTrain tr) {s : ℝ} (hs : 0 < s) (j : ℕ) :
    Tendsto (fun r => jetEnergy c j (fun z => trainErr tr r z - trainErr tr s z)) (𝓝 s)
      (𝓝 0) := by
  have hsum : Tendsto (fun r => ∑ w ∈ wordsOfLength j, ∑ k : Fin 2, ∫ z in Cyl.cell c,
      (wordComp w (trainErr tr r) k z - wordComp w (trainErr tr s) k z) ^ 2) (𝓝 s) (𝓝 0) := by
    have h := tendsto_finsetSum (wordsOfLength j) (fun w _ =>
      tendsto_finsetSum (Finset.univ : Finset (Fin 2))
        (fun k _ => tgc_word_tendsto hν hc tr htr hs w k))
    simpa using h
  refine hsum.congr' ?_
  filter_upwards [Ioi_mem_nhds hs] with r hr
  have hr0 : (0 : ℝ) < r := hr
  have hsr := tgc_cellSmoothL2 hν hc tr htr hr0.le
  have hss := tgc_cellSmoothL2 hν hc tr htr hs.le
  rw [tgc_jetEnergy_eq j (tgc_cellSmoothL2_sub hsr hss).2.2]
  refine Finset.sum_congr rfl (fun w _ => Finset.sum_congr rfl (fun k _ => ?_))
  congr 1
  funext z
  rw [tgc_wordComp_sub hsr.1 hss.1]

/-- At every age `s ≥ 0`, every jet energy of `e(r) - e(s)` tends to `0` as `r → s` in `[0, ∞)`. -/
theorem tgc_jet_tendsto {ν c : ℝ} (hν : 0 < ν) (hc : 1 ≤ c) (tr : B0140.TrainSol ν c)
    (htr : IsBUCTrain tr) {s : ℝ} (hs : 0 ≤ s) (j : ℕ) :
    Tendsto (fun r => jetEnergy c j (fun z => trainErr tr r z - trainErr tr s z)) (𝓝[Ici 0] s)
      (𝓝 0) := by
  rcases hs.lt_or_eq with hs | hs
  · exact (tgc_jet_tendsto_pos hν hc tr htr hs j).mono_left nhdsWithin_le_nhds
  · subst hs
    have e : ∀ r : ℝ, (fun z => trainErr tr r z - trainErr tr 0 z) = trainErr tr r := by
      intro r
      funext z
      rw [trainErr_zero_local]
      simp
    simp only [e]
    have h := trainJetEnergyRightCont_proof ν c hν hc tr htr j
    have h0 : jetEnergy c j (trainErr tr 0) = 0 := by
      rw [trainErr_zero_local]
      exact jetEnergy_zero_local c j
    rw [ContinuousWithinAt, h0] at h
    exact h

/-- `supRhs` tends to `0` when its three jet arguments do. -/
theorem tgc_supRhs_tendsto {α : Type*} {l : Filter α} (C c : ℝ) {f1 f2 f3 : α → ℝ}
    (h1 : Tendsto f1 l (𝓝 0)) (h2 : Tendsto f2 l (𝓝 0)) (h3 : Tendsto f3 l (𝓝 0)) :
    Tendsto (fun x => supRhs C c (f1 x) (f2 x) (f3 x)) l (𝓝 0) := by
  have hp : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have e1 : Tendsto (fun x => (Real.sqrt (f1 x) * Real.sqrt (f3 x)) ^ (1 / 2 : ℝ)) l
      (𝓝 ((Real.sqrt 0 * Real.sqrt 0) ^ (1 / 2 : ℝ))) :=
    (h1.sqrt.mul h3.sqrt).rpow_const (Or.inr hp)
  have e2 : Tendsto (fun x => (Real.sqrt (f1 x) * Real.sqrt (f2 x)) ^ (1 / 2 : ℝ)) l
      (𝓝 ((Real.sqrt 0 * Real.sqrt 0) ^ (1 / 2 : ℝ))) :=
    (h1.sqrt.mul h2.sqrt).rpow_const (Or.inr hp)
  have e3 := (e1.add (e2.const_mul (c ^ (-(1 / 2 : ℝ))))).const_mul C
  have hz : (Real.sqrt 0 * Real.sqrt 0) ^ (1 / 2 : ℝ) = 0 := by
    rw [Real.sqrt_zero, mul_zero, Real.zero_rpow (by norm_num)]
  rw [hz, mul_zero, add_zero, mul_zero] at e3
  exact e3

/-- `‖∇e(r)‖_∞ ≤ ‖∇e(s)‖_∞ + B` when the first partials differ by at most `B` everywhere. -/
theorem tgc_gradErrSup_le {ν c : ℝ} (tr : B0140.TrainSol ν c) {r s B : ℝ}
    (hbdd : BddAbove {x : ℝ | ∃ (β : Bool) (k : Fin 2) (z : Plane),
      x = |wordComp [β] (trainErr tr s) k z|})
    (h : ∀ (β : Bool) (k : Fin 2) (z : Plane),
      |wordComp [β] (trainErr tr r) k z - wordComp [β] (trainErr tr s) k z| ≤ B) :
    gradErrSup tr r ≤ gradErrSup tr s + B := by
  unfold gradErrSup
  refine csSup_le ⟨|wordComp [true] (trainErr tr r) 0 0|, true, 0, 0, rfl⟩ ?_
  rintro x ⟨β, k, z, rfl⟩
  have h1 : |wordComp [β] (trainErr tr s) k z| ≤ sSup {x : ℝ | ∃ (β : Bool) (k : Fin 2)
      (z : Plane), x = |wordComp [β] (trainErr tr s) k z|} := le_csSup hbdd ⟨β, k, z, rfl⟩
  have h2 := h β k z
  have h3 := abs_sub_abs_le_abs_sub (wordComp [β] (trainErr tr r) k z)
    (wordComp [β] (trainErr tr s) k z)
  linarith

/-- **`TrainErrGradCont`** (source lines 270-288, 355): for a BUC train, `s ↦ ‖∇e(s)‖_∞` is
continuous on `[0, ∞)`. -/
theorem trainErrGradCont_proof : TrainErrGradCont := by
  intro ν c hν hc tr htr s hs
  have hs0 : (0 : ℝ) ≤ s := hs
  obtain ⟨C, -, hC⟩ := jetSupBridge_proof 1
  have hJt : ∀ j : ℕ, Tendsto
      (fun r => jetEnergy c j (fun z => trainErr tr r z - trainErr tr s z)) (𝓝[Ici 0] s)
      (𝓝 0) := fun j => tgc_jet_tendsto hν hc tr htr hs0 j
  have hS := tgc_supRhs_tendsto C c (hJt 1) (hJt (1 + 1)) (hJt (1 + 2))
  have hbound : ∀ r ∈ Ici (0 : ℝ), |gradErrSup tr r - gradErrSup tr s| ≤
      supRhs C c (jetEnergy c 1 (fun z => trainErr tr r z - trainErr tr s z))
        (jetEnergy c (1 + 1) (fun z => trainErr tr r z - trainErr tr s z))
        (jetEnergy c (1 + 2) (fun z => trainErr tr r z - trainErr tr s z)) := by
    intro r hr
    have hr0 : (0 : ℝ) ≤ r := hr
    have hsr := tgc_cellSmoothL2 hν hc tr htr hr0
    have hss := tgc_cellSmoothL2 hν hc tr htr hs0
    have hpt : ∀ (β : Bool) (k : Fin 2) (z : Plane),
        |wordComp [β] (trainErr tr r) k z - wordComp [β] (trainErr tr s) k z| ≤
          supRhs C c (jetEnergy c 1 (fun z => trainErr tr r z - trainErr tr s z))
            (jetEnergy c (1 + 1) (fun z => trainErr tr r z - trainErr tr s z))
            (jetEnergy c (1 + 2) (fun z => trainErr tr r z - trainErr tr s z)) := by
      intro β k z
      have h := (hC c hc _ (tgc_cellSmoothL2_sub hsr hss)).1 [β] rfl k z
      rw [tgc_wordComp_sub hsr.1 hss.1] at h
      exact h
    have hbr := trainErrGradBdd_proof ν c hν hc tr htr r hr0
    have hbs := trainErrGradBdd_proof ν c hν hc tr htr s hs0
    have hle1 := tgc_gradErrSup_le tr hbs hpt
    have hle2 := tgc_gradErrSup_le tr hbr (fun β k z => by
      rw [abs_sub_comm]
      exact hpt β k z)
    rw [abs_sub_le_iff]
    constructor <;> linarith
  show Tendsto (gradErrSup tr) (𝓝[Ici 0] s) (𝓝 (gradErrSup tr s))
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_ hS
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [Real.norm_eq_abs]
  exact hbound r hr

end UnforcedLeray.Short.PartI
