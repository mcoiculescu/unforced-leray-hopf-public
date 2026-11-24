import UnforcedLeray.Short.PartI.Sub.PartI_T15
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanDecay.DuhamelSplit.LineHeatFTC

/-!
# Smoothness, `BUC` bounds, and pointwise 1D heat Duhamel split for `overlapMeanStream`

For `ν > 0`, `c > 1`, and a `BUC` train `tr : B0140.TrainSol ν c`:
1. Both `overlapMeanStream tr` and `overlapStressProfile tr` are jointly `C^∞` on an open
   neighborhood `overlapTimeIoi ν c ×ˢ univ` of `[0, ∞) × ℝ`, so all their spatial derivatives
   `iteratedDeriv k` are jointly `C^∞` on `[0, ∞) × ℝ`.
2. On every compact time interval `[0, T]`, `IsBUCTrain.deriv_bound` and `tr.isTrain.stream_decay`
   provide a uniform bound `M` on `iteratedDeriv k (overlapMeanStream tr t) Y`,
   `deriv (fun r => overlapMeanStream tr r Y) t`, and `iteratedDeriv k (overlapStressProfile tr t) Y`
   for all `k ≤ N`, `t ∈ [0, T]`, and `Y ∈ ℝ`.
3. Combining `lineHeat_duhamel_of_pde`, `iteratedDeriv_lineDuhamel_one`, and
   `iteratedDeriv_lineHeat_data` gives the pointwise Duhamel split at `T / 2` for
   `iteratedDeriv j b`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI.DuhamelSplit

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec jet)
open UnforcedLeray.Heat (lineHeat lineDuhamel)

/-! ### 1. Open time neighborhood of `[0, ∞)` and joint smoothness -/

/-- Open time ray `( -s_c ν / c², ∞ )` containing `[0, ∞)` on which `s_c + c² t / ν > 0`. -/
def overlapTimeIoi (ν c : ℝ) : Set ℝ :=
  Ioi (-(B0146.overlapAge ν c * ν / c ^ 2))

theorem Ici_subset_overlapTimeIoi {ν c : ℝ} (hν : 0 < ν) (hc : 1 < c) :
    Ici (0 : ℝ) ⊆ overlapTimeIoi ν c := by
  intro t ht
  rw [mem_Ici] at ht
  rw [overlapTimeIoi, mem_Ioi]
  have hs0 : 0 < B0146.overlapAge ν c := by
    unfold B0146.overlapAge
    exact div_pos (by nlinarith) hν
  have hc0 : 0 < c := zero_lt_one.trans hc
  have hneg : -(B0146.overlapAge ν c * ν / c ^ 2) < 0 :=
    neg_neg_of_pos (div_pos (mul_pos hs0 hν) (sq_pos_of_pos hc0))
  linarith

theorem overlapAge_pos_of_mem_overlapTimeIoi {ν c t : ℝ} (hν : 0 < ν) (hc : 1 < c)
    (ht : t ∈ overlapTimeIoi ν c) :
    0 < B0146.overlapAge ν c + c ^ 2 * t / ν := by
  rw [overlapTimeIoi, mem_Ioi] at ht
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos (zero_lt_one.trans hc)
  have hmul : -(B0146.overlapAge ν c * ν / c ^ 2) * (c ^ 2 / ν) < t * (c ^ 2 / ν) :=
    mul_lt_mul_of_pos_right ht (div_pos hc2 hν)
  have hsimp : -(B0146.overlapAge ν c * ν / c ^ 2) * (c ^ 2 / ν) = -B0146.overlapAge ν c := by
    field_simp [hν.ne', hc2.ne']
  rw [hsimp] at hmul
  have h2 : t * (c ^ 2 / ν) = c ^ 2 * t / ν := by ring
  linarith

theorem contDiffOn_overlapMeanStream_open {ν c : ℝ} (hν : 0 < ν) (hc : 1 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr) :
    ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => overlapMeanStream tr x.1 x.2)
      (overlapTimeIoi ν c ×ˢ univ) := by
  have hc0 : 0 < c := zero_lt_one.trans hc
  have hS := (trainMeanEquations_proof ν c hν hc0 tr htr).1
  have hΦ : ContDiff ℝ ∞ (fun x : ℝ × ℝ =>
      (B0146.overlapAge ν c + c ^ 2 * x.1 / ν, c * x.2)) := by
    refine ContDiff.prodMk ?_ ?_
    · exact contDiff_const.add ((contDiff_const.mul contDiff_fst).div_const ν)
    · exact contDiff_const.mul contDiff_snd
  have hmaps : MapsTo (fun x : ℝ × ℝ => (B0146.overlapAge ν c + c ^ 2 * x.1 / ν, c * x.2))
      (overlapTimeIoi ν c ×ˢ univ) (Ioi 0 ×ˢ univ) := by
    intro x hx
    exact ⟨overlapAge_pos_of_mem_overlapTimeIoi hν hc hx.1, mem_univ _⟩
  exact (hS.comp hΦ.contDiffOn hmaps).const_smul (c ^ 2)

theorem contDiffOn_deriv_snd {I : Set ℝ} (hI : IsOpen I) {u : ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => u x.1 x.2) (I ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => deriv (u x.1) x.2) (I ×ˢ univ) := by
  have hopen : IsOpen (I ×ˢ (univ : Set ℝ)) := hI.prod isOpen_univ
  have hfd : ContDiffOn ℝ ∞
      (fun x : ℝ × ℝ => fderiv ℝ (fun y : ℝ × ℝ => u y.1 y.2) x (0, 1)) (I ×ˢ univ) :=
    (hu.fderiv_of_isOpen hopen (by simp)).clm_apply contDiffOn_const
  refine hfd.congr fun x hx => ?_
  have hd : DifferentiableAt ℝ (fun y : ℝ × ℝ => u y.1 y.2) x :=
    (hu.contDiffAt (hopen.mem_nhds hx)).differentiableAt (by simp)
  exact (hd.hasFDerivAt.comp_hasDerivAt x.2
    ((hasDerivAt_const x.2 x.1).prodMk (hasDerivAt_id x.2))).deriv

theorem contDiffOn_iteratedDeriv_snd_open {I : Set ℝ} (hI : IsOpen I) {u : ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => u x.1 x.2) (I ×ˢ univ)) (k : ℕ) :
    ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => iteratedDeriv k (u x.1) x.2) (I ×ˢ univ) := by
  induction k with
  | zero =>
    simpa [iteratedDeriv_zero] using hu
  | succ k ih =>
    have hstep := contDiffOn_deriv_snd hI (u := fun t Y => iteratedDeriv k (u t) Y) ih
    refine hstep.congr fun x _ => ?_
    rw [iteratedDeriv_succ]

theorem contDiffOn_deriv_fst {I : Set ℝ} (hI : IsOpen I) {u : ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => u x.1 x.2) (I ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => deriv (fun r => u r x.2) x.1) (I ×ˢ univ) := by
  have hopen : IsOpen (I ×ˢ (univ : Set ℝ)) := hI.prod isOpen_univ
  have hfd : ContDiffOn ℝ ∞
      (fun x : ℝ × ℝ => fderiv ℝ (fun y : ℝ × ℝ => u y.1 y.2) x (1, 0)) (I ×ˢ univ) :=
    (hu.fderiv_of_isOpen hopen (by simp)).clm_apply contDiffOn_const
  refine hfd.congr fun x hx => ?_
  have hd : DifferentiableAt ℝ (fun y : ℝ × ℝ => u y.1 y.2) x :=
    (hu.contDiffAt (hopen.mem_nhds hx)).differentiableAt (by simp)
  exact (hd.hasFDerivAt.comp_hasDerivAt x.1
    ((hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2))).deriv

theorem overlapMeanStream_pde_profile {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr) {t : ℝ}
    (hs : 0 < B0146.overlapAge ν c + c ^ 2 * t / ν) (Y : ℝ) :
    deriv (fun r => overlapMeanStream tr r Y) t -
      deriv (deriv (overlapMeanStream tr t)) Y =
      eC ν c * overlapStressProfile tr t Y :=
  overlapMeanStream_eq hν hc tr htr hs Y

theorem contDiffOn_overlapStressProfile_open {ν c : ℝ} (hν : 0 < ν) (hc : 1 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr) :
    ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => overlapStressProfile tr x.1 x.2)
      (overlapTimeIoi ν c ×ˢ univ) := by
  have hI : IsOpen (overlapTimeIoi ν c) := isOpen_Ioi
  have hu := contDiffOn_overlapMeanStream_open hν hc tr htr
  have hut := contDiffOn_deriv_fst hI hu
  have huyy := contDiffOn_deriv_snd hI (u := fun t Y => deriv (overlapMeanStream tr t) Y)
    (contDiffOn_deriv_snd hI hu)
  have hsub : ContDiffOn ℝ ∞
      (fun x : ℝ × ℝ => (eC ν c)⁻¹ *
        (deriv (fun r => overlapMeanStream tr r x.2) x.1 -
          deriv (deriv (overlapMeanStream tr x.1)) x.2))
      (overlapTimeIoi ν c ×ˢ univ) :=
    contDiffOn_const.mul (hut.sub huyy)
  have hc0 : 0 < c := zero_lt_one.trans hc
  have heC : eC ν c ≠ 0 := by
    unfold eC
    positivity
  refine hsub.congr fun x hx => ?_
  have hs : 0 < B0146.overlapAge ν c + c ^ 2 * x.1 / ν :=
    overlapAge_pos_of_mem_overlapTimeIoi hν hc hx.1
  have hpde := overlapMeanStream_pde_profile hν hc0 tr htr hs x.2
  symm
  rw [hpde, inv_mul_cancel_left₀ heC]

theorem contDiff_overlapStressProfile_slice {ν c : ℝ} (hν : 0 < ν) (hc : 1 < c)
    (tr : B0140.TrainSol ν c) (_htr : IsBUCTrain tr) {t : ℝ} (ht : 0 ≤ t) :
    ContDiff ℝ ∞ (overlapStressProfile tr t) := by
  have hU : ContDiff ℝ ∞ (overlapField ν c tr.v t) :=
    PartI_T15.contDiff_overlapField_slice tr (overlapAge_add_pos hν hc ht).le
  have hU_fluct : ContDiff ℝ ∞ (hfluct 1 (overlapField ν c tr.v t)) :=
    PartI_T15.contDiff_hfluct_unit hU
  have hprod : ContDiff ℝ ∞
      (fun z : Plane => hfluct 1 (overlapField ν c tr.v t) z 0 *
        hfluct 1 (overlapField ν c tr.v t) z 1) :=
    ((EuclideanSpace.proj (0 : Fin 2)).contDiff.comp hU_fluct).mul
      ((EuclideanSpace.proj (1 : Fin 2)).contDiff.comp hU_fluct)
  exact PartI_T15.contDiff_hmean_unit hprod

theorem contDiff_overlapMeanStream_slice {ν c : ℝ} (hν : 0 < ν) (hc : 1 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr) {t : ℝ} (ht : 0 ≤ t) :
    ContDiff ℝ ∞ (overlapMeanStream tr t) := by
  have hcd := overlapMeanStream_contDiffOn hν hc tr htr
  have hmap : ContDiff ℝ ∞ (fun Y : ℝ => ((t, Y) : ℝ × ℝ)) :=
    contDiff_const.prodMk contDiff_id
  exact contDiffOn_univ.1 (hcd.comp hmap.contDiffOn (fun Y _ => ⟨ht, mem_univ Y⟩))

/-! ### 2. Uniform spatial and temporal bounds on `[0, T] × ℝ` from `IsBUCTrain` -/

/-- Uniform bound on `‖jet i (overlapField ν c tr.v t) z‖` for `t ∈ [0, T]`, `i ≤ N`, `z ∈ ℝ²`. -/
theorem exists_jet_overlapField_bound {ν c : ℝ} (hν : 0 < ν) (hc : 1 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr) {T : ℝ} (hT : 0 ≤ T) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc 0 T, ∀ i ≤ N, ∀ z : Plane,
      ‖jet i (overlapField ν c tr.v t) z‖ ≤ M := by
  have hc0 : 0 < c := zero_lt_one.trans hc
  set S : ℝ := B0146.overlapAge ν c + c ^ 2 * T / ν
  have hS : 0 ≤ S := (overlapAge_add_pos hν hc hT).le
  choose f hf using fun i : ℕ => IsBUCTrain.deriv_bound htr hS i
  set M : ℝ := ∑ i ∈ Finset.range (N + 1), c ^ 3 * c ^ i * |f i|
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ => by positivity
  refine ⟨M, hM0, fun t ht i hi z => ?_⟩
  have hs_mem : B0146.overlapAge ν c + c ^ 2 * t / ν ∈ Icc 0 S := by
    refine ⟨(overlapAge_add_pos hν hc ht.1).le, ?_⟩
    dsimp [S]
    have : c ^ 2 * t / ν ≤ c ^ 2 * T / ν :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ht.2 (sq_nonneg c)) hν.le
    linarith
  have hscale : overlapField ν c tr.v t =
      scaleField c (tr.v (B0146.overlapAge ν c + c ^ 2 * t / ν)) := rfl
  have hjet := jet_scaleField i c (tr.v (B0146.overlapAge ν c + c ^ 2 * t / ν)) z
  rw [← hscale] at hjet
  have hnorm : ‖jet i (overlapField ν c tr.v t) z‖ =
      c ^ 3 * c ^ i * ‖jet i (tr.v (B0146.overlapAge ν c + c ^ 2 * t / ν)) (c • z)‖ := by
    rw [hjet, norm_smul, Real.norm_of_nonneg (by positivity)]
  have hv_le : ‖jet i (tr.v (B0146.overlapAge ν c + c ^ 2 * t / ν)) (c • z)‖ ≤ |f i| :=
    (hf i _ hs_mem (c • z)).trans (le_abs_self _)
  calc ‖jet i (overlapField ν c tr.v t) z‖
      ≤ c ^ 3 * c ^ i * |f i| := by
        rw [hnorm]
        exact mul_le_mul_of_nonneg_left hv_le (by positivity)
    _ ≤ M := Finset.single_le_sum (f := fun j => c ^ 3 * c ^ j * |f j|)
        (fun j _ => by positivity) (Finset.mem_range.2 (Nat.lt_succ_of_le hi))

private theorem norm_proj_le_one (i : Fin 2) :
    ‖(EuclideanSpace.proj i : Vec →L[ℝ] ℝ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
    simpa using PiLp.norm_apply_le v i

private theorem norm_iteratedFDeriv_coord_le {U : Plane → Vec} (hU : ContDiff ℝ ∞ U)
    (i : Fin 2) (j : ℕ) (z : Plane) :
    ‖iteratedFDeriv ℝ j (fun w : Plane => U w i) z‖ ≤ ‖jet j U z‖ := by
  have h := (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).norm_iteratedFDeriv_comp_left
    (f := U) (x := z) (N := (∞ : WithTop ℕ∞)) (n := j) hU.contDiffAt (mod_cast le_top)
  calc ‖iteratedFDeriv ℝ j (fun w : Plane => U w i) z‖
      ≤ ‖(EuclideanSpace.proj i : Vec →L[ℝ] ℝ)‖ * ‖iteratedFDeriv ℝ j U z‖ := h
    _ ≤ 1 * ‖iteratedFDeriv ℝ j U z‖ :=
        mul_le_mul_of_nonneg_right (norm_proj_le_one i) (norm_nonneg _)
    _ = ‖jet j U z‖ := by rw [one_mul]; rfl

/-- Uniform bound on `|iteratedDeriv k (overlapStressProfile tr t) Y|` for `t ∈ [0, T]`, `k ≤ N`. -/
theorem exists_overlapStressProfile_deriv_bound {ν c : ℝ} (hν : 0 < ν) (hc : 1 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr) {T : ℝ} (hT : 0 ≤ T) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc 0 T, ∀ k ≤ N, ∀ Y : ℝ,
      |iteratedDeriv k (overlapStressProfile tr t) Y| ≤ M := by
  have hc0 : 0 < c := zero_lt_one.trans hc
  obtain ⟨M₀, hM₀, hjet⟩ := exists_jet_overlapField_bound hν hc tr htr hT N
  set B : ℝ := (N + 1 : ℝ) * 2 ^ N * M₀ ^ 2
  have hB0 : 0 ≤ B := by positivity
  refine ⟨B, hB0, fun t ht k hk Y => ?_⟩
  set U := overlapField ν c tr.v t
  have hs : 0 < B0146.overlapAge ν c + c ^ 2 * t / ν := overlapAge_add_pos hν hc ht.1
  have hU : ContDiff ℝ ∞ U := PartI_T15.contDiff_overlapField_slice tr hs.le
  have hU0 : ContDiff ℝ ∞ (fun w : Plane => U w 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hU
  have hU1 : ContDiff ℝ ∞ (fun w : Plane => U w 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec →L[ℝ] ℝ).contDiff.comp hU
  set Φ : Plane → ℝ := fun w => U w 0 * U w 1
  have hΦ : ContDiff ℝ ∞ Φ := hU0.mul hU1
  have hg_eq : overlapStressProfile tr t = hmean 1 Φ := by
    funext Y'
    unfold overlapStressProfile
    rw [← overlapMeanStress_eq_fluct hν hc0 tr htr hs Y']
    have hU_prod : Φ =
        fun y : Plane => (c ^ 6 : ℝ) •
          (fun z : Plane => tr.v (B0146.overlapAge ν c + c ^ 2 * t / ν) z 0 *
            tr.v (B0146.overlapAge ν c + c ^ 2 * t / ν) z 1) (c • y) := by
      funext y
      simp only [Φ, U, overlapField, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [hU_prod]
    unfold hmean
    rw [inv_one, one_smul, MeasureTheory.integral_smul, smul_eq_mul]
    congr 1
    have hscale := hmean_scale_unit hc0
      (fun z : Plane => tr.v (B0146.overlapAge ν c + c ^ 2 * t / ν) z 0 *
        tr.v (B0146.overlapAge ν c + c ^ 2 * t / ν) z 1) Y'
    unfold hmean at hscale
    rw [inv_one, one_smul] at hscale
    exact hscale.symm
  rw [hg_eq, ← Real.norm_eq_abs]
  have h1 := PartI_T15.norm_iteratedDeriv_hmean_unit_le hΦ k Y
  have hpt : ∀ q : ℝ, ‖iteratedFDeriv ℝ k Φ (q, Y)‖ ≤ B := by
    intro q
    have hleib := norm_iteratedFDeriv_mul_le hU0 hU1 (q, Y) (n := k) (mod_cast le_top)
    have hsum : ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun w : Plane => U w 0) (q, Y)‖ *
          ‖iteratedFDeriv ℝ (k - i) (fun w : Plane => U w 1) (q, Y)‖ ≤
        ∑ _i ∈ Finset.range (k + 1), (2 ^ N : ℝ) * M₀ * M₀ := by
      refine Finset.sum_le_sum fun i hi => ?_
      have hi_le : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      have hchoose : (k.choose i : ℝ) ≤ (2 ^ N : ℝ) := by
        calc (k.choose i : ℝ) ≤ (2 ^ k : ℝ) := by exact_mod_cast Nat.choose_le_two_pow k i
          _ ≤ (2 ^ N : ℝ) := by exact_mod_cast Nat.pow_le_pow_right (by norm_num) hk
      have h0 : ‖iteratedFDeriv ℝ i (fun w : Plane => U w 0) (q, Y)‖ ≤ M₀ :=
        (norm_iteratedFDeriv_coord_le hU 0 i (q, Y)).trans (hjet t ht i (hi_le.trans hk) (q, Y))
      have h1' : ‖iteratedFDeriv ℝ (k - i) (fun w : Plane => U w 1) (q, Y)‖ ≤ M₀ :=
        (norm_iteratedFDeriv_coord_le hU 1 (k - i) (q, Y)).trans
          (hjet t ht (k - i) ((Nat.sub_le k i).trans hk) (q, Y))
      exact mul_le_mul (mul_le_mul hchoose h0 (norm_nonneg _) (by positivity))
        h1' (norm_nonneg _) (by positivity)
    calc ‖iteratedFDeriv ℝ k Φ (q, Y)‖
        ≤ ∑ _i ∈ Finset.range (k + 1), (2 ^ N : ℝ) * M₀ * M₀ := hleib.trans hsum
      _ = (k + 1 : ℝ) * 2 ^ N * M₀ ^ 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
          ring
      _ ≤ (N + 1 : ℝ) * 2 ^ N * M₀ ^ 2 := by
          have hkN : (k : ℝ) ≤ N := by exact_mod_cast hk
          nlinarith [pow_nonneg hM₀ 2]
  have hint : ∫ q in Ioc (-1 / 2 : ℝ) (1 / 2), ‖iteratedFDeriv ℝ k Φ (q, Y)‖ ≤ B := by
    have hcont : Continuous (fun q : ℝ => ‖iteratedFDeriv ℝ k Φ (q, Y)‖) :=
      ((hΦ.continuous_iteratedFDeriv (m := k) (mod_cast le_top)).comp
        (continuous_id.prodMk continuous_const)).norm
    calc ∫ q in Ioc (-1 / 2 : ℝ) (1 / 2), ‖iteratedFDeriv ℝ k Φ (q, Y)‖
        ≤ ∫ _q in Ioc (-1 / 2 : ℝ) (1 / 2), B :=
          setIntegral_mono_on hcont.integrableOn_Ioc (integrableOn_const measure_Ioc_lt_top.ne)
            measurableSet_Ioc (fun q _ => hpt q)
      _ = B := by
          rw [MeasureTheory.setIntegral_const, Real.volume_real_Ioc_of_le (by linarith)]
          norm_num
  exact h1.trans hint

/-- Uniform bound on `|overlapMeanStream tr 0 Y|` for all `Y ∈ ℝ`. -/
theorem exists_overlapMeanStream_zero_bound {ν c : ℝ} (hν : 0 < ν) (hc : 1 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr) :
    ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ Y : ℝ, |overlapMeanStream tr 0 Y| ≤ M₀ := by
  have hc0 : 0 < c := zero_lt_one.trans hc
  set s₀ : ℝ := B0146.overlapAge ν c
  have hs₀ : 0 < s₀ := by
    unfold s₀ B0146.overlapAge
    exact div_pos (by nlinarith) hν
  have hdec := Metric.tendsto_nhds.1 (tr.isTrain.stream_decay s₀ hs₀.le) 1 one_pos
  rw [Filter.eventually_comap] at hdec
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.1 hdec
  set R₁ : ℝ := max R 0
  have hS_cont : Continuous (meanStream tr s₀) := by
    have hS := (trainMeanEquations_proof ν c hν hc0 tr htr).1
    have hmap : ContDiff ℝ ∞ (fun η : ℝ => ((s₀, η) : ℝ × ℝ)) :=
      contDiff_const.prodMk contDiff_id
    exact (contDiffOn_univ.1
      (hS.comp hmap.contDiffOn (fun η _ => ⟨hs₀, mem_univ η⟩))).continuous
  obtain ⟨B₀, hB₀⟩ := (isCompact_Icc (a := -R₁) (b := R₁)).exists_bound_of_continuousOn
    hS_cont.continuousOn
  set B : ℝ := max (|B₀|) 1
  have hB_pos : 0 ≤ B := le_max_of_le_right zero_le_one
  refine ⟨c ^ 2 * B, by positivity, fun Y => ?_⟩
  rw [overlapMeanStream_zero, abs_mul, abs_of_pos (sq_pos_of_pos hc0)]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg c)
  by_cases hη : |c * Y| ≤ R₁
  · have hmem : c * Y ∈ Icc (-R₁) R₁ := abs_le.1 hη
    calc |meanStream tr s₀ (c * Y)|
        ≤ B₀ := by simpa [Real.norm_eq_abs] using hB₀ (c * Y) hmem
      _ ≤ |B₀| := le_abs_self B₀
      _ ≤ B := le_max_left _ _
  · rw [not_le] at hη
    have hR_le : R ≤ |c * Y| := (le_max_left R 0).trans hη.le
    have hbd : ∀ q : ℝ, ‖tr.ψ s₀ (q, c * Y)‖ ≤ 1 := by
      intro q
      have h := hR |c * Y| hR_le (q, c * Y) rfl
      rw [dist_zero_right] at h
      exact h.le
    have hint : ‖∫ q in Ioc (-c / 2) (c / 2), tr.ψ s₀ (q, c * Y)‖ ≤ 1 * c := by
      have h := norm_setIntegral_le_of_norm_le_const (μ := volume)
        (s := Ioc (-c / 2) (c / 2)) (f := fun q : ℝ => tr.ψ s₀ (q, c * Y))
        (C := 1) measure_Ioc_lt_top (fun q _ => hbd q)
      rw [Real.volume_real_Ioc_of_le (by linarith), show c / 2 - -c / 2 = c by ring] at h
      exact h
    have hmean_le : |meanStream tr s₀ (c * Y)| ≤ 1 := by
      unfold meanStream hmean
      rw [ ← Real.norm_eq_abs, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hc0]
      calc c⁻¹ * ‖∫ q in Ioc (-c / 2) (c / 2), tr.ψ s₀ (q, c * Y)‖
          ≤ c⁻¹ * (1 * c) := mul_le_mul_of_nonneg_left hint (inv_nonneg.2 hc0.le)
        _ = 1 := by field_simp [hc0.ne']
    exact hmean_le.trans (le_max_right _ _)

/-- Combined bound on `overlapMeanStream tr`, its time derivative, and `overlapStressProfile tr`
along with all their spatial derivatives up to order `N` on `[0, T] × ℝ`. -/
theorem exists_overlap_duhamel_bounds {ν c : ℝ} (hν : 0 < ν) (hc : 1 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr) {T : ℝ} (hT : 0 ≤ T) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ t ∈ Icc 0 T, ∀ k ≤ N, ∀ Y : ℝ, |iteratedDeriv k (overlapMeanStream tr t) Y| ≤ M) ∧
      (∀ t ∈ Icc 0 T, ∀ Y : ℝ, |deriv (fun r => overlapMeanStream tr r Y) t| ≤ M) ∧
      (∀ t ∈ Icc 0 T, ∀ k ≤ N, ∀ Y : ℝ, |iteratedDeriv k (overlapStressProfile tr t) Y| ≤ M) := by
  have hc0 : 0 < c := zero_lt_one.trans hc
  obtain ⟨M_jet, hM_jet0, hjet⟩ := exists_jet_overlapField_bound hν hc tr htr hT (max N 2)
  obtain ⟨M_g, hM_g0, hg_bd⟩ := exists_overlapStressProfile_deriv_bound hν hc tr htr hT (max N 2)
  obtain ⟨M₀, hM₀0, hS0_bd⟩ := exists_overlapMeanStream_zero_bound hν hc tr htr
  -- Bound on `|iteratedDeriv k (overlapMeanStream tr t) Y|` for `1 ≤ k ≤ max N 2`
  have hS_pos_bd : ∀ t ∈ Icc 0 T, ∀ k : ℕ, 1 ≤ k → k ≤ max N 2 → ∀ Y : ℝ,
      |iteratedDeriv k (overlapMeanStream tr t) Y| ≤ M_jet := by
    intro t ht k hk1 hkN Y
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.1 hk1)
    have hm_le : m ≤ max N 2 := Nat.le_of_succ_le hkN
    have hs : 0 < B0146.overlapAge ν c + c ^ 2 * t / ν := overlapAge_add_pos hν hc ht.1
    set U := overlapField ν c tr.v t
    have hU : ContDiff ℝ ∞ U := PartI_T15.contDiff_overlapField_slice tr hs.le
    have hderiv_eq : deriv (overlapMeanStream tr t) = -(fun Y' => hmean 1 U Y' 0) := by
      funext Y'
      dsimp
      linarith [overlapMean_b_eq_neg_deriv hν hc0 tr htr hs Y']
    rw [iteratedDeriv_succ', hderiv_eq, iteratedDeriv_neg, abs_neg, ← Real.norm_eq_abs]
    have h1 := PartI_T15.norm_iteratedDeriv_b_le_hmean_jet hU m Y
    have h2 : hmean 1 (fun z : Plane => ‖jet m U z‖) Y ≤ M_jet := by
      unfold hmean
      rw [inv_one, one_smul]
      have hcont : Continuous (fun q : ℝ => ‖jet m U (q, Y)‖) :=
        ((hU.continuous_iteratedFDeriv (m := m) (mod_cast le_top)).comp
          (continuous_id.prodMk continuous_const)).norm
      calc ∫ q in Ioc (-1 / 2 : ℝ) (1 / 2), ‖jet m U (q, Y)‖
          ≤ ∫ _q in Ioc (-1 / 2 : ℝ) (1 / 2), M_jet :=
            setIntegral_mono_on hcont.integrableOn_Ioc (integrableOn_const measure_Ioc_lt_top.ne)
              measurableSet_Ioc (fun q _ => hjet t ht m hm_le (q, Y))
        _ = M_jet := by
            rw [MeasureTheory.setIntegral_const, Real.volume_real_Ioc_of_le (by linarith)]
            norm_num
    exact h1.trans h2
  -- Bound on `|deriv (fun r => overlapMeanStream tr r Y) t|` on `[0, T] × ℝ`
  set M_t : ℝ := M_jet + eC ν c * M_g
  have hMt0 : 0 ≤ M_t := by
    have : 0 < eC ν c := by unfold eC; positivity
    positivity
  have hSt_bd : ∀ t ∈ Icc 0 T, ∀ Y : ℝ, |deriv (fun r => overlapMeanStream tr r Y) t| ≤ M_t := by
    intro t ht Y
    have hs : 0 < B0146.overlapAge ν c + c ^ 2 * t / ν := overlapAge_add_pos hν hc ht.1
    have hpde := overlapMeanStream_eq hν hc0 tr htr hs Y
    have h1 : deriv (fun r => overlapMeanStream tr r Y) t =
        deriv (deriv (overlapMeanStream tr t)) Y + eC ν c * overlapStressProfile tr t Y := by
      unfold overlapStressProfile; linarith
    have h2 : |deriv (deriv (overlapMeanStream tr t)) Y| ≤ M_jet := by
      have h2' := hS_pos_bd t ht 2 (by norm_num) (le_max_right N 2) Y
      simpa [iteratedDeriv_succ, iteratedDeriv_zero] using h2'
    have h3 : |overlapStressProfile tr t Y| ≤ M_g := by
      simpa [iteratedDeriv_zero] using hg_bd t ht 0 (Nat.zero_le _) Y
    have heC : 0 ≤ eC ν c := by unfold eC; positivity
    rw [h1]
    calc |deriv (deriv (overlapMeanStream tr t)) Y + eC ν c * overlapStressProfile tr t Y|
        ≤ |deriv (deriv (overlapMeanStream tr t)) Y| +
            |eC ν c * overlapStressProfile tr t Y| := abs_add_le _ _
      _ = |deriv (deriv (overlapMeanStream tr t)) Y| +
            eC ν c * |overlapStressProfile tr t Y| := by rw [abs_mul, abs_of_nonneg heC]
      _ ≤ M_jet + eC ν c * M_g :=
          add_le_add h2 (mul_le_mul_of_nonneg_left h3 heC)
  -- Bound on `|overlapMeanStream tr t Y|` on `[0, T] × ℝ` via MVT from `t = 0`
  have hut_diff : ∀ t ∈ Icc 0 T, ∀ Y : ℝ,
      DifferentiableAt ℝ (fun r => overlapMeanStream tr r Y) t := by
    intro t ht Y
    have hopen : IsOpen (overlapTimeIoi ν c ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
    have hmem : ((t, Y) : ℝ × ℝ) ∈ overlapTimeIoi ν c ×ˢ univ :=
      ⟨Ici_subset_overlapTimeIoi hν hc ht.1, mem_univ Y⟩
    have hd : DifferentiableAt ℝ (fun x : ℝ × ℝ => overlapMeanStream tr x.1 x.2) (t, Y) :=
      ((contDiffOn_overlapMeanStream_open hν hc tr htr).contDiffAt
        (hopen.mem_nhds hmem)).differentiableAt (by simp)
    exact (hd.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t Y))).differentiableAt
  have hS0_t_bd : ∀ t ∈ Icc 0 T, ∀ Y : ℝ, |overlapMeanStream tr t Y| ≤ M₀ + M_t * T := by
    intro t ht Y
    have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (s := Icc 0 T)
      (fun r hr => hut_diff r hr Y)
      (fun r hr => by rw [Real.norm_eq_abs]; exact hSt_bd r hr Y)
      (convex_Icc 0 T) ⟨le_rfl, hT⟩ ht
    rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, abs_of_nonneg ht.1] at hmvt
    calc |overlapMeanStream tr t Y|
        = |(overlapMeanStream tr t Y - overlapMeanStream tr 0 Y) + overlapMeanStream tr 0 Y| := by
          ring_nf
      _ ≤ |overlapMeanStream tr t Y - overlapMeanStream tr 0 Y| + |overlapMeanStream tr 0 Y| :=
          abs_add_le _ _
      _ ≤ M_t * t + M₀ := add_le_add hmvt (hS0_bd Y)
      _ ≤ M₀ + M_t * T := by nlinarith [ht.2]
  set M : ℝ := (M₀ + M_t * T) + M_jet + M_t + M_g
  have hM0 : 0 ≤ M := by positivity
  refine ⟨M, hM0, ?_, ?_, ?_⟩
  · intro t ht k hk Y
    rcases Nat.eq_zero_or_pos k with rfl | hk_pos
    · rw [iteratedDeriv_zero]
      exact (hS0_t_bd t ht Y).trans (by dsimp [M]; nlinarith)
    · exact (hS_pos_bd t ht k hk_pos (hk.trans (le_max_left N 2)) Y).trans (by dsimp [M]; nlinarith)
  · intro t ht Y
    exact (hSt_bd t ht Y).trans (by dsimp [M]; nlinarith)
  · intro t ht k hk Y
    exact (hg_bd t ht k (hk.trans (le_max_left N 2)) Y).trans (by dsimp [M]; nlinarith)

/-! ### 3. Pointwise Duhamel split at `T / 2` for `iteratedDeriv j b` -/

private theorem iteratedDeriv_const_mul_fun (c : ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    iteratedDeriv k (fun x => c * f x) = fun x => c * iteratedDeriv k f x := by
  induction k with
  | zero =>
    funext x
    simp [iteratedDeriv_zero]
  | succ k ih =>
    funext x
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
    have hd : DifferentiableAt ℝ (iteratedDeriv k f) x :=
      ((contDiff_iteratedDeriv_of_top hf k).differentiable (by simp)).differentiableAt
    exact (hd.hasDerivAt.const_mul c).deriv

private theorem lineHeat_const_mul (θ c : ℝ) (f : ℝ → ℝ) (Y : ℝ) :
    lineHeat θ (fun x => c * f x) Y = c * lineHeat θ f Y := by
  unfold lineHeat
  have h : (fun ξ : ℝ => Heat.lineGauss θ ξ * (c * f (Y - ξ))) =
      fun ξ : ℝ => c * (Heat.lineGauss θ ξ * f (Y - ξ)) := by
    funext ξ; ring
  rw [h, MeasureTheory.integral_const_mul]

/-- Abstract 1D heat Duhamel split at `T / 2` for `b = -∂_Y (u T)` where `∂_t u - ∂_Y² u = e * g`. -/
theorem iteratedDeriv_duhamel_split_of_pde {u g : ℝ → ℝ → ℝ} {b : ℝ → ℝ} {T e M : ℝ}
    (hT : 1 ≤ T) (he : 0 < e) (hM0 : 0 ≤ M) (j : ℕ)
    (hu_smooth : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => u x.1 x.2) (Ici 0 ×ˢ univ))
    (hu_zero_cd : ContDiff ℝ ∞ (u 0))
    (hg_Ioi : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => g x.1 x.2) (Ioi 0 ×ˢ univ))
    (hg_slice : ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (g t))
    (hut_diff : ∀ t ∈ Icc 0 T, ∀ Y : ℝ, DifferentiableAt ℝ (fun r => u r Y) t)
    (hb_eq : b = -(deriv (u T)))
    (hpde : ∀ t ∈ Icc 0 T, ∀ Y : ℝ, deriv (fun r => u r Y) t - deriv (deriv (u t)) Y = e * g t Y)
    (hu_bd : ∀ t ∈ Icc 0 T, ∀ k ≤ j + 2, ∀ Y : ℝ, |iteratedDeriv k (u t) Y| ≤ M)
    (hut_bd : ∀ t ∈ Icc 0 T, ∀ Y : ℝ, |deriv (fun r => u r Y) t| ≤ M)
    (hg_bd : ∀ t ∈ Icc 0 T, ∀ k ≤ j + 2, ∀ Y : ℝ, |iteratedDeriv k (g t) Y| ≤ M)
    (Y : ℝ) :
    iteratedDeriv j b Y =
      -iteratedDeriv (j + 1) (lineHeat T (u 0)) Y -
        e * (∫ t in Ioc 0 (T / 2), iteratedDeriv (j + 1) (lineHeat (T - t) (g t)) Y) -
        e * (∫ t in Ioc (T / 2) T, lineHeat (T - t) (iteratedDeriv (j + 1) (g t)) Y) := by
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  let F : ℝ → ℝ → ℝ := fun t Y' => e * g t Y'
  let M' : ℝ := (1 + e) * M
  have hM'0 : 0 ≤ M' := by positivity
  have hM_le_M' : M ≤ M' := by dsimp [M']; nlinarith
  have hF_bd : ∀ t ∈ Icc 0 T, ∀ m ≤ j + 1, ∀ x : ℝ, |iteratedDeriv m (F t) x| ≤ M' := by
    intro t ht m hm x
    have hg_cd : ContDiff ℝ ∞ (g t) := hg_slice t ht
    change |iteratedDeriv m (fun y => e * g t y) x| ≤ M'
    rw [iteratedDeriv_const_mul_fun e hg_cd m, abs_mul, abs_of_pos he]
    calc e * |iteratedDeriv m (g t) x|
        ≤ e * M := mul_le_mul_of_nonneg_left (hg_bd t ht m (hm.trans (by omega)) x) he.le
      _ ≤ (1 + e) * M := by nlinarith
  -- 1. Order-0 Duhamel identity `u T = lineDuhamel 1 (u 0) F T`
  have hduhamel0 : u T = lineDuhamel 1 (u 0) F T := by
    funext Y'
    refine lineHeat_duhamel_of_pde hT0 hu_smooth hut_diff hM0
      (fun t ht z => by simpa [iteratedDeriv_zero] using hu_bd t ht 0 (by omega) z)
      (fun t ht z => by
        simpa [iteratedDeriv_succ, iteratedDeriv_zero] using hu_bd t ht 1 (by omega) z)
      (fun t ht z => by
        simpa [iteratedDeriv_succ, iteratedDeriv_zero] using hu_bd t ht 2 (by omega) z)
      hut_bd hpde Y'
  -- 2. Differentiate `j + 1` times in `Y` via `iteratedDeriv_lineDuhamel_one`
  have hF_cd : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => F x.1 x.2) (Ioi 0 ×ˢ univ) :=
    contDiffOn_const.mul hg_Ioi
  have hduhamel_k := congr_fun (iteratedDeriv_lineDuhamel_one hT0 hu_zero_cd hF_cd (j + 1) hM'0
    (fun m hm x => (hu_bd 0 ⟨le_rfl, hT0.le⟩ m (hm.trans (by omega)) x).trans hM_le_M')
    (fun m hm t ht x => hF_bd t ht m hm x)) Y
  rw [← hduhamel0] at hduhamel_k
  -- 3. Relate `iteratedDeriv j b Y` to `-iteratedDeriv (j + 1) (u T) Y`
  have hb_iter : iteratedDeriv j b Y = -iteratedDeriv (j + 1) (u T) Y := by
    rw [hb_eq, iteratedDeriv_neg, ← iteratedDeriv_succ']
  rw [hb_iter, hduhamel_k]
  unfold lineDuhamel
  simp only [one_mul]
  -- 4. Commute `iteratedDeriv (j + 1)` outside `lineHeat T (u 0)`
  have hinit_comm : lineHeat T (iteratedDeriv (j + 1) (u 0)) Y =
      iteratedDeriv (j + 1) (lineHeat T (u 0)) Y :=
    (congr_fun (iteratedDeriv_lineHeat_data hT0 hu_zero_cd (j + 1)
      (fun m hm x => hu_bd 0 ⟨le_rfl, hT0.le⟩ m (hm.trans (by omega)) x)) Y).symm
  -- 5. Split the interval integral `∫ t in 0..T` at `T / 2`
  have hint_full : IntervalIntegrable
      (fun t => lineHeat (T - t) (iteratedDeriv (j + 1) (F t)) Y) volume 0 T :=
    intervalIntegrable_lineHeat_iteratedDeriv hT0.le hF_cd (j + 1)
      (fun t ht x => hF_bd t ht (j + 1) le_rfl x) Y
  have hint_early : IntervalIntegrable
      (fun t => lineHeat (T - t) (iteratedDeriv (j + 1) (F t)) Y) volume 0 (T / 2) :=
    hint_full.mono_set (uIcc_subset_uIcc_left (by rw [uIcc_of_le hT0.le]; constructor <;> linarith))
  have hint_late : IntervalIntegrable
      (fun t => lineHeat (T - t) (iteratedDeriv (j + 1) (F t)) Y) volume (T / 2) T :=
    hint_full.mono_set (uIcc_subset_uIcc_right (by rw [uIcc_of_le hT0.le]; constructor <;> linarith))
  have hsplit := (intervalIntegral.integral_add_adjacent_intervals hint_early hint_late).symm
  rw [hinit_comm, hsplit, intervalIntegral.integral_of_le (by linarith : 0 ≤ T / 2),
    intervalIntegral.integral_of_le (by linarith : T / 2 ≤ T)]
  -- 6. Rewrite the early and late integrands
  have hearly_eq : (∫ t in Ioc 0 (T / 2), lineHeat (T - t) (iteratedDeriv (j + 1) (F t)) Y) =
      e * ∫ t in Ioc 0 (T / 2), iteratedDeriv (j + 1) (lineHeat (T - t) (g t)) Y := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have ht_Icc : t ∈ Icc 0 T := ⟨ht.1.le, ht.2.trans (by linarith)⟩
    have hθ : 0 < T - t := by linarith [ht.2]
    have hg_cd : ContDiff ℝ ∞ (g t) := hg_slice t ht_Icc
    change lineHeat (T - t) (iteratedDeriv (j + 1) (fun y => e * g t y)) Y = _
    rw [iteratedDeriv_const_mul_fun e hg_cd (j + 1), lineHeat_const_mul,
      ← congr_fun (iteratedDeriv_lineHeat_data hθ hg_cd (j + 1)
        (fun m hm x => hg_bd t ht_Icc m (hm.trans (by omega)) x)) Y]
  have hlate_eq : (∫ t in Ioc (T / 2) T, lineHeat (T - t) (iteratedDeriv (j + 1) (F t)) Y) =
      e * ∫ t in Ioc (T / 2) T, lineHeat (T - t) (iteratedDeriv (j + 1) (g t)) Y := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have ht_Icc : t ∈ Icc 0 T := ⟨(by linarith [ht.1]), ht.2⟩
    have hg_cd : ContDiff ℝ ∞ (g t) := hg_slice t ht_Icc
    change lineHeat (T - t) (iteratedDeriv (j + 1) (fun y => e * g t y)) Y = _
    rw [iteratedDeriv_const_mul_fun e hg_cd (j + 1), lineHeat_const_mul]
  rw [hearly_eq, hlate_eq]
  ring

/-- **Pointwise 1D Heat Duhamel Split at `T / 2`**:
for `ν > 0`, `c > 1`, `tr : B0140.TrainSol ν c` with `IsBUCTrain tr`, `T ≥ 1`, and `j : ℕ`,
`iteratedDeriv j b Y` splits into the initial-datum heat propagation at `T`, the early forcing
integral on `Ioc 0 (T / 2)` (with `iteratedDeriv (j + 1)` outside `lineHeat (T - t)`), and the
late forcing integral on `Ioc (T / 2) T` (with `iteratedDeriv (j + 1)` inside `lineHeat (T - t)`). -/
theorem iteratedDeriv_b_duhamel_split {ν c : ℝ} (hν : 0 < ν) (hc : 1 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr) {T : ℝ} (hT : 1 ≤ T) (j : ℕ) (Y : ℝ) :
    let U := overlapField ν c tr.v T
    let b : ℝ → ℝ := fun Y' => hmean 1 U Y' 0
    let S₀ : ℝ → ℝ := overlapMeanStream tr 0
    let g : ℝ → ℝ → ℝ := overlapStressProfile tr
    iteratedDeriv j b Y =
      -iteratedDeriv (j + 1) (lineHeat T S₀) Y -
        eC ν c * (∫ t in Ioc 0 (T / 2), iteratedDeriv (j + 1) (lineHeat (T - t) (g t)) Y) -
        eC ν c * (∫ t in Ioc (T / 2) T, lineHeat (T - t) (iteratedDeriv (j + 1) (g t)) Y) := by
  dsimp only
  have hc0 : 0 < c := zero_lt_one.trans hc
  have hT0 : 0 ≤ T := (zero_lt_one.trans_le hT).le
  have heC_pos : 0 < eC ν c := by unfold eC; positivity
  obtain ⟨M, hM0, hS_bd, hSt_bd, hg_bd⟩ :=
    exists_overlap_duhamel_bounds hν hc tr htr hT0 (j + 2)
  have hg_open := contDiffOn_overlapStressProfile_open hν hc tr htr
  have hg_Ioi : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => overlapStressProfile tr x.1 x.2)
      (Ioi 0 ×ˢ univ) :=
    hg_open.mono (prod_mono (Ioi_subset_Ici_self.trans (Ici_subset_overlapTimeIoi hν hc)) Subset.rfl)
  have hut_diff : ∀ t ∈ Icc 0 T, ∀ Y' : ℝ,
      DifferentiableAt ℝ (fun r => overlapMeanStream tr r Y') t := by
    intro t ht Y'
    have hopen : IsOpen (overlapTimeIoi ν c ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
    have hmem : ((t, Y') : ℝ × ℝ) ∈ overlapTimeIoi ν c ×ˢ univ :=
      ⟨Ici_subset_overlapTimeIoi hν hc ht.1, mem_univ Y'⟩
    have hd : DifferentiableAt ℝ (fun x : ℝ × ℝ => overlapMeanStream tr x.1 x.2) (t, Y') :=
      ((contDiffOn_overlapMeanStream_open hν hc tr htr).contDiffAt
        (hopen.mem_nhds hmem)).differentiableAt (by simp)
    exact (hd.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t Y'))).differentiableAt
  have hb_eq : (fun Y' => hmean 1 (overlapField ν c tr.v T) Y' 0) =
      -(deriv (overlapMeanStream tr T)) := by
    funext Y'
    exact overlapMean_b_eq_neg_deriv hν hc0 tr htr (overlapAge_add_pos hν hc hT0) Y'
  exact iteratedDeriv_duhamel_split_of_pde hT heC_pos hM0 j
    (overlapMeanStream_contDiffOn hν hc tr htr)
    (contDiff_overlapMeanStream_slice hν hc tr htr le_rfl)
    hg_Ioi
    (fun t ht => contDiff_overlapStressProfile_slice hν hc tr htr ht.1)
    hut_diff hb_eq
    (fun t ht z => overlapMeanStream_pde_profile hν hc0 tr htr (overlapAge_add_pos hν hc ht.1) z)
    hS_bd hSt_bd hg_bd Y

end UnforcedLeray.Short.PartI.DuhamelSplit
