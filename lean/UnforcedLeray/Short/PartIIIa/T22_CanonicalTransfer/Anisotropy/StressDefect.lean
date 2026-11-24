import UnforcedLeray.Short.PartIIIa.T22_CanonicalTransfer.Anisotropy.CompactWindow
import UnforcedLeray.Short.PartIIIa.Clock.Restart

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal NNReal ContDiff Interval InnerProductSpace ComplexConjugate SchwartzMap

namespace UnforcedLeray.Short.IIIa.AnisoSynthAux

open UnforcedLeray.Short.IIIa

/-! ## 4. Three-way clock split and proof of `CTStressDefect` -/

lemma symFlow_pairings_and_iA_eq {ν m : ℝ} (hν : 0 < ν) (hm : 8 < m)
    (_P : PlanarData) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (μ : ℂ)
    (hv_fin : ∀ s : ℝ, 0 ≤ s → UnforcedLeray.Train.cellL2 (ν ^ (-2 : ℝ)) (tr.v s) < ⊤)
    {f : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr 0 f w u) :
    (∀ s : ℝ, 0 ≤ s →
      pairEta tr μ (symFlowU u s) s = pairEta tr μ (u s) s ∧
      pairQ tr μ (symFlowU u s) s = pairQ tr μ (u s) s ∧
      pairC tr μ (symFlowU u s) s = pairC tr μ (u s) s ∧
      aPlus ν μ (symFlowW w) s = aPlus ν μ w s) ∧
    iA ν μ (symFlowW w) = iA ν μ w := by
  let c : ℝ := ν ^ (-2 : ℝ)
  have hslice : ∀ s : ℝ, 0 ≤ s →
      pairEta tr μ (symFlowU u s) s = pairEta tr μ (u s) s ∧
      pairQ tr μ (symFlowU u s) s = pairQ tr μ (u s) s ∧
      pairC tr μ (symFlowU u s) s = pairC tr μ (u s) s ∧
      aPlus ν μ (symFlowW w) s = aPlus ν μ w s := by
    intro s hs
    obtain ⟨hpair, hq⟩ := symFlow_preserves_pairings_and_quadQ hm tr hs
      (hw.memX s hs) (hw.biotSavart s hs) (hv_fin s hs)
    have hv_m : ∀ i : Fin 2, MemLp (fun x => tr.v s x i) 2 (volume.restrict (B0579.cell c)) :=
      fun i => (memLp_train_coord_of_cellL2 hs tr (hv_fin s hs) i).1
    have hu_sym_m : ∀ j : Fin 2,
        MemLp (fun x => symFlowU u s x j) 2 (volume.restrict (B0579.cell c)) := fun j => by
      have hsub := ((hw.biotSavart s hs).1 j).sub (memLp_comp_neg_vol_aniso ((hw.biotSavart s hs).1 j))
      exact hsub.const_mul (2 : ℂ)⁻¹
    have hpull : ∀ (U : ℝ × ℝ → Fin 2 → ℂ) (i j : Fin 2),
        (∫ x in B0579.cell c, ((tr.v s x i : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * U x j)) =
          (s : ℂ) ^ (-μ) * ∫ x in B0579.cell c, ((tr.v s x i : ℝ) : ℂ) * U x j := fun U i j => by
      have hp : (fun x => ((tr.v s x i : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * U x j)) =
          fun x => (s : ℂ) ^ (-μ) * (((tr.v s x i : ℝ) : ℂ) * U x j) := by funext x; ring
      rw [hp, integral_const_mul]
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold pairEta; rw [hpull (symFlowU u s) 0 0, hpull (u s) 0 0, hpair 0 0]
    · unfold pairQ; rw [hpull (symFlowU u s) 1 1, hpull (u s) 1 1, hpair 1 1]
    · unfold pairC
      have is01 : IntegrableOn
          (fun x => ((tr.v s x 0 : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * symFlowU u s x 1))
          (B0579.cell c) := by
        have hp : (fun x => ((tr.v s x 0 : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * symFlowU u s x 1)) =
            fun x => (s : ℂ) ^ (-μ) * (((tr.v s x 0 : ℝ) : ℂ) * symFlowU u s x 1) := by
          funext x; ring
        rw [hp]; exact ((hv_m 0).ofReal.integrable_mul (hu_sym_m 1)).const_mul _
      have is10 : IntegrableOn
          (fun x => ((tr.v s x 1 : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * symFlowU u s x 0))
          (B0579.cell c) := by
        have hp : (fun x => ((tr.v s x 1 : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * symFlowU u s x 0)) =
            fun x => (s : ℂ) ^ (-μ) * (((tr.v s x 1 : ℝ) : ℂ) * symFlowU u s x 0) := by
          funext x; ring
        rw [hp]; exact ((hv_m 1).ofReal.integrable_mul (hu_sym_m 0)).const_mul _
      have iu01 : IntegrableOn
          (fun x => ((tr.v s x 0 : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * u s x 1))
          (B0579.cell c) := by
        have hp : (fun x => ((tr.v s x 0 : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * u s x 1)) =
            fun x => (s : ℂ) ^ (-μ) * (((tr.v s x 0 : ℝ) : ℂ) * u s x 1) := by funext x; ring
        rw [hp]; exact ((hv_m 0).ofReal.integrable_mul ((hw.biotSavart s hs).1 1)).const_mul _
      have iu10 : IntegrableOn
          (fun x => ((tr.v s x 1 : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * u s x 0))
          (B0579.cell c) := by
        have hp : (fun x => ((tr.v s x 1 : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * u s x 0)) =
            fun x => (s : ℂ) ^ (-μ) * (((tr.v s x 1 : ℝ) : ℂ) * u s x 0) := by funext x; ring
        rw [hp]; exact ((hv_m 1).ofReal.integrable_mul ((hw.biotSavart s hs).1 0)).const_mul _
      rw [integral_add is01 is10, integral_add iu01 iu10,
        hpull (symFlowU u s) 0 1, hpull (symFlowU u s) 1 0,
        hpull (u s) 0 1, hpull (u s) 1 0, hpair 0 1, hpair 1 0]
    · unfold aPlus; rw [hq]
  refine ⟨hslice, ?_⟩
  unfold iA
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  have hs0 : 0 ≤ s := ((Real.rpow_pos_of_pos hν (-3 / 2 : ℝ)).trans hs).le
  rw [(hslice s hs0).2.2.2]

lemma sAbs_smul_aniso {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (μ : ℂ)
    (α : ℂ) (u : ℝ × ℝ → Fin 2 → ℂ) (s : ℝ) :
    sAbs tr μ (fun x j => α * u x j) s = ENNReal.ofReal ‖α‖ * sAbs tr μ u s := by
  unfold sAbs
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun x => ?_
  have hterm : ∀ i j : Fin 2,
      ‖((tr.v s x i : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * (α * u x j)) +
          ((s : ℂ) ^ (-μ) * (α * u x i)) * ((tr.v s x j : ℝ) : ℂ)‖ ^ 2 =
        ‖α‖ ^ 2 *
          ‖((tr.v s x i : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * u x j) +
              ((s : ℂ) ^ (-μ) * u x i) * ((tr.v s x j : ℝ) : ℂ)‖ ^ 2 := fun i j => by
    have hpull : ((tr.v s x i : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * (α * u x j)) +
        ((s : ℂ) ^ (-μ) * (α * u x i)) * ((tr.v s x j : ℝ) : ℂ) =
        α * (((tr.v s x i : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * u x j) +
          ((s : ℂ) ^ (-μ) * u x i) * ((tr.v s x j : ℝ) : ℂ)) := by ring
    rw [hpull, norm_mul, mul_pow]
  have hsum : (∑ i : Fin 2, ∑ j : Fin 2,
        ‖((tr.v s x i : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * (α * u x j)) +
            ((s : ℂ) ^ (-μ) * (α * u x i)) * ((tr.v s x j : ℝ) : ℂ)‖ ^ 2) =
      ‖α‖ ^ 2 * ∑ i : Fin 2, ∑ j : Fin 2,
        ‖((tr.v s x i : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * u x j) +
            ((s : ℂ) ^ (-μ) * u x i) * ((tr.v s x j : ℝ) : ℂ)‖ ^ 2 := by
    simp_rw [hterm, ← Finset.mul_sum]
  rw [hsum, Real.sqrt_mul (sq_nonneg ‖α‖), Real.sqrt_sq (norm_nonneg α),
    ENNReal.ofReal_mul (norm_nonneg α)]
  ring

lemma isLinearisedFlow_smul_aniso {ν c m t : ℝ} (hm : 1 < m) (α : ℂ)
    {tr : UnforcedLeray.B0140.TrainSol ν c} {f : ℝ × ℝ → ℂ}
    {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν c m tr t f w u) :
    IsLinearisedFlow ν c m tr t (fun x => α * f x)
      (fun s x => α * w s x) (fun s x j => α * u s x j) := by
  have hfl : ∀ ψ (r : ℝ) (x : ℝ × ℝ),
      flowIntegrand tr (fun y => α * w r y) (fun y j => α * u r y j) r ψ x =
        α * flowIntegrand tr (w r) (u r) r ψ x := by
    intro ψ r x; unfold flowIntegrand; ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hw.initial] with x hx
    rw [hx]
  · intro s hs
    exact (hw.memX s hs).const_mul α
  · intro s hs
    have hlim : Tendsto (fun s' => ‖α‖ₑ * xNorm c m (w s' - w s))
        (𝓝[Ici t] s) (𝓝 (‖α‖ₑ * 0)) :=
      ENNReal.Tendsto.const_mul (hw.strongCont s hs) (Or.inr enorm_ne_top)
    rw [mul_zero] at hlim
    refine hlim.congr fun s' => ?_
    have hfun : (fun x => α * w s' x) - (fun x => α * w s x) = α • (w s' - w s) := by
      funext x; simp [mul_sub]
    unfold xNorm
    rw [hfun, eLpNorm_const_smul]
  · intro s hs
    exact isBiotSavart_smul_aniso α
      (integrableOn_cell_of_memX (by linarith) (hw.memX s hs))
      (hw.biotSavart s hs)
  · intro ψ hψ r hr
    have hpt : flowIntegrand tr (fun y => α * w r y) (fun y j => α * u r y j) r ψ =
        fun x => α * flowIntegrand tr (w r) (u r) r ψ x := funext (hfl ψ r)
    rw [hpt]
    exact (hw.integrable ψ hψ r hr).const_mul α
  · intro ψ hψ s hs
    refine ((hw.timeIntegrable ψ hψ s hs).const_mul α).congr fun r hr => ?_
    rw [uIoc_of_le hs] at hr
    have hpt : flowIntegrand tr (fun y => α * w r y) (fun y j => α * u r y j) r ψ =
        fun x => α * flowIntegrand tr (w r) (u r) r ψ x := funext (hfl ψ r)
    rw [hpt, integral_const_mul]
  · intro ψ hψ s hs
    have hptL : (fun x => (α * w s x) * (ψ x : ℂ)) = fun x => α * (w s x * (ψ x : ℂ)) := by
      funext x; ring
    have hptF : (fun x => (α * f x) * (ψ x : ℂ)) = fun x => α * (f x * (ψ x : ℂ)) := by
      funext x; ring
    have hcongr : ∀ r ∈ uIoc t s,
        (∫ x in B0579.cell c,
          flowIntegrand tr (fun y => α * w r y) (fun y j => α * u r y j) r ψ x) =
        α * ∫ x in B0579.cell c, flowIntegrand tr (w r) (u r) r ψ x := by
      intro r _
      have hpt : flowIntegrand tr (fun y => α * w r y) (fun y j => α * u r y j) r ψ =
          fun x => α * flowIntegrand tr (w r) (u r) r ψ x := funext (hfl ψ r)
      rw [hpt, integral_const_mul]
    rw [hptL, hptF, integral_const_mul, integral_const_mul,
      intervalIntegral.integral_congr_ae (ae_of_all _ hcongr),
      intervalIntegral.integral_const_mul, hw.weak ψ hψ s hs, mul_add]

lemma integrableOn_each_pair_Ioi_onset
    (P : PlanarData) (hP : IsPlanarReference P) (m : ℝ) (hm : 8 < m)
    (K : Set ℂ) (hK : IsAdmissibleK K) :
    ∃ ν_int : ℝ, 0 < ν_int ∧ ∀ ν ∈ Ioc 0 ν_int,
      ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
        UnforcedLeray.Short.PartI.IsBUCTrain tr →
        ∀ w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr 0 (preparedDatum P ν) w u →
          ∀ μ ∈ K,
            IntegrableOn (fun s => pairEta tr μ (u s) s * ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ))
              (Ioi (onsetAge ν)) ∧
            IntegrableOn (fun s => pairQ tr μ (u s) s * ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ))
              (Ioi (onsetAge ν)) ∧
            IntegrableOn (fun s => pairC tr μ (u s) s * ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ))
              (Ioi (onsetAge ν)) := by
  obtain ⟨C_abs, ν_abs, hν_abs, hAbs⟩ := ctAbsoluteStress P hP m hm K hK 0 (Nat.zero_le 1)
  obtain ⟨C_L2, ν_L2, hC_L2, hν_L2, hL2_unif⟩ := train_cellL2_uniform_aniso
  have hBranch := T22Sub.ctCanonicalBranchProps P hP m hm
  set ν_int : ℝ := min ν_abs (min ν_L2 (1 / 4))
  have hν_int : 0 < ν_int := lt_min hν_abs (lt_min hν_L2 (by norm_num))
  refine ⟨ν_int, hν_int, fun ν hν tr htr w u hw μ hμ => ?_⟩
  have hν_pos : 0 < ν := hν.1
  have hν_abs_le : ν ≤ ν_abs := hν.2.trans (min_le_left _ _)
  have hν_L2_le : ν ≤ ν_L2 := hν.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν_qtr : ν ≤ 1 / 4 := hν.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hν1 : ν ≤ 1 := hν_qtr.trans (by norm_num)
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc1 : 1 ≤ c := by
    have hle : ((1 / 4 : ℝ) ^ (-2 : ℝ)) ≤ c :=
      Real.rpow_le_rpow_of_nonpos hν_pos hν_qtr (by norm_num)
    have hev : ((1 / 4 : ℝ) ^ (-2 : ℝ)) = 16 := by norm_num
    linarith
  obtain ⟨hprep_mem, hprep_zc, hprep_ev⟩ := hBranch.1 ν ⟨hν_pos, hν1⟩
  -- Symmetrize `(w, u)` so right-continuity applies
  set w_ev : ℝ → ℝ × ℝ → ℂ := symFlowW w
  set u_odd : ℝ → ℝ × ℝ → Fin 2 → ℂ := symFlowU u
  have hw_sym : IsLinearisedFlow ν c m tr 0 (preparedDatum P ν) w_ev u_odd :=
    isLinearisedFlow_sym_aniso (by linarith) tr hprep_mem hprep_ev hw
  have hw_ev_all : ∀ s : ℝ, IsCentrallyEven (w_ev s) := fun s x => by
    unfold w_ev symFlowW; rw [neg_neg]; ring
  have hv_fin : ∀ s : ℝ, 0 ≤ s → UnforcedLeray.Train.cellL2 c (tr.v s) < ⊤ := fun s hs =>
    lt_of_le_of_lt (hL2_unif ν ⟨hν_pos, hν_L2_le⟩ tr htr s hs) ENNReal.ofReal_lt_top
  obtain ⟨hpair_eq, _⟩ := symFlow_pairings_and_iA_eq hν_pos hm P tr μ hv_fin hw
  have hrc_pair : ∀ i j : Fin 2, ∀ s₀ : ℝ, 0 < s₀ →
      ContinuousWithinAt
        (fun s => ∫ x in B0579.cell c, ((tr.v s x i : ℝ) : ℂ) * u_odd s x j) (Ici s₀) s₀ :=
    fun i j s₀ hs₀ => rightContinuous_train_vel_pairing hm hc1 hC_L2 tr
      (hL2_unif ν ⟨hν_pos, hν_L2_le⟩ tr htr) hprep_zc hw_sym hw_ev_all i j hs₀.le
  have hcpow_rc : ∀ s₀ : ℝ, 0 < s₀ →
      ContinuousWithinAt (fun s : ℝ => (s : ℂ) ^ (-μ)) (Ici s₀) s₀ := fun s₀ hs₀ =>
    ((continuousAt_cpow_const (Complex.ofReal_mem_slitPlane.2 hs₀)).comp
      Complex.continuous_ofReal.continuousAt).continuousWithinAt
  have hrpow_rc : ∀ s₀ : ℝ, 0 < s₀ →
      ContinuousWithinAt (fun s : ℝ => ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ)) (Ici s₀) s₀ := fun s₀ hs₀ =>
    (Complex.continuous_ofReal.continuousAt.comp
      (Real.continuousAt_rpow_const s₀ (-3 / 2 : ℝ) (Or.inl hs₀.ne'))).continuousWithinAt
  have huo_pos : 0 < onsetAge ν := Real.rpow_pos_of_pos hν_pos _
  have hIoi_sub : Ioi (onsetAge ν) ⊆ Ioi 0 := Ioi_subset_Ioi huo_pos.le
  -- Bound `∫⁻ s in Ioi (onsetAge ν), s^(-3/2) * sAbs < ⊤` for `(w_ev, u_odd)`
  have habs_lt : (∫⁻ s in Ioi (onsetAge ν),
      ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * sAbs tr μ (u_odd s) s) < ⊤ := by
    have h0 := hAbs ν ⟨hν_pos, hν_abs_le⟩ tr htr w_ev u_odd hw_sym μ hμ
    have hexp : (-3 / 2 - ((0 : ℕ) : ℝ) / 2 : ℝ) = -3 / 2 := by norm_num
    rw [hexp] at h0
    exact lt_of_le_of_lt h0 ENNReal.ofReal_lt_top
  -- Helper turning `ContinuousWithinAt` + `‖g s‖ₑ ≤ sAbs` into `IntegrableOn`
  have mk_int : ∀ (g g_orig : ℝ → ℂ),
      (∀ s₀ : ℝ, 0 < s₀ → ContinuousWithinAt g (Ici s₀) s₀) →
      (∀ s : ℝ, 0 ≤ s → ‖g s‖ₑ ≤ sAbs tr μ (u_odd s) s) →
      (∀ s : ℝ, 0 ≤ s → g s = g_orig s) →
      IntegrableOn (fun s => g_orig s * ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ)) (Ioi (onsetAge ν)) := by
    intro g g_orig hrc hle heq
    have haesm : AEStronglyMeasurable
        (fun s => g s * ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ)) (volume.restrict (Ioi (onsetAge ν))) :=
      aestronglyMeasurable_on_subset_Ioi_of_rightContinuous hIoi_sub measurableSet_Ioi
        (fun s₀ hs₀ => (hrc s₀ hs₀).mul (hrpow_rc s₀ hs₀))
    have hfin : HasFiniteIntegral
        (fun s => g s * ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ)) (volume.restrict (Ioi (onsetAge ν))) := by
      refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioi fun s hs => ?_) habs_lt
      have hs0 : 0 ≤ s := (huo_pos.trans hs).le
      have hw_en : ‖((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ)‖ₑ = ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) := by
        rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hs0 _)]
      rw [enorm_mul, hw_en, mul_comm]
      exact mul_le_mul_of_nonneg_left (hle s hs0) bot_le
    have hint_sym : IntegrableOn
        (fun s => g s * ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ)) (Ioi (onsetAge ν)) := ⟨haesm, hfin⟩
    refine hint_sym.congr_fun (fun s hs => ?_) measurableSet_Ioi
    dsimp only
    rw [heq s (huo_pos.trans hs).le]
  have hpull_odd : ∀ (i j : Fin 2) {s : ℝ},
      (∫ x in B0579.cell c, ((tr.v s x i : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * u_odd s x j)) =
        (s : ℂ) ^ (-μ) * ∫ x in B0579.cell c, ((tr.v s x i : ℝ) : ℂ) * u_odd s x j :=
    fun i j {s} => by
      have hp : (fun x => ((tr.v s x i : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * u_odd s x j)) =
          fun x => (s : ℂ) ^ (-μ) * (((tr.v s x i : ℝ) : ℂ) * u_odd s x j) := by funext x; ring
      rw [hp, integral_const_mul]
  refine ⟨?_, ?_, ?_⟩
  · refine mk_int (fun s => pairEta tr μ (u_odd s) s) (fun s => pairEta tr μ (u s) s)
      (fun s₀ hs₀ => ?_)
      (fun s _ => (enorm_pairs_le_sAbs hν_pos tr μ (u_odd s) s).1)
      (fun s hs => (hpair_eq s hs).1)
    have hfun : EqOn (fun s => pairEta tr μ (u_odd s) s)
        (fun s => (2 / (c : ℂ)) * ((s : ℂ) ^ (-μ) *
          ∫ x in B0579.cell c, ((tr.v s x 0 : ℝ) : ℂ) * u_odd s x 0)) (Ici s₀) :=
      fun s _ => by dsimp only; unfold pairEta; rw [hpull_odd 0 0]
    exact (continuousWithinAt_const.mul ((hcpow_rc s₀ hs₀).mul (hrc_pair 0 0 s₀ hs₀))).congr
      (fun s hs => hfun hs) (hfun (mem_Ici.2 le_rfl))
  · refine mk_int (fun s => pairQ tr μ (u_odd s) s) (fun s => pairQ tr μ (u s) s)
      (fun s₀ hs₀ => ?_)
      (fun s _ => (enorm_pairs_le_sAbs hν_pos tr μ (u_odd s) s).2.1)
      (fun s hs => (hpair_eq s hs).2.1)
    have hfun : EqOn (fun s => pairQ tr μ (u_odd s) s)
        (fun s => (2 / (c : ℂ)) * ((s : ℂ) ^ (-μ) *
          ∫ x in B0579.cell c, ((tr.v s x 1 : ℝ) : ℂ) * u_odd s x 1)) (Ici s₀) :=
      fun s _ => by dsimp only; unfold pairQ; rw [hpull_odd 1 1]
    exact (continuousWithinAt_const.mul ((hcpow_rc s₀ hs₀).mul (hrc_pair 1 1 s₀ hs₀))).congr
      (fun s hs => hfun hs) (hfun (mem_Ici.2 le_rfl))
  · refine mk_int (fun s => pairC tr μ (u_odd s) s) (fun s => pairC tr μ (u s) s)
      (fun s₀ hs₀ => ?_)
      (fun s _ => (enorm_pairs_le_sAbs hν_pos tr μ (u_odd s) s).2.2)
      (fun s hs => (hpair_eq s hs).2.2.1)
    have hfun : EqOn (fun s => pairC tr μ (u_odd s) s)
        (fun s => (1 / (c : ℂ)) * ((s : ℂ) ^ (-μ) *
          ((∫ x in B0579.cell c, ((tr.v s x 0 : ℝ) : ℂ) * u_odd s x 1) +
            ∫ x in B0579.cell c, ((tr.v s x 1 : ℝ) : ℂ) * u_odd s x 0))) (Ici s₀) := by
      intro s hs
      have hs0 : 0 ≤ s := hs₀.le.trans hs
      have hv_m : ∀ i, MemLp (fun x => tr.v s x i) 2 (volume.restrict (B0579.cell c)) :=
        fun i => (memLp_train_coord_of_cellL2 hs0 tr (hv_fin s hs0) i).1
      have i01 : IntegrableOn
          (fun x => ((tr.v s x 0 : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * u_odd s x 1))
          (B0579.cell c) := by
        have hp : (fun x => ((tr.v s x 0 : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * u_odd s x 1)) =
            fun x => (s : ℂ) ^ (-μ) * (((tr.v s x 0 : ℝ) : ℂ) * u_odd s x 1) := by
          funext x; ring
        rw [hp]; exact ((hv_m 0).ofReal.integrable_mul ((hw_sym.biotSavart s hs0).1 1)).const_mul _
      have i10 : IntegrableOn
          (fun x => ((tr.v s x 1 : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * u_odd s x 0))
          (B0579.cell c) := by
        have hp : (fun x => ((tr.v s x 1 : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * u_odd s x 0)) =
            fun x => (s : ℂ) ^ (-μ) * (((tr.v s x 1 : ℝ) : ℂ) * u_odd s x 0) := by
          funext x; ring
        rw [hp]; exact ((hv_m 1).ofReal.integrable_mul ((hw_sym.biotSavart s hs0).1 0)).const_mul _
      dsimp only [c]; unfold pairC
      rw [integral_add i01 i10, hpull_odd 0 1, hpull_odd 1 0]
      ring
    exact (continuousWithinAt_const.mul ((hcpow_rc s₀ hs₀).mul
      ((hrc_pair 0 1 s₀ hs₀).add (hrc_pair 1 0 s₀ hs₀)))).congr
      (fun s hs => hfun hs) (hfun (mem_Ici.2 le_rfl))

lemma onset_and_core_clock_props_aniso {B ν : ℝ} (hB1 : 1 ≤ B) (hν : 0 < ν)
    (hν_qtr : ν ≤ 1 / 4) (hν_9B2 : ν ≤ (9 * B ^ 2)⁻¹) :
    0 < onsetAge ν ∧
      onsetAge ν < clockAge ν B ∧
      clockAge ν B ≤ UnforcedLeray.B0146.overlapAge ν (ν ^ (-2 : ℝ)) ∧
      ∀ s ∈ Ioc (onsetAge ν) (clockAge ν B),
        0 < s ∧
        B ≤ clockTheta ν s ∧
        clockTheta ν s ≤ ν⁻¹ ∧
        (2 * ν ^ 2 * clockTheta ν s)⁻¹ ≤ s ∧
        (UnforcedLeray.Train.width ν s)⁻¹ = ν * clockTheta ν s := by
  have hB0 : 0 < B := lt_of_lt_of_le one_pos hB1
  have hν1 : ν ≤ 1 := hν_qtr.trans (by norm_num)
  have huo_pos : 0 < onsetAge ν := Real.rpow_pos_of_pos hν _
  have hsqrt_le : ν ^ (1 / 2 : ℝ) ≤ (3 * B)⁻¹ := by
    have h9 : (9 * B ^ 2)⁻¹ = ((3 * B)⁻¹) ^ (2 : ℝ) := by
      rw [Real.rpow_two, inv_pow]; ring
    calc ν ^ (1 / 2 : ℝ)
        ≤ ((9 * B ^ 2)⁻¹) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hν.le hν_9B2 (by norm_num)
      _ = (((3 * B)⁻¹) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by rw [h9]
      _ = (3 * B)⁻¹ := by
          rw [← Real.rpow_mul (by positivity : 0 ≤ (3 * B)⁻¹)]
          norm_num
  have huo_lt : onsetAge ν < clockAge ν B := by
    unfold onsetAge clockAge
    rw [lt_div_iff₀ (by positivity)]
    have hprod : ν ^ (-3 / 2 : ℝ) * (ν ^ 2 * B) = B * ν ^ (1 / 2 : ℝ) := by
      have h2 : (ν ^ 2 : ℝ) = ν ^ (2 : ℝ) := (Real.rpow_two ν).symm
      calc ν ^ (-3 / 2 : ℝ) * (ν ^ 2 * B)
          = B * (ν ^ (-3 / 2 : ℝ) * ν ^ (2 : ℝ)) := by rw [h2]; ring
        _ = B * ν ^ (1 / 2 : ℝ) := by congr 1; rw [← Real.rpow_add hν]; norm_num
    have hle3 : B * ν ^ (1 / 2 : ℝ) ≤ 1 / 3 := by
      calc B * ν ^ (1 / 2 : ℝ) ≤ B * (3 * B)⁻¹ := mul_le_mul_of_nonneg_left hsqrt_le hB0.le
        _ = 1 / 3 := by field_simp
    have hνB_le : ν * B ≤ 1 / 9 := by
      calc ν * B ≤ (9 * B ^ 2)⁻¹ * B := mul_le_mul_of_nonneg_right hν_9B2 hB0.le
        _ = (9 * B)⁻¹ := by field_simp
        _ ≤ 1 / 9 := by
            rw [inv_eq_one_div]
            exact div_le_div_of_nonneg_left zero_le_one (by norm_num) (by linarith)
    linarith
  have hsB_le_sc : clockAge ν B ≤ UnforcedLeray.B0146.overlapAge ν (ν ^ (-2 : ℝ)) := by
    have hc_sq : (ν ^ (-2 : ℝ)) ^ 2 = (ν ^ 4)⁻¹ := by
      rw [Real.rpow_neg hν.le, Real.rpow_two, inv_pow]; ring
    have hsc_eq : UnforcedLeray.B0146.overlapAge ν (ν ^ (-2 : ℝ)) = (1 - ν ^ 4) / ν ^ 5 := by
      unfold UnforcedLeray.B0146.overlapAge; rw [hc_sq]; have := hν.ne'; field_simp
    rw [hsc_eq]; unfold clockAge
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hν3_lt : ν ^ 3 ≤ B := by
      have : ν ^ 3 ≤ (1 / 4 : ℝ) ^ 3 := pow_le_pow_left₀ hν.le hν_qtr 3
      linarith
    have hmul : ν ^ 5 ≤ ν ^ 2 * B := by
      calc ν ^ 5 = ν ^ 2 * ν ^ 3 := by ring
        _ ≤ ν ^ 2 * B := mul_le_mul_of_nonneg_left hν3_lt (sq_nonneg ν)
    nlinarith [pow_nonneg hν.le 6]
  refine ⟨huo_pos, huo_lt, hsB_le_sc, fun s hs => ?_⟩
  have hs0 : 0 < s := huo_pos.trans hs.1
  have ha_s1 : 1 ≤ clockA ν s := by unfold clockA; nlinarith
  have ha_s0 : 0 < clockA ν s := lt_of_lt_of_le one_pos ha_s1
  have hB_le_θ : B ≤ clockTheta ν s := by
    have ha_le : clockA ν s ≤ clockA ν (clockAge ν B) := by unfold clockA; nlinarith [hs.2]
    rw [T22Sub.clockA_clockAge hν hB0] at ha_le
    have hmul : ν * clockA ν s ≤ B⁻¹ := by
      calc ν * clockA ν s ≤ ν * (ν * B)⁻¹ := mul_le_mul_of_nonneg_left ha_le hν.le
        _ = B⁻¹ := by field_simp [hν.ne', hB0.ne']
    unfold clockTheta
    have hinv := inv_anti₀ (mul_pos hν ha_s0) hmul
    rwa [inv_inv] at hinv
  have hθ_le_inv : clockTheta ν s ≤ ν⁻¹ := by
    unfold clockTheta
    exact inv_anti₀ hν (le_mul_of_one_le_right hν.le ha_s1)
  have hνs_ge1 : 1 ≤ ν * s := by
    have h1 : 1 ≤ ν ^ (-1 / 2 : ℝ) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by norm_num)
    have h2 : ν ^ (-1 / 2 : ℝ) = ν * onsetAge ν := by
      unfold onsetAge
      calc ν ^ (-1 / 2 : ℝ) = ν ^ ((1 : ℝ) + (-3 / 2 : ℝ)) := by norm_num
        _ = ν ^ (1 : ℝ) * ν ^ (-3 / 2 : ℝ) := Real.rpow_add hν 1 (-3 / 2)
        _ = ν * ν ^ (-3 / 2 : ℝ) := by rw [Real.rpow_one]
    calc (1 : ℝ) ≤ ν ^ (-1 / 2 : ℝ) := h1
      _ = ν * onsetAge ν := h2
      _ ≤ ν * s := mul_le_mul_of_nonneg_left hs.1.le hν.le
  have hs_lower : (2 * ν ^ 2 * clockTheta ν s)⁻¹ ≤ s := by
    have heq : (2 * ν ^ 2 * clockTheta ν s)⁻¹ = (1 + ν * s) / (2 * ν) := by
      unfold clockTheta clockA; have := hν.ne'; have := ha_s0.ne'; field_simp
    rw [heq, div_le_iff₀ (by positivity)]
    linarith
  have hwidth_eq : (UnforcedLeray.Train.width ν s)⁻¹ = ν * clockTheta ν s := by
    unfold UnforcedLeray.Train.width clockTheta clockA
    have := hν.ne'; have := ha_s0.ne'; field_simp
  exact ⟨hs0, hB_le_θ, hθ_le_inv, hs_lower, hwidth_eq⟩

lemma rpow_mul_exp_le_half_exp_aniso {γ θ q : ℝ} (hγ : 0 < γ) (hθ1 : 1 ≤ θ)
    (M : ℕ) (hq : q ≤ (M : ℝ)) :
    θ ^ q * Real.exp (-γ * θ) ≤
      ((M.factorial : ℝ) * (2 / γ) ^ M) * Real.exp (-(γ / 2) * θ) := by
  have hpow_le : θ ^ q ≤ θ ^ M := by
    rw [← Real.rpow_natCast θ M]
    exact Real.rpow_le_rpow_of_exponent_le hθ1 hq
  have hfac := Real.pow_div_factorial_le_exp ((γ / 2) * θ) (by positivity) M
  have hθM : θ ^ M ≤ ((M.factorial : ℝ) * (2 / γ) ^ M) * Real.exp ((γ / 2) * θ) := by
    have h1 : ((γ / 2) * θ) ^ M ≤ (M.factorial : ℝ) * Real.exp ((γ / 2) * θ) := by
      have hpos_f : (0 : ℝ) < (M.factorial : ℝ) := Nat.cast_pos.2 (Nat.factorial_pos M)
      rw [div_le_iff₀ hpos_f] at hfac
      linarith
    have hid : θ ^ M = (2 / γ) ^ M * ((γ / 2) * θ) ^ M := by
      rw [← mul_pow]; congr 1; field_simp [hγ.ne']
    rw [hid]
    calc (2 / γ) ^ M * ((γ / 2) * θ) ^ M
        ≤ (2 / γ) ^ M * ((M.factorial : ℝ) * Real.exp ((γ / 2) * θ)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ((M.factorial : ℝ) * (2 / γ) ^ M) * Real.exp ((γ / 2) * θ) := by ring
  calc θ ^ q * Real.exp (-γ * θ)
      ≤ θ ^ M * Real.exp (-γ * θ) := mul_le_mul_of_nonneg_right hpow_le (Real.exp_nonneg _)
    _ ≤ (((M.factorial : ℝ) * (2 / γ) ^ M) * Real.exp ((γ / 2) * θ)) * Real.exp (-γ * θ) :=
        mul_le_mul_of_nonneg_right hθM (Real.exp_nonneg _)
    _ = ((M.factorial : ℝ) * (2 / γ) ^ M) * (Real.exp ((γ / 2) * θ) * Real.exp (-γ * θ)) := by
        ring
    _ = ((M.factorial : ℝ) * (2 / γ) ^ M) * Real.exp (-(γ / 2) * θ) := by
        rw [← Real.exp_add]; congr 2; ring

lemma integral_Ioc_exp_clockTheta_le_aniso {γ ν t₁ B : ℝ}
    (hγ : 0 < γ) (hν : 0 < ν) (hB : 0 < B) (ht₁ : 0 ≤ t₁) (ht12 : t₁ ≤ clockAge ν B) :
    IntegrableOn
      (fun s => Real.exp (-(γ / 2) * clockTheta ν s) * (ν ^ 2 * (clockTheta ν s) ^ 2))
      (Ioc t₁ (clockAge ν B)) ∧
    (∫ s in Ioc t₁ (clockAge ν B),
      Real.exp (-(γ / 2) * clockTheta ν s) * (ν ^ 2 * (clockTheta ν s) ^ 2)) ≤
      (2 / γ) * Real.exp (-(γ / 2) * B) := by
  set t₂ : ℝ := clockAge ν B
  let g : ℝ → ℝ := fun s => Real.exp (-(γ / 2) * clockTheta ν s) * (ν ^ 2 * (clockTheta ν s) ^ 2)
  let Φ : ℝ → ℝ := fun s => (2 / γ) * Real.exp (-(γ / 2) * clockTheta ν s)
  have hθ_cont : ContinuousOn (clockTheta ν) (Icc t₁ t₂) := by
    unfold clockTheta clockA
    refine ContinuousOn.inv₀
      (continuousOn_const.mul (continuousOn_const.add (continuousOn_const.mul continuousOn_id))) ?_
    intro s hs
    have hs0 : 0 ≤ s := ht₁.trans hs.1
    exact (mul_pos hν (by positivity : 0 < 1 + ν * s)).ne'
  have hg_cont : ContinuousOn g (Icc t₁ t₂) :=
    (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hθ_cont)).mul
      (continuousOn_const.mul (hθ_cont.pow 2))
  have hderiv : ∀ s ∈ Icc t₁ t₂, HasDerivAt Φ (g s) s := by
    intro s hs
    have hs0 : 0 ≤ s := ht₁.trans hs.1
    have hden_pos : 0 < ν + ν ^ 2 * s := by positivity
    have h_lin : HasDerivAt (fun r : ℝ => ν + ν ^ 2 * r) (ν ^ 2) s := by
      simpa using (hasDerivAt_id s).const_mul (ν ^ 2) |>.const_add ν
    have h_inv := h_lin.inv hden_pos.ne'
    have hθ_eq : clockTheta ν = fun r : ℝ => (ν + ν ^ 2 * r)⁻¹ := by
      funext r; unfold clockTheta clockA; congr 1; ring
    have hθ_deriv : HasDerivAt (clockTheta ν) (-(ν ^ 2 * (clockTheta ν s) ^ 2)) s := by
      rw [hθ_eq]
      refine h_inv.congr_deriv ?_
      rw [neg_div, div_eq_mul_inv, inv_pow]
    have hexp_deriv := ((hθ_deriv.const_mul (-(γ / 2))).exp).const_mul (2 / γ)
    refine hexp_deriv.congr_deriv ?_
    dsimp only [g]
    field_simp [hγ.ne']
  have hg_iiv : IntervalIntegrable g volume t₁ t₂ :=
    hg_cont.intervalIntegrable_of_Icc ht12
  have hg_intOn : IntegrableOn g (Ioc t₁ t₂) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht12).1 hg_iiv
  refine ⟨hg_intOn, ?_⟩
  rw [← intervalIntegral.integral_of_le ht12,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs => hderiv s (uIcc_of_le ht12 ▸ hs))
      hg_iiv]
  have hΦ_t1_nn : 0 ≤ Φ t₁ := by dsimp [Φ]; positivity
  have hΦ_t2_eq : Φ t₂ = (2 / γ) * Real.exp (-(γ / 2) * B) := by
    dsimp [Φ, t₂]; rw [T22Sub.clockTheta_clockAge hν hB]
  linarith

lemma heatColumn_even_props_aniso
    {P : PlanarData} {ν m θ : ℝ} (hν : 0 < ν) (hθ : 0 < θ) (hθν : θ ≤ ν⁻¹)
    (hν3 : ν ^ 3 ≤ θ) (hm : 8 < m)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    {f : ℝ × ℝ → ℂ} (hf_zc : HasZeroCirculation (ν ^ (-2 : ℝ)) f)
    {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr 0 f w u)
    (hw_ev : ∀ s : ℝ, IsCentrallyEven (w s)) :
    let d := dOfTheta ν θ
    let Z := heatColumn P ν w θ
    let a := (ν * θ)⁻¹
    let s_θ := clockAge ν θ
    let U_Z : ℝ × ℝ → Fin 2 → ℂ := fun y j =>
      (P.gaugeFactor ν)⁻¹ * ((a ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
        u s_θ (Real.sqrt a * y.1, Real.sqrt a * y.2) j
    1 ≤ d ∧
      MemLp Z 2 (B0579.cellMeasure d m) ∧
      HasZeroCirculation d Z ∧
      IsCentrallyEven Z ∧
      IsBiotSavart d Z U_Z ∧
      Jscale a Z = (fun x => (P.gaugeFactor ν)⁻¹ * w s_θ x) ∧
      quadQ (ν ^ (-2 : ℝ)) (w s_θ) = P.gaugeFactor ν * quadQ d Z := by
  dsimp only
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc_pos : 0 < c := Real.rpow_pos_of_pos hν _
  set s_θ : ℝ := clockAge ν θ
  have hs_θ0 : 0 ≤ s_θ := T22Sub.clockAge_nonneg hν hθ hθν
  set a : ℝ := (ν * θ)⁻¹
  have ha_pos : 0 < a := inv_pos.2 (mul_pos hν hθ)
  have ha_s : clockA ν s_θ = a := T22Sub.clockA_clockAge hν hθ
  have hθ_s : clockTheta ν s_θ = θ := T22Sub.clockTheta_clockAge hν hθ
  set d : ℝ := dOfTheta ν θ
  have hd_cell : d = cellLen c a := by
    dsimp [d]
    rw [← hθ_s, T22Sub.dOfTheta_eq_cellLen hν (ha_s.symm ▸ ha_pos), ha_s]
  have hd1 : 1 ≤ d := T22Sub.one_le_dOfTheta hν hν3
  have hgf_ne : P.gaugeFactor ν ≠ 0 := T22Sub.gaugeFactor_ne_zero P hν
  set Z : ℝ × ℝ → ℂ := heatColumn P ν w θ
  have hZ_eq : Z = fun y => (P.gaugeFactor ν)⁻¹ * JscaleInv a (w s_θ) y := rfl
  -- MemLp Z 2
  have hm_j : MemLp (JscaleInv a (w s_θ)) 2 (B0579.cellMeasure d m) := by
    rw [hd_cell]
    exact ComplFreeRateSub.Leaf2WeakEqFrame.KerBSAux.memLp_JscaleInv_pos
      (c := c) (by linarith : (0 : ℝ) ≤ m) ha_pos (hw.memX s_θ hs_θ0)
  have hZ_mem : MemLp Z 2 (B0579.cellMeasure d m) := hm_j.const_mul (P.gaugeFactor ν)⁻¹
  -- HasZeroCirculation d Z
  have hw_zc : HasZeroCirculation c (w s_θ) :=
    zeroCirculationPreserved ν c m hc_pos (by linarith) tr 0 f w u hw hf_zc s_θ hs_θ0
  have hZ_zc : HasZeroCirculation d Z := by
    refine ⟨integrableOn_cell_of_memX (by linarith) hZ_mem, ?_⟩
    have hcv := cv_cell (c := c) ha_pos (w s_θ)
    rw [← hd_cell, Complex.real_smul, hw_zc.2] at hcv
    have h0 : ∫ y in B0579.cell d, w s_θ (Real.sqrt a * y.1, Real.sqrt a * y.2) = 0 :=
      (mul_eq_zero.1 hcv).resolve_left (Complex.ofReal_ne_zero.2 ha_pos.ne')
    have hpt : Z = fun y => ((P.gaugeFactor ν)⁻¹ * ((a ^ 2 : ℝ) : ℂ)) *
        w s_θ (Real.sqrt a * y.1, Real.sqrt a * y.2) := by
      funext y; dsimp [Z, heatColumn, JscaleInv]; ring
    rw [hpt, integral_const_mul, h0, mul_zero]
  -- IsCentrallyEven Z
  have hZ_ev : IsCentrallyEven Z := fun y => by
    dsimp only [Z, heatColumn, JscaleInv]
    have hneg : (Real.sqrt ((ν * θ)⁻¹) * (-y).1, Real.sqrt ((ν * θ)⁻¹) * (-y).2) =
        -(Real.sqrt ((ν * θ)⁻¹) * y.1, Real.sqrt ((ν * θ)⁻¹) * y.2) := by ext <;> simp
    rw [hneg, hw_ev s_θ]
  -- IsBiotSavart d Z U_Z
  set U_Z : ℝ × ℝ → Fin 2 → ℂ := fun y j =>
    (P.gaugeFactor ν)⁻¹ * ((a ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
      u s_θ (Real.sqrt a * y.1, Real.sqrt a * y.2) j
  have hUZ_bs : IsBiotSavart d Z U_Z := by
    have hbs_j := UnforcedLeray.Short.PartIIIb.Concrete.isBiotSavart_jscaleInv
      c a hc_pos ha_pos (w s_θ) (u s_θ) (hw.biotSavart s_θ hs_θ0)
    rw [← hd_cell] at hbs_j
    have hU_eq : U_Z = fun y j => (P.gaugeFactor ν)⁻¹ *
        (((a ^ (3 / 2 : ℝ) : ℝ) : ℂ) * u s_θ (Real.sqrt a * y.1, Real.sqrt a * y.2) j) := by
      funext y j; dsimp [U_Z]; ring
    rw [hZ_eq, hU_eq]
    exact isBiotSavart_smul_aniso (P.gaugeFactor ν)⁻¹
      (integrableOn_cell_of_memX (by linarith) hm_j) hbs_j
  -- Pointwise Jscale inverse
  have hJ_eq : Jscale a Z = fun x => (P.gaugeFactor ν)⁻¹ * w s_θ x := by
    funext x
    have hsq : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha_pos).ne'
    have hpow : (a ^ (-2 : ℝ) : ℝ) * a ^ 2 = 1 := by
      rw [Real.rpow_neg ha_pos.le, Real.rpow_two, inv_mul_cancel₀ (pow_ne_zero 2 ha_pos.ne')]
    dsimp [Jscale, Z, heatColumn, JscaleInv]
    rw [mul_div_cancel₀ _ hsq, mul_div_cancel₀ _ hsq]
    calc ((a ^ (-2 : ℝ) : ℝ) : ℂ) * ((P.gaugeFactor ν)⁻¹ * (((a ^ 2 : ℝ) : ℂ) * w s_θ x))
        = (P.gaugeFactor ν)⁻¹ * ((((a ^ (-2 : ℝ) * a ^ 2 : ℝ)) : ℂ) * w s_θ x) := by
          push_cast; ring
      _ = (P.gaugeFactor ν)⁻¹ * w s_θ x := by rw [hpow, Complex.ofReal_one, one_mul]
  -- quadQ rescaling
  have hQ_eq : quadQ c (w s_θ) = P.gaugeFactor ν * quadQ d Z := by
    have hcv := cv_cell (c := c) ha_pos (fun x => ((x.2 ^ 2 : ℝ) : ℂ) * w s_θ x)
    rw [← hd_cell, Complex.real_smul] at hcv
    have hpt : (fun y : ℝ × ℝ =>
          (((Real.sqrt a * y.2) ^ 2 : ℝ) : ℂ) * w s_θ (Real.sqrt a * y.1, Real.sqrt a * y.2)) =
        fun y => P.gaugeFactor ν * ((a⁻¹ : ℝ) : ℂ) * (((y.2 ^ 2 : ℝ) : ℂ) * Z y) := by
      funext y
      have hsq2 : (Real.sqrt a * y.2) ^ 2 = a * y.2 ^ 2 := by
        rw [mul_pow, Real.sq_sqrt ha_pos.le]
      have ha2 : a = a⁻¹ * a ^ 2 := by field_simp [ha_pos.ne']
      dsimp only [Z, heatColumn, JscaleInv]
      rw [hsq2]
      calc ((a * y.2 ^ 2 : ℝ) : ℂ) * w s_θ (Real.sqrt a * y.1, Real.sqrt a * y.2)
          = (P.gaugeFactor ν * (P.gaugeFactor ν)⁻¹) *
              (((a⁻¹ * a ^ 2 : ℝ) : ℂ) * ((y.2 ^ 2 : ℝ) : ℂ) *
                w s_θ (Real.sqrt a * y.1, Real.sqrt a * y.2)) := by
            rw [mul_inv_cancel₀ hgf_ne, ← ha2]; push_cast; ring
        _ = P.gaugeFactor ν * ((a⁻¹ : ℝ) : ℂ) *
              (((y.2 ^ 2 : ℝ) : ℂ) *
                ((P.gaugeFactor ν)⁻¹ * (((a ^ 2 : ℝ) : ℂ) *
                  w s_θ (Real.sqrt a * y.1, Real.sqrt a * y.2)))) := by
            push_cast; ring
    simp_rw [hpt, integral_const_mul] at hcv
    have hainv : (a : ℂ) * (P.gaugeFactor ν * ((a⁻¹ : ℝ) : ℂ)) = P.gaugeFactor ν := by
      calc (a : ℂ) * (P.gaugeFactor ν * ((a⁻¹ : ℝ) : ℂ))
          = P.gaugeFactor ν * (((a * a⁻¹ : ℝ)) : ℂ) := by push_cast; ring
        _ = P.gaugeFactor ν := by rw [mul_inv_cancel₀ ha_pos.ne', Complex.ofReal_one, mul_one]
    rw [← mul_assoc, hainv] at hcv
    unfold quadQ
    rw [← hcv]; ring
  exact ⟨hd1, hZ_mem, hZ_zc, hZ_ev, hUZ_bs, hJ_eq, hQ_eq⟩

theorem ctStressDefect_impl : CTStressDefect := by
  intro P hP m hm K hK ε hε
  have hγ : 0 < P.eigenvalue.re := hP.eigenpair.re_pos
  set γ : ℝ := P.eigenvalue.re
  set κ_re : ℝ := P.kappa.re
  obtain ⟨C_emb0, hEmb0⟩ := ctEmbeddings m hm
  set C_emb : ℝ := max C_emb0 1
  have hC_emb : 0 < C_emb := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hEmb : ∀ d : ℝ, 1 ≤ d → ∀ f : ℝ × ℝ → ℂ,
      MemLp f 2 (B0579.cellMeasure d m) → HasZeroCirculation d f → IsCentrallyEven f →
        ∀ u, IsBiotSavart d f u →
          ENNReal.ofReal ‖quadQ d f‖ + velNorm d u ≤ ENNReal.ofReal C_emb * xNorm d m f := by
    intro d hd f hf hz hev u hu
    exact (hEmb0 d hd f hf hz hev u hu).trans
      (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (le_max_left _ _)) bot_le)
  have hBranch := T22Sub.ctCanonicalBranchProps P hP m hm
  obtain ⟨b₀_br, _, hBr_all⟩ := hBranch.2.2.1
  obtain ⟨b₀_long, hLong_all⟩ := ctLongComparison P hP m hm
  obtain ⟨b₀_imp, hImp_all⟩ := T22Sub.ctAbsoluteImpulse P hP m hm K hK 0 (Nat.zero_le 1)
  obtain ⟨C_tr, ν_tr, hC_tr, hν_tr, htr_l2⟩ :=
    T22Sub.trainL2Decay_unconditional 2 (by norm_num : (1 / 2 : ℝ) < 2)
  obtain ⟨C_L2, ν_L2, hC_L2, hν_L2, hL2_unif⟩ := train_cellL2_uniform_aniso
  obtain ⟨ν_int, hν_int, hInt_pairs⟩ := integrableOn_each_pair_Ioi_onset P hP m hm K hK
  -- Step 1: Fix `b_base` independent of `ε` and `B`, then choose `B` large enough for the core tail
  set b_base : ℝ := max 1 (max b₀_br b₀_long)
  have hb_base1 : 1 ≤ b_base := le_max_left _ _
  obtain ⟨C_br, hC_br, hBr_est⟩ := hBr_all b_base ((le_max_left _ _).trans (le_max_right _ _))
  obtain ⟨C_long0, a₁, ν_long, ha₁, hν_long, hLong_est⟩ :=
    hLong_all b_base ((le_max_right _ _).trans (le_max_right _ _))
  set C_long : ℝ := max C_long0 1
  have hC_long : 0 < C_long := lt_of_lt_of_le one_pos (le_max_right _ _)
  set C_Z : ℝ := C_emb * (C_br + 3 * C_long)
  have hC_Z : 0 < C_Z := by dsimp [C_Z]; positivity
  set M_pow : ℕ := ⌈3 - κ_re⌉₊
  set M_exp : ℝ := (M_pow.factorial : ℝ) * (2 / γ) ^ M_pow
  have hM_exp : 0 < M_exp :=
    mul_pos (Nat.cast_pos.2 (Nat.factorial_pos M_pow)) (pow_pos (div_pos two_pos hγ) M_pow)
  set C_core : ℝ := 96 * C_tr * C_Z * M_exp * (2 / γ)
  have hC_core : 0 < C_core := by dsimp [C_core]; positivity
  -- Choose `B ≥ max b_base b₀_imp` so `C_core * Real.exp (-(γ / 2) * B) ≤ ε / 3`
  have hlim_B : Tendsto (fun B : ℝ => C_core * Real.exp (-(γ / 2) * B)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun B : ℝ => (γ / 2) * B) atTop atTop :=
      Tendsto.const_mul_atTop (by positivity) tendsto_id
    have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul C_core
    rw [mul_zero] at h2
    exact h2.congr fun B => by dsimp [Function.comp]; ring_nf
  obtain ⟨B_big, hB_big⟩ :=
    (eventually_atTop.1 ((Metric.tendsto_nhds.1 hlim_B) (ε / 3) (by positivity)))
  set B : ℝ := max (max b_base b₀_imp) B_big
  have hB_base : b_base ≤ B := (le_max_left _ _).trans (le_max_left _ _)
  have hB1 : 1 ≤ B := hb_base1.trans hB_base
  have hB_pos : 0 < B := lt_of_lt_of_le one_pos hB1
  have hB_imp : b₀_imp ≤ B := (le_max_right _ _).trans (le_max_left _ _)
  have hCore_eps : C_core * Real.exp (-(γ / 2) * B) ≤ ε / 3 := by
    have h := hB_big B (le_max_right _ _)
    rw [dist_zero_right, Real.norm_of_nonneg (by positivity)] at h
    exact h.le
  -- Step 2: With `B` fixed, choose `r ∈ (0, min (B / 2) (1 / 2))` for the small-clock impulse tail
  obtain ⟨C_imp0, ν_imp, hν_imp, hImp_est⟩ := hImp_all B hB_imp
  set C_imp : ℝ := max C_imp0 1
  have hC_imp : 0 < C_imp := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨C_V, hC_V, hVd_xnorm⟩ := hBranch.2.2.2 B hB_pos
  set K_Z_max : ℝ := 2 * (1 + C_emb * C_V)
  have hKZ_pos : 0 < K_Z_max := by dsimp [K_Z_max]; positivity
  set r : ℝ := min (min (B / 2) (1 / 2)) ((ε / 3) / (6 * C_imp * K_Z_max + 1))
  have hr_pos : 0 < r := lt_min (lt_min (by positivity) (by norm_num)) (by positivity)
  have hr_le_B2 : r ≤ B / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hr_lt_B : r < B := by linarith
  have hr_le_half : r ≤ 1 / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hr_le1 : r ≤ 1 := hr_le_half.trans (by norm_num)
  have hImp_eps : 6 * C_imp * K_Z_max * r ≤ ε / 3 := by
    have hr_bd : r ≤ (ε / 3) / (6 * C_imp * K_Z_max + 1) := min_le_right _ _
    calc 6 * C_imp * K_Z_max * r
        ≤ (6 * C_imp * K_Z_max) * ((ε / 3) / (6 * C_imp * K_Z_max + 1)) :=
          mul_le_mul_of_nonneg_left hr_bd (by positivity)
      _ ≤ ε / 3 := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          linarith only [hε, show 6 * C_imp * K_Z_max * (ε / 3) = (ε / 3) * (6 * C_imp * K_Z_max) by ring]
  -- Step 3: Gather small-ν filters for compact comparison at `r` and compact window `(s_B, s_r]`
  obtain ⟨b₀_comp, hComp_all⟩ := ctCompactComparison P hP m hm
  have hComp_r_ev := hComp_all (max B b₀_comp) (le_max_right _ _) r hr_pos
    (hr_lt_B.le.trans (le_max_left _ _)) 1 one_pos
  have hWin_ev := stressDefect_compact_window P hP m hm K hK hB1 hr_pos hr_lt_B
    (by positivity : 0 < ε / 3)
  set ν_cap : ℝ :=
    min ν_int (min ν_long (min ν_imp (min ν_tr (min ν_L2 (min (1 / 4) ((9 * B ^ 2)⁻¹))))))
  have hν_cap : 0 < ν_cap :=
    lt_min hν_int (lt_min hν_long (lt_min hν_imp (lt_min hν_tr
      (lt_min hν_L2 (lt_min (by norm_num) (inv_pos.2 (by positivity)))))))
  have hev_ν3 : ∀ᶠ ν : ℝ in 𝓝[>] (0 : ℝ), ν ∈ Ioc 0 ν_cap ∧ ν ^ 3 ≤ r := by
    have hev1 : Ioc 0 ν_cap ∈ 𝓝[>] (0 : ℝ) := Ioc_mem_nhdsGT hν_cap
    have hev2 : ∀ᶠ ν : ℝ in 𝓝[>] (0 : ℝ), ν ^ 3 ≤ r := by
      have h0 : Tendsto (fun ν : ℝ => ν ^ 3) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        simpa using ((continuous_pow 3).continuousAt (x := (0 : ℝ))).tendsto.mono_left
          nhdsWithin_le_nhds
      filter_upwards [(Metric.tendsto_nhds.1 h0) r hr_pos, self_mem_nhdsWithin] with ν hν_r hν_p
      rw [dist_zero_right, Real.norm_of_nonneg (pow_nonneg (mem_Ioi.1 hν_p).le 3)] at hν_r
      exact hν_r.le
    filter_upwards [hev1, hev2] with ν h1 h2 using ⟨h1, h2⟩
  filter_upwards [hev_ν3, hComp_r_ev, hWin_ev] with ν ⟨hν_in, hν3_r⟩ hComp_r hWin
  intro tr htr w u hw μ hμ
  have hν_pos : 0 < ν := hν_in.1
  have hν_int_le : ν ≤ ν_int := hν_in.2.trans (min_le_left _ _)
  have hν_long_le : ν ≤ ν_long :=
    hν_in.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν_imp_le : ν ≤ ν_imp :=
    hν_in.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hν_tr_le : ν ≤ ν_tr :=
    hν_in.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have hν_L2_le : ν ≤ ν_L2 :=
    hν_in.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have hν_qtr : ν ≤ 1 / 4 :=
    hν_in.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        (min_le_left _ _))))))
  have hν_9B2 : ν ≤ (9 * B ^ 2)⁻¹ :=
    hν_in.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        (min_le_right _ _))))))
  have hν1 : ν ≤ 1 := hν_qtr.trans (by norm_num)
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc_pos : 0 < c := Real.rpow_pos_of_pos hν_pos _
  obtain ⟨hprep_mem, hprep_zc, hprep_ev⟩ := hBranch.1 ν ⟨hν_pos, hν1⟩
  obtain ⟨hσ_pos, hσ_lt⟩ := hK.2 μ hμ
  set σ : ℝ := μ.re
  have hscaleA_nn : 0 ≤ scaleA P ν μ := by unfold scaleA; positivity
  -- Integrability on `Ioi (onsetAge ν)` for `(w, u)`
  obtain ⟨hi_Eta, hi_Q, hi_C⟩ := hInt_pairs ν ⟨hν_pos, hν_int_le⟩ tr htr w u hw μ hμ
  set F_orig : ℝ → ℂ := fun s =>
    ((pairEta tr μ (u s) s + pairQ tr μ (u s) s) -
      3 * (pairQ tr μ (u s) s - Complex.I * pairC tr μ (u s) s)) *
        ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ)
  have hInt_orig : IntegrableOn F_orig (Ioi (onsetAge ν)) := by
    have hcomb := ((hi_Eta.add hi_Q).sub ((hi_Q.sub (hi_C.const_mul Complex.I)).const_mul 3))
    refine hcomb.congr_fun (fun s _ => ?_) measurableSet_Ioi
    dsimp only [F_orig, Pi.add_apply, Pi.sub_apply]; ring
  refine ⟨hInt_orig, ?_⟩
  -- Symmetrize `(w, u)` to `(w_ev, u_odd)` and identify the defect integral
  set w_ev : ℝ → ℝ × ℝ → ℂ := symFlowW w
  set u_odd : ℝ → ℝ × ℝ → Fin 2 → ℂ := symFlowU u
  have hw_sym : IsLinearisedFlow ν c m tr 0 (preparedDatum P ν) w_ev u_odd :=
    isLinearisedFlow_sym_aniso (by linarith) tr hprep_mem hprep_ev hw
  have hw_ev_all : ∀ s : ℝ, IsCentrallyEven (w_ev s) := fun s x => by
    unfold w_ev symFlowW; rw [neg_neg]; ring
  have hv_fin : ∀ s : ℝ, 0 ≤ s → UnforcedLeray.Train.cellL2 c (tr.v s) < ⊤ := fun s hs =>
    lt_of_le_of_lt (hL2_unif ν ⟨hν_pos, hν_L2_le⟩ tr htr s hs) ENNReal.ofReal_lt_top
  obtain ⟨hpair_eq, _⟩ := symFlow_pairings_and_iA_eq hν_pos hm P tr μ hv_fin hw
  set F_def : ℝ → ℂ := fun s =>
    ((pairEta tr μ (u_odd s) s + pairQ tr μ (u_odd s) s) -
      3 * (pairQ tr μ (u_odd s) s - Complex.I * pairC tr μ (u_odd s) s)) *
        ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ)
  obtain ⟨huo_pos, huo_lt_sB, hsB_le_sc, hclock_Ioc⟩ :=
    onset_and_core_clock_props_aniso hB1 hν_pos hν_qtr hν_9B2
  have hF_eq : EqOn F_def F_orig (Ioi (onsetAge ν)) := fun s hs => by
    have hs0 : 0 ≤ s := (huo_pos.trans hs).le
    obtain ⟨he, hq, hc_p, _⟩ := hpair_eq s hs0
    dsimp only [F_def, F_orig]
    rw [he, hq, hc_p]
  have hInt_def : IntegrableOn F_def (Ioi (onsetAge ν)) :=
    hInt_orig.congr_fun (fun s hs => (hF_eq hs).symm) measurableSet_Ioi
  rw [← setIntegral_congr_fun measurableSet_Ioi hF_eq]
  -- Three-way clock split: `Ioi u_o = Ioc u_o s_B ∪ Ioc s_B s_r ∪ Ioi s_r`
  set u_o : ℝ := onsetAge ν
  set s_B : ℝ := clockAge ν B
  set s_r : ℝ := clockAge ν r
  have hsB_lt_sr : s_B < s_r := by
    have hrew : ∀ z : ℝ, z ≠ 0 → clockAge ν z = (ν ^ 2 * z)⁻¹ - ν⁻¹ := fun z hz => by
      unfold clockAge; have := hν_pos.ne'; field_simp
    dsimp [s_B, s_r]
    rw [hrew B hB_pos.ne', hrew r hr_pos.ne']
    have hlt : (ν ^ 2 * B)⁻¹ < (ν ^ 2 * r)⁻¹ :=
      inv_strictAnti₀ (by positivity) (mul_lt_mul_of_pos_left hr_lt_B (by positivity))
    linarith
  have huo_lt_sr : u_o < s_r := huo_lt_sB.trans hsB_lt_sr
  have hsplit_all : ∫ s in Ioi u_o, F_def s =
      (∫ s in Ioc u_o s_B, F_def s) +
        (∫ s in Ioc s_B s_r, F_def s) +
        (∫ s in Ioi s_r, F_def s) := by
    have hu1 : Ioc u_o s_r ∪ Ioi s_r = Ioi u_o := Ioc_union_Ioi_eq_Ioi huo_lt_sr.le
    have hd1 : Disjoint (Ioc u_o s_r) (Ioi s_r) :=
      disjoint_left.2 fun s hs1 hs2 => not_lt_of_ge hs1.2 hs2
    have hu2 : Ioc u_o s_B ∪ Ioc s_B s_r = Ioc u_o s_r :=
      Ioc_union_Ioc_eq_Ioc huo_lt_sB.le hsB_lt_sr.le
    have hd2 : Disjoint (Ioc u_o s_B) (Ioc s_B s_r) := Ioc_disjoint_Ioc_of_le le_rfl
    have hi_sr : IntegrableOn F_def (Ioc u_o s_r) := hInt_def.mono_set Ioc_subset_Ioi_self
    have hi_ioi : IntegrableOn F_def (Ioi s_r) :=
      hInt_def.mono_set (Ioi_subset_Ioi huo_lt_sr.le)
    have hi_1 : IntegrableOn F_def (Ioc u_o s_B) := hInt_def.mono_set Ioc_subset_Ioi_self
    have hi_2 : IntegrableOn F_def (Ioc s_B s_r) :=
      hInt_def.mono_set (fun s hs => huo_lt_sB.trans hs.1)
    rw [← hu1, setIntegral_union hd1 measurableSet_Ioi hi_sr hi_ioi,
      ← hu2, setIntegral_union hd2 measurableSet_Ioc hi_1 hi_2]
  -- Piece 1: Core tail `Ioc u_o s_B`
  have hPiece1 : ‖∫ s in Ioc u_o s_B, F_def s‖ ≤ (ε / 3) * scaleA P ν μ := by
    set K_core : ℝ := 96 * C_tr * C_Z * M_exp * scaleA P ν μ
    have hKc_nn : 0 ≤ K_core := by dsimp [K_core]; positivity
    obtain ⟨hint_exp, hval_exp⟩ :=
      integral_Ioc_exp_clockTheta_le_aniso hγ hν_pos hB_pos huo_pos.le huo_lt_sB.le
    have hpt_core : ∀ s ∈ Ioc u_o s_B,
        ‖F_def s‖ ≤ K_core *
          (Real.exp (-(γ / 2) * clockTheta ν s) * (ν ^ 2 * (clockTheta ν s) ^ 2)) := by
      intro s hs
      obtain ⟨hs_pos, hB_le_θ, hθ_le_inv, hs_lower, hwidth_eq⟩ := hclock_Ioc s hs
      have hs0 : 0 ≤ s := hs_pos.le
      set θ : ℝ := clockTheta ν s
      have hθ_base : b_base ≤ θ := hB_base.trans hB_le_θ
      have hθ1 : 1 ≤ θ := hB1.trans hB_le_θ
      have hθ0 : 0 < θ := lt_of_lt_of_le one_pos hθ1
      have ha_s : 0 < clockA ν s := by unfold clockA; positivity
      have hs_eq : clockAge ν θ = s := T22Sub.clockAge_clockTheta hν_pos ha_s
      have hν3_θ : ν ^ 3 ≤ θ := hν3_r.trans (hr_lt_B.le.trans hB_le_θ)
      -- Rescale `(w_ev s, u_odd s)` to `(Z_θ, U_Z)` on `d = dOfTheta ν θ`
      obtain ⟨hd1, hZ_mem, hZ_zc, hZ_ev, hUZ_bs, _, _⟩ :=
        heatColumn_even_props_aniso (P := P) hν_pos hθ0 hθ_le_inv hν3_θ hm hprep_zc hw_sym hw_ev_all
      set d : ℝ := dOfTheta ν θ
      set Z_θ : ℝ × ℝ → ℂ := heatColumn P ν w_ev θ
      set V_d : ℝ × ℝ → ℂ := canonicalPeriodized P ν θ
      have hVd_mem := (hBranch.2.1 ν θ hν_pos hθ0 hd1).1
      have hBr_θ := hBr_est ν ⟨hν_pos, hν1⟩ θ hθ_base hd1
      have hLong_θ0 := (hLong_est ν ⟨hν_pos, hν_long_le⟩ tr htr).2 w_ev u_odd hw_sym θ hθ_base hθ_le_inv
      set W_θ : ℝ := Real.exp (γ * θ) * θ ^ κ_re
      have hW_pos : 0 < W_θ := mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hθ0 _)
      have herr_le3 : ν + (ν ^ 3) ^ 2 / θ + Real.exp (-a₁ * θ / ν ^ 3) ≤ 3 := by
        have hν6 : (ν ^ 3) ^ 2 / θ ≤ 1 := by
          have h1 : (ν ^ 3) ^ 2 ≤ 1 := pow_le_one₀ (by positivity) (pow_le_one₀ hν_pos.le hν1)
          exact (div_le_one hθ0).2 (h1.trans hθ1)
        have hexp1 : Real.exp (-a₁ * θ / ν ^ 3) ≤ 1 :=
          Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 ha₁.le) hθ0.le) (by positivity))
        linarith
      have hLong_3 : ENNReal.ofReal W_θ * xNorm d m (Z_θ - V_d) ≤ ENNReal.ofReal (3 * C_long) := by
        refine hLong_θ0.trans (ENNReal.ofReal_le_ofReal ?_)
        have h1 : C_long0 ≤ C_long := le_max_left _ _
        have hnn : 0 ≤ ν + (ν ^ 3) ^ 2 / θ + Real.exp (-a₁ * θ / ν ^ 3) := by positivity
        nlinarith only [h1, hnn, herr_le3, hC_long]
      have hxZ_tri : xNorm d m Z_θ ≤ xNorm d m (Z_θ - V_d) + xNorm d m V_d := by
        have heq : Z_θ = (Z_θ - V_d) + V_d := by funext y; simp
        unfold xNorm; conv_lhs => rw [heq]
        exact eLpNorm_add_le (hZ_mem.sub hVd_mem).1 hVd_mem.1 one_le_two
      have hWZ : ENNReal.ofReal W_θ * xNorm d m Z_θ ≤ ENNReal.ofReal (C_br + 3 * C_long) := by
        calc ENNReal.ofReal W_θ * xNorm d m Z_θ
            ≤ ENNReal.ofReal W_θ * (xNorm d m (Z_θ - V_d) + xNorm d m V_d) :=
              mul_le_mul_of_nonneg_left hxZ_tri bot_le
          _ = ENNReal.ofReal W_θ * xNorm d m (Z_θ - V_d) + ENNReal.ofReal W_θ * xNorm d m V_d :=
              mul_add _ _ _
          _ ≤ ENNReal.ofReal (3 * C_long) + ENNReal.ofReal C_br := add_le_add hLong_3 hBr_θ
          _ = ENNReal.ofReal (C_br + 3 * C_long) := by
              rw [← ENNReal.ofReal_add (by positivity) hC_br.le]; congr 1; ring
      have hxZ_bd : xNorm d m Z_θ ≤
          ENNReal.ofReal ((C_br + 3 * C_long) * Real.exp (-γ * θ) * θ ^ (-κ_re)) := by
        have hWinv : W_θ⁻¹ = Real.exp (-γ * θ) * θ ^ (-κ_re) := by
          dsimp [W_θ]; rw [mul_inv, ← Real.exp_neg, neg_mul, ← Real.rpow_neg hθ0.le]
        have hsc := mul_le_mul_of_nonneg_left hWZ (bot_le : 0 ≤ ENNReal.ofReal W_θ⁻¹)
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hW_pos.le),
          inv_mul_cancel₀ hW_pos.ne', ENNReal.ofReal_one, one_mul,
          ← ENNReal.ofReal_mul (inv_nonneg.2 hW_pos.le), hWinv] at hsc
        exact hsc.trans (le_of_eq (by congr 1; ring))
      -- Bound `eLpNorm (u_odd s · j) 2` on `B0579.cell c`
      set a : ℝ := (ν * θ)⁻¹
      have ha_pos : 0 < a := inv_pos.2 (mul_pos hν_pos hθ0)
      set U_Z : ℝ × ℝ → Fin 2 → ℂ := fun y j =>
        (P.gaugeFactor ν)⁻¹ * ((a ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
          u_odd (clockAge ν θ) (Real.sqrt a * y.1, Real.sqrt a * y.2) j
      have hUZ_bd : velNorm d U_Z ≤
          ENNReal.ofReal (C_Z * Real.exp (-γ * θ) * θ ^ (-κ_re)) := by
        have hemb := (le_add_self.trans (hEmb d hd1 Z_θ hZ_mem hZ_zc hZ_ev U_Z hUZ_bs)).trans
          (mul_le_mul_of_nonneg_left hxZ_bd bot_le)
        rwa [← ENNReal.ofReal_mul hC_emb.le,
          show C_emb * ((C_br + 3 * C_long) * Real.exp (-γ * θ) * θ ^ (-κ_re)) =
            C_Z * Real.exp (-γ * θ) * θ ^ (-κ_re) by dsimp [C_Z]; ring] at hemb
      have hu_c_bd : ∀ j : Fin 2,
          (eLpNorm (fun x => u_odd s x j) 2 (volume.restrict (B0579.cell c))).toReal ≤
            ‖P.gaugeFactor ν‖ * (ν * θ) * (C_Z * Real.exp (-γ * θ) * θ ^ (-κ_re)) := by
        intro j
        have hgf_ne : P.gaugeFactor ν ≠ 0 := T22Sub.gaugeFactor_ne_zero P hν_pos
        have heq_u := eLpNorm_u_cell_eq_rescaled hc_pos ha_pos (P.gaugeFactor ν) hgf_ne
          (hw_sym.biotSavart s hs0).1 j
        have hd_cell : d = cellLen c a := by
          dsimp [d, a]
          rw [← T22Sub.clockA_clockAge hν_pos hθ0, hs_eq,
            T22Sub.dOfTheta_eq_cellLen hν_pos ha_s]
        have ha1 : a ^ (-1 : ℝ) = ν * θ := by dsimp [a]; rw [Real.rpow_neg_one, inv_inv]
        rw [← hd_cell, ha1] at heq_u
        have hUZ_j : (eLpNorm (fun y => U_Z y j) 2 (volume.restrict (B0579.cell d))).toReal ≤
            C_Z * Real.exp (-γ * θ) * θ ^ (-κ_re) :=
          ENNReal.toReal_le_of_le_ofReal (by positivity)
            ((eLpNorm_coord_le_velNorm U_Z j).trans hUZ_bd)
        dsimp only [U_Z] at hUZ_j
        rw [hs_eq] at hUZ_j
        rw [heq_u]
        exact mul_le_mul_of_nonneg_left hUZ_j (by positivity)
      -- Bound `eLpNorm (tr.v s · i) 2` on `B0579.cell c`
      have hl2_s : UnforcedLeray.Train.cellL2 c (tr.v s) ≤ ENNReal.ofReal (C_tr * ν * θ) := by
        have h := (htr_l2 ν hν_pos hν_tr_le tr htr s hs0).1 (hs.2.trans hsB_le_sc)
        dsimp only [UnforcedLeray.Short.PartI.trainPeriod] at h
        rw [hwidth_eq, ← mul_assoc] at h; exact h
      have hv_c_bd : ∀ i : Fin 2,
          (eLpNorm (fun x => tr.v s x i) 2 (volume.restrict (B0579.cell c))).toReal ≤
            C_tr * ν * θ := fun i =>
        ENNReal.toReal_le_of_le_ofReal (by positivity)
          ((memLp_train_coord_of_cellL2 hs0 tr (hv_fin s hs0) i).2.trans hl2_s)
      obtain ⟨_, hdef_bd⟩ := integrable_and_norm_defectPairIntegrand_cell
        (by positivity : 0 ≤ C_tr * ν * θ)
        (by positivity : 0 ≤ ‖P.gaugeFactor ν‖ * (ν * θ) * (C_Z * Real.exp (-γ * θ) * θ ^ (-κ_re)))
        (fun i => (memLp_train_coord_of_cellL2 hs0 tr (hv_fin s hs0) i).1)
        (hw_sym.biotSavart s hs0).1 hv_c_bd hu_c_bd
      -- Combine powers of `s`, `ν`, and `θ`
      have hnorm_F : ‖F_def s‖ =
          c⁻¹ * s ^ (-σ) * s ^ (-3 / 2 : ℝ) *
            ‖∫ x in B0579.cell c, defectPairIntegrand (fun z i => tr.v s z i) (u_odd s) x‖ := by
        dsimp only [F_def]
        rw [pairs_defect_eq_defectPairIntegrand hν_pos tr μ hs0 (hv_fin s hs0)
            (hw_sym.biotSavart s hs0),
          norm_mul, norm_mul, norm_mul,
          Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hc_pos.le),
          Complex.norm_cpow_eq_rpow_re_of_pos hs_pos (-μ), Complex.neg_re,
          Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hs0 _)]
        ring
      have hsinv_le : s⁻¹ ≤ 2 * ν ^ 2 * θ := by
        have h := inv_anti₀ (by positivity : 0 < (2 * ν ^ 2 * θ)⁻¹) hs_lower
        rwa [inv_inv] at h
      have hp0_pos : 0 < σ + 3 / 2 := by linarith
      have hp0_le3 : σ + 3 / 2 ≤ 3 := by linarith
      have hs_pow : c⁻¹ * s ^ (-σ) * s ^ (-3 / 2 : ℝ) ≤
          8 * (ν ^ (3 + 2 * σ) / c) * θ ^ (σ + 3 / 2) := by
        have hcomb : s ^ (-σ) * s ^ (-3 / 2 : ℝ) = (s⁻¹) ^ (σ + 3 / 2) := by
          rw [← Real.rpow_add hs_pos, Real.inv_rpow hs0, ← Real.rpow_neg hs0]
          congr 1; ring
        have hsp : (s⁻¹) ^ (σ + 3 / 2) ≤ 8 * ν ^ (3 + 2 * σ) * θ ^ (σ + 3 / 2) := by
          calc (s⁻¹) ^ (σ + 3 / 2)
              ≤ (2 * ν ^ 2 * θ) ^ (σ + 3 / 2) :=
                Real.rpow_le_rpow (inv_nonneg.2 hs0) hsinv_le hp0_pos.le
            _ = 2 ^ (σ + 3 / 2) * (ν ^ 2) ^ (σ + 3 / 2) * θ ^ (σ + 3 / 2) := by
                rw [Real.mul_rpow (by positivity) hθ0.le, Real.mul_rpow (by norm_num) (sq_nonneg ν)]
            _ ≤ 8 * (ν ^ 2) ^ (σ + 3 / 2) * θ ^ (σ + 3 / 2) := by
                have h2 : (2 : ℝ) ^ (σ + 3 / 2) ≤ 8 := by
                  calc (2 : ℝ) ^ (σ + 3 / 2) ≤ (2 : ℝ) ^ (3 : ℝ) :=
                        Real.rpow_le_rpow_of_exponent_le (by norm_num) hp0_le3
                    _ = 8 := by norm_num
                gcongr
            _ = 8 * ν ^ (3 + 2 * σ) * θ ^ (σ + 3 / 2) := by
                congr 2; rw [← Real.rpow_natCast ν 2, ← Real.rpow_mul hν_pos.le]; push_cast; ring_nf
        rw [mul_assoc, hcomb]
        calc c⁻¹ * (s⁻¹) ^ (σ + 3 / 2)
            ≤ c⁻¹ * (8 * ν ^ (3 + 2 * σ) * θ ^ (σ + 3 / 2)) :=
              mul_le_mul_of_nonneg_left hsp (inv_nonneg.2 hc_pos.le)
          _ = 8 * (ν ^ (3 + 2 * σ) / c) * θ ^ (σ + 3 / 2) := by ring
      have hθ_exp : θ ^ (σ + 3 / 2) * θ ^ (-κ_re) * Real.exp (-γ * θ) ≤
          M_exp * Real.exp (-(γ / 2) * θ) := by
        rw [← Real.rpow_add hθ0, ← sub_eq_add_neg]
        exact rpow_mul_exp_le_half_exp_aniso hγ hθ1 M_pow
          ((by linarith : σ + 3 / 2 - κ_re ≤ 3 - κ_re).trans (Nat.le_ceil _))
      rw [hnorm_F]
      calc c⁻¹ * s ^ (-σ) * s ^ (-3 / 2 : ℝ) *
              ‖∫ x in B0579.cell c, defectPairIntegrand (fun z i => tr.v s z i) (u_odd s) x‖
          ≤ (8 * (ν ^ (3 + 2 * σ) / c) * θ ^ (σ + 3 / 2)) *
              (12 * (C_tr * ν * θ) *
                (‖P.gaugeFactor ν‖ * (ν * θ) * (C_Z * Real.exp (-γ * θ) * θ ^ (-κ_re)))) :=
            mul_le_mul hs_pow hdef_bd (norm_nonneg _) (by positivity)
        _ = 96 * C_tr * C_Z * (‖P.gaugeFactor ν‖ * ν ^ (3 + 2 * σ) / c) *
              (θ ^ (σ + 3 / 2) * θ ^ (-κ_re) * Real.exp (-γ * θ)) * (ν ^ 2 * θ ^ 2) := by ring
        _ = 96 * C_tr * C_Z * scaleA P ν μ *
              (θ ^ (σ + 3 / 2) * θ ^ (-κ_re) * Real.exp (-γ * θ)) * (ν ^ 2 * θ ^ 2) := by
            unfold scaleA; dsimp [c]
        _ ≤ 96 * C_tr * C_Z * scaleA P ν μ *
              (M_exp * Real.exp (-(γ / 2) * θ)) * (ν ^ 2 * θ ^ 2) := by gcongr
        _ = K_core * (Real.exp (-(γ / 2) * θ) * (ν ^ 2 * θ ^ 2)) := by dsimp [K_core]; ring
    calc ‖∫ s in Ioc u_o s_B, F_def s‖
        ≤ ∫ s in Ioc u_o s_B, ‖F_def s‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ s in Ioc u_o s_B,
            K_core * (Real.exp (-(γ / 2) * clockTheta ν s) * (ν ^ 2 * (clockTheta ν s) ^ 2)) :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
            (hint_exp.const_mul K_core)
            (ae_restrict_mem measurableSet_Ioc |>.mono hpt_core)
      _ = K_core * ∫ s in Ioc u_o s_B,
            Real.exp (-(γ / 2) * clockTheta ν s) * (ν ^ 2 * (clockTheta ν s) ^ 2) :=
          integral_const_mul _ _
      _ ≤ K_core * ((2 / γ) * Real.exp (-(γ / 2) * B)) :=
          mul_le_mul_of_nonneg_left hval_exp hKc_nn
      _ = (C_core * Real.exp (-(γ / 2) * B)) * scaleA P ν μ := by
          dsimp [K_core, C_core]; ring
      _ ≤ (ε / 3) * scaleA P ν μ := mul_le_mul_of_nonneg_right hCore_eps hscaleA_nn
  -- Piece 2: Compact window `Ioc s_B s_r`
  have hPiece2 : ‖∫ s in Ioc s_B s_r, F_def s‖ ≤ (ε / 3) * scaleA P ν μ :=
    hWin tr htr w_ev u_odd hw_sym hw_ev_all μ hμ
  -- Piece 3: Small-clock impulse tail `Ioi s_r`
  have hPiece3 : ‖∫ s in Ioi s_r, F_def s‖ ≤ (ε / 3) * scaleA P ν μ := by
    have hr_le_inv : r ≤ ν⁻¹ := by
      have hB_le_inv : B ≤ ν⁻¹ := by
        have hνB : ν * B ≤ 1 := by
          calc ν * B ≤ (9 * B ^ 2)⁻¹ * B := mul_le_mul_of_nonneg_right hν_9B2 hB_pos.le
            _ = (9 * B)⁻¹ := by field_simp
            _ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
        calc B = ν⁻¹ * (ν * B) := by field_simp [hν_pos.ne']
          _ ≤ ν⁻¹ * 1 := mul_le_mul_of_nonneg_left hνB (inv_nonneg.2 hν_pos.le)
          _ = ν⁻¹ := mul_one _
      exact hr_lt_B.le.trans hB_le_inv
    obtain ⟨hdr1, hZr_mem, hZr_zc, hZr_ev, hUZr_bs, hJZr_eq, _⟩ :=
      heatColumn_even_props_aniso (P := P) hν_pos hr_pos hr_le_inv hν3_r hm hprep_zc hw_sym hw_ev_all
    set d_r : ℝ := dOfTheta ν r
    have hdr0 : 0 < d_r := lt_of_lt_of_le one_pos hdr1
    set Z_r : ℝ × ℝ → ℂ := heatColumn P ν w_ev r
    set V_dr : ℝ × ℝ → ℂ := canonicalPeriodized P ν r
    -- Bound `kinNorm d_r Z_r ≤ ENNReal.ofReal K_Z_max` via `hComp_r` at `θ = r`
    have hComp_at_r := (hComp_r tr htr w_ev u_odd hw_sym r
      ⟨le_rfl, hr_lt_B.le.trans (le_max_left _ _)⟩).1
    obtain ⟨hVdr_mem, hVdr_zc, hVdr_ev, _⟩ := hBranch.2.1 ν r hν_pos hr_pos hdr1
    obtain ⟨U_Vdr, hUVdr_bs⟩ := exists_isBiotSavart_of_memX hm hdr1 V_dr hVdr_mem hVdr_zc hVdr_ev
    set a_r : ℝ := (ν * r)⁻¹
    set U_Zr : ℝ × ℝ → Fin 2 → ℂ := fun y j =>
      (P.gaugeFactor ν)⁻¹ * ((a_r ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
        u_odd s_r (Real.sqrt a_r * y.1, Real.sqrt a_r * y.2) j
    have hdiff_bs : IsBiotSavart d_r (Z_r - V_dr) (fun y j => U_Zr y j - U_Vdr y j) :=
      isBiotSavart_sub_aniso (by linarith) hZr_mem hVdr_mem hUZr_bs hUVdr_bs
    have hUVdr_bd : velNorm d_r U_Vdr ≤ ENNReal.ofReal (C_emb * C_V) := by
      calc velNorm d_r U_Vdr
          ≤ ENNReal.ofReal C_emb * xNorm d_r m V_dr :=
            le_add_self.trans (hEmb d_r hdr1 V_dr hVdr_mem hVdr_zc hVdr_ev U_Vdr hUVdr_bs)
        _ ≤ ENNReal.ofReal C_emb * ENNReal.ofReal C_V :=
            mul_le_mul_of_nonneg_left
              (hVd_xnorm ν ⟨hν_pos, hν1⟩ r ⟨hr_pos, hr_lt_B.le⟩ hdr1) bot_le
        _ = ENNReal.ofReal (C_emb * C_V) := (ENNReal.ofReal_mul hC_emb.le).symm
    have hUZr_coord : ∀ j : Fin 2,
        eLpNorm (fun y => U_Zr y j) 2 (volume.restrict (B0579.cell d_r)) ≤
          ENNReal.ofReal (1 + C_emb * C_V) := by
      intro j
      have heq_j : (fun y => U_Zr y j) =
          (fun y => U_Zr y j - U_Vdr y j) + (fun y => U_Vdr y j) := by funext y; simp
      have htri : eLpNorm (fun y => U_Zr y j) 2 (volume.restrict (B0579.cell d_r)) ≤
          eLpNorm (fun y => U_Zr y j - U_Vdr y j) 2 (volume.restrict (B0579.cell d_r)) +
            eLpNorm (fun y => U_Vdr y j) 2 (volume.restrict (B0579.cell d_r)) := by
        conv_lhs => rw [heq_j]
        exact eLpNorm_add_le (hdiff_bs.1 j).1 (hUVdr_bs.1 j).1 one_le_two
      have hj1 : eLpNorm (fun y => U_Zr y j - U_Vdr y j) 2 (volume.restrict (B0579.cell d_r)) ≤
          ENNReal.ofReal 1 :=
        (eLpNorm_coord_le_velNorm (fun y k => U_Zr y k - U_Vdr y k) j).trans
          ((kinNorm_eq_velNorm_aniso hdr0 hdiff_bs).symm.le.trans hComp_at_r)
      have hj2 : eLpNorm (fun y => U_Vdr y j) 2 (volume.restrict (B0579.cell d_r)) ≤
          ENNReal.ofReal (C_emb * C_V) :=
        (eLpNorm_coord_le_velNorm U_Vdr j).trans hUVdr_bd
      calc eLpNorm (fun y => U_Zr y j) 2 (volume.restrict (B0579.cell d_r))
          ≤ ENNReal.ofReal 1 + ENNReal.ofReal (C_emb * C_V) := htri.trans (add_le_add hj1 hj2)
        _ = ENNReal.ofReal (1 + C_emb * C_V) :=
            (ENNReal.ofReal_add zero_le_one (by positivity)).symm
    have hkin_Zr : kinNorm d_r Z_r ≤ ENNReal.ofReal K_Z_max := by
      refine (iInf₂_le U_Zr hUZr_bs).trans ?_
      unfold velNorm
      rw [Fin.sum_univ_two]
      have hsq : eLpNorm (fun x => U_Zr x 0) 2 (volume.restrict (B0579.cell d_r)) ^ 2 +
            eLpNorm (fun x => U_Zr x 1) 2 (volume.restrict (B0579.cell d_r)) ^ 2 ≤
          ENNReal.ofReal K_Z_max ^ 2 := by
        have h0 := pow_le_pow_left' (hUZr_coord 0) 2
        have h1 := pow_le_pow_left' (hUZr_coord 1) 2
        refine (add_le_add h0 h1).trans ?_
        rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_pow hKZ_pos.le,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        dsimp [K_Z_max]; nlinarith only [sq_nonneg (1 + C_emb * C_V)]
      calc (eLpNorm (fun x => U_Zr x 0) 2 (volume.restrict (B0579.cell d_r)) ^ 2 +
              eLpNorm (fun x => U_Zr x 1) 2 (volume.restrict (B0579.cell d_r)) ^ 2) ^
              (1 / 2 : ℝ)
          ≤ (ENNReal.ofReal K_Z_max ^ 2) ^ (1 / 2 : ℝ) :=
            ENNReal.rpow_le_rpow hsq (by positivity)
        _ = ENNReal.ofReal K_Z_max := by
            rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
    -- Restart `(w_ev, u_odd)` at `s_r` and rescale by `(P.gaugeFactor ν)⁻¹`
    have hs_r0 : 0 ≤ s_r := T22Sub.clockAge_nonneg hν_pos hr_pos hr_le_inv
    set w_sc : ℝ → ℝ × ℝ → ℂ := fun s x => (P.gaugeFactor ν)⁻¹ * w_ev s x
    set u_sc : ℝ → ℝ × ℝ → Fin 2 → ℂ := fun s x j => (P.gaugeFactor ν)⁻¹ * u_odd s x j
    have hw_sc : IsLinearisedFlow ν c m tr s_r (Jscale (ν * r)⁻¹ Z_r) w_sc u_sc := by
      rw [hJZr_eq]
      exact isLinearisedFlow_smul_aniso (by linarith) (P.gaugeFactor ν)⁻¹ (hw_sym.restart hs_r0)
    have himp := hImp_est ν ⟨hν_pos, hν_imp_le⟩ tr htr r hr_pos hr_lt_B.le
      Z_r hZr_mem hZr_zc hZr_ev w_sc u_sc hw_sc μ hμ
    have hexp0 : (-3 / 2 - ((0 : ℕ) : ℝ) / 2 : ℝ) = -3 / 2 := by norm_num
    have hexp_r : (σ + 5 / 2 + ((0 : ℕ) : ℝ) / 2 : ℝ) = σ + 5 / 2 := by norm_num
    rw [hexp0, hexp_r, pow_zero, mul_one] at himp
    have hmax1 : max 1 ((ν ^ 3 / r) ^ (1 / 4 : ℝ)) = 1 := by
      apply max_eq_left
      have hdiv1 : ν ^ 3 / r ≤ 1 := (div_le_one hr_pos).2 hν3_r
      calc (ν ^ 3 / r) ^ (1 / 4 : ℝ)
          ≤ (1 : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_le_rpow (by positivity) hdiv1 (by norm_num)
        _ = 1 := Real.one_rpow _
    rw [hmax1, mul_one] at himp
    have hr_pow : r ^ (σ + 5 / 2) ≤ r := by
      calc r ^ (σ + 5 / 2)
          ≤ r ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hr_pos hr_le1 (by linarith)
        _ = r := Real.rpow_one r
    have hfac_le : ENNReal.ofReal (C_imp0 * (ν ^ (3 + 2 * σ) / c) * r ^ (σ + 5 / 2)) ≤
        ENNReal.ofReal (C_imp * (ν ^ (3 + 2 * σ) / c) * r) := by
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : C_imp0 ≤ C_imp := le_max_left _ _
      exact mul_le_mul (mul_le_mul_of_nonneg_right h1 (by positivity)) hr_pow
        (Real.rpow_nonneg hr_pos.le _) (by positivity)
    have hgf_ne : P.gaugeFactor ν ≠ 0 := T22Sub.gaugeFactor_ne_zero P hν_pos
    have hu_eq : ∀ s : ℝ, u_odd s = fun x j => P.gaugeFactor ν * u_sc s x j := by
      intro s; funext x j; dsimp [u_sc]; rw [← mul_assoc, mul_inv_cancel₀ hgf_ne, one_mul]
    have hlint_tail : ∫⁻ s in Ioi s_r, ‖F_def s‖ₑ ≤
        ENNReal.ofReal ((6 * C_imp * K_Z_max * r) * scaleA P ν μ) := by
      calc ∫⁻ s in Ioi s_r, ‖F_def s‖ₑ
          ≤ ∫⁻ s in Ioi s_r,
              6 * (ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * sAbs tr μ (u_odd s) s) :=
            setLIntegral_mono' measurableSet_Ioi fun s hs =>
              enorm_stressDefect_le_sAbs hν_pos tr μ (u_odd s) (hs_r0.trans hs.le)
        _ = 6 * ∫⁻ s in Ioi s_r,
              ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * sAbs tr μ (u_odd s) s :=
            lintegral_const_mul' _ _ (by norm_num)
        _ = 6 * ∫⁻ s in Ioi s_r,
              ENNReal.ofReal ‖P.gaugeFactor ν‖ *
                (ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * sAbs tr μ (u_sc s) s) := by
            congr 1; refine lintegral_congr fun s => ?_
            conv_lhs => rw [hu_eq s, sAbs_smul_aniso]
            exact mul_left_comm _ _ _
        _ = 6 * (ENNReal.ofReal ‖P.gaugeFactor ν‖ *
              ∫⁻ s in Ioi s_r, ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * sAbs tr μ (u_sc s) s) := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ ≤ 6 * (ENNReal.ofReal ‖P.gaugeFactor ν‖ *
              (ENNReal.ofReal (C_imp * (ν ^ (3 + 2 * σ) / c) * r) * ENNReal.ofReal K_Z_max)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left
                (himp.trans (mul_le_mul hfac_le hkin_Zr bot_le bot_le)) bot_le) bot_le
        _ = ENNReal.ofReal ((6 * C_imp * K_Z_max * r) * scaleA P ν μ) := by
            have h6 : (6 : ℝ≥0∞) = ENNReal.ofReal 6 := by norm_num
            rw [h6, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (norm_nonneg _),
              ← ENNReal.ofReal_mul (by norm_num)]
            congr 1; unfold scaleA; dsimp [c]; ring
    have hen_int : ENNReal.ofReal ‖∫ s in Ioi s_r, F_def s‖ ≤
        ENNReal.ofReal ((ε / 3) * scaleA P ν μ) := by
      rw [ofReal_norm]
      exact (enorm_integral_le_lintegral_enorm _).trans
        (hlint_tail.trans (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right hImp_eps hscaleA_nn)))
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by positivity) hscaleA_nn)).1 hen_int
  -- Combine all three pieces
  rw [hsplit_all]
  calc ‖(∫ s in Ioc u_o s_B, F_def s) + (∫ s in Ioc s_B s_r, F_def s) +
          (∫ s in Ioi s_r, F_def s)‖
      ≤ ‖(∫ s in Ioc u_o s_B, F_def s) + (∫ s in Ioc s_B s_r, F_def s)‖ +
          ‖∫ s in Ioi s_r, F_def s‖ := norm_add_le _ _
    _ ≤ ‖∫ s in Ioc u_o s_B, F_def s‖ + ‖∫ s in Ioc s_B s_r, F_def s‖ +
          ‖∫ s in Ioi s_r, F_def s‖ := add_le_add (norm_add_le _ _) le_rfl
    _ ≤ (ε / 3) * scaleA P ν μ + (ε / 3) * scaleA P ν μ + (ε / 3) * scaleA P ν μ :=
        add_le_add (add_le_add hPiece1 hPiece2) hPiece3
    _ = ε * scaleA P ν μ := by ring


end UnforcedLeray.Short.IIIa.AnisoSynthAux

end
