import UnforcedLeray.Short.PartIIb.Tasks.BlockFactorization.FrozenEulerSplitting.PeriodizedCylinderCoord.PeriodizeTail
import UnforcedLeray.Short.PartIIb.Tasks.BlockFactorization.FrozenEulerSplitting.PeriodizedCylinderCoord.DualApprox

/-!
# `PartII-b:F2/3/2` (`PeriodizedCylinderCoord.lean`): Periodized cylinder coordinates for frozen Euler

Source of record: `the November 2 reference manuscript` (SP), lines 2167–2171,
2347–2358 (`short-sp:dichotomy`).

Proves `periodizedCylinderCoordStep_proof : UnforcedLeray.Short.IIb.PeriodizedCylinderCoordStep`
unconditionally by combining:
1. Uniform `X_G` Gaussian decay and zero integral of the dilated planar direct modes
   (`PeriodizedCylinderCoord/GaussDil.lean`);
2. Periodized `Xmc c m` norm bounds, zero circulation on `B0579.cell c`, and exponential
   `O(exp(-c² / (128 (1 + Sig))))` convergence `(Jc c m).comp (ι_c c σ) → ι_pl σ` in `Xm m`
   (`PeriodizedCylinderCoord/PeriodizeTail.lean`);
3. Uniform restricted dual approximation `(π_pl σ).comp (Jc c m ∘L Rc c m - id) → 0` on
   `σ ∈ Icc 0 Sig` via Hilbert-adjoint compactness and 2×2 Neumann normalization of
   `(π_pl σ ∘L Jc c m) ∘L (ι_c c σ)` (`PeriodizedCylinderCoord/DualApprox.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

open UnforcedLeray UnforcedLeray.Short.IIb UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.Short.IIb.PeriodizedCylCoordAux in
theorem periodizedCylinderCoordStep_proof :
    UnforcedLeray.Short.IIb.PeriodizedCylinderCoordStep := by
  intro m hm Sig lam q hSig hEig ι_pl π_pl _hι_cont hπ_cont h_id_pl h_ae_pl
  set A : ℝ := 1 + Sig
  have hm0 : 0 ≤ m := by linarith
  have hA1 : 1 ≤ A := by dsimp [A]; linarith
  have hA0 : 0 < A := by linarith
  have hq : Blueprint.Planar.MemXG q := hEig.memXG
  have hqc : ContinuousOn q (Ioi 0) := hEig.smooth.continuousOn
  obtain ⟨K_norm, K_tail, hKn_nn, hKt_nn, hMode⟩ :=
    exists_frozenDirectMode_memLp_and_tail hm0 hA1 hq hqc
  -- Periodized direct mode Lp elements and coordinate injection `ι_c`
  let modeLp : ∀ c : ℝ, ℝ → Fin 2 → Xmc c m := fun c σ i =>
    if h : 1 ≤ c ∧ σ ∈ Icc 0 Sig then
      (hMode c (1 + σ) h.1 (by linarith [h.2.1]) (by dsimp [A]; linarith [h.2.2]) i).1.toLp
        (frozenDirectMode q c (1 + σ) i)
    else 0
  let proj : Fin 2 → (E2 →L[ℝ] ℝ) := fun i => EuclideanSpace.proj i
  let ι_c : ∀ c : ℝ, ℝ → (E2 →L[ℝ] Xmc c m) := fun c σ =>
    ∑ i : Fin 2, (proj i).smulRight (modeLp c σ i)
  have hproj_norm : ∀ i : Fin 2, ‖proj i‖ ≤ 1 := fun i =>
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun α => by
      simpa [proj] using PiLp.norm_apply_le α i
  have hmode_ae : ∀ {c σ : ℝ}, 1 ≤ c → σ ∈ Icc 0 Sig → ∀ i : Fin 2,
      (modeLp c σ i : B0579.Plane → ℝ) =ᵐ[B0579.cellMeasure c m]
        frozenDirectMode q c (1 + σ) i := by
    intro c σ hc1 hσ i
    have h : 1 ≤ c ∧ σ ∈ Icc 0 Sig := ⟨hc1, hσ⟩
    dsimp only [modeLp]
    simp only [h, and_self, ↓reduceDIte]
    exact MemLp.coeFn_toLp _
  have hmode_norm : ∀ {c σ : ℝ}, 1 ≤ c → σ ∈ Icc 0 Sig → ∀ i : Fin 2,
      ‖modeLp c σ i‖ ≤ K_norm := by
    intro c σ hc1 hσ i
    have h : 1 ≤ c ∧ σ ∈ Icc 0 Sig := ⟨hc1, hσ⟩
    dsimp only [modeLp]
    simp only [h, and_self, ↓reduceDIte]
    rw [Lp.norm_toLp]
    have hbd := (hMode c (1 + σ) hc1 (by linarith [hσ.1]) (by dsimp [A]; linarith [hσ.2]) i).2.1
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbd).trans (ENNReal.toReal_ofReal hKn_nn).le
  have hι_ae : ∀ {c σ : ℝ}, 1 ≤ c → σ ∈ Icc 0 Sig → ∀ α : E2,
      (ι_c c σ α : B0579.Plane → ℝ) =ᵐ[B0579.cellMeasure c m]
        fun x => ∑ i : Fin 2, α i * frozenDirectMode q c (1 + σ) i x := by
    intro c σ hc1 hσ α
    have hι_eq : ι_c c σ α = α 0 • modeLp c σ 0 + α 1 • modeLp c σ 1 := by
      simp [ι_c, proj, Fin.sum_univ_two]
    rw [hι_eq]
    filter_upwards [Lp.coeFn_add (α 0 • modeLp c σ 0) (α 1 • modeLp c σ 1),
      Lp.coeFn_smul (α 0) (modeLp c σ 0), Lp.coeFn_smul (α 1) (modeLp c σ 1),
      hmode_ae hc1 hσ 0, hmode_ae hc1 hσ 1] with x hadd hs0 hs1 e0 e1
    rw [hadd, Pi.add_apply, hs0, hs1, Pi.smul_apply, Pi.smul_apply, Fin.sum_univ_two]
    have e0' : (modeLp c σ 0 : B0579.Plane → ℝ) x = frozenDirectMode q c (1 + σ) 0 x := e0
    have e1' : (modeLp c σ 1 : B0579.Plane → ℝ) x = frozenDirectMode q c (1 + σ) 1 x := e1
    rw [e0', e1']
    simp [smul_eq_mul]
  have hι_circ : ∀ {c σ : ℝ}, 1 ≤ c → σ ∈ Icc 0 Sig → ∀ α : E2,
      HasZeroCirculationR c (ι_c c σ α) := by
    intro c σ hc1 hσ α
    have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
    have ha1 : 1 ≤ 1 + σ := by linarith [hσ.1]
    have haA : 1 + σ ≤ A := by dsimp [A]; linarith [hσ.2]
    obtain ⟨hint0, hzero0⟩ := hasZeroCirculationR_frozenDirectMode hc0 ha1 haA hq hqc 0
    obtain ⟨hint1, hzero1⟩ := hasZeroCirculationR_frozenDirectMode hc0 ha1 haA hq hqc 1
    set g : B0579.Plane → ℝ :=
      fun x => α 0 * frozenDirectMode q c (1 + σ) 0 x + α 1 * frozenDirectMode q c (1 + σ) 1 x
    have hg_eq : (fun x => ∑ i : Fin 2, α i * frozenDirectMode q c (1 + σ) i x) = g := by
      funext x
      exact Fin.sum_univ_two _
    have hint_g : IntegrableOn g (B0579.cell c) volume :=
      (hint0.const_mul (α 0)).add (hint1.const_mul (α 1))
    have hzero_g : ∫ x in B0579.cell c, g x = 0 := by
      change ∫ x in B0579.cell c,
        (α 0 * frozenDirectMode q c (1 + σ) 0 x + α 1 * frozenDirectMode q c (1 + σ) 1 x) = 0
      rw [integral_add (hint0.const_mul (α 0)) (hint1.const_mul (α 1)),
        integral_const_mul, integral_const_mul, hzero0, hzero1]
      simp
    have hae_cell : (ι_c c σ α : B0579.Plane → ℝ) =ᵐ[B0579.cellMeasure c m] g := by
      rw [← hg_eq]
      exact hι_ae hc1 hσ α
    have hae_vol : g =ᵐ[volume.restrict (B0579.cell c)] (ι_c c σ α : B0579.Plane → ℝ) :=
      (B0579.ac_cellMeasure c m).ae_eq hae_cell.symm
    exact ⟨hint_g.congr hae_vol, (integral_congr_ae hae_vol.symm).trans hzero_g⟩
  have hι_norm : ∀ {c σ : ℝ}, 1 ≤ c → σ ∈ Icc 0 Sig → ‖ι_c c σ‖ ≤ 2 * K_norm := by
    intro c σ hc1 hσ
    dsimp only [ι_c]
    rw [Fin.sum_univ_two]
    calc ‖(proj 0).smulRight (modeLp c σ 0) + (proj 1).smulRight (modeLp c σ 1)‖
        ≤ ‖(proj 0).smulRight (modeLp c σ 0)‖ + ‖(proj 1).smulRight (modeLp c σ 1)‖ :=
          norm_add_le _ _
      _ ≤ K_norm + K_norm := by
          refine add_le_add ?_ ?_
          · rw [ContinuousLinearMap.norm_smulRight_apply]
            calc ‖proj 0‖ * ‖modeLp c σ 0‖
                ≤ 1 * K_norm :=
                  mul_le_mul (hproj_norm 0) (hmode_norm hc1 hσ 0) (norm_nonneg _) zero_le_one
              _ = K_norm := one_mul _
          · rw [ContinuousLinearMap.norm_smulRight_apply]
            calc ‖proj 1‖ * ‖modeLp c σ 1‖
                ≤ 1 * K_norm :=
                  mul_le_mul (hproj_norm 1) (hmode_norm hc1 hσ 1) (norm_nonneg _) zero_le_one
              _ = K_norm := one_mul _
      _ = 2 * K_norm := by ring
  -- Basis decomposition on `E2` to bound `‖(Jc c m).comp (ι_c c σ) - ι_pl σ‖`
  let eBasis : Fin 2 → E2 := fun i => PiLp.single 2 i (1 : ℝ)
  have hα_decomp : ∀ α : E2, α = α 0 • eBasis 0 + α 1 • eBasis 1 := by
    intro α
    ext j
    fin_cases j <;> simp [eBasis]
  have hop_le_basis : ∀ (L : E2 →L[ℝ] Xm m) {B0 B1 : ℝ},
      0 ≤ B0 → 0 ≤ B1 → ‖L (eBasis 0)‖ ≤ B0 → ‖L (eBasis 1)‖ ≤ B1 → ‖L‖ ≤ B0 + B1 := by
    intro L B0 B1 hB0 hB1 h0 h1
    refine ContinuousLinearMap.opNorm_le_bound _ (add_nonneg hB0 hB1) fun α => ?_
    have hα0 : |α 0| ≤ ‖α‖ := by simpa using PiLp.norm_apply_le α 0
    have hα1 : |α 1| ≤ ‖α‖ := by simpa using PiLp.norm_apply_le α 1
    calc ‖L α‖
        = ‖L (α 0 • eBasis 0 + α 1 • eBasis 1)‖ := by rw [← hα_decomp α]
      _ = ‖α 0 • L (eBasis 0) + α 1 • L (eBasis 1)‖ := by rw [map_add, map_smul, map_smul]
      _ ≤ ‖α 0 • L (eBasis 0)‖ + ‖α 1 • L (eBasis 1)‖ := norm_add_le _ _
      _ = |α 0| * ‖L (eBasis 0)‖ + |α 1| * ‖L (eBasis 1)‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ ‖α‖ * B0 + ‖α‖ * B1 :=
          add_le_add (mul_le_mul hα0 h0 (norm_nonneg _) (norm_nonneg α))
            (mul_le_mul hα1 h1 (norm_nonneg _) (norm_nonneg α))
      _ = (B0 + B1) * ‖α‖ := by ring
  have hι_tail : ∀ {c σ : ℝ}, 1 ≤ c → σ ∈ Icc 0 Sig →
      ‖(Jc c m).comp (ι_c c σ) - ι_pl σ‖ ≤
        2 * K_tail * Real.exp (-(c ^ 2 / (128 * A))) := by
    intro c σ hc1 hσ
    set tailVal : ℝ := K_tail * Real.exp (-(c ^ 2 / (128 * A)))
    have htv_nn : 0 ≤ tailVal := by dsimp [tailVal]; positivity
    have hbasis_bd : ∀ i : Fin 2,
        ‖((Jc c m).comp (ι_c c σ) - ι_pl σ) (eBasis i)‖ ≤ tailVal := by
      intro i
      have hιc_ei : ι_c c σ (eBasis i) = modeLp c σ i := by
        fin_cases i <;>
          simp [ι_c, proj, eBasis, Fin.sum_univ_two]
      have hind_ae : (B0579.cell c).indicator (modeLp c σ i : B0579.Plane → ℝ) =ᵐ[planeMeasure m]
          (B0579.cell c).indicator (frozenDirectMode q c (1 + σ) i) := by
        have hm_eq :
            (modeLp c σ i : B0579.Plane → ℝ) =ᵐ[(planeMeasure m).restrict (B0579.cell c)]
              frozenDirectMode q c (1 + σ) i := by
          rw [← cellMeasure_eq_restrict_planeMeasure]
          exact hmode_ae hc1 hσ i
        filter_upwards [(ae_restrict_iff' (B0579.measurableSet_cell c)).mp hm_eq] with x hx
        by_cases hxc : x ∈ B0579.cell c
        · simp [hxc, hx hxc]
        · simp [hxc]
      have hjc_ae : (Jc c m (ι_c c σ (eBasis i)) : B0579.Plane → ℝ) =ᵐ[planeMeasure m]
          (B0579.cell c).indicator (frozenDirectMode q c (1 + σ) i) := by
        rw [hιc_ei]
        exact (coeFn_zeroExtFun c m (modeLp c σ i)).trans hind_ae
      have hpl_ae : (ι_pl σ (eBasis i) : B0579.Plane → ℝ) =ᵐ[planeMeasure m]
          planarFrozenDirectMode q (1 + σ) i := by
        filter_upwards [h_ae_pl σ hσ (eBasis i)] with x hx
        rw [hx, Fin.sum_univ_two]
        fin_cases i <;> simp [eBasis]
      have hdiff_ae :
          ((((Jc c m).comp (ι_c c σ) - ι_pl σ) (eBasis i) : Xm m) : B0579.Plane → ℝ)
            =ᵐ[planeMeasure m]
              (B0579.cell c).indicator (frozenDirectMode q c (1 + σ) i) -
                planarFrozenDirectMode q (1 + σ) i := by
        change (Jc c m (ι_c c σ (eBasis i)) - ι_pl σ (eBasis i) : Xm m) =ᵐ[planeMeasure m] _
        filter_upwards [Lp.coeFn_sub (Jc c m (ι_c c σ (eBasis i))) (ι_pl σ (eBasis i)),
          hjc_ae, hpl_ae] with x hsub hjc hpl
        rw [hsub, Pi.sub_apply, Pi.sub_apply]
        have hjc' : (Jc c m (ι_c c σ (eBasis i)) : B0579.Plane → ℝ) x =
            (B0579.cell c).indicator (frozenDirectMode q c (1 + σ) i) x := hjc
        have hpl' : (ι_pl σ (eBasis i) : B0579.Plane → ℝ) x =
            planarFrozenDirectMode q (1 + σ) i x := hpl
        rw [hjc', hpl']
      rw [Lp.norm_def, eLpNorm_congr_ae hdiff_ae]
      have hbd := (hMode c (1 + σ) hc1 (by linarith [hσ.1]) (by dsimp [A]; linarith [hσ.2]) i).2.2
      exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbd).trans
        (ENNReal.toReal_ofReal htv_nn).le
    calc ‖(Jc c m).comp (ι_c c σ) - ι_pl σ‖
        ≤ tailVal + tailVal :=
          hop_le_basis _ htv_nn htv_nn (hbasis_bd 0) (hbasis_bd 1)
      _ = 2 * K_tail * Real.exp (-(c ^ 2 / (128 * A))) := by dsimp [tailVal]; ring
  -- Uniform norm bound `M_π` on `π_pl` over `Icc 0 Sig`
  have hπ_bdd : IsCompact (π_pl '' Icc 0 Sig) := isCompact_Icc.image_of_continuousOn hπ_cont
  obtain ⟨R_π, hR_π⟩ := hπ_bdd.isBounded.subset_closedBall (0 : Xm m →L[ℝ] E2)
  set M_π : ℝ := max 1 R_π
  have hM_π_ge_one : 1 ≤ M_π := le_max_left 1 R_π
  have hM_π_pos : 0 < M_π := lt_of_lt_of_le one_pos hM_π_ge_one
  have hπ_norm : ∀ {σ : ℝ}, σ ∈ Icc 0 Sig → ‖π_pl σ‖ ≤ M_π := by
    intro σ hσ
    have hmem := hR_π ⟨σ, hσ, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hmem
    exact hmem.trans (le_max_right 1 R_π)
  -- Threshold selector for Gaussian decay `C * exp(-c² / (128 * A)) ≤ η`
  have exists_c_exp_sq_le : ∀ {C η : ℝ}, 0 ≤ C → 0 < η →
      ∃ c_thr : ℝ, 1 ≤ c_thr ∧ ∀ c : ℝ, c_thr ≤ c →
        C * Real.exp (-(c ^ 2 / (128 * A))) ≤ η := by
    intro C η hC hη
    set C' : ℝ := C + 1
    have hC'_pos : 0 < C' := by dsimp [C']; linarith
    have hδ : 0 < 1 / (128 * A) := by positivity
    have hratio : 0 < C' / (4 * η) := by positivity
    obtain ⟨c_thr, hc_thr1, hc_thr⟩ := PartIIbF23Sub.exists_L_exp_neg_le_quarter hδ hratio
    refine ⟨c_thr, hc_thr1, fun c hc => ?_⟩
    have hc1 : 1 ≤ c := hc_thr1.trans hc
    have hexp_le : Real.exp (-(c ^ 2 / (128 * A))) ≤ Real.exp (-(1 / (128 * A)) * c) := by
      apply Real.exp_le_exp.mpr
      have hsq : c ≤ c ^ 2 := by nlinarith
      have hdiv : c / (128 * A) ≤ c ^ 2 / (128 * A) :=
        div_le_div_of_nonneg_right hsq (by positivity)
      linarith [show -(1 / (128 * A)) * c = -(c / (128 * A)) by ring]
    have hq1 := hc_thr c hc
    have hq2 : C' * Real.exp (-(1 / (128 * A)) * c) ≤ η := by
      have hm_le := mul_le_mul_of_nonneg_left hq1 (by positivity : 0 ≤ 4 * η)
      have h1 : 4 * η * (C' / (4 * η) * Real.exp (-(1 / (128 * A)) * c)) =
          C' * Real.exp (-(1 / (128 * A)) * c) := by
        field_simp [hη.ne']
      have h2 : 4 * η * (1 / 4 : ℝ) = η := by ring
      linarith
    calc C * Real.exp (-(c ^ 2 / (128 * A)))
        ≤ C' * Real.exp (-(c ^ 2 / (128 * A))) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          dsimp [C']; linarith
      _ ≤ C' * Real.exp (-(1 / (128 * A)) * c) :=
          mul_le_mul_of_nonneg_left hexp_le hC'_pos.le
      _ ≤ η := hq2
  -- Choose `c₀ ≥ 1` so `‖G_op c σ - id‖ ≤ 1 / 2` for all `c ≥ c₀` and `σ ∈ Icc 0 Sig`
  obtain ⟨c₀, hc₀_1, hc₀_bd⟩ := exists_c_exp_sq_le
    (C := M_π * (2 * K_tail)) (η := 1 / 2) (by positivity) (by norm_num)
  let π_raw : ∀ c : ℝ, ℝ → (Xmc c m →L[ℝ] E2) := fun c σ => (π_pl σ).comp (Jc c m)
  let G_op : ℝ → ℝ → (E2 →L[ℝ] E2) := fun c σ => (π_raw c σ).comp (ι_c c σ)
  have hG_sub_eq : ∀ (c : ℝ) {σ : ℝ}, σ ∈ Icc 0 Sig →
      G_op c σ - ContinuousLinearMap.id ℝ E2 =
        (π_pl σ).comp ((Jc c m).comp (ι_c c σ) - ι_pl σ) := by
    intro c σ hσ
    dsimp only [G_op, π_raw]
    rw [ContinuousLinearMap.comp_sub, ← h_id_pl σ hσ, ContinuousLinearMap.comp_assoc]
  have hG_norm : ∀ {c σ : ℝ}, 1 ≤ c → σ ∈ Icc 0 Sig →
      ‖G_op c σ - ContinuousLinearMap.id ℝ E2‖ ≤
        (M_π * (2 * K_tail)) * Real.exp (-(c ^ 2 / (128 * A))) := by
    intro c σ hc1 hσ
    rw [hG_sub_eq c hσ]
    calc ‖(π_pl σ).comp ((Jc c m).comp (ι_c c σ) - ι_pl σ)‖
        ≤ ‖π_pl σ‖ * ‖(Jc c m).comp (ι_c c σ) - ι_pl σ‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ M_π * (2 * K_tail * Real.exp (-(c ^ 2 / (128 * A)))) :=
          mul_le_mul (hπ_norm hσ) (hι_tail hc1 hσ) (norm_nonneg _) hM_π_pos.le
      _ = (M_π * (2 * K_tail)) * Real.exp (-(c ^ 2 / (128 * A))) := by ring
  have hG_half : ∀ {c σ : ℝ}, c₀ ≤ c → σ ∈ Icc 0 Sig →
      ‖G_op c σ - ContinuousLinearMap.id ℝ E2‖ ≤ 1 / 2 := by
    intro c σ hc hσ
    exact (hG_norm (hc₀_1.trans hc) hσ).trans (hc₀_bd c hc)
  let U_of : ∀ (c σ : ℝ), (c₀ ≤ c ∧ σ ∈ Icc 0 Sig) → (E2 →L[ℝ] E2) :=
    fun c σ h => Classical.choose (invertible_e2_of_sub_id_le (hG_half h.1 h.2))
  have hU_spec : ∀ (c σ : ℝ) (h : c₀ ≤ c ∧ σ ∈ Icc 0 Sig),
      (U_of c σ h).comp (G_op c σ) = ContinuousLinearMap.id ℝ E2 ∧
        ‖U_of c σ h‖ ≤ 2 ∧
        ‖U_of c σ h - ContinuousLinearMap.id ℝ E2‖ ≤
          2 * ‖G_op c σ - ContinuousLinearMap.id ℝ E2‖ :=
    fun c σ h => Classical.choose_spec (invertible_e2_of_sub_id_le (hG_half h.1 h.2))
  let π_c : ∀ c : ℝ, ℝ → (Xmc c m →L[ℝ] E2) := fun c σ =>
    if h : c₀ ≤ c ∧ σ ∈ Icc 0 Sig then (U_of c σ h).comp (π_raw c σ) else 0
  set M_c : ℝ := max 1 (max (2 * K_norm) (2 * M_π))
  refine ⟨c₀, M_c, ι_c, π_c, hc₀_1, le_max_left _ _, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) Pointwise a.e. formula for `ι_c c σ α`
    intro c hc σ hσ α
    exact hι_ae (hc₀_1.trans hc) hσ α
  · -- (2) Zero circulation on `B0579.cell c`
    intro c hc σ hσ α
    exact hι_circ (hc₀_1.trans hc) hσ α
  · -- (3) Normalization `(π_c c σ).comp (ι_c c σ) = id`
    intro c hc σ hσ
    have h : c₀ ≤ c ∧ σ ∈ Icc 0 Sig := ⟨hc, hσ⟩
    dsimp only [π_c]
    simp only [h, and_self, ↓reduceDIte]
    rw [ContinuousLinearMap.comp_assoc]
    exact (hU_spec c σ h).1
  · -- (4) Uniform operator norm bounds `‖ι_c c σ‖ ≤ M_c` and `‖π_c c σ‖ ≤ M_c`
    intro c hc σ hσ
    have h : c₀ ≤ c ∧ σ ∈ Icc 0 Sig := ⟨hc, hσ⟩
    constructor
    · exact (hι_norm (hc₀_1.trans hc) hσ).trans
        ((le_max_left (2 * K_norm) (2 * M_π)).trans (le_max_right 1 _))
    · dsimp only [π_c, π_raw]
      simp only [h, and_self, ↓reduceDIte]
      have hπ_raw_le : ‖(π_pl σ).comp (Jc c m)‖ ≤ M_π := by
        calc ‖(π_pl σ).comp (Jc c m)‖
            ≤ ‖π_pl σ‖ * ‖Jc c m‖ := ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ M_π * 1 := mul_le_mul (hπ_norm hσ) (norm_Jc_le_one c m) (norm_nonneg _) hM_π_pos.le
          _ = M_π := mul_one _
      have hπc_le : ‖(U_of c σ h).comp ((π_pl σ).comp (Jc c m))‖ ≤ 2 * M_π := by
        calc ‖(U_of c σ h).comp ((π_pl σ).comp (Jc c m))‖
            ≤ ‖U_of c σ h‖ * ‖(π_pl σ).comp (Jc c m)‖ := ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ 2 * M_π :=
              mul_le_mul (hU_spec c σ h).2.1 hπ_raw_le (norm_nonneg _) zero_le_two
      exact hπc_le.trans ((le_max_right (2 * K_norm) (2 * M_π)).trans (le_max_right 1 _))
  · -- (5) Uniform convergence of `(Jc c m).comp (ι_c c σ)` and `(π_c c σ).comp (Rc c m)`
    intro ε hε
    obtain ⟨c_dual, _hc_dual1, hc_dual⟩ :=
      exists_c_norm_comp_Jc_Rc_sub_id_le π_pl hπ_cont (half_pos hε)
    obtain ⟨c_exp0, _hc_exp0_1, hc_exp0⟩ :=
      exists_c_exp_sq_le (C := 2 * K_tail) (η := ε) (by positivity) hε
    obtain ⟨c_exp1, _hc_exp1_1, hc_exp1⟩ :=
      exists_c_exp_sq_le (C := 4 * M_π ^ 2 * K_tail) (η := ε / 2) (by positivity) (half_pos hε)
    set c₁ : ℝ := max c₀ (max c_dual (max c_exp0 c_exp1))
    refine ⟨c₁, le_max_left _ _, fun c hc σ hσ => ?_⟩
    have hc_ge_c₀ : c₀ ≤ c := (le_max_left _ _).trans hc
    have hc1 : 1 ≤ c := hc₀_1.trans hc_ge_c₀
    have hc_ge_dual : c_dual ≤ c :=
      ((le_max_left _ _).trans (le_max_right c₀ _)).trans hc
    have hc_ge_exp0 : c_exp0 ≤ c :=
      ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right c₀ _))).trans hc
    have hc_ge_exp1 : c_exp1 ≤ c :=
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right c₀ _))).trans hc
    constructor
    · exact (hι_tail hc1 hσ).trans (hc_exp0 c hc_ge_exp0)
    · have h : c₀ ≤ c ∧ σ ∈ Icc 0 Sig := ⟨hc_ge_c₀, hσ⟩
      dsimp only [π_c, π_raw]
      simp only [h, and_self, ↓reduceDIte]
      set Pc : Xm m →L[ℝ] Xm m := (Jc c m).comp (Rc c m)
      have hdecomp :
          ((U_of c σ h).comp ((π_pl σ).comp (Jc c m))).comp (Rc c m) - π_pl σ =
            (U_of c σ h - ContinuousLinearMap.id ℝ E2).comp ((π_pl σ).comp Pc) +
              (π_pl σ).comp (Pc - ContinuousLinearMap.id ℝ (Xm m)) := by
        ext f
        simp only [Pc, ContinuousLinearMap.comp_apply, FunLike.coe_sub, Pi.sub_apply,
          FunLike.coe_add, Pi.add_apply, ContinuousLinearMap.id_apply, map_sub]
        abel_nf
      rw [hdecomp]
      have hterm1 :
          ‖(U_of c σ h - ContinuousLinearMap.id ℝ E2).comp ((π_pl σ).comp Pc)‖ ≤ ε / 2 := by
        have hπPc : ‖(π_pl σ).comp Pc‖ ≤ M_π := by
          calc ‖(π_pl σ).comp Pc‖
              ≤ ‖π_pl σ‖ * ‖Pc‖ := ContinuousLinearMap.opNorm_comp_le _ _
            _ ≤ M_π * 1 :=
                mul_le_mul (hπ_norm hσ) (norm_Jc_comp_Rc_le_one c m) (norm_nonneg _) hM_π_pos.le
            _ = M_π := mul_one _
        have hU_diff : ‖U_of c σ h - ContinuousLinearMap.id ℝ E2‖ ≤
            2 * ((M_π * (2 * K_tail)) * Real.exp (-(c ^ 2 / (128 * A)))) :=
          (hU_spec c σ h).2.2.trans
            (mul_le_mul_of_nonneg_left (hG_norm hc1 hσ) zero_le_two)
        calc ‖(U_of c σ h - ContinuousLinearMap.id ℝ E2).comp ((π_pl σ).comp Pc)‖
            ≤ ‖U_of c σ h - ContinuousLinearMap.id ℝ E2‖ * ‖(π_pl σ).comp Pc‖ :=
              ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ (2 * ((M_π * (2 * K_tail)) * Real.exp (-(c ^ 2 / (128 * A))))) * M_π :=
              mul_le_mul hU_diff hπPc (norm_nonneg _) (by positivity)
          _ = (4 * M_π ^ 2 * K_tail) * Real.exp (-(c ^ 2 / (128 * A))) := by ring
          _ ≤ ε / 2 := hc_exp1 c hc_ge_exp1
      have hterm2 :
          ‖(π_pl σ).comp (Pc - ContinuousLinearMap.id ℝ (Xm m))‖ ≤ ε / 2 :=
        hc_dual c hc_ge_dual σ hσ
      calc ‖(U_of c σ h - ContinuousLinearMap.id ℝ E2).comp ((π_pl σ).comp Pc) +
              (π_pl σ).comp (Pc - ContinuousLinearMap.id ℝ (Xm m))‖
          ≤ ‖(U_of c σ h - ContinuousLinearMap.id ℝ E2).comp ((π_pl σ).comp Pc)‖ +
              ‖(π_pl σ).comp (Pc - ContinuousLinearMap.id ℝ (Xm m))‖ := norm_add_le _ _
        _ ≤ ε / 2 + ε / 2 := add_le_add hterm1 hterm2
        _ = ε := add_halves ε

end
