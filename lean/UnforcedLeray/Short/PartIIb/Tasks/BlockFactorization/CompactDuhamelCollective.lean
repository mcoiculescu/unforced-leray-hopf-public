import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2_4
import UnforcedLeray.Short.PartIIb.Org.RealCompactDuhamel
import UnforcedLeray.Short.PartIIb.Tasks.BlockFactorization.FrozenTransportCont
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.TotallyBounded

/-!
# `PartII-b:F2/4/2` (`CompactDuhamelCollective.lean`): Uniform bound & collective compactness of the frozen planar Euler Duhamel family

Source of record: `the November 2 reference manuscript`, lines 841–852, 2147–2150.

Proves `planarDuhamelCollectiveCompact_proof : UnforcedLeray.Short.IIb.PlanarDuhamelCollectiveCompact`:
1. Uniform operator-norm bound `‖E_pl σ τ‖ ≤ M_op` on `[0, Sig] × [0, Lmax]` via Banach–Steinhaus
   (`RCDuhamel.exists_norm_le_of_continuousOn`) and Gronwall (`RCDuhamel.isDuhamelEvolution_of_semigroup`
   + `RCDuhamel.IsDuhamelEvolution.norm_le`).
2. Collective total boundedness of `⋃_{σ ∈ [0, Sig]} ⋃_{τ ∈ [0, Lmax]} (E_pl σ τ - T_pl σ τ)(B_R)`
   via `frozenTransportJointCont_proof`, `TotallyBounded.convexHull`, and `Convex.set_average_mem_closure`.
-/

set_option autoImplicit false

open Set MeasureTheory Filter Topology Real Metric
open scoped ENNReal

open UnforcedLeray.Short.IIb in
theorem planarDuhamelCollectiveCompact_proof :
    UnforcedLeray.Short.IIb.PlanarDuhamelCollectiveCompact := by
  intro m hm Sig Lmax hSig hLmax AplOp hAcont _hAop hAtb T_pl E_pl hT hEcont hEmild
  have hbd_each : ∀ p : Icc (0 : ℝ) Sig, ∃ C, ∀ τ, 0 ≤ τ → τ ≤ Lmax → ‖E_pl p.1 τ‖ ≤ C := by
    intro p
    obtain ⟨C, hC⟩ :=
      RCDuhamel.exists_norm_le_of_continuousOn (𝕜 := ℝ) (H := Xm m) (E := E_pl p.1)
        (c := 0) (d := Lmax) (fun f => (hEcont p.1 p.2 f).mono Icc_subset_Ici_self)
    exact ⟨C, fun τ h0 hL => hC τ ⟨h0, hL⟩⟩
  have hEvol : RCDuhamel.IsDuhamelEvolution (𝕜 := ℝ) Lmax
      (fun (p : Icc (0 : ℝ) Sig) t s => T_pl p.1 (t - s))
      (fun p _ => AplOp p.1)
      (fun p t s => E_pl p.1 (t - s)) :=
    RCDuhamel.isDuhamelEvolution_of_semigroup (B := Lmax)
      (T := fun (p : Icc (0 : ℝ) Sig) τ => T_pl p.1 τ)
      (E := fun p τ => E_pl p.1 τ)
      (A := fun p => AplOp p.1)
      (fun p τ h0 _hL f => hEmild p.1 p.2 τ h0 f) hbd_each
  have hT_norm : ∀ (p : Icc (0 : ℝ) Sig) (t s : ℝ), s ≤ t → t ≤ s + Lmax →
      ‖T_pl p.1 (t - s)‖ ≤ 1 := by
    intro p t s _ _
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
    rw [one_mul, hT.isometry p.1 p.2]
  obtain ⟨K_A, hK_A⟩ := isCompact_Icc.exists_bound_of_continuousOn hAcont
  obtain ⟨M_op, hM_op_def⟩ : ∃ M_op : ℝ,
      M_op = max 1 (2 * 1 * Real.exp ((2 * (1 * K_A) + 1) * Lmax)) := ⟨_, rfl⟩
  have hM_op_ge1 : 1 ≤ M_op := hM_op_def ▸ le_max_left _ _
  have hE_bd : ∀ σ ∈ Icc 0 Sig, ∀ τ ∈ Icc 0 Lmax, ‖E_pl σ τ‖ ≤ M_op := by
    intro σ hσ τ hτ
    have h1 := hEvol.norm_le hT_norm (fun p _ => hK_A p.1 p.2)
      ⟨σ, hσ⟩ τ 0 hτ.1 (by linarith [hτ.2])
    simp only [sub_zero] at h1
    rw [hM_op_def]
    exact h1.trans (le_max_right _ _)
  refine ⟨⟨M_op, hM_op_ge1, hE_bd⟩, fun R => ?_⟩
  rcases lt_or_ge R 0 with hR | hR
  · refine totallyBounded_empty.subset fun y hy => ?_
    rcases mem_iUnion₂.1 hy with ⟨σ, _, hy⟩
    rcases mem_iUnion₂.1 hy with ⟨τ, _, f, hf, _⟩
    rw [Metric.closedBall_eq_empty.2 hR] at hf
    exact hf
  · set U₀ : Set (Xm m) :=
      ⋃ σ ∈ Icc 0 Sig, AplOp σ '' Metric.closedBall (0 : Xm m) (M_op * R)
    set K₀ : Set (Xm m) := closure U₀
    have hK₀_comp : IsCompact K₀ :=
      isCompact_iff_totallyBounded_isComplete.2
        ⟨(hAtb (M_op * R)).closure, isClosed_closure.isComplete⟩
    have h0_K₀ : (0 : Xm m) ∈ K₀ := by
      refine subset_closure (mem_iUnion₂.2 ⟨0, ⟨le_rfl, hSig.le⟩, 0, ?_, map_zero _⟩)
      rw [Metric.mem_closedBall, dist_self]
      exact mul_nonneg (by linarith) hR
    let Φ : ℝ × ℝ × Xm m → Xm m := fun q => T_pl q.1 q.2.1 q.2.2
    have hΦ_cont : ContinuousOn Φ (Icc 0 Sig ×ˢ univ) :=
      frozenTransportJointCont_proof m hm Sig hSig T_pl hT
    let Q : Set (ℝ × ℝ × Xm m) := Icc 0 Sig ×ˢ (Icc 0 Lmax ×ˢ K₀)
    have hQ_comp : IsCompact Q := isCompact_Icc.prod (isCompact_Icc.prod hK₀_comp)
    have hQ_sub : Q ⊆ Icc 0 Sig ×ˢ univ := fun _ hq => ⟨hq.1, trivial⟩
    set S : Set (Xm m) := Φ '' Q
    have hS_comp : IsCompact S := hQ_comp.image_of_continuousOn (hΦ_cont.mono hQ_sub)
    set K_conv : Set (Xm m) := closure (convexHull ℝ S)
    have hKconv_comp : IsCompact K_conv :=
      isCompact_iff_totallyBounded_isComplete.2
        ⟨hS_comp.totallyBounded.convexHull.closure, isClosed_closure.isComplete⟩
    have h0_S : Φ (0, 0, 0) ∈ S :=
      ⟨(0, 0, 0), ⟨⟨le_rfl, hSig.le⟩, ⟨le_rfl, hLmax.le⟩, h0_K₀⟩, rfl⟩
    have h0_Kconv : Φ (0, 0, 0) ∈ K_conv :=
      subset_closure (subset_convexHull ℝ S h0_S)
    let W : Set (Xm m) := (fun p : ℝ × Xm m => p.1 • p.2) '' (Icc 0 Lmax ×ˢ K_conv)
    have hW_comp : IsCompact W := (isCompact_Icc.prod hKconv_comp).image continuous_smul
    refine hW_comp.totallyBounded.subset fun y hy => ?_
    rcases mem_iUnion₂.1 hy with ⟨σ, hσ, hy⟩
    rcases mem_iUnion₂.1 hy with ⟨τ, hτ, f, hf, rfl⟩
    have hf_norm : ‖f‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hf
    obtain ⟨h_int, h_duh⟩ := hEmild σ hσ τ hτ.1 f
    have hdiff_eq : (E_pl σ τ - T_pl σ τ) f =
        ∫ r in (0 : ℝ)..τ, T_pl σ (τ - r) (AplOp σ (E_pl σ r f)) := by
      rw [sub_apply, h_duh, add_sub_cancel_left]
    rw [hdiff_eq]
    rcases eq_or_lt_of_le hτ.1 with rfl | hτ_pos
    · rw [intervalIntegral.integral_same]
      exact ⟨(0, Φ (0, 0, 0)), ⟨⟨le_rfl, hLmax.le⟩, h0_Kconv⟩, zero_smul ℝ _⟩
    · set g : ℝ → Xm m := fun r => T_pl σ (τ - r) (AplOp σ (E_pl σ r f))
      have hg_mem : ∀ r ∈ Ioc 0 τ, g r ∈ convexHull ℝ S := by
        intro r hr
        have hr_mem : r ∈ Icc 0 Lmax := ⟨hr.1.le, hr.2.trans hτ.2⟩
        have hEf_norm : ‖E_pl σ r f‖ ≤ M_op * R :=
          ((E_pl σ r).le_opNorm f).trans
            (mul_le_mul (hE_bd σ hσ r hr_mem) hf_norm (norm_nonneg _) (by linarith))
        have hAE_U₀ : AplOp σ (E_pl σ r f) ∈ U₀ := by
          refine mem_iUnion₂.2 ⟨σ, hσ, E_pl σ r f, ?_, rfl⟩
          rwa [Metric.mem_closedBall, dist_zero_right]
        have htr_mem : τ - r ∈ Icc 0 Lmax := ⟨sub_nonneg.2 hr.2, by linarith [hr.1, hτ.2]⟩
        have hg_S : g r ∈ S :=
          ⟨(σ, τ - r, AplOp σ (E_pl σ r f)), ⟨hσ, htr_mem, subset_closure hAE_U₀⟩, rfl⟩
        exact subset_convexHull ℝ S hg_S
      have hae_mem : ∀ᵐ r ∂volume.restrict (Ioc 0 τ), g r ∈ convexHull ℝ S :=
        (ae_restrict_mem measurableSet_Ioc).mono hg_mem
      have hint_on : IntegrableOn g (Ioc 0 τ) volume :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hτ.1).1 h_int
      have hvol_eq : volume (Ioc 0 τ) = ENNReal.ofReal τ := by rw [Real.volume_Ioc, sub_zero]
      have hvol_ne0 : volume (Ioc 0 τ) ≠ 0 := by
        rw [hvol_eq]
        exact (ENNReal.ofReal_pos.2 hτ_pos).ne'
      have hvol_netop : volume (Ioc 0 τ) ≠ ∞ := by
        rw [hvol_eq]
        exact ENNReal.ofReal_ne_top
      have havg_mem : (⨍ r in Ioc 0 τ, g r) ∈ K_conv :=
        (convex_convexHull ℝ S).set_average_mem_closure hvol_ne0 hvol_netop hae_mem hint_on
      refine ⟨(τ, ⨍ r in Ioc 0 τ, g r), ⟨hτ, havg_mem⟩, ?_⟩
      dsimp only
      rw [MeasureTheory.setAverage_eq, Measure.real_def, hvol_eq,
        ENNReal.toReal_ofReal hτ_pos.le, smul_smul, mul_inv_cancel₀ hτ_pos.ne',
        one_smul, ← intervalIntegral.integral_of_le hτ.1]
