import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org_2_2
import UnforcedLeray.Lib.HeatCylinder.HeatVecGaussianShiftPairing
import UnforcedLeray.Lib.CylinderB.Liouville
import UnforcedLeray.Lib.SobolevC.CylDensity
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.SpatialRepFromPersistent.AePeriodicEq
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Uniqueness of Weak `C([0, 2]; H¹_σ(C_c))` Oseen Solutions (`WeakMildUnique`)

Support submodule 1 for task `PartII-b:F8/1/org/2/2` (`RealCylOseenSpatialBootstrap`).
Proves that any weak `C([0, 2]; H¹_σ(C_c))` solution `(W, Wq, Wη)` of the real periodic-cylinder
Oseen equation (`F8Ex.IsRealWeakH1OseenSol c ν V W Wq Wη u uq uη`) coincides a.e. on every slice
`s ∈ [0, 2]` with the mild Volterra evolution `U s := F8WeakEx.E_oseen hc hν hV s 0 u₀`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff InnerProductSpace Convolution

namespace UnforcedLeray.Short.IIb.F8SpBoot

open UnforcedLeray
open UnforcedLeray.Short.IIb
open UnforcedLeray.Cyl (L2v cellμ divFree P0 Vec2)
open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.HeatCylinder

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-! ## 1. `L²(cell)` norm bridges and lifting `IsRealWeakH1OseenSol` to `C([0, 2]; H1Sol c)` -/

private lemma eLpNorm_cellMeas_eq_ofReal_norm {c : ℝ} {f : Plane → F8Ex.RMerid} {x : L2v c}
    (h : f =ᵐ[F8Ex.cellMeas c] (x : Plane → F8Ex.RMerid)) :
    F8Ex.cellL2R c f = ENNReal.ofReal ‖x‖ := by
  have hx : f =ᵐ[cellμ c] (x : Plane → Vec2) := by
    rw [show ae (cellμ c) = ae (F8Ex.cellMeas c) from
      congr_arg ae (F8WeakEx.cellMeas_eq_cellμ c).symm]
    exact h
  unfold F8Ex.cellL2R
  rw [F8WeakEx.cellMeas_eq_cellμ, eLpNorm_congr_ae hx, ← Lp.enorm_def, ofReal_norm]

private lemma norm_H1Sol_le_sum {c : ℝ} (p : F8WeakEx.H1Sol c) :
    ‖p‖ ≤ ‖F8WeakEx.val0CLM c p‖ + ‖F8WeakEx.dqCLM c p‖ + ‖F8WeakEx.detaCLM c p‖ := by
  change max ‖p.1.1‖ (max ‖p.1.2.1‖ ‖p.1.2.2‖) ≤
    ‖p.1.1‖ + ‖p.1.2.1‖ + ‖p.1.2.2‖
  have h0 : 0 ≤ ‖p.1.1‖ := norm_nonneg _
  have h1 : 0 ≤ ‖p.1.2.1‖ := norm_nonneg _
  have h2 : 0 ≤ ‖p.1.2.2‖ := norm_nonneg _
  refine max_le (by linarith) (max_le (by linarith) (by linarith))

private def liftWeakSol {c ν : ℝ} {V : ℝ → Plane → F8Ex.RMerid}
    {W Wq Wη : ℝ → Plane → F8Ex.RMerid} {u uq uη : Plane → F8Ex.RMerid}
    (hwk : F8Ex.IsRealWeakH1OseenSol c ν V W Wq Wη u uq uη) (s : ℝ) : F8WeakEx.H1Sol c :=
  open Classical in
  if hs : s ∈ Icc (0 : ℝ) 2 then F8WeakEx.H1Sol.ofRealDatum (hwk.slice_h1 s hs) else 0

private lemma liftWeakSol_ae {c ν : ℝ} {V : ℝ → Plane → F8Ex.RMerid}
    {W Wq Wη : ℝ → Plane → F8Ex.RMerid} {u uq uη : Plane → F8Ex.RMerid}
    (hwk : F8Ex.IsRealWeakH1OseenSol c ν V W Wq Wη u uq uη)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 2) :
    (F8WeakEx.val0CLM c (liftWeakSol hwk s) : Plane → F8Ex.RMerid) =ᵐ[F8Ex.cellMeas c] W s ∧
    (F8WeakEx.dqCLM c (liftWeakSol hwk s) : Plane → F8Ex.RMerid) =ᵐ[F8Ex.cellMeas c] Wq s ∧
    (F8WeakEx.detaCLM c (liftWeakSol hwk s) : Plane → F8Ex.RMerid) =ᵐ[F8Ex.cellMeas c] Wη s := by
  have heq : liftWeakSol hwk s = F8WeakEx.H1Sol.ofRealDatum (hwk.slice_h1 s hs) := by
    unfold liftWeakSol; simp [hs]
  rw [heq]
  exact F8WeakEx.H1Sol.ofRealDatum_ae (hwk.slice_h1 s hs)

private lemma liftWeakSol_zero {c ν : ℝ} (hc : 0 < c) {V : ℝ → Plane → F8Ex.RMerid}
    {W Wq Wη : ℝ → Plane → F8Ex.RMerid} {u uq uη : Plane → F8Ex.RMerid}
    (hdat : F8Ex.IsRealCylH1Datum c u uq uη)
    (hwk : F8Ex.IsRealWeakH1OseenSol c ν V W Wq Wη u uq uη) :
    liftWeakSol hwk 0 = F8WeakEx.H1Sol.ofRealDatum hdat := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 2 := ⟨le_rfl, by norm_num⟩
  apply F8WeakEx.H1Sol.ext_val0 hc
  apply Lp.ext
  have ha1 := (liftWeakSol_ae hwk h0).1
  have ha2 := (F8WeakEx.H1Sol.ofRealDatum_ae hdat).1
  rw [hwk.init_eq.1] at ha1
  have h12 : (F8WeakEx.val0CLM c (liftWeakSol hwk 0) : Plane → F8Ex.RMerid) =ᵐ[cellμ c]
      (F8WeakEx.val0CLM c (F8WeakEx.H1Sol.ofRealDatum hdat) : Plane → F8Ex.RMerid) := by
    rw [show ae (cellμ c) = ae (F8Ex.cellMeas c) from
      congr_arg ae (F8WeakEx.cellMeas_eq_cellμ c).symm]
    exact ha1.trans ha2.symm
  exact h12

private lemma continuousOn_liftWeakSol {c ν : ℝ} {V : ℝ → Plane → F8Ex.RMerid}
    {W Wq Wη : ℝ → Plane → F8Ex.RMerid} {u uq uη : Plane → F8Ex.RMerid}
    (hwk : F8Ex.IsRealWeakH1OseenSol c ν V W Wq Wη u uq uη) :
    ContinuousOn (liftWeakSol hwk) (Icc (0 : ℝ) 2) := by
  intro s hs
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have hlim_enn := hwk.cont_h1 s hs
  obtain ⟨hs0, hsq, hsη⟩ := liftWeakSol_ae hwk hs
  let S : ℝ → ℝ := fun t =>
    ‖F8WeakEx.val0CLM c (liftWeakSol hwk t - liftWeakSol hwk s)‖ +
    ‖F8WeakEx.dqCLM c (liftWeakSol hwk t - liftWeakSol hwk s)‖ +
    ‖F8WeakEx.detaCLM c (liftWeakSol hwk t - liftWeakSol hwk s)‖
  have hlim_ofReal : Tendsto (fun t => ENNReal.ofReal (S t)) (𝓝[Icc (0 : ℝ) 2] s) (𝓝 0) := by
    refine hlim_enn.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    obtain ⟨ht0, htq, htη⟩ := liftWeakSol_ae hwk ht
    have sub_ae : ∀ (f₁ f₂ : Plane → F8Ex.RMerid) (x₁ x₂ : L2v c),
        (x₁ : Plane → F8Ex.RMerid) =ᵐ[F8Ex.cellMeas c] f₁ →
        (x₂ : Plane → F8Ex.RMerid) =ᵐ[F8Ex.cellMeas c] f₂ →
        (fun y => f₁ y - f₂ y) =ᵐ[F8Ex.cellMeas c] ((x₁ - x₂ : L2v c) : Plane → F8Ex.RMerid) := by
      intro f₁ f₂ x₁ x₂ h1 h2
      have hsub : ((x₁ - x₂ : L2v c) : Plane → F8Ex.RMerid) =ᵐ[F8Ex.cellMeas c]
          fun y => (x₁ : Plane → F8Ex.RMerid) y - (x₂ : Plane → F8Ex.RMerid) y := by
        rw [F8WeakEx.cellMeas_eq_cellμ]
        exact Lp.coeFn_sub x₁ x₂
      filter_upwards [h1, h2, hsub] with y a1 a2 asub
      rw [← a1, ← a2, asub]
    dsimp only [F8Ex.cylH1R, S]
    rw [map_sub, map_sub, map_sub,
      eLpNorm_cellMeas_eq_ofReal_norm (sub_ae _ _ _ _ ht0 hs0),
      eLpNorm_cellMeas_eq_ofReal_norm (sub_ae _ _ _ _ htq hsq),
      eLpNorm_cellMeas_eq_ofReal_norm (sub_ae _ _ _ _ htη hsη),
      ENNReal.ofReal_add (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _),
      ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
  have hlim_S : Tendsto S (𝓝[Icc (0 : ℝ) 2] s) (𝓝 0) := by
    have hto := (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hlim_ofReal
    simpa only [Function.comp_def, ENNReal.toReal_zero] using hto.congr fun t =>
      ENNReal.toReal_ofReal (add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _))
  exact squeeze_zero (fun _ => norm_nonneg _) (fun t => norm_H1Sol_le_sum _) hlim_S

private lemma continuousOn_bv_comp {c : ℝ} (hc : 0 < c) {V : ℝ → Plane → F8Ex.RMerid}
    (hV : F8Ex.IsSmoothBUCDrift c V) {P : ℝ → F8WeakEx.H1Sol c}
    (hP : ContinuousOn P (Icc (0 : ℝ) 2)) :
    ContinuousOn (fun r => F8WeakEx.bvCLM hc hV r (P r)) (Icc (0 : ℝ) 2) := by
  intro s hs
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  have h1 : ContinuousWithinAt (fun r => F8WeakEx.bvCLM hc hV r (P s)) (Icc (0 : ℝ) 2) s :=
    (F8WeakEx.continuous_bvCLM_apply hc hV (P s)).continuousWithinAt
  obtain ⟨δ₁, hδ₁, hb₁⟩ := Metric.continuousWithinAt_iff.mp h1 (ε / 2) hε2
  let K : ℝ := 6 * F8WeakEx.driftBound hV + 1
  have hK : 0 < K := by
    have := F8WeakEx.driftBound_nonneg hV
    dsimp [K]; positivity
  obtain ⟨δ₂, hδ₂, hb₂⟩ := Metric.continuousWithinAt_iff.mp (hP s hs) ((ε / 2) / K) (div_pos hε2 hK)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun r hr hdist => ?_⟩
  have hd1 : dist r s < δ₁ := lt_of_lt_of_le hdist (min_le_left _ _)
  have hd2 : dist r s < δ₂ := lt_of_lt_of_le hdist (min_le_right _ _)
  rw [dist_eq_norm]
  have hsplit : F8WeakEx.bvCLM hc hV r (P r) - F8WeakEx.bvCLM hc hV s (P s) =
      F8WeakEx.bvCLM hc hV r (P r - P s) +
        (F8WeakEx.bvCLM hc hV r (P s) - F8WeakEx.bvCLM hc hV s (P s)) := by
    rw [map_sub]; abel
  rw [hsplit]
  have hle1 : ‖F8WeakEx.bvCLM hc hV r (P r - P s)‖ < ε / 2 := by
    calc ‖F8WeakEx.bvCLM hc hV r (P r - P s)‖
        ≤ ‖F8WeakEx.bvCLM hc hV r‖ * ‖P r - P s‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (6 * F8WeakEx.driftBound hV) * ‖P r - P s‖ :=
          mul_le_mul_of_nonneg_right (F8WeakEx.norm_bvCLM_le hc hV r) (norm_nonneg _)
      _ ≤ K * dist (P r) (P s) := by
          rw [dist_eq_norm]
          exact mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) (norm_nonneg _)
      _ < K * ((ε / 2) / K) := mul_lt_mul_of_pos_left (hb₂ hr hd2) hK
      _ = ε / 2 := mul_div_cancel₀ _ hK.ne'
  have hle2 : ‖F8WeakEx.bvCLM hc hV r (P s) - F8WeakEx.bvCLM hc hV s (P s)‖ < ε / 2 := by
    rw [← dist_eq_norm]
    exact hb₁ hr hd1
  calc ‖F8WeakEx.bvCLM hc hV r (P r - P s) +
          (F8WeakEx.bvCLM hc hV r (P s) - F8WeakEx.bvCLM hc hV s (P s))‖
      ≤ ‖F8WeakEx.bvCLM hc hV r (P r - P s)‖ +
          ‖F8WeakEx.bvCLM hc hV r (P s) - F8WeakEx.bvCLM hc hV s (P s)‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hle1 hle2
    _ = ε := add_halves ε

private lemma weak_eq_liftWeakSol {c ν : ℝ} (hc : 0 < c) {V : ℝ → Plane → F8Ex.RMerid}
    (hV : F8Ex.IsSmoothBUCDrift c V)
    {W Wq Wη : ℝ → Plane → F8Ex.RMerid} {u uq uη : Plane → F8Ex.RMerid}
    (hdat : F8Ex.IsRealCylH1Datum c u uq uη)
    (hwk : F8Ex.IsRealWeakH1OseenSol c ν V W Wq Wη u uq uη)
    {Φ : Plane → F8Ex.RMerid} (hΦ : F8Ex.IsRealSolCylTest c Φ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) :
    let hsm := F8WeakEx.isCylSmooth_of_solTest hΦ
    let φ₀ := F8WeakEx.cylSmoothToL2 hsm
    let φq := F8WeakEx.cylSmoothToL2 (hsm.dir (B0579.dir 0))
    let φη := F8WeakEx.cylSmoothToL2 (hsm.dir (B0579.dir 1))
    let U₁ := liftWeakSol hwk
    ⟪φ₀, F8WeakEx.val0CLM c (U₁ t) - F8WeakEx.val0CLM c (F8WeakEx.H1Sol.ofRealDatum hdat)⟫_ℝ +
      ∫ r in (0 : ℝ)..t,
        (ν * (⟪φq, F8WeakEx.dqCLM c (U₁ r)⟫_ℝ + ⟪φη, F8WeakEx.detaCLM c (U₁ r)⟫_ℝ) +
          ⟪φ₀, F8WeakEx.bvCLM hc hV r (U₁ r)⟫_ℝ) = 0 := by
  intro hsm φ₀ φq φη U₁
  obtain ⟨_, hwk_eq⟩ := hwk.weak_eq Φ hΦ t ht
  obtain ⟨hu0, _, _⟩ := F8WeakEx.H1Sol.ofRealDatum_ae hdat
  have hhead : ⟪φ₀, F8WeakEx.val0CLM c (U₁ t) -
      F8WeakEx.val0CLM c (F8WeakEx.H1Sol.ofRealDatum hdat)⟫_ℝ =
      ∫ y in B0579.cell c, inner ℝ (Φ y) (W t y - u y) := by
    rw [F8WeakEx.inner_cylSmoothToL2_right]
    obtain ⟨ht0, _, _⟩ := liftWeakSol_ae hwk ht
    have hsub : ((F8WeakEx.val0CLM c (U₁ t) -
        F8WeakEx.val0CLM c (F8WeakEx.H1Sol.ofRealDatum hdat) : L2v c) : Plane → F8Ex.RMerid) =ᵐ[
        F8Ex.cellMeas c] fun y =>
          (F8WeakEx.val0CLM c (U₁ t) : Plane → F8Ex.RMerid) y -
            (F8WeakEx.val0CLM c (F8WeakEx.H1Sol.ofRealDatum hdat) : Plane → F8Ex.RMerid) y := by
      rw [F8WeakEx.cellMeas_eq_cellμ]
      exact Lp.coeFn_sub _ _
    refine integral_congr_ae ?_
    filter_upwards [ht0, hu0, hsub] with y a1 a2 asub
    rw [asub, a1, a2]
  have hslice : ∀ r ∈ Icc (0 : ℝ) 2,
      ν * (⟪φq, F8WeakEx.dqCLM c (U₁ r)⟫_ℝ + ⟪φη, F8WeakEx.detaCLM c (U₁ r)⟫_ℝ) +
        ⟪φ₀, F8WeakEx.bvCLM hc hV r (U₁ r)⟫_ℝ =
      ∫ y in B0579.cell c,
        (ν * (∑ k : Fin 2, (B0579.pd 0 (fun z => Φ z k) y * Wq r y k +
            B0579.pd 1 (fun z => Φ z k) y * Wη r y k)) +
          inner ℝ (Φ y) (F8Ex.realBvSlice (V r) (W r) (Wq r) (Wη r) y)) := by
    intro r hr
    obtain ⟨hr0, hrq, hrη⟩ := liftWeakSol_ae hwk hr
    have hbv_ae : (F8WeakEx.bvCLM hc hV r (U₁ r) : Plane → F8Ex.RMerid) =ᵐ[F8Ex.cellMeas c]
        F8Ex.realBvSlice (V r) (W r) (Wq r) (Wη r) := by
      filter_upwards [hr0, hrq, hrη, F8WeakEx.bvCLM_ae_realBvSlice hc hV hr (U₁ r)] with
        y a0 aq aη abv
      rw [abv]
      dsimp only [U₁]
      simp only [F8Ex.realBvSlice, a0, aq, aη]
    have hq_int : ⟪φq, F8WeakEx.dqCLM c (U₁ r)⟫_ℝ =
        ∫ y in B0579.cell c, ∑ k : Fin 2, B0579.pd 0 (fun z => Φ z k) y * Wq r y k := by
      rw [F8WeakEx.inner_cylSmoothToL2_right]
      refine integral_congr_ae ?_
      filter_upwards [hrq] with y aq
      rw [aq, PiLp.inner_apply, Fin.sum_univ_two, Fin.sum_univ_two,
        F8WeakEx.pd_coord_cylSmooth hsm 0 0 y, F8WeakEx.pd_coord_cylSmooth hsm 0 1 y]
      simp [mul_comm]
    have hη_int : ⟪φη, F8WeakEx.detaCLM c (U₁ r)⟫_ℝ =
        ∫ y in B0579.cell c, ∑ k : Fin 2, B0579.pd 1 (fun z => Φ z k) y * Wη r y k := by
      rw [F8WeakEx.inner_cylSmoothToL2_right]
      refine integral_congr_ae ?_
      filter_upwards [hrη] with y aη
      rw [aη, PiLp.inner_apply, Fin.sum_univ_two, Fin.sum_univ_two,
        F8WeakEx.pd_coord_cylSmooth hsm 1 0 y, F8WeakEx.pd_coord_cylSmooth hsm 1 1 y]
      simp [mul_comm]
    have hb_int : ⟪φ₀, F8WeakEx.bvCLM hc hV r (U₁ r)⟫_ℝ =
        ∫ y in B0579.cell c, inner ℝ (Φ y) (F8Ex.realBvSlice (V r) (W r) (Wq r) (Wη r) y) := by
      rw [F8WeakEx.inner_cylSmoothToL2_right]
      refine integral_congr_ae ?_
      filter_upwards [hbv_ae] with y abv
      rw [abv]
    have hmΦ : MemLp Φ 2 (F8Ex.cellMeas c) := F8Ex.memLp_realSolCylTest hΦ
    have hmb : MemLp (F8Ex.realBvSlice (V r) (W r) (Wq r) (Wη r)) 2 (F8Ex.cellMeas c) := by
      have hmb0 : MemLp (F8WeakEx.bvCLM hc hV r (U₁ r) : Plane → F8Ex.RMerid) 2
          (F8Ex.cellMeas c) := by
        let gb : Plane → Vec2 := F8WeakEx.bvCLM hc hV r (U₁ r)
        change MemLp gb 2 (F8Ex.cellMeas c)
        rw [F8WeakEx.cellMeas_eq_cellμ]
        exact Lp.memLp (F8WeakEx.bvCLM hc hV r (U₁ r))
      exact MemLp.ae_eq hbv_ae hmb0
    have hi_bv : IntegrableOn
        (fun y => inner ℝ (Φ y) (F8Ex.realBvSlice (V r) (W r) (Wq r) (Wη r) y))
        (B0579.cell c) volume := F8Ex.integrableOn_innerR_cell hmΦ hmb
    have hi_q : IntegrableOn
        (fun y => ∑ k : Fin 2, B0579.pd 0 (fun z => Φ z k) y * Wq r y k)
        (B0579.cell c) volume := by
      have hi0 : IntegrableOn
          (fun y => ⟪fderiv ℝ Φ y (B0579.dir 0),
            (F8WeakEx.dqCLM c (U₁ r) : Plane → F8Ex.RMerid) y⟫_ℝ)
          (B0579.cell c) volume := by
        rw [F8WeakEx.b0579_cell_eq_cyl_cell]
        refine (L2.integrable_inner (𝕜 := ℝ) φq (F8WeakEx.dqCLM c (U₁ r))).congr ?_
        filter_upwards [(F8WeakEx.memLp_of_cylSmooth (hsm.dir (B0579.dir 0))).coeFn_toLp] with y hy
        dsimp only [φq, F8WeakEx.cylSmoothToL2]
        rw [hy]
      refine hi0.congr ?_
      filter_upwards [hrq] with y aq
      rw [aq, PiLp.inner_apply, Fin.sum_univ_two, Fin.sum_univ_two,
        F8WeakEx.pd_coord_cylSmooth hsm 0 0 y, F8WeakEx.pd_coord_cylSmooth hsm 0 1 y]
      simp [mul_comm]
    have hi_η : IntegrableOn
        (fun y => ∑ k : Fin 2, B0579.pd 1 (fun z => Φ z k) y * Wη r y k)
        (B0579.cell c) volume := by
      have hi1 : IntegrableOn
          (fun y => ⟪fderiv ℝ Φ y (B0579.dir 1),
            (F8WeakEx.detaCLM c (U₁ r) : Plane → F8Ex.RMerid) y⟫_ℝ)
          (B0579.cell c) volume := by
        rw [F8WeakEx.b0579_cell_eq_cyl_cell]
        refine (L2.integrable_inner (𝕜 := ℝ) φη (F8WeakEx.detaCLM c (U₁ r))).congr ?_
        filter_upwards [(F8WeakEx.memLp_of_cylSmooth (hsm.dir (B0579.dir 1))).coeFn_toLp] with y hy
        dsimp only [φη, F8WeakEx.cylSmoothToL2]
        rw [hy]
      refine hi1.congr ?_
      filter_upwards [hrη] with y aη
      rw [aη, PiLp.inner_apply, Fin.sum_univ_two, Fin.sum_univ_two,
        F8WeakEx.pd_coord_cylSmooth hsm 1 0 y, F8WeakEx.pd_coord_cylSmooth hsm 1 1 y]
      simp [mul_comm]
    have hsplit_sum :
        (∫ y in B0579.cell c,
          (ν * (∑ k : Fin 2, (B0579.pd 0 (fun z => Φ z k) y * Wq r y k +
              B0579.pd 1 (fun z => Φ z k) y * Wη r y k)) +
            inner ℝ (Φ y) (F8Ex.realBvSlice (V r) (W r) (Wq r) (Wη r) y))) =
        (∫ y in B0579.cell c,
          (ν * ((∑ k : Fin 2, B0579.pd 0 (fun z => Φ z k) y * Wq r y k) +
              (∑ k : Fin 2, B0579.pd 1 (fun z => Φ z k) y * Wη r y k)) +
            inner ℝ (Φ y) (F8Ex.realBvSlice (V r) (W r) (Wq r) (Wη r) y))) := by
      refine setIntegral_congr_fun (B0579.measurableSet_cell c) fun y _ => ?_
      simp only [Fin.sum_univ_two]
      ring
    have hi_visc : IntegrableOn
        (fun y => ν * ((∑ k : Fin 2, B0579.pd 0 (fun z => Φ z k) y * Wq r y k) +
            (∑ k : Fin 2, B0579.pd 1 (fun z => Φ z k) y * Wη r y k)))
        (B0579.cell c) volume :=
      (Integrable.add hi_q hi_η).const_mul ν
    rw [hsplit_sum, integral_add hi_visc hi_bv, integral_const_mul, integral_add hi_q hi_η,
      ← hq_int, ← hη_int, ← hb_int]
  have huIcc : ∀ r ∈ uIcc 0 t, r ∈ Icc (0 : ℝ) 2 := by
    rw [uIcc_of_le ht.1]
    exact fun r hr => ⟨hr.1, hr.2.trans ht.2⟩
  rw [hhead, intervalIntegral.integral_congr (fun r hr => hslice r (huIcc r hr))]
  exact hwk_eq

/-! ## 2. Solenoidal test completeness in `divFree c` (`0 < c`) -/

private lemma isRealSolCylTest_rotT {c : ℝ} {φ : Plane → ℝ}
    (hφ : Sob.IsCylTest c φ) : F8Ex.IsRealSolCylTest c (Cyl.rotT φ) where
  cyl_test k := by
    fin_cases k
    · exact (F8WeakEx.isCylTest_sob_iff c _).mp (Cyl.isCylTest_partialEta hφ)
    · have hq := Cyl.isCylTest_partialQ hφ
      have hneg : Sob.IsCylTest c (fun y => -Cyl.partialQ φ y) :=
        ⟨hq.smooth.neg, fun z => by simp [hq.periodic z],
          let ⟨R, hR⟩ := hq.bounded; ⟨R, fun z hz => by simp [hR z hz]⟩⟩
      exact (F8WeakEx.isCylTest_sob_iff c _).mp hneg
  div_free y := by
    have hdφ := hφ.differentiable
    have hη_sm := Cyl.isCylTest_partialEta hφ
    have hq_sm := Cyl.isCylTest_partialQ hφ
    have hfunη : Cyl.partialEta φ = fun w => fderiv ℝ φ w ((0 : ℝ), (1 : ℝ)) :=
      funext (Cyl.partialEta_eq_fderiv hdφ)
    have h1 : Cyl.partialQ (fun w => Cyl.rotT φ w 0) y =
        Sob.iterDirDeriv [((1 : ℝ), (0 : ℝ)), ((0 : ℝ), (1 : ℝ))] φ y := by
      change Cyl.partialQ (Cyl.partialEta φ) y = _
      rw [Cyl.partialQ_eq_fderiv hη_sm.differentiable y, hfunη]
      rfl
    have h2 : Cyl.partialEta (fun w => Cyl.rotT φ w 1) y =
        -Sob.iterDirDeriv [((0 : ℝ), (1 : ℝ)), ((1 : ℝ), (0 : ℝ))] φ y := by
      change Cyl.partialEta (fun w => -Cyl.partialQ φ w) y = _
      rw [Cyl.partialEta_eq_fderiv hq_sm.differentiable.fun_neg y, fderiv_fun_neg, neg_apply]
      congr 1
      rw [funext (Cyl.partialQ_eq_fderiv hdφ)]
      rfl
    have hsymm : Sob.iterDirDeriv [((1 : ℝ), (0 : ℝ)), ((0 : ℝ), (1 : ℝ))] φ =
        Sob.iterDirDeriv [((0 : ℝ), (1 : ℝ)), ((1 : ℝ), (0 : ℝ))] φ :=
      Sob.iterDirDeriv_perm (List.Perm.swap ((0 : ℝ), (1 : ℝ)) ((1 : ℝ), (0 : ℝ)) []) hφ.smooth
    unfold Cyl.divergence
    rw [h1, h2, congrFun hsymm y, add_neg_cancel]

private def pairH10 {c : ℝ} {h : Plane → ℝ}
    (hh0 : MemLp h 2 (Sob.wμ (Sob.cylinder c).μ (Cyl.ρ0 c))) : Cyl.Hneg c 0 1 :=
  (innerSL ℝ (hh0.toLp h)).comp (Sob.W.value (Sob.cylinder c) (Cyl.ρ0 c) ℝ ℝ 1 2)

private lemma pairH10_testH {c : ℝ} (hc : 0 < c) {h : Plane → ℝ}
    (hh0 : MemLp h 2 (Sob.wμ (Sob.cylinder c).μ (Cyl.ρ0 c)))
    {ψ : Plane → ℝ} (hψ : Sob.IsCylTest c ψ) :
    pairH10 hh0 (Cyl.testH hc hψ (Cyl.ρ0 c) 1) = ∫ z in Cyl.cell c, h z * ψ z := by
  simp only [pairH10, ContinuousLinearMap.comp_apply, innerSL_apply_apply]
  rw [L2.inner_def]
  have hcoe1 : (hh0.toLp h : Plane → ℝ) =ᵐ[cellμ c] h := by
    rw [← Cyl.wμ_ρwW_zero_inv c]
    exact hh0.coeFn_toLp
  have hcoe2 : (Sob.W.value (Sob.cylinder c) (Cyl.ρ0 c) ℝ ℝ 1 2
      (Cyl.testH hc hψ (Cyl.ρ0 c) 1) : Plane → ℝ) =ᵐ[cellμ c] ψ := by
    have hv := Cyl.ae_cell_of_cylinder (Cyl.coeFn_deriv_testH hc hψ (Cyl.ρ0 c) 1 Sob.Idx.zero)
    have h1 := Sob.W.deriv_zero (D := Sob.cylinder c) (ρ := Cyl.ρ0 c) (𝕜 := ℝ) (F := ℝ)
      (k := 1) (p := 2) (Cyl.testH hc hψ (Cyl.ρ0 c) 1)
    have h2 : Sob.iterDirDeriv ((Sob.cylinder c).word (Sob.Idx.zero : Sob.Idx 2 1)) ψ = ψ := by
      rw [Cyl.word_zero, Sob.iterDirDeriv_nil]
    rwa [h1, h2] at hv
  rw [Cyl.integral_wμ0]
  refine integral_congr_ae ?_
  filter_upwards [hcoe1, hcoe2] with z hz1 hz2
  simp only [RCLike.inner_apply, conj_trivial]
  rw [hz1, hz2, mul_comm]

private lemma eq_zero_of_divFree_and_ortho_solTest {c : ℝ} (hc : 0 < c) (g : L2v c)
    (hg : g ∈ divFree c)
    (horth : ∀ (Φ : Plane → F8Ex.RMerid) (hΦ : F8Ex.IsRealSolCylTest c Φ),
      ⟪F8WeakEx.cylSmoothToL2 (F8WeakEx.isCylSmooth_of_solTest hΦ), g⟫_ℝ = 0) :
    g = 0 := by
  let g0 : Plane → ℝ := fun z => (g : Plane → Vec2) z 0
  let g1 : Plane → ℝ := fun z => (g : Plane → Vec2) z 1
  have hg0 : MemLp g0 2 (cellμ c) :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec2 →L[ℝ] ℝ).comp_memLp' (Lp.memLp g)
  have hg1 : MemLp g1 2 (cellμ c) :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec2 →L[ℝ] ℝ).comp_memLp' (Lp.memLp g)
  have hg0w : MemLp g0 2 (Sob.wμ (Sob.cylinder c).μ (Cyl.ρ0 c)) :=
    (Cyl.wμ_ρwW_zero_inv c).symm ▸ hg0
  have hg1w : MemLp g1 2 (Sob.wμ (Sob.cylinder c).μ (Cyl.ρ0 c)) :=
    (Cyl.wμ_ρwW_zero_inv c).symm ▸ hg1
  let D : Cyl.Hneg c 0 1 × Cyl.Hneg c 0 1 := (pairH10 hg0w, pairH10 hg1w)
  have hcurl : ∀ (φ : Plane → ℝ) (hφ : Sob.IsCylTest c φ),
      D.1 (Cyl.testH hc (hφ.dirDeriv ((0 : ℝ), (1 : ℝ))) (Cyl.ρ0 c) 1) -
        D.2 (Cyl.testH hc (hφ.dirDeriv ((1 : ℝ), (0 : ℝ))) (Cyl.ρ0 c) 1) = 0 := by
    intro φ hφ
    have hdφ := hφ.differentiable
    change pairH10 hg0w _ - pairH10 hg1w _ = 0
    rw [pairH10_testH hc hg0w (hφ.dirDeriv ((0 : ℝ), (1 : ℝ))),
      pairH10_testH hc hg1w (hφ.dirDeriv ((1 : ℝ), (0 : ℝ)))]
    have hi0 : IntegrableOn (fun z => g0 z * fderiv ℝ φ z ((0 : ℝ), (1 : ℝ))) (Cyl.cell c) :=
      (Cyl.integrableOn_test_mul (hφ.dirDeriv ((0 : ℝ), (1 : ℝ))) hg0).congr_fun
        (fun _ _ => by ring) (Cyl.measurableSet_cell c)
    have hi1 : IntegrableOn (fun z => g1 z * fderiv ℝ φ z ((1 : ℝ), (0 : ℝ))) (Cyl.cell c) :=
      (Cyl.integrableOn_test_mul (hφ.dirDeriv ((1 : ℝ), (0 : ℝ))) hg1).congr_fun
        (fun _ _ => by ring) (Cyl.measurableSet_cell c)
    rw [← integral_sub hi0 hi1]
    have hrot := horth (Cyl.rotT φ) (isRealSolCylTest_rotT hφ)
    rw [F8WeakEx.inner_cylSmoothToL2_right, F8WeakEx.b0579_cell_eq_cyl_cell] at hrot
    refine Eq.trans ?_ hrot
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    dsimp only
    rw [real_inner_comm, Cyl.rotT, Cyl.inner_vec,
      Cyl.partialEta_eq_fderiv hdφ z, Cyl.partialQ_eq_fderiv hdφ z]
    simp only [g0, g1]
    ring
  have hdiv : ∀ (φ : Plane → ℝ) (hφ : Sob.IsCylTest c φ),
      D.1 (Cyl.testH hc (hφ.dirDeriv ((1 : ℝ), (0 : ℝ))) (Cyl.ρ0 c) 1) +
        D.2 (Cyl.testH hc (hφ.dirDeriv ((0 : ℝ), (1 : ℝ))) (Cyl.ρ0 c) 1) = 0 := by
    intro φ hφ
    have hdφ := hφ.differentiable
    change pairH10 hg0w _ + pairH10 hg1w _ = 0
    rw [pairH10_testH hc hg0w (hφ.dirDeriv ((1 : ℝ), (0 : ℝ))),
      pairH10_testH hc hg1w (hφ.dirDeriv ((0 : ℝ), (1 : ℝ)))]
    have hi0 : IntegrableOn (fun z => g0 z * fderiv ℝ φ z ((1 : ℝ), (0 : ℝ))) (Cyl.cell c) :=
      (Cyl.integrableOn_test_mul (hφ.dirDeriv ((1 : ℝ), (0 : ℝ))) hg0).congr_fun
        (fun _ _ => by ring) (Cyl.measurableSet_cell c)
    have hi1 : IntegrableOn (fun z => g1 z * fderiv ℝ φ z ((0 : ℝ), (1 : ℝ))) (Cyl.cell c) :=
      (Cyl.integrableOn_test_mul (hφ.dirDeriv ((0 : ℝ), (1 : ℝ))) hg1).congr_fun
        (fun _ _ => by ring) (Cyl.measurableSet_cell c)
    rw [← integral_add hi0 hi1]
    have hgr := Cyl.mem_divFree.mp hg φ hφ
    rw [Cyl.gradL, Cyl.inner_toLp_left] at hgr
    refine Eq.trans ?_ hgr
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    dsimp only
    rw [real_inner_comm, Cyl.gradT, Cyl.inner_vec,
      Cyl.partialQ_eq_fderiv hdφ z, Cyl.partialEta_eq_fderiv hdφ z]
  have hD0 := Cyl.eq_zero_of_curl_div hc D hcurl hdiv
  have hD1 : pairH10 hg0w = 0 := congrArg Prod.fst hD0
  have hD2 : pairH10 hg1w = 0 := congrArg Prod.snd hD0
  have hae_comp : ∀ (hi : Plane → ℝ) (hmi : MemLp hi 2 (cellμ c))
      (hmiw : MemLp hi 2 (Sob.wμ (Sob.cylinder c).μ (Cyl.ρ0 c))),
      pairH10 hmiw = 0 → hi =ᵐ[cellμ c] 0 := by
    intro hi hmi hmiw hp0
    have hmi' : MemLp hi 2 (Sob.cylinder c).μ := (Cyl.cylinder_μ_eq c).symm ▸ hmi
    have hae_cyl : hi =ᵐ[(Sob.cylinder c).μ] 0 := by
      refine (Sob.cylinder c).ae_zero hi (hmi'.locallyIntegrable (by norm_num)) fun ψ hψ => ?_
      have hp := congrArg (fun L : Cyl.Hneg c 0 1 => L (Cyl.testH hc hψ (Cyl.ρ0 c) 1)) hp0
      simp only [zero_apply] at hp
      rw [pairH10_testH hc hmiw hψ] at hp
      rw [Cyl.cylinder_μ_eq c]; unfold cellμ
      simpa only [smul_eq_mul, mul_comm (ψ _)] using hp
    rwa [Cyl.cylinder_μ_eq c] at hae_cyl
  apply Lp.ext
  filter_upwards [hae_comp g0 hg0 hg0w hD1, hae_comp g1 hg1 hg1w hD2,
    Lp.coeFn_zero Vec2 2 (cellμ c)] with z hz0 hz1 hzZ
  rw [hzZ]
  ext i
  fin_cases i
  · exact hz0
  · exact hz1

/-! ## 3. Even product-bump mollifier `mollCLM` and `dmollCLM` on `L2v c` -/

def bump1D (k : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := ((k : ℝ) + 2)⁻¹
  rOut := 2 * ((k : ℝ) + 2)⁻¹
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have hp : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    linarith [inv_pos.mpr hp]

def k1 (k : ℕ) : ℝ → ℝ := (bump1D k).normed volume
def k1' (k : ℕ) : ℝ → ℝ := deriv (k1 k)

private lemma k1_nonneg (k : ℕ) (s : ℝ) : 0 ≤ k1 k s := (bump1D k).nonneg_normed s
private lemma k1_neg (k : ℕ) (s : ℝ) : k1 k (-s) = k1 k s := (bump1D k).normed_neg s
private lemma k1_contDiff (k : ℕ) : ContDiff ℝ ∞ (k1 k) := (bump1D k).contDiff_normed
private lemma k1_hasCompactSupport (k : ℕ) : HasCompactSupport (k1 k) :=
  (bump1D k).hasCompactSupport_normed
private lemma k1_integral (k : ℕ) : ∫ s : ℝ, k1 k s = 1 := (bump1D k).integral_normed

private lemma k1_integrable (k : ℕ) : Integrable (k1 k) volume :=
  (k1_contDiff k).continuous.integrable_of_hasCompactSupport (k1_hasCompactSupport k)

private lemma k1_eq_zero_of_le (k : ℕ) {s : ℝ} (hs : 2 * ((k : ℝ) + 2)⁻¹ ≤ |s|) :
    k1 k s = 0 := by
  by_contra h
  have hmem : s ∈ Function.support (k1 k) := h
  unfold k1 at hmem
  rw [(bump1D k).support_normed_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at hmem
  change |s| < 2 * ((k : ℝ) + 2)⁻¹ at hmem
  linarith

private lemma k1_eq_zero_of_one_le (k : ℕ) {s : ℝ} (hs : 1 ≤ |s|) : k1 k s = 0 := by
  refine k1_eq_zero_of_le k (le_trans ?_ hs)
  have hk : (2 : ℝ) ≤ (k : ℝ) + 2 := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hinv : ((k : ℝ) + 2)⁻¹ ≤ (2 : ℝ)⁻¹ :=
    inv_anti₀ (by norm_num) hk
  linarith

private lemma k1'_contDiff (k : ℕ) : ContDiff ℝ ∞ (k1' k) :=
  (k1_contDiff k).deriv'

private lemma k1'_hasCompactSupport (k : ℕ) : HasCompactSupport (k1' k) :=
  (k1_hasCompactSupport k).deriv

private lemma k1'_integrable (k : ℕ) : Integrable (k1' k) volume :=
  (k1'_contDiff k).continuous.integrable_of_hasCompactSupport (k1'_hasCompactSupport k)

private lemma hasDerivAt_k1 (k : ℕ) (s : ℝ) : HasDerivAt (k1 k) (k1' k s) s :=
  ((k1_contDiff k).differentiable (by norm_num) s).hasDerivAt

private lemma k1'_neg (k : ℕ) (s : ℝ) : k1' k (-s) = -k1' k s := by
  have h1 : HasDerivAt (fun t : ℝ => k1 k (-t)) (-k1' k (-s)) s := by
    have hc : HasDerivAt (k1 k ∘ Neg.neg) (k1' k (-s) * -1) s :=
      (hasDerivAt_k1 k (-s)).comp s (hasDerivAt_neg s)
    convert hc using 1
    · rfl
    · ring
  have heq : (fun t : ℝ => k1 k (-t)) = k1 k := funext (k1_neg k)
  rw [heq] at h1
  linarith [h1.unique (hasDerivAt_k1 k s)]

def K2 (k : ℕ) (w : Plane) : ℝ := k1 k w.1 * k1 k w.2

def DK2 (j : Fin 2) (k : ℕ) (w : Plane) : ℝ :=
  match j with
  | ⟨0, _⟩ => k1' k w.1 * k1 k w.2
  | ⟨1, _⟩ => k1 k w.1 * k1' k w.2

private lemma integrable_K2 (k : ℕ) : Integrable (K2 k) volume :=
  F8WeakEx.integrable_prod_plane (k1_integrable k) (k1_integrable k)

private lemma integrable_DK2 (j : Fin 2) (k : ℕ) : Integrable (DK2 j k) volume := by
  fin_cases j
  · exact F8WeakEx.integrable_prod_plane (k1'_integrable k) (k1_integrable k)
  · exact F8WeakEx.integrable_prod_plane (k1_integrable k) (k1'_integrable k)

private lemma K2_nonneg (k : ℕ) (w : Plane) : 0 ≤ K2 k w :=
  mul_nonneg (k1_nonneg k w.1) (k1_nonneg k w.2)

private lemma K2_neg (k : ℕ) (w : Plane) : K2 k (-w) = K2 k w := by
  simp [K2, k1_neg]

private lemma DK2_neg (j : Fin 2) (k : ℕ) (w : Plane) : DK2 j k (-w) = -DK2 j k w := by
  fin_cases j <;> simp [DK2, k1_neg, k1'_neg]

private lemma K2_contDiff (k : ℕ) : ContDiff ℝ ∞ (K2 k) :=
  ((k1_contDiff k).comp contDiff_fst).mul ((k1_contDiff k).comp contDiff_snd)

private lemma K2_hasCompactSupport (k : ℕ) : HasCompactSupport (K2 k) := by
  refine HasCompactSupport.intro (isCompact_Icc.prod isCompact_Icc :
      IsCompact (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)) fun w hw => ?_
  by_cases h1 : |w.1| < 1
  · by_cases h2 : |w.2| < 1
    · exfalso
      exact hw ⟨⟨(abs_lt.mp h1).1.le, (abs_lt.mp h1).2.le⟩,
        ⟨(abs_lt.mp h2).1.le, (abs_lt.mp h2).2.le⟩⟩
    · simp [K2, k1_eq_zero_of_one_le k (not_lt.mp h2)]
  · simp [K2, k1_eq_zero_of_one_le k (not_lt.mp h1)]

private lemma integral_K2 (k : ℕ) : ∫ w : Plane, K2 k w = 1 := by
  change ∫ w : ℝ × ℝ, k1 k w.1 * k1 k w.2 ∂(volume : Measure (ℝ × ℝ)) = 1
  rw [Measure.volume_eq_prod, integral_prod_mul, k1_integral k, mul_one]

private lemma integral_norm_K2 (k : ℕ) : ∫ w : Plane, ‖K2 k w‖ = 1 := by
  have heq : (fun w : Plane => ‖K2 k w‖) = K2 k :=
    funext fun w => Real.norm_of_nonneg (K2_nonneg k w)
  rw [heq, integral_K2 k]

def mollCLM {c : ℝ} (hc : 0 < c) (k : ℕ) : L2v c →L[ℝ] L2v c :=
  F8WeakEx.shiftAvgCLM hc (K2 k) (integrable_K2 k)

def dmollCLM {c : ℝ} (hc : 0 < c) (j : Fin 2) (k : ℕ) : L2v c →L[ℝ] L2v c :=
  F8WeakEx.shiftAvgCLM hc (DK2 j k) (integrable_DK2 j k)

private lemma norm_mollCLM_le {c : ℝ} (hc : 0 < c) (k : ℕ) : ‖mollCLM hc k‖ ≤ 1 :=
  (F8WeakEx.norm_shiftAvgCLM_le hc (integrable_K2 k)).trans_eq (integral_norm_K2 k)

private lemma mollCLM_P0_comm {c : ℝ} (hc : 0 < c) (k : ℕ) (x : L2v c) :
    mollCLM hc k (P0 c x) = P0 c (mollCLM hc k x) :=
  F8WeakEx.shiftAvgCLM_P0_comm hc (integrable_K2 k) x

private lemma inner_mollCLM_symm {c : ℝ} (hc : 0 < c) (k : ℕ) (x y : L2v c) :
    ⟪mollCLM hc k x, y⟫_ℝ = ⟪x, mollCLM hc k y⟫_ℝ := by
  show ⟪F8WeakEx.shiftAvgCLM hc (K2 k) (integrable_K2 k) x, y⟫_ℝ =
    ⟪x, F8WeakEx.shiftAvgCLM hc (K2 k) (integrable_K2 k) y⟫_ℝ
  rw [F8WeakEx.inner_shiftAvgCLM hc (integrable_K2 k) x y,
    real_inner_comm _ x, F8WeakEx.inner_shiftAvgCLM hc (integrable_K2 k) y x]
  have h1 : (fun w : Plane => K2 k w * ⟪planeShiftL2CLM hc w x, y⟫_ℝ) =
      fun w => (fun v : Plane => K2 k v * ⟪planeShiftL2CLM hc v y, x⟫_ℝ) (-w) := by
    funext w
    dsimp only
    rw [F8WeakEx.inner_planeShiftL2CLM_adj hc w x y, K2_neg k w, real_inner_comm]
  rw [h1]
  exact integral_neg_eq_self
    (fun v : Plane => K2 k v * ⟪planeShiftL2CLM hc v y, x⟫_ℝ) volume

private lemma inner_dmollCLM_skew {c : ℝ} (hc : 0 < c) (j : Fin 2) (k : ℕ) (x y : L2v c) :
    ⟪dmollCLM hc j k x, y⟫_ℝ = -⟪x, dmollCLM hc j k y⟫_ℝ := by
  show ⟪F8WeakEx.shiftAvgCLM hc (DK2 j k) (integrable_DK2 j k) x, y⟫_ℝ =
    -⟪x, F8WeakEx.shiftAvgCLM hc (DK2 j k) (integrable_DK2 j k) y⟫_ℝ
  rw [F8WeakEx.inner_shiftAvgCLM hc (integrable_DK2 j k) x y,
    real_inner_comm _ x, F8WeakEx.inner_shiftAvgCLM hc (integrable_DK2 j k) y x]
  have h1 : (fun w : Plane => DK2 j k w * ⟪planeShiftL2CLM hc w x, y⟫_ℝ) =
      fun w => -((fun v : Plane => DK2 j k v * ⟪planeShiftL2CLM hc v y, x⟫_ℝ) (-w)) := by
    funext w
    dsimp only
    rw [F8WeakEx.inner_planeShiftL2CLM_adj hc w x y, DK2_neg j k w, real_inner_comm]
    ring
  rw [h1, integral_neg]
  exact congrArg Neg.neg (integral_neg_eq_self
    (fun v : Plane => DK2 j k v * ⟪planeShiftL2CLM hc v y, x⟫_ℝ) volume)

private lemma inner_dir_cylSmooth_mollCLM {c : ℝ} (hc : 0 < c) (k : ℕ)
    {Ψ : Plane → F8Ex.RMerid} (hΨ : Sob.IsCylSmooth c Ψ) (j : Fin 2) (x : L2v c) :
    ⟪F8WeakEx.cylSmoothToL2 (hΨ.dir (B0579.dir j)), mollCLM hc k x⟫_ℝ =
      -⟪F8WeakEx.cylSmoothToL2 hΨ, dmollCLM hc j k x⟫_ℝ := by
  rw [real_inner_comm (mollCLM hc k x) _, real_inner_comm (dmollCLM hc j k x) _]
  fin_cases j
  · exact F8WeakEx.inner_shiftAvg_prod_ibp_q hc
      (k1_integrable k) (k1'_integrable k) (k1_integrable k) (hasDerivAt_k1 k) hΨ x
  · exact F8WeakEx.inner_shiftAvg_prod_ibp_eta hc
      (k1_integrable k) (k1_integrable k) (k1'_integrable k) (hasDerivAt_k1 k) hΨ x

private lemma hasWeakCellDerivR_dmollCLM {c : ℝ} (hc : 0 < c) (j : Fin 2) (k : ℕ) (x : L2v c) :
    ∀ i : Fin 2, F8Ex.HasWeakCellDerivR c j
      (fun y => (mollCLM hc k x : Plane → F8Ex.RMerid) y i)
      (fun y => (dmollCLM hc j k x : Plane → F8Ex.RMerid) y i) := by
  rw [F8WeakEx.hasWeakCellDerivR_l2_iff]
  intro ψ hψ i
  have hsm := F8WeakEx.isCylSmooth_single hψ i
  have hdir : F8WeakEx.cylSmoothToL2 (F8WeakEx.isCylSmooth_single (hψ.pd j) i) =
      F8WeakEx.cylSmoothToL2 (hsm.dir (B0579.dir j)) := by
    apply Lp.ext
    filter_upwards [(F8WeakEx.memLp_of_cylSmooth (F8WeakEx.isCylSmooth_single (hψ.pd j) i)).coeFn_toLp,
      (F8WeakEx.memLp_of_cylSmooth (hsm.dir (B0579.dir j))).coeFn_toLp] with y hy1 hy2
    dsimp only [F8WeakEx.cylSmoothToL2]
    rw [hy1, hy2]
    ext l
    rw [F8WeakEx.pd_coord_cylSmooth hsm j l y]
    fin_cases i <;> fin_cases l <;> simp [B0579.pd]
  rw [real_inner_comm _ (mollCLM hc k x), real_inner_comm _ (dmollCLM hc j k x),
    hdir, inner_dir_cylSmooth_mollCLM hc k hsm j x]
  ring

private lemma dmollCLM_eq_mollCLM_of_weakDeriv {c : ℝ} (hc : 0 < c) (j : Fin 2) (k : ℕ)
    {x dx : L2v c}
    (h : ∀ i : Fin 2, F8Ex.HasWeakCellDerivR c j (fun y => x y i) (fun y => dx y i)) :
    dmollCLM hc j k x = mollCLM hc k dx :=
  F8WeakEx.eq_of_hasWeakCellDerivR hc (hasWeakCellDerivR_dmollCLM hc j k x)
    (F8WeakEx.hasWeakCellDerivR_shiftAvgCLM hc (integrable_K2 k) h)

private lemma inner_dmollCLM_mollCLM_weak {c : ℝ} (hc : 0 < c) (j : Fin 2) (k : ℕ)
    {x dx : L2v c}
    (h : ∀ i : Fin 2, F8Ex.HasWeakCellDerivR c j (fun y => x y i) (fun y => dx y i)) :
    ⟪dmollCLM hc j k dx, mollCLM hc k x⟫_ℝ = -‖mollCLM hc k dx‖ ^ 2 := by
  have hm : dmollCLM hc j k (mollCLM hc k x) = mollCLM hc k (mollCLM hc k dx) :=
    dmollCLM_eq_mollCLM_of_weakDeriv hc j k
      (F8WeakEx.hasWeakCellDerivR_shiftAvgCLM hc (integrable_K2 k) h)
  rw [inner_dmollCLM_skew hc j k, hm, ← inner_mollCLM_symm hc k, real_inner_self_eq_norm_sq]

private lemma tendsto_mollCLM {c : ℝ} (hc : 0 < c) (x : L2v c) :
    Tendsto (fun k : ℕ => mollCLM hc k x) atTop (𝓝 x) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have horb := continuous_planeShiftL2_orbit hc x
  have h0 : planeShiftL2CLM hc 0 x = x := by
    rw [planeShiftL2CLM_apply]
    unfold planeShiftL2
    have hq0 : TrainB.qShiftL2 hc 0 x = x := by
      have h1 := qShiftL2_add_comp hc (a := 0) (b := 0) x
      have h2 := TrainB.qShiftL2_neg_comp (a := 0) hc x
      simp only [add_zero, neg_zero] at h1 h2
      exact h1.symm.trans h2
    have he0 : TrainB.etaShiftL2 c 0 x = x := by
      apply Lp.ext
      filter_upwards [TrainB.etaShiftL2_ae (c := c) (a := 0) x] with z hz
      simpa only [Prod.mk_zero_zero, add_zero] using hz
    change TrainB.qShiftL2 hc (-0) (TrainB.etaShiftL2 c (-0) x) = x
    simp [he0, hq0]
  obtain ⟨δ, hδ, hb⟩ := Metric.continuousAt_iff.mp (horb.continuousAt (x := 0)) (ε / 2) (half_pos hε)
  rw [h0] at hb
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / δ)
  refine ⟨N, fun k hk => ?_⟩
  rw [dist_eq_norm]
  have h1 : x = ∫ w : Plane, K2 k w • x := by
    rw [integral_smul_const, integral_K2 k, one_smul]
  have hdiff : mollCLM hc k x - x =
      ∫ w : Plane, K2 k w • (planeShiftL2CLM hc w x - x) := by
    change (∫ w : Plane, K2 k w • planeShiftL2CLM hc w x) - x = _
    conv_lhs => rhs; rw [h1]
    rw [← integral_sub (F8WeakEx.integrable_kernel_smul_planeShift hc (integrable_K2 k) x)
      ((integrable_K2 k).smul_const x)]
    congr 1; funext w; rw [smul_sub]
  rw [hdiff]
  have hpt : ∀ w : Plane, ‖K2 k w • (planeShiftL2CLM hc w x - x)‖ ≤ K2 k w * (ε / 2) := by
    intro w
    rw [norm_smul, Real.norm_of_nonneg (K2_nonneg k w)]
    by_cases hw : ‖w‖ < δ
    · have hd : dist w 0 < δ := by simpa [dist_zero_right] using hw
      have hlt : ‖planeShiftL2CLM hc w x - x‖ < ε / 2 := by
        simpa [dist_eq_norm] using hb hd
      exact mul_le_mul_of_nonneg_left hlt.le (K2_nonneg k w)
    · have hk2 : 2 / ((k : ℝ) + 2) < δ := by
        have hkN : (N : ℝ) ≤ k := Nat.cast_le.mpr hk
        have hpos : (0 : ℝ) < (k : ℝ) + 2 := by positivity
        rw [div_lt_iff₀ hpos]
        have hN' : 2 < (N : ℝ) * δ := (div_lt_iff₀ hδ).mp hN
        nlinarith
      have hmax : max |w.1| |w.2| ≥ δ := by
        simpa [Prod.norm_def, Real.norm_eq_abs] using not_lt.mp hw
      have hK0 : K2 k w = 0 := by
        rcases max_choice |w.1| |w.2| with hfst | hsnd
        · rw [hfst] at hmax
          have : 2 * ((k : ℝ) + 2)⁻¹ ≤ |w.1| := by
            rw [← div_eq_mul_inv]; linarith
          simp [K2, k1_eq_zero_of_le k this]
        · rw [hsnd] at hmax
          have : 2 * ((k : ℝ) + 2)⁻¹ ≤ |w.2| := by
            rw [← div_eq_mul_inv]; linarith
          simp [K2, k1_eq_zero_of_le k this]
      simp [hK0]
  have hint_norm : Integrable (fun w : Plane => ‖K2 k w • (planeShiftL2CLM hc w x - x)‖) volume :=
    ((F8WeakEx.integrable_kernel_smul_planeShift hc (integrable_K2 k) x).sub
      ((integrable_K2 k).smul_const x)).congr (ae_of_all _ fun w => (smul_sub _ _ _).symm) |>.norm
  calc ‖∫ w : Plane, K2 k w • (planeShiftL2CLM hc w x - x)‖
      ≤ ∫ w : Plane, ‖K2 k w • (planeShiftL2CLM hc w x - x)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ w : Plane, K2 k w * (ε / 2) :=
        integral_mono hint_norm ((integrable_K2 k).mul_const _) hpt
    _ = (∫ w : Plane, K2 k w) * (ε / 2) := integral_mul_const _ _
    _ = ε / 2 := by rw [integral_K2 k, one_mul]
    _ < ε := half_lt_self hε

/-! ## 4. Mollifying `IsRealSolCylTest` fields by `K2 k` -/

def convSolTest (k : ℕ) (Φ : Plane → F8Ex.RMerid) : Plane → F8Ex.RMerid :=
  K2 k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] Φ

private lemma locallyIntegrable_of_cylSmooth {c : ℝ} {Ψ : Plane → F8Ex.RMerid}
    (hΨ : Sob.IsCylSmooth c Ψ) : LocallyIntegrable Ψ volume :=
  hΨ.smooth.continuous.locallyIntegrable

private lemma isCylSmooth_convSolTest {c : ℝ} (k : ℕ) {Φ : Plane → F8Ex.RMerid}
    (hsm : Sob.IsCylSmooth c Φ) : Sob.IsCylSmooth c (convSolTest k Φ) where
  smooth := (K2_hasCompactSupport k).contDiff_convolution_left _ (K2_contDiff k)
    (locallyIntegrable_of_cylSmooth hsm)
  periodic y := by
    unfold convSolTest
    simp only [MeasureTheory.convolution_def, ContinuousLinearMap.lsmul_apply]
    congr 1; funext w
    have hshift : y + ((c, 0) : Plane) - w = (y - w) + (c, 0) := by
      ext <;> simp only [Prod.fst_add, Prod.fst_sub, Prod.snd_add, Prod.snd_sub] <;> ring
    rw [hshift, hsm.periodic (y - w)]
  bounded := by
    obtain ⟨R, hR⟩ := hsm.bounded
    refine ⟨max R 0 + 1, fun y hy => ?_⟩
    unfold convSolTest
    simp only [MeasureTheory.convolution_def, ContinuousLinearMap.lsmul_apply]
    have hzero : (fun w : Plane => K2 k w • Φ (y - w)) = 0 := by
      funext w
      by_cases hw : |w.2| < 1
      · have hyw : R < |(y - w).2| := by
          have hR0 : R ≤ max R 0 := le_max_left _ _
          have habs : |y.2| - |w.2| ≤ |y.2 - w.2| := abs_sub_abs_le_abs_sub y.2 w.2
          change R < |y.2 - w.2|
          linarith [(abs_lt.mp hw).2]
        simp [hR (y - w) hyw]
      · simp [K2, k1_eq_zero_of_one_le k (not_lt.mp hw)]
    simp [hzero]

private lemma cylSmoothToL2_conv_eq_mollCLM {c : ℝ} (hc : 0 < c) (k : ℕ)
    {Ψ : Plane → F8Ex.RMerid} (hΨ : Sob.IsCylSmooth c Ψ) :
    F8WeakEx.cylSmoothToL2 (isCylSmooth_convSolTest k hΨ) =
      mollCLM hc k (F8WeakEx.cylSmoothToL2 hΨ) := by
  set L := F8WeakEx.cylSmoothToL2 (isCylSmooth_convSolTest k hΨ)
  set R := mollCLM hc k (F8WeakEx.cylSmoothToL2 hΨ)
  have horth : ∀ {U : Plane → F8Ex.RMerid} (hU : Sob.IsCylSmooth c U),
      ⟪L - R, F8WeakEx.cylSmoothToL2 hU⟫_ℝ = 0 := by
    intro U hU
    rw [inner_sub_left]
    have hmΨ := F8WeakEx.memLp_of_cylSmooth hΨ
    have hmU := F8WeakEx.memLp_of_cylSmooth hU
    have hmC := F8WeakEx.memLp_of_cylSmooth (isCylSmooth_convSolTest k hΨ)
    obtain ⟨M, _, hΨbound⟩ := exists_global_bound_of_cylSmooth hc hΨ
    have hUnorm : Integrable (fun z : Plane => ‖U z‖) (cellμ c) := by
      have hUcell : Integrable U (cellμ c) := by
        rw [Cyl.cellμ, Sob.cyl_cell_eq]; exact hU.integrableOn
      exact hUcell.norm
    have hdom : Integrable (fun p : Plane × Plane => M * (K2 k p.1 * ‖U p.2‖))
        ((volume : Measure Plane).prod (cellμ c)) := by
      simpa only [mul_comm] using ((integrable_K2 k).mul_prod hUnorm).const_mul M
    have hmeas : Measurable (fun p : Plane × Plane => K2 k p.1 * ⟪Ψ (p.2 - p.1), U p.2⟫_ℝ) := by
      have hmK : Measurable (K2 k) := (K2_contDiff k).continuous.measurable
      have hm1 : Measurable Ψ := hΨ.smooth.continuous.measurable
      have hm2 : Measurable U := hU.smooth.continuous.measurable
      fun_prop
    have hjoint : Integrable (fun p : Plane × Plane => K2 k p.1 * ⟪Ψ (p.2 - p.1), U p.2⟫_ℝ)
        ((volume : Measure Plane).prod (cellμ c)) := by
      refine hdom.mono' hmeas.aestronglyMeasurable (ae_of_all _ fun p => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (K2_nonneg k p.1)]
      calc K2 k p.1 * |⟪Ψ (p.2 - p.1), U p.2⟫_ℝ|
          ≤ K2 k p.1 * (‖Ψ (p.2 - p.1)‖ * ‖U p.2‖) :=
            mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (K2_nonneg k p.1)
        _ ≤ K2 k p.1 * (M * ‖U p.2‖) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (hΨbound _) (norm_nonneg _)) (K2_nonneg k p.1)
        _ = M * (K2 k p.1 * ‖U p.2‖) := by ring
    have hR_eq : ⟪R, F8WeakEx.cylSmoothToL2 hU⟫_ℝ =
        ∫ w : Plane, ∫ z : Plane, K2 k w * ⟪Ψ (z - w), U z⟫_ℝ ∂(cellμ c) := by
      dsimp only [R, mollCLM]
      rw [F8WeakEx.inner_shiftAvgCLM hc (integrable_K2 k)]
      refine integral_congr_ae (ae_of_all _ fun w => ?_)
      dsimp only [F8WeakEx.cylSmoothToL2]
      rw [planeShiftL2CLM_apply, inner_planeShiftL2_smooth_eq_integral hc hΨ hmΨ hmU w]
      exact (integral_const_mul (K2 k w) _).symm
    have hL_eq : ⟪L, F8WeakEx.cylSmoothToL2 hU⟫_ℝ =
        ∫ z : Plane, ∫ w : Plane, K2 k w * ⟪Ψ (z - w), U z⟫_ℝ ∂(volume : Measure Plane) ∂(cellμ c) := by
      dsimp only [L, F8WeakEx.cylSmoothToL2]
      rw [Cyl.inner_toLp_eq hmC hmU]
      refine setIntegral_congr_fun (Cyl.measurableSet_cell c) fun z _ => ?_
      have hint_w : Integrable (fun w : Plane => K2 k w • Ψ (z - w)) volume := by
        have hm_w : Measurable (fun w : Plane => K2 k w • Ψ (z - w)) := by
          have hmK : Measurable (K2 k) := (K2_contDiff k).continuous.measurable
          have hm1 : Measurable Ψ := hΨ.smooth.continuous.measurable
          fun_prop
        refine ((integrable_K2 k).mul_const (max M 0)).mono' hm_w.aestronglyMeasurable
          (ae_of_all _ fun w => ?_)
        rw [norm_smul, Real.norm_of_nonneg (K2_nonneg k w)]
        exact mul_le_mul_of_nonneg_left ((hΨbound _).trans (le_max_left _ _)) (K2_nonneg k w)
      unfold convSolTest
      simp only [MeasureTheory.convolution_def, ContinuousLinearMap.lsmul_apply]
      rw [real_inner_comm (U z) _, ← integral_inner hint_w (U z)]
      refine integral_congr_ae (ae_of_all _ fun w => ?_)
      dsimp only
      rw [real_inner_comm, inner_smul_left, RCLike.conj_to_real]
    rw [hL_eq, hR_eq, ← integral_integral_swap hjoint, sub_self]
  let d : L2v c := L - R
  have hd_zero : d = 0 := by
    have hcoord : ∀ i : Fin 2, (fun z : Plane => (d : Plane → Vec2) z i) =ᵐ[cellμ c] 0 := by
      intro i
      let gi : Plane → ℝ := fun z => (d : Plane → Vec2) z i
      have hmi : MemLp gi 2 (Sob.cylinder c).μ := by
        rw [Cyl.cylinder_μ_eq c]
        exact (EuclideanSpace.proj i : Vec2 →L[ℝ] ℝ).comp_memLp' (Lp.memLp d)
      have hae := (Sob.cylinder c).ae_zero gi (hmi.locallyIntegrable (by norm_num)) fun ψ hψ => by
        have hψb := (F8WeakEx.isCylTest_sob_iff c ψ).mp hψ
        have h0 := horth (F8WeakEx.isCylSmooth_single hψb i)
        rw [F8WeakEx.inner_cylSmooth_single hψb i d] at h0
        change ∫ y in B0579.cell c, gi y * ψ y = 0 at h0
        rw [Cyl.cylinder_μ_eq c]; unfold cellμ
        rw [← F8WeakEx.b0579_cell_eq_cyl_cell]
        simpa only [smul_eq_mul, mul_comm (ψ _)] using h0
      rwa [Cyl.cylinder_μ_eq c] at hae
    apply Lp.ext
    filter_upwards [hcoord 0, hcoord 1, Lp.coeFn_zero Vec2 2 (cellμ c)] with z hz0 hz1 hzZ
    rw [hzZ]; ext i; fin_cases i
    · exact hz0
    · exact hz1
  exact sub_eq_zero.mp hd_zero

private lemma hasWeakCellDerivR_of_cylSmooth {c : ℝ} (hc : 0 < c)
    {Ψ : Plane → F8Ex.RMerid} (hΨ : Sob.IsCylSmooth c Ψ) (j i : Fin 2) :
    F8Ex.HasWeakCellDerivR c j (fun y => Ψ y i) (fun y => fderiv ℝ Ψ y (B0579.dir j) i) := by
  have hΨi : Sob.IsCylTest c (fun y => Ψ y i) :=
    (F8WeakEx.isCylTest_sob_iff c _).2 (F8WeakEx.isCylTest_coord_of_cylSmooth hΨ i)
  have hpd_eq : (fun y => fderiv ℝ Ψ y (B0579.dir j) i) =
      fun y => fderiv ℝ (fun z => Ψ z i) y (B0579.dir j) := by
    funext y
    exact F8WeakEx.pd_coord_cylSmooth hΨ j i y
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_⟩
  · have hφs : Sob.IsCylTest c φ := (F8WeakEx.isCylTest_sob_iff c φ).2 hφ
    rw [F8WeakEx.b0579_cell_eq_cyl_cell]
    have hi1 : IntegrableOn (fun y => Ψ y i * B0579.pd j φ y) (Cyl.cell c) := by
      refine ((hφs.dirDeriv (B0579.dir j)).integrableOn_mul hΨi.continuous).congr_fun
        (fun y _ => ?_) (Cyl.measurableSet_cell c)
      dsimp only [B0579.pd]; ring
    have hi2 : IntegrableOn (fun y => fderiv ℝ Ψ y (B0579.dir j) i * φ y) (Cyl.cell c) := by
      refine ((hΨi.dirDeriv (B0579.dir j)).integrableOn_mul hφs.continuous).congr_fun
        (fun y _ => ?_) (Cyl.measurableSet_cell c)
      rw [congrFun hpd_eq y]
    exact ⟨hi1, hi2⟩
  · have hφs : Sob.IsCylTest c φ := (F8WeakEx.isCylTest_sob_iff c φ).2 hφ
    rw [F8WeakEx.b0579_cell_eq_cyl_cell]
    have h1 : (∫ y in Cyl.cell c, Ψ y i * B0579.pd j φ y) =
        ∫ y in Cyl.cell c, fderiv ℝ φ y (B0579.dir j) * Ψ y i :=
      setIntegral_congr_fun (Cyl.measurableSet_cell c) fun y _ => by
        dsimp only [B0579.pd]; ring
    have h2 : (∫ y in Cyl.cell c, fderiv ℝ Ψ y (B0579.dir j) i * φ y) =
        ∫ y in Cyl.cell c, φ y * fderiv ℝ (fun z => Ψ z i) y (B0579.dir j) :=
      setIntegral_congr_fun (Cyl.measurableSet_cell c) fun y _ => by
        rw [congrFun hpd_eq y]; ring
    rw [h1, h2, Cyl.integral_fderiv_mul_test hc hφs hΨi]

private lemma hasWeakCellDerivR_cylSmoothToL2 {c : ℝ} (hc : 0 < c)
    {Ψ : Plane → F8Ex.RMerid} (hΨ : Sob.IsCylSmooth c Ψ) (j : Fin 2) :
    ∀ i : Fin 2, F8Ex.HasWeakCellDerivR c j
      (fun y => (F8WeakEx.cylSmoothToL2 hΨ : Plane → F8Ex.RMerid) y i)
      (fun y => (F8WeakEx.cylSmoothToL2 (hΨ.dir (B0579.dir j)) : Plane → F8Ex.RMerid) y i) := by
  intro i
  have hc0 : (F8WeakEx.cylSmoothToL2 hΨ : Plane → F8Ex.RMerid) =ᵐ[F8Ex.cellMeas c] Ψ := by
    rw [F8WeakEx.cellMeas_eq_cellμ]; exact (F8WeakEx.memLp_of_cylSmooth hΨ).coeFn_toLp
  have hcd : (F8WeakEx.cylSmoothToL2 (hΨ.dir (B0579.dir j)) : Plane → F8Ex.RMerid) =ᵐ[
      F8Ex.cellMeas c] fun y => fderiv ℝ Ψ y (B0579.dir j) := by
    rw [F8WeakEx.cellMeas_eq_cellμ]
    exact (F8WeakEx.memLp_of_cylSmooth (hΨ.dir (B0579.dir j))).coeFn_toLp
  exact F8WeakEx.hasWeakCellDerivR_congr_ae
    (hc0.symm.mono fun y hy => congrArg (fun v : F8Ex.RMerid => v i) hy)
    (hcd.symm.mono fun y hy => congrArg (fun v : F8Ex.RMerid => v i) hy)
    (hasWeakCellDerivR_of_cylSmooth hc hΨ j i)

private lemma fderiv_convSolTest_dir {c : ℝ} (hc : 0 < c) (k : ℕ)
    {Φ : Plane → F8Ex.RMerid} (hsm : Sob.IsCylSmooth c Φ) (j : Fin 2) :
    F8WeakEx.cylSmoothToL2 ((isCylSmooth_convSolTest k hsm).dir (B0579.dir j)) =
      mollCLM hc k (F8WeakEx.cylSmoothToL2 (hsm.dir (B0579.dir j))) := by
  have h1 := hasWeakCellDerivR_cylSmoothToL2 hc (isCylSmooth_convSolTest k hsm) j
  rw [cylSmoothToL2_conv_eq_mollCLM hc k hsm] at h1
  have h2 := F8WeakEx.hasWeakCellDerivR_shiftAvgCLM hc (integrable_K2 k)
    (hasWeakCellDerivR_cylSmoothToL2 hc hsm j)
  exact F8WeakEx.eq_of_hasWeakCellDerivR hc h1 h2

private lemma isRealSolCylTest_convSolTest {c : ℝ} (hc : 0 < c) (k : ℕ)
    {Φ : Plane → F8Ex.RMerid} (hΦ : F8Ex.IsRealSolCylTest c Φ) :
    F8Ex.IsRealSolCylTest c (convSolTest k Φ) where
  cyl_test i :=
    F8WeakEx.isCylTest_coord_of_cylSmooth
      (isCylSmooth_convSolTest k (F8WeakEx.isCylSmooth_of_solTest hΦ)) i
  div_free y := by
    let hsm := F8WeakEx.isCylSmooth_of_solTest hΦ
    let hsm_c := isCylSmooth_convSolTest k hsm
    let Ψ := convSolTest k Φ
    have hΨ0 : Sob.IsCylTest c (fun z => Ψ z 0) :=
      (F8WeakEx.isCylTest_sob_iff c _).2 (F8WeakEx.isCylTest_coord_of_cylSmooth hsm_c 0)
    have hΨ1 : Sob.IsCylTest c (fun z => Ψ z 1) :=
      (F8WeakEx.isCylTest_sob_iff c _).2 (F8WeakEx.isCylTest_coord_of_cylSmooth hsm_c 1)
    let d : Plane → ℝ := Cyl.divergence Ψ
    have hd_eq : d = fun z =>
        fderiv ℝ (fun w => Ψ w 0) z ((1 : ℝ), (0 : ℝ)) +
          fderiv ℝ (fun w => Ψ w 1) z ((0 : ℝ), (1 : ℝ)) := by
      funext z
      unfold d Cyl.divergence
      rw [Cyl.partialQ_eq_fderiv hΨ0.differentiable, Cyl.partialEta_eq_fderiv hΨ1.differentiable]
    have hd_test : Sob.IsCylTest c d := by
      rw [hd_eq]
      have h0 := hΨ0.dirDeriv ((1 : ℝ), (0 : ℝ))
      have h1 := hΨ1.dirDeriv ((0 : ℝ), (1 : ℝ))
      refine ⟨h0.smooth.add h1.smooth, fun z => by simp [h0.periodic z, h1.periodic z], ?_⟩
      obtain ⟨R0, hR0⟩ := h0.bounded
      obtain ⟨R1, hR1⟩ := h1.bounded
      exact ⟨max R0 R1, fun z hz => by
        simp [hR0 z (lt_of_le_of_lt (le_max_left _ _) hz),
          hR1 z (lt_of_le_of_lt (le_max_right _ _) hz)]⟩
    have hmem_df : F8WeakEx.cylSmoothToL2 hsm_c ∈ divFree c := by
      have hp0 : P0 c (F8WeakEx.cylSmoothToL2 hsm) = F8WeakEx.cylSmoothToL2 hsm :=
        Cyl.P0_eq_self (F8WeakEx.cylSmoothToL2_mem_divFree_of_solTest hc hΦ)
      rw [show F8WeakEx.cylSmoothToL2 hsm_c = mollCLM hc k (F8WeakEx.cylSmoothToL2 hsm) from
        cylSmoothToL2_conv_eq_mollCLM hc k hsm, ← hp0, mollCLM_P0_comm hc k]
      exact Cyl.P0_mem _
    have horth_d : ∀ (φ : Plane → ℝ), Sob.IsCylTest c φ → ∫ z in Cyl.cell c, φ z * d z = 0 := by
      intro φ hφ
      have hgr := Cyl.mem_divFree.mp hmem_df φ hφ
      rw [Cyl.gradL, F8WeakEx.cylSmoothToL2, Cyl.inner_toLp_eq] at hgr
      have he : (fun z => ⟪Cyl.gradT φ z, Ψ z⟫_ℝ) =
          fun z => fderiv ℝ φ z ((1 : ℝ), (0 : ℝ)) * Ψ z 0 +
            fderiv ℝ φ z ((0 : ℝ), (1 : ℝ)) * Ψ z 1 := by
        funext z
        rw [real_inner_comm, Cyl.gradT, Cyl.inner_vec,
          Cyl.partialQ_eq_fderiv hφ.differentiable, Cyl.partialEta_eq_fderiv hφ.differentiable]
        ring
      rw [he, integral_add ((hφ.dirDeriv _).integrableOn_mul hΨ0.continuous)
        ((hφ.dirDeriv _).integrableOn_mul hΨ1.continuous),
        Cyl.integral_fderiv_mul_test hc hφ hΨ0,
        Cyl.integral_fderiv_mul_test hc hφ hΨ1,
        ← neg_add, ← integral_add (hφ.integrableOn_mul (hΨ0.dirDeriv _).continuous)
          (hφ.integrableOn_mul (hΨ1.dirDeriv _).continuous)] at hgr
      have hmul : (fun z => φ z * fderiv ℝ (fun w => Ψ w 0) z ((1 : ℝ), (0 : ℝ)) +
          φ z * fderiv ℝ (fun w => Ψ w 1) z ((0 : ℝ), (1 : ℝ))) = fun z => φ z * d z := by
        funext z; rw [congrFun hd_eq z]; ring
      rw [hmul] at hgr
      exact neg_eq_zero.mp hgr
    have hd_mem : MemLp d 2 (Sob.cylinder c).μ := by
      rw [Cyl.cylinder_μ_eq c]
      exact F8WeakEx.memLp_cellμ_of_test ((F8WeakEx.isCylTest_sob_iff c d).1 hd_test)
    have hd_ae : d =ᵐ[cellμ c] 0 := by
      have hae := (Sob.cylinder c).ae_zero d (hd_mem.locallyIntegrable (by norm_num))
        fun φ hφ => by rw [Cyl.cylinder_μ_eq c]; exact horth_d φ hφ
      rwa [Cyl.cylinder_μ_eq c] at hae
    have hvec_eq : (fun z : Plane => d z • F8Ex.eR0) = 0 := by
      refine UnforcedLeray.Short.PartI.aePeriodicEq c hc
        (fun z => d z • F8Ex.eR0) 0
        (hd_test.continuous.smul continuous_const) continuous_const
        (fun z => ?_) (fun _ => rfl) ?_
      · have hz : (z.1 + c, z.2) = z + (c, 0) := by ext <;> simp
        dsimp only; rw [hz, hd_test.periodic z]
      · filter_upwards [hd_ae] with z hz
        simp only [hz, Pi.zero_apply, zero_smul]
    have hy := congrArg (fun v : F8Ex.RMerid => v 0) (congrFun hvec_eq y)
    simpa [d, F8Ex.eR0] using hy

/-! ## 5. Embedding `H1Sol c` into `TrainB.VecH1 c` and convective cancellation -/

lemma hasWeakDeriv_cylinder_of_hasWeakCellDerivR {c : ℝ} {j : Fin 2} {u g : L2v c}
    (hw : ∀ k : Fin 2, F8Ex.HasWeakCellDerivR c j (fun y => u y k) (fun y => g y k)) :
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (u : Plane → Vec2) (g : Plane → Vec2) where
  int_left φ hφ :=
    Sob.integrable_smul_of_memLp
      (Sob.CompactlyBounded.of_adm ((Sob.cylinder c).adm_iterDirDeriv hφ _))
      (by rw [TrainB.vecH1_measure_eq_cell c]; exact Lp.memLp u)
  int_right φ hφ :=
    Sob.integrable_smul_of_memLp (Sob.CompactlyBounded.of_adm hφ)
      (by rw [TrainB.vecH1_measure_eq_cell c]; exact Lp.memLp g)
  identity φ hφ := by
    have hφb : B0579.IsCylTest c φ := (F8WeakEx.isCylTest_sob_iff c φ).1 hφ
    have hdir : (Sob.cylinder c).dir j = B0579.dir j := by
      fin_cases j <;> rfl
    have hl : Integrable (fun x => Sob.iterDirDeriv [(Sob.cylinder c).dir j] φ x •
        (u : Plane → Vec2) x) (Sob.cylinder c).μ :=
      Sob.integrable_smul_of_memLp
        (Sob.CompactlyBounded.of_adm ((Sob.cylinder c).adm_iterDirDeriv hφ [(Sob.cylinder c).dir j]))
        (by rw [TrainB.vecH1_measure_eq_cell c]; exact Lp.memLp u)
    have hr : Integrable (fun x => φ x • (g : Plane → Vec2) x) (Sob.cylinder c).μ :=
      Sob.integrable_smul_of_memLp (Sob.CompactlyBounded.of_adm hφ)
        (by rw [TrainB.vecH1_measure_eq_cell c]; exact Lp.memLp g)
    ext k
    let pk := (EuclideanSpace.proj k : Vec2 →L[ℝ] ℝ)
    have eL := (pk.integral_comp_comm hl).symm
    have eR := (pk.integral_comp_comm hr).symm
    simp only [List.length_singleton, pow_one, neg_smul, one_smul, PiLp.neg_apply]
    change pk (∫ x, Sob.iterDirDeriv [(Sob.cylinder c).dir j] φ x • (u : Plane → Vec2) x
      ∂(Sob.cylinder c).μ) = -(pk (∫ x, φ x • (g : Plane → Vec2) x ∂(Sob.cylinder c).μ))
    let uk : Plane → ℝ := fun x => u x k
    let gk : Plane → ℝ := fun x => g x k
    have hL_eq : (fun x : Plane => pk (Sob.iterDirDeriv [(Sob.cylinder c).dir j] φ x •
        (u : Plane → Vec2) x)) = fun x => uk x * B0579.pd j φ x := by
      funext x
      rw [map_smul, smul_eq_mul, hdir]
      dsimp only [pk, uk, Sob.iterDirDeriv, List.foldr, B0579.pd]
      exact mul_comm _ _
    have hR_eq : (fun x : Plane => pk (φ x • (g : Plane → Vec2) x)) =
        fun x => gk x * φ x := by
      funext x
      rw [map_smul, smul_eq_mul]
      dsimp only [pk, gk]
      exact mul_comm _ _
    rw [eL, eR, hL_eq, hR_eq, Cyl.cylinder_μ_eq c]
    unfold cellμ
    rw [← F8WeakEx.b0579_cell_eq_cyl_cell]
    exact (hw k).2 φ hφb

def h1SolComponent {c : ℝ} (p : F8WeakEx.H1Sol c) (α : Sob.Idx 2 1) : L2v c :=
  if α = (Sob.Idx.zero : Sob.Idx 2 1) then
    F8WeakEx.val0CLM c p
  else if α = (Sob.Idx.cons 0 Sob.Idx.zero : Sob.Idx 2 1) then
    F8WeakEx.dqCLM c p
  else
    F8WeakEx.detaCLM c p

private lemma weightedToCell_of_toLp {c : ℝ} (u : L2v c)
    {F : Plane → Vec2}
    (hF : MemLp F 2 (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))))
    (hFae : (u : Plane → Vec2) =ᵐ[cellμ c] F) :
    TrainB.weightedToCellL2Isometry c (hF.toLp F) = u := by
  apply Lp.ext
  let hMP : MeasurePreserving id (cellμ c)
      (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) := by
    rw [← TrainB.vecH1_measure_eq_cell c]
    exact MeasurePreserving.id _
  have hcomp := Lp.coeFn_compMeasurePreserving (hF.toLp F) hMP
  have hFcell := hMP.quasiMeasurePreserving.ae hF.coeFn_toLp
  filter_upwards [hcomp, hFcell, hFae] with z hzComp hzF hzU
  calc
    ((Lp.compMeasurePreserving id hMP (hF.toLp F) : L2v c) : Plane → Vec2) z =
        (hF.toLp F : Lp Vec2 2 (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ)))) z := by
          simpa [Function.comp_id] using hzComp
    _ = F z := hzF
    _ = (u : Plane → Vec2) z := hzU.symm

private lemma exists_vecH1_of_h1Sol {c : ℝ} (p : F8WeakEx.H1Sol c) :
    ∃ y : TrainB.VecH1 c,
      TrainB.vecH1ValueCellCLM_MP y = F8WeakEx.val0CLM c p ∧
      TrainB.vecH1DqCellCLM_MP y = F8WeakEx.dqCLM c p ∧
      TrainB.vecH1DetaCellCLM_MP y = F8WeakEx.detaCLM c p := by
  let component : Sob.Idx 2 1 → L2v c := h1SolComponent p
  let g : Sob.Idx 2 1 → Plane → Vec2 := fun α z => (component α : Plane → Vec2) z
  have hmem : ∀ α, MemLp (g α) 2 (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) :=
    fun α => TrainB.memLp_cell_to_weighted (component α)
  have hcomponent0 : component Sob.Idx.zero = F8WeakEx.val0CLM c p := by
    simp [component, h1SolComponent]
  have hcomponentQ : component (Sob.Idx.cons 0 Sob.Idx.zero) = F8WeakEx.dqCLM c p := by
    simp only [component, h1SolComponent]
    have hne : (Sob.Idx.cons 0 Sob.Idx.zero : Sob.Idx 2 1) ≠ Sob.Idx.zero :=
      fun h => Cyl.idx_ne.1 h.symm
    simp [hne]
  have hcomponentEta : component (Sob.Idx.cons 1 Sob.Idx.zero) = F8WeakEx.detaCLM c p := by
    simp only [component, h1SolComponent]
    have hne0 : (Sob.Idx.cons 1 Sob.Idx.zero : Sob.Idx 2 1) ≠ Sob.Idx.zero :=
      fun h => Cyl.idx_ne.2.1 h.symm
    have hneq : (Sob.Idx.cons 1 Sob.Idx.zero : Sob.Idx 2 1) ≠ Sob.Idx.cons 0 Sob.Idx.zero :=
      fun h => Cyl.idx_ne.2.2 h.symm
    simp [hne0, hneq]
  have hweak : ∀ α : Sob.Idx 2 1,
      Sob.HasWeakDeriv (Sob.cylinder c) ((Sob.cylinder c).word α) (g Sob.Idx.zero) (g α) := by
    intro α
    have hcases : α = (Sob.Idx.zero : Sob.Idx 2 1) ∨ α = Cyl.iQ ∨ α = Cyl.iEta := by
      have hm : α ∈ (Finset.univ : Finset (Sob.Idx 2 1)) := Finset.mem_univ α
      rw [Cyl.univ_idx_two_one] at hm
      simpa [Cyl.iQ, Cyl.iEta] using hm
    rcases hcases with hzero | hq | heta
    · subst α
      rw [Cyl.word_zero]
      exact Sob.HasWeakDeriv.nil fun φ hφ =>
        Sob.integrable_smul_of_memLp (p := 2) (Sob.CompactlyBounded.of_adm hφ) (hmem Sob.Idx.zero)
    · subst α
      rw [Cyl.word_iQ]
      have hsource : g Sob.Idx.zero = (F8WeakEx.val0CLM c p : Plane → Vec2) :=
        funext fun z => congrFun (congrArg (fun u : L2v c => (u : Plane → Vec2)) hcomponent0) z
      have htarget : g Cyl.iQ = (F8WeakEx.dqCLM c p : Plane → Vec2) :=
        funext fun z => congrFun (congrArg (fun u : L2v c => (u : Plane → Vec2)) hcomponentQ) z
      exact (hasWeakDeriv_cylinder_of_hasWeakCellDerivR (F8WeakEx.H1Sol.weak_q p)).congr_ae
        (ae_of_all _ fun z => (congrFun hsource z).symm)
        (ae_of_all _ fun z => (congrFun htarget z).symm)
    · subst α
      rw [Cyl.word_iEta]
      have hsource : g Sob.Idx.zero = (F8WeakEx.val0CLM c p : Plane → Vec2) :=
        funext fun z => congrFun (congrArg (fun u : L2v c => (u : Plane → Vec2)) hcomponent0) z
      have htarget : g Cyl.iEta = (F8WeakEx.detaCLM c p : Plane → Vec2) :=
        funext fun z => congrFun (congrArg (fun u : L2v c => (u : Plane → Vec2)) hcomponentEta) z
      exact (hasWeakDeriv_cylinder_of_hasWeakCellDerivR (F8WeakEx.H1Sol.weak_eta p)).congr_ae
        (ae_of_all _ fun z => (congrFun hsource z).symm)
        (ae_of_all _ fun z => (congrFun htarget z).symm)
  let y : TrainB.VecH1 c := Sob.W.ofFields
    (D := Sob.cylinder c) (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Vec2)
    (k := 1) (p := 2) g hmem hweak
  have hzero : (F8WeakEx.val0CLM c p : Plane → Vec2) =ᵐ[cellμ c] g Sob.Idx.zero := by
    have heq := congrArg (fun u : L2v c => (u : Plane → Vec2)) hcomponent0.symm
    exact ae_of_all _ fun z => congrFun heq z
  have hq : (F8WeakEx.dqCLM c p : Plane → Vec2) =ᵐ[cellμ c] g (Sob.Idx.cons 0 Sob.Idx.zero) := by
    have heq := congrArg (fun u : L2v c => (u : Plane → Vec2)) hcomponentQ.symm
    exact ae_of_all _ fun z => congrFun heq z
  have heta : (F8WeakEx.detaCLM c p : Plane → Vec2) =ᵐ[cellμ c] g (Sob.Idx.cons 1 Sob.Idx.zero) := by
    have heq := congrArg (fun u : L2v c => (u : Plane → Vec2)) hcomponentEta.symm
    exact ae_of_all _ fun z => congrFun heq z
  refine ⟨y, ?_, ?_, ?_⟩
  · change TrainB.weightedToCellL2Isometry c
      (Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec2 1 2 y) = _
    rw [Sob.W.value_ofFields]
    exact weightedToCell_of_toLp _ (hmem Sob.Idx.zero) hzero
  · change TrainB.weightedToCellL2Isometry c
      (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec2 1 2
        (Sob.Idx.cons 0 Sob.Idx.zero) y) = _
    rw [Sob.W.deriv_ofFields]
    exact weightedToCell_of_toLp _ (hmem (Sob.Idx.cons 0 Sob.Idx.zero)) hq
  · change TrainB.weightedToCellL2Isometry c
      (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec2 1 2
        (Sob.Idx.cons 1 Sob.Idx.zero) y) = _
    rw [Sob.W.deriv_ofFields]
    exact weightedToCell_of_toLp _ (hmem (Sob.Idx.cons 1 Sob.Idx.zero)) heta

def h1SolToVecH1 {c : ℝ} (p : F8WeakEx.H1Sol c) : TrainB.VecH1 c :=
  (exists_vecH1_of_h1Sol p).choose

lemma vecH1Value_h1SolToVecH1 {c : ℝ} (p : F8WeakEx.H1Sol c) :
    TrainB.vecH1ValueCellCLM_MP (h1SolToVecH1 p) = F8WeakEx.val0CLM c p :=
  (exists_vecH1_of_h1Sol p).choose_spec.1

lemma vecH1Dq_h1SolToVecH1 {c : ℝ} (p : F8WeakEx.H1Sol c) :
    TrainB.vecH1DqCellCLM_MP (h1SolToVecH1 p) = F8WeakEx.dqCLM c p :=
  (exists_vecH1_of_h1Sol p).choose_spec.2.1

lemma vecH1Deta_h1SolToVecH1 {c : ℝ} (p : F8WeakEx.H1Sol c) :
    TrainB.vecH1DetaCellCLM_MP (h1SolToVecH1 p) = F8WeakEx.detaCLM c p :=
  (exists_vecH1_of_h1Sol p).choose_spec.2.2

private lemma inner_convective_smooth_eq_zero {c : ℝ} (hc : 0 < c)
    {V : ℝ → Plane → F8Ex.RMerid} (hV : F8Ex.IsSmoothBUCDrift c V)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 2) {u : Plane → Vec2} (hu : Sob.IsCylSmooth c u) :
    ∫ z in Cyl.cell c,
      ⟪u z, V r z 0 • Cyl.partialQ u z + V r z 1 • Cyl.partialEta u z⟫_ℝ = 0 := by
  have hVr_smooth : ContDiff ℝ ∞ (V r) := by
    have hc_on := hV.smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (s := univ) (fun z _ => ⟨hr, mem_univ z⟩)
    exact contDiffOn_univ.1 hc_on
  have hVr_coord : ∀ j : Fin 2, ContDiff ℝ ∞ (fun z => V r z j) := fun j =>
    (F8Ex.πR j).contDiff.comp hVr_smooth
  let ψ : Plane → ℝ := fun z => (1 / 2 : ℝ) * ⟪u z, u z⟫_ℝ
  have hψ_sm : ContDiff ℝ ∞ ψ :=
    contDiff_const.mul (hu.smooth.inner ℝ hu.smooth)
  let hF : Fin 2 → Plane → ℝ := fun j z => V r z j * ψ z
  have hhF_cyl : ∀ j : Fin 2, Sob.IsCylSmooth c (hF j) := by
    intro j
    obtain ⟨R, hR⟩ := hu.bounded
    refine ⟨(hVr_coord j).mul hψ_sm, fun z => ?_, ⟨R, fun z hz => ?_⟩⟩
    · have hz : z + (c, 0) = (z.1 + c, z.2) := by ext <;> simp
      have hpV := congrArg (fun v : F8Ex.RMerid => v j) (hV.periodic r hr z)
      dsimp only [hF, ψ]
      rw [hz, hpV, ← hz, hu.periodic z]
    · dsimp only [hF, ψ]
      rw [hR z hz, inner_zero_left, mul_zero, mul_zero]
  have hfderiv_hF : ∀ (j : Fin 2) (z : Plane),
      fderiv ℝ (hF j) z (B0579.dir j) =
        fderiv ℝ (fun y => V r y j) z (B0579.dir j) * ψ z +
          V r z j * ⟪u z, fderiv ℝ u z (B0579.dir j)⟫_ℝ := by
    intro j z
    have hdV : HasFDerivAt (fun y => V r y j) (fderiv ℝ (fun y => V r y j) z) z :=
      ((hVr_coord j).differentiable (by simp) z).hasFDerivAt
    have hdu : HasFDerivAt u (fderiv ℝ u z) z :=
      (hu.smooth.differentiable (by simp) z).hasFDerivAt
    have hdψ : HasFDerivAt ψ ((1 / 2 : ℝ) • ((fderivInnerCLM ℝ (u z, u z)).comp
        ((fderiv ℝ u z).prod (fderiv ℝ u z)))) z := by
      have hi := hdu.inner ℝ hdu
      exact hi.const_smul (1 / 2 : ℝ)
    have hmul := (hdV.mul hdψ).fderiv
    change fderiv ℝ ((fun y => V r y j) * ψ) z (B0579.dir j) = _
    rw [hmul]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      fderivInnerCLM_apply, smul_eq_mul]
    rw [real_inner_comm (fderiv ℝ u z (B0579.dir j)) (u z)]
    ring
  have hpoint : ∀ z : Plane,
      ⟪u z, V r z 0 • Cyl.partialQ u z + V r z 1 • Cyl.partialEta u z⟫_ℝ =
        fderiv ℝ (hF 0) z (B0579.dir 0) + fderiv ℝ (hF 1) z (B0579.dir 1) := by
    intro z
    have hdivV : fderiv ℝ (fun y => V r y 0) z (B0579.dir 0) +
        fderiv ℝ (fun y => V r y 1) z (B0579.dir 1) = 0 := by
      have hs := hV.solenoidal r hr z
      unfold Cyl.divergence at hs
      rwa [Cyl.partialQ_eq_fderiv ((hVr_coord 0).differentiable (by simp)),
        Cyl.partialEta_eq_fderiv ((hVr_coord 1).differentiable (by simp))] at hs
    have hdu : Differentiable ℝ u := hu.smooth.differentiable (by simp)
    rw [hfderiv_hF 0 z, hfderiv_hF 1 z, inner_add_right,
      real_inner_smul_right, real_inner_smul_right,
      Cyl.partialQ_eq_fderiv hdu z, Cyl.partialEta_eq_fderiv hdu z]
    calc V r z 0 * ⟪u z, fderiv ℝ u z ((1 : ℝ), (0 : ℝ))⟫_ℝ +
          V r z 1 * ⟪u z, fderiv ℝ u z ((0 : ℝ), (1 : ℝ))⟫_ℝ
        = (fderiv ℝ (fun y => V r y 0) z (B0579.dir 0) +
            fderiv ℝ (fun y => V r y 1) z (B0579.dir 1)) * ψ z +
          (V r z 0 * ⟪u z, fderiv ℝ u z (B0579.dir 0)⟫_ℝ +
            V r z 1 * ⟪u z, fderiv ℝ u z (B0579.dir 1)⟫_ℝ) := by
          rw [hdivV, zero_mul, zero_add]; rfl
      _ = _ := by ring
  simp_rw [hpoint]
  rw [Sob.cyl_cell_eq]
  have hi0 : IntegrableOn (fun z => fderiv ℝ (hF 0) z (B0579.dir 0)) (Sob.cylCell c) :=
    ((hhF_cyl 0).dir (B0579.dir 0)).integrableOn
  have hi1 : IntegrableOn (fun z => fderiv ℝ (hF 1) z (B0579.dir 1)) (Sob.cylCell c) :=
    ((hhF_cyl 1).dir (B0579.dir 1)).integrableOn
  rw [integral_add hi0 hi1,
    Sob.integral_cylCell_fderiv_eq_zero hc (hhF_cyl 0) (B0579.dir 0),
    Sob.integral_cylCell_fderiv_eq_zero hc (hhF_cyl 1) (B0579.dir 1), add_zero]

set_option maxHeartbeats 3200000 in
private lemma abs_inner_bvCLM_le {c : ℝ} (hc : 0 < c)
    {V : ℝ → Plane → F8Ex.RMerid} (hV : F8Ex.IsSmoothBUCDrift c V)
    {M1 : ℝ} (hM1_nn : 0 ≤ M1)
    (hM1 : ∀ s ∈ Icc (0 : ℝ) 2, ∀ y : Plane, ‖iteratedFDeriv ℝ 1 (V s) y‖ ≤ M1)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 2) (p : F8WeakEx.H1Sol c) :
    |⟪F8WeakEx.val0CLM c p, F8WeakEx.bvCLM hc hV r p⟫_ℝ| ≤
      2 * M1 * ‖F8WeakEx.val0CLM c p‖ ^ 2 := by
  obtain ⟨M0, hM0_nn, hM0⟩ := hV.deriv_bound 0
  have hVr_cont : ∀ j : Fin 2, Continuous (fun y : Plane => V r y j) := by
    intro j
    exact (F8Ex.πR j).continuous.comp
      (hV.smooth.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
        fun y => ⟨hr, mem_univ y⟩)
  have hVr_bdd : ∀ (j : Fin 2) (y : Plane), |V r y j| ≤ M0 := by
    intro j y
    calc |V r y j| = ‖V r y j‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖V r y‖ := PiLp.norm_apply_le _ j
      _ = ‖iteratedFDeriv ℝ 0 (V r) y‖ := norm_iteratedFDeriv_zero.symm
      _ ≤ M0 := hM0 r hr y
  let MV0 : L2v c →L[ℝ] L2v c :=
    F8WeakEx.scalarMultCLM (fun y => V r y 0) (hVr_cont 0) hM0_nn (hVr_bdd 0)
  let MV1 : L2v c →L[ℝ] L2v c :=
    F8WeakEx.scalarMultCLM (fun y => V r y 1) (hVr_cont 1) hM0_nn (hVr_bdd 1)
  have hconv_zero : ⟪F8WeakEx.val0CLM c p,
      MV0 (F8WeakEx.dqCLM c p) + MV1 (F8WeakEx.detaCLM c p)⟫_ℝ = 0 := by
    let Q : TrainB.VecH1 c → ℝ := fun z =>
      ⟪TrainB.vecH1ValueCellCLM_MP z,
        MV0 (TrainB.vecH1DqCellCLM_MP z) + MV1 (TrainB.vecH1DetaCellCLM_MP z)⟫_ℝ
    have hQ_cont : Continuous Q :=
      TrainB.vecH1ValueCellCLM_MP.continuous.inner
        ((MV0.continuous.comp TrainB.vecH1DqCellCLM_MP.continuous).add
          (MV1.continuous.comp TrainB.vecH1DetaCellCLM_MP.continuous))
    obtain ⟨yseq, fseq, hfseq, hyseq, hlim⟩ :=
      TrainB.exists_smoothVecH1_sequence hc (h1SolToVecH1 p)
    have hQ_seq : ∀ n : ℕ, Q (yseq n) = 0 := by
      intro n
      rw [hyseq n]
      let xn := Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
        (𝕜 := ℝ) (F := Vec2) (k := 1) (p := 2) hc (fseq n) (hfseq n)
      change ⟪TrainB.vecH1ValueCellCLM_MP xn,
        MV0 (TrainB.vecH1DqCellCLM_MP xn) + MV1 (TrainB.vecH1DetaCellCLM_MP xn)⟫_ℝ = 0
      rw [L2.inner_def]
      have hv := TrainB.vecH1ValueCellCLM_MP_ofCylSmooth_ae hc (hfseq n)
      have hq := TrainB.vecH1DqCellCLM_MP_ofCylSmooth_ae hc (hfseq n)
      have he := TrainB.vecH1DetaCellCLM_MP_ofCylSmooth_ae hc (hfseq n)
      have hm0 := F8WeakEx.coeFn_scalarMultCLM (hVr_cont 0) hM0_nn (hVr_bdd 0)
        (TrainB.vecH1DqCellCLM_MP xn)
      have hm1 := F8WeakEx.coeFn_scalarMultCLM (hVr_cont 1) hM0_nn (hVr_bdd 1)
        (TrainB.vecH1DetaCellCLM_MP xn)
      have hadd := Lp.coeFn_add (MV0 (TrainB.vecH1DqCellCLM_MP xn))
        (MV1 (TrainB.vecH1DetaCellCLM_MP xn))
      have hint_eq : (∫ z : Plane, ⟪(TrainB.vecH1ValueCellCLM_MP xn : Plane → Vec2) z,
          ((MV0 (TrainB.vecH1DqCellCLM_MP xn) + MV1 (TrainB.vecH1DetaCellCLM_MP xn) : L2v c) :
            Plane → Vec2) z⟫_ℝ ∂(cellμ c)) =
          ∫ z in Cyl.cell c, ⟪fseq n z,
            V r z 0 • Cyl.partialQ (fseq n) z + V r z 1 • Cyl.partialEta (fseq n) z⟫_ℝ := by
        unfold cellμ
        refine integral_congr_ae ?_
        filter_upwards [hv, hq, he, hm0, hm1, hadd] with z az aq ae am0 am1 aadd
        change ⟪(TrainB.vecH1ValueCellCLM_MP xn : Plane → Vec2) z,
          ((MV0 (TrainB.vecH1DqCellCLM_MP xn) + MV1 (TrainB.vecH1DetaCellCLM_MP xn) : L2v c) :
            Plane → Vec2) z⟫_ℝ = _
        rw [az, aadd, Pi.add_apply, am0, am1, aq, ae]
      rw [hint_eq]
      exact inner_convective_smooth_eq_zero hc hV hr (hfseq n)
    have hQ_lim : Tendsto (fun n => Q (yseq n)) atTop (𝓝 (Q (h1SolToVecH1 p))) :=
      (hQ_cont.tendsto _).comp hlim
    have hQx : Q (h1SolToVecH1 p) = 0 :=
      tendsto_nhds_unique hQ_lim (by simp_rw [hQ_seq]; exact tendsto_const_nhds)
    simpa only [Q, vecH1Value_h1SolToVecH1, vecH1Dq_h1SolToVecH1, vecH1Deta_h1SolToVecH1] using hQx
  let stretch : L2v c := F8WeakEx.bvCLM hc hV r p -
    (MV0 (F8WeakEx.dqCLM c p) + MV1 (F8WeakEx.detaCLM c p))
  have hinner_eq : ⟪F8WeakEx.val0CLM c p, F8WeakEx.bvCLM hc hV r p⟫_ℝ =
      ⟪F8WeakEx.val0CLM c p, stretch⟫_ℝ := by
    dsimp only [stretch]
    rw [inner_sub_right, hconv_zero, sub_zero]
  have hVs : ContDiff ℝ ∞ (V r) := by
    have hc_on := hV.smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (s := univ) (fun z _ => ⟨hr, mem_univ z⟩)
    exact contDiffOn_univ.1 hc_on
  have hdV_bdd : ∀ (j i : Fin 2) (y : Plane),
      |fderiv ℝ (fun z => V r z i) y (B0579.dir j)| ≤ M1 := by
    intro j i y
    have hproj : fderiv ℝ (fun z => V r z i) y (B0579.dir j) =
        fderiv ℝ (V r) y (B0579.dir j) i := by
      have hc := ((F8Ex.πR i).hasFDerivAt.comp y
        (hVs.contDiffAt.differentiableAt (by simp)).hasFDerivAt).fderiv
      change fderiv ℝ ((F8Ex.πR i) ∘ (V r)) y (B0579.dir j) =
        F8Ex.πR i (fderiv ℝ (V r) y (B0579.dir j))
      rw [hc, ContinuousLinearMap.comp_apply]
    have hdir_norm : ‖B0579.dir j‖ = 1 := by fin_cases j <;> simp [B0579.dir]
    rw [hproj]
    calc |fderiv ℝ (V r) y (B0579.dir j) i|
        = ‖fderiv ℝ (V r) y (B0579.dir j) i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ (V r) y (B0579.dir j)‖ := PiLp.norm_apply_le _ i
      _ = ‖iteratedFDeriv ℝ 1 (V r) y ![B0579.dir j]‖ := by
          rw [iteratedFDeriv_one_apply, Matrix.cons_val_zero]
      _ ≤ ‖iteratedFDeriv ℝ 1 (V r) y‖ *
            ∏ l : Fin 1, ‖(![B0579.dir j] : Fin 1 → Plane) l‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖iteratedFDeriv ℝ 1 (V r) y‖ := by simp [hdir_norm]
      _ ≤ M1 := hM1 r hr y
  let w : L2v c := F8WeakEx.val0CLM c p
  have hbv_ae : (F8WeakEx.bvCLM hc hV r p : Plane → Vec2) =ᵐ[cellμ c]
      F8Ex.realBvSlice (V r) (w : Plane → F8Ex.RMerid)
        (F8WeakEx.dqCLM c p : Plane → F8Ex.RMerid)
        (F8WeakEx.detaCLM c p : Plane → F8Ex.RMerid) := by
    have h := F8WeakEx.bvCLM_ae_realBvSlice hc hV hr p
    rwa [F8WeakEx.cellMeas_eq_cellμ] at h
  have hstretch_ae : ∀ᵐ y ∂(cellμ c),
      ‖⟪(w : Plane → Vec2) y, (stretch : Plane → Vec2) y⟫_ℝ‖ ≤
        2 * M1 * ⟪(w : Plane → Vec2) y, (w : Plane → Vec2) y⟫_ℝ := by
    have hm0 := F8WeakEx.coeFn_scalarMultCLM (hVr_cont 0) hM0_nn (hVr_bdd 0) (F8WeakEx.dqCLM c p)
    have hm1 := F8WeakEx.coeFn_scalarMultCLM (hVr_cont 1) hM0_nn (hVr_bdd 1) (F8WeakEx.detaCLM c p)
    have hadd := Lp.coeFn_add (MV0 (F8WeakEx.dqCLM c p)) (MV1 (F8WeakEx.detaCLM c p))
    have hsub := Lp.coeFn_sub (F8WeakEx.bvCLM hc hV r p)
      (MV0 (F8WeakEx.dqCLM c p) + MV1 (F8WeakEx.detaCLM c p))
    filter_upwards [hbv_ae, hm0, hm1, hadd, hsub] with y abv am0 am1 aadd asub
    have hst_vec : (stretch : Plane → Vec2) y =
        F8Ex.realBvSlice (V r) (w : Plane → F8Ex.RMerid)
          (F8WeakEx.dqCLM c p : Plane → F8Ex.RMerid)
          (F8WeakEx.detaCLM c p : Plane → F8Ex.RMerid) y -
        ((V r y).ofLp 0 • (F8WeakEx.dqCLM c p : Plane → Vec2) y +
          (V r y).ofLp 1 • (F8WeakEx.detaCLM c p : Plane → Vec2) y) := by
      dsimp only [stretch]
      rw [asub, Pi.sub_apply, abv, aadd, Pi.add_apply]
      dsimp only [MV0, MV1]
      rw [am0, am1]
    have hst_coord : ∀ i : Fin 2, ((stretch : Plane → Vec2) y).ofLp i =
        ((w : Plane → Vec2) y).ofLp 0 * fderiv ℝ (fun z => (V r z).ofLp i) y ((1 : ℝ), (0 : ℝ)) +
          ((w : Plane → Vec2) y).ofLp 1 * fderiv ℝ (fun z => (V r z).ofLp i) y ((0 : ℝ), (1 : ℝ)) := by
      intro i
      rw [hst_vec]
      simp only [F8Ex.realBvSlice, WithLp.ofLp_sub, WithLp.ofLp_add, WithLp.ofLp_smul,
        Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [Real.norm_eq_abs, PiLp.inner_apply, PiLp.inner_apply, Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [RCLike.inner_apply, conj_trivial]
    rw [hst_coord 0, hst_coord 1]
    have b00 := hdV_bdd 0 0 y
    have b10 := hdV_bdd 1 0 y
    have b01 := hdV_bdd 0 1 y
    have b11 := hdV_bdd 1 1 y
    dsimp only [B0579.dir] at b00 b10 b01 b11
    set w0 := ((w : Plane → Vec2) y).ofLp (0 : Fin 2)
    set w1 := ((w : Plane → Vec2) y).ofLp (1 : Fin 2)
    set a00 := fderiv ℝ (fun z => (V r z).ofLp (0 : Fin 2)) y ((1 : ℝ), (0 : ℝ))
    set a10 := fderiv ℝ (fun z => (V r z).ofLp (0 : Fin 2)) y ((0 : ℝ), (1 : ℝ))
    set a01 := fderiv ℝ (fun z => (V r z).ofLp (1 : Fin 2)) y ((1 : ℝ), (0 : ℝ))
    set a11 := fderiv ℝ (fun z => (V r z).ofLp (1 : Fin 2)) y ((0 : ℝ), (1 : ℝ))
    have ht1 : |w0 * a00 + w1 * a10| ≤ M1 * (|w0| + |w1|) := by
      calc |w0 * a00 + w1 * a10|
          ≤ |w0 * a00| + |w1 * a10| := abs_add_le _ _
        _ = |w0| * |a00| + |w1| * |a10| := by rw [abs_mul, abs_mul]
        _ ≤ |w0| * M1 + |w1| * M1 :=
            add_le_add (mul_le_mul_of_nonneg_left b00 (abs_nonneg _))
              (mul_le_mul_of_nonneg_left b10 (abs_nonneg _))
        _ = M1 * (|w0| + |w1|) := by ring
    have ht2 : |w0 * a01 + w1 * a11| ≤ M1 * (|w0| + |w1|) := by
      calc |w0 * a01 + w1 * a11|
          ≤ |w0 * a01| + |w1 * a11| := abs_add_le _ _
        _ = |w0| * |a01| + |w1| * |a11| := by rw [abs_mul, abs_mul]
        _ ≤ |w0| * M1 + |w1| * M1 :=
            add_le_add (mul_le_mul_of_nonneg_left b01 (abs_nonneg _))
              (mul_le_mul_of_nonneg_left b11 (abs_nonneg _))
        _ = M1 * (|w0| + |w1|) := by ring
    calc |(w0 * a00 + w1 * a10) * w0 + (w0 * a01 + w1 * a11) * w1|
        ≤ |(w0 * a00 + w1 * a10) * w0| + |(w0 * a01 + w1 * a11) * w1| := abs_add_le _ _
      _ = |w0 * a00 + w1 * a10| * |w0| + |w0 * a01 + w1 * a11| * |w1| := by
          rw [abs_mul, abs_mul]
      _ ≤ M1 * (|w0| + |w1|) * |w0| + M1 * (|w0| + |w1|) * |w1| :=
          add_le_add (mul_le_mul_of_nonneg_right ht1 (abs_nonneg _))
            (mul_le_mul_of_nonneg_right ht2 (abs_nonneg _))
      _ = M1 * (|w0| + |w1|) ^ 2 := by ring
      _ ≤ M1 * (2 * (w0 * w0 + w1 * w1)) := by
          refine mul_le_mul_of_nonneg_left ?_ hM1_nn
          have hsq0 : |w0| ^ 2 = w0 * w0 := by rw [sq_abs, sq]
          have hsq1 : |w1| ^ 2 = w1 * w1 := by rw [sq_abs, sq]
          nlinarith [sq_nonneg (|w0| - |w1|)]
      _ = 2 * M1 * (w0 * w0 + w1 * w1) := by ring
  rw [hinner_eq, L2.inner_def, ← Real.norm_eq_abs]
  have hint_ws : Integrable (fun y => ⟪(w : Plane → Vec2) y, (stretch : Plane → Vec2) y⟫_ℝ)
      (cellμ c) := L2.integrable_inner (𝕜 := ℝ) w stretch
  have hint_ww : Integrable (fun y => ⟪(w : Plane → Vec2) y, (w : Plane → Vec2) y⟫_ℝ) (cellμ c) :=
    L2.integrable_inner (𝕜 := ℝ) w w
  calc ‖∫ y, ⟪(w : Plane → Vec2) y, (stretch : Plane → Vec2) y⟫_ℝ ∂(cellμ c)‖
      ≤ ∫ y, ‖⟪(w : Plane → Vec2) y, (stretch : Plane → Vec2) y⟫_ℝ‖ ∂(cellμ c) :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ y, 2 * M1 * ⟪(w : Plane → Vec2) y, (w : Plane → Vec2) y⟫_ℝ ∂(cellμ c) :=
        integral_mono_ae hint_ws.norm (hint_ww.const_mul (2 * M1)) hstretch_ae
    _ = 2 * M1 * ∫ y, ⟪(w : Plane → Vec2) y, (w : Plane → Vec2) y⟫_ℝ ∂(cellμ c) :=
        integral_const_mul _ _
    _ = 2 * M1 * ‖w‖ ^ 2 := by rw [← L2.inner_def, real_inner_self_eq_norm_sq]

/-! ## 6. Mollified ODE, energy dissipation inequality, Gronwall, and weak-mild uniqueness -/

private lemma gronwall_nonneg_continuousOn {g : ℝ → ℝ} (hg_cont : ContinuousOn g (Icc (0 : ℝ) 2))
    (hg_nn : ∀ t ∈ Icc (0 : ℝ) 2, 0 ≤ g t)
    {C : ℝ} (hC : 0 < C)
    (hg_ineq : ∀ t ∈ Icc (0 : ℝ) 2, g t ≤ C * ∫ r in (0 : ℝ)..t, g r) :
    ∀ t ∈ Icc (0 : ℝ) 2, g t = 0 := by
  let cl : ℝ → ℝ := fun r => (Set.projIcc (0 : ℝ) 2 (by norm_num) r : ℝ)
  have hcl_cont : Continuous cl := continuous_subtype_val.comp continuous_projIcc
  have hcl_mem : ∀ r : ℝ, cl r ∈ Icc (0 : ℝ) 2 :=
    fun r => (Set.projIcc (0 : ℝ) 2 (by norm_num) r).2
  have hcl_eq : ∀ r ∈ Icc (0 : ℝ) 2, cl r = r :=
    fun r hr => by simp [cl, Set.projIcc_of_mem _ hr]
  let G : ℝ → ℝ := fun r => g (cl r)
  have hG_cont : Continuous G := hg_cont.comp_continuous hcl_cont hcl_mem
  let I : ℝ → ℝ := fun t => ∫ r in (0 : ℝ)..t, G r
  have hI_deriv : ∀ t : ℝ, HasDerivAt I (G t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hG_cont.intervalIntegrable 0 t)
      (hG_cont.stronglyMeasurableAtFilter volume (𝓝 t)) hG_cont.continuousAt
  let E : ℝ → ℝ := fun t => Real.exp (-C * t) * I t
  have hE_deriv : ∀ t : ℝ, HasDerivAt E
      (Real.exp (-C * t) * (G t - C * I t)) t := by
    intro t
    have hexp : HasDerivAt (fun s => Real.exp (-C * s)) (Real.exp (-C * t) * (-C)) t := by
      simpa [mul_comm] using ((hasDerivAt_id t).const_mul (-C)).exp
    have hm : HasDerivAt E (Real.exp (-C * t) * (-C) * I t + Real.exp (-C * t) * G t) t :=
      (hexp.mul (hI_deriv t)).congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)
    convert hm using 1
    ring
  have hE_diff : Differentiable ℝ E := fun t => (hE_deriv t).differentiableAt
  have hE_anti : AntitoneOn E (Icc (0 : ℝ) 2) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc (0 : ℝ) 2)
      hE_diff.continuous.continuousOn hE_diff.differentiableOn fun t ht_int => ?_
    have ht : t ∈ Icc (0 : ℝ) 2 := interior_subset ht_int
    rw [(hE_deriv t).deriv]
    have hGt : G t = g t := congrArg g (hcl_eq t ht)
    have hIt : I t = ∫ r in (0 : ℝ)..t, g r := by
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le ht.1] at hr
      exact congrArg g (hcl_eq r ⟨hr.1, hr.2.trans ht.2⟩)
    rw [hGt, hIt]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.mpr (hg_ineq t ht))
  intro t ht
  have hE0 : E 0 = 0 := by simp [E, I]
  have hEt_le : E t ≤ 0 := hE0 ▸ hE_anti ⟨le_rfl, by norm_num⟩ ht ht.1
  have hIt_le : I t ≤ 0 := nonpos_of_mul_nonpos_right hEt_le (Real.exp_pos _)
  have hIt_eq : I t = ∫ r in (0 : ℝ)..t, g r := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le ht.1] at hr
    exact congrArg g (hcl_eq r ⟨hr.1, hr.2.trans ht.2⟩)
  rw [hIt_eq] at hIt_le
  have hgt_le : g t ≤ 0 := (hg_ineq t ht).trans (mul_nonpos_of_nonneg_of_nonpos hC.le hIt_le)
  exact le_antisymm hgt_le (hg_nn t ht)

set_option maxHeartbeats 6400000 in
theorem weakH1_lift_eq_mild {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    {V : ℝ → Plane → F8Ex.RMerid} (hV : F8Ex.IsSmoothBUCDrift c V)
    {W Wq Wη : ℝ → Plane → F8Ex.RMerid} {u uq uη : Plane → F8Ex.RMerid}
    (hdat : F8Ex.IsRealCylH1Datum c u uq uη)
    (hwk : F8Ex.IsRealWeakH1OseenSol c ν V W Wq Wη u uq uη) :
    ∀ (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 2),
      F8WeakEx.H1Sol.ofRealDatum (hwk.slice_h1 s hs) =
        F8WeakEx.E_oseen hc hν hV s 0 (F8WeakEx.H1Sol.ofRealDatum hdat) := by
  let u₀ := F8WeakEx.H1Sol.ofRealDatum hdat
  let U : ℝ → F8WeakEx.H1Sol c := fun s => F8WeakEx.E_oseen hc hν hV s 0 u₀
  have hU_cont : ContinuousOn U (Icc (0 : ℝ) 2) :=
    F8WeakEx.continuousOn_E_oseen hc hν hV ⟨le_rfl, by norm_num⟩ u₀
  obtain ⟨hwk_mild, hae_mild⟩ := F8WeakEx.exists_mild_weakH1OseenSol hc hν hV hdat
  have hlift_mild : ∀ s ∈ Icc (0 : ℝ) 2, liftWeakSol hwk_mild s = U s := by
    intro s hs
    apply F8WeakEx.H1Sol.ext_val0 hc
    apply Lp.ext
    have h1 := (liftWeakSol_ae hwk_mild hs).1
    have h2 := (hae_mild s hs).1
    have h12 : (F8WeakEx.val0CLM c (liftWeakSol hwk_mild s) : Plane → F8Ex.RMerid) =ᵐ[cellμ c]
        (F8WeakEx.val0CLM c (U s) : Plane → F8Ex.RMerid) := by
      rw [show ae (cellμ c) = ae (F8Ex.cellMeas c) from
        congr_arg ae (F8WeakEx.cellMeas_eq_cellμ c).symm]
      exact h1.trans h2
    exact h12
  let δU : ℝ → F8WeakEx.H1Sol c := fun s => liftWeakSol hwk s - U s
  have hδU_cont : ContinuousOn δU (Icc (0 : ℝ) 2) :=
    (continuousOn_liftWeakSol hwk).sub hU_cont
  have hδU_zero : δU 0 = 0 := by
    dsimp only [δU, U]
    rw [liftWeakSol_zero hc hdat hwk, F8WeakEx.E_oseen_self hc hν hV 0]
    simp [u₀]
  let b : ℝ → L2v c := fun r => F8WeakEx.bvCLM hc hV r (δU r)
  have hb_cont : ContinuousOn b (Icc (0 : ℝ) 2) := continuousOn_bv_comp hc hV hδU_cont
  -- Difference weak equation on `L2v c`
  have hdiff_weak : ∀ {Φ : Plane → F8Ex.RMerid} (hΦ : F8Ex.IsRealSolCylTest c Φ)
      {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2),
      let hsm := F8WeakEx.isCylSmooth_of_solTest hΦ
      let φ₀ := F8WeakEx.cylSmoothToL2 hsm
      let φq := F8WeakEx.cylSmoothToL2 (hsm.dir (B0579.dir 0))
      let φη := F8WeakEx.cylSmoothToL2 (hsm.dir (B0579.dir 1))
      ⟪φ₀, F8WeakEx.val0CLM c (δU t)⟫_ℝ +
        ∫ r in (0 : ℝ)..t,
          (ν * (⟪φq, F8WeakEx.dqCLM c (δU r)⟫_ℝ + ⟪φη, F8WeakEx.detaCLM c (δU r)⟫_ℝ) +
            ⟪φ₀, b r⟫_ℝ) = 0 := by
    intro Φ hΦ t ht hsm φ₀ φq φη
    have hw1 := weak_eq_liftWeakSol hc hV hdat hwk hΦ ht
    have hw2 := weak_eq_liftWeakSol hc hV hdat hwk_mild hΦ ht
    dsimp only at hw1 hw2
    rw [hlift_mild t ht] at hw2
    have hsub_head : ⟪φ₀, F8WeakEx.val0CLM c (δU t)⟫_ℝ =
        ⟪φ₀, F8WeakEx.val0CLM c (liftWeakSol hwk t) - F8WeakEx.val0CLM c u₀⟫_ℝ -
          ⟪φ₀, F8WeakEx.val0CLM c (U t) - F8WeakEx.val0CLM c u₀⟫_ℝ := by
      dsimp only [δU, u₀]
      rw [map_sub, ← inner_sub_right]
      congr 1; abel
    have hU1_cont := continuousOn_liftWeakSol hwk
    have hb1_cont := continuousOn_bv_comp hc hV hU1_cont
    have hb2_cont := continuousOn_bv_comp hc hV hU_cont
    have hi1 : IntervalIntegrable (fun r =>
        ν * (⟪φq, F8WeakEx.dqCLM c (liftWeakSol hwk r)⟫_ℝ +
          ⟪φη, F8WeakEx.detaCLM c (liftWeakSol hwk r)⟫_ℝ) +
        ⟪φ₀, F8WeakEx.bvCLM hc hV r (liftWeakSol hwk r)⟫_ℝ) volume 0 t := by
      refine (((continuousOn_const.mul
        ((continuous_const.continuousOn.inner
            ((F8WeakEx.dqCLM c).continuous.comp_continuousOn hU1_cont)).add
          (continuous_const.continuousOn.inner
            ((F8WeakEx.detaCLM c).continuous.comp_continuousOn hU1_cont)))).add
        (continuous_const.continuousOn.inner hb1_cont)).mono
        (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
    have hi2 : IntervalIntegrable (fun r =>
        ν * (⟪φq, F8WeakEx.dqCLM c (U r)⟫_ℝ + ⟪φη, F8WeakEx.detaCLM c (U r)⟫_ℝ) +
        ⟪φ₀, F8WeakEx.bvCLM hc hV r (U r)⟫_ℝ) volume 0 t := by
      refine (((continuousOn_const.mul
        ((continuous_const.continuousOn.inner
            ((F8WeakEx.dqCLM c).continuous.comp_continuousOn hU_cont)).add
          (continuous_const.continuousOn.inner
            ((F8WeakEx.detaCLM c).continuous.comp_continuousOn hU_cont)))).add
        (continuous_const.continuousOn.inner hb2_cont)).mono
        (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
    have hint_sub : (∫ r in (0 : ℝ)..t,
        (ν * (⟪φq, F8WeakEx.dqCLM c (δU r)⟫_ℝ + ⟪φη, F8WeakEx.detaCLM c (δU r)⟫_ℝ) +
          ⟪φ₀, b r⟫_ℝ)) =
        (∫ r in (0 : ℝ)..t,
          (ν * (⟪φq, F8WeakEx.dqCLM c (liftWeakSol hwk r)⟫_ℝ +
            ⟪φη, F8WeakEx.detaCLM c (liftWeakSol hwk r)⟫_ℝ) +
          ⟪φ₀, F8WeakEx.bvCLM hc hV r (liftWeakSol hwk r)⟫_ℝ)) -
        (∫ r in (0 : ℝ)..t,
          (ν * (⟪φq, F8WeakEx.dqCLM c (U r)⟫_ℝ + ⟪φη, F8WeakEx.detaCLM c (U r)⟫_ℝ) +
          ⟪φ₀, F8WeakEx.bvCLM hc hV r (U r)⟫_ℝ)) := by
      rw [← intervalIntegral.integral_sub hi1 hi2]
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le ht.1] at hr
      have hr2 : r ∈ Icc (0 : ℝ) 2 := ⟨hr.1, hr.2.trans ht.2⟩
      dsimp only [δU, b]
      have hr_lift := hlift_mild r hr2
      simp only [← hr_lift, map_sub, inner_sub_right]
      ring
    have hw2' : ⟪φ₀, F8WeakEx.val0CLM c (U t) - F8WeakEx.val0CLM c u₀⟫_ℝ +
        ∫ r in (0 : ℝ)..t,
          (ν * (⟪φq, F8WeakEx.dqCLM c (U r)⟫_ℝ + ⟪φη, F8WeakEx.detaCLM c (U r)⟫_ℝ) +
            ⟪φ₀, F8WeakEx.bvCLM hc hV r (U r)⟫_ℝ) = 0 := by
      refine Eq.trans ?_ hw2
      congr 1
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le ht.1] at hr
      rw [hlift_mild r ⟨hr.1, hr.2.trans ht.2⟩]
    linarith [hsub_head, hint_sub, hw1, hw2']
  -- Mollified ODE & energy dissipation inequality for each `k : ℕ`
  have hmoll_energy : ∀ (k : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2),
      ‖mollCLM hc k (F8WeakEx.val0CLM c (δU t))‖ ^ 2 ≤
        -2 * ∫ r in (0 : ℝ)..t,
          ⟪mollCLM hc k (F8WeakEx.val0CLM c (δU r)), mollCLM hc k (b r)⟫_ℝ := by
    intro k t ht
    let uk : ℝ → L2v c := fun r => mollCLM hc k (F8WeakEx.val0CLM c (δU r))
    let Fk : ℝ → L2v c := fun r =>
      P0 c (ν • (dmollCLM hc 0 k (F8WeakEx.dqCLM c (δU r)) +
        dmollCLM hc 1 k (F8WeakEx.detaCLM c (δU r))) - mollCLM hc k (b r))
    have hFk_cont : ContinuousOn Fk (Icc (0 : ℝ) 2) := by
      dsimp only [Fk]
      have hd0 : ContinuousOn (fun r => dmollCLM hc 0 k (F8WeakEx.dqCLM c (δU r))) (Icc (0 : ℝ) 2) :=
        (dmollCLM hc 0 k).continuous.comp_continuousOn
          ((F8WeakEx.dqCLM c).continuous.comp_continuousOn hδU_cont)
      have hd1 : ContinuousOn (fun r => dmollCLM hc 1 k (F8WeakEx.detaCLM c (δU r))) (Icc (0 : ℝ) 2) :=
        (dmollCLM hc 1 k).continuous.comp_continuousOn
          ((F8WeakEx.detaCLM c).continuous.comp_continuousOn hδU_cont)
      have hmb : ContinuousOn (fun r => mollCLM hc k (b r)) (Icc (0 : ℝ) 2) :=
        (mollCLM hc k).continuous.comp_continuousOn hb_cont
      exact ((P0 c).continuous.comp_continuousOn (((hd0.add hd1).const_smul ν).sub hmb)).congr
        fun _ _ => rfl
    have huk_integral : ∀ s ∈ Icc (0 : ℝ) 2, uk s = ∫ r in (0 : ℝ)..s, Fk r := by
      intro s hs
      have huk_df : uk s ∈ divFree c := by
        dsimp only [uk]
        have hp0 : P0 c (F8WeakEx.val0CLM c (δU s)) = F8WeakEx.val0CLM c (δU s) :=
          Cyl.P0_eq_self (F8WeakEx.H1Sol.mem_divFree (δU s))
        rw [← hp0, mollCLM_P0_comm hc k]
        exact Cyl.P0_mem _
      have hint_Fk : IntervalIntegrable Fk volume 0 s :=
        (hFk_cont.mono (Icc_subset_Icc_right hs.2)).intervalIntegrable_of_Icc hs.1
      have hInt_df : (∫ r in (0 : ℝ)..s, Fk r) ∈ divFree c := by
        let fP0 : ℝ → divFree c := fun r =>
          ⟨Fk r, by dsimp only [Fk]; exact Cyl.P0_mem _⟩
        have hfP0_cont : ContinuousOn fP0 (Icc (0 : ℝ) 2) :=
          Topology.IsInducing.subtypeVal.continuousOn_iff.mpr hFk_cont
        have hiP0 : IntervalIntegrable fP0 volume 0 s :=
          (hfP0_cont.mono (Icc_subset_Icc_right hs.2)).intervalIntegrable_of_Icc hs.1
        have hsubL := (divFree c).subtypeL.intervalIntegral_comp_comm hiP0
        change (∫ r in (0 : ℝ)..s, (divFree c).subtypeL (fP0 r)) ∈ divFree c
        rw [hsubL]
        exact Submodule.coe_mem _
      apply sub_eq_zero.mp
      refine eq_zero_of_divFree_and_ortho_solTest hc (uk s - ∫ r in (0 : ℝ)..s, Fk r)
        (Submodule.sub_mem _ huk_df hInt_df) fun Φ hΦ => ?_
      let hsm := F8WeakEx.isCylSmooth_of_solTest hΦ
      let φ₀ := F8WeakEx.cylSmoothToL2 hsm
      let φq := F8WeakEx.cylSmoothToL2 (hsm.dir (B0579.dir 0))
      let φη := F8WeakEx.cylSmoothToL2 (hsm.dir (B0579.dir 1))
      have hP0_φ₀ : P0 c φ₀ = φ₀ :=
        Cyl.P0_eq_self (F8WeakEx.cylSmoothToL2_mem_divFree_of_solTest hc hΦ)
      have hΨ_sol := isRealSolCylTest_convSolTest hc k hΦ
      have hw_conv := hdiff_weak hΨ_sol hs
      dsimp only at hw_conv
      have hsm_eq : F8WeakEx.cylSmoothToL2 (F8WeakEx.isCylSmooth_of_solTest hΨ_sol) =
          F8WeakEx.cylSmoothToL2 (isCylSmooth_convSolTest k hsm) := by
        apply Lp.ext
        filter_upwards [(F8WeakEx.memLp_of_cylSmooth
            (F8WeakEx.isCylSmooth_of_solTest hΨ_sol)).coeFn_toLp,
          (F8WeakEx.memLp_of_cylSmooth (isCylSmooth_convSolTest k hsm)).coeFn_toLp] with y h1 h2
        exact h1.trans h2.symm
      have hsm_dir_eq : ∀ j : Fin 2,
          F8WeakEx.cylSmoothToL2
            ((F8WeakEx.isCylSmooth_of_solTest hΨ_sol).dir (B0579.dir j)) =
          F8WeakEx.cylSmoothToL2 ((isCylSmooth_convSolTest k hsm).dir (B0579.dir j)) := by
        intro j
        apply Lp.ext
        filter_upwards [(F8WeakEx.memLp_of_cylSmooth
            ((F8WeakEx.isCylSmooth_of_solTest hΨ_sol).dir (B0579.dir j))).coeFn_toLp,
          (F8WeakEx.memLp_of_cylSmooth
            ((isCylSmooth_convSolTest k hsm).dir (B0579.dir j))).coeFn_toLp] with y h1 h2
        exact h1.trans h2.symm
      rw [hsm_eq, hsm_dir_eq 0, hsm_dir_eq 1,
        cylSmoothToL2_conv_eq_mollCLM hc k hsm,
        fderiv_convSolTest_dir hc k hsm 0,
        fderiv_convSolTest_dir hc k hsm 1,
        inner_mollCLM_symm hc k] at hw_conv
      have hint_comm := (innerSL ℝ φ₀).intervalIntegral_comp_comm hint_Fk
      simp only [innerSL_apply_apply] at hint_comm
      rw [inner_sub_right, ← hint_comm]
      have hcongr : (∫ r in (0 : ℝ)..s, ⟪φ₀, Fk r⟫_ℝ) =
          -(∫ r in (0 : ℝ)..s,
            (ν * (⟪mollCLM hc k φq, F8WeakEx.dqCLM c (δU r)⟫_ℝ +
                ⟪mollCLM hc k φη, F8WeakEx.detaCLM c (δU r)⟫_ℝ) +
              ⟪mollCLM hc k φ₀, b r⟫_ℝ)) := by
        rw [← intervalIntegral.integral_neg]
        refine intervalIntegral.integral_congr fun r _ => ?_
        dsimp only [Fk]
        rw [real_inner_comm (P0 c _) φ₀, Cyl.inner_P0_comm, hP0_φ₀, real_inner_comm φ₀ _,
          inner_sub_right, real_inner_smul_right, inner_add_right,
          inner_mollCLM_symm hc k φq, inner_mollCLM_symm hc k φη,
          inner_mollCLM_symm hc k φ₀,
          inner_dir_cylSmooth_mollCLM hc k hsm 0,
          inner_dir_cylSmooth_mollCLM hc k hsm 1]
        ring
      rw [hcongr]
      change ⟪φ₀, uk s⟫_ℝ - _ = 0
      dsimp only [uk]
      linarith [hw_conv]
    -- Differentiate `Hk s := ∫ r in 0..s, Gk r` where `Gk` clamps `Fk` to `[0, 2]`
    let cl : ℝ → ℝ := fun r => (Set.projIcc (0 : ℝ) 2 (by norm_num) r : ℝ)
    have hcl_cont : Continuous cl := continuous_subtype_val.comp continuous_projIcc
    have hcl_mem : ∀ r : ℝ, cl r ∈ Icc (0 : ℝ) 2 :=
      fun r => (Set.projIcc (0 : ℝ) 2 (by norm_num) r).2
    have hcl_eq : ∀ r ∈ Icc (0 : ℝ) 2, cl r = r :=
      fun r hr => by simp [cl, Set.projIcc_of_mem _ hr]
    let Gk : ℝ → L2v c := fun r => Fk (cl r)
    have hGk_cont : Continuous Gk := hFk_cont.comp_continuous hcl_cont hcl_mem
    let Hk : ℝ → L2v c := fun s => ∫ r in (0 : ℝ)..s, Gk r
    have hHk_eq_uk : ∀ s ∈ Icc (0 : ℝ) 2, Hk s = uk s := by
      intro s hs
      rw [huk_integral s hs]
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le hs.1] at hr
      exact congrArg Fk (hcl_eq r ⟨hr.1, hr.2.trans hs.2⟩)
    have hHk_deriv : ∀ s : ℝ, HasDerivAt Hk (Gk s) s := fun s =>
      intervalIntegral.integral_hasDerivAt_right (hGk_cont.intervalIntegrable 0 s)
        (hGk_cont.stronglyMeasurableAtFilter volume (𝓝 s)) hGk_cont.continuousAt
    have hnorm_deriv : ∀ s : ℝ,
        HasDerivAt (fun τ => ⟪Hk τ, Hk τ⟫_ℝ) (2 * ⟪Hk s, Gk s⟫_ℝ) s := by
      intro s
      have hd := (hHk_deriv s).inner ℝ (hHk_deriv s)
      have hsym : ⟪Hk s, Gk s⟫_ℝ + ⟪Gk s, Hk s⟫_ℝ = 2 * ⟪Hk s, Gk s⟫_ℝ := by
        rw [real_inner_comm (Gk s) (Hk s)]; ring
      rwa [hsym] at hd
    have hGk_inner_cont : Continuous (fun s => 2 * ⟪Hk s, Gk s⟫_ℝ) := by
      have hHk_cont : Continuous Hk :=
        continuous_iff_continuousAt.mpr fun s => (hHk_deriv s).continuousAt
      exact continuous_const.mul (hHk_cont.inner hGk_cont)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t)
      (f := fun τ => ⟪Hk τ, Hk τ⟫_ℝ) (f' := fun s => 2 * ⟪Hk s, Gk s⟫_ℝ)
      (fun s _ => hnorm_deriv s) (hGk_inner_cont.intervalIntegrable 0 t)
    have hHk0 : Hk 0 = 0 := by simp [Hk]
    rw [hHk0, inner_zero_left, sub_zero, hHk_eq_uk t ht, real_inner_self_eq_norm_sq] at hftc
    have hslice_le : ∀ r ∈ Icc (0 : ℝ) 2,
        2 * ⟪Hk r, Gk r⟫_ℝ ≤ -2 * ⟪uk r, mollCLM hc k (b r)⟫_ℝ := by
      intro r hr
      rw [hHk_eq_uk r hr, show Gk r = Fk r from congrArg Fk (hcl_eq r hr)]
      have huk_df : P0 c (uk r) = uk r := by
        dsimp only [uk]
        have hp0 : P0 c (F8WeakEx.val0CLM c (δU r)) = F8WeakEx.val0CLM c (δU r) :=
          Cyl.P0_eq_self (F8WeakEx.H1Sol.mem_divFree (δU r))
        rw [← hp0, mollCLM_P0_comm hc k, Cyl.P0_idem]
      dsimp only [Fk]
      rw [real_inner_comm (P0 c _) (uk r), Cyl.inner_P0_comm, huk_df, real_inner_comm (uk r) _,
        inner_sub_right, real_inner_smul_right, inner_add_right,
        real_inner_comm (dmollCLM hc 0 k _) (uk r),
        real_inner_comm (dmollCLM hc 1 k _) (uk r)]
      dsimp only [uk]
      rw [inner_dmollCLM_mollCLM_weak hc 0 k (F8WeakEx.H1Sol.weak_q (δU r)),
        inner_dmollCLM_mollCLM_weak hc 1 k (F8WeakEx.H1Sol.weak_eta (δU r))]
      have hsq0 : 0 ≤ ‖mollCLM hc k (F8WeakEx.dqCLM c (δU r))‖ ^ 2 := sq_nonneg _
      have hsq1 : 0 ≤ ‖mollCLM hc k (F8WeakEx.detaCLM c (δU r))‖ ^ 2 := sq_nonneg _
      nlinarith
    have hrhs_cont : ContinuousOn (fun r => -2 * ⟪uk r, mollCLM hc k (b r)⟫_ℝ) (Icc (0 : ℝ) 2) :=
      continuousOn_const.mul
        (((mollCLM hc k).continuous.comp_continuousOn
            ((F8WeakEx.val0CLM c).continuous.comp_continuousOn hδU_cont)).inner
          ((mollCLM hc k).continuous.comp_continuousOn hb_cont))
    have hi_rhs : IntervalIntegrable (fun r => -2 * ⟪uk r, mollCLM hc k (b r)⟫_ℝ) volume 0 t :=
      (hrhs_cont.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
    have hmono := intervalIntegral.integral_mono_on ht.1
      (hGk_inner_cont.intervalIntegrable 0 t) hi_rhs
      fun r hr => hslice_le r ⟨hr.1, hr.2.trans ht.2⟩
    change ‖uk t‖ ^ 2 ≤ -2 * ∫ r in (0 : ℝ)..t, ⟪uk r, mollCLM hc k (b r)⟫_ℝ
    calc ‖uk t‖ ^ 2
        = ∫ y in (0 : ℝ)..t, 2 * ⟪Hk y, Gk y⟫_ℝ := hftc.symm
      _ ≤ ∫ u in (0 : ℝ)..t, -2 * ⟪uk u, mollCLM hc k (b u)⟫_ℝ := hmono
      _ = -2 * ∫ r in (0 : ℝ)..t, ⟪uk r, mollCLM hc k (b r)⟫_ℝ :=
          intervalIntegral.integral_const_mul _ _
  -- Pass `k → ∞` in `hmoll_energy` via dominated convergence on `Ioc 0 t`
  have henergy : ∀ t ∈ Icc (0 : ℝ) 2,
      ‖F8WeakEx.val0CLM c (δU t)‖ ^ 2 ≤
        -2 * ∫ r in (0 : ℝ)..t, ⟪F8WeakEx.val0CLM c (δU r), b r⟫_ℝ := by
    intro t ht
    have hlim_lhs : Tendsto
        (fun k : ℕ => ‖mollCLM hc k (F8WeakEx.val0CLM c (δU t))‖ ^ 2)
        atTop (𝓝 (‖F8WeakEx.val0CLM c (δU t)‖ ^ 2)) :=
      ((tendsto_mollCLM hc (F8WeakEx.val0CLM c (δU t))).norm).pow 2
    obtain ⟨Mu, hMu⟩ := isCompact_Icc.exists_bound_of_continuousOn
      ((F8WeakEx.val0CLM c).continuous.comp_continuousOn hδU_cont)
    obtain ⟨Mb, hMb⟩ := isCompact_Icc.exists_bound_of_continuousOn hb_cont
    let B : ℝ := max Mu 0 * max Mb 0
    have hlim_int : Tendsto
        (fun k : ℕ => ∫ r in (0 : ℝ)..t,
          ⟪mollCLM hc k (F8WeakEx.val0CLM c (δU r)), mollCLM hc k (b r)⟫_ℝ)
        atTop (𝓝 (∫ r in (0 : ℝ)..t, ⟪F8WeakEx.val0CLM c (δU r), b r⟫_ℝ)) := by
      simp_rw [intervalIntegral.integral_of_le ht.1]
      refine MeasureTheory.tendsto_integral_of_dominated_convergence (fun _ => B) ?_ ?_ ?_ ?_
      · intro k
        have hc_k : ContinuousOn
            (fun r => ⟪mollCLM hc k (F8WeakEx.val0CLM c (δU r)), mollCLM hc k (b r)⟫_ℝ)
            (Icc (0 : ℝ) 2) :=
          ((mollCLM hc k).continuous.comp_continuousOn
            ((F8WeakEx.val0CLM c).continuous.comp_continuousOn hδU_cont)).inner
            ((mollCLM hc k).continuous.comp_continuousOn hb_cont)
        exact (hc_k.mono (Ioc_subset_Icc_self.trans (Icc_subset_Icc_right ht.2))).aestronglyMeasurable
          measurableSet_Ioc
      · exact integrableOn_const (hs := measure_Ioc_lt_top.ne)
      · intro k
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
        have hr2 : r ∈ Icc (0 : ℝ) 2 := ⟨hr.1.le, hr.2.trans ht.2⟩
        have h1 : ‖mollCLM hc k (F8WeakEx.val0CLM c (δU r))‖ ≤ max Mu 0 :=
          ((ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_of_le_one_left (norm_nonneg _) (norm_mollCLM_le hc k))).trans
            ((hMu r hr2).trans (le_max_left _ _))
        have h2 : ‖mollCLM hc k (b r)‖ ≤ max Mb 0 :=
          ((ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_of_le_one_left (norm_nonneg _) (norm_mollCLM_le hc k))).trans
            ((hMb r hr2).trans (le_max_left _ _))
        rw [Real.norm_eq_abs]
        exact (abs_real_inner_le_norm _ _).trans (mul_le_mul h1 h2 (norm_nonneg _) (le_max_right _ _))
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r _
        exact (tendsto_mollCLM hc (F8WeakEx.val0CLM c (δU r))).inner (tendsto_mollCLM hc (b r))
    exact le_of_tendsto_of_tendsto hlim_lhs (tendsto_const_nhds.mul hlim_int)
      (Eventually.of_forall fun k => hmoll_energy k ht)
  -- Apply convective cancellation + Gronwall
  obtain ⟨M1, hM1_nn, hM1⟩ := hV.deriv_bound 1
  let g : ℝ → ℝ := fun r => ‖F8WeakEx.val0CLM c (δU r)‖ ^ 2
  have hg_cont : ContinuousOn g (Icc (0 : ℝ) 2) :=
    (((F8WeakEx.val0CLM c).continuous.comp_continuousOn hδU_cont).norm).pow 2
  let C : ℝ := 4 * M1 + 1
  have hC_pos : 0 < C := by dsimp only [C]; linarith
  have hg_ineq : ∀ t ∈ Icc (0 : ℝ) 2, g t ≤ C * ∫ r in (0 : ℝ)..t, g r := by
    intro t ht
    have hi_b : IntervalIntegrable (fun r => -2 * ⟪F8WeakEx.val0CLM c (δU r), b r⟫_ℝ) volume 0 t :=
      ((continuousOn_const.mul
        (((F8WeakEx.val0CLM c).continuous.comp_continuousOn hδU_cont).inner hb_cont)).mono
        (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
    have hi_g : IntervalIntegrable (fun r => C * g r) volume 0 t :=
      ((continuousOn_const.mul hg_cont).mono
        (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
    have hpt : ∀ r ∈ Icc (0 : ℝ) t, -2 * ⟪F8WeakEx.val0CLM c (δU r), b r⟫_ℝ ≤ C * g r := by
      intro r hr
      have hr2 : r ∈ Icc (0 : ℝ) 2 := ⟨hr.1, hr.2.trans ht.2⟩
      have habs := abs_inner_bvCLM_le hc hV hM1_nn hM1 hr2 (δU r)
      have hneg := neg_abs_le ⟪F8WeakEx.val0CLM c (δU r), b r⟫_ℝ
      have hgnn : 0 ≤ g r := sq_nonneg _
      dsimp only [C, g, b] at habs hneg ⊢
      linarith
    calc g t
        ≤ -2 * ∫ r in (0 : ℝ)..t, ⟪F8WeakEx.val0CLM c (δU r), b r⟫_ℝ := henergy t ht
      _ = ∫ r in (0 : ℝ)..t, (-2 * ⟪F8WeakEx.val0CLM c (δU r), b r⟫_ℝ) :=
          (intervalIntegral.integral_const_mul _ _).symm
      _ ≤ ∫ r in (0 : ℝ)..t, C * g r :=
          intervalIntegral.integral_mono_on ht.1 hi_b hi_g hpt
      _ = C * ∫ r in (0 : ℝ)..t, g r := intervalIntegral.integral_const_mul _ _
  have hg_zero := gronwall_nonneg_continuousOn hg_cont (fun _ _ => sq_nonneg _) hC_pos hg_ineq
  intro s hs
  have hval0 : F8WeakEx.val0CLM c (δU s) = 0 :=
    norm_eq_zero.mp (sq_eq_zero_iff.mp (hg_zero s hs))
  have hδU_s : δU s = 0 :=
    F8WeakEx.H1Sol.ext_val0 hc (by rw [hval0, map_zero])
  have heq : liftWeakSol hwk s = U s := sub_eq_zero.mp hδU_s
  have hlift_eq : liftWeakSol hwk s = F8WeakEx.H1Sol.ofRealDatum (hwk.slice_h1 s hs) := by
    unfold liftWeakSol; simp [hs]
  rw [hlift_eq] at heq
  exact heq

theorem weakH1_ae_eq_mild {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    {V : ℝ → Plane → F8Ex.RMerid} (hV : F8Ex.IsSmoothBUCDrift c V)
    {W Wq Wη : ℝ → Plane → F8Ex.RMerid} {u uq uη : Plane → F8Ex.RMerid}
    (hdat : F8Ex.IsRealCylH1Datum c u uq uη)
    (hwk : F8Ex.IsRealWeakH1OseenSol c ν V W Wq Wη u uq uη)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 2) :
    let U := F8WeakEx.E_oseen hc hν hV s 0 (F8WeakEx.H1Sol.ofRealDatum hdat)
    W s =ᵐ[F8Ex.cellMeas c] (F8WeakEx.val0CLM c U : Plane → F8Ex.RMerid) ∧
    Wq s =ᵐ[F8Ex.cellMeas c] (F8WeakEx.dqCLM c U : Plane → F8Ex.RMerid) ∧
    Wη s =ᵐ[F8Ex.cellMeas c] (F8WeakEx.detaCLM c U : Plane → F8Ex.RMerid) := by
  intro U
  have heq := weakH1_lift_eq_mild hc hν hV hdat hwk s hs
  obtain ⟨h0, hq, hη⟩ := F8WeakEx.H1Sol.ofRealDatum_ae (hwk.slice_h1 s hs)
  rw [heq] at h0 hq hη
  exact ⟨h0.symm, hq.symm, hη.symm⟩

end UnforcedLeray.Short.IIb.F8SpBoot

namespace UnforcedLeray.Short.IIb

theorem realCylOseenWeakMildUnique_proof : UnforcedLeray.Short.IIb.RealCylOseenWeakMildUnique :=
  fun _ _ hc hν _ hV _ _ _ _ _ _ hdat hwk _ hs =>
    F8SpBoot.weakH1_ae_eq_mild hc hν hV hdat hwk hs

end UnforcedLeray.Short.IIb
