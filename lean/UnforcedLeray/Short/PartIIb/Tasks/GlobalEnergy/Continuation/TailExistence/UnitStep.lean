import UnforcedLeray.Short.PartIIb.Tasks.GlobalEnergy.Continuation.TailExistence.HeatL2
import UnforcedLeray.Short.PartIIb.Tasks.GlobalEnergy.Continuation.BodySourceGlue
import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3_2_2.P0Rep
import UnforcedLeray.Infra.VolterraEvolution.Strip
import UnforcedLeray.Infra.JointMeasurableRep
import UnforcedLeray.Lib.BochnerTime.Duhamel

/-!
# Real unit-slab 2D cylinder Oseen/Stokes existence (`RealCylUnitOseenStep`)

Proves `realCylUnitOseenStep_proof : RealCylUnitOseenStep` for `PartII-b:F7/2/1`:
1. Inhomogeneous square-root Volterra Picard iteration on `[0, 1]` over `H1Sol p.c`;
2. Clamped BUC train drift operator `bvCLM : ℝ → H1Sol p.c →L[ℝ] L2v p.c` on `[t₀, t₀ + 1]`;
3. Bochner `L¹([0, 1]; H1Sol p.c)` lift `G` of the unit-slab source `(g₀, gq₀, gη₀)` and its
   continuous heat Duhamel integral `S_G`;
4. Jointly `StronglyMeasurable`, everywhere `p.c`-periodic spacetime representatives `(z, zq, zη)`
   matching `(u₀, uq₀, uη₀)` at `s = t₀` and continuous in `cylSliceH1` on `[t₀, t₀ + 1]`;
5. Master heat-adjoint FTC + Fubini verification of the weak meridional PDE on `(t₀, t₀ + 1)`.

All declarations live in `namespace UnforcedLeray.Short.IIb.TailExistenceAux`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology intervalIntegral
open scoped ENNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIb.TailExistenceAux

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace
open UnforcedLeray.Short.IIb
open UnforcedLeray.Cyl (L2v cellμ divFree P0 Vec2)
open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.HeatCylinder
open UnforcedLeray.Infra.VolterraEvolution

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-! ## 1. Statement of `RealCylUnitOseenStep` -/

/-- **Real unit-slab 2D cylinder Oseen/Stokes existence**:
for any `BgRegime` point `p`, starting age `t₀ > 0`, real `p.c`-periodic initial slice
`(u₀, uq₀, uη₀)` in `H¹_σ(C_c)`, and real `p.c`-periodic body source `(g₀, gq₀, gη₀)` supported in
`s ∈ (t₀, t₀ + 1)` with `H¹_σ(C_c)` slices in `L¹((t₀, t₀ + 1); H¹(C_c))`, the linear 2D cylinder
Oseen/Stokes equation `z_s - ν Δ_{q,η} z + P_0(B_v z) = g₀` on `(t₀, t₀ + 1)` admits a strongly
measurable, everywhere-`p.c`-periodic real solution `(z, zq, zη)` in `C([t₀, t₀ + 1]; H¹_σ(C_c))`
matching `(u₀, uq₀, uη₀)` at `s = t₀`. -/
def RealCylUnitOseenStep : Prop :=
  ∀ {p : Params} {d dm dp t₀ : ℝ},
    BgRegime p d dm dp → 0 < t₀ →
    ∀ {u₀ uq₀ uη₀ : B0579.Plane → Fin 2 → ℝ},
      StronglyMeasurable u₀ → StronglyMeasurable uq₀ → StronglyMeasurable uη₀ →
      (∀ y : B0579.Plane, u₀ (y.1 + p.c, y.2) = u₀ y ∧
        uq₀ (y.1 + p.c, y.2) = uq₀ y ∧ uη₀ (y.1 + p.c, y.2) = uη₀ y) →
      IsCylH1Slice p.c (ofRealSlice u₀) (ofRealSlice uq₀) (ofRealSlice uη₀) →
    ∀ {g₀ gq₀ gη₀ : Coord → Fin 2 → ℝ},
      StronglyMeasurable g₀ → StronglyMeasurable gq₀ → StronglyMeasurable gη₀ →
      (∀ x : Coord, g₀ (qShift p.c x) = g₀ x ∧
        gq₀ (qShift p.c x) = gq₀ x ∧ gη₀ (qShift p.c x) = gη₀ x) →
      (∀ x : Coord, x.1 ∉ Ioo t₀ (t₀ + 1) → g₀ x = 0 ∧ gq₀ x = 0 ∧ gη₀ x = 0) →
      (∀ s : ℝ, IsCylH1Slice p.c (fun y => ofRealProf g₀ (s, y))
        (fun y => ofRealProf gq₀ (s, y)) (fun y => ofRealProf gη₀ (s, y))) →
      (∫⁻ s in Ioo t₀ (t₀ + 1),
        sliceH1Norm p.c (ofRealProf g₀) (ofRealProf gq₀) (ofRealProf gη₀) s) < ⊤ →
      ∃ z zq zη : Coord → Fin 2 → ℝ,
        StronglyMeasurable z ∧ StronglyMeasurable zq ∧ StronglyMeasurable zη ∧
        (∀ x : Coord, z (qShift p.c x) = z x ∧
          zq (qShift p.c x) = zq x ∧ zη (qShift p.c x) = zη x) ∧
        (∀ s ∈ Icc t₀ (t₀ + 1), IsCylH1Slice p.c (fun y => ofRealProf z (s, y))
          (fun y => ofRealProf zq (s, y)) (fun y => ofRealProf zη (s, y))) ∧
        cylSliceH1 p.c (fun y => ofRealProf z (t₀, y) - ofRealSlice u₀ y)
          (fun y => ofRealProf zq (t₀, y) - ofRealSlice uq₀ y)
          (fun y => ofRealProf zη (t₀, y) - ofRealSlice uη₀ y) = 0 ∧
        (∀ s ∈ Icc t₀ (t₀ + 1),
          Tendsto (fun s' => cylSliceH1 p.c
            (fun y => ofRealProf z (s', y) - ofRealProf z (s, y))
            (fun y => ofRealProf zq (s', y) - ofRealProf zq (s, y))
            (fun y => ofRealProf zη (s', y) - ofRealProf zη (s, y)))
            (𝓝[Icc t₀ (t₀ + 1)] s) (𝓝 0)) ∧
        ∀ Ψ, IsPlanarSolTest Ψ →
          (∀ i, tsupport (fun x => Ψ x i) ⊆ Ioo t₀ (t₀ + 1) ×ˢ univ) →
          ∫ x, (∑ i : Fin 2, ofRealProf z x i * meridTranspose p.ν Ψ x i +
              cdot (flatBv p.train (ofRealProf z) (ofRealProf zq) (ofRealProf zη)) Ψ x) =
            ∫ x, cdot (ofRealProf g₀) Ψ x

/-! ## 2. Inhomogeneous Picard iteration on `[0, 1]` -/

private def inhomoPicard {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (D : VolterraData ℝ X Y) (f₀ : ℝ → X) : ℕ → ℝ → X
  | 0 => f₀
  | n + 1 => D.vol 0 (inhomoPicard D f₀ n)

private lemma continuousOn_inhomoPicard {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (D : VolterraData ℝ X Y) {f₀ : ℝ → X} (hf₀ : ContinuousOn f₀ (Icc 0 1)) (n : ℕ) :
    ContinuousOn (inhomoPicard D f₀ n) (Icc 0 1) := by
  induction n with
  | zero => exact hf₀
  | succ n ih =>
    change ContinuousOn (D.vol 0 (inhomoPicard D f₀ n)) (Icc 0 1)
    exact D.continuousOn_vol zero_le_one (by norm_num) ih

private lemma norm_inhomoPicard_le {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (D : VolterraData ℝ X Y) {f₀ : ℝ → X} {M : ℝ} (hM_nn : 0 ≤ M)
    (hf₀_bdd : ∀ τ ∈ Icc (0 : ℝ) 1, ‖f₀ τ‖ ≤ M) (n : ℕ) :
    ∀ τ ∈ Icc (0 : ℝ) 1,
      ‖inhomoPicard D f₀ n τ‖ ≤ M * D.q ^ n * Real.exp (D.lam * (τ - 0)) := by
  induction n with
  | zero =>
    intro τ hτ
    change ‖f₀ τ‖ ≤ M * D.q ^ 0 * Real.exp (D.lam * (τ - 0))
    rw [pow_zero, mul_one]
    have h1 : 1 ≤ Real.exp (D.lam * (τ - 0)) :=
      Real.one_le_exp (mul_nonneg D.lam_pos.le (by linarith [hτ.1]))
    exact (hf₀_bdd τ hτ).trans (le_mul_of_one_le_right hM_nn h1)
  | succ n ih =>
    intro τ hτ
    change ‖D.vol 0 (inhomoPicard D f₀ n) τ‖ ≤ _
    refine (D.norm_vol_le D.lam_pos hτ.1 (by linarith [hτ.2]) (A := M * D.q ^ n)
      (fun r hr => ih r ⟨hr.1, hr.2.trans hτ.2⟩)).trans (le_of_eq ?_)
    unfold VolterraData.q
    ring

private lemma exists_inhomo_volterra_sol {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (D : VolterraData ℝ X Y) {f₀ : ℝ → X} (hf₀ : ContinuousOn f₀ (Icc 0 1)) :
    ∃ U : ℝ → X,
      ContinuousOn U (Icc 0 1) ∧
      U 0 = f₀ 0 ∧
      ∀ τ ∈ Icc (0 : ℝ) 1, U τ = f₀ τ + D.vol 0 U τ := by
  obtain ⟨M0, hM0⟩ := isCompact_Icc.exists_bound_of_continuousOn hf₀
  let M : ℝ := max 0 M0
  have hM_nn : 0 ≤ M := le_max_left 0 M0
  have hf₀_bdd : ∀ τ ∈ Icc (0 : ℝ) 1, ‖f₀ τ‖ ≤ M :=
    fun τ hτ => (hM0 τ hτ).trans (le_max_right 0 M0)
  let maj : ℕ → ℝ := fun n => M * Real.exp D.lam * D.q ^ n
  have hmaj_sum : Summable maj :=
    (summable_geometric_of_lt_one D.q_nonneg D.q_lt_one).mul_left _
  have hle_maj : ∀ (n : ℕ) {τ : ℝ}, τ ∈ Icc (0 : ℝ) 1 → ‖inhomoPicard D f₀ n τ‖ ≤ maj n := by
    intro n τ hτ
    refine (norm_inhomoPicard_le D hM_nn hf₀_bdd n τ hτ).trans ?_
    have hexp : Real.exp (D.lam * (τ - 0)) ≤ Real.exp D.lam :=
      Real.exp_le_exp.mpr (by nlinarith [D.lam_pos, hτ.1, hτ.2])
    have h0 : 0 ≤ M * D.q ^ n := mul_nonneg hM_nn (pow_nonneg D.q_nonneg _)
    calc M * D.q ^ n * Real.exp (D.lam * (τ - 0))
        ≤ M * D.q ^ n * Real.exp D.lam := mul_le_mul_of_nonneg_left hexp h0
      _ = maj n := by dsimp [maj]; ring
  let U : ℝ → X := fun τ => ∑' n, inhomoPicard D f₀ n τ
  have hU_cont : ContinuousOn U (Icc 0 1) :=
    continuousOn_tsum (continuousOn_inhomoPicard D hf₀) hmaj_sum (fun n _ hτ => hle_maj n hτ)
  have hsum_pic : ∀ {τ : ℝ}, τ ∈ Icc (0 : ℝ) 1 → Summable (fun n => inhomoPicard D f₀ n τ) :=
    fun hτ => Summable.of_norm_bounded hmaj_sum (fun n => hle_maj n hτ)
  have hU_eq : ∀ τ ∈ Icc (0 : ℝ) 1, U τ = f₀ τ + D.vol 0 U τ := by
    intro τ hτ
    dsimp only [U]
    rw [(hsum_pic hτ).tsum_eq_zero_add]
    change f₀ τ + ∑' n, D.vol 0 (inhomoPicard D f₀ n) τ =
      f₀ τ + D.vol 0 (fun r => ∑' n, inhomoPicard D f₀ n r) τ
    congr 1
    refine (?_ : HasSum (fun n => D.vol 0 (inhomoPicard D f₀ n) τ)
      (D.vol 0 (fun r => ∑' n, inhomoPicard D f₀ n r) τ)).tsum_eq
    unfold VolterraData.vol
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n r => D.C₀ * D.β * (τ - r) ^ (-(1 / 2 : ℝ)) * maj n) ?_ ?_ ?_ ?_ ?_
    · intro n
      exact (D.intervalIntegrable_integrand hτ.1 (by linarith [hτ.2])
        ((continuousOn_inhomoPicard D hf₀ n).mono (Icc_subset_Icc_right hτ.2))).def'.aestronglyMeasurable
    · intro n
      filter_upwards [ae_ne_real τ] with r hrτ hr
      rw [uIoc_of_le hτ.1] at hr
      have hr' : r ∈ Ico 0 τ := ⟨hr.1.le, lt_of_le_of_ne hr.2 hrτ⟩
      refine (D.norm_integrand_le (by linarith [hτ.2]) hr' _).trans ?_
      refine mul_le_mul_of_nonneg_left (hle_maj n ⟨hr'.1, hr'.2.le.trans hτ.2⟩) ?_
      exact mul_nonneg (mul_nonneg D.C₀_nonneg D.β_nonneg)
        (Real.rpow_nonneg (by linarith [hr'.2]) _)
    · exact Eventually.of_forall fun _ _ => hmaj_sum.mul_left _
    · simp_rw [tsum_mul_left]
      exact ((intervalIntegrable_kernel τ 0 τ).const_mul (D.C₀ * D.β)).mul_const _
    · refine Eventually.of_forall fun r hr => ?_
      rw [uIoc_of_le hτ.1] at hr
      have hs := (hsum_pic (τ := r) ⟨hr.1.le, hr.2.trans hτ.2⟩).hasSum
      exact (D.S (τ - r)).hasSum ((D.B r).hasSum hs)
  have hU0 : U 0 = f₀ 0 := by
    rw [hU_eq 0 ⟨le_rfl, zero_le_one⟩]
    unfold VolterraData.vol
    rw [intervalIntegral.integral_same, add_zero]
  exact ⟨U, hU_cont, hU0, hU_eq⟩

/-! ## 3. Clamped BUC train drift operator `bvCLM` on `[0, 1]` -/

private def clamp01 (r : ℝ) : ℝ := (Set.projIcc (0 : ℝ) 1 zero_le_one r : ℝ)

private lemma clamp01_mem (r : ℝ) : clamp01 r ∈ Icc (0 : ℝ) 1 :=
  (Set.projIcc (0 : ℝ) 1 zero_le_one r).2

private lemma clamp01_of_mem {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) : clamp01 r = r :=
  congrArg Subtype.val (Set.projIcc_of_mem zero_le_one hr)

private lemma continuous_clamp01 : Continuous clamp01 :=
  continuous_subtype_val.comp continuous_projIcc

private lemma clamped_train_coeffs {p : Params} {d dm dp t₀ : ℝ}
    (hbg : BgRegime p d dm dp) (ht₀ : 0 < t₀) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ k : Fin 2, Continuous (fun q : ℝ × Plane => p.train.v (t₀ + clamp01 q.1) q.2 k)) ∧
      (∀ j i : Fin 2, Continuous (fun q : ℝ × Plane =>
        fderiv ℝ (fun z => p.train.v (t₀ + clamp01 q.1) z i) q.2 (B0579.dir j))) ∧
      (∀ (r : ℝ) (k : Fin 2) (y : Plane), |p.train.v (t₀ + clamp01 r) y k| ≤ M) ∧
      (∀ (r : ℝ) (j i : Fin 2) (y : Plane),
        |fderiv ℝ (fun z => p.train.v (t₀ + clamp01 r) z i) y (B0579.dir j)| ≤ M) := by
  have ht1 : 0 ≤ t₀ + 1 := by linarith
  obtain ⟨M0, hM0⟩ := hbg.train_buc.sup_bound ht1
  obtain ⟨M1, hM1⟩ := hbg.train_buc.deriv_bound ht1 1
  let M : ℝ := max 0 (max M0 M1)
  have hM_nn : 0 ≤ M := le_max_left 0 _
  have hpos_arg : ∀ q : ℝ × Plane, 0 < t₀ + clamp01 q.1 :=
    fun q => by linarith [(clamp01_mem q.1).1]
  have hmem_U0 : ∀ q : ℝ × Plane, ((t₀ + clamp01 q.1, q.2) : Coord) ∈ FlatBvWL.U0 :=
    fun q => FlatBvWL.mem_U0_iff.mpr (hpos_arg q)
  have hc_arg : Continuous (fun q : ℝ × Plane => ((t₀ + clamp01 q.1, q.2) : Coord)) :=
    (continuous_const.add (continuous_clamp01.comp continuous_fst)).prodMk continuous_snd
  have hcont_V : ∀ k : Fin 2, Continuous (fun q : ℝ × Plane =>
      p.train.v (t₀ + clamp01 q.1) q.2 k) := fun k =>
    (FlatBvWL.gC_contDiffOn p.train k).continuousOn.comp_continuous hc_arg hmem_U0
  have hcont_dV : ∀ j i : Fin 2, Continuous (fun q : ℝ × Plane =>
      fderiv ℝ (fun z => p.train.v (t₀ + clamp01 q.1) z i) q.2 (B0579.dir j)) := by
    intro j i
    have hc1 := (FlatBvWL.gD_contDiffOn p.train i (B0579.dir j)).continuousOn.comp_continuous
      hc_arg hmem_U0
    exact hc1.congr fun q =>
      FlatBvWL.gD_eq p.train i (B0579.dir j) (x := ((t₀ + clamp01 q.1, q.2) : Coord)) (hpos_arg q)
  refine ⟨M, hM_nn, hcont_V, hcont_dV, ?_, ?_⟩
  · intro r k y
    have hs : t₀ + clamp01 r ∈ Icc 0 (t₀ + 1) :=
      ⟨by linarith [(clamp01_mem r).1], by linarith [(clamp01_mem r).2]⟩
    calc |p.train.v (t₀ + clamp01 r) y k|
        = ‖p.train.v (t₀ + clamp01 r) y k‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖p.train.v (t₀ + clamp01 r) y‖ := PiLp.norm_apply_le _ k
      _ ≤ M0 := hM0 (t₀ + clamp01 r) hs y
      _ ≤ M := (le_max_left M0 M1).trans (le_max_right 0 _)
  · intro r j i y
    have hs : t₀ + clamp01 r ∈ Icc 0 (t₀ + 1) :=
      ⟨by linarith [(clamp01_mem r).1], by linarith [(clamp01_mem r).2]⟩
    have hVs : ContDiff ℝ ∞ (p.train.v (t₀ + clamp01 r)) := by
      have hc0 := p.train.isTrain.smooth_v.comp (contDiff_const.prodMk contDiff_id).contDiffOn
        (s := univ) (fun z _ => ⟨hs.1, mem_univ z⟩)
      exact contDiffOn_univ.1 hc0
    have hproj : fderiv ℝ (fun z => p.train.v (t₀ + clamp01 r) z i) y (B0579.dir j) =
        fderiv ℝ (p.train.v (t₀ + clamp01 r)) y (B0579.dir j) i := by
      have hc0 := ((πR i).hasFDerivAt.comp y
        (hVs.contDiffAt.differentiableAt (by simp)).hasFDerivAt).fderiv
      change fderiv ℝ ((πR i) ∘ (p.train.v (t₀ + clamp01 r))) y (B0579.dir j) =
        πR i (fderiv ℝ (p.train.v (t₀ + clamp01 r)) y (B0579.dir j))
      rw [hc0, ContinuousLinearMap.comp_apply]
    have hdir_norm : ‖B0579.dir j‖ = 1 := by fin_cases j <;> simp [B0579.dir]
    rw [hproj]
    calc |fderiv ℝ (p.train.v (t₀ + clamp01 r)) y (B0579.dir j) i|
        = ‖fderiv ℝ (p.train.v (t₀ + clamp01 r)) y (B0579.dir j) i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ (p.train.v (t₀ + clamp01 r)) y (B0579.dir j)‖ := PiLp.norm_apply_le _ i
      _ = ‖iteratedFDeriv ℝ 1 (p.train.v (t₀ + clamp01 r)) y ![B0579.dir j]‖ := by
          rw [iteratedFDeriv_one_apply, Matrix.cons_val_zero]
      _ ≤ ‖iteratedFDeriv ℝ 1 (p.train.v (t₀ + clamp01 r)) y‖ *
            ∏ l : Fin 1, ‖(![B0579.dir j] : Fin 1 → Plane) l‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖iteratedFDeriv ℝ 1 (p.train.v (t₀ + clamp01 r)) y‖ := by simp [hdir_norm]
      _ ≤ M1 := hM1 (t₀ + clamp01 r) hs y
      _ ≤ M := (le_max_right M0 M1).trans (le_max_right 0 _)

private def trainDriftBound {p : Params} {d dm dp t₀ : ℝ}
    (hbg : BgRegime p d dm dp) (ht₀ : 0 < t₀) : ℝ :=
  (clamped_train_coeffs hbg ht₀).choose

private lemma trainDriftBound_nonneg {p : Params} {d dm dp t₀ : ℝ}
    (hbg : BgRegime p d dm dp) (ht₀ : 0 < t₀) :
    0 ≤ trainDriftBound hbg ht₀ :=
  (clamped_train_coeffs hbg ht₀).choose_spec.1

private def trainBvCLM {p : Params} {d dm dp t₀ : ℝ}
    (hbg : BgRegime p d dm dp) (ht₀ : 0 < t₀) (r : ℝ) : H1Sol p.c →L[ℝ] L2v p.c :=
  let hspec := (clamped_train_coeffs hbg ht₀).choose_spec
  let hM := hspec.1
  let hcV := hspec.2.1
  let hcdV := hspec.2.2.1
  let hbV := hspec.2.2.2.1
  let hbdV := hspec.2.2.2.2
  let tq := (scalarMultCLM (fun y => p.train.v (t₀ + clamp01 r) y 0)
    ((hcV 0).comp (continuous_const.prodMk continuous_id)) hM (hbV r 0)).comp (dqCLM p.c)
  let tη := (scalarMultCLM (fun y => p.train.v (t₀ + clamp01 r) y 1)
    ((hcV 1).comp (continuous_const.prodMk continuous_id)) hM (hbV r 1)).comp (detaCLM p.c)
  let ts (j i : Fin 2) := (scalarMultCLM
    (fun y => fderiv ℝ (fun z => p.train.v (t₀ + clamp01 r) z i) y (B0579.dir j))
    ((hcdV j i).comp (continuous_const.prodMk continuous_id)) hM (hbdV r j i)).comp
    (((rank1VecCLM j i).compLpL 2 (cellμ p.c)).comp (val0CLM p.c))
  ((tq + tη) + (ts 0 0 + ts 0 1)) + (ts 1 0 + ts 1 1)

private lemma norm_trainBvCLM_le {p : Params} {d dm dp t₀ : ℝ}
    (hbg : BgRegime p d dm dp) (ht₀ : 0 < t₀) (r : ℝ) :
    ‖trainBvCLM hbg ht₀ r‖ ≤ 6 * trainDriftBound hbg ht₀ := by
  let M := trainDriftBound hbg ht₀
  have hM : 0 ≤ M := trainDriftBound_nonneg hbg ht₀
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun q => ?_
  let hspec := (clamped_train_coeffs hbg ht₀).choose_spec
  have hcV_r : ∀ k : Fin 2, Continuous (fun y : Plane => p.train.v (t₀ + clamp01 r) y k) :=
    fun k => (hspec.2.1 k).comp (continuous_const.prodMk continuous_id)
  have hcdV_r : ∀ j i : Fin 2,
      Continuous (fun y : Plane =>
        fderiv ℝ (fun z => p.train.v (t₀ + clamp01 r) z i) y (B0579.dir j)) :=
    fun j i => (hspec.2.2.1 j i).comp (continuous_const.prodMk continuous_id)
  have b_sc : ∀ {a : Plane → ℝ} (ha : Continuous a) (hb : ∀ y, |a y| ≤ M) (w : L2v p.c),
      ‖w‖ ≤ ‖q‖ → ‖scalarMultCLM a ha hM hb w‖ ≤ M * ‖q‖ := by
    intro a ha hb w hw
    exact ((ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (norm_scalarMultCLM_le ha hM hb) (norm_nonneg _))).trans
      (mul_le_mul_of_nonneg_left hw hM)
  have b_rk : ∀ j i : Fin 2,
      ‖((rank1VecCLM j i).compLpL 2 (cellμ p.c)) (val0CLM p.c q)‖ ≤ ‖q‖ := by
    intro j i
    calc ‖((rank1VecCLM j i).compLpL 2 (cellμ p.c)) (val0CLM p.c q)‖
        ≤ ‖(rank1VecCLM j i).compLpL 2 (cellμ p.c)‖ * ‖val0CLM p.c q‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖val0CLM p.c q‖ :=
          mul_le_mul_of_nonneg_right
            ((ContinuousLinearMap.norm_compLpL_le (rank1VecCLM j i)).trans (norm_rank1VecCLM_le j i))
            (norm_nonneg _)
      _ = ‖val0CLM p.c q‖ := one_mul _
      _ ≤ ‖q‖ := norm_val0CLM_le q
  let tq := scalarMultCLM (fun y => p.train.v (t₀ + clamp01 r) y 0) (hcV_r 0) hM
    (hspec.2.2.2.1 r 0) (dqCLM p.c q)
  let tη := scalarMultCLM (fun y => p.train.v (t₀ + clamp01 r) y 1) (hcV_r 1) hM
    (hspec.2.2.2.1 r 1) (detaCLM p.c q)
  let ts (j i : Fin 2) := scalarMultCLM
    (fun y => fderiv ℝ (fun z => p.train.v (t₀ + clamp01 r) z i) y (B0579.dir j))
    (hcdV_r j i) hM (hspec.2.2.2.2 r j i)
    (((rank1VecCLM j i).compLpL 2 (cellμ p.c)) (val0CLM p.c q))
  have h_eq : trainBvCLM hbg ht₀ r q = ((tq + tη) + (ts 0 0 + ts 0 1)) + (ts 1 0 + ts 1 1) := rfl
  rw [h_eq]
  have b1 : ‖tq‖ ≤ M * ‖q‖ := b_sc (hcV_r 0) (hspec.2.2.2.1 r 0) (dqCLM p.c q) (norm_dqCLM_le q)
  have b2 : ‖tη‖ ≤ M * ‖q‖ := b_sc (hcV_r 1) (hspec.2.2.2.1 r 1) (detaCLM p.c q) (norm_detaCLM_le q)
  have b3 : ‖ts 0 0‖ ≤ M * ‖q‖ := b_sc (hcdV_r 0 0) (hspec.2.2.2.2 r 0 0) _ (b_rk 0 0)
  have b4 : ‖ts 0 1‖ ≤ M * ‖q‖ := b_sc (hcdV_r 0 1) (hspec.2.2.2.2 r 0 1) _ (b_rk 0 1)
  have b5 : ‖ts 1 0‖ ≤ M * ‖q‖ := b_sc (hcdV_r 1 0) (hspec.2.2.2.2 r 1 0) _ (b_rk 1 0)
  have b6 : ‖ts 1 1‖ ≤ M * ‖q‖ := b_sc (hcdV_r 1 1) (hspec.2.2.2.2 r 1 1) _ (b_rk 1 1)
  have n12 : ‖tq + tη‖ ≤ 2 * M * ‖q‖ := (norm_add_le _ _).trans (by linarith)
  have n34 : ‖ts 0 0 + ts 0 1‖ ≤ 2 * M * ‖q‖ := (norm_add_le _ _).trans (by linarith)
  have n56 : ‖ts 1 0 + ts 1 1‖ ≤ 2 * M * ‖q‖ := (norm_add_le _ _).trans (by linarith)
  have n1234 : ‖(tq + tη) + (ts 0 0 + ts 0 1)‖ ≤ 4 * M * ‖q‖ :=
    (norm_add_le _ _).trans (by linarith)
  exact (norm_add_le _ _).trans (by linarith)

private lemma continuous_trainBvCLM_apply {p : Params} {d dm dp t₀ : ℝ}
    (hbg : BgRegime p d dm dp) (ht₀ : 0 < t₀) (q : H1Sol p.c) :
    Continuous (fun r : ℝ => trainBvCLM hbg ht₀ r q) := by
  let hspec := (clamped_train_coeffs hbg ht₀).choose_spec
  let hM := hspec.1
  have c1 := continuous_scalarMultCLM_apply (a := fun r y => p.train.v (t₀ + clamp01 r) y 0)
    (hspec.2.1 0) hM (fun r y => hspec.2.2.2.1 r 0 y) (dqCLM p.c q)
  have c2 := continuous_scalarMultCLM_apply (a := fun r y => p.train.v (t₀ + clamp01 r) y 1)
    (hspec.2.1 1) hM (fun r y => hspec.2.2.2.1 r 1 y) (detaCLM p.c q)
  have cs : ∀ j i : Fin 2, Continuous (fun r : ℝ => scalarMultCLM
      (fun y => fderiv ℝ (fun z => p.train.v (t₀ + clamp01 r) z i) y (B0579.dir j))
      ((hspec.2.2.1 j i).comp (continuous_const.prodMk continuous_id)) hM
      (hspec.2.2.2.2 r j i)
      (((rank1VecCLM j i).compLpL 2 (cellμ p.c)) (val0CLM p.c q))) := fun j i =>
    continuous_scalarMultCLM_apply
      (a := fun r y => fderiv ℝ (fun z => p.train.v (t₀ + clamp01 r) z i) y (B0579.dir j))
      (hspec.2.2.1 j i) hM (fun r y => hspec.2.2.2.2 r j i y)
      (((rank1VecCLM j i).compLpL 2 (cellμ p.c)) (val0CLM p.c q))
  exact ((c1.add c2).add ((cs 0 0).add (cs 0 1))).add ((cs 1 0).add (cs 1 1))

private lemma trainBvCLM_ae {p : Params} {d dm dp t₀ : ℝ}
    (hbg : BgRegime p d dm dp) (ht₀ : 0 < t₀) (r : ℝ) (q : H1Sol p.c)
    {w wq wη : B0579.Plane → Fin 2 → ℝ}
    (hw : (val0CLM p.c q : Plane → Vec2) =ᵐ[cellμ p.c] toVecSlice w)
    (hwq : (dqCLM p.c q : Plane → Vec2) =ᵐ[cellμ p.c] toVecSlice wq)
    (hwη : (detaCLM p.c q : Plane → Vec2) =ᵐ[cellμ p.c] toVecSlice wη) :
    (trainBvCLM hbg ht₀ r q : Plane → Vec2) =ᵐ[cellμ p.c]
      toVecSlice (fun y i =>
        p.train.v (t₀ + clamp01 r) y 0 * wq y i +
        p.train.v (t₀ + clamp01 r) y 1 * wη y i +
        w y 0 * fderiv ℝ (fun z => p.train.v (t₀ + clamp01 r) z i) y (B0579.dir 0) +
        w y 1 * fderiv ℝ (fun z => p.train.v (t₀ + clamp01 r) z i) y (B0579.dir 1)) := by
  let hspec := (clamped_train_coeffs hbg ht₀).choose_spec
  let hM := hspec.1
  have hcV_r : ∀ k : Fin 2, Continuous (fun y : Plane => p.train.v (t₀ + clamp01 r) y k) :=
    fun k => (hspec.2.1 k).comp (continuous_const.prodMk continuous_id)
  have hcdV_r : ∀ j i : Fin 2,
      Continuous (fun y : Plane =>
        fderiv ℝ (fun z => p.train.v (t₀ + clamp01 r) z i) y (B0579.dir j)) :=
    fun j i => (hspec.2.2.1 j i).comp (continuous_const.prodMk continuous_id)
  let fq := scalarMultCLM (fun y => p.train.v (t₀ + clamp01 r) y 0) (hcV_r 0) hM
    (hspec.2.2.2.1 r 0) (dqCLM p.c q)
  let fη := scalarMultCLM (fun y => p.train.v (t₀ + clamp01 r) y 1) (hcV_r 1) hM
    (hspec.2.2.2.1 r 1) (detaCLM p.c q)
  let rk (j i : Fin 2) := ((rank1VecCLM j i).compLpL 2 (cellμ p.c)) (val0CLM p.c q)
  let fs (j i : Fin 2) := scalarMultCLM
    (fun y => fderiv ℝ (fun z => p.train.v (t₀ + clamp01 r) z i) y (B0579.dir j))
    (hcdV_r j i) hM (hspec.2.2.2.2 r j i) (rk j i)
  have hae_rk : ∀ j i : Fin 2, (rk j i : Plane → Vec2) =ᵐ[cellμ p.c]
      fun y => rank1VecCLM j i (toVecSlice w y) := by
    intro j i
    filter_upwards [ContinuousLinearMap.coeFn_compLpL (rank1VecCLM j i) (val0CLM p.c q), hw]
      with y h1 h2
    rw [h1, h2]
  have hae_fq := coeFn_scalarMultCLM (hcV_r 0) hM (hspec.2.2.2.1 r 0) (dqCLM p.c q)
  have hae_fη := coeFn_scalarMultCLM (hcV_r 1) hM (hspec.2.2.2.1 r 1) (detaCLM p.c q)
  have hae_fs : ∀ j i : Fin 2, (fs j i : Plane → Vec2) =ᵐ[cellμ p.c]
      fun y => fderiv ℝ (fun z => p.train.v (t₀ + clamp01 r) z i) y (B0579.dir j) •
        rank1VecCLM j i (toVecSlice w y) := by
    intro j i
    filter_upwards [coeFn_scalarMultCLM (hcdV_r j i) hM (hspec.2.2.2.2 r j i) (rk j i),
      hae_rk j i] with y h1 h2
    exact h1.trans (congrArg _ h2)
  have hadd_top := Lp.coeFn_add ((fq + fη) + (fs 0 0 + fs 0 1)) (fs 1 0 + fs 1 1)
  have hadd_L := Lp.coeFn_add (fq + fη) (fs 0 0 + fs 0 1)
  have hadd_12 := Lp.coeFn_add fq fη
  have hadd_34 := Lp.coeFn_add (fs 0 0) (fs 0 1)
  have hadd_56 := Lp.coeFn_add (fs 1 0) (fs 1 1)
  filter_upwards [hadd_top, hadd_L, hadd_12, hadd_34, hadd_56,
    hae_fq, hae_fη, hwq, hwη, hae_fs 0 0, hae_fs 0 1, hae_fs 1 0, hae_fs 1 1]
    with y htop hL h12 h34 h56 hfq hfη hq hη hs00 hs01 hs10 hs11
  change ((((fq + fη) + (fs 0 0 + fs 0 1)) + (fs 1 0 + fs 1 1) : L2v p.c) : Plane → Vec2) y = _
  rw [htop, Pi.add_apply, hL, Pi.add_apply, h12, Pi.add_apply, h34, Pi.add_apply,
    h56, Pi.add_apply, hfq, hfη, hq, hη, hs00, hs01, hs10, hs11]
  ext i
  fin_cases i <;>
    simp [toVecSlice, rank1VecCLM, πR] <;> ring

/-! ## 4. General `StronglyMeasurable` operator application and periodic cell retraction -/

private lemma stronglyMeasurable_clm_apply {α X Y : Type*} [TopologicalSpace α]
    [SecondCountableTopology α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {U : α → X →L[ℝ] Y} (hU : ∀ x, Continuous fun a => U a x)
    {f : α → X} (hf : StronglyMeasurable f) :
    StronglyMeasurable (fun a => U a (f a)) := by
  induction f, hf using StronglyMeasurable.induction with
  | @ind c s hs =>
    have : (fun a => U a (s.indicator (fun _ => c) a)) = s.indicator fun a => U a c := by
      funext a; by_cases ha : a ∈ s <;> simp [ha]
    rw [this]
    exact (hU c).stronglyMeasurable.indicator hs
  | @add f g _ _ _ _ ihf ihg =>
    have : (fun a => U a ((f + g) a)) = fun a => U a (f a) + U a (g a) := by
      funext a; simp [map_add]
    rw [this]
    exact ihf.add ihg
  | @lim f g _ _ ihf hlim =>
    refine stronglyMeasurable_of_tendsto atTop ihf ?_
    rw [tendsto_pi_nhds]
    intro a
    exact ((U a).continuous.tendsto _).comp (hlim a)

private def toCellLocal (c : ℝ) (z : B0579.Plane) : B0579.Plane :=
  (z.1 - c * (⌊(z.1 + c / 2) / c⌋ : ℝ), z.2)

private lemma measurable_toCellLocal (c : ℝ) : Measurable (toCellLocal c) := by
  unfold toCellLocal
  have hfl : Measurable (fun z : B0579.Plane => (⌊(z.1 + c / 2) / c⌋ : ℝ)) :=
    (measurable_of_countable (fun n : ℤ => (n : ℝ))).comp
      (((measurable_fst.add measurable_const).div_const c).floor)
  exact (measurable_fst.sub (measurable_const.mul hfl)).prodMk measurable_snd

private lemma toCellLocal_periodic {c : ℝ} (hc : 0 < c) (z : B0579.Plane) :
    toCellLocal c (z.1 + c, z.2) = toCellLocal c z := by
  unfold toCellLocal
  ext
  · dsimp only
    have hdiv : (z.1 + c + c / 2) / c = (z.1 + c / 2) / c + 1 := by
      field_simp [hc.ne']; ring
    rw [hdiv, Int.floor_add_one]
    push_cast; ring
  · rfl

private lemma toCellLocal_eq_self_of_mem_cell {c : ℝ} (hc : 0 < c) {z : B0579.Plane}
    (hz : z ∈ B0579.cell c) : toCellLocal c z = z := by
  have hlo : 0 ≤ (z.1 + c / 2) / c := div_nonneg (by linarith [hz.1.1]) hc.le
  have hhi : (z.1 + c / 2) / c < 1 := (div_lt_one hc).2 (by linarith [hz.1.2])
  have hfl : ⌊(z.1 + c / 2) / c⌋ = 0 := by
    rw [Int.floor_eq_iff]
    exact ⟨by simpa using hlo, by simpa using hhi⟩
  ext
  · simp [toCellLocal, hfl]
  · rfl

/-! ## 5. Periodized planar test curve regularity and heat-adjoint FTC + Fubini helpers -/

private lemma tsupport_cpd_subset (j : Fin 3) (φ : Coord → ℝ) :
    tsupport (cpd j φ) ⊆ tsupport φ := by
  refine closure_minimal (fun x hx => ?_) (isClosed_tsupport φ)
  by_contra hnot
  exact hx (by simp [cpd, fderiv_of_notMem_tsupport (𝕜 := ℝ) hnot])

private lemma isPlanarSolTest_cpd0 {Ψ : Coord → Fin 2 → ℝ} (hΨ : IsPlanarSolTest Ψ) :
    IsPlanarSolTest (fun x i => cpd 0 (fun w => Ψ w i) x) where
  smooth i := planarTest_isCoordTest_partial (hΨ.smooth i) (cdir 0)
  div_free x := by
    have h0_sm : ContDiff ℝ ∞ (fun w => Ψ w 0) := (hΨ.smooth 0).smooth
    have h1_sm : ContDiff ℝ ∞ (fun w => Ψ w 1) := (hΨ.smooth 1).smooth
    have hcomm0 : cpd 1 (cpd 0 (fun w => Ψ w 0)) x = cpd 0 (cpd 1 (fun w => Ψ w 0)) x := by
      have hp := UnforcedLeray.Sob.iterDirDeriv_perm
        (List.Perm.swap (cdir 0) (cdir 1) []) h0_sm
      exact congrFun hp x
    have hcomm1 : cpd 2 (cpd 0 (fun w => Ψ w 1)) x = cpd 0 (cpd 2 (fun w => Ψ w 1)) x := by
      have hp := UnforcedLeray.Sob.iterDirDeriv_perm
        (List.Perm.swap (cdir 0) (cdir 2) []) h1_sm
      exact congrFun hp x
    change cpd 1 (cpd 0 (fun w => Ψ w 0)) x + cpd 2 (cpd 0 (fun w => Ψ w 1)) x = 0
    rw [hcomm0, hcomm1]
    have hd1 : DifferentiableAt ℝ (cpd 1 (fun w => Ψ w 0)) x :=
      ((planarTest_isCoordTest_partial (hΨ.smooth 0) (cdir 1)).smooth.differentiable (by simp)) x
    have hd2 : DifferentiableAt ℝ (cpd 2 (fun w => Ψ w 1)) x :=
      ((planarTest_isCoordTest_partial (hΨ.smooth 1) (cdir 2)).smooth.differentiable (by simp)) x
    have hadd : fderiv ℝ (cpd 1 (fun w => Ψ w 0) + cpd 2 (fun w => Ψ w 1)) x (cdir 0) =
        fderiv ℝ (cpd 1 (fun w => Ψ w 0)) x (cdir 0) +
          fderiv ℝ (cpd 2 (fun w => Ψ w 1)) x (cdir 0) := by
      rw [fderiv_add hd1 hd2, add_apply]
    have hsum : cpd 1 (fun w => Ψ w 0) + cpd 2 (fun w => Ψ w 1) = fun _ => (0 : ℝ) :=
      funext hΨ.div_free
    change fderiv ℝ (cpd 1 (fun w => Ψ w 0)) x (cdir 0) +
      fderiv ℝ (cpd 2 (fun w => Ψ w 1)) x (cdir 0) = 0
    rw [← hadd, hsum, (hasFDerivAt_const (0 : ℝ) x).fderiv, zero_apply]

private lemma shift_outside_cell_box {c R : ℝ} (hc : 0 < c)
    {K : ℕ} (hK : (c / 2 + R) / c + 1 < (K : ℝ))
    {y : B0579.Plane} (hy : y ∈ B0579.cell c) {k : ℤ}
    (hk : k ∉ Finset.Icc (-(K : ℤ)) (K : ℤ)) :
    R < |y.1 + (k : ℝ) * c| := by
  have hy_abs : |y.1| ≤ c / 2 := abs_le.2 ⟨hy.1.1, hy.1.2.le⟩
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hk
  have hk_abs : (K : ℝ) + 1 ≤ |(k : ℝ)| := by
    have hk_int : (K : ℤ) + 1 ≤ |k| := by
      rcases hk with hk | hk
      · rw [abs_of_neg (by omega)]; omega
      · rw [abs_of_nonneg (by omega)]; omega
    have hk_r : ((K : ℤ) + 1 : ℝ) ≤ (|k| : ℝ) := by exact_mod_cast hk_int
    simpa [Int.cast_abs] using hk_r
  have h1 : c / 2 + R + c < ((K : ℝ) + 1) * c := by
    have hm := mul_lt_mul_of_pos_right hK hc
    have hdiv : ((c / 2 + R) / c + 1) * c = c / 2 + R + c := by field_simp [hc.ne']
    linarith
  have h2 : ((K : ℝ) + 1) * c ≤ |(k : ℝ)| * c :=
    mul_le_mul_of_nonneg_right hk_abs hc.le
  have h3 : |(k : ℝ)| * c - |y.1| ≤ |y.1 + (k : ℝ) * c| := by
    have hsub := abs_sub_abs_le_abs_add ((k : ℝ) * c) y.1
    rw [add_comm, abs_mul, abs_of_pos hc] at hsub
    linarith
  linarith

private lemma continuous_qPeriodize_L2 {c t₀ : ℝ} (hc : 0 < c)
    {Ξ : Coord → Fin 2 → ℝ} (hΞ : ∀ i : Fin 2, IsCoordTest (fun x => Ξ x i))
    (φ : ℝ → L2v c)
    (hφ_ae : ∀ τ : ℝ, (φ τ : Plane → Vec2) =ᵐ[cellμ c]
      toVecSlice (TailPeriodizeAux.qPeriodizeVec c Ξ (t₀ + τ))) :
    Continuous φ := by
  obtain ⟨_a0, _b0, R0, _, _, hR0, hbox0⟩ := TailPeriodizeAux.coordTest_box (hΞ 0)
  obtain ⟨_a1, _b1, R1, _, _, _, hbox1⟩ := TailPeriodizeAux.coordTest_box (hΞ 1)
  let R : ℝ := max R0 R1
  have hR_pos : 0 < R := lt_of_lt_of_le hR0 (le_max_left R0 R1)
  have hbox : ∀ (i : Fin 2) (x : Coord), (R < |x.2.1| ∨ R < |x.2.2|) → Ξ x i = 0 := by
    intro i x hx
    fin_cases i
    · refine (hbox0 x ?_).1
      rcases hx with hq | hη
      · exact Or.inr (Or.inl ((le_max_left R0 R1).trans_lt hq))
      · exact Or.inr (Or.inr ((le_max_left R0 R1).trans_lt hη))
    · refine (hbox1 x ?_).1
      rcases hx with hq | hη
      · exact Or.inr (Or.inl ((le_max_right R0 R1).trans_lt hq))
      · exact Or.inr (Or.inr ((le_max_right R0 R1).trans_lt hη))
  have hbdd_i : ∀ i : Fin 2, ∃ M : ℝ, 0 ≤ M ∧ ∀ x : Coord, |Ξ x i| ≤ M := by
    intro i
    obtain ⟨M_i, hM_i⟩ := (hΞ i).compact.exists_bound_of_continuousOn
      (hΞ i).smooth.continuous.continuousOn
    refine ⟨max 0 M_i, le_max_left 0 M_i, fun x => ?_⟩
    by_cases hx : x ∈ tsupport (fun w => Ξ w i)
    · exact (Real.norm_eq_abs _ ▸ hM_i x hx).trans (le_max_right 0 M_i)
    · rw [image_eq_zero_of_notMem_tsupport hx, abs_zero]
      exact le_max_left 0 M_i
  obtain ⟨M0_v, hM0_nn, hM0_b⟩ := hbdd_i 0
  obtain ⟨M1_v, hM1_nn, hM1_b⟩ := hbdd_i 1
  let M_pt : ℝ := M0_v + M1_v
  have hM_pt_nn : 0 ≤ M_pt := add_nonneg hM0_nn hM1_nn
  obtain ⟨K, hK⟩ := exists_nat_gt ((c / 2 + R) / c + 1)
  let I_fin : Finset ℤ := Finset.Icc (-(K : ℤ)) (K : ℤ)
  let B_box : Set Plane := Ico (-(c / 2)) (c / 2) ×ˢ Icc (-R) R
  have hB_meas : MeasurableSet B_box := measurableSet_Ico.prod measurableSet_Icc
  have hB_fin : volume B_box < ⊤ := by
    dsimp [B_box]
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, Real.volume_Icc]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  let F_fin : ℝ → Plane → Vec2 := fun τ y =>
    ∑ k ∈ I_fin, toVecSlice (fun w i => Ξ (t₀ + τ, (w.1 + (k : ℝ) * c, w.2)) i) y
  have hF_eq_cell : ∀ (τ : ℝ) {y : Plane}, y ∈ B0579.cell c →
      toVecSlice (TailPeriodizeAux.qPeriodizeVec c Ξ (t₀ + τ)) y = F_fin τ y := by
    intro τ y hy
    ext i
    have hsum : TailPeriodizeAux.qPeriodize c (fun x => Ξ x i) (t₀ + τ) y =
        ∑ k ∈ I_fin, Ξ (t₀ + τ, (y.1 + (k : ℝ) * c, y.2)) i :=
      tsum_eq_sum fun k hk =>
        hbox i _ (Or.inl (shift_outside_cell_box hc hK hy hk))
    simp [toVecSlice, TailPeriodizeAux.qPeriodizeVec, F_fin, hsum]
  have hF_zero_out : ∀ (τ : ℝ) {y : Plane}, y ∈ B0579.cell c → y ∉ B_box → F_fin τ y = 0 := by
    intro τ y hy hnotB
    have hnot_η : y.2 ∉ Icc (-R) R := fun hη => hnotB ⟨hy.1, hη⟩
    have hη_gt : R < |y.2| := by
      by_contra hle; push Not at hle; exact hnot_η (abs_le.1 hle)
    ext i
    simp only [F_fin, toVecSlice]
    have h0 : ∀ k ∈ I_fin, Ξ (t₀ + τ, (y.1 + (k : ℝ) * c, y.2)) i = 0 :=
      fun k _ => hbox i _ (Or.inr hη_gt)
    simp [Finset.sum_eq_zero h0]
  let C_dom : ℝ := (I_fin.card : ℝ) * M_pt
  have hC_dom_nn : 0 ≤ C_dom := by positivity
  have hF_norm_le : ∀ (τ : ℝ) (y : Plane), ‖F_fin τ y‖ ≤ C_dom := by
    intro τ y
    refine (norm_sum_le I_fin _).trans ?_
    have hterm : ∀ k ∈ I_fin,
        ‖toVecSlice (fun w i => Ξ (t₀ + τ, (w.1 + (k : ℝ) * c, w.2)) i) y‖ ≤ M_pt := by
      intro k _
      have hsq : ‖toVecSlice (fun w i => Ξ (t₀ + τ, (w.1 + (k : ℝ) * c, w.2)) i) y‖ ^ 2 ≤
          M_pt ^ 2 := by
        rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
        simp only [toVecSlice, WithLp.ofLp_toLp, Real.norm_eq_abs]
        have b0 := hM0_b (t₀ + τ, (y.1 + (k : ℝ) * c, y.2))
        have b1 := hM1_b (t₀ + τ, (y.1 + (k : ℝ) * c, y.2))
        have s0 : |Ξ (t₀ + τ, (y.1 + (k : ℝ) * c, y.2)) 0| ^ 2 ≤ M0_v ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) b0 2
        have s1 : |Ξ (t₀ + τ, (y.1 + (k : ℝ) * c, y.2)) 1| ^ 2 ≤ M1_v ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) b1 2
        dsimp [M_pt]
        nlinarith [hM0_nn, hM1_nn]
      nlinarith [norm_nonneg (toVecSlice (fun w i => Ξ (t₀ + τ, (w.1 + (k : ℝ) * c, w.2)) i) y)]
    simpa [C_dom] using Finset.sum_le_card_nsmul I_fin _ M_pt hterm
  have hF_cont_tau : ∀ y : Plane, Continuous (fun τ : ℝ => F_fin τ y) := by
    intro y
    refine continuous_finsetSum I_fin fun k _ => ?_
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
    exact (hΞ i).smooth.continuous.comp ((continuous_const.add continuous_id).prodMk continuous_const)
  have hF_cont_y : ∀ τ : ℝ, Continuous (F_fin τ) := by
    intro τ
    refine continuous_finsetSum I_fin fun k _ => ?_
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
    exact (hΞ i).smooth.continuous.comp
      (continuous_const.prodMk ((continuous_fst.add continuous_const).prodMk continuous_snd))
  rw [continuous_iff_continuousAt]
  intro τ₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hnorm_eq : ∀ τ : ℝ, ‖φ τ - φ τ₀‖ =
      Real.sqrt (∫ y : Plane, ‖F_fin τ y - F_fin τ₀ y‖ ^ 2 ∂(cellμ c)) := by
    intro τ
    rw [norm_eq_sqrt_real_inner (φ τ - φ τ₀)]
    congr 1
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    have hcell_mem : ∀ᵐ y ∂(cellμ c), y ∈ B0579.cell c := by
      rw [← restrict_b0579_cell_eq_cellμ]
      exact ae_restrict_mem (B0579.measurableSet_cell c)
    filter_upwards [Lp.coeFn_sub (φ τ) (φ τ₀), hφ_ae τ, hφ_ae τ₀, hcell_mem]
      with y hsub h1 h2 hy
    change ⟪((φ τ - φ τ₀ : L2v c) : Plane → Vec2) y, ((φ τ - φ τ₀ : L2v c) : Plane → Vec2) y⟫_ℝ = _
    rw [hsub, Pi.sub_apply, h1, h2, hF_eq_cell τ hy, hF_eq_cell τ₀ hy, real_inner_self_eq_norm_sq]
  simp_rw [hnorm_eq]
  rw [← Real.sqrt_zero]
  refine (Real.continuous_sqrt.tendsto 0).comp ?_
  let dom : Plane → ℝ := B_box.indicator (fun _ => (2 * C_dom) ^ 2)
  have hdom_int_vol : Integrable dom volume :=
    (integrable_indicator_iff hB_meas).2 (integrableOn_const hB_fin.ne enorm_ne_top)
  have hdom_int : Integrable dom (cellμ c) := by
    rw [← restrict_b0579_cell_eq_cellμ]; exact hdom_int_vol.restrict
  have hcell_mem : ∀ᵐ y ∂(cellμ c), y ∈ B0579.cell c := by
    rw [← restrict_b0579_cell_eq_cellμ]
    exact ae_restrict_mem (B0579.measurableSet_cell c)
  have hlim := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := cellμ c)
    (F := fun τ y => ‖F_fin τ y - F_fin τ₀ y‖ ^ 2)
    (bound := dom)
    (f := fun _ => (0 : ℝ))
    (Eventually.of_forall fun τ =>
      ((((hF_cont_y τ).sub (hF_cont_y τ₀)).norm).pow 2).aestronglyMeasurable)
    (Eventually.of_forall fun τ => hcell_mem.mono fun y hy => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      by_cases hyB : y ∈ B_box
      · dsimp [dom]; rw [indicator_of_mem hyB]
        have htri : ‖F_fin τ y - F_fin τ₀ y‖ ≤ 2 * C_dom :=
          (norm_sub_le _ _).trans (by linarith [hF_norm_le τ y, hF_norm_le τ₀ y])
        exact pow_le_pow_left₀ (norm_nonneg _) htri 2
      · dsimp [dom]; rw [indicator_of_notMem hyB, hF_zero_out τ hy hyB, hF_zero_out τ₀ hy hyB]
        simp)
    hdom_int
    (Eventually.of_forall fun y => by
      have hcy : Continuous (fun τ : ℝ => ‖F_fin τ y - F_fin τ₀ y‖ ^ 2) :=
        (((hF_cont_tau y).sub continuous_const).norm).pow 2
      simpa using hcy.tendsto τ₀)
  simpa using hlim

private lemma hasDerivAt_qPeriodize_L2 {c t₀ : ℝ} (hc : 0 < c)
    {Ψ : Coord → Fin 2 → ℝ} (hΨ : IsPlanarSolTest Ψ)
    (φ₀ φ₀' : ℝ → L2v c)
    (hφ₀_ae : ∀ τ : ℝ, (φ₀ τ : Plane → Vec2) =ᵐ[cellμ c]
      toVecSlice (TailPeriodizeAux.qPeriodizeVec c Ψ (t₀ + τ)))
    (hφ₀'_ae : ∀ τ : ℝ, (φ₀' τ : Plane → Vec2) =ᵐ[cellμ c]
      toVecSlice (TailPeriodizeAux.qPeriodizeVec c (fun x i => cpd 0 (fun w => Ψ w i) x) (t₀ + τ)))
    (τ₀ : ℝ) :
    HasDerivAt φ₀ (φ₀' τ₀) τ₀ := by
  let Ψ' : Coord → Fin 2 → ℝ := fun x i => cpd 0 (fun w => Ψ w i) x
  have hΨ' : IsPlanarSolTest Ψ' := isPlanarSolTest_cpd0 hΨ
  obtain ⟨_a0, _b0, R0, _, _, hR0, hbox0⟩ := TailPeriodizeAux.coordTest_box (hΨ.smooth 0)
  obtain ⟨_a1, _b1, R1, _, _, _, hbox1⟩ := TailPeriodizeAux.coordTest_box (hΨ.smooth 1)
  let R : ℝ := max R0 R1
  have hR_pos : 0 < R := lt_of_lt_of_le hR0 (le_max_left R0 R1)
  have hbox : ∀ (i : Fin 2) (x : Coord), (R < |x.2.1| ∨ R < |x.2.2|) →
      Ψ x i = 0 ∧ Ψ' x i = 0 := by
    intro i x hx
    fin_cases i
    · have h := hbox0 x (hx.elim (fun hq => Or.inr (Or.inl ((le_max_left R0 R1).trans_lt hq)))
        (fun hη => Or.inr (Or.inr ((le_max_left R0 R1).trans_lt hη))))
      exact ⟨h.1, h.2 0⟩
    · have h := hbox1 x (hx.elim (fun hq => Or.inr (Or.inl ((le_max_right R0 R1).trans_lt hq)))
        (fun hη => Or.inr (Or.inr ((le_max_right R0 R1).trans_lt hη))))
      exact ⟨h.1, h.2 0⟩
  have hbdd_i : ∀ i : Fin 2, ∃ M : ℝ, 0 ≤ M ∧ ∀ x : Coord, |Ψ' x i| ≤ M := by
    intro i
    obtain ⟨M_i, hM_i⟩ := (hΨ'.smooth i).compact.exists_bound_of_continuousOn
      (hΨ'.smooth i).smooth.continuous.continuousOn
    refine ⟨max 0 M_i, le_max_left 0 M_i, fun x => ?_⟩
    by_cases hx : x ∈ tsupport (fun w => Ψ' w i)
    · exact (Real.norm_eq_abs _ ▸ hM_i x hx).trans (le_max_right 0 M_i)
    · rw [image_eq_zero_of_notMem_tsupport hx, abs_zero]
      exact le_max_left 0 M_i
  obtain ⟨M0_v, hM0_nn, hM0_b⟩ := hbdd_i 0
  obtain ⟨M1_v, hM1_nn, hM1_b⟩ := hbdd_i 1
  let M_pt : ℝ := M0_v + M1_v
  have hM_pt_nn : 0 ≤ M_pt := add_nonneg hM0_nn hM1_nn
  obtain ⟨K, hK⟩ := exists_nat_gt ((c / 2 + R) / c + 1)
  let I_fin : Finset ℤ := Finset.Icc (-(K : ℤ)) (K : ℤ)
  let B_box : Set Plane := Ico (-(c / 2)) (c / 2) ×ˢ Icc (-R) R
  have hB_meas : MeasurableSet B_box := measurableSet_Ico.prod measurableSet_Icc
  have hB_fin : volume B_box < ⊤ := by
    dsimp [B_box]
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, Real.volume_Icc]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  let F0 : ℝ → Plane → Vec2 := fun τ y =>
    ∑ k ∈ I_fin, toVecSlice (fun w i => Ψ (t₀ + τ, (w.1 + (k : ℝ) * c, w.2)) i) y
  let F1 : ℝ → Plane → Vec2 := fun τ y =>
    ∑ k ∈ I_fin, toVecSlice (fun w i => Ψ' (t₀ + τ, (w.1 + (k : ℝ) * c, w.2)) i) y
  have hF0_eq : ∀ (τ : ℝ) {y : Plane}, y ∈ B0579.cell c →
      toVecSlice (TailPeriodizeAux.qPeriodizeVec c Ψ (t₀ + τ)) y = F0 τ y := by
    intro τ y hy; ext i
    have hs : TailPeriodizeAux.qPeriodize c (fun x => Ψ x i) (t₀ + τ) y =
        ∑ k ∈ I_fin, Ψ (t₀ + τ, (y.1 + (k : ℝ) * c, y.2)) i :=
      tsum_eq_sum fun k hk => (hbox i _ (Or.inl (shift_outside_cell_box hc hK hy hk))).1
    simp [toVecSlice, TailPeriodizeAux.qPeriodizeVec, F0, hs]
  have hF1_eq : ∀ (τ : ℝ) {y : Plane}, y ∈ B0579.cell c →
      toVecSlice (TailPeriodizeAux.qPeriodizeVec c Ψ' (t₀ + τ)) y = F1 τ y := by
    intro τ y hy; ext i
    have hs : TailPeriodizeAux.qPeriodize c (fun x => Ψ' x i) (t₀ + τ) y =
        ∑ k ∈ I_fin, Ψ' (t₀ + τ, (y.1 + (k : ℝ) * c, y.2)) i :=
      tsum_eq_sum fun k hk => (hbox i _ (Or.inl (shift_outside_cell_box hc hK hy hk))).2
    simp [toVecSlice, TailPeriodizeAux.qPeriodizeVec, F1, hs]
  have hF_zero_out : ∀ (τ : ℝ) {y : Plane}, y ∈ B0579.cell c → y ∉ B_box →
      F0 τ y = 0 ∧ F1 τ y = 0 := by
    intro τ y hy hnotB
    have hnot_η : y.2 ∉ Icc (-R) R := fun hη => hnotB ⟨hy.1, hη⟩
    have hη_gt : R < |y.2| := by
      by_contra hle; push Not at hle; exact hnot_η (abs_le.1 hle)
    refine ⟨Finset.sum_eq_zero fun k _ => ?_, Finset.sum_eq_zero fun k _ => ?_⟩
    · ext i
      exact (hbox i (t₀ + τ, (y.1 + (k : ℝ) * c, y.2)) (Or.inr hη_gt)).1
    · ext i
      exact (hbox i (t₀ + τ, (y.1 + (k : ℝ) * c, y.2)) (Or.inr hη_gt)).2
  have hF_deriv_pt : ∀ (y : Plane) (τ : ℝ), HasDerivAt (fun r => F0 r y) (F1 τ y) τ := by
    intro y τ
    refine HasDerivAt.fun_sum fun k _ => ?_
    have hscalar : ∀ i : Fin 2,
        HasDerivAt (fun r : ℝ => Ψ (t₀ + r, (y.1 + (k : ℝ) * c, y.2)) i)
          (Ψ' (t₀ + τ, (y.1 + (k : ℝ) * c, y.2)) i) τ := by
      intro i
      let γ : ℝ → Coord := fun r => (t₀ + r, (y.1 + (k : ℝ) * c, y.2))
      have hγ : HasDerivAt γ (cdir 0) τ := by
        have h1 : HasDerivAt (fun r : ℝ => t₀ + r) 1 τ := (hasDerivAt_id τ).const_add t₀
        exact h1.prodMk (hasDerivAt_const τ (y.1 + (k : ℝ) * c, y.2))
      have hf : HasFDerivAt (fun w => Ψ w i) (fderiv ℝ (fun w => Ψ w i) (γ τ)) (γ τ) :=
        (((hΨ.smooth i).smooth.differentiable (by simp)) (γ τ)).hasFDerivAt
      exact hf.comp_hasDerivAt τ hγ
    have hpi : HasDerivAt
        (fun r : ℝ => fun i : Fin 2 => Ψ (t₀ + r, (y.1 + (k : ℝ) * c, y.2)) i)
        (fun i : Fin 2 => Ψ' (t₀ + τ, (y.1 + (k : ℝ) * c, y.2)) i) τ :=
      hasDerivAt_pi.2 hscalar
    exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt τ hpi
  let C_dom : ℝ := (I_fin.card : ℝ) * M_pt
  have hC_dom_nn : 0 ≤ C_dom := by positivity
  have hF1_norm_le : ∀ (τ : ℝ) (y : Plane), ‖F1 τ y‖ ≤ C_dom := by
    intro τ y
    refine (norm_sum_le I_fin _).trans ?_
    have hterm : ∀ k ∈ I_fin,
        ‖toVecSlice (fun w i => Ψ' (t₀ + τ, (w.1 + (k : ℝ) * c, w.2)) i) y‖ ≤ M_pt := by
      intro k _
      have hsq : ‖toVecSlice (fun w i => Ψ' (t₀ + τ, (w.1 + (k : ℝ) * c, w.2)) i) y‖ ^ 2 ≤
          M_pt ^ 2 := by
        rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
        simp only [toVecSlice, WithLp.ofLp_toLp, Real.norm_eq_abs]
        have b0 := hM0_b (t₀ + τ, (y.1 + (k : ℝ) * c, y.2))
        have b1 := hM1_b (t₀ + τ, (y.1 + (k : ℝ) * c, y.2))
        have s0 : |Ψ' (t₀ + τ, (y.1 + (k : ℝ) * c, y.2)) 0| ^ 2 ≤ M0_v ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) b0 2
        have s1 : |Ψ' (t₀ + τ, (y.1 + (k : ℝ) * c, y.2)) 1| ^ 2 ≤ M1_v ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) b1 2
        dsimp [M_pt]
        nlinarith [hM0_nn, hM1_nn]
      nlinarith [norm_nonneg (toVecSlice (fun w i => Ψ' (t₀ + τ, (w.1 + (k : ℝ) * c, w.2)) i) y)]
    simpa [C_dom] using Finset.sum_le_card_nsmul I_fin _ M_pt hterm
  have hslope_le : ∀ (y : Plane) (τ : ℝ), ‖slope (fun r => F0 r y) τ₀ τ‖ ≤ C_dom := by
    intro y τ
    rw [slope_def_module, norm_smul, Real.norm_eq_abs, abs_inv]
    by_cases hτ : τ = τ₀
    · simp [hτ, hC_dom_nn]
    · have hmvt : ‖F0 τ y - F0 τ₀ y‖ ≤ C_dom * ‖τ - τ₀‖ :=
        convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
          (fun r _ => (hF_deriv_pt y r).hasDerivWithinAt)
          (fun r _ => hF1_norm_le r y) (mem_univ τ₀) (mem_univ τ)
      have hpos : 0 < |τ - τ₀| := abs_pos.mpr (sub_ne_zero.mpr hτ)
      rw [Real.norm_eq_abs] at hmvt
      calc |τ - τ₀|⁻¹ * ‖F0 τ y - F0 τ₀ y‖
          ≤ |τ - τ₀|⁻¹ * (C_dom * |τ - τ₀|) :=
            mul_le_mul_of_nonneg_left hmvt (inv_nonneg.mpr hpos.le)
        _ = C_dom := by field_simp [hpos.ne']
  have hF0_cont_y : ∀ τ : ℝ, Continuous (F0 τ) := by
    intro τ
    refine continuous_finsetSum I_fin fun k _ => ?_
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
    exact (hΨ.smooth i).smooth.continuous.comp
      (continuous_const.prodMk ((continuous_fst.add continuous_const).prodMk continuous_snd))
  have hF1_cont_y : ∀ τ : ℝ, Continuous (F1 τ) := by
    intro τ
    refine continuous_finsetSum I_fin fun k _ => ?_
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
    exact (hΨ'.smooth i).smooth.continuous.comp
      (continuous_const.prodMk ((continuous_fst.add continuous_const).prodMk continuous_snd))
  rw [hasDerivAt_iff_tendsto_slope, tendsto_iff_norm_sub_tendsto_zero]
  have hcell_mem : ∀ᵐ y ∂(cellμ c), y ∈ B0579.cell c := by
    rw [← restrict_b0579_cell_eq_cellμ]
    exact ae_restrict_mem (B0579.measurableSet_cell c)
  have hnorm_eq : ∀ τ : ℝ, ‖slope φ₀ τ₀ τ - φ₀' τ₀‖ =
      Real.sqrt (∫ y : Plane, ‖slope (fun r => F0 r y) τ₀ τ - F1 τ₀ y‖ ^ 2 ∂(cellμ c)) := by
    intro τ
    rw [norm_eq_sqrt_real_inner (slope φ₀ τ₀ τ - φ₀' τ₀)]
    congr 1
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    have hsl_ae : (slope φ₀ τ₀ τ : Plane → Vec2) =ᵐ[cellμ c]
        fun y => (τ - τ₀)⁻¹ • ((φ₀ τ : Plane → Vec2) y - (φ₀ τ₀ : Plane → Vec2) y) := by
      rw [slope_def_module]
      filter_upwards [Lp.coeFn_smul (τ - τ₀)⁻¹ (φ₀ τ - φ₀ τ₀), Lp.coeFn_sub (φ₀ τ) (φ₀ τ₀)]
        with y hsm hsb
      rw [hsm, Pi.smul_apply, hsb, Pi.sub_apply]
    filter_upwards [Lp.coeFn_sub (slope φ₀ τ₀ τ) (φ₀' τ₀), hsl_ae,
      hφ₀_ae τ, hφ₀_ae τ₀, hφ₀'_ae τ₀, hcell_mem]
      with y hsub hsl h0t h0t0 h1t0 hy
    change ⟪((slope φ₀ τ₀ τ - φ₀' τ₀ : L2v c) : Plane → Vec2) y,
      ((slope φ₀ τ₀ τ - φ₀' τ₀ : L2v c) : Plane → Vec2) y⟫_ℝ = _
    rw [hsub, Pi.sub_apply, hsl, h0t, h0t0, h1t0,
      hF0_eq τ hy, hF0_eq τ₀ hy, hF1_eq τ₀ hy, slope_def_module, real_inner_self_eq_norm_sq]
  simp_rw [hnorm_eq]
  rw [← Real.sqrt_zero]
  refine (Real.continuous_sqrt.tendsto 0).comp ?_
  let dom : Plane → ℝ := B_box.indicator (fun _ => (2 * C_dom) ^ 2)
  have hdom_int_vol : Integrable dom volume :=
    (integrable_indicator_iff hB_meas).2 (integrableOn_const hB_fin.ne enorm_ne_top)
  have hdom_int : Integrable dom (cellμ c) := by
    rw [← restrict_b0579_cell_eq_cellμ]; exact hdom_int_vol.restrict
  have hlim := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := cellμ c)
    (F := fun τ y => ‖slope (fun r => F0 r y) τ₀ τ - F1 τ₀ y‖ ^ 2)
    (bound := dom)
    (f := fun _ => (0 : ℝ))
    (Eventually.of_forall fun τ => by
      have hc_sl : Continuous (fun y : Plane => slope (fun r => F0 r y) τ₀ τ) := by
        simp_rw [slope_def_module]
        exact ((hF0_cont_y τ).sub (hF0_cont_y τ₀)).const_smul (τ - τ₀)⁻¹
      exact (((hc_sl.sub (hF1_cont_y τ₀)).norm).pow 2).aestronglyMeasurable)
    (Eventually.of_forall fun τ => hcell_mem.mono fun y hy => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      by_cases hyB : y ∈ B_box
      · dsimp [dom]; rw [indicator_of_mem hyB]
        have htri : ‖slope (fun r => F0 r y) τ₀ τ - F1 τ₀ y‖ ≤ 2 * C_dom :=
          (norm_sub_le _ _).trans (by linarith [hslope_le y τ, hF1_norm_le τ₀ y])
        exact pow_le_pow_left₀ (norm_nonneg _) htri 2
      · dsimp [dom]
        rw [indicator_of_notMem hyB]
        have h0t := (hF_zero_out τ hy hyB).1
        have h0t0 := (hF_zero_out τ₀ hy hyB).1
        have h1t0 := (hF_zero_out τ₀ hy hyB).2
        rw [slope_def_module, h0t, h0t0, h1t0]
        simp)
    hdom_int
    (Eventually.of_forall fun y => by
      have hdy := hasDerivAt_iff_tendsto_slope.mp (hF_deriv_pt y τ₀)
      simpa using (((hdy.sub_const (F1 τ₀ y)).norm).pow 2))
  simpa using hlim

private lemma hasDerivAt_inner_moving_heat {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    {Φ : ℝ → Plane → Vec2} (hΦ : ∀ τ : ℝ, IsRealSolCylTest c (Φ τ))
    {φ₀' : ℝ → L2v c}
    (hderiv_φ₀ : ∀ τ : ℝ,
      HasDerivAt (fun r => cylSmoothToL2 (isCylSmooth_of_solTest (hΦ r))) (φ₀' τ) τ)
    (σ : ℝ) (x : L2v c) {τ₀ : ℝ} (hστ₀ : σ < τ₀) :
    HasDerivAt
      (fun τ => ⟪cylSmoothToL2 (isCylSmooth_of_solTest (hΦ τ)),
        centeredHeatVecL2CLM hc (ν * (τ - σ)) x⟫_ℝ)
      (⟪φ₀' τ₀, centeredHeatVecL2CLM hc (ν * (τ₀ - σ)) x⟫_ℝ -
        ν * (⟪cylSmoothToL2 ((isCylSmooth_of_solTest (hΦ τ₀)).dir ((1 : ℝ), (0 : ℝ))),
              DHeatCLM hc 0 (ν * (τ₀ - σ)) x⟫_ℝ +
            ⟪cylSmoothToL2 ((isCylSmooth_of_solTest (hΦ τ₀)).dir ((0 : ℝ), (1 : ℝ))),
              DHeatCLM hc 1 (ν * (τ₀ - σ)) x⟫_ℝ))
      τ₀ := by
  let φ₀ : ℝ → L2v c := fun r => cylSmoothToL2 (isCylSmooth_of_solTest (hΦ r))
  let H : ℝ → L2v c := fun r => centeredHeatVecL2CLM hc (ν * (r - σ)) x
  have hH_cont : Continuous H :=
    (continuous_centeredHeatVecL2CLM_apply hc x).comp
      (continuous_const.mul (continuous_id.sub continuous_const))
  have hage_pos : 0 < ν * (τ₀ - σ) := mul_pos hν (sub_pos.mpr hστ₀)
  have hlin : HasDerivAt (fun r : ℝ => ν * (r - σ)) ν τ₀ := by
    simpa using ((hasDerivAt_id τ₀).sub_const σ).const_mul ν
  have hH_deriv : HasDerivAt (fun r => ⟪φ₀ τ₀, H r⟫_ℝ)
      (-ν * (⟪cylSmoothToL2 ((isCylSmooth_of_solTest (hΦ τ₀)).dir ((1 : ℝ), (0 : ℝ))),
            DHeatCLM hc 0 (ν * (τ₀ - σ)) x⟫_ℝ +
          ⟪cylSmoothToL2 ((isCylSmooth_of_solTest (hΦ τ₀)).dir ((0 : ℝ), (1 : ℝ))),
            DHeatCLM hc 1 (ν * (τ₀ - σ)) x⟫_ℝ)) τ₀ := by
    have hd := (hasDerivAt_inner_centeredHeatVecL2CLM hc hage_pos
      (isCylSmooth_of_solTest (hΦ τ₀)) x).comp τ₀ hlin
    exact hd.congr_deriv (by ring)
  rw [hasDerivAt_iff_tendsto_slope]
  have hsl_eq : slope (fun r => ⟪φ₀ r, H r⟫_ℝ) τ₀ =
      fun r => ⟪slope φ₀ τ₀ r, H r⟫_ℝ + slope (fun r => ⟪φ₀ τ₀, H r⟫_ℝ) τ₀ r := by
    funext r
    rw [slope_def_field, slope_def_module, slope_def_field, real_inner_smul_left]
    have hsplit : ⟪φ₀ r, H r⟫_ℝ - ⟪φ₀ τ₀, H τ₀⟫_ℝ =
        ⟪φ₀ r - φ₀ τ₀, H r⟫_ℝ + (⟪φ₀ τ₀, H r⟫_ℝ - ⟪φ₀ τ₀, H τ₀⟫_ℝ) := by
      rw [inner_sub_left]; ring
    rw [hsplit]
    ring
  rw [hsl_eq]
  have ht1 : Tendsto (fun r => ⟪slope φ₀ τ₀ r, H r⟫_ℝ) (𝓝[≠] τ₀)
      (𝓝 ⟪φ₀' τ₀, H τ₀⟫_ℝ) :=
    (hasDerivAt_iff_tendsto_slope.mp (hderiv_φ₀ τ₀)).inner
      ((hH_cont.tendsto τ₀).mono_left nhdsWithin_le_nhds)
  have ht2 := hasDerivAt_iff_tendsto_slope.mp hH_deriv
  simpa [H, sub_eq_add_neg] using ht1.add ht2

private lemma master_heat_adjoint_ftc {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    {Φ : ℝ → Plane → Vec2} (hΦ : ∀ τ : ℝ, IsRealSolCylTest c (Φ τ))
    (hφ1_zero : cylSmoothToL2 (isCylSmooth_of_solTest (hΦ 1)) = 0)
    {φ₀' : ℝ → L2v c} (hφ₀'_cont : Continuous φ₀')
    (hφq_cont : Continuous (fun τ =>
      cylSmoothToL2 ((isCylSmooth_of_solTest (hΦ τ)).dir ((1 : ℝ), (0 : ℝ)))))
    (hφη_cont : Continuous (fun τ =>
      cylSmoothToL2 ((isCylSmooth_of_solTest (hΦ τ)).dir ((0 : ℝ), (1 : ℝ)))))
    (hderiv_φ₀ : ∀ τ : ℝ,
      HasDerivAt (fun r => cylSmoothToL2 (isCylSmooth_of_solTest (hΦ r))) (φ₀' τ) τ)
    {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) 1) (x : L2v c) :
    ∫ τ in σ..1,
      (-⟪φ₀' τ, centeredHeatVecL2CLM hc (ν * (τ - σ)) x⟫_ℝ +
        ν * (⟪cylSmoothToL2 ((isCylSmooth_of_solTest (hΦ τ)).dir ((1 : ℝ), (0 : ℝ))),
              DHeatCLM hc 0 (ν * (τ - σ)) x⟫_ℝ +
            ⟪cylSmoothToL2 ((isCylSmooth_of_solTest (hΦ τ)).dir ((0 : ℝ), (1 : ℝ))),
              DHeatCLM hc 1 (ν * (τ - σ)) x⟫_ℝ)) =
      ⟪cylSmoothToL2 (isCylSmooth_of_solTest (hΦ σ)), x⟫_ℝ := by
  let φ₀ : ℝ → L2v c := fun τ => cylSmoothToL2 (isCylSmooth_of_solTest (hΦ τ))
  let φq : ℝ → L2v c := fun τ =>
    cylSmoothToL2 ((isCylSmooth_of_solTest (hΦ τ)).dir ((1 : ℝ), (0 : ℝ)))
  let φη : ℝ → L2v c := fun τ =>
    cylSmoothToL2 ((isCylSmooth_of_solTest (hΦ τ)).dir ((0 : ℝ), (1 : ℝ)))
  let L : ℝ → ℝ := fun τ =>
    -⟪φ₀' τ, centeredHeatVecL2CLM hc (ν * (τ - σ)) x⟫_ℝ +
      ν * (⟪φq τ, DHeatCLM hc 0 (ν * (τ - σ)) x⟫_ℝ +
          ⟪φη τ, DHeatCLM hc 1 (ν * (τ - σ)) x⟫_ℝ)
  let F : ℝ → ℝ := fun τ => ⟪φ₀ τ, centeredHeatVecL2CLM hc (ν * (τ - σ)) x⟫_ℝ
  have hφ₀_cont : Continuous φ₀ :=
    continuous_iff_continuousAt.2 fun τ => (hderiv_φ₀ τ).continuousAt
  have hF_cont : Continuous F :=
    hφ₀_cont.inner ((continuous_centeredHeatVecL2CLM_apply hc x).comp
      (continuous_const.mul (continuous_id.sub continuous_const)))
  have hF_deriv : ∀ τ ∈ Ioo σ 1, HasDerivAt F (-L τ) τ := by
    intro τ hτ
    exact (hasDerivAt_inner_moving_heat hc hν hΦ hderiv_φ₀ σ x hτ.1).congr_deriv (by dsimp [L, φq, φη]; ring)
  by_cases hσ1 : σ = 1
  · subst hσ1
    rw [intervalIntegral.integral_same, hφ1_zero, inner_zero_left]
  · have hσ_lt1 : σ < 1 := lt_of_le_of_ne hσ.2 hσ1
    obtain ⟨M0, hM0⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (f := fun τ => ‖φ₀' τ‖ + ‖φq τ‖ + ‖φη τ‖)
      ((hφ₀'_cont.norm.add hφq_cont.norm).add hφη_cont.norm).continuousOn
    let Mφ : ℝ := max 0 M0
    have hMφ_nn : 0 ≤ Mφ := le_max_left 0 M0
    have hMφ_b : ∀ τ ∈ Icc (0 : ℝ) 1, ‖φ₀' τ‖ + ‖φq τ‖ + ‖φη τ‖ ≤ Mφ := by
      intro τ hτ
      have h := hM0 τ hτ
      rw [Real.norm_of_nonneg (by positivity)] at h
      exact h.trans (le_max_right 0 M0)
    have hint_negL : IntervalIntegrable (fun τ => -L τ) volume σ 1 := by
      rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hσ.2]
      have hcont_Ioo : ContinuousOn (fun τ => -L τ) (Ioo σ 1) := by
        have hc0 : ContinuousOn (fun τ => ⟪φ₀' τ, centeredHeatVecL2CLM hc (ν * (τ - σ)) x⟫_ℝ) (Ioo σ 1) :=
          (hφ₀'_cont.inner ((continuous_centeredHeatVecL2CLM_apply hc x).comp
            (continuous_const.mul (continuous_id.sub continuous_const)))).continuousOn
        have hcj : ∀ j : Fin 2, ContinuousOn (fun τ => DHeatCLM hc j (ν * (τ - σ)) x) (Ioo σ 1) :=
          fun j => (continuousOn_DHeatCLM_apply hc j x).comp
            (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))
            (fun τ hτ => mul_pos hν (sub_pos.mpr hτ.1))
        exact (hc0.neg.add (continuousOn_const.mul
          ((hφq_cont.continuousOn.inner (hcj 0)).add (hφη_cont.continuousOn.inner (hcj 1))))).neg
      have hrp : IntervalIntegrable (fun τ : ℝ => (τ - σ) ^ (-(1 / 2 : ℝ))) volume σ 1 := by
        have h1 := (intervalIntegrable_rpow_neg_half 0 (1 - σ)).comp_sub_right σ
        simpa only [zero_add, sub_add_cancel] using h1
      let C_maj : ℝ := Mφ * ‖x‖ * (1 + ν * ((2 / Real.sqrt Real.pi) * ν ^ (-(1 / 2 : ℝ))))
      have hdom : IntegrableOn (fun τ : ℝ => C_maj * (τ - σ) ^ (-(1 / 2 : ℝ))) (Ioo σ 1) volume :=
        (intervalIntegrable_iff_integrableOn_Ioo_of_le hσ.2).1 (hrp.const_mul C_maj)
      refine hdom.mono' (hcont_Ioo.aestronglyMeasurable measurableSet_Ioo) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with τ hτ
      have hτ_Icc : τ ∈ Icc (0 : ℝ) 1 := ⟨hσ.1.trans hτ.1.le, hτ.2.le⟩
      have hpos_d : 0 < τ - σ := sub_pos.mpr hτ.1
      have hle1_d : τ - σ ≤ 1 := by linarith [hσ.1, hτ.2]
      have h1_le_rp : 1 ≤ (τ - σ) ^ (-(1 / 2 : ℝ)) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos hpos_d hle1_d (by norm_num)
      have hpos_age : 0 < ν * (τ - σ) := mul_pos hν hpos_d
      have hφb := hMφ_b τ hτ_Icc
      have b0 : |⟪φ₀' τ, centeredHeatVecL2CLM hc (ν * (τ - σ)) x⟫_ℝ| ≤ Mφ * ‖x‖ * 1 := by
        calc |⟪φ₀' τ, centeredHeatVecL2CLM hc (ν * (τ - σ)) x⟫_ℝ|
            ≤ ‖φ₀' τ‖ * ‖centeredHeatVecL2CLM hc (ν * (τ - σ)) x‖ :=
              Real.norm_eq_abs _ ▸ abs_real_inner_le_norm _ _
          _ ≤ ‖φ₀' τ‖ * (1 * ‖x‖) := mul_le_mul_of_nonneg_left
              ((ContinuousLinearMap.le_opNorm _ _).trans
                (mul_le_mul_of_nonneg_right (norm_centeredHeatVecL2CLM_le_one_all hc _) (norm_nonneg _)))
              (norm_nonneg _)
          _ ≤ Mφ * ‖x‖ * 1 := by
              nlinarith [norm_nonneg (φq τ), norm_nonneg (φη τ), norm_nonneg x]
      have bj : ∀ (j : Fin 2) (ψ : L2v c), ‖ψ‖ ≤ Mφ →
          |⟪ψ, DHeatCLM hc j (ν * (τ - σ)) x⟫_ℝ| ≤
            ‖ψ‖ * (heatDivL2Coeff (ν * (τ - σ)) * ‖x‖) := by
        intro j ψ _
        calc |⟪ψ, DHeatCLM hc j (ν * (τ - σ)) x⟫_ℝ|
            ≤ ‖ψ‖ * ‖DHeatCLM hc j (ν * (τ - σ)) x‖ :=
              Real.norm_eq_abs _ ▸ abs_real_inner_le_norm _ _
          _ ≤ ‖ψ‖ * (heatDivL2Coeff (ν * (τ - σ)) * ‖x‖) := mul_le_mul_of_nonneg_left
              ((ContinuousLinearMap.le_opNorm _ _).trans
                (mul_le_mul_of_nonneg_right (norm_DHeatCLM_le hc j hpos_age) (norm_nonneg _)))
              (norm_nonneg _)
      have bq := bj 0 (φq τ) (by linarith [norm_nonneg (φ₀' τ), norm_nonneg (φη τ)])
      have bη := bj 1 (φη τ) (by linarith [norm_nonneg (φ₀' τ), norm_nonneg (φq τ)])
      rw [Real.norm_eq_abs, abs_neg]
      have htri : |L τ| ≤ |⟪φ₀' τ, centeredHeatVecL2CLM hc (ν * (τ - σ)) x⟫_ℝ| +
          ν * (|⟪φq τ, DHeatCLM hc 0 (ν * (τ - σ)) x⟫_ℝ| +
              |⟪φη τ, DHeatCLM hc 1 (ν * (τ - σ)) x⟫_ℝ|) := by
        dsimp [L]
        calc |-⟪φ₀' τ, _⟫_ℝ + ν * (⟪φq τ, _⟫_ℝ + ⟪φη τ, _⟫_ℝ)|
            ≤ |-⟪φ₀' τ, _⟫_ℝ| + |ν * (⟪φq τ, _⟫_ℝ + ⟪φη τ, _⟫_ℝ)| := abs_add_le _ _
          _ = |⟪φ₀' τ, _⟫_ℝ| + ν * |⟪φq τ, _⟫_ℝ + ⟪φη τ, _⟫_ℝ| := by
              rw [abs_neg, abs_mul, abs_of_pos hν]
          _ ≤ |⟪φ₀' τ, _⟫_ℝ| + ν * (|⟪φq τ, _⟫_ℝ| + |⟪φη τ, _⟫_ℝ|) :=
              add_le_add le_rfl (mul_le_mul_of_nonneg_left (abs_add_le _ _) hν.le)
      have hqη_sum : ‖φq τ‖ + ‖φη τ‖ ≤ Mφ := by linarith [norm_nonneg (φ₀' τ)]
      have hcoeff_nn : 0 ≤ heatDivL2Coeff (ν * (τ - σ)) := by unfold heatDivL2Coeff; positivity
      calc |L τ|
          ≤ Mφ * ‖x‖ * 1 + ν * ((‖φq τ‖ + ‖φη τ‖) * (heatDivL2Coeff (ν * (τ - σ)) * ‖x‖)) := by
            have h12 : |⟪φq τ, DHeatCLM hc 0 (ν * (τ - σ)) x⟫_ℝ| +
                |⟪φη τ, DHeatCLM hc 1 (ν * (τ - σ)) x⟫_ℝ| ≤
                (‖φq τ‖ + ‖φη τ‖) * (heatDivL2Coeff (ν * (τ - σ)) * ‖x‖) := by
              linarith [bq, bη]
            exact htri.trans (add_le_add b0 (mul_le_mul_of_nonneg_left h12 hν.le))
        _ ≤ Mφ * ‖x‖ * (τ - σ) ^ (-(1 / 2 : ℝ)) +
              ν * (Mφ * (heatDivL2Coeff (ν * (τ - σ)) * ‖x‖)) := by
            refine add_le_add
              (mul_le_mul_of_nonneg_left h1_le_rp (mul_nonneg hMφ_nn (norm_nonneg x)))
              (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hqη_sum (mul_nonneg hcoeff_nn (norm_nonneg x))) hν.le)
        _ = C_maj * (τ - σ) ^ (-(1 / 2 : ℝ)) := by
            rw [heatDivL2Coeff_eq_singular hν hpos_d]
            dsimp [C_maj]
            ring
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hσ.2
      hF_cont.continuousOn hF_deriv hint_negL
    rw [intervalIntegral.integral_neg] at hftc
    have hF1 : F 1 = 0 := by dsimp [F, φ₀]; rw [hφ1_zero, inner_zero_left]
    have hFσ : F σ = ⟪φ₀ σ, x⟫_ℝ := by
      dsimp [F]
      rw [sub_self, mul_zero, centeredHeatVecL2CLM_eq_id_of_nonpos hc le_rfl,
        ContinuousLinearMap.id_apply]
    rw [hF1, hFσ, zero_sub] at hftc
    exact neg_inj.mp hftc

private lemma fubini_triangle_rpow_half_unit {C_ker : ℝ}
    {K : ℝ → ℝ → ℝ}
    (hK_contOn : ContinuousOn (fun p : ℝ × ℝ => K p.1 p.2)
      {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < 1})
    (hC_ker_nn : 0 ≤ C_ker)
    (hK_bdd : ∀ r s : ℝ, 0 < r → r < s → s < 1 → |K r s| ≤ C_ker * (s - r) ^ (-(1 / 2 : ℝ))) :
    Integrable (fun s => ∫ r in (0 : ℝ)..s, K r s) (volume.restrict (Ioo 0 1)) ∧
      (∫ r in Ioo (0 : ℝ) 1, ∫ s in r..1, K r s) =
        ∫ s in Ioo (0 : ℝ) 1, ∫ r in (0 : ℝ)..s, K r s := by
  let T_open : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < 1}
  have hT_open : IsOpen T_open :=
    (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_fst continuous_snd).inter
        (isOpen_lt continuous_snd continuous_const))
  let G : ℝ × ℝ → ℝ := T_open.indicator (fun p => K p.1 p.2)
  let μI : Measure ℝ := volume.restrict (Ioo 0 1)
  have hG_meas' : AEStronglyMeasurable G (volume.prod volume) := by
    rw [aestronglyMeasurable_indicator_iff hT_open.measurableSet, ← Measure.volume_eq_prod]
    exact hK_contOn.aestronglyMeasurable hT_open.measurableSet
  have hG_meas_I : AEStronglyMeasurable G (μI.prod μI) := by
    rw [Measure.prod_restrict]; exact hG_meas'.restrict
  have hG_int : Integrable G (μI.prod μI) := by
    rw [MeasureTheory.integrable_prod_iff hG_meas_I]
    have hslice_int : ∀ r ∈ Ioo (0 : ℝ) 1, Integrable (fun s => G (r, s)) μI ∧
        ∫ s, ‖G (r, s)‖ ∂μI ≤ C_ker * (2 * (1 - r) ^ (1 / 2 : ℝ)) := by
      intro r hr
      have hrp : IntervalIntegrable (fun σ : ℝ => σ ^ (-(1 / 2 : ℝ))) volume 0 (1 - r) :=
        intervalIntegrable_rpow_neg_half 0 (1 - r)
      have hrp_shift : IntervalIntegrable (fun s : ℝ => (s - r) ^ (-(1 / 2 : ℝ))) volume r 1 := by
        have h1 := hrp.comp_sub_right r
        simpa only [zero_add, sub_add_cancel] using h1
      have hrp_Ioo : IntegrableOn (fun s : ℝ => C_ker * (s - r) ^ (-(1 / 2 : ℝ))) (Ioo r 1) volume :=
        (intervalIntegrable_iff_integrableOn_Ioo_of_le hr.2.le).1 (hrp_shift.const_mul C_ker)
      let dom_r : ℝ → ℝ := (Ioo r 1).indicator (fun s => C_ker * (s - r) ^ (-(1 / 2 : ℝ)))
      have hdom_int_vol : Integrable dom_r volume :=
        (integrable_indicator_iff measurableSet_Ioo).2 hrp_Ioo
      have hdom_int : Integrable dom_r μI := hdom_int_vol.restrict
      have hG_slice_meas : AEStronglyMeasurable (fun s => G (r, s)) μI := by
        have heq_ind : (fun s => G (r, s)) = (Ioo r 1).indicator (fun s => K r s) := by
          funext s
          by_cases hs : s ∈ Ioo r 1
          · have hp : (r, s) ∈ T_open := ⟨hr.1, hs.1, hs.2⟩
            simp only [G, indicator_of_mem hp, indicator_of_mem hs]
          · have hp : (r, s) ∉ T_open := fun h => hs ⟨h.2.1, h.2.2⟩
            simp only [G, indicator_of_notMem hp, indicator_of_notMem hs]
        rw [heq_ind]
        have hc_s : ContinuousOn (fun s => K r s) (Ioo r 1) :=
          hK_contOn.comp (continuous_const.prodMk continuous_id).continuousOn
            (fun s hs => ⟨hr.1, hs.1, hs.2⟩)
        exact ((aestronglyMeasurable_indicator_iff measurableSet_Ioo).2
          (hc_s.aestronglyMeasurable measurableSet_Ioo)).restrict
      have hle_dom : ∀ s ∈ Ioo (0 : ℝ) 1, ‖G (r, s)‖ ≤ dom_r s := by
        intro s hs
        by_cases hsr : r < s
        · have hp : (r, s) ∈ T_open := ⟨hr.1, hsr, hs.2⟩
          have hs' : s ∈ Ioo r 1 := ⟨hsr, hs.2⟩
          dsimp only [G, dom_r]
          rw [indicator_of_mem hp, indicator_of_mem hs', Real.norm_eq_abs]
          exact hK_bdd r s hr.1 hsr hs.2
        · have hp : (r, s) ∉ T_open := fun h => hsr h.2.1
          have hs' : s ∉ Ioo r 1 := fun h => hsr h.1
          dsimp only [G, dom_r]
          rw [indicator_of_notMem hp, indicator_of_notMem hs', norm_zero]
      have hint_Gr : Integrable (fun s => G (r, s)) μI :=
        hdom_int.mono' hG_slice_meas (ae_restrict_of_forall_mem measurableSet_Ioo hle_dom)
      refine ⟨hint_Gr, ?_⟩
      calc ∫ s, ‖G (r, s)‖ ∂μI
          ≤ ∫ s, dom_r s ∂μI :=
            integral_mono_ae hint_Gr.norm hdom_int
              (ae_restrict_of_forall_mem measurableSet_Ioo hle_dom)
        _ ≤ ∫ s, dom_r s ∂volume :=
            setIntegral_le_integral hdom_int_vol (Eventually.of_forall fun s => by
              by_cases hs : s ∈ Ioo r 1
              · dsimp only [dom_r]; rw [indicator_of_mem hs]
                exact mul_nonneg hC_ker_nn (Real.rpow_nonneg (sub_pos.mpr hs.1).le _)
              · simp [dom_r, indicator_of_notMem hs])
        _ = ∫ s in Ioo r 1, C_ker * (s - r) ^ (-(1 / 2 : ℝ)) :=
            integral_indicator measurableSet_Ioo
        _ = C_ker * ∫ s in r..1, (s - r) ^ (-(1 / 2 : ℝ)) := by
            rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.2.le,
              intervalIntegral.integral_const_mul]
        _ = C_ker * (2 * (1 - r) ^ (1 / 2 : ℝ)) := by
            have hchg := intervalIntegral.integral_comp_sub_right
              (fun σ : ℝ => σ ^ (-(1 / 2 : ℝ))) r (a := r) (b := 1)
            simp only [sub_self] at hchg
            rw [hchg, integral_rpow (Or.inl (by norm_num)),
              show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num, Real.zero_rpow (by norm_num)]
            ring
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact (hslice_int r hr).1
    · have hfin : IsFiniteMeasure μI := ⟨by simp [μI, Real.volume_Ioo]⟩
      refine Integrable.of_bound hG_meas_I.norm.integral_prod_right' (2 * C_ker) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      refine (hslice_int r hr).2.trans ?_
      have hr1 : (1 - r) ^ (1 / 2 : ℝ) ≤ 1 :=
        Real.rpow_le_one (sub_pos.mpr hr.2).le (by linarith [hr.1]) (by norm_num)
      nlinarith
  have hfub := (MeasureTheory.integral_prod G hG_int).symm.trans
    (MeasureTheory.integral_prod_symm G hG_int)
  have hG_r : ∀ r ∈ Ioo (0 : ℝ) 1, ∫ s, G (r, s) ∂μI = ∫ s in r..1, K r s := by
    intro r hr
    have hsub_Ioo : Ioo r 1 ⊆ Ioo 0 1 := fun s hs => ⟨lt_trans hr.1 hs.1, hs.2⟩
    change ∫ s in Ioo 0 1, G (r, s) = _
    have hind_eq : ∫ s in Ioo 0 1, G (r, s) =
        ∫ s in Ioo 0 1, (Ioo r 1).indicator (fun s => K r s) s := by
      refine setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
      by_cases hsr : r < s
      · have hp : (r, s) ∈ T_open := ⟨hr.1, hsr, hs.2⟩
        have hs' : s ∈ Ioo r 1 := ⟨hsr, hs.2⟩
        simp only [G, indicator_of_mem hp, indicator_of_mem hs']
      · have hp : (r, s) ∉ T_open := fun h => hsr h.2.1
        have hs' : s ∉ Ioo r 1 := fun h => hsr h.1
        simp only [G, indicator_of_notMem hp, indicator_of_notMem hs']
    rw [hind_eq, setIntegral_indicator measurableSet_Ioo, inter_eq_self_of_subset_right hsub_Ioo,
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.2.le]
  have hG_s : ∀ s ∈ Ioo (0 : ℝ) 1, ∫ r, G (r, s) ∂μI = ∫ r in (0 : ℝ)..s, K r s := by
    intro s hs
    have hsub_Ioo : Ioo 0 s ⊆ Ioo 0 1 := fun r hr => ⟨hr.1, lt_trans hr.2 hs.2⟩
    change ∫ r in Ioo 0 1, G (r, s) = _
    have hind_eq : ∫ r in Ioo 0 1, G (r, s) =
        ∫ r in Ioo 0 1, (Ioo 0 s).indicator (fun r => K r s) r := by
      refine setIntegral_congr_fun measurableSet_Ioo fun r hr => ?_
      by_cases hrs : r < s
      · have hp : (r, s) ∈ T_open := ⟨hr.1, hrs, hs.2⟩
        have hr' : r ∈ Ioo 0 s := ⟨hr.1, hrs⟩
        simp only [G, indicator_of_mem hp, indicator_of_mem hr']
      · have hp : (r, s) ∉ T_open := fun h => hrs h.2.1
        have hr' : r ∉ Ioo 0 s := fun h => hrs h.2
        simp only [G, indicator_of_notMem hp, indicator_of_notMem hr']
    rw [hind_eq, setIntegral_indicator measurableSet_Ioo, inter_eq_self_of_subset_right hsub_Ioo,
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hs.1.le]
  have hint_G_right : Integrable (fun s => ∫ r, G (r, s) ∂μI) μI :=
    hG_int.integral_prod_right
  refine ⟨hint_G_right.congr (ae_restrict_of_forall_mem measurableSet_Ioo hG_s), ?_⟩
  have hL : ∫ r in Ioo 0 1, ∫ s in r..1, K r s = ∫ r, (∫ s, G (r, s) ∂μI) ∂μI :=
    setIntegral_congr_fun measurableSet_Ioo fun r hr => (hG_r r hr).symm
  have hR : ∫ s, (∫ r, G (r, s) ∂μI) ∂μI = ∫ s in Ioo 0 1, ∫ r in (0 : ℝ)..s, K r s :=
    setIntegral_congr_fun measurableSet_Ioo hG_s
  exact hL.trans (hfub.trans hR)

/-! ## 6. Proof of `RealCylUnitOseenStep` -/

private lemma unitStep_weak_pde
    {p : Params} {d dm dp t₀ : ℝ} (hbg : BgRegime p d dm dp) (ht₀ : 0 < t₀)
    {g₀ gq₀ gη₀ : Coord → Fin 2 → ℝ}
    (hg_sm : StronglyMeasurable g₀)
    (hg0_per : ∀ x : Coord, g₀ (qShift p.c x) = g₀ x)
    (hg_int : (∫⁻ s in Ioo t₀ (t₀ + 1),
      sliceH1Norm p.c (ofRealProf g₀) (ofRealProf gq₀) (ofRealProf gη₀) s) < ⊤)
    (u_sol : H1Sol p.c)
    {G : ℝ → H1Sol p.c}
    (hG0_sm : StronglyMeasurable (fun σ : ℝ => val0CLM p.c (G σ)))
    (hGq_sm : StronglyMeasurable (fun σ : ℝ => dqCLM p.c (G σ)))
    (hGη_sm : StronglyMeasurable (fun σ : ℝ => detaCLM p.c (G σ)))
    (hG_sm : StronglyMeasurable G)
    (hG_int : IntegrableOn G (Icc 0 1) volume)
    (hG_ae : ∀ τ : ℝ, (val0CLM p.c (G τ) : Plane → Vec2) =ᵐ[cellμ p.c]
      toVecSlice (fun y => g₀ (t₀ + τ, y)))
    {U : ℝ → H1Sol p.c}
    (hU_cont : ContinuousOn U (Icc 0 1))
    (hb_cont : ContinuousOn (fun r => trainBvCLM hbg ht₀ r (U r)) (Icc 0 1))
    (hduh_int_tau : ∀ τ ∈ Icc (0 : ℝ) 1,
      IntegrableOn (fun r => duhH1CLM p.c_pos (p.ν * (τ - r)) (trainBvCLM hbg ht₀ r (U r)))
        (Ioc 0 τ) volume)
    (hU_duhamel : ∀ τ ∈ Icc (0 : ℝ) 1,
      U τ = freeH1CLM p.c_pos (p.ν * τ) u_sol +
        (∫ σ in (0 : ℝ)..τ, freeH1CLM p.c_pos (p.ν * (τ - σ)) (G σ)) -
        (∫ r in (0 : ℝ)..τ, duhH1CLM p.c_pos (p.ν * (τ - r)) (trainBvCLM hbg ht₀ r (U r))))
    {z zq zη : Coord → Fin 2 → ℝ}
    (hz_sm : StronglyMeasurable z)
    (hzq_sm : StronglyMeasurable zq)
    (hzη_sm : StronglyMeasurable zη)
    (hz_per : ∀ x : Coord, z (qShift p.c x) = z x ∧
      zq (qShift p.c x) = zq x ∧ zη (qShift p.c x) = zη x)
    (hz_ae : ∀ s ∈ Icc t₀ (t₀ + 1),
      ((val0CLM p.c (U (s - t₀)) : Plane → Vec2) =ᵐ[cellμ p.c] toVecSlice (fun y => z (s, y))) ∧
      ((dqCLM p.c (U (s - t₀)) : Plane → Vec2) =ᵐ[cellμ p.c] toVecSlice (fun y => zq (s, y))) ∧
      ((detaCLM p.c (U (s - t₀)) : Plane → Vec2) =ᵐ[cellμ p.c] toVecSlice (fun y => zη (s, y))))
    (Ψ : Coord → Fin 2 → ℝ) (hΨ : IsPlanarSolTest Ψ)
    (hΨ_supp : ∀ i, tsupport (fun x => Ψ x i) ⊆ Ioo t₀ (t₀ + 1) ×ˢ univ) :
    ∫ x, (∑ i : Fin 2, ofRealProf z x i * meridTranspose p.ν Ψ x i +
        cdot (flatBv p.train (ofRealProf z) (ofRealProf zq) (ofRealProf zη)) Ψ x) =
      ∫ x, cdot (ofRealProf g₀) Ψ x := by
  have hc : 0 < p.c := p.c_pos
  have hν : 0 < p.ν := p.ν_pos
  have hsub_map : MapsTo (fun s : ℝ => s - t₀) (Icc t₀ (t₀ + 1)) (Icc 0 1) :=
    fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hU_shift_cont : ContinuousOn (fun s : ℝ => U (s - t₀)) (Icc t₀ (t₀ + 1)) :=
    hU_cont.comp (continuousOn_id.sub continuousOn_const) hsub_map
  let Ψ' : Coord → Fin 2 → ℝ := fun x i => cpd 0 (fun w => Ψ w i) x
  have hΨ' : IsPlanarSolTest Ψ' := isPlanarSolTest_cpd0 hΨ
  let Φ : ℝ → Plane → Vec2 := fun τ => toVecSlice (TailPeriodizeAux.qPeriodizeVec p.c Ψ (t₀ + τ))
  let Φ' : ℝ → Plane → Vec2 := fun τ => toVecSlice (TailPeriodizeAux.qPeriodizeVec p.c Ψ' (t₀ + τ))
  have hΦ : ∀ τ : ℝ, IsRealSolCylTest p.c (Φ τ) := fun τ =>
    let hd := TailPeriodizeAux.isDivFreeTestField_qPeriodizeVec hc hΨ (t₀ + τ)
    ⟨hd.1, hd.2⟩
  have hΦ' : ∀ τ : ℝ, IsRealSolCylTest p.c (Φ' τ) := fun τ =>
    let hd := TailPeriodizeAux.isDivFreeTestField_qPeriodizeVec hc hΨ' (t₀ + τ)
    ⟨hd.1, hd.2⟩
  let φ₀ : ℝ → L2v p.c := fun τ => cylSmoothToL2 (isCylSmooth_of_solTest (hΦ τ))
  let φ₀' : ℝ → L2v p.c := fun τ => cylSmoothToL2 (isCylSmooth_of_solTest (hΦ' τ))
  let φq : ℝ → L2v p.c := fun τ =>
    cylSmoothToL2 ((isCylSmooth_of_solTest (hΦ τ)).dir ((1 : ℝ), (0 : ℝ)))
  let φη : ℝ → L2v p.c := fun τ =>
    cylSmoothToL2 ((isCylSmooth_of_solTest (hΦ τ)).dir ((0 : ℝ), (1 : ℝ)))
  have hφ₀'_div : ∀ τ : ℝ, φ₀' τ ∈ divFree p.c :=
    fun τ => cylSmoothToL2_mem_divFree_of_solTest hc (hΦ' τ)
  have hφq_div : ∀ τ : ℝ, φq τ ∈ divFree p.c :=
    fun τ => cylSmoothToL2_mem_divFree_of_solTest hc (isRealSolCylTest_dir (hΦ τ) 0)
  have hφη_div : ∀ τ : ℝ, φη τ ∈ divFree p.c :=
    fun τ => cylSmoothToL2_mem_divFree_of_solTest hc (isRealSolCylTest_dir (hΦ τ) 1)
  have hP0_inner : ∀ {ψ : L2v p.c}, ψ ∈ divFree p.c → ∀ w : L2v p.c,
      ⟪ψ, P0 p.c w⟫_ℝ = ⟪ψ, w⟫_ℝ := by
    intro ψ hψ w
    rw [← UnforcedLeray.Cyl.inner_P0_comm, UnforcedLeray.Cyl.P0_eq_self hψ]
  have hΨ_vanish_end : ∀ (τ : ℝ), τ ∉ Ioo (0 : ℝ) 1 → Φ τ = 0 := by
    intro τ hτ
    funext y; ext i
    simp only [Φ, toVecSlice, TailPeriodizeAux.qPeriodizeVec, TailPeriodizeAux.qPeriodize,
      WithLp.ofLp_toLp, Pi.zero_apply, PiLp.zero_apply]
    have h0 : ∀ k : ℤ, Ψ (t₀ + τ, (y.1 + (k : ℝ) * p.c, y.2)) i = 0 := by
      intro k
      refine image_eq_zero_of_notMem_tsupport (f := fun w => Ψ w i) fun hmem => hτ ?_
      have hs := (hΨ_supp i hmem).1
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    simp [h0]
  have hφ₀_zero0 : φ₀ 0 = 0 := by
    apply Lp.ext
    filter_upwards [(memLp_of_cylSmooth (isCylSmooth_of_solTest (hΦ 0))).coeFn_toLp,
      Lp.coeFn_zero Vec2 2 (cellμ p.c)] with y h1 h2
    exact h1.trans ((congrFun (hΨ_vanish_end 0 (by simp)) y).trans h2.symm)
  have hφ₀_zero1 : φ₀ 1 = 0 := by
    apply Lp.ext
    filter_upwards [(memLp_of_cylSmooth (isCylSmooth_of_solTest (hΦ 1))).coeFn_toLp,
      Lp.coeFn_zero Vec2 2 (cellμ p.c)] with y h1 h2
    exact h1.trans ((congrFun (hΨ_vanish_end 1 (by simp)) y).trans h2.symm)
  have hφ₀_ae : ∀ τ : ℝ, (φ₀ τ : Plane → Vec2) =ᵐ[cellμ p.c] Φ τ :=
    fun τ => (memLp_of_cylSmooth (isCylSmooth_of_solTest (hΦ τ))).coeFn_toLp
  have hφ₀'_ae : ∀ τ : ℝ, (φ₀' τ : Plane → Vec2) =ᵐ[cellμ p.c] Φ' τ :=
    fun τ => (memLp_of_cylSmooth (isCylSmooth_of_solTest (hΦ' τ))).coeFn_toLp
  have hφq_ae : ∀ τ : ℝ, (φq τ : Plane → Vec2) =ᵐ[cellμ p.c]
      toVecSlice (TailPeriodizeAux.qPeriodizeVec p.c
        (fun x i => cpd 1 (fun w => Ψ w i) x) (t₀ + τ)) := by
    intro τ
    filter_upwards [(memLp_of_cylSmooth ((isCylSmooth_of_solTest (hΦ τ)).dir ((1 : ℝ), (0 : ℝ)))).coeFn_toLp]
      with y hy
    ext i
    have hpd := pd_coord_cylSmooth (isCylSmooth_of_solTest (hΦ τ)) 0 i y
    have hper := TailPeriodizeAux.pd_qPeriodize hc (hΨ.smooth i) (t₀ + τ) 0 y
    exact (congrArg (fun v : Vec2 => v i) hy).trans (hpd.trans hper)
  have hφη_ae : ∀ τ : ℝ, (φη τ : Plane → Vec2) =ᵐ[cellμ p.c]
      toVecSlice (TailPeriodizeAux.qPeriodizeVec p.c
        (fun x i => cpd 2 (fun w => Ψ w i) x) (t₀ + τ)) := by
    intro τ
    filter_upwards [(memLp_of_cylSmooth ((isCylSmooth_of_solTest (hΦ τ)).dir ((0 : ℝ), (1 : ℝ)))).coeFn_toLp]
      with y hy
    ext i
    have hpd := pd_coord_cylSmooth (isCylSmooth_of_solTest (hΦ τ)) 1 i y
    have hper := TailPeriodizeAux.pd_qPeriodize hc (hΨ.smooth i) (t₀ + τ) 1 y
    exact (congrArg (fun v : Vec2 => v i) hy).trans (hpd.trans hper)
  have hφ₀'_cont : Continuous φ₀' :=
    continuous_qPeriodize_L2 hc (fun i => hΨ'.smooth i) φ₀' hφ₀'_ae
  have hφq_cont : Continuous φq :=
    continuous_qPeriodize_L2 hc
      (fun i => planarTest_isCoordTest_partial (hΨ.smooth i) (cdir 1)) φq hφq_ae
  have hφη_cont : Continuous φη :=
    continuous_qPeriodize_L2 hc
      (fun i => planarTest_isCoordTest_partial (hΨ.smooth i) (cdir 2)) φη hφη_ae
  have hderiv_φ₀ : ∀ τ : ℝ, HasDerivAt φ₀ (φ₀' τ) τ :=
    hasDerivAt_qPeriodize_L2 hc hΨ φ₀ φ₀' hφ₀_ae hφ₀'_ae
  have hφ₀_cont : Continuous φ₀ :=
    continuous_iff_continuousAt.2 fun τ => (hderiv_φ₀ τ).continuousAt

  -- Step 5a: Pointwise Volterra inner-product identity on `Ioo 0 1` + Fubini
  let b : ℝ → L2v p.c := fun r => trainBvCLM hbg ht₀ r (U r)
  let L_adj : ℝ → ℝ → L2v p.c → ℝ := fun σ τ x =>
    -⟪φ₀' τ, centeredHeatVecL2CLM hc (p.ν * (τ - σ)) x⟫_ℝ +
      p.ν * (⟪φq τ, DHeatCLM hc 0 (p.ν * (τ - σ)) x⟫_ℝ +
          ⟪φη τ, DHeatCLM hc 1 (p.ν * (τ - σ)) x⟫_ℝ)
  have hmaster : ∀ {σ : ℝ}, σ ∈ Icc (0 : ℝ) 1 → ∀ x : L2v p.c,
      ∫ τ in σ..1, L_adj σ τ x = ⟪φ₀ σ, x⟫_ℝ :=
    fun hσ x => master_heat_adjoint_ftc hc hν hΦ hφ₀_zero1 hφ₀'_cont hφq_cont hφη_cont hderiv_φ₀ hσ x

  let I_PDE : ℝ → ℝ := fun τ =>
    -⟪φ₀' τ, val0CLM p.c (U τ)⟫_ℝ +
      p.ν * (⟪φq τ, dqCLM p.c (U τ)⟫_ℝ + ⟪φη τ, detaCLM p.c (U τ)⟫_ℝ)

  have hSG_int_tau : ∀ τ ∈ Icc (0 : ℝ) 1,
      IntegrableOn (fun σ => freeH1CLM hc (p.ν * (τ - σ)) (G σ)) (Ioc 0 τ) volume := by
    intro τ hτ
    have hsm_app : StronglyMeasurable (fun σ : ℝ => freeH1CLM hc (p.ν * (τ - σ)) (G σ)) :=
      stronglyMeasurable_clm_apply
        (fun x => (continuous_freeH1CLM_apply hc x).comp
          (continuous_const.mul (continuous_const.sub continuous_id)))
        hG_sm
    refine Integrable.mono'
      ((hG_int.mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc_right hτ.2))).norm)
      hsm_app.aestronglyMeasurable.restrict ?_
    filter_upwards [] with σ
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) (norm_freeH1CLM_le hc _))

  have hI_PDE_eq : ∀ τ ∈ Ioo (0 : ℝ) 1,
      I_PDE τ = L_adj 0 τ (val0CLM p.c u_sol) +
        (∫ σ in (0 : ℝ)..τ, L_adj σ τ (val0CLM p.c (G σ))) -
        (∫ r in (0 : ℝ)..τ, L_adj r τ (b r)) := by
    intro τ hτ
    have hτ_Icc : τ ∈ Icc (0 : ℝ) 1 := ⟨hτ.1.le, hτ.2.le⟩
    have hclm_int : ∀ (Λ : H1Sol p.c →L[ℝ] ℝ) {F : ℝ → H1Sol p.c},
        IntegrableOn F (Ioc 0 τ) volume →
        Λ (∫ r in (0 : ℝ)..τ, F r) = ∫ r in (0 : ℝ)..τ, Λ (F r) := by
      intro Λ F hF
      rw [intervalIntegral.integral_of_le hτ.1.le, intervalIntegral.integral_of_le hτ.1.le]
      exact (Λ.integral_comp_comm hF).symm
    let Λ : H1Sol p.c →L[ℝ] ℝ :=
      -(innerSL ℝ (φ₀' τ)).comp (val0CLM p.c) +
        p.ν • ((innerSL ℝ (φq τ)).comp (dqCLM p.c) + (innerSL ℝ (φη τ)).comp (detaCLM p.c))
    have hΛ_apply : ∀ q : H1Sol p.c,
        Λ q = -⟪φ₀' τ, val0CLM p.c q⟫_ℝ +
          p.ν * (⟪φq τ, dqCLM p.c q⟫_ℝ + ⟪φη τ, detaCLM p.c q⟫_ℝ) := by
      intro q; simp [Λ, innerSL_apply_apply]; ring
    change Λ (U τ) = _
    rw [hU_duhamel τ hτ_Icc, map_sub, map_add, hclm_int Λ (hSG_int_tau τ hτ_Icc),
      hclm_int Λ (hduh_int_tau τ hτ_Icc)]
    have hterm_u : Λ (freeH1CLM hc (p.ν * τ) u_sol) = L_adj 0 τ (val0CLM p.c u_sol) := by
      rw [hΛ_apply, val0_freeH1CLM, dq_freeH1CLM, deta_freeH1CLM]
      have hpos : 0 < p.ν * τ := mul_pos hν hτ.1
      rw [← DHeatCLM_eq_centeredHeat_of_weakDeriv hc hpos (H1Sol.weak_q u_sol),
        ← DHeatCLM_eq_centeredHeat_of_weakDeriv hc hpos (H1Sol.weak_eta u_sol)]
      simp [L_adj]
    have hne_τ : ∀ᵐ r ∂volume, r ∈ uIoc 0 τ → r < τ := by
      filter_upwards [ae_ne_real τ] with r hr hmem
      rw [uIoc_of_le hτ.1.le] at hmem
      exact lt_of_le_of_ne hmem.2 hr
    have hterm_G : (∫ σ in (0 : ℝ)..τ, Λ (freeH1CLM hc (p.ν * (τ - σ)) (G σ))) =
        ∫ σ in (0 : ℝ)..τ, L_adj σ τ (val0CLM p.c (G σ)) := by
      refine intervalIntegral.integral_congr_ae (hne_τ.mono fun σ hσ hmem => ?_)
      have hpos : 0 < p.ν * (τ - σ) := mul_pos hν (sub_pos.mpr (hσ hmem))
      rw [hΛ_apply, val0_freeH1CLM, dq_freeH1CLM, deta_freeH1CLM,
        ← DHeatCLM_eq_centeredHeat_of_weakDeriv hc hpos (H1Sol.weak_q (G σ)),
        ← DHeatCLM_eq_centeredHeat_of_weakDeriv hc hpos (H1Sol.weak_eta (G σ))]
    have hterm_b : (∫ r in (0 : ℝ)..τ, Λ (duhH1CLM hc (p.ν * (τ - r)) (b r))) =
        ∫ r in (0 : ℝ)..τ, L_adj r τ (b r) := by
      refine intervalIntegral.integral_congr_ae (hne_τ.mono fun r hr hmem => ?_)
      have hpos : 0 < p.ν * (τ - r) := mul_pos hν (sub_pos.mpr (hr hmem))
      rw [hΛ_apply, val0_duhH1CLM_of_pos hc hpos, dq_duhH1CLM_of_pos hc hpos,
        deta_duhH1CLM_of_pos hc hpos, hP0_inner (hφ₀'_div τ),
        hP0_inner (hφq_div τ), hP0_inner (hφη_div τ)]
    rw [hterm_u, hterm_G, hterm_b]

  -- Fubini for term 1 (`u_sol`)
  have h_int_term1 : IntegrableOn (fun τ => L_adj 0 τ (val0CLM p.c u_sol)) (Ioo 0 1) volume ∧
      (∫ τ in Ioo (0 : ℝ) 1, L_adj 0 τ (val0CLM p.c u_sol)) = 0 := by
    have hpos_eq : ∀ τ ∈ Ioo (0 : ℝ) 1,
        L_adj 0 τ (val0CLM p.c u_sol) =
          -⟪φ₀' τ, centeredHeatVecL2CLM hc (p.ν * τ) (val0CLM p.c u_sol)⟫_ℝ +
            p.ν * (⟪φq τ, centeredHeatVecL2CLM hc (p.ν * τ) (dqCLM p.c u_sol)⟫_ℝ +
                ⟪φη τ, centeredHeatVecL2CLM hc (p.ν * τ) (detaCLM p.c u_sol)⟫_ℝ) := by
      intro τ hτ
      have hpos : 0 < p.ν * (τ - 0) := mul_pos hν (by linarith [hτ.1])
      dsimp only [L_adj]
      rw [DHeatCLM_eq_centeredHeat_of_weakDeriv hc hpos (H1Sol.weak_q u_sol),
        DHeatCLM_eq_centeredHeat_of_weakDeriv hc hpos (H1Sol.weak_eta u_sol), sub_zero]
    have hcont_rhs : Continuous (fun τ : ℝ =>
        -⟪φ₀' τ, centeredHeatVecL2CLM hc (p.ν * τ) (val0CLM p.c u_sol)⟫_ℝ +
          p.ν * (⟪φq τ, centeredHeatVecL2CLM hc (p.ν * τ) (dqCLM p.c u_sol)⟫_ℝ +
              ⟪φη τ, centeredHeatVecL2CLM hc (p.ν * τ) (detaCLM p.c u_sol)⟫_ℝ)) :=
      (hφ₀'_cont.inner ((continuous_centeredHeatVecL2CLM_apply hc _).comp
        (continuous_const.mul continuous_id))).neg.add
        (continuous_const.mul
          ((hφq_cont.inner ((continuous_centeredHeatVecL2CLM_apply hc _).comp
              (continuous_const.mul continuous_id))).add
            (hφη_cont.inner ((continuous_centeredHeatVecL2CLM_apply hc _).comp
              (continuous_const.mul continuous_id)))))
    have hint : IntegrableOn (fun τ => L_adj 0 τ (val0CLM p.c u_sol)) (Ioo 0 1) volume :=
      (hcont_rhs.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self).congr_fun
        (fun τ hτ => (hpos_eq τ hτ).symm) measurableSet_Ioo
    refine ⟨hint, ?_⟩
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
      hmaster ⟨le_rfl, zero_le_one⟩ (val0CLM p.c u_sol), hφ₀_zero0, inner_zero_left]

  -- Fubini for term 2 (`G`)
  have h_int_term2 : IntegrableOn (fun τ => ∫ σ in (0 : ℝ)..τ, L_adj σ τ (val0CLM p.c (G σ)))
        (Ioo 0 1) volume ∧
      (∫ τ in Ioo (0 : ℝ) 1, ∫ σ in (0 : ℝ)..τ, L_adj σ τ (val0CLM p.c (G σ))) =
        ∫ σ in Ioo (0 : ℝ) 1, ⟪φ₀ σ, val0CLM p.c (G σ)⟫_ℝ := by
    let T_open : Set (ℝ × ℝ) := {q | 0 < q.1 ∧ q.1 < q.2 ∧ q.2 < 1}
    have hT_meas : MeasurableSet T_open :=
      ((isOpen_lt continuous_const continuous_fst).inter
        ((isOpen_lt continuous_fst continuous_snd).inter
          (isOpen_lt continuous_snd continuous_const))).measurableSet
    let K_reg : ℝ × ℝ → ℝ := fun q =>
      -⟪φ₀' q.2, centeredHeatVecL2CLM hc (p.ν * (q.2 - q.1)) (val0CLM p.c (G q.1))⟫_ℝ +
        p.ν * (⟪φq q.2, centeredHeatVecL2CLM hc (p.ν * (q.2 - q.1)) (dqCLM p.c (G q.1))⟫_ℝ +
            ⟪φη q.2, centeredHeatVecL2CLM hc (p.ν * (q.2 - q.1)) (detaCLM p.c (G q.1))⟫_ℝ)
    have hK_reg_sm : StronglyMeasurable K_reg := by
      have hm0 := stronglyMeasurable_clm_apply
        (U := fun q : ℝ × ℝ => centeredHeatVecL2CLM hc (p.ν * (q.2 - q.1)))
        (fun x => (continuous_centeredHeatVecL2CLM_apply hc x).comp
          (continuous_const.mul (continuous_snd.sub continuous_fst)))
        (hG0_sm.comp_measurable measurable_fst)
      have hmq := stronglyMeasurable_clm_apply
        (U := fun q : ℝ × ℝ => centeredHeatVecL2CLM hc (p.ν * (q.2 - q.1)))
        (fun x => (continuous_centeredHeatVecL2CLM_apply hc x).comp
          (continuous_const.mul (continuous_snd.sub continuous_fst)))
        (hGq_sm.comp_measurable measurable_fst)
      have hmη := stronglyMeasurable_clm_apply
        (U := fun q : ℝ × ℝ => centeredHeatVecL2CLM hc (p.ν * (q.2 - q.1)))
        (fun x => (continuous_centeredHeatVecL2CLM_apply hc x).comp
          (continuous_const.mul (continuous_snd.sub continuous_fst)))
        (hGη_sm.comp_measurable measurable_fst)
      exact (((hφ₀'_cont.comp continuous_snd).stronglyMeasurable.inner hm0).neg).add
        (stronglyMeasurable_const.mul
          (((hφq_cont.comp continuous_snd).stronglyMeasurable.inner hmq).add
            ((hφη_cont.comp continuous_snd).stronglyMeasurable.inner hmη)))
    let μI : Measure ℝ := volume.restrict (Ioo 0 1)
    let K_ind : ℝ × ℝ → ℝ := T_open.indicator K_reg
    have hK_ind_meas : AEStronglyMeasurable K_ind (μI.prod μI) :=
      (hK_reg_sm.indicator hT_meas).aestronglyMeasurable
    obtain ⟨M0, hM0⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (f := fun τ => ‖φ₀' τ‖ + p.ν * (‖φq τ‖ + ‖φη τ‖))
      (hφ₀'_cont.norm.add (continuous_const.mul (hφq_cont.norm.add hφη_cont.norm))).continuousOn
    let Mφ : ℝ := max 0 M0
    have hMφ_nn : 0 ≤ Mφ := le_max_left 0 M0
    have hG_norm_int : Integrable (fun σ => Mφ * ‖G σ‖) μI :=
      ((hG_int.mono_set Ioo_subset_Icc_self).norm).const_mul Mφ
    have h1_int : Integrable (fun _ : ℝ => (1 : ℝ)) μI :=
      integrableOn_const (by simp [Real.volume_Ioo]) enorm_ne_top
    have hdom_prod : Integrable (fun q : ℝ × ℝ => (Mφ * ‖G q.1‖) * (1 : ℝ)) (μI.prod μI) :=
      hG_norm_int.mul_prod h1_int
    have hK_ind_int : Integrable K_ind (μI.prod μI) := by
      refine hdom_prod.mono' hK_ind_meas ?_
      have hmem_prod : ∀ᵐ q ∂(μI.prod μI), q.1 ∈ Ioo (0 : ℝ) 1 ∧ q.2 ∈ Ioo (0 : ℝ) 1 := by
        rw [Measure.prod_restrict]
        exact ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)
      filter_upwards [hmem_prod] with q ⟨_, hq2⟩
      by_cases hq : q ∈ T_open
      · dsimp only [K_ind]; rw [indicator_of_mem hq, mul_one, Real.norm_eq_abs]
        have hτ_Icc : q.2 ∈ Icc (0 : ℝ) 1 := ⟨hq2.1.le, hq2.2.le⟩
        have hM_le : ‖φ₀' q.2‖ + p.ν * (‖φq q.2‖ + ‖φη q.2‖) ≤ Mφ := by
          have h := hM0 q.2 hτ_Icc
          rw [Real.norm_of_nonneg (by positivity)] at h
          exact h.trans (le_max_right 0 M0)
        have b_in : ∀ (ψ w : L2v p.c), ‖w‖ ≤ ‖G q.1‖ →
            |⟪ψ, centeredHeatVecL2CLM hc (p.ν * (q.2 - q.1)) w⟫_ℝ| ≤ ‖ψ‖ * ‖G q.1‖ := by
          intro ψ w hw
          calc |⟪ψ, centeredHeatVecL2CLM hc (p.ν * (q.2 - q.1)) w⟫_ℝ|
              ≤ ‖ψ‖ * ‖centeredHeatVecL2CLM hc (p.ν * (q.2 - q.1)) w‖ :=
                Real.norm_eq_abs _ ▸ abs_real_inner_le_norm _ _
            _ ≤ ‖ψ‖ * (1 * ‖w‖) := mul_le_mul_of_nonneg_left
                ((ContinuousLinearMap.le_opNorm _ _).trans
                  (mul_le_mul_of_nonneg_right (norm_centeredHeatVecL2CLM_le_one_all hc _) (norm_nonneg _)))
                (norm_nonneg _)
            _ ≤ ‖ψ‖ * ‖G q.1‖ := by nlinarith [norm_nonneg ψ]
        have b0 := b_in (φ₀' q.2) (val0CLM p.c (G q.1)) (norm_val0CLM_le _)
        have bq := b_in (φq q.2) (dqCLM p.c (G q.1)) (norm_dqCLM_le _)
        have bη := b_in (φη q.2) (detaCLM p.c (G q.1)) (norm_detaCLM_le _)
        dsimp [K_reg]
        calc |-⟪φ₀' q.2, _⟫_ℝ + p.ν * (⟪φq q.2, _⟫_ℝ + ⟪φη q.2, _⟫_ℝ)|
            ≤ |-⟪φ₀' q.2, _⟫_ℝ| + |p.ν * (⟪φq q.2, _⟫_ℝ + ⟪φη q.2, _⟫_ℝ)| := abs_add_le _ _
          _ ≤ |⟪φ₀' q.2, _⟫_ℝ| + p.ν * (|⟪φq q.2, _⟫_ℝ| + |⟪φη q.2, _⟫_ℝ|) := by
              rw [abs_neg, abs_mul, abs_of_pos hν]
              exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (abs_add_le _ _) hν.le)
          _ ≤ ‖φ₀' q.2‖ * ‖G q.1‖ + p.ν * (‖φq q.2‖ * ‖G q.1‖ + ‖φη q.2‖ * ‖G q.1‖) :=
              add_le_add b0 (mul_le_mul_of_nonneg_left (add_le_add bq bη) hν.le)
          _ = (‖φ₀' q.2‖ + p.ν * (‖φq q.2‖ + ‖φη q.2‖)) * ‖G q.1‖ := by ring
          _ ≤ Mφ * ‖G q.1‖ := mul_le_mul_of_nonneg_right hM_le (norm_nonneg _)
      · simp only [K_ind, indicator_of_notMem hq, norm_zero, mul_one]
        exact mul_nonneg hMφ_nn (norm_nonneg _)
    have hK_eq_L : ∀ {σ τ : ℝ}, 0 < σ → σ < τ → τ < 1 →
        K_reg (σ, τ) = L_adj σ τ (val0CLM p.c (G σ)) := by
      intro σ τ _ hστ _
      have hpos : 0 < p.ν * (τ - σ) := mul_pos hν (sub_pos.mpr hστ)
      dsimp only [K_reg, L_adj]
      rw [DHeatCLM_eq_centeredHeat_of_weakDeriv hc hpos (H1Sol.weak_q (G σ)),
        DHeatCLM_eq_centeredHeat_of_weakDeriv hc hpos (H1Sol.weak_eta (G σ))]
    have hslice_τ : ∀ τ ∈ Ioo (0 : ℝ) 1,
        ∫ σ, K_ind (σ, τ) ∂μI = ∫ σ in (0 : ℝ)..τ, L_adj σ τ (val0CLM p.c (G σ)) := by
      intro τ hτ
      have hsub : Ioo 0 τ ⊆ Ioo 0 1 := fun σ hσ => ⟨hσ.1, hσ.2.trans hτ.2⟩
      change ∫ σ in Ioo 0 1, K_ind (σ, τ) = _
      have hind : ∫ σ in Ioo 0 1, K_ind (σ, τ) =
          ∫ σ in Ioo 0 1, (Ioo 0 τ).indicator (fun σ => L_adj σ τ (val0CLM p.c (G σ))) σ := by
        refine setIntegral_congr_fun measurableSet_Ioo fun σ hσ => ?_
        by_cases hστ : σ < τ
        · have hq : (σ, τ) ∈ T_open := ⟨hσ.1, hστ, hτ.2⟩
          have hs' : σ ∈ Ioo 0 τ := ⟨hσ.1, hστ⟩
          simp only [K_ind, indicator_of_mem hq, indicator_of_mem hs',
            hK_eq_L hσ.1 hστ hτ.2]
        · have hq : (σ, τ) ∉ T_open := fun h => hστ h.2.1
          have hs' : σ ∉ Ioo 0 τ := fun h => hστ h.2
          simp only [K_ind, indicator_of_notMem hq, indicator_of_notMem hs']
      rw [hind, setIntegral_indicator measurableSet_Ioo, inter_eq_self_of_subset_right hsub,
        ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hτ.1.le]
    have hslice_σ : ∀ σ ∈ Ioo (0 : ℝ) 1,
        ∫ τ, K_ind (σ, τ) ∂μI = ⟪φ₀ σ, val0CLM p.c (G σ)⟫_ℝ := by
      intro σ hσ
      have hsub : Ioo σ 1 ⊆ Ioo 0 1 := fun τ hτ => ⟨hσ.1.trans hτ.1, hτ.2⟩
      change ∫ τ in Ioo 0 1, K_ind (σ, τ) = _
      have hind : ∫ τ in Ioo 0 1, K_ind (σ, τ) =
          ∫ τ in Ioo 0 1, (Ioo σ 1).indicator (fun τ => L_adj σ τ (val0CLM p.c (G σ))) τ := by
        refine setIntegral_congr_fun measurableSet_Ioo fun τ hτ => ?_
        by_cases hστ : σ < τ
        · have hq : (σ, τ) ∈ T_open := ⟨hσ.1, hστ, hτ.2⟩
          have ht' : τ ∈ Ioo σ 1 := ⟨hστ, hτ.2⟩
          simp only [K_ind, indicator_of_mem hq, indicator_of_mem ht',
            hK_eq_L hσ.1 hστ hτ.2]
        · have hq : (σ, τ) ∉ T_open := fun h => hστ h.2.1
          have ht' : τ ∉ Ioo σ 1 := fun h => hστ h.1
          simp only [K_ind, indicator_of_notMem hq, indicator_of_notMem ht']
      rw [hind, setIntegral_indicator measurableSet_Ioo, inter_eq_self_of_subset_right hsub,
        ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hσ.2.le,
        hmaster ⟨hσ.1.le, hσ.2.le⟩ (val0CLM p.c (G σ))]
    have hfub := (MeasureTheory.integral_prod_symm K_ind hK_ind_int).symm.trans
      (MeasureTheory.integral_prod K_ind hK_ind_int)
    have hint_right : Integrable (fun τ => ∫ σ, K_ind (σ, τ) ∂μI) μI :=
      hK_ind_int.integral_prod_right
    refine ⟨hint_right.congr (ae_restrict_of_forall_mem measurableSet_Ioo hslice_τ), ?_⟩
    have hL : ∫ τ in Ioo 0 1, ∫ σ in (0 : ℝ)..τ, L_adj σ τ (val0CLM p.c (G σ)) =
        ∫ τ, (∫ σ, K_ind (σ, τ) ∂μI) ∂μI :=
      setIntegral_congr_fun measurableSet_Ioo fun τ hτ => (hslice_τ τ hτ).symm
    have hR : ∫ σ, (∫ τ, K_ind (σ, τ) ∂μI) ∂μI =
        ∫ σ in Ioo 0 1, ⟪φ₀ σ, val0CLM p.c (G σ)⟫_ℝ :=
      setIntegral_congr_fun measurableSet_Ioo hslice_σ
    exact hL.trans (hfub.trans hR)

  -- Fubini for term 3 (`b r := trainBvCLM hbg ht₀ r (U r)`)
  have h_int_term3 : IntegrableOn (fun τ => ∫ r in (0 : ℝ)..τ, L_adj r τ (b r))
        (Ioo 0 1) volume ∧
      (∫ τ in Ioo (0 : ℝ) 1, ∫ r in (0 : ℝ)..τ, L_adj r τ (b r)) =
        ∫ r in Ioo (0 : ℝ) 1, ⟪φ₀ r, b r⟫_ℝ := by
    obtain ⟨Mb₀, hMb₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hb_cont
    let Mb : ℝ := max 0 Mb₀
    have hMb_nn : 0 ≤ Mb := le_max_left 0 Mb₀
    have hb_bdd : ∀ r ∈ Icc (0 : ℝ) 1, ‖b r‖ ≤ Mb :=
      fun r hr => (hMb₀ r hr).trans (le_max_right 0 Mb₀)
    obtain ⟨Mφ₀, hMφ₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (f := fun τ => ‖φ₀' τ‖ + ‖φq τ‖ + ‖φη τ‖)
      ((hφ₀'_cont.norm.add hφq_cont.norm).add hφη_cont.norm).continuousOn
    let Mφ : ℝ := max 0 Mφ₀
    have hMφ_nn : 0 ≤ Mφ := le_max_left 0 Mφ₀
    have hMφ_b : ∀ τ ∈ Icc (0 : ℝ) 1, ‖φ₀' τ‖ + ‖φq τ‖ + ‖φη τ‖ ≤ Mφ := by
      intro τ hτ
      have h := hMφ₀ τ hτ
      rw [Real.norm_of_nonneg (by positivity)] at h
      exact h.trans (le_max_right 0 Mφ₀)
    let T_open : Set (ℝ × ℝ) := {q | 0 < q.1 ∧ q.1 < q.2 ∧ q.2 < 1}
    have hK_contOn : ContinuousOn (fun q : ℝ × ℝ => L_adj q.1 q.2 (b q.1)) T_open := by
      have hb_q : ContinuousOn (fun q : ℝ × ℝ => b q.1) T_open :=
        hb_cont.comp continuous_fst.continuousOn
          (fun q hq => ⟨hq.1.le, (hq.2.1.trans hq.2.2).le⟩)
      have hH_q : ContinuousOn
          (fun q : ℝ × ℝ => centeredHeatVecL2CLM hc (p.ν * (q.2 - q.1)) (b q.1)) T_open :=
        UnforcedLeray.Infra.VolterraEvolution.continuousOn_clm_apply
          (fun e => ((continuous_centeredHeatVecL2CLM_apply hc e).comp
            (continuous_const.mul (continuous_snd.sub continuous_fst))).continuousOn)
          (fun _ _ => ⟨1, Eventually.of_forall fun _ => norm_centeredHeatVecL2CLM_le_one_all hc _⟩)
          hb_q
      have hDj_q : ∀ j : Fin 2, ContinuousOn
          (fun q : ℝ × ℝ => DHeatCLM hc j (p.ν * (q.2 - q.1)) (b q.1)) T_open := by
        intro j
        refine UnforcedLeray.Infra.VolterraEvolution.continuousOn_clm_apply
          (K := fun q : ℝ × ℝ => DHeatCLM hc j (p.ν * (q.2 - q.1))) ?_ ?_ hb_q
        · intro e
          exact (continuousOn_DHeatCLM_apply hc j e).comp
            (continuousOn_const.mul (continuousOn_snd.sub continuousOn_fst))
            (fun q hq => mul_pos hν (sub_pos.mpr hq.2.1))
        · intro q₀ hq₀
          let δ := (q₀.2 - q₀.1) / 2
          have hδ : 0 < δ := half_pos (sub_pos.mpr hq₀.2.1)
          refine ⟨(2 / Real.sqrt Real.pi) * (p.ν ^ (-(1 / 2 : ℝ)) * δ ^ (-(1 / 2 : ℝ))), ?_⟩
          have hopen_δ : IsOpen {q : ℝ × ℝ | δ < q.2 - q.1} :=
            isOpen_lt continuous_const (continuous_snd.sub continuous_fst)
          filter_upwards [nhdsWithin_le_nhds (hopen_δ.mem_nhds (half_lt_self (sub_pos.mpr hq₀.2.1)))]
            with q (hq : δ < q.2 - q.1)
          have hpos : 0 < q.2 - q.1 := lt_trans hδ hq
          refine (norm_DHeatCLM_le hc j (mul_pos hν hpos)).trans ?_
          rw [heatDivL2Coeff_eq_singular hν hpos]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_nonpos hδ hq.le (by norm_num))
              (Real.rpow_nonneg hν.le _))
            (by positivity)
      exact (((hφ₀'_cont.comp continuous_snd).continuousOn.inner hH_q).neg).add
        (continuousOn_const.mul
          (((hφq_cont.comp continuous_snd).continuousOn.inner (hDj_q 0)).add
            ((hφη_cont.comp continuous_snd).continuousOn.inner (hDj_q 1))))
    let C_ker : ℝ := Mφ * Mb * (1 + p.ν * ((2 / Real.sqrt Real.pi) * p.ν ^ (-(1 / 2 : ℝ))))
    have hC_ker_nn : 0 ≤ C_ker := by positivity
    have hK_bdd : ∀ r τ : ℝ, 0 < r → r < τ → τ < 1 →
        |L_adj r τ (b r)| ≤ C_ker * (τ - r) ^ (-(1 / 2 : ℝ)) := by
      intro r τ hr0 hrτ hτ1
      have hpos_d : 0 < τ - r := sub_pos.mpr hrτ
      have hle1_d : τ - r ≤ 1 := by linarith
      have h1_rp : 1 ≤ (τ - r) ^ (-(1 / 2 : ℝ)) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos hpos_d hle1_d (by norm_num)
      have hpos_age : 0 < p.ν * (τ - r) := mul_pos hν hpos_d
      have hbr : ‖b r‖ ≤ Mb := hb_bdd r ⟨hr0.le, (hrτ.trans hτ1).le⟩
      have hφτ : ‖φ₀' τ‖ + ‖φq τ‖ + ‖φη τ‖ ≤ Mφ := hMφ_b τ ⟨(hr0.trans hrτ).le, hτ1.le⟩
      have b0 : |⟪φ₀' τ, centeredHeatVecL2CLM hc (p.ν * (τ - r)) (b r)⟫_ℝ| ≤ Mφ * Mb * 1 := by
        calc |⟪φ₀' τ, centeredHeatVecL2CLM hc (p.ν * (τ - r)) (b r)⟫_ℝ|
            ≤ ‖φ₀' τ‖ * ‖centeredHeatVecL2CLM hc (p.ν * (τ - r)) (b r)‖ :=
              Real.norm_eq_abs _ ▸ abs_real_inner_le_norm _ _
          _ ≤ ‖φ₀' τ‖ * (1 * ‖b r‖) := mul_le_mul_of_nonneg_left
              ((ContinuousLinearMap.le_opNorm _ _).trans
                (mul_le_mul_of_nonneg_right (norm_centeredHeatVecL2CLM_le_one_all hc _) (norm_nonneg _)))
              (norm_nonneg _)
          _ ≤ Mφ * Mb * 1 := by
              have h1 : ‖φ₀' τ‖ ≤ Mφ := by linarith [norm_nonneg (φq τ), norm_nonneg (φη τ)]
              nlinarith [norm_nonneg (φ₀' τ), norm_nonneg (b r)]
      have bj : ∀ (j : Fin 2) (ψ : L2v p.c),
          |⟪ψ, DHeatCLM hc j (p.ν * (τ - r)) (b r)⟫_ℝ| ≤
            ‖ψ‖ * (heatDivL2Coeff (p.ν * (τ - r)) * Mb) := by
        intro j ψ
        have hcoeff_nn : 0 ≤ heatDivL2Coeff (p.ν * (τ - r)) := by unfold heatDivL2Coeff; positivity
        calc |⟪ψ, DHeatCLM hc j (p.ν * (τ - r)) (b r)⟫_ℝ|
            ≤ ‖ψ‖ * ‖DHeatCLM hc j (p.ν * (τ - r)) (b r)‖ :=
              Real.norm_eq_abs _ ▸ abs_real_inner_le_norm _ _
          _ ≤ ‖ψ‖ * (heatDivL2Coeff (p.ν * (τ - r)) * Mb) := mul_le_mul_of_nonneg_left
              ((ContinuousLinearMap.le_opNorm _ _).trans
                (mul_le_mul (norm_DHeatCLM_le hc j hpos_age) hbr (norm_nonneg _) hcoeff_nn))
              (norm_nonneg _)
      have htri : |L_adj r τ (b r)| ≤
          |⟪φ₀' τ, centeredHeatVecL2CLM hc (p.ν * (τ - r)) (b r)⟫_ℝ| +
            p.ν * (|⟪φq τ, DHeatCLM hc 0 (p.ν * (τ - r)) (b r)⟫_ℝ| +
                |⟪φη τ, DHeatCLM hc 1 (p.ν * (τ - r)) (b r)⟫_ℝ|) := by
        dsimp [L_adj]
        calc |-⟪φ₀' τ, _⟫_ℝ + p.ν * (⟪φq τ, _⟫_ℝ + ⟪φη τ, _⟫_ℝ)|
            ≤ |-⟪φ₀' τ, _⟫_ℝ| + |p.ν * (⟪φq τ, _⟫_ℝ + ⟪φη τ, _⟫_ℝ)| := abs_add_le _ _
          _ ≤ |⟪φ₀' τ, _⟫_ℝ| + p.ν * (|⟪φq τ, _⟫_ℝ| + |⟪φη τ, _⟫_ℝ|) := by
              rw [abs_neg, abs_mul, abs_of_pos hν]
              exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (abs_add_le _ _) hν.le)
      have hqη_le : ‖φq τ‖ + ‖φη τ‖ ≤ Mφ := by linarith [norm_nonneg (φ₀' τ)]
      have hcoeff_nn : 0 ≤ heatDivL2Coeff (p.ν * (τ - r)) := by unfold heatDivL2Coeff; positivity
      calc |L_adj r τ (b r)|
          ≤ Mφ * Mb * 1 +
              p.ν * ((‖φq τ‖ + ‖φη τ‖) * (heatDivL2Coeff (p.ν * (τ - r)) * Mb)) := by
            have h12 : |⟪φq τ, DHeatCLM hc 0 (p.ν * (τ - r)) (b r)⟫_ℝ| +
                |⟪φη τ, DHeatCLM hc 1 (p.ν * (τ - r)) (b r)⟫_ℝ| ≤
                (‖φq τ‖ + ‖φη τ‖) * (heatDivL2Coeff (p.ν * (τ - r)) * Mb) := by
              linarith [bj 0 (φq τ), bj 1 (φη τ)]
            exact htri.trans (add_le_add b0 (mul_le_mul_of_nonneg_left h12 hν.le))
        _ ≤ Mφ * Mb * (τ - r) ^ (-(1 / 2 : ℝ)) +
              p.ν * (Mφ * (heatDivL2Coeff (p.ν * (τ - r)) * Mb)) := by
            refine add_le_add
              (mul_le_mul_of_nonneg_left h1_rp (mul_nonneg hMφ_nn hMb_nn))
              (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hqη_le (mul_nonneg hcoeff_nn hMb_nn)) hν.le)
        _ = C_ker * (τ - r) ^ (-(1 / 2 : ℝ)) := by
            rw [heatDivL2Coeff_eq_singular hν hpos_d]
            dsimp [C_ker]; ring
    obtain ⟨hint_K, hfub⟩ := fubini_triangle_rpow_half_unit hK_contOn hC_ker_nn hK_bdd
    refine ⟨hint_K, hfub.symm.trans ?_⟩
    refine setIntegral_congr_fun measurableSet_Ioo fun r hr => ?_
    exact hmaster ⟨hr.1.le, hr.2.le⟩ (b r)

  have hb_inner_int : IntegrableOn (fun τ => ⟪φ₀ τ, b τ⟫_ℝ) (Ioo 0 1) volume :=
    ((hφ₀_cont.continuousOn.inner hb_cont).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hI_PDE_int : IntegrableOn I_PDE (Ioo 0 1) volume :=
    ((h_int_term1.1.add h_int_term2.1).sub h_int_term3.1).congr_fun
      (fun τ hτ => (hI_PDE_eq τ hτ).symm) measurableSet_Ioo
  have hreal_master : ∫ τ in Ioo (0 : ℝ) 1, (I_PDE τ + ⟪φ₀ τ, b τ⟫_ℝ) =
      ∫ τ in Ioo (0 : ℝ) 1, ⟪φ₀ τ, val0CLM p.c (G τ)⟫_ℝ := by
    have hsplit : ∫ τ in Ioo (0 : ℝ) 1, I_PDE τ =
        (∫ τ in Ioo (0 : ℝ) 1, L_adj 0 τ (val0CLM p.c u_sol)) +
          (∫ τ in Ioo (0 : ℝ) 1, ∫ σ in (0 : ℝ)..τ, L_adj σ τ (val0CLM p.c (G σ))) -
          (∫ τ in Ioo (0 : ℝ) 1, ∫ r in (0 : ℝ)..τ, L_adj r τ (b r)) := by
      have h12 : IntegrableOn
          (fun τ => L_adj 0 τ (val0CLM p.c u_sol) +
            ∫ σ in (0 : ℝ)..τ, L_adj σ τ (val0CLM p.c (G σ))) (Ioo 0 1) volume :=
        h_int_term1.1.add h_int_term2.1
      rw [setIntegral_congr_fun measurableSet_Ioo hI_PDE_eq,
        integral_sub h12 h_int_term3.1,
        integral_add h_int_term1.1 h_int_term2.1]
    linarith [integral_add hI_PDE_int hb_inner_int, hsplit,
      h_int_term1.2, h_int_term2.2, h_int_term3.2]

  -- Step 5b: Unfold the `Coord` integrals via `integrable_and_integral_coord_eq_cell_qPeriodize`
  have hex_R : ∀ i : Fin 2, ∃ Ri : ℝ, 0 < Ri ∧
      ∀ x ∈ tsupport (fun w => Ψ w i), |x.2.1| ≤ Ri ∧ |x.2.2| ≤ Ri := by
    intro i
    obtain ⟨M, hM⟩ := (hΨ.smooth i).compact.isBounded.subset_closedBall (0 : Coord)
    refine ⟨max 1 M, lt_of_lt_of_le one_pos (le_max_left _ _), fun x hx => ?_⟩
    have hx_le : ‖x‖ ≤ M := by simpa [Metric.mem_closedBall, dist_zero_right] using hM hx
    have hxM : ‖x‖ ≤ max 1 M := hx_le.trans (le_max_right _ _)
    have h2 : ‖x.2‖ ≤ max 1 M := (norm_snd_le x).trans hxM
    exact ⟨by simpa only [Real.norm_eq_abs] using (norm_fst_le x.2).trans h2,
      by simpa only [Real.norm_eq_abs] using (norm_snd_le x.2).trans h2⟩
  obtain ⟨R0, hR0, hR0_mem⟩ := hex_R 0
  obtain ⟨R1, _, hR1_mem⟩ := hex_R 1
  let R : ℝ := max R0 R1
  have hR_pos : 0 < R := lt_of_lt_of_le hR0 (le_max_left R0 R1)
  have hnot_tsupp : ∀ (i : Fin 2) (x : Coord),
      (x.1 ∉ Icc t₀ (t₀ + 1) ∨ R < |x.2.1| ∨ R < |x.2.2|) →
        x ∉ tsupport (fun w => Ψ w i) := by
    intro i x hx hmem
    rcases hx with ht | hq | hη
    · have hs := (hΨ_supp i hmem).1
      exact ht ⟨hs.1.le, hs.2.le⟩
    · fin_cases i
      · linarith [(hR0_mem x hmem).1, le_max_left R0 R1]
      · linarith [(hR1_mem x hmem).1, le_max_right R0 R1]
    · fin_cases i
      · linarith [(hR0_mem x hmem).2, le_max_left R0 R1]
      · linarith [(hR1_mem x hmem).2, le_max_right R0 R1]
  have hvan_sub : ∀ (i : Fin 2) {α : Coord → ℝ},
      tsupport α ⊆ tsupport (fun w => Ψ w i) →
      ∀ x : Coord, (x.1 ∉ Icc t₀ (t₀ + 1) ∨ R < |x.2.1| ∨ R < |x.2.2|) → α x = 0 :=
    fun i {_α} hsub x hx =>
      image_eq_zero_of_notMem_tsupport (fun hm => hnot_tsupp i x hx (hsub hm))

  have hpre_Ioo : (fun τ : ℝ => t₀ + τ) ⁻¹' Ioo t₀ (t₀ + 1) = Ioo (0 : ℝ) 1 := by
    ext τ; simp only [mem_preimage, mem_Ioo]
    constructor <;> intro h <;> exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hmp_Ioo : MeasurePreserving (fun τ : ℝ => t₀ + τ)
      (volume.restrict (Ioo 0 1)) (volume.restrict (Ioo t₀ (t₀ + 1))) := by
    simpa only [hpre_Ioo] using (measurePreserving_add_left volume t₀).restrict_preimage_emb
      (measurableEmbedding_addLeft t₀) (Ioo t₀ (t₀ + 1))

  have hunfold : ∀ {w : Coord → Fin 2 → ℝ}, StronglyMeasurable w →
      (∀ x : Coord, w (qShift p.c x) = w x) →
      (∫⁻ s in Icc t₀ (t₀ + 1), cylSliceL2 p.c (fun y => ofRealProf w (s, y))) < ⊤ →
      ∀ (i : Fin 2) {α : Coord → ℝ}, Continuous α →
        (∀ x : Coord, (x.1 ∉ Icc t₀ (t₀ + 1) ∨ R < |x.2.1| ∨ R < |x.2.2|) → α x = 0) →
        Integrable (fun x : Coord => (w x i : ℂ) * (α x : ℂ)) volume ∧
        IntegrableOn (fun τ : ℝ => ∫ y in B0579.cell p.c,
          w (t₀ + τ, y) i * TailPeriodizeAux.qPeriodize p.c α (t₀ + τ) y) (Ioo 0 1) volume ∧
        ∫ x : Coord, (w x i : ℂ) * (α x : ℂ) =
          Complex.ofReal (∫ τ in Ioo (0 : ℝ) 1, ∫ y in B0579.cell p.c,
            w (t₀ + τ, y) i * TailPeriodizeAux.qPeriodize p.c α (t₀ + τ) y) := by
    intro w hw_sm hw_per hw_loc i α hα_cont hα_supp
    have hwi_meas : AEStronglyMeasurable (fun x : Coord => (w x i : ℂ)) volume :=
      (Complex.continuous_ofReal.comp_stronglyMeasurable
        ((continuous_apply i).comp_stronglyMeasurable hw_sm)).aestronglyMeasurable
    have hwi_per : ∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}),
        (w (qShift p.c x) i : ℂ) = (w x i : ℂ) :=
      Eventually.of_forall fun x => by simp [hw_per x]
    have hwi_loc : (∫⁻ s in Icc t₀ (t₀ + 1),
        eLpNorm (fun z => (w (s, z) i : ℂ)) 2 (volume.restrict (B0579.cell p.c))) < ⊤ := by
      refine (lintegral_mono fun s => ?_).trans_lt hw_loc
      unfold cylSliceL2
      refine eLpNorm_mono_enorm fun z => ?_
      rw [enorm_eq_nnnorm, enorm_eq_nnnorm, ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
      exact PiLp.norm_apply_le (ofRealProf w (s, z)) i
    obtain ⟨hint_coord, hcell_int, heq_coord⟩ :=
      TailPeriodizeAux.integrable_and_integral_coord_eq_cell_qPeriodize hc ht₀ (by linarith)
        hR_pos hwi_meas hwi_per hwi_loc hα_cont hα_supp
    have hprod_R : Integrable
        (fun x : Coord => w x i * TailPeriodizeAux.qPeriodize p.c α x.1 x.2)
        ((volume.restrict (Icc t₀ (t₀ + 1))).prod (volume.restrict (B0579.cell p.c))) := by
      have hprod_C : Integrable
          (fun x : Coord => (w x i : ℂ) * (TailPeriodizeAux.qPeriodize p.c α x.1 x.2 : ℂ))
          ((volume.restrict (Icc t₀ (t₀ + 1))).prod (volume.restrict (B0579.cell p.c))) := by
        rwa [Measure.prod_restrict, ← Measure.volume_eq_prod]
      simpa using Complex.reCLM.integrable_comp hprod_C
    have hs_int : IntegrableOn
        (fun s : ℝ => ∫ y in B0579.cell p.c, w (s, y) i * TailPeriodizeAux.qPeriodize p.c α s y)
        (Ioo t₀ (t₀ + 1)) volume :=
      (show IntegrableOn _ (Icc t₀ (t₀ + 1)) volume from hprod_R.integral_prod_left).mono_set
        Ioo_subset_Icc_self
    have hτ_int : IntegrableOn
        (fun τ : ℝ => ∫ y in B0579.cell p.c,
          w (t₀ + τ, y) i * TailPeriodizeAux.qPeriodize p.c α (t₀ + τ) y)
        (Ioo 0 1) volume := by
      simpa [IntegrableOn, Function.comp_def] using
        (hmp_Ioo.integrable_comp_emb (measurableEmbedding_addLeft t₀)).2 hs_int
    refine ⟨hint_coord, hτ_int, ?_⟩
    rw [heq_coord]
    have hcast : (∫ s in Icc t₀ (t₀ + 1), ∫ y in B0579.cell p.c,
        (w (s, y) i : ℂ) * (TailPeriodizeAux.qPeriodize p.c α s y : ℂ)) =
        Complex.ofReal (∫ s in Icc t₀ (t₀ + 1), ∫ y in B0579.cell p.c,
          w (s, y) i * TailPeriodizeAux.qPeriodize p.c α s y) := by
      simp_rw [← Complex.ofReal_mul, integral_complex_ofReal]
    rw [hcast, integral_Icc_eq_integral_Ioo]
    have hsh := (measurePreserving_add_left volume t₀).setIntegral_preimage_emb
      (measurableEmbedding_addLeft t₀)
      (fun s : ℝ => ∫ y in B0579.cell p.c, w (s, y) i * TailPeriodizeAux.qPeriodize p.c α s y)
      (Ioo t₀ (t₀ + 1))
    rw [hpre_Ioo] at hsh
    exact congrArg Complex.ofReal hsh.symm

  have hunfold_pair : ∀ {w Ξ : Coord → Fin 2 → ℝ} {f : ℝ → ℝ},
      StronglyMeasurable w →
      (∀ x : Coord, w (qShift p.c x) = w x) →
      (∫⁻ s in Icc t₀ (t₀ + 1), cylSliceL2 p.c (fun y => ofRealProf w (s, y))) < ⊤ →
      (∀ i : Fin 2, Continuous (fun x => Ξ x i)) →
      (∀ i : Fin 2, ∀ x : Coord,
        (x.1 ∉ Icc t₀ (t₀ + 1) ∨ R < |x.2.1| ∨ R < |x.2.2|) → Ξ x i = 0) →
      (∀ τ ∈ Ioo (0 : ℝ) 1,
        (∫ y in B0579.cell p.c,
            w (t₀ + τ, y) 0 * TailPeriodizeAux.qPeriodize p.c (fun x => Ξ x 0) (t₀ + τ) y) +
          (∫ y in B0579.cell p.c,
            w (t₀ + τ, y) 1 * TailPeriodizeAux.qPeriodize p.c (fun x => Ξ x 1) (t₀ + τ) y) =
          f τ) →
      Integrable (fun x : Coord =>
        (w x 0 : ℂ) * (Ξ x 0 : ℂ) + (w x 1 : ℂ) * (Ξ x 1 : ℂ)) volume ∧
      IntegrableOn f (Ioo 0 1) volume ∧
      ∫ x : Coord, ((w x 0 : ℂ) * (Ξ x 0 : ℂ) + (w x 1 : ℂ) * (Ξ x 1 : ℂ)) =
        Complex.ofReal (∫ τ in Ioo (0 : ℝ) 1, f τ) := by
    intro w Ξ f hw_sm hw_per hw_loc hΞ_c hΞ_supp hpt
    obtain ⟨hi0, hτ0, heq0⟩ := hunfold hw_sm hw_per hw_loc 0 (hΞ_c 0) (hΞ_supp 0)
    obtain ⟨hi1, hτ1, heq1⟩ := hunfold hw_sm hw_per hw_loc 1 (hΞ_c 1) (hΞ_supp 1)
    refine ⟨hi0.add hi1, (hτ0.add hτ1).congr_fun hpt measurableSet_Ioo, ?_⟩
    rw [integral_add hi0 hi1, heq0, heq1, ← Complex.ofReal_add, ← integral_add hτ0 hτ1]
    exact congrArg Complex.ofReal (setIntegral_congr_fun measurableSet_Ioo hpt)

  have hslice_inner : ∀ {f ψ : L2v p.c} {w_sl Ξ_sl : B0579.Plane → Fin 2 → ℝ},
      (f : Plane → Vec2) =ᵐ[cellμ p.c] toVecSlice w_sl →
      (∀ i : Fin 2, B0579.IsCylTest p.c (fun y => Ξ_sl y i)) →
      (ψ : Plane → Vec2) =ᵐ[cellμ p.c] toVecSlice Ξ_sl →
      (∫ y in B0579.cell p.c, w_sl y 0 * Ξ_sl y 0) +
        (∫ y in B0579.cell p.c, w_sl y 1 * Ξ_sl y 1) = ⟪ψ, f⟫_ℝ := by
    intro f ψ w_sl Ξ_sl hfw hΞt hψΞ
    have hcoord : ∀ i : Fin 2,
        ∫ y in B0579.cell p.c, w_sl y i * Ξ_sl y i =
          ⟪f, cylSmoothToL2 (isCylSmooth_single (hΞt i) i)⟫_ℝ := by
      intro i
      rw [inner_cylSmooth_single (hΞt i) i f]
      have hfw' : ∀ᵐ y ∂(volume.restrict (B0579.cell p.c)),
          w_sl y i = (f : Plane → Vec2) y i := by
        rw [restrict_b0579_cell_eq_cellμ]
        exact hfw.mono fun y hy => (congrArg (fun v : Vec2 => v i) hy).symm
      exact integral_congr_ae (hfw'.mono fun y hy => congrArg (· * Ξ_sl y i) hy)
    rw [hcoord 0, hcoord 1, ← inner_add_right, real_inner_comm]
    congr 1
    apply Lp.ext
    filter_upwards [Lp.coeFn_add (cylSmoothToL2 (isCylSmooth_single (hΞt 0) 0))
        (cylSmoothToL2 (isCylSmooth_single (hΞt 1) 1)),
      (memLp_of_cylSmooth (isCylSmooth_single (hΞt 0) 0)).coeFn_toLp,
      (memLp_of_cylSmooth (isCylSmooth_single (hΞt 1) 1)).coeFn_toLp, hψΞ]
      with y hadd h0 h1 hψy
    rw [hadd, Pi.add_apply]
    dsimp only [cylSmoothToL2]
    rw [h0, h1, hψy]
    ext k
    fin_cases k <;> simp [toVecSlice]

  -- Clamped periodic drift profile `B_clamp`
  let B_clamp : Coord → Fin 2 → ℝ := fun x i =>
    p.train.v (t₀ + clamp01 (x.1 - t₀)) x.2 0 * zq x i +
    p.train.v (t₀ + clamp01 (x.1 - t₀)) x.2 1 * zη x i +
    z x 0 * fderiv ℝ (fun w => p.train.v (t₀ + clamp01 (x.1 - t₀)) w i) x.2 (B0579.dir 0) +
    z x 1 * fderiv ℝ (fun w => p.train.v (t₀ + clamp01 (x.1 - t₀)) w i) x.2 (B0579.dir 1)
  have hB_sm : StronglyMeasurable B_clamp := by
    let hspec := (clamped_train_coeffs hbg ht₀).choose_spec
    have hc_arg : Continuous (fun x : Coord => (x.1 - t₀, x.2)) :=
      (continuous_fst.sub continuous_const).prodMk continuous_snd
    have hV_sm : ∀ k : Fin 2,
        StronglyMeasurable (fun x : Coord => p.train.v (t₀ + clamp01 (x.1 - t₀)) x.2 k) :=
      fun k => ((hspec.2.1 k).comp hc_arg).stronglyMeasurable
    have hdV_sm : ∀ j i : Fin 2, StronglyMeasurable (fun x : Coord =>
        fderiv ℝ (fun w => p.train.v (t₀ + clamp01 (x.1 - t₀)) w i) x.2 (B0579.dir j)) :=
      fun j i => ((hspec.2.2.1 j i).comp hc_arg).stronglyMeasurable
    refine (measurable_pi_lambda _ fun i => ?_).stronglyMeasurable
    have hzi : ∀ k : Fin 2, StronglyMeasurable (fun x : Coord => z x k) :=
      fun k => (continuous_apply k).comp_stronglyMeasurable hz_sm
    have hzqi : StronglyMeasurable (fun x : Coord => zq x i) :=
      (continuous_apply i).comp_stronglyMeasurable hzq_sm
    have hzηi : StronglyMeasurable (fun x : Coord => zη x i) :=
      (continuous_apply i).comp_stronglyMeasurable hzη_sm
    exact (((((hV_sm 0).mul hzqi).add ((hV_sm 1).mul hzηi)).add
      ((hzi 0).mul (hdV_sm 0 i))).add ((hzi 1).mul (hdV_sm 1 i))).measurable
  have hB_per : ∀ x : Coord, B_clamp (qShift p.c x) = B_clamp x := by
    intro x
    ext i
    obtain ⟨hpz, hpzq, hpzη⟩ := hz_per x
    have hs_nn : 0 ≤ t₀ + clamp01 (x.1 - t₀) := by linarith [(clamp01_mem (x.1 - t₀)).1]
    have hq1 : (qShift p.c x).1 = x.1 := rfl
    have hq2 : (qShift p.c x).2 = (x.2.1 + p.c, x.2.2) := rfl
    have hpV : p.train.v (t₀ + clamp01 (x.1 - t₀)) (x.2.1 + p.c, x.2.2) =
        p.train.v (t₀ + clamp01 (x.1 - t₀)) x.2 :=
      p.train.isTrain.periodic_v (t₀ + clamp01 (x.1 - t₀)) hs_nn x.2
    have hpdV : ∀ j : Fin 2,
        fderiv ℝ (fun w => p.train.v (t₀ + clamp01 (x.1 - t₀)) w i)
          (x.2.1 + p.c, x.2.2) (B0579.dir j) =
        fderiv ℝ (fun w => p.train.v (t₀ + clamp01 (x.1 - t₀)) w i) x.2 (B0579.dir j) := by
      intro j
      let fi : Plane → ℝ := fun w => p.train.v (t₀ + clamp01 (x.1 - t₀)) w i
      have hVs : ContDiff ℝ ∞ (p.train.v (t₀ + clamp01 (x.1 - t₀))) :=
        contDiffOn_univ.1 (p.train.isTrain.smooth_v.comp
          (contDiff_const.prodMk contDiff_id).contDiffOn (s := univ)
          (fun w _ => ⟨hs_nn, mem_univ w⟩))
      have hfi_diff : Differentiable ℝ fi :=
        ((πR i).contDiff.comp hVs).differentiable (by simp)
      have hshift : HasFDerivAt (fun w : Plane => w + (p.c, (0 : ℝ)))
          (ContinuousLinearMap.id ℝ Plane) x.2 := by
        simpa using (hasFDerivAt_id x.2).add_const (p.c, (0 : ℝ))
      have hcomp := (hfi_diff (x.2 + (p.c, (0 : ℝ)))).hasFDerivAt.comp x.2 hshift
      have hfun : (fi ∘ fun w : Plane => w + (p.c, (0 : ℝ))) = fi := by
        funext w
        change p.train.v _ (w.1 + p.c, w.2 + 0) i = p.train.v _ w i
        rw [add_zero, p.train.isTrain.periodic_v _ hs_nn w]
      rw [hfun] at hcomp
      have heq : fderiv ℝ fi x.2 = fderiv ℝ fi (x.2 + (p.c, (0 : ℝ))) := by
        simpa using hcomp.fderiv
      have hz2 : (x.2.1 + p.c, x.2.2) = x.2 + (p.c, (0 : ℝ)) := by ext <;> simp
      change fderiv ℝ fi (x.2.1 + p.c, x.2.2) (B0579.dir j) = fderiv ℝ fi x.2 (B0579.dir j)
      rw [hz2, ← heq]
    dsimp only [B_clamp]
    rw [hpz, hpzq, hpzη, hq1, hq2, hpV, hpdV 0, hpdV 1]
  have hB_ae : ∀ s ∈ Icc t₀ (t₀ + 1),
      (b (s - t₀) : Plane → Vec2) =ᵐ[cellμ p.c] toVecSlice (fun y => B_clamp (s, y)) := by
    intro s hs
    obtain ⟨h0, hq, hη⟩ := hz_ae s hs
    exact trainBvCLM_ae hbg ht₀ (s - t₀) (U (s - t₀)) h0 hq hη

  -- Local `L¹([t₀, t₀ + 1]; L²(cell))` bounds for `z`, `B_clamp`, and `g₀`
  obtain ⟨Mu, hMu⟩ := isCompact_Icc.exists_bound_of_continuousOn hU_shift_cont
  let M_U : ℝ := max 0 Mu
  have hz_loc : (∫⁻ s in Icc t₀ (t₀ + 1),
      cylSliceL2 p.c (fun y => ofRealProf z (s, y))) < ⊤ := by
    have hle : ∫⁻ s in Icc t₀ (t₀ + 1), cylSliceL2 p.c (fun y => ofRealProf z (s, y)) ≤
        ∫⁻ _ in Icc t₀ (t₀ + 1), ENNReal.ofReal M_U := by
      refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
      rw [show (fun y => ofRealProf z (s, y)) = ofRealSlice (fun y => z (s, y)) from rfl,
        cylSliceL2_ofRealSlice_eq_ofReal_norm (hz_ae s hs).1]
      exact ENNReal.ofReal_le_ofReal ((norm_val0CLM_le _).trans ((hMu s hs).trans (le_max_right 0 Mu)))
    refine hle.trans_lt ?_
    simp [Real.volume_Icc]
  obtain ⟨Mb1, hMb1⟩ := isCompact_Icc.exists_bound_of_continuousOn hb_cont
  let M_B : ℝ := max 0 Mb1
  have hB_loc : (∫⁻ s in Icc t₀ (t₀ + 1),
      cylSliceL2 p.c (fun y => ofRealProf B_clamp (s, y))) < ⊤ := by
    have hle : ∫⁻ s in Icc t₀ (t₀ + 1), cylSliceL2 p.c (fun y => ofRealProf B_clamp (s, y)) ≤
        ∫⁻ _ in Icc t₀ (t₀ + 1), ENNReal.ofReal M_B := by
      refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
      rw [show (fun y => ofRealProf B_clamp (s, y)) = ofRealSlice (fun y => B_clamp (s, y)) from rfl,
        cylSliceL2_ofRealSlice_eq_ofReal_norm (hB_ae s hs)]
      exact ENNReal.ofReal_le_ofReal ((hMb1 (s - t₀) (hsub_map hs)).trans (le_max_right 0 Mb1))
    refine hle.trans_lt ?_
    simp [Real.volume_Icc]
  have hg_loc : (∫⁻ s in Icc t₀ (t₀ + 1),
      cylSliceL2 p.c (fun y => ofRealProf g₀ (s, y))) < ⊤ := by
    rw [setLIntegral_congr Ioo_ae_eq_Icc.symm]
    refine (lintegral_mono fun s => ?_).trans_lt hg_int
    unfold cylSliceL2 sliceH1Norm
    exact le_self_add.trans le_self_add

  have hB_flat : ∀ x : Coord,
      cdot (flatBv p.train (ofRealProf z) (ofRealProf zq) (ofRealProf zη)) Ψ x =
        ∑ i : Fin 2, (B_clamp x i : ℂ) * (Ψ x i : ℂ) := by
    intro x
    unfold cdot
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hx : x.1 ∈ Icc t₀ (t₀ + 1)
    · congr 1
      have hcl : clamp01 (x.1 - t₀) = x.1 - t₀ := clamp01_of_mem (hsub_map hx)
      have ht : t₀ + clamp01 (x.1 - t₀) = x.1 := by rw [hcl]; ring
      have hd0 : B0579.dir 0 = ((1 : ℝ), (0 : ℝ)) := by simp [B0579.dir]
      have hd1 : B0579.dir 1 = ((0 : ℝ), (1 : ℝ)) := by simp [B0579.dir]
      simp only [flatBv, ofRealProf, WithLp.ofLp_toLp, B_clamp, ht, hd0, hd1]
      push_cast
      ring
    · have h0 : Ψ x i = 0 := hvan_sub i Subset.rfl x (Or.inl hx)
      simp [h0]

  -- Coordinate test regularity and unfolding for all five pairs
  let Ψ11 : Coord → Fin 2 → ℝ := fun x i => cpd 1 (cpd 1 (fun w => Ψ w i)) x
  let Ψ22 : Coord → Fin 2 → ℝ := fun x i => cpd 2 (cpd 2 (fun w => Ψ w i)) x
  have hΨ_c : ∀ i : Fin 2, Continuous (fun w => Ψ w i) := fun i => (hΨ.smooth i).smooth.continuous
  have hΨ'_c : ∀ i : Fin 2, Continuous (fun w => Ψ' w i) := fun i => (hΨ'.smooth i).smooth.continuous
  have hφ1 : ∀ i : Fin 2, IsCoordTest (cpd 1 (fun w => Ψ w i)) :=
    fun i => planarTest_isCoordTest_partial (hΨ.smooth i) (cdir 1)
  have hφ2 : ∀ i : Fin 2, IsCoordTest (cpd 2 (fun w => Ψ w i)) :=
    fun i => planarTest_isCoordTest_partial (hΨ.smooth i) (cdir 2)
  have hφ11 : ∀ i : Fin 2, IsCoordTest (fun x => Ψ11 x i) :=
    fun i => planarTest_isCoordTest_partial (hφ1 i) (cdir 1)
  have hφ22 : ∀ i : Fin 2, IsCoordTest (fun x => Ψ22 x i) :=
    fun i => planarTest_isCoordTest_partial (hφ2 i) (cdir 2)
  have hsupp_0 : ∀ i : Fin 2,
      ∀ x : Coord, (x.1 ∉ Icc t₀ (t₀ + 1) ∨ R < |x.2.1| ∨ R < |x.2.2|) → Ψ x i = 0 :=
    fun i => hvan_sub i Subset.rfl
  have hsupp_t : ∀ i : Fin 2,
      ∀ x : Coord, (x.1 ∉ Icc t₀ (t₀ + 1) ∨ R < |x.2.1| ∨ R < |x.2.2|) → Ψ' x i = 0 :=
    fun i => hvan_sub i (tsupport_cpd_subset 0 _)
  have hsupp_11 : ∀ i : Fin 2, ∀ x : Coord,
      (x.1 ∉ Icc t₀ (t₀ + 1) ∨ R < |x.2.1| ∨ R < |x.2.2|) → Ψ11 x i = 0 :=
    fun i => hvan_sub i ((tsupport_cpd_subset 1 _).trans (tsupport_cpd_subset 1 _))
  have hsupp_22 : ∀ i : Fin 2, ∀ x : Coord,
      (x.1 ∉ Icc t₀ (t₀ + 1) ∨ R < |x.2.1| ∨ R < |x.2.2|) → Ψ22 x i = 0 :=
    fun i => hvan_sub i ((tsupport_cpd_subset 2 _).trans (tsupport_cpd_subset 2 _))

  -- Unfold RHS (`g₀`)
  obtain ⟨_, _, heq_G_pair⟩ :=
    hunfold_pair hg_sm hg0_per hg_loc hΨ_c hsupp_0
      (f := fun τ => ⟪φ₀ τ, val0CLM p.c (G τ)⟫_ℝ)
      (fun τ _ => hslice_inner (hG_ae τ) (hΦ τ).cyl_test (hφ₀_ae τ))
  have hrhs_eq : ∫ x : Coord, cdot (ofRealProf g₀) Ψ x =
      Complex.ofReal (∫ τ in Ioo (0 : ℝ) 1, ⟪φ₀ τ, val0CLM p.c (G τ)⟫_ℝ) := by
    have hfn : (fun x : Coord => cdot (ofRealProf g₀) Ψ x) =
        fun x : Coord => (g₀ x 0 : ℂ) * (Ψ x 0 : ℂ) + (g₀ x 1 : ℂ) * (Ψ x 1 : ℂ) := by
      funext x; simp [cdot, Fin.sum_univ_two, ofRealProf]
    rw [hfn, heq_G_pair]

  -- Unfold each of the four LHS pairs (`zt`, `z11`, `z22`, `B`)
  obtain ⟨hi_zt, hτ_zt_f, heq_zt_f⟩ :=
    hunfold_pair hz_sm (fun x => (hz_per x).1) hz_loc hΨ'_c hsupp_t
      (f := fun τ => ⟪φ₀' τ, val0CLM p.c (U τ)⟫_ℝ)
      (fun τ hτ => by
        have hsτ : t₀ + τ ∈ Icc t₀ (t₀ + 1) := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
        have hz0_τ : (val0CLM p.c (U τ) : Plane → Vec2) =ᵐ[cellμ p.c]
            toVecSlice (fun y => z (t₀ + τ, y)) := by
          simpa only [add_sub_cancel_left] using (hz_ae (t₀ + τ) hsτ).1
        exact hslice_inner hz0_τ (hΦ' τ).cyl_test (hφ₀'_ae τ))
  obtain ⟨hi_B, hτ_B_f, heq_B_f⟩ :=
    hunfold_pair hB_sm hB_per hB_loc hΨ_c hsupp_0
      (f := fun τ => ⟪φ₀ τ, b τ⟫_ℝ)
      (fun τ hτ => by
        have hsτ : t₀ + τ ∈ Icc t₀ (t₀ + 1) := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
        have hb_τ : (b τ : Plane → Vec2) =ᵐ[cellμ p.c]
            toVecSlice (fun y => B_clamp (t₀ + τ, y)) := by
          simpa only [add_sub_cancel_left] using hB_ae (t₀ + τ) hsτ
        exact hslice_inner hb_τ (hΦ τ).cyl_test (hφ₀_ae τ))
  obtain ⟨hi_z11, hτ_z11_f, heq_z11_f⟩ :=
    hunfold_pair hz_sm (fun x => (hz_per x).1) hz_loc
      (fun i => (hφ11 i).smooth.continuous) hsupp_11
      (f := fun τ => -⟪φq τ, dqCLM p.c (U τ)⟫_ℝ)
      (fun τ hτ => by
        have hsτ : t₀ + τ ∈ Icc t₀ (t₀ + 1) := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
        have hz0_τ : (val0CLM p.c (U τ) : Plane → Vec2) =ᵐ[cellμ p.c]
            toVecSlice (fun y => z (t₀ + τ, y)) := by
          simpa only [add_sub_cancel_left] using (hz_ae (t₀ + τ) hsτ).1
        have hibp : ∀ i : Fin 2,
            ∫ y in B0579.cell p.c,
              z (t₀ + τ, y) i *
                TailPeriodizeAux.qPeriodize p.c (fun x => Ψ11 x i) (t₀ + τ) y =
              -∫ y in B0579.cell p.c,
                (dqCLM p.c (U τ) : Plane → Vec2) y i *
                  TailPeriodizeAux.qPeriodize p.c (cpd 1 (fun w => Ψ w i)) (t₀ + τ) y := by
          intro i
          let ψ1i := TailPeriodizeAux.qPeriodize p.c (cpd 1 (fun w => Ψ w i)) (t₀ + τ)
          have htest : B0579.IsCylTest p.c ψ1i :=
            TailPeriodizeAux.isCylTest_qPeriodize hc (hφ1 i) (t₀ + τ)
          have hae : ∀ᵐ y ∂(volume.restrict (B0579.cell p.c)),
              z (t₀ + τ, y) i *
                TailPeriodizeAux.qPeriodize p.c (fun x => Ψ11 x i) (t₀ + τ) y =
              (val0CLM p.c (U τ) : Plane → Vec2) y i * B0579.pd 0 ψ1i y := by
            rw [restrict_b0579_cell_eq_cellμ]
            filter_upwards [hz0_τ] with y hy
            dsimp only [ψ1i, Ψ11]
            rw [TailPeriodizeAux.pd_qPeriodize hc (hφ1 i) (t₀ + τ) 0 y]
            change z (t₀ + τ, y) i *
                TailPeriodizeAux.qPeriodize p.c (cpd 1 (cpd 1 fun w => Ψ w i)) (t₀ + τ) y =
              (val0CLM p.c (U τ) : Plane → Vec2) y i *
                TailPeriodizeAux.qPeriodize p.c (cpd 1 (cpd 1 fun w => Ψ w i)) (t₀ + τ) y
            exact congrArg (· * _) (congrArg (fun v : Vec2 => v i) hy).symm
          exact (integral_congr_ae hae).trans ((H1Sol.weak_q (U τ) i).2 ψ1i htest)
        have hvec : (dqCLM p.c (U τ) : Plane → Vec2) =ᵐ[cellμ p.c]
            toVecSlice (fun y k => (dqCLM p.c (U τ) : Plane → Vec2) y k) :=
          Eventually.of_forall fun y => by ext k; rfl
        have hsum := hslice_inner hvec
          (fun i => TailPeriodizeAux.isCylTest_qPeriodize hc (hφ1 i) (t₀ + τ)) (hφq_ae τ)
        rw [hibp 0, hibp 1]
        dsimp only [TailPeriodizeAux.qPeriodizeVec] at hsum
        linarith)
  obtain ⟨hi_z22, hτ_z22_f, heq_z22_f⟩ :=
    hunfold_pair hz_sm (fun x => (hz_per x).1) hz_loc
      (fun i => (hφ22 i).smooth.continuous) hsupp_22
      (f := fun τ => -⟪φη τ, detaCLM p.c (U τ)⟫_ℝ)
      (fun τ hτ => by
        have hsτ : t₀ + τ ∈ Icc t₀ (t₀ + 1) := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
        have hz0_τ : (val0CLM p.c (U τ) : Plane → Vec2) =ᵐ[cellμ p.c]
            toVecSlice (fun y => z (t₀ + τ, y)) := by
          simpa only [add_sub_cancel_left] using (hz_ae (t₀ + τ) hsτ).1
        have hibp : ∀ i : Fin 2,
            ∫ y in B0579.cell p.c,
              z (t₀ + τ, y) i *
                TailPeriodizeAux.qPeriodize p.c (fun x => Ψ22 x i) (t₀ + τ) y =
              -∫ y in B0579.cell p.c,
                (detaCLM p.c (U τ) : Plane → Vec2) y i *
                  TailPeriodizeAux.qPeriodize p.c (cpd 2 (fun w => Ψ w i)) (t₀ + τ) y := by
          intro i
          let ψ2i := TailPeriodizeAux.qPeriodize p.c (cpd 2 (fun w => Ψ w i)) (t₀ + τ)
          have htest : B0579.IsCylTest p.c ψ2i :=
            TailPeriodizeAux.isCylTest_qPeriodize hc (hφ2 i) (t₀ + τ)
          have hae : ∀ᵐ y ∂(volume.restrict (B0579.cell p.c)),
              z (t₀ + τ, y) i *
                TailPeriodizeAux.qPeriodize p.c (fun x => Ψ22 x i) (t₀ + τ) y =
              (val0CLM p.c (U τ) : Plane → Vec2) y i * B0579.pd 1 ψ2i y := by
            rw [restrict_b0579_cell_eq_cellμ]
            filter_upwards [hz0_τ] with y hy
            dsimp only [ψ2i, Ψ22]
            rw [TailPeriodizeAux.pd_qPeriodize hc (hφ2 i) (t₀ + τ) 1 y]
            change z (t₀ + τ, y) i *
                TailPeriodizeAux.qPeriodize p.c (cpd 2 (cpd 2 fun w => Ψ w i)) (t₀ + τ) y =
              (val0CLM p.c (U τ) : Plane → Vec2) y i *
                TailPeriodizeAux.qPeriodize p.c (cpd 2 (cpd 2 fun w => Ψ w i)) (t₀ + τ) y
            exact congrArg (· * _) (congrArg (fun v : Vec2 => v i) hy).symm
          exact (integral_congr_ae hae).trans ((H1Sol.weak_eta (U τ) i).2 ψ2i htest)
        have hvec : (detaCLM p.c (U τ) : Plane → Vec2) =ᵐ[cellμ p.c]
            toVecSlice (fun y k => (detaCLM p.c (U τ) : Plane → Vec2) y k) :=
          Eventually.of_forall fun y => by ext k; rfl
        have hsum := hslice_inner hvec
          (fun i => TailPeriodizeAux.isCylTest_qPeriodize hc (hφ2 i) (t₀ + τ)) (hφη_ae τ)
        rw [hibp 0, hibp 1]
        dsimp only [TailPeriodizeAux.qPeriodizeVec] at hsum
        linarith)

  -- Combine LHS pieces (`z * meridTranspose + flatBv`)
  have hlhs_eq : ∫ x : Coord,
      (∑ i : Fin 2, ofRealProf z x i * meridTranspose p.ν Ψ x i +
        cdot (flatBv p.train (ofRealProf z) (ofRealProf zq) (ofRealProf zη)) Ψ x) =
      Complex.ofReal (∫ τ in Ioo (0 : ℝ) 1, (I_PDE τ + ⟪φ₀ τ, b τ⟫_ℝ)) := by
    have hcomb4 : ∀ {α 𝕜 : Type} [MeasurableSpace α] [RCLike 𝕜] {μ : Measure α}
        (r : 𝕜) {f1 f2 f3 f4 : α → 𝕜}
        (h1 : Integrable f1 μ) (h2 : Integrable f2 μ)
        (h3 : Integrable f3 μ) (h4 : Integrable f4 μ),
        ∫ x, ((-f1 x - r * (f2 x + f3 x)) + f4 x) ∂μ =
          -(∫ x, f1 x ∂μ) - r * ((∫ x, f2 x ∂μ) + (∫ x, f3 x ∂μ)) + (∫ x, f4 x ∂μ) := by
      intro α 𝕜 _ _ μ r f1 f2 f3 f4 h1 h2 h3 h4
      have h23 : Integrable (fun x => f2 x + f3 x) μ := h2.add h3
      have hr23 : Integrable (fun x => r * (f2 x + f3 x)) μ := h23.const_mul r
      have h1n : Integrable (fun x => -f1 x) μ := h1.neg
      have h123 : Integrable (fun x => -f1 x - r * (f2 x + f3 x)) μ := h1n.sub hr23
      rw [MeasureTheory.integral_add h123 h4, MeasureTheory.integral_sub h1n hr23,
        MeasureTheory.integral_neg, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_add h2 h3]
    have hmt : ∀ (x : Coord) (i : Fin 2),
        ofRealProf z x i * meridTranspose p.ν Ψ x i =
          -((z x i : ℂ) * (Ψ' x i : ℂ)) -
            (p.ν : ℂ) * ((z x i : ℂ) * (Ψ11 x i : ℂ) + (z x i : ℂ) * (Ψ22 x i : ℂ)) := by
      intro x i
      dsimp only [ofRealProf, meridTranspose, Ψ', Ψ11, Ψ22, WithLp.ofLp_toLp]
      push_cast
      ring
    have hfn : (fun x : Coord =>
        ∑ i : Fin 2, ofRealProf z x i * meridTranspose p.ν Ψ x i +
          cdot (flatBv p.train (ofRealProf z) (ofRealProf zq) (ofRealProf zη)) Ψ x) =
        fun x : Coord =>
          (-(((z x 0 : ℂ) * (Ψ' x 0 : ℂ)) + ((z x 1 : ℂ) * (Ψ' x 1 : ℂ))) -
            (p.ν : ℂ) *
              ((((z x 0 : ℂ) * (Ψ11 x 0 : ℂ)) + ((z x 1 : ℂ) * (Ψ11 x 1 : ℂ))) +
                (((z x 0 : ℂ) * (Ψ22 x 0 : ℂ)) + ((z x 1 : ℂ) * (Ψ22 x 1 : ℂ))))) +
          (((B_clamp x 0 : ℂ) * (Ψ x 0 : ℂ)) + ((B_clamp x 1 : ℂ) * (Ψ x 1 : ℂ))) := by
      funext x
      rw [Fin.sum_univ_two, hmt x 0, hmt x 1, hB_flat x, Fin.sum_univ_two]
      ring
    have hlhs_split : ∫ x : Coord,
        (∑ i : Fin 2, ofRealProf z x i * meridTranspose p.ν Ψ x i +
          cdot (flatBv p.train (ofRealProf z) (ofRealProf zq) (ofRealProf zη)) Ψ x) =
        -(∫ x : Coord, ((z x 0 : ℂ) * (Ψ' x 0 : ℂ) + (z x 1 : ℂ) * (Ψ' x 1 : ℂ))) -
          (p.ν : ℂ) *
            ((∫ x : Coord, ((z x 0 : ℂ) * (Ψ11 x 0 : ℂ) + (z x 1 : ℂ) * (Ψ11 x 1 : ℂ))) +
              (∫ x : Coord, ((z x 0 : ℂ) * (Ψ22 x 0 : ℂ) + (z x 1 : ℂ) * (Ψ22 x 1 : ℂ)))) +
          (∫ x : Coord, ((B_clamp x 0 : ℂ) * (Ψ x 0 : ℂ) + (B_clamp x 1 : ℂ) * (Ψ x 1 : ℂ))) := by
      rw [hfn]
      exact hcomb4 (p.ν : ℂ) hi_zt hi_z11 hi_z22 hi_B
    have hI_split : ∫ τ in Ioo (0 : ℝ) 1, (I_PDE τ + ⟪φ₀ τ, b τ⟫_ℝ) =
        -(∫ τ in Ioo (0 : ℝ) 1, ⟪φ₀' τ, val0CLM p.c (U τ)⟫_ℝ) -
          p.ν * ((∫ τ in Ioo (0 : ℝ) 1, -⟪φq τ, dqCLM p.c (U τ)⟫_ℝ) +
            (∫ τ in Ioo (0 : ℝ) 1, -⟪φη τ, detaCLM p.c (U τ)⟫_ℝ)) +
          (∫ τ in Ioo (0 : ℝ) 1, ⟪φ₀ τ, b τ⟫_ℝ) := by
      have hI_eq : (fun τ => I_PDE τ + ⟪φ₀ τ, b τ⟫_ℝ) = fun τ =>
          (-⟪φ₀' τ, val0CLM p.c (U τ)⟫_ℝ -
            p.ν * ((-⟪φq τ, dqCLM p.c (U τ)⟫_ℝ) + (-⟪φη τ, detaCLM p.c (U τ)⟫_ℝ))) +
          ⟪φ₀ τ, b τ⟫_ℝ := by
        funext τ; dsimp only [I_PDE]; ring
      rw [hI_eq]
      exact hcomb4 (μ := volume.restrict (Ioo 0 1)) p.ν hτ_zt_f hτ_z11_f hτ_z22_f hτ_B_f
    rw [hlhs_split, heq_zt_f, heq_z11_f, heq_z22_f, heq_B_f, hI_split]
    push_cast
    ring

  rw [hlhs_eq, hrhs_eq, hreal_master]

theorem realCylUnitOseenStep_proof : RealCylUnitOseenStep := by
  intro p d dm dp t₀ hbg ht₀ u₀ uq₀ uη₀ hu_sm huq_sm huη_sm _hu_per hu_h1
    g₀ gq₀ gη₀ hg_sm hgq_sm hgη_sm hg_per _hg_supp hg_h1 hg_int
  have hc : 0 < p.c := p.c_pos
  have hν : 0 < p.ν := p.ν_pos
  -- Step 1: Source path `G : ℝ → H1Sol p.c` and its continuous heat Duhamel integral `S_G`
  let G : ℝ → H1Sol p.c := fun σ => h1SolOfCylSlice (hg_h1 (t₀ + σ))
  have hG_sm_comp : ∀ (w : Coord → Fin 2 → ℝ) (hw : StronglyMeasurable w)
      (hmem : ∀ s : ℝ, MemLp (toVecSlice (fun y => w (s, y))) 2 (cellμ p.c)),
      StronglyMeasurable (fun σ : ℝ =>
        (memLp_toVecSlice_of_ofRealSlice
          (stronglyMeasurable_ofRealSlice_aux
            (hw.comp_measurable (measurable_const.prodMk measurable_id)))
          ⟨(stronglyMeasurable_ofRealSlice_aux
            (hw.comp_measurable
              (measurable_const.prodMk measurable_id))).aestronglyMeasurable,
            (cylSliceL2_ofRealSlice_eq_eLpNorm p.c _).trans_lt (hmem (t₀ + σ)).eLpNorm_lt_top⟩).toLp
          (toVecSlice (fun y => w (t₀ + σ, y)))) := by
    intro w hw hmem
    let F_w : ℝ × Plane → Vec2 := fun q => toVecSlice (fun y => w (t₀ + q.1, y)) q.2
    have hF_meas : Measurable F_w := by
      refine (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_lambda _ fun i => ?_)
      have hcomp : StronglyMeasurable (fun q : ℝ × Plane => w (t₀ + q.1, q.2)) :=
        hw.comp_measurable ((measurable_const.add measurable_fst).prodMk measurable_snd)
      exact ((continuous_apply i).comp_stronglyMeasurable hcomp).measurable
    have hpath := UnforcedLeray.Short.IIIa.lmToL2vPath p.c hc F_w hF_meas
    convert hpath using 1
    funext σ
    change _ = UnforcedLeray.Short.IIIa.toL2v p.c (toVecSlice (fun y => w (t₀ + σ, y)))
    simp only [UnforcedLeray.Short.IIIa.toL2v, hmem (t₀ + σ), ↓reduceDIte]
  have hG0_sm : StronglyMeasurable (fun σ : ℝ => val0CLM p.c (G σ)) :=
    hG_sm_comp g₀ hg_sm (fun s => memLp_toVecSlice_of_ofRealSlice (hg_h1 s).sm_u (hg_h1 s).memL2_u)
  have hGq_sm : StronglyMeasurable (fun σ : ℝ => dqCLM p.c (G σ)) :=
    hG_sm_comp gq₀ hgq_sm (fun s => memLp_toVecSlice_of_ofRealSlice (hg_h1 s).sm_uq (hg_h1 s).memL2_uq)
  have hGη_sm : StronglyMeasurable (fun σ : ℝ => detaCLM p.c (G σ)) :=
    hG_sm_comp gη₀ hgη_sm (fun s => memLp_toVecSlice_of_ofRealSlice (hg_h1 s).sm_uη (hg_h1 s).memL2_uη)
  have hG_sm : StronglyMeasurable G :=
    (Embedding.comp_stronglyMeasurable_iff Topology.IsEmbedding.subtypeVal).1
      (hG0_sm.prodMk (hGq_sm.prodMk hGη_sm))
  have hG_int : IntegrableOn G (Icc 0 1) volume := by
    refine ⟨hG_sm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, setLIntegral_congr Ioo_ae_eq_Icc.symm]
    have hle : ∫⁻ σ in Ioo (0 : ℝ) 1, ‖G σ‖ₑ ≤
        ∫⁻ σ in Ioo (0 : ℝ) 1,
          sliceH1Norm p.c (ofRealProf g₀) (ofRealProf gq₀) (ofRealProf gη₀) (t₀ + σ) := by
      refine lintegral_mono fun σ => ?_
      exact enorm_h1SolOfCylSlice_le (hg_h1 (t₀ + σ))
    have hpre : (fun σ : ℝ => t₀ + σ) ⁻¹' Ioo t₀ (t₀ + 1) = Ioo (0 : ℝ) 1 := by
      ext σ; simp only [mem_preimage, mem_Ioo]
      constructor <;> intro h <;> exact ⟨by linarith [h.1], by linarith [h.2]⟩
    have hshift := (measurePreserving_add_left volume t₀).setLIntegral_comp_preimage_emb
      (measurableEmbedding_addLeft t₀)
      (sliceH1Norm p.c (ofRealProf g₀) (ofRealProf gq₀) (ofRealProf gη₀))
      (Ioo t₀ (t₀ + 1))
    rw [hpre] at hshift
    exact (hle.trans_eq hshift).trans_lt hg_int
  let S_G : ℝ → H1Sol p.c := fun τ => ∫ σ in (0 : ℝ)..τ, freeH1CLM hc (p.ν * (τ - σ)) (G σ)
  have hSG_cont : ContinuousOn S_G (Icc 0 1) := by
    refine UnforcedLeray.BochnerTime.continuousOn_duhamel
      (U := fun τ σ => freeH1CLM hc (p.ν * (τ - σ))) (M := 1) ?_ ?_ hG_int
    · intro x
      exact ((continuous_freeH1CLM_apply hc x).comp
        (continuous_const.mul (continuous_fst.sub continuous_snd))).continuousOn
    · intro s t _ _ _
      exact norm_freeH1CLM_le hc (p.ν * (s - t))
  have hSG_zero : S_G 0 = 0 := intervalIntegral.integral_same

  -- Step 2: VolterraData on `[0, 1]` and mild solution `U : ℝ → H1Sol p.c`
  let C₀_val : ℝ := max 1 ((2 / Real.sqrt Real.pi) * p.ν ^ (-(1 / 2 : ℝ)))
  let D : VolterraData ℝ (H1Sol p.c) (L2v p.c) :=
    { S₀ := fun τ => freeH1CLM hc (p.ν * τ)
      S := fun τ => -duhH1CLM hc (p.ν * τ)
      B := fun r => trainBvCLM hbg ht₀ r
      M₀ := 1
      C₀ := C₀_val
      β := 6 * trainDriftBound hbg ht₀
      norm_S₀_le := fun t _ _ => norm_freeH1CLM_le hc (p.ν * t)
      norm_S_le := fun t ht_pos ht1 => by
        rw [norm_neg]
        refine (norm_duhH1CLM_le hc (mul_pos hν ht_pos)).trans ?_
        have h1_rp : 1 ≤ t ^ (-(1 / 2 : ℝ)) :=
          Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht_pos ht1 (by norm_num)
        have h1_C : 1 ≤ C₀_val * t ^ (-(1 / 2 : ℝ)) := by
          have hc1 : 1 ≤ C₀_val := le_max_left _ _
          nlinarith
        have h2_C : heatDivL2Coeff (p.ν * t) ≤ C₀_val * t ^ (-(1 / 2 : ℝ)) := by
          rw [heatDivL2Coeff_eq_singular hν ht_pos, ← mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _)
            (Real.rpow_nonneg ht_pos.le _)
        exact max_le h1_C h2_C
      norm_B_le := fun t => norm_trainBvCLM_le hbg ht₀ t
      continuousOn_S₀ := fun x =>
        ((continuous_freeH1CLM_apply hc x).comp (continuous_const.mul continuous_id)).continuousOn
      continuousOn_S := fun y =>
        ((continuousOn_duhH1CLM_apply hc y).comp
          (continuousOn_const.mul continuousOn_id)
          (fun t (ht : t ∈ Ioc 0 1) => mul_pos hν ht.1)).neg
      continuous_B := fun x => continuous_trainBvCLM_apply hbg ht₀ x }
  let u_sol : H1Sol p.c := h1SolOfCylSlice hu_h1
  let f₀ : ℝ → H1Sol p.c := fun τ => freeH1CLM hc (p.ν * τ) u_sol + S_G τ
  have hf₀_cont : ContinuousOn f₀ (Icc 0 1) :=
    ((continuous_freeH1CLM_apply hc u_sol).comp
      (continuous_const.mul continuous_id)).continuousOn.add hSG_cont
  have hf₀_zero : f₀ 0 = u_sol := by
    dsimp [f₀]
    rw [mul_zero, freeH1CLM_of_nonpos hc le_rfl, ContinuousLinearMap.id_apply, hSG_zero, add_zero]
  obtain ⟨U, hU_cont, hU_zero_f₀, hU_vol⟩ := exists_inhomo_volterra_sol D hf₀_cont
  have hU_zero : U 0 = u_sol := hU_zero_f₀.trans hf₀_zero

  -- Step 3: Jointly `StronglyMeasurable` periodic representatives `(z, zq, zη)`
  have hsub_map : MapsTo (fun s : ℝ => s - t₀) (Icc t₀ (t₀ + 1)) (Icc 0 1) :=
    fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hU_shift_cont : ContinuousOn (fun s : ℝ => U (s - t₀)) (Icc t₀ (t₀ + 1)) :=
    hU_cont.comp (continuousOn_id.sub continuousOn_const) hsub_map
  obtain ⟨F0, hF0_sm, hF0_ae⟩ :=
    UnforcedLeray.Infra.JointMeasurableRep.exists_stronglyMeasurable_rep_of_continuousOn_Icc
      ((val0CLM p.c).continuous.comp_continuousOn hU_shift_cont)
  obtain ⟨Fq, hFq_sm, hFq_ae⟩ :=
    UnforcedLeray.Infra.JointMeasurableRep.exists_stronglyMeasurable_rep_of_continuousOn_Icc
      ((dqCLM p.c).continuous.comp_continuousOn hU_shift_cont)
  obtain ⟨Fη, hFη_sm, hFη_ae⟩ :=
    UnforcedLeray.Infra.JointMeasurableRep.exists_stronglyMeasurable_rep_of_continuousOn_Icc
      ((detaCLM p.c).continuous.comp_continuousOn hU_shift_cont)
  let z : Coord → Fin 2 → ℝ := fun x i => F0 (x.1, toCellLocal p.c x.2) i
  let zq : Coord → Fin 2 → ℝ := fun x i => Fq (x.1, toCellLocal p.c x.2) i
  let zη : Coord → Fin 2 → ℝ := fun x i => Fη (x.1, toCellLocal p.c x.2) i
  have hm_ret : Measurable (fun x : Coord => (x.1, toCellLocal p.c x.2)) :=
    measurable_fst.prodMk ((measurable_toCellLocal p.c).comp measurable_snd)
  have hz_sm : StronglyMeasurable z :=
    (measurable_pi_lambda _ fun i =>
      ((πR i).continuous.comp_stronglyMeasurable (hF0_sm.comp_measurable hm_ret)).measurable).stronglyMeasurable
  have hzq_sm : StronglyMeasurable zq :=
    (measurable_pi_lambda _ fun i =>
      ((πR i).continuous.comp_stronglyMeasurable (hFq_sm.comp_measurable hm_ret)).measurable).stronglyMeasurable
  have hzη_sm : StronglyMeasurable zη :=
    (measurable_pi_lambda _ fun i =>
      ((πR i).continuous.comp_stronglyMeasurable (hFη_sm.comp_measurable hm_ret)).measurable).stronglyMeasurable
  have hz_per : ∀ x : Coord,
      z (qShift p.c x) = z x ∧ zq (qShift p.c x) = zq x ∧ zη (qShift p.c x) = zη x := by
    intro x
    have hret : toCellLocal p.c (qShift p.c x).2 = toCellLocal p.c x.2 :=
      toCellLocal_periodic hc x.2
    exact ⟨funext fun i => by dsimp [z]; rw [hret],
      funext fun i => by dsimp [zq]; rw [hret],
      funext fun i => by dsimp [zη]; rw [hret]⟩
  have hcell_mem : ∀ᵐ y ∂(cellμ p.c), y ∈ B0579.cell p.c := by
    rw [← restrict_b0579_cell_eq_cellμ]
    exact ae_restrict_mem (B0579.measurableSet_cell p.c)
  have hz_ae : ∀ s ∈ Icc t₀ (t₀ + 1),
      ((val0CLM p.c (U (s - t₀)) : Plane → Vec2) =ᵐ[cellμ p.c] toVecSlice (fun y => z (s, y))) ∧
      ((dqCLM p.c (U (s - t₀)) : Plane → Vec2) =ᵐ[cellμ p.c] toVecSlice (fun y => zq (s, y))) ∧
      ((detaCLM p.c (U (s - t₀)) : Plane → Vec2) =ᵐ[cellμ p.c] toVecSlice (fun y => zη (s, y))) := by
    intro s hs
    refine ⟨?_, ?_, ?_⟩
    · filter_upwards [(hF0_ae s hs).symm, hcell_mem] with y hy hcell
      ext i; exact (congrArg (fun v : Vec2 => v i) hy).trans
        (by dsimp [toVecSlice, z]; rw [toCellLocal_eq_self_of_mem_cell hc hcell])
    · filter_upwards [(hFq_ae s hs).symm, hcell_mem] with y hy hcell
      ext i; exact (congrArg (fun v : Vec2 => v i) hy).trans
        (by dsimp [toVecSlice, zq]; rw [toCellLocal_eq_self_of_mem_cell hc hcell])
    · filter_upwards [(hFη_ae s hs).symm, hcell_mem] with y hy hcell
      ext i; exact (congrArg (fun v : Vec2 => v i) hy).trans
        (by dsimp [toVecSlice, zη]; rw [toCellLocal_eq_self_of_mem_cell hc hcell])

  -- Step 4: Slice `IsCylH1Slice`, initial condition at `t₀`, and `cylSliceH1` continuity
  have hz_slice : ∀ s ∈ Icc t₀ (t₀ + 1),
      IsCylH1Slice p.c (fun y => ofRealProf z (s, y))
        (fun y => ofRealProf zq (s, y)) (fun y => ofRealProf zη (s, y)) := by
    intro s hs
    obtain ⟨h0, hq, hη⟩ := hz_ae s hs
    exact isCylH1Slice_of_h1Sol_ae (U (s - t₀))
      (hz_sm.comp_measurable (measurable_const.prodMk measurable_id))
      (hzq_sm.comp_measurable (measurable_const.prodMk measurable_id))
      (hzη_sm.comp_measurable (measurable_const.prodMk measurable_id))
      h0 hq hη
  have hz_init : cylSliceH1 p.c (fun y => ofRealProf z (t₀, y) - ofRealSlice u₀ y)
      (fun y => ofRealProf zq (t₀, y) - ofRealSlice uq₀ y)
      (fun y => ofRealProf zη (t₀, y) - ofRealSlice uη₀ y) = 0 := by
    obtain ⟨hz0, hzq0, hzη0⟩ := hz_ae t₀ ⟨le_rfl, by linarith⟩
    obtain ⟨hu0, huq0, huη0⟩ := h1SolOfCylSlice_ae hu_h1
    change cylSliceL2 p.c (fun y => ofRealSlice (fun y => z (t₀, y)) y - ofRealSlice u₀ y) +
      cylSliceL2 p.c (fun y => ofRealSlice (fun y => zq (t₀, y)) y - ofRealSlice uq₀ y) +
      cylSliceL2 p.c (fun y => ofRealSlice (fun y => zη (t₀, y)) y - ofRealSlice uη₀ y) = 0
    rw [cylSliceL2_sub_ofRealSlice_eq_ofReal_norm hz0 hu0,
      cylSliceL2_sub_ofRealSlice_eq_ofReal_norm hzq0 huq0,
      cylSliceL2_sub_ofRealSlice_eq_ofReal_norm hzη0 huη0]
    simp [sub_self, hU_zero, u_sol]
  have hz_cont : ∀ s ∈ Icc t₀ (t₀ + 1),
      Tendsto (fun s' => cylSliceH1 p.c
        (fun y => ofRealProf z (s', y) - ofRealProf z (s, y))
        (fun y => ofRealProf zq (s', y) - ofRealProf zq (s, y))
        (fun y => ofRealProf zη (s', y) - ofRealProf zη (s, y)))
        (𝓝[Icc t₀ (t₀ + 1)] s) (𝓝 0) := by
    intro s hs
    obtain ⟨hs0, hsq, hsη⟩ := hz_ae s hs
    have hev : (fun s' =>
        ENNReal.ofReal ‖val0CLM p.c (U (s' - t₀)) - val0CLM p.c (U (s - t₀))‖ +
        ENNReal.ofReal ‖dqCLM p.c (U (s' - t₀)) - dqCLM p.c (U (s - t₀))‖ +
        ENNReal.ofReal ‖detaCLM p.c (U (s' - t₀)) - detaCLM p.c (U (s - t₀))‖) =ᶠ[𝓝[Icc t₀ (t₀ + 1)] s]
        fun s' => cylSliceH1 p.c
          (fun y => ofRealProf z (s', y) - ofRealProf z (s, y))
          (fun y => ofRealProf zq (s', y) - ofRealProf zq (s, y))
          (fun y => ofRealProf zη (s', y) - ofRealProf zη (s, y)) := by
      filter_upwards [self_mem_nhdsWithin] with s' hs'
      obtain ⟨h0', hq', hη'⟩ := hz_ae s' hs'
      rw [← cylSliceL2_sub_ofRealSlice_eq_ofReal_norm h0' hs0,
        ← cylSliceL2_sub_ofRealSlice_eq_ofReal_norm hq' hsq,
        ← cylSliceL2_sub_ofRealSlice_eq_ofReal_norm hη' hsη]
      rfl
    refine Tendsto.congr' hev ?_
    have htU : Tendsto (fun s' => U (s' - t₀)) (𝓝[Icc t₀ (t₀ + 1)] s) (𝓝 (U (s - t₀))) :=
      hU_shift_cont s hs
    have ht0 : Tendsto (fun s' => ENNReal.ofReal ‖val0CLM p.c (U (s' - t₀)) - val0CLM p.c (U (s - t₀))‖)
        (𝓝[Icc t₀ (t₀ + 1)] s) (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact (ENNReal.continuous_ofReal.tendsto 0).comp
        (tendsto_iff_norm_sub_tendsto_zero.mp (((val0CLM p.c).continuous.tendsto _).comp htU))
    have htq : Tendsto (fun s' => ENNReal.ofReal ‖dqCLM p.c (U (s' - t₀)) - dqCLM p.c (U (s - t₀))‖)
        (𝓝[Icc t₀ (t₀ + 1)] s) (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact (ENNReal.continuous_ofReal.tendsto 0).comp
        (tendsto_iff_norm_sub_tendsto_zero.mp (((dqCLM p.c).continuous.tendsto _).comp htU))
    have htη : Tendsto (fun s' => ENNReal.ofReal ‖detaCLM p.c (U (s' - t₀)) - detaCLM p.c (U (s - t₀))‖)
        (𝓝[Icc t₀ (t₀ + 1)] s) (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact (ENNReal.continuous_ofReal.tendsto 0).comp
        (tendsto_iff_norm_sub_tendsto_zero.mp (((detaCLM p.c).continuous.tendsto _).comp htU))
    simpa using (ht0.add htq).add htη

  -- Step 5: Weak meridional PDE identity on `(t₀, t₀ + 1)`
  have hb_cont : ContinuousOn (fun r => trainBvCLM hbg ht₀ r (U r)) (Icc 0 1) :=
    D.continuousOn_B_apply hU_cont
  have hduh_int_tau : ∀ τ ∈ Icc (0 : ℝ) 1,
      IntegrableOn (fun r => duhH1CLM hc (p.ν * (τ - r)) (trainBvCLM hbg ht₀ r (U r)))
        (Ioc 0 τ) volume := by
    intro τ hτ
    have h1 := (intervalIntegrable_iff_integrableOn_Ioc_of_le hτ.1).1
      (D.intervalIntegrable_integrand hτ.1 (by linarith [hτ.2])
        (hU_cont.mono (Icc_subset_Icc_right hτ.2)))
    have hsm : (fun r => duhH1CLM hc (p.ν * (τ - r)) (trainBvCLM hbg ht₀ r (U r))) =
        fun r => -(D.S (τ - r) (D.B r (U r))) := by
      funext r
      change _ = -((-duhH1CLM hc (p.ν * (τ - r))) (trainBvCLM hbg ht₀ r (U r)))
      simp
    rw [hsm]
    exact h1.neg
  have hU_duhamel : ∀ τ ∈ Icc (0 : ℝ) 1,
      U τ = freeH1CLM hc (p.ν * τ) u_sol +
        (∫ σ in (0 : ℝ)..τ, freeH1CLM hc (p.ν * (τ - σ)) (G σ)) -
        (∫ r in (0 : ℝ)..τ, duhH1CLM hc (p.ν * (τ - r)) (trainBvCLM hbg ht₀ r (U r))) := by
    intro τ hτ
    have hUτ := hU_vol τ hτ
    have hvol_eq : D.vol 0 U τ =
        -∫ r in (0 : ℝ)..τ, duhH1CLM hc (p.ν * (τ - r)) (trainBvCLM hbg ht₀ r (U r)) := by
      unfold VolterraData.vol
      have heq_f : (fun r => D.S (τ - r) (D.B r (U r))) =
          fun r => -duhH1CLM hc (p.ν * (τ - r)) (trainBvCLM hbg ht₀ r (U r)) := rfl
      rw [heq_f, intervalIntegral.integral_neg]
    dsimp [f₀, S_G] at hUτ
    rw [hvol_eq] at hUτ
    rw [hUτ, sub_eq_add_neg]
  have hG_ae : ∀ τ : ℝ, (val0CLM p.c (G τ) : Plane → Vec2) =ᵐ[cellμ p.c]
      toVecSlice (fun y => g₀ (t₀ + τ, y)) :=
    fun τ => (h1SolOfCylSlice_ae (hg_h1 (t₀ + τ))).1
  refine ⟨z, zq, zη, hz_sm, hzq_sm, hzη_sm, hz_per, hz_slice, hz_init, hz_cont, ?_⟩
  exact unitStep_weak_pde hbg ht₀ hg_sm (fun x => (hg_per x).1) hg_int u_sol
    hG0_sm hGq_sm hGη_sm hG_sm hG_int hG_ae
    hU_cont hb_cont hduh_int_tau hU_duhamel
    hz_sm hzq_sm hzη_sm hz_per hz_ae

end UnforcedLeray.Short.IIb.TailExistenceAux
