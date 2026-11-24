import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollCommDefs

/-!
# `CommTestLimit`: the Friedrichs commutator vanishes on phase tests

Source `the November 2 reference manuscript` lines 1351-1362 and 1556-1583.

Route.  The kernel `kap ρ = div_y(z_y ρ)` is the sum of the `y_j`-derivatives of the
coordinate factors `φ_j(z) = z_j ρ(z)`, so integration by parts in each `y_j` moves the
derivative onto the test:
`commK ρ Ψ x = ½ ∑_j ∫ φ_j(z) DΨ(x - z)(0, e_j) dz`.
Hence `‖commK ρ Ψ x‖ ≤ (3/2) C rOut` whenever `‖DΨ‖ ≤ C` on the relevant window, and
`commK ρ Ψ x = 0` far out in `y` (as `Ψ` vanishes there).  The phase-normalised `L²` norm over
one period is then at most `rOut · (3/2) C √vol(B)`, which tends to `0` as `rOut → 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

instance commProdHaar : (volume : Measure (ℝ × Space)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure Space)

/-- The coordinate factor `z_j ρ(z)` of the commutator kernel. -/
def commPhi (ρ : ContDiffBump (0 : ℝ × Space)) (j : Fin 3) (z : ℝ × Space) : ℝ :=
  z.2 j * ρ.normed volume z

lemma commPhi_contDiff (ρ : ContDiffBump (0 : ℝ × Space)) (j : Fin 3) :
    ContDiff ℝ ∞ (commPhi ρ j) := by
  have h1 : ContDiff ℝ ∞ (fun z : ℝ × Space => z.2 j) :=
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff.comp contDiff_snd
  exact h1.mul (ρ.contDiff_normed (n := ⊤))

lemma commPhi_fderiv (ρ : ContDiffBump (0 : ℝ × Space)) (j : Fin 3) (z v : ℝ × Space) :
    fderiv ℝ (commPhi ρ j) z v =
      v.2 j * ρ.normed volume z + z.2 j * fderiv ℝ (ρ.normed volume) z v := by
  have hℓ : HasFDerivAt (fun w : ℝ × Space => w.2 j)
      ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).comp (ContinuousLinearMap.snd ℝ ℝ Space)) z :=
    ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).comp (ContinuousLinearMap.snd ℝ ℝ Space)).hasFDerivAt
  have hρ : HasFDerivAt (ρ.normed volume) (fderiv ℝ (ρ.normed volume) z) z :=
    ((ρ.contDiff_normed (n := ⊤)).differentiable (by simp) z).hasFDerivAt
  have hm : HasFDerivAt (fun w : ℝ × Space => w.2 j * ρ.normed volume w)
      (z.2 j • fderiv ℝ (ρ.normed volume) z +
        ρ.normed volume z • ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).comp
          (ContinuousLinearMap.snd ℝ ℝ Space))) z := hℓ.mul hρ
  have hfun : commPhi ρ j = fun w => w.2 j * ρ.normed volume w := rfl
  rw [hfun, hm.fderiv]
  simp [ContinuousLinearMap.comp_apply] <;> ring

/-- Off the closed ball of radius `rOut` the normalised bump and its derivative vanish. -/
lemma normed_far (ρ : ContDiffBump (0 : ℝ × Space)) (z : ℝ × Space) (h : ρ.rOut < ‖z‖) :
    ρ.normed volume z = 0 ∧ fderiv ℝ (ρ.normed volume) z = 0 := by
  constructor
  · by_contra hne
    have hmem : z ∈ Function.support (ρ.normed volume) := hne
    rw [ContDiffBump.support_normed_eq, mem_ball_zero_iff] at hmem
    linarith
  · apply fderiv_of_notMem_tsupport
    rw [ContDiffBump.tsupport_normed_eq, mem_closedBall_zero_iff]
    exact not_le.mpr h

lemma commPhi_far (ρ : ContDiffBump (0 : ℝ × Space)) (j : Fin 3) (z : ℝ × Space)
    (h : ρ.rOut < ‖z‖) : commPhi ρ j z = 0 := by
  simp [commPhi, (normed_far ρ z h).1]

lemma kap_far (ρ : ContDiffBump (0 : ℝ × Space)) (z : ℝ × Space) (h : ρ.rOut < ‖z‖) :
    kap ρ z = 0 := by
  simp [kap, kerDv, (normed_far ρ z h).1, (normed_far ρ z h).2]

lemma kap_eq_sum (ρ : ContDiffBump (0 : ℝ × Space)) (z : ℝ × Space) :
    kap ρ z = ∑ j : Fin 3, fderiv ℝ (commPhi ρ j) z (0, coordinateVector j) := by
  have hsum : ∑ j : Fin 3, z.2 j • coordinateVector j = z.2 := by
    ext i
    simp [coordinateVector, Pi.single_apply, mul_ite, Finset.sum_ite_eq']
  have h0 : ((0 : ℝ), z.2) = ∑ j : Fin 3, z.2 j • ((0 : ℝ), coordinateVector j) := by
    rw [Prod.ext_iff]
    constructor
    · simp [Prod.fst_sum]
    · simp only [Prod.snd_sum, Prod.smul_snd, hsum]
  have hD : fderiv ℝ (ρ.normed volume) z (0, z.2) =
      ∑ j : Fin 3, z.2 j * fderiv ℝ (ρ.normed volume) z (0, coordinateVector j) := by
    rw [h0, map_sum]
    simp only [map_smul, smul_eq_mul]
  simp only [commPhi_fderiv, kap, kerDv, hD]
  simp [coordinateVector, EuclideanSpace.single_apply, Finset.sum_add_distrib] <;> ring

/-- A continuous field vanishing off the ball of radius `rOut` is integrable. -/
lemma integrable_of_far {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ρ : ContDiffBump (0 : ℝ × Space)) (G : ℝ × Space → F) (hG : Continuous G)
    (h : ∀ z : ℝ × Space, ρ.rOut < ‖z‖ → G z = 0) : Integrable G volume := by
  refine hG.integrable_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_closedBall (0 : ℝ × Space) ρ.rOut) ?_)
  intro z hz
  apply h
  simpa using hz

lemma fderiv_comp_sub (Ψ : ℝ × Space → CVec3) (hΨ : Differentiable ℝ Ψ) (x z v : ℝ × Space) :
    fderiv ℝ (fun w => Ψ (x - w)) z v = -(fderiv ℝ Ψ (x - z) v) := by
  have h : HasFDerivAt (fun w => Ψ (x - w))
      ((fderiv ℝ Ψ (x - z)).comp (-ContinuousLinearMap.id ℝ (ℝ × Space))) z :=
    (hΨ (x - z)).hasFDerivAt.comp z ((hasFDerivAt_id z).const_sub x)
  rw [h.fderiv]
  simp

lemma integrable_piece1 (ρ : ContDiffBump (0 : ℝ × Space)) (Ψ : ℝ × Space → CVec3)
    (hΨ : ContDiff ℝ ∞ Ψ) (x : ℝ × Space) (j : Fin 3) :
    Integrable (fun z => fderiv ℝ (commPhi ρ j) z (0, coordinateVector j) • Ψ (x - z)) volume := by
  refine integrable_of_far ρ _ ?_ ?_
  · exact (((commPhi_contDiff ρ j).continuous_fderiv (by simp)).clm_apply continuous_const).smul
      (hΨ.continuous.comp (continuous_const.sub continuous_id))
  · intro z hz
    simp [commPhi_fderiv, (normed_far ρ z hz).1, (normed_far ρ z hz).2]

/-- Integration by parts in the `y_j` direction. -/
lemma ibp_piece (ρ : ContDiffBump (0 : ℝ × Space)) (Ψ : ℝ × Space → CVec3)
    (hΨ : ContDiff ℝ ∞ Ψ) (x : ℝ × Space) (j : Fin 3) :
    ∫ z, fderiv ℝ (commPhi ρ j) z (0, coordinateVector j) • Ψ (x - z) =
      ∫ z, commPhi ρ j z • fderiv ℝ Ψ (x - z) (0, coordinateVector j) := by
  have hΨd : Differentiable ℝ Ψ := hΨ.differentiable (by simp)
  have hD : Continuous (fun w => fderiv ℝ Ψ w) := hΨ.continuous_fderiv (by simp)
  have hsub : ∀ z, fderiv ℝ (fun w => Ψ (x - w)) z (0, coordinateVector j) =
      -(fderiv ℝ Ψ (x - z) (0, coordinateVector j)) :=
    fun z => fderiv_comp_sub Ψ hΨd x z _
  have I2 : Integrable (fun z => commPhi ρ j z •
      fderiv ℝ (fun w => Ψ (x - w)) z (0, coordinateVector j)) volume := by
    refine integrable_of_far ρ _ ?_ ?_
    · simp only [hsub]
      exact (commPhi_contDiff ρ j).continuous.smul
        (((hD.comp (continuous_const.sub continuous_id))).clm_apply continuous_const).neg
    · intro z hz
      simp [commPhi_far ρ j z hz]
  have I3 : Integrable (fun z => commPhi ρ j z • Ψ (x - z)) volume := by
    refine integrable_of_far ρ _ ?_ ?_
    · exact (commPhi_contDiff ρ j).continuous.smul
        (hΨ.continuous.comp (continuous_const.sub continuous_id))
    · intro z hz
      simp [commPhi_far ρ j z hz]
  have key := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    (f := commPhi ρ j) (g := fun z => Ψ (x - z)) (v := (0, coordinateVector j))
    (integrable_piece1 ρ Ψ hΨ x j) I2 I3
    (fun z _ => ((commPhi_contDiff ρ j).differentiable (by simp)) z)
    (fun z _ => (hΨd (x - z)).comp z (by fun_prop))
  simp only [hsub, smul_neg, integral_neg] at key
  exact (neg_inj.mp key).symm

lemma commK_eq_pieces (ρ : ContDiffBump (0 : ℝ × Space)) (Ψ : ℝ × Space → CVec3)
    (hΨ : ContDiff ℝ ∞ Ψ) (x : ℝ × Space) :
    commK ρ Ψ x = ∑ j : Fin 3, (1 / 2 : ℝ) •
      ∫ z, commPhi ρ j z • fderiv ℝ Ψ (x - z) (0, coordinateVector j) := by
  have hpt : ∀ z : ℝ × Space, (1 / 2 * kap ρ z) • Ψ (x - z) =
      ∑ j : Fin 3, (1 / 2 : ℝ) •
        (fderiv ℝ (commPhi ρ j) z (0, coordinateVector j) • Ψ (x - z)) := by
    intro z
    rw [kap_eq_sum, Finset.mul_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul]
  unfold commK
  simp_rw [hpt]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_smul, ibp_piece ρ Ψ hΨ x j]
  · intro j _
    exact (integrable_piece1 ρ Ψ hΨ x j).smul (1 / 2 : ℝ)

lemma commK_norm_le (ρ : ContDiffBump (0 : ℝ × Space)) (Ψ : ℝ × Space → CVec3)
    (hΨ : ContDiff ℝ ∞ Ψ) (x : ℝ × Space) (C : ℝ) (hC : 0 ≤ C)
    (hxK : ∀ z : ℝ × Space, ‖z‖ ≤ ρ.rOut → ‖fderiv ℝ Ψ (x - z)‖ ≤ C) :
    ‖commK ρ Ψ x‖ ≤ (3 / 2) * C * ρ.rOut := by
  rw [commK_eq_pieces ρ Ψ hΨ x]
  have hnormv : ∀ j : Fin 3, ‖((0 : ℝ), coordinateVector j)‖ ≤ 1 := fun j => by
    rw [Prod.norm_def]
    simp [coordinateVector, EuclideanSpace.norm_single]
  have hpiece : ∀ j : Fin 3,
      ‖∫ z, commPhi ρ j z • fderiv ℝ Ψ (x - z) (0, coordinateVector j)‖ ≤ ρ.rOut * C := by
    intro j
    have hint : Integrable (fun z : ℝ × Space => ρ.rOut * C * ρ.normed volume z) volume :=
      ((ρ.continuous_normed (μ := volume)).integrable_of_hasCompactSupport
        (ρ.hasCompactSupport_normed (μ := volume))).const_mul _
    have hle : ∀ z : ℝ × Space,
        ‖commPhi ρ j z • fderiv ℝ Ψ (x - z) (0, coordinateVector j)‖ ≤
          ρ.rOut * C * ρ.normed volume z := by
      intro z
      rw [norm_smul]
      by_cases hz : ‖z‖ ≤ ρ.rOut
      · have hρn := ρ.nonneg_normed (μ := volume) z
        have h1 : ‖commPhi ρ j z‖ ≤ ρ.rOut * ρ.normed volume z := by
          unfold commPhi
          rw [norm_mul, Real.norm_of_nonneg hρn]
          apply mul_le_mul_of_nonneg_right _ hρn
          have h2 : ‖z.2 j‖ ≤ ‖z.2‖ := by
            simpa [Real.norm_eq_abs] using PiLp.norm_apply_le z.2 j
          have h3 : ‖z.2‖ ≤ ‖z‖ := norm_snd_le z
          rw [Real.norm_eq_abs] at h2 ⊢
          linarith
        have h2 : ‖fderiv ℝ Ψ (x - z) (0, coordinateVector j)‖ ≤ C := by
          calc ‖fderiv ℝ Ψ (x - z) (0, coordinateVector j)‖
              ≤ ‖fderiv ℝ Ψ (x - z)‖ * ‖((0 : ℝ), coordinateVector j)‖ :=
                ContinuousLinearMap.le_opNorm _ _
            _ ≤ C * 1 := mul_le_mul (hxK z hz) (hnormv j) (norm_nonneg _) hC
            _ = C := mul_one C
        calc ‖commPhi ρ j z‖ * ‖fderiv ℝ Ψ (x - z) (0, coordinateVector j)‖
            ≤ (ρ.rOut * ρ.normed volume z) * C :=
              mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg ρ.rOut_pos.le hρn)
          _ = ρ.rOut * C * ρ.normed volume z := by ring
      · have h0 : ρ.normed volume z = 0 := (normed_far ρ z (not_le.mp hz)).1
        simp [commPhi, h0]
    calc ‖∫ z, commPhi ρ j z • fderiv ℝ Ψ (x - z) (0, coordinateVector j)‖
        ≤ ∫ z, ρ.rOut * C * ρ.normed volume z :=
          norm_integral_le_of_norm_le hint (ae_of_all _ hle)
      _ = ρ.rOut * C := by rw [integral_const_mul, ContDiffBump.integral_normed (μ := volume), mul_one]
  calc ‖∑ j : Fin 3, (1 / 2 : ℝ) •
        ∫ z, commPhi ρ j z • fderiv ℝ Ψ (x - z) (0, coordinateVector j)‖
      ≤ ∑ j : Fin 3, ‖(1 / 2 : ℝ) •
          ∫ z, commPhi ρ j z • fderiv ℝ Ψ (x - z) (0, coordinateVector j)‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin 3, (1 / 2 : ℝ) * (ρ.rOut * C) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        exact mul_le_mul_of_nonneg_left (hpiece j) (by norm_num)
    _ = (3 / 2) * C * ρ.rOut := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

theorem commTestLimit : CommTestLimit := by
  intro P hP Ψ hΨ ε hε
  obtain ⟨R, hR⟩ := hΨ.bounded_support
  have hΨs : ContDiff ℝ ∞ Ψ := hΨ.smooth
  have hΨd : Differentiable ℝ Ψ := hΨs.differentiable (by simp)
  have hΨc : Continuous Ψ := hΨs.continuous
  have hKc : IsCompact (Icc (-1 : ℝ) (P + 1) ×ˢ Metric.closedBall (0 : Space) (|R| + 2)) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hcont : ContinuousOn (fun w => ‖fderiv ℝ Ψ w‖)
      (Icc (-1 : ℝ) (P + 1) ×ˢ Metric.closedBall (0 : Space) (|R| + 2)) :=
    ((hΨs.continuous_fderiv (by simp)).norm).continuousOn
  obtain ⟨C0, hC0⟩ := hKc.exists_bound_of_continuousOn hcont
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = max C0 0 := ⟨_, rfl⟩
  have hC : 0 ≤ C := hCdef ▸ le_max_right _ _
  have hCK : ∀ w ∈ Icc (-1 : ℝ) (P + 1) ×ˢ Metric.closedBall (0 : Space) (|R| + 2),
      ‖fderiv ℝ Ψ w‖ ≤ C := fun w hw => by
    have h := hC0 w hw
    simp only [norm_norm] at h
    rw [hCdef]
    exact h.trans (le_max_left _ _)
  obtain ⟨V, hVdef⟩ : ∃ V : ℝ, V = (volume (Metric.closedBall (0 : Space) (|R| + 1))).toReal :=
    ⟨_, rfl⟩
  have hV0 : 0 ≤ V := hVdef ▸ ENNReal.toReal_nonneg
  have hK1nn : 0 ≤ (3 / 2) * C * Real.sqrt V :=
    mul_nonneg (mul_nonneg (by norm_num) hC) (Real.sqrt_nonneg _)
  refine ⟨min 1 (ε / ((3 / 2) * C * Real.sqrt V + 1)),
    lt_min one_pos (div_pos hε (by linarith)), fun ρ hρ => ?_⟩
  have hr1 : ρ.rOut ≤ 1 := (hρ.trans_le (min_le_left _ _)).le
  have hrK : ρ.rOut * ((3 / 2) * C * Real.sqrt V + 1) < ε :=
    (lt_div_iff₀ (by linarith)).mp (hρ.trans_le (min_le_right _ _))
  have hr0 : 0 ≤ ρ.rOut := ρ.rOut_pos.le
  -- far field: the commutator vanishes for `|y| > |R| + 1`
  have hfar : ∀ x : ℝ × Space, |R| + 1 < ‖x.2‖ → commK ρ Ψ x = 0 := by
    intro x hx
    have hz : ∀ z : ℝ × Space, (1 / 2 * kap ρ z) • Ψ (x - z) = 0 := by
      intro z
      by_cases hzr : ‖z‖ ≤ ρ.rOut
      · have hzs : ‖z.2‖ ≤ 1 := (norm_snd_le z).trans (hzr.trans hr1)
        have hsec : R < ‖(x - z).2‖ := by
          rw [Prod.snd_sub]
          have h1 := norm_sub_norm_le x.2 z.2
          have h2 := le_abs_self R
          linarith
        have h0 : Ψ (x - z) = 0 := hR _ _ hsec
        rw [h0, smul_zero]
      · rw [kap_far ρ z (not_le.mp hzr), mul_zero, zero_smul]
    unfold commK
    simp only [hz, integral_zero]
  -- near field: the uniform pointwise bound
  have hnear : ∀ x : ℝ × Space, x.1 ∈ Icc (0 : ℝ) P → ‖x.2‖ ≤ |R| + 1 →
      ‖commK ρ Ψ x‖ ≤ (3 / 2) * C * ρ.rOut := by
    intro x hx1 hx2
    obtain ⟨hx1a, hx1b⟩ := hx1
    apply commK_norm_le ρ Ψ hΨs x C hC
    intro z hz
    apply hCK
    have hz1 : |z.1| ≤ 1 := by
      have h := (norm_fst_le z).trans (hz.trans hr1)
      rwa [Real.norm_eq_abs] at h
    have hzs : ‖z.2‖ ≤ 1 := (norm_snd_le z).trans (hz.trans hr1)
    simp only [Set.mem_prod, Set.mem_Icc, mem_closedBall_zero_iff, Prod.fst_sub, Prod.snd_sub]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · linarith [(abs_le.mp hz1).2]
    · linarith [(abs_le.mp hz1).1]
    · have := norm_sub_le x.2 z.2
      linarith
  have hM0 : 0 ≤ (3 / 2) * C * ρ.rOut := mul_nonneg (mul_nonneg (by norm_num) hC) hr0
  have hWfin : volume (Metric.closedBall (0 : Space) (|R| + 1)) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hWeq : volume (Metric.closedBall (0 : Space) (|R| + 1)) = ENNReal.ofReal V := by
    rw [hVdef, ENNReal.ofReal_toReal hWfin]
  have hpt : ∀ t ∈ Ioc (0 : ℝ) P, ∀ y : Space,
      ‖commK ρ Ψ (t, y)‖ₑ ^ (2 : ℝ) ≤
        (Metric.closedBall (0 : Space) (|R| + 1)).indicator
          (fun _ => ENNReal.ofReal ((3 / 2) * C * ρ.rOut) ^ 2) y := by
    intro t ht y
    by_cases hy : y ∈ Metric.closedBall (0 : Space) (|R| + 1)
    · rw [indicator_of_mem hy]
      have hyn : ‖y‖ ≤ |R| + 1 := mem_closedBall_zero_iff.mp hy
      have hle : ‖commK ρ Ψ (t, y)‖ ≤ (3 / 2) * C * ρ.rOut :=
        hnear (t, y) ⟨ht.1.le, ht.2⟩ hyn
      rw [← ofReal_norm_eq_enorm, ENNReal.rpow_two]
      exact pow_le_pow_left₀ (by positivity) (ENNReal.ofReal_le_ofReal hle) 2
    · rw [indicator_of_notMem hy]
      have hyn : |R| + 1 < ‖y‖ := by
        rw [mem_closedBall_zero_iff, not_le] at hy
        exact hy
      rw [hfar (t, y) hyn]
      simp
  have hLint : ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ‖commK ρ Ψ (t, y)‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal P * (ENNReal.ofReal ((3 / 2) * C * ρ.rOut) ^ 2 *
        volume (Metric.closedBall (0 : Space) (|R| + 1))) := by
    calc ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ‖commK ρ Ψ (t, y)‖ₑ ^ (2 : ℝ)
        ≤ ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space,
            (Metric.closedBall (0 : Space) (|R| + 1)).indicator
              (fun _ => ENNReal.ofReal ((3 / 2) * C * ρ.rOut) ^ 2) y := by
          apply setLIntegral_mono' measurableSet_Ioc
          intro t ht
          exact lintegral_mono (hpt t ht)
      _ = ∫⁻ t in Ioc (0 : ℝ) P, ENNReal.ofReal ((3 / 2) * C * ρ.rOut) ^ 2 *
            volume (Metric.closedBall (0 : Space) (|R| + 1)) := by
          apply lintegral_congr
          intro t
          rw [lintegral_indicator_const measurableSet_closedBall]
      _ = ENNReal.ofReal P * (ENNReal.ofReal ((3 / 2) * C * ρ.rOut) ^ 2 *
            volume (Metric.closedBall (0 : Space) (|R| + 1))) := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero, mul_comm]
  have hcomb : ENNReal.ofReal P⁻¹ * ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space,
      ‖commK ρ Ψ (t, y)‖ₑ ^ (2 : ℝ) ≤
        ENNReal.ofReal (((3 / 2) * C * ρ.rOut) ^ 2 * V) := by
    calc ENNReal.ofReal P⁻¹ * ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space,
          ‖commK ρ Ψ (t, y)‖ₑ ^ (2 : ℝ)
        ≤ ENNReal.ofReal P⁻¹ * (ENNReal.ofReal P * (ENNReal.ofReal ((3 / 2) * C * ρ.rOut) ^ 2 *
            volume (Metric.closedBall (0 : Space) (|R| + 1)))) := by gcongr
      _ = ENNReal.ofReal ((3 / 2) * C * ρ.rOut) ^ 2 *
            volume (Metric.closedBall (0 : Space) (|R| + 1)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hP.le), inv_mul_cancel₀ hP.ne',
            ENNReal.ofReal_one, one_mul]
      _ = ENNReal.ofReal (((3 / 2) * C * ρ.rOut) ^ 2 * V) := by
          rw [hWeq, ← ENNReal.ofReal_pow hM0, ← ENNReal.ofReal_mul (sq_nonneg _)]
  have hMsq : ENNReal.ofReal (((3 / 2) * C * ρ.rOut) ^ 2 * V) ^ ((1 : ℝ) / 2) =
      ENNReal.ofReal (((3 / 2) * C * ρ.rOut) * Real.sqrt V) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (sq_nonneg _) hV0) (by norm_num),
      ← Real.sqrt_eq_rpow, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hM0]
  have hlt : ENNReal.ofReal (((3 / 2) * C * ρ.rOut) * Real.sqrt V) < ENNReal.ofReal ε := by
    rw [ENNReal.ofReal_lt_ofReal_iff hε]
    have h1 : ρ.rOut * ((3 / 2) * C * Real.sqrt V) ≤ ρ.rOut * ((3 / 2) * C * Real.sqrt V + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hr0
    have h2 : ((3 / 2) * C * ρ.rOut) * Real.sqrt V = ρ.rOut * ((3 / 2) * C * Real.sqrt V) := by
      ring
    rw [h2]
    linarith
  unfold UnforcedLeray.Short.IIb.phaseLpNorm
  calc (ENNReal.ofReal P⁻¹ * ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space,
          ‖commK ρ Ψ (t, y)‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
      ≤ (ENNReal.ofReal (((3 / 2) * C * ρ.rOut) ^ 2 * V)) ^ ((1 : ℝ) / 2) :=
        ENNReal.rpow_le_rpow hcomb (by norm_num)
    _ = ENNReal.ofReal (((3 / 2) * C * ρ.rOut) * Real.sqrt V) := hMsq
    _ < ENNReal.ofReal ε := hlt

end UnforcedLeray.Short.PartIIIb.Concrete
