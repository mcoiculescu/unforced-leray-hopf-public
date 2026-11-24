import UnforcedLeray.Units.B0448.Representation

/-!
# B0448, part 5: from `C_c^∞` tests to Schwartz tests

The manuscript (tex 7663–7677) states `F = (∂_t − Δ_z + 1)H` "distributionally", i.e. against
compactly supported smooth tests. For `H, F ∈ L^p` this implies the identity in `𝓢'`, which is
the hypothesis of `ae_eq_kernelConv`. Here:

* `resolventOpT_eqOn`: `Lᵗ` is local (two Schwartz functions equal on an open set have equal
  `Lᵗ` there);
* `cutN n X = χ(X/(n+1))`, a bump equal to `1` on the ball of radius `n + 1`, with
  `‖D^i cutN n‖ ≤ B` uniformly in `n` (`i ≤ 2`);
* `norm_resolventOpT_cutoffS_le`: `|Lᵗ(cutN n · φ)| ≤ 20 B S_φ`, with `S_φ ∈ L^{p'}`;
* `resolventOp_eq_of_compactSupport`: if `∫ (Lᵗφ) H = ∫ φ F` for every compactly supported
  Schwartz `φ` (= every `C_c^∞` test), then `(∂_t − Δ_z + 1)H = F` in `𝓢'` (dominated
  convergence on `φ_n = cutN n · φ`);
* `ae_eq_kernelConv_of_compactSupport`: the identity `H = K * F` under that hypothesis.
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.B0448

open MeasureTheory SchwartzMap LineDeriv Filter Topology
open scoped SchwartzMap ENNReal

/-! ### Locality of `Lᵗ` -/

theorem lineDerivOp_eqOn {ψ₁ ψ₂ : 𝓢(ST, ℂ)} {U : Set ST} (hU : IsOpen U)
    (h : ∀ x ∈ U, ψ₁ x = ψ₂ x) (v : ST) : ∀ x ∈ U, (∂_{v} ψ₁) x = (∂_{v} ψ₂) x := by
  intro x hx
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have : (ψ₁ : ST → ℂ) =ᶠ[𝓝 x] ψ₂ := Filter.eventually_of_mem (hU.mem_nhds hx) h
  rw [this.fderiv_eq]

theorem resolventOpT_eqOn {ψ₁ ψ₂ : 𝓢(ST, ℂ)} {U : Set ST} (hU : IsOpen U)
    (h : ∀ x ∈ U, ψ₁ x = ψ₂ x) : ∀ x ∈ U, resolventOpT ψ₁ x = resolventOpT ψ₂ x := by
  intro x hx
  simp only [resolventOpT, sub_apply, add_apply, neg_apply, sum_apply]
  rw [lineDerivOp_eqOn hU h _ x hx, h x hx,
    Finset.sum_congr rfl fun i _ => lineDerivOp_eqOn hU (lineDerivOp_eqOn hU h _) _ x hx]

/-! ### Pointwise bounds through iterated derivatives -/

theorem norm_timeDir : ‖timeDir‖ = 1 := by
  have h := real_inner_self_eq_norm_sq timeDir
  rw [inner_timeDir] at h
  have h1 : (WithLp.ofLp timeDir).1 = 1 := rfl
  rw [h1] at h
  have := norm_nonneg timeDir
  nlinarith

theorem norm_spaceDir (i : Fin 3) : ‖spaceDir i‖ = 1 := by
  have h := real_inner_self_eq_norm_sq (spaceDir i)
  rw [inner_spaceDir] at h
  have h1 : (WithLp.ofLp (spaceDir i)).2 i = 1 := by simp [spaceDir]
  rw [h1] at h
  have := norm_nonneg (spaceDir i)
  nlinarith

theorem norm_lineDerivOp_apply_le (ψ : 𝓢(ST, ℂ)) {v : ST} (hv : ‖v‖ = 1) (x : ST) :
    ‖(∂_{v} ψ) x‖ ≤ ‖iteratedFDeriv ℝ 1 ψ x‖ := by
  have h : (∂_{v} ψ) x = iteratedFDeriv ℝ 1 ψ x (fun _ => v) := by
    rw [← SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv,
      iteratedLineDerivOp_const_eq_iter_lineDerivOp]
    rfl
  rw [h]
  calc _ ≤ ‖iteratedFDeriv ℝ 1 ψ x‖ * ∏ _i : Fin 1, ‖v‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ = _ := by simp [hv]

theorem norm_lineDerivOp_lineDerivOp_apply_le (ψ : 𝓢(ST, ℂ)) {v : ST} (hv : ‖v‖ = 1)
    (x : ST) : ‖(∂_{v} (∂_{v} ψ)) x‖ ≤ ‖iteratedFDeriv ℝ 2 ψ x‖ := by
  have h : (∂_{v} (∂_{v} ψ)) x = iteratedFDeriv ℝ 2 ψ x (fun _ => v) := by
    rw [← SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv,
      iteratedLineDerivOp_const_eq_iter_lineDerivOp]
    rfl
  rw [h]
  calc _ ≤ ‖iteratedFDeriv ℝ 2 ψ x‖ * ∏ _i : Fin 2, ‖v‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ = _ := by simp [hv]

/-- `|Lᵗψ| ≤ |ψ| + ‖Dψ‖ + 3 ‖D²ψ‖` pointwise. -/
theorem norm_resolventOpT_apply_le (ψ : 𝓢(ST, ℂ)) (x : ST) :
    ‖resolventOpT ψ x‖ ≤ ‖iteratedFDeriv ℝ 0 ψ x‖ + ‖iteratedFDeriv ℝ 1 ψ x‖ +
      3 * ‖iteratedFDeriv ℝ 2 ψ x‖ := by
  simp only [resolventOpT, sub_apply, add_apply, neg_apply, sum_apply]
  rw [norm_iteratedFDeriv_zero]
  have h1 := norm_lineDerivOp_apply_le ψ norm_timeDir x
  have h2 : ‖∑ i : Fin 3, (∂_{spaceDir i} (∂_{spaceDir i} ψ)) x‖ ≤
      3 * ‖iteratedFDeriv ℝ 2 ψ x‖ := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i : Fin 3, ‖(∂_{spaceDir i} (∂_{spaceDir i} ψ)) x‖
        ≤ ∑ _i : Fin 3, ‖iteratedFDeriv ℝ 2 ψ x‖ :=
          Finset.sum_le_sum fun i _ => norm_lineDerivOp_lineDerivOp_apply_le ψ (norm_spaceDir i) x
      _ = _ := by simp
  calc ‖-(∂_{timeDir} ψ) x - ∑ i : Fin 3, (∂_{spaceDir i} (∂_{spaceDir i} ψ)) x + ψ x‖
      ≤ ‖(∂_{timeDir} ψ) x‖ + ‖∑ i : Fin 3, (∂_{spaceDir i} (∂_{spaceDir i} ψ)) x‖ + ‖ψ x‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_sub_le _ _).trans ?_
        rw [norm_neg]
    _ ≤ _ := by linarith

/-! ### The cutoffs `cutN n X = χ(X/(n+1))` -/

/-- A fixed bump on `ST`, equal to `1` on the unit ball, supported in the ball of radius `2`. -/
def bump : ContDiffBump (0 : ST) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The complexified bump. -/
def cutC (X : ST) : ℂ := ((bump : ST → ℝ) X : ℂ)

theorem contDiff_cutC {n : ℕ∞} : ContDiff ℝ n cutC :=
  Complex.ofRealCLM.contDiff.comp bump.contDiff

theorem hasCompactSupport_cutC : HasCompactSupport cutC :=
  bump.hasCompactSupport.comp_left Complex.ofReal_zero

/-- The dilation `X ↦ X/(n+1)`. -/
def scaleCLM (n : ℕ) : ST →L[ℝ] ST := ((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ ST

theorem scaleCLM_apply (n : ℕ) (X : ST) : scaleCLM n X = ((n : ℝ) + 1)⁻¹ • X := rfl

theorem norm_scaleCLM_le (n : ℕ) : ‖scaleCLM n‖ ≤ 1 := by
  refine (norm_smul_le ((n : ℝ) + 1)⁻¹ (ContinuousLinearMap.id ℝ ST)).trans ?_
  have h1 : ‖((n : ℝ) + 1)⁻¹‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  calc ‖((n : ℝ) + 1)⁻¹‖ * ‖ContinuousLinearMap.id ℝ ST‖ ≤ 1 * 1 :=
        mul_le_mul h1 (ContinuousLinearMap.norm_id_le) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- `cutN n X = χ(X/(n+1))`. -/
def cutN (n : ℕ) (X : ST) : ℂ := cutC (scaleCLM n X)

theorem contDiff_cutN (n : ℕ) {m : ℕ∞} : ContDiff ℝ m (cutN n) :=
  contDiff_cutC.comp (scaleCLM n).contDiff

theorem hasCompactSupport_cutN (n : ℕ) : HasCompactSupport (cutN n) := by
  have := hasCompactSupport_cutC.comp_smul (c := ((n : ℝ) + 1)⁻¹) (by positivity)
  exact this

theorem hasTemperateGrowth_cutN (n : ℕ) : (cutN n).HasTemperateGrowth :=
  (hasCompactSupport_cutN n).hasTemperateGrowth (contDiff_cutN n)

theorem norm_cutN_le_one (n : ℕ) (X : ST) : ‖cutN n X‖ ≤ 1 := by
  simp only [cutN, cutC, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg bump.nonneg]
  exact bump.le_one

theorem cutN_eq_one {n : ℕ} {X : ST} (hX : ‖X‖ < (n : ℝ) + 1) : cutN n X = 1 := by
  simp only [cutN, cutC]
  rw [bump.one_of_mem_closedBall]
  · simp
  rw [Metric.mem_closedBall, dist_zero_right, scaleCLM_apply, norm_smul,
    Real.norm_of_nonneg (by positivity)]
  show ((n : ℝ) + 1)⁻¹ * ‖X‖ ≤ 1
  rw [inv_mul_le_iff₀ (by positivity), mul_one]
  exact hX.le

theorem exists_bound_cutC :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ i ≤ 2, ∀ x, ‖iteratedFDeriv ℝ i cutC x‖ ≤ B := by
  have hb : ∀ i : ℕ, ∃ b : ℝ, ∀ x, ‖iteratedFDeriv ℝ i cutC x‖ ≤ b := by
    intro i
    have hc : Continuous fun x => ‖iteratedFDeriv ℝ i cutC x‖ :=
      (ContDiff.continuous_iteratedFDeriv' (contDiff_cutC (n := i))).norm
    obtain ⟨x₀, hx₀⟩ :=
      hc.exists_forall_ge_of_hasCompactSupport ((hasCompactSupport_cutC.iteratedFDeriv i).norm)
    exact ⟨_, hx₀⟩
  obtain ⟨b0, h0⟩ := hb 0
  obtain ⟨b1, h1⟩ := hb 1
  obtain ⟨b2, h2⟩ := hb 2
  refine ⟨1 + |b0| + |b1| + |b2|, by linarith [abs_nonneg b0, abs_nonneg b1, abs_nonneg b2],
    fun i hi x => ?_⟩
  interval_cases i
  · linarith [h0 x, le_abs_self b0, abs_nonneg b1, abs_nonneg b2]
  · linarith [h1 x, le_abs_self b1, abs_nonneg b0, abs_nonneg b2]
  · linarith [h2 x, le_abs_self b2, abs_nonneg b0, abs_nonneg b1]

theorem norm_iteratedFDeriv_cutN_le {B : ℝ}
    (hB : ∀ i ≤ 2, ∀ x, ‖iteratedFDeriv ℝ i cutC x‖ ≤ B) (n : ℕ) {i : ℕ} (hi : i ≤ 2)
    (x : ST) : ‖iteratedFDeriv ℝ i (cutN n) x‖ ≤ B := by
  have hcomp : cutN n = cutC ∘ scaleCLM n := rfl
  rw [hcomp, (scaleCLM n).iteratedFDeriv_comp_right (contDiff_cutC (n := ⊤)) x
    (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB i hi x)
  calc ‖iteratedFDeriv ℝ i cutC (scaleCLM n x)‖ * ∏ _j : Fin i, ‖scaleCLM n‖ ≤ B * 1 :=
        mul_le_mul (hB i hi _)
          (Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => norm_scaleCLM_le n))
          (Finset.prod_nonneg fun _ _ => norm_nonneg _) hB0
    _ = B := mul_one B

/-! ### The envelope and the bound on `Lᵗ(cutN n · φ)` -/

/-- The envelope `S_φ = |φ| + ‖Dφ‖ + ‖D²φ‖`. -/
def envelope (φ : 𝓢(ST, ℂ)) (x : ST) : ℝ :=
  ∑ k ∈ Finset.range 3, ‖iteratedFDeriv ℝ k φ x‖

theorem norm_iteratedFDeriv_le_envelope (φ : 𝓢(ST, ℂ)) {k : ℕ} (hk : k ≤ 2) (x : ST) :
    ‖iteratedFDeriv ℝ k φ x‖ ≤ envelope φ x :=
  Finset.single_le_sum (f := fun k => ‖iteratedFDeriv ℝ k φ x‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_range.2 (by omega))

theorem memLp_envelope (φ : 𝓢(ST, ℂ)) (r : ℝ≥0∞) : MemLp (envelope φ) r volume := by
  set φ₁ := fderivCLM ℝ ST ℂ φ
  set φ₂ := fderivCLM ℝ ST (ST →L[ℝ] ℂ) φ₁
  have hφ₁ : (φ₁ : ST → ST →L[ℝ] ℂ) = fderiv ℝ φ := funext fun x => fderivCLM_apply ℝ φ x
  have e : envelope φ = fun x => ‖φ x‖ + ‖φ₁ x‖ + ‖φ₂ x‖ := by
    funext x
    simp only [envelope, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      norm_iteratedFDeriv_zero, norm_iteratedFDeriv_one]
    rw [fderivCLM_apply, show (2 : ℕ) = 1 + 1 from rfl, ← norm_iteratedFDeriv_fderiv,
      norm_iteratedFDeriv_one, fderivCLM_apply, hφ₁]
  rw [e]
  exact (((φ.memLp r).norm.add (φ₁.memLp r).norm).add (φ₂.memLp r).norm)

theorem cutoff_apply_eq (n : ℕ) (φ : 𝓢(ST, ℂ)) :
    (smulLeftCLM ℂ (cutN n) φ : ST → ℂ) = fun y => cutN n y * φ y := by
  funext y
  rw [smulLeftCLM_apply_apply (hasTemperateGrowth_cutN n), smul_eq_mul]

/-- `φ_n = cutN n · φ`, a compactly supported Schwartz function. -/
def cutoffS (n : ℕ) (φ : 𝓢(ST, ℂ)) : 𝓢(ST, ℂ) := smulLeftCLM ℂ (cutN n) φ

theorem coe_cutoffS (n : ℕ) (φ : 𝓢(ST, ℂ)) :
    (cutoffS n φ : ST → ℂ) = fun y => cutN n y * φ y := cutoff_apply_eq n φ

theorem hasCompactSupport_cutoffS (n : ℕ) (φ : 𝓢(ST, ℂ)) :
    HasCompactSupport (cutoffS n φ) := by
  rw [coe_cutoffS]
  exact (hasCompactSupport_cutN n).mul_right

theorem norm_iteratedFDeriv_cutoff_le {B : ℝ}
    (hB : ∀ i ≤ 2, ∀ x, ‖iteratedFDeriv ℝ i cutC x‖ ≤ B) (n : ℕ) (φ : 𝓢(ST, ℂ)) {m : ℕ}
    (hm : m ≤ 2) (x : ST) :
    ‖iteratedFDeriv ℝ m (fun y => cutN n y * φ y) x‖ ≤ 4 * B * envelope φ x := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by norm_num) x)
  have hS0 : 0 ≤ envelope φ x := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine (norm_iteratedFDeriv_mul_le (N := ((⊤ : ℕ∞) : WithTop ℕ∞)) (contDiff_cutN n) (φ.smooth ⊤) x
    (by exact_mod_cast le_top)).trans ?_
  calc ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (cutN n) x‖ *
        ‖iteratedFDeriv ℝ (m - i) φ x‖
      ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * B * envelope φ x := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        exact mul_le_mul (mul_le_mul_of_nonneg_left
          (norm_iteratedFDeriv_cutN_le hB n (by omega) x) (Nat.cast_nonneg _))
          (norm_iteratedFDeriv_le_envelope φ (by omega) x) (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) hB0)
    _ = (2 : ℝ) ^ m * B * envelope φ x := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        congr 2
        exact_mod_cast Nat.sum_range_choose m
    _ ≤ 4 * B * envelope φ x := by
        have : (2 : ℝ) ^ m ≤ 4 := by
          calc (2 : ℝ) ^ m ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num) hm
            _ = 4 := by norm_num
        gcongr

theorem norm_resolventOpT_cutoffS_le {B : ℝ}
    (hB : ∀ i ≤ 2, ∀ x, ‖iteratedFDeriv ℝ i cutC x‖ ≤ B) (n : ℕ) (φ : 𝓢(ST, ℂ)) (x : ST) :
    ‖resolventOpT (cutoffS n φ) x‖ ≤ 20 * B * envelope φ x := by
  have h := norm_resolventOpT_apply_le (cutoffS n φ) x
  rw [coe_cutoffS] at h
  have h0 := norm_iteratedFDeriv_cutoff_le hB n φ (m := 0) (by norm_num) x
  have h1 := norm_iteratedFDeriv_cutoff_le hB n φ (m := 1) (by norm_num) x
  have h2 := norm_iteratedFDeriv_cutoff_le hB n φ (m := 2) (by norm_num) x
  linarith

/-! ### From `C_c^∞` tests to `𝓢'` -/

/-- **`C_c^∞` tests suffice.** If `H, F ∈ L^p(ℝ × ℝ³)` (`1 ≤ p ≤ ∞`) satisfy
`∫ (Lᵗφ) H = ∫ φ F` for every compactly supported Schwartz `φ` (that is, every `C_c^∞` test),
then `(∂_t − Δ_z + 1)H = F` in `𝓢'`. -/
theorem resolventOp_eq_of_compactSupport {p : ℝ≥0∞} [hp : Fact (1 ≤ p)]
    {H F : Lp ℂ p (volume : Measure ST)}
    (hHF : ∀ φ : 𝓢(ST, ℂ), HasCompactSupport φ →
      ∫ X, resolventOpT φ X * H X = ∫ X, φ X * F X) :
    resolventOp (H : 𝓢'(ST, ℂ)) = (F : 𝓢'(ST, ℂ)) := by
  have hc : ENNReal.HolderConjugate p (conjExp p) :=
    ENNReal.HolderConjugate.inv_one_sub_inv' hp.out
  have : ENNReal.HolderTriple (conjExp p) p 1 := hc.symm
  obtain ⟨B, -, hB⟩ := exists_bound_cutC
  ext φ
  rw [resolventOp_apply]
  simp only [Lp.toTemperedDistribution_apply, smul_eq_mul]
  have hev : ∀ X : ST, ∀ᶠ n : ℕ in atTop, ‖X‖ < (n : ℝ) + 1 := by
    intro X
    obtain ⟨N, hN⟩ := exists_nat_ge ‖X‖
    filter_upwards [eventually_ge_atTop N] with n hn
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hlim1 : Tendsto (fun n : ℕ => ∫ X, resolventOpT (cutoffS n φ) X * H X) atTop
      (𝓝 (∫ X, resolventOpT φ X * H X)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun X => 20 * B * envelope φ X * ‖H X‖) (fun n => ?_) ?_ (fun n => ?_) ?_
    · exact (resolventOpT (cutoffS n φ)).continuous.aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable H)
    · have h := (memLp_envelope φ (conjExp p)).integrable_mul (Lp.memLp H).norm
      have h' := h.const_mul (20 * B)
      refine h'.congr (Filter.Eventually.of_forall fun X => ?_)
      simp only [Pi.mul_apply]
      ring
    · refine Filter.Eventually.of_forall fun X => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_resolventOpT_cutoffS_le hB n φ X) (norm_nonneg _)
    · refine Filter.Eventually.of_forall fun X => tendsto_const_nhds.congr' ?_
      filter_upwards [hev X] with n hn
      have hU : IsOpen (Metric.ball (0 : ST) ((n : ℝ) + 1)) := Metric.isOpen_ball
      have heq : ∀ y ∈ Metric.ball (0 : ST) ((n : ℝ) + 1), cutoffS n φ y = φ y := by
        intro y hy
        rw [Metric.mem_ball, dist_zero_right] at hy
        rw [coe_cutoffS]
        simp only [cutN_eq_one hy, one_mul]
      have hX : X ∈ Metric.ball (0 : ST) ((n : ℝ) + 1) := by
        rwa [Metric.mem_ball, dist_zero_right]
      rw [resolventOpT_eqOn hU heq X hX]
  have hlim2 : Tendsto (fun n : ℕ => ∫ X, cutoffS n φ X * F X) atTop
      (𝓝 (∫ X, φ X * F X)) := by
    refine tendsto_integral_of_dominated_convergence (fun X => ‖φ X‖ * ‖F X‖) (fun n => ?_) ?_
      (fun n => ?_) ?_
    · exact (cutoffS n φ).continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable F)
    · exact (φ.memLp (conjExp p)).norm.integrable_mul (Lp.memLp F).norm
    · refine Filter.Eventually.of_forall fun X => ?_
      rw [coe_cutoffS, norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right
        (by simpa using mul_le_mul_of_nonneg_right (norm_cutN_le_one n X) (norm_nonneg (φ X)))
        (norm_nonneg _)
    · refine Filter.Eventually.of_forall fun X => tendsto_const_nhds.congr' ?_
      filter_upwards [hev X] with n hn
      rw [coe_cutoffS]
      simp only [cutN_eq_one hn, one_mul]
  have heq : ∀ n : ℕ, ∫ X, resolventOpT (cutoffS n φ) X * H X = ∫ X, cutoffS n φ X * F X :=
    fun n => hHF _ (hasCompactSupport_cutoffS n φ)
  exact tendsto_nhds_unique (Tendsto.congr heq hlim1) hlim2

/-- **The identity `H = K * F`, distributional form (tex 7663–7679).** If `H, F ∈ L^p(ℝ × ℝ³)`
(`1 ≤ p ≤ ∞`) and `F = (∂_t − Δ_z + 1)H` against every `C_c^∞` test
(`∫ H (−∂_tφ − Δ_zφ + φ) = ∫ F φ`), then `H = K * F` almost everywhere. -/
theorem ae_eq_kernelConv_of_compactSupport {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {H F : Lp ℂ p (volume : Measure ST)}
    (hHF : ∀ φ : 𝓢(ST, ℂ), HasCompactSupport φ →
      ∫ X, resolventOpT φ X * H X = ∫ X, φ X * F X) :
    (H : ST → ℂ) =ᵐ[volume] kernelConv F :=
  ae_eq_kernelConv (resolventOp_eq_of_compactSupport hHF)

end UnforcedLeray.B0448
