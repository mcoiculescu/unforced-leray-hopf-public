import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.ComplCoupling.EulerSubBound.KernelNear

/-!
# The Gaussian-cylinder dual residual and the conditional assembly (helper for `PartIII-a:T21/c5/3/2`)

Source of record: `the November 2 reference manuscript` (SP), lines 2866-2897,
2905-2918, 2990-2997.

* `PlanarSeedEulerDual κ` (the remaining leaf): the planar seed duality `L₀^* λ_k = λ_k λ_k`
  for the linearised Euler operator around the Gaussian vortex `v₀`, `ω₀ = curl v₀`, written with
  the planar Biot-Savart adjoint `kerAdjPl`.
* `gaussSub_bound`: given the planar duality, the Gaussian-cylinder residual
  `movLam0EulerGaussSub κ lam d k` (periodized Gaussian vortex, cylinder kernel `K_d`, periodized
  dual row `P_d λ_k`) is `O(d⁻²)` in `X_{-m,d}` (SP 2876-2897: image expansion, paired translates,
  Gaussian columns).
* `movLam0DualEulerSubBound_of_dual`, `movLamDualEulerSubBound_of_dual`: with the proved train
  comparison (`EulerSubTrain.memLp_and_xNorm_movEulerAdj_trainDiff`) and the proved linearity
  (`DirectEulerSub.kerAdj_perLam_eq`, `DirectEulerSub.transCx_perLam_eq_of_diff`), the target
  `MovLamDualEulerSubBound κ` follows from `PlanarSeedEulerDual κ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace EulerSubCore

open EulerSubTrain

/-- **Leaf: planar seed duality** (SP 593-610, 2891-2918, `eq:short-seed-functional`): for the
Part I seed kernels there is the seed eigenvalue `lam` with
`v₀ · ∇λ_k - K_∞^T(λ_k ∇ω₀) = λ_k λ_k` on the plane (`λ₀ = lam`, `λ₁ = conj lam`), where
`v₀ = e^{-|y|²/4} y^⊥` is the Gaussian vortex and `ω₀ = curl v₀`. -/
def PlanarSeedEulerDual (κ : PlanarFrameKernels) : Prop :=
  IsSeedKernels κ → ∃ lam : ℂ, ∀ (k : Fin 2) (y : ℝ × ℝ),
    E0.transCx (fun z l => UnforcedLeray.Train.v0 z l) (κ.lamP k) y -
      kerAdjPl (fun l x => κ.lamP k x *
        ((B0579.pd l (UnforcedLeray.Cyl.curl UnforcedLeray.Train.v0) x : ℝ) : ℂ)) y =
    seedModeEigen lam k * κ.lamP k y

/-! ## 1. The vorticity gradients of the Gaussian and of the periodized Gaussian -/

theorem curl_eq_pd (v : ℝ × ℝ → EuclideanSpace ℝ (Fin 2)) (hv : ContDiff ℝ 1 v) :
    UnforcedLeray.Cyl.curl v =
      fun z => B0579.pd 0 (fun w => v w 1) z - B0579.pd 1 (fun w => v w 0) z := by
  funext z
  rw [UnforcedLeray.B0238.curl_eq_fderiv hv z]
  simp [B0579.pd, B0579.dir]

theorem pd_sub {A B : ℝ × ℝ → ℝ} {x : ℝ × ℝ} (j : Fin 2) (hA : DifferentiableAt ℝ A x)
    (hB : DifferentiableAt ℝ B x) :
    B0579.pd j (fun z => A z - B z) x = B0579.pd j A x - B0579.pd j B x := by
  unfold B0579.pd
  rw [fderiv_fun_sub hA hB]
  simp

theorem pd_curl_sub (u w : ℝ × ℝ → EuclideanSpace ℝ (Fin 2)) (hu : ContDiff ℝ ∞ u)
    (hw : ContDiff ℝ ∞ w) (l : Fin 2) (x : ℝ × ℝ) :
    B0579.pd l (UnforcedLeray.Cyl.curl u) x - B0579.pd l (UnforcedLeray.Cyl.curl w) x =
      B0579.pd l (UnforcedLeray.Cyl.curl (u - w)) x := by
  have hc2 : ∀ v : ℝ × ℝ → EuclideanSpace ℝ (Fin 2), ContDiff ℝ ∞ v → ∀ i : Fin 2,
      ContDiff ℝ 2 (fun z => v z i) := fun v hv i =>
    (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp (hv.of_le (by simp))
  have hdiff : ∀ v : ℝ × ℝ → EuclideanSpace ℝ (Fin 2), ContDiff ℝ ∞ v → ∀ (i j : Fin 2) (z : ℝ × ℝ),
      DifferentiableAt ℝ (fun z => B0579.pd j (fun w => v w i) z) z := fun v hv i j z =>
    TrainBddAux.pd_differentiableAt (hc2 v hv i) j z
  have huw : ContDiff ℝ ∞ (u - w) := hu.sub hw
  have hcu := curl_eq_pd u (hu.of_le (by simp))
  have hcw := curl_eq_pd w (hw.of_le (by simp))
  have hcuw := curl_eq_pd (u - w) (huw.of_le (by simp))
  have hcomp : ∀ (i j : Fin 2) (z : ℝ × ℝ), B0579.pd j (fun y => (u - w) y i) z =
      B0579.pd j (fun y => u y i) z - B0579.pd j (fun y => w y i) z := by
    intro i j z
    have : (fun y => (u - w) y i) = fun y => u y i - w y i := by
      funext y; simp [Pi.sub_apply]
    rw [this]
    exact pd_sub j ((hc2 u hu i).differentiable (by norm_num) z)
      ((hc2 w hw i).differentiable (by norm_num) z)
  have hcurl : UnforcedLeray.Cyl.curl (u - w) =
      fun z => UnforcedLeray.Cyl.curl u z - UnforcedLeray.Cyl.curl w z := by
    rw [hcuw, hcu, hcw]
    funext z
    rw [hcomp 1 0 z, hcomp 0 1 z]
    ring
  rw [hcurl, pd_sub l]
  · rw [hcu]; exact (hdiff u hu 1 0 x).sub (hdiff u hu 0 1 x)
  · rw [hcw]; exact (hdiff w hw 1 0 x).sub (hdiff w hw 0 1 x)

/-- Gaussian and periodized-Gaussian vorticity gradients (SP 2861-2873, 2895). -/
theorem gradE_bounds : ∃ C_E : ℝ, 0 ≤ C_E ∧ ∀ d : ℝ, 1 ≤ d → ∀ l : Fin 2,
    (∀ x : ℝ × ℝ, |B0579.pd l (UnforcedLeray.Cyl.curl UnforcedLeray.Train.v0) x| ≤
      C_E * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 8)) ∧
    (∀ x ∈ B0579.cell d, B0579.jb x ^ 2 *
      |B0579.pd l (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) x -
        B0579.pd l (UnforcedLeray.Cyl.curl UnforcedLeray.Train.v0) x| ≤ C_E / d ^ 2) ∧
    (∀ x ∈ B0579.cell d, B0579.jb x ^ 2 *
      |B0579.pd l (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) x| ≤ C_E) := by
  obtain ⟨A, hA, hbA⟩ := UnforcedLeray.Train.norm_iteratedFDeriv_v0_le 2
  obtain ⟨C₃, hC₃, hT3⟩ := datum_jet2_tail
  refine ⟨2 * C₃ + 2 * A * 1026 + 2 * A, by positivity, fun d hd l => ?_⟩
  have hd0 : d ≠ 0 := by positivity
  have hv0 : ContDiff ℝ ∞ UnforcedLeray.Train.v0 := UnforcedLeray.Train.contDiff_v0
  have hdat : ContDiff ℝ ∞ (UnforcedLeray.Train.datum d) := UnforcedLeray.Train.datum_contDiff hd0
  have h0 : ∀ x : ℝ × ℝ, |B0579.pd l (UnforcedLeray.Cyl.curl UnforcedLeray.Train.v0) x| ≤
      2 * A * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 8) := by
    intro x
    refine (TrainBddAux.pd_curl_le _ hv0 l x).trans ?_
    have := hbA x
    linarith
  have h1 : ∀ x ∈ B0579.cell d, B0579.jb x ^ 2 *
      |B0579.pd l (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) x -
        B0579.pd l (UnforcedLeray.Cyl.curl UnforcedLeray.Train.v0) x| ≤ 2 * C₃ / d ^ 2 := by
    intro x hx
    rw [pd_curl_sub _ _ hdat hv0 l x]
    have hle := TrainBddAux.pd_curl_le (UnforcedLeray.Train.datum d - UnforcedLeray.Train.v0)
      (hdat.sub hv0) l x
    rw [iteratedFDeriv_sub_apply (hdat.contDiffAt.of_le (by simp)) (hv0.contDiffAt.of_le (by simp))] at hle
    have hT := hT3 d hd x hx
    have hj : 0 ≤ B0579.jb x ^ 2 := by positivity
    calc B0579.jb x ^ 2 * |B0579.pd l (UnforcedLeray.Cyl.curl
          (UnforcedLeray.Train.datum d - UnforcedLeray.Train.v0)) x|
        ≤ B0579.jb x ^ 2 * (2 * ‖iteratedFDeriv ℝ 2 (UnforcedLeray.Train.datum d) x -
            iteratedFDeriv ℝ 2 UnforcedLeray.Train.v0 x‖) := mul_le_mul_of_nonneg_left hle hj
      _ = 2 * (B0579.jb x ^ 2 * ‖iteratedFDeriv ℝ 2 (UnforcedLeray.Train.datum d) x -
            iteratedFDeriv ℝ 2 UnforcedLeray.Train.v0 x‖) := by ring
      _ ≤ 2 * (C₃ / d ^ 2) := by linarith
      _ = 2 * C₃ / d ^ 2 := by ring
  have hd2 : 1 ≤ d ^ 2 := by nlinarith
  refine ⟨fun x => (h0 x).trans (mul_le_mul_of_nonneg_right (by linarith [hC₃])
    (Real.exp_pos _).le), fun x hx => (h1 x hx).trans ?_, fun x hx => ?_⟩
  · gcongr; linarith [hA]
  · have hj : 0 ≤ B0579.jb x ^ 2 := by positivity
    have htri : |B0579.pd l (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) x| ≤
        |B0579.pd l (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) x -
          B0579.pd l (UnforcedLeray.Cyl.curl UnforcedLeray.Train.v0) x| +
        |B0579.pd l (UnforcedLeray.Cyl.curl UnforcedLeray.Train.v0) x| := by
      have := abs_add_le (B0579.pd l (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) x -
          B0579.pd l (UnforcedLeray.Cyl.curl UnforcedLeray.Train.v0) x)
        (B0579.pd l (UnforcedLeray.Cyl.curl UnforcedLeray.Train.v0) x)
      rwa [sub_add_cancel] at this
    have hg : B0579.jb x ^ 2 * |B0579.pd l (UnforcedLeray.Cyl.curl UnforcedLeray.Train.v0) x| ≤
        2 * A * 1026 := by
      have h3 : Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16) ≤ 1 :=
        Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg x.1, sq_nonneg x.2])
      calc B0579.jb x ^ 2 * |B0579.pd l (UnforcedLeray.Cyl.curl UnforcedLeray.Train.v0) x|
          ≤ B0579.jb x ^ 2 * (2 * A * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 8)) :=
            mul_le_mul_of_nonneg_left (h0 x) hj
        _ = 2 * A * (B0579.jb x ^ 2 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 8)) := by ring
        _ ≤ 2 * A * 1026 := mul_le_mul_of_nonneg_left (jb_sq_exp_le_const x) (by positivity)
    have h1x := h1 x hx
    have hC3d : 2 * C₃ / d ^ 2 ≤ 2 * C₃ := div_le_self (by positivity) hd2
    nlinarith [mul_le_mul_of_nonneg_left htri hj]

/-! ## 2. The Gaussian-cylinder residual -/

theorem norm_seedModeEigen (lam : ℂ) (k : Fin 2) : ‖seedModeEigen lam k‖ = ‖lam‖ := by
  unfold seedModeEigen; split_ifs <;> simp

theorem inv_sq_le_one (a b : ℝ) : ((1 + |a| + |b|)⁻¹) ^ 2 ≤ 1 := by
  have h : 1 ≤ 1 + |a| + |b| := by linarith [abs_nonneg a, abs_nonneg b]
  have h1 : (1 + |a| + |b|)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h
  have h0 : 0 ≤ (1 + |a| + |b|)⁻¹ := by positivity
  nlinarith

/-- **The Gaussian-cylinder dual residual is `O(d⁻²)`** (SP 2876-2897), given the planar seed
duality at `lam`. -/
theorem gaussSub_bound {κ : PlanarFrameKernels} (hκ : IsSeedKernels κ) {lam : ℂ}
    (hdual : ∀ (k : Fin 2) (y : ℝ × ℝ),
      E0.transCx (fun z l => UnforcedLeray.Train.v0 z l) (κ.lamP k) y -
        kerAdjPl (fun l x => κ.lamP k x *
          ((B0579.pd l (UnforcedLeray.Cyl.curl UnforcedLeray.Train.v0) x : ℝ) : ℂ)) y =
      seedModeEigen lam k * κ.lamP k y)
    {m : ℝ} (hm : 3 < m) :
    ∃ C_G : ℝ, 0 ≤ C_G ∧ ∀ d : ℝ, 1 ≤ d → ∀ k : Fin 2,
      MemLp (movLam0EulerGaussSub κ lam d k) 2 (B0579.cellMeasure d (-m)) ∧
      xNorm d (-m) (movLam0EulerGaussSub κ lam d k) ≤ ENNReal.ofReal (C_G / d ^ 2) := by
  obtain ⟨hL, Cl, hCl0, hl0, hl1⟩ := lamP_jets hκ
  obtain ⟨C₁, hC₁0, hT1⟩ := lamP_tails hκ
  obtain ⟨B₀, hB₀, hB0⟩ := Lam0B.perLam0_sup κ
  obtain ⟨C₂, hC₂0, hT2⟩ := datum_tail
  obtain ⟨Cv, hCv0, hCv⟩ := v0_bound
  obtain ⟨C_E, hCE0, hgrad⟩ := gradE_bounds
  obtain ⟨K_u, hKu0, hKunif⟩ := kernel_unif
  obtain ⟨K_n, hKn0, hKnear⟩ := kernel_near
  set U : ℝ := 2 * ((Cv + C₂) * (Cl + C₁)) + K_u * (B₀ * C_E) + ‖lam‖ * B₀ with hU
  set Nc : ℝ := 2 * (C₂ * (Cl + C₁) + Cv * C₁) + K_n * ((B₀ + Cl + C₁) * C_E) + ‖lam‖ * C₁
    with hNc
  set M_R : ℝ := Nc + 64 * U with hMR
  have hU0 : 0 ≤ U := by positivity
  have hNc0 : 0 ≤ Nc := by positivity
  refine ⟨(B0592.weightConst (m - 2)).toReal * M_R, by positivity, fun d hd k => ?_⟩
  have hd0 : 0 < d := by linarith
  have hd2 : 0 < d ^ 2 := by positivity
  have hd21 : 1 ≤ d ^ 2 := by nlinarith
  set Φ : ℝ × ℝ → ℂ := perLam0 κ d k with hΦ
  set lamF : ℝ × ℝ → ℂ := κ.lamP k with hlamF
  set E : ℝ × ℝ → ℝ := UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d) with hE
  set E0' : ℝ × ℝ → ℝ := UnforcedLeray.Cyl.curl UnforcedLeray.Train.v0 with hE0'
  have hΦc : Continuous Φ :=
    ComplCouplingHeat.perSum_continuous_of_inv_sq_decay hd0 (κ.lamP_cont k) (hl0 k)
  have hlc : Continuous lamF := κ.lamP_cont k
  have hlb : ∀ x, ‖lamF x‖ ≤ Cl := fun x =>
    (hl0 k x).trans (mul_le_of_le_one_right hCl0 (inv_sq_le_one _ _))
  have hlgb : ∀ (l : Fin 2) (x : ℝ × ℝ), ‖pdCx l lamF x‖ ≤ Cl := fun l x =>
    ((CutFTCGradPerSum.norm_pdCx_le_norm_fderiv _ l x).trans (hl1 k x)).trans
      (mul_le_of_le_one_right hCl0 (inv_sq_le_one _ _))
  have hgradΦ : ∀ (l : Fin 2), ∀ y ∈ B0579.cell d, ‖pdCx l Φ y‖ ≤ Cl + C₁ := by
    intro l y hy
    have h := (hT1 d hd k y hy).2 l
    have h' : C₁ / d ^ 2 ≤ C₁ := div_le_self hC₁0 hd21
    calc ‖pdCx l Φ y‖ = ‖(pdCx l Φ y - pdCx l lamF y) + pdCx l lamF y‖ := by ring_nf
      _ ≤ ‖pdCx l Φ y - pdCx l lamF y‖ + ‖pdCx l lamF y‖ := norm_add_le _ _
      _ ≤ C₁ + Cl := add_le_add (h.trans h') (hlgb l y)
      _ = Cl + C₁ := by ring
  have hVb : ∀ y ∈ B0579.cell d, ∀ l : Fin 2,
      |UnforcedLeray.Train.datum d y l - UnforcedLeray.Train.v0 y l| ≤ C₂ / d ^ 2 ∧
      |UnforcedLeray.Train.datum d y l| ≤ Cv + C₂ ∧ |UnforcedLeray.Train.v0 y l| ≤ Cv := by
    intro y hy l
    have hv0 : ‖UnforcedLeray.Train.v0 y‖ ≤ Cv :=
      (hCv y).trans (mul_le_of_le_one_right hCv0
        (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg y.1]) (by norm_num)))
    have htail := hT2 d hd y hy
    have hc1 : |UnforcedLeray.Train.datum d y l - UnforcedLeray.Train.v0 y l| ≤
        ‖UnforcedLeray.Train.datum d y - UnforcedLeray.Train.v0 y‖ := by
      have := PiLp.norm_apply_le (UnforcedLeray.Train.datum d y - UnforcedLeray.Train.v0 y) l
      simpa [Real.norm_eq_abs] using this
    have hc2 : |UnforcedLeray.Train.v0 y l| ≤ ‖UnforcedLeray.Train.v0 y‖ := by
      have := PiLp.norm_apply_le (UnforcedLeray.Train.v0 y) l
      simpa [Real.norm_eq_abs] using this
    have h' : C₂ / d ^ 2 ≤ C₂ := div_le_self hC₂0 hd21
    refine ⟨hc1.trans htail, ?_, hc2.trans hv0⟩
    have := abs_add_le (UnforcedLeray.Train.datum d y l - UnforcedLeray.Train.v0 y l)
      (UnforcedLeray.Train.v0 y l)
    rw [sub_add_cancel] at this
    linarith [hc1.trans htail, hc2.trans hv0]
  -- the residual
  set R : ℝ × ℝ → ℂ := movLam0EulerGaussSub κ lam d k with hR
  have hRexp : ∀ y, R y = E0.transCx (fun z l => UnforcedLeray.Train.datum d z l) Φ y -
      kerAdj d (fun l x => Φ x * ((B0579.pd l E x : ℝ) : ℂ)) y - seedModeEigen lam k * Φ y :=
    fun y => rfl
  have hEgrad := hgrad d hd
  -- the uniform bound on the cell
  have hunif : ∀ y ∈ B0579.cell d, ‖R y‖ ≤ U := by
    intro y hy
    rw [hRexp]
    have hT : ‖E0.transCx (fun z l => UnforcedLeray.Train.datum d z l) Φ y‖ ≤
        2 * ((Cv + C₂) * (Cl + C₁)) := by
      unfold E0.transCx
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs]
      have h0 := mul_le_mul (hVb y hy 0).2.1 (hgradΦ 0 y hy) (norm_nonneg _) (by positivity)
      have h1 := mul_le_mul (hVb y hy 1).2.1 (hgradΦ 1 y hy) (norm_nonneg _) (by positivity)
      linarith
    have hK := (hKunif d B₀ C_E hd hB₀ hCE0 Φ E hΦc (fun x hx => hB0 d hd k x hx)
      (fun l x hx => (hEgrad l).2.2 x hx) y).2
    have hEig : ‖seedModeEigen lam k * Φ y‖ ≤ ‖lam‖ * B₀ := by
      rw [norm_mul, norm_seedModeEigen]
      exact mul_le_mul_of_nonneg_left (hB0 d hd k y hy) (norm_nonneg _)
    calc ‖E0.transCx (fun z l => UnforcedLeray.Train.datum d z l) Φ y -
          kerAdj d (fun l x => Φ x * ((B0579.pd l E x : ℝ) : ℂ)) y - seedModeEigen lam k * Φ y‖
        ≤ ‖E0.transCx (fun z l => UnforcedLeray.Train.datum d z l) Φ y‖ +
            ‖kerAdj d (fun l x => Φ x * ((B0579.pd l E x : ℝ) : ℂ)) y‖ +
            ‖seedModeEigen lam k * Φ y‖ := norm_sub_le_of_le (norm_sub_le _ _) le_rfl
      _ ≤ U := by rw [hU]; linarith
  -- the bound near the axis
  have hnear : ∀ y ∈ B0579.cell d, ‖planeToC y‖ ≤ d / 8 → ‖R y‖ ≤ Nc * B0579.jb y / d ^ 2 := by
    intro y hy hy8
    have hjb1 : 1 ≤ B0579.jb y := one_le_jb y
    have hP := hdual k y
    have hsplit : R y =
        (E0.transCx (fun z l => UnforcedLeray.Train.datum d z l) Φ y -
          E0.transCx (fun z l => UnforcedLeray.Train.v0 z l) lamF y) -
        (kerAdj d (fun l x => Φ x * ((B0579.pd l E x : ℝ) : ℂ)) y -
          kerAdjPl (fun l x => lamF x * ((B0579.pd l E0' x : ℝ) : ℂ)) y) -
        seedModeEigen lam k * (Φ y - lamF y) := by
      rw [hRexp]
      rw [hlamF, hE0'] at *
      linear_combination hP
    have hT : ‖E0.transCx (fun z l => UnforcedLeray.Train.datum d z l) Φ y -
        E0.transCx (fun z l => UnforcedLeray.Train.v0 z l) lamF y‖ ≤
        2 * (C₂ * (Cl + C₁) + Cv * C₁) / d ^ 2 := by
      have hterm : ∀ l : Fin 2,
          ‖((UnforcedLeray.Train.datum d y l : ℝ) : ℂ) * pdCx l Φ y -
            ((UnforcedLeray.Train.v0 y l : ℝ) : ℂ) * pdCx l lamF y‖ ≤
          (C₂ * (Cl + C₁) + Cv * C₁) / d ^ 2 := by
        intro l
        have he : ((UnforcedLeray.Train.datum d y l : ℝ) : ℂ) * pdCx l Φ y -
            ((UnforcedLeray.Train.v0 y l : ℝ) : ℂ) * pdCx l lamF y =
            ((UnforcedLeray.Train.datum d y l - UnforcedLeray.Train.v0 y l : ℝ) : ℂ) * pdCx l Φ y +
              ((UnforcedLeray.Train.v0 y l : ℝ) : ℂ) * (pdCx l Φ y - pdCx l lamF y) := by
          push_cast; ring
        rw [he]
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs]
        obtain ⟨hv1, -, hv3⟩ := hVb y hy l
        have hg := (hT1 d hd k y hy).2 l
        have e1 := mul_le_mul hv1 (hgradΦ l y hy) (norm_nonneg _) (by positivity)
        have e2 := mul_le_mul hv3 hg (norm_nonneg _) hCv0
        calc |UnforcedLeray.Train.datum d y l - UnforcedLeray.Train.v0 y l| * ‖pdCx l Φ y‖ +
              |UnforcedLeray.Train.v0 y l| * ‖pdCx l Φ y - pdCx l lamF y‖
            ≤ C₂ / d ^ 2 * (Cl + C₁) + Cv * (C₁ / d ^ 2) := add_le_add e1 e2
          _ = (C₂ * (Cl + C₁) + Cv * C₁) / d ^ 2 := by ring
      have hsum : E0.transCx (fun z l => UnforcedLeray.Train.datum d z l) Φ y -
          E0.transCx (fun z l => UnforcedLeray.Train.v0 z l) lamF y =
          (((UnforcedLeray.Train.datum d y 0 : ℝ) : ℂ) * pdCx 0 Φ y -
            ((UnforcedLeray.Train.v0 y 0 : ℝ) : ℂ) * pdCx 0 lamF y) +
          (((UnforcedLeray.Train.datum d y 1 : ℝ) : ℂ) * pdCx 1 Φ y -
            ((UnforcedLeray.Train.v0 y 1 : ℝ) : ℂ) * pdCx 1 lamF y) := by
        unfold E0.transCx; ring
      rw [hsum]
      refine (norm_add_le _ _).trans ?_
      have := hterm 0
      have := hterm 1
      rw [show 2 * (C₂ * (Cl + C₁) + Cv * C₁) / d ^ 2 =
        (C₂ * (Cl + C₁) + Cv * C₁) / d ^ 2 + (C₂ * (Cl + C₁) + Cv * C₁) / d ^ 2 by ring]
      linarith
    have hK := hKnear d B₀ Cl C₁ C_E hd hB₀ hCl0 hC₁0 hCE0 Φ lamF E E0' hΦc hlc
      (fun x hx => hB0 d hd k x hx) hlb (fun x hx => (hT1 d hd k x hx).1)
      (fun l x => (hEgrad l).1 x) (fun l x hx => (hEgrad l).2.1 x hx)
      (fun l x hx => (hEgrad l).2.2 x hx) y hy8
    have hEig : ‖seedModeEigen lam k * (Φ y - lamF y)‖ ≤ ‖lam‖ * C₁ / d ^ 2 := by
      rw [norm_mul, norm_seedModeEigen, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (hT1 d hd k y hy).1 (norm_nonneg _)
    rw [hsplit]
    have h3 := norm_sub_le_of_le (norm_sub_le_of_le (le_refl
      ‖E0.transCx (fun z l => UnforcedLeray.Train.datum d z l) Φ y -
        E0.transCx (fun z l => UnforcedLeray.Train.v0 z l) lamF y‖) (le_refl
      ‖kerAdj d (fun l x => Φ x * ((B0579.pd l E x : ℝ) : ℂ)) y -
        kerAdjPl (fun l x => lamF x * ((B0579.pd l E0' x : ℝ) : ℂ)) y‖)) (le_refl
      ‖seedModeEigen lam k * (Φ y - lamF y)‖)
    refine h3.trans ?_
    have e1 : 2 * (C₂ * (Cl + C₁) + Cv * C₁) / d ^ 2 ≤
        2 * (C₂ * (Cl + C₁) + Cv * C₁) * B0579.jb y / d ^ 2 := by
      rw [div_le_div_iff_of_pos_right hd2]; nlinarith [show 0 ≤ 2 * (C₂ * (Cl + C₁) + Cv * C₁) by positivity]
    have e3 : ‖lam‖ * C₁ / d ^ 2 ≤ ‖lam‖ * C₁ * B0579.jb y / d ^ 2 := by
      rw [div_le_div_iff_of_pos_right hd2]; nlinarith [show 0 ≤ ‖lam‖ * C₁ by positivity]
    have : Nc * B0579.jb y / d ^ 2 = 2 * (C₂ * (Cl + C₁) + Cv * C₁) * B0579.jb y / d ^ 2 +
        K_n * ((B₀ + Cl + C₁) * C_E) * B0579.jb y / d ^ 2 + ‖lam‖ * C₁ * B0579.jb y / d ^ 2 := by
      rw [hNc]; ring
    rw [this]
    linarith
  -- the pointwise bound on the cell
  have hpt : ∀ y ∈ B0579.cell d, ‖R y‖ ≤ M_R / d ^ 2 * B0579.jb y := by
    intro y hy
    have hjb1 : 1 ≤ B0579.jb y := one_le_jb y
    by_cases hy8 : ‖planeToC y‖ ≤ d / 8
    · refine (hnear y hy hy8).trans ?_
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hd2, hMR]
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ 64 * U by positivity) (le_trans zero_le_one hjb1)]
    · have hy8' : d / 8 < ‖planeToC y‖ := lt_of_not_ge hy8
      have hjb : d ^ 2 / 64 ≤ B0579.jb y := by
        rw [jb_eq_norm]; nlinarith [norm_nonneg (planeToC y)]
      refine (hunif y hy).trans ?_
      rw [div_mul_eq_mul_div, le_div_iff₀ hd2, hMR]
      nlinarith [mul_le_mul_of_nonneg_left hjb (show (0 : ℝ) ≤ 64 * U by positivity),
        mul_nonneg hNc0 (le_trans zero_le_one hjb1)]
  -- measurability
  have hRm : AEStronglyMeasurable R (volume.restrict (B0579.cell d)) := by
    have hVc : ∀ l : Fin 2, Continuous fun z => UnforcedLeray.Train.datum d z l := fun l =>
      (EuclideanSpace.proj l : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).continuous.comp
        (UnforcedLeray.Train.datum_contDiff (by positivity)).continuous
    have hpdΦ : ∀ l : Fin 2, Measurable fun y => pdCx l Φ y := fun l =>
      measurable_fderiv_apply_const ℝ Φ (B0579.dir l)
    have hT : Measurable fun y => E0.transCx (fun z l => UnforcedLeray.Train.datum d z l) Φ y := by
      unfold E0.transCx
      exact ((Complex.measurable_ofReal.comp (hVc 0).measurable).mul (hpdΦ 0)).add
        ((Complex.measurable_ofReal.comp (hVc 1).measurable).mul (hpdΦ 1))
    have hK : StronglyMeasurable (kerAdj d (fun l x => Φ x * ((B0579.pd l E x : ℝ) : ℂ))) :=
      stronglyMeasurable_kerAdj d (fun l =>
        (hΦc.measurable.mul (Complex.measurable_ofReal.comp (measurable_pd E l))).stronglyMeasurable)
    have hRfun : R = fun y => E0.transCx (fun z l => UnforcedLeray.Train.datum d z l) Φ y -
        kerAdj d (fun l x => Φ x * ((B0579.pd l E x : ℝ) : ℂ)) y - seedModeEigen lam k * Φ y :=
      funext hRexp
    rw [hRfun]
    exact ((hT.aestronglyMeasurable.sub hK.aestronglyMeasurable).sub
      (hΦc.aestronglyMeasurable.const_mul _))
  obtain ⟨hmem, hx⟩ := memLp_and_xNorm_of_le_jb hm (by positivity) hRm hpt
  refine ⟨hmem, hx.trans (le_of_eq ?_)⟩
  congr 1
  ring

/-! ## 3. The conditional assembly of the target -/

/-- `MovLam0DualEulerSubBound κ` from the planar seed duality (train comparison and linearity are
proved). -/
theorem movLam0DualEulerSubBound_of_dual (κ : PlanarFrameKernels)
    (hdual : PlanarSeedEulerDual κ) : ComplCouplingEuler.MovLam0DualEulerSubBound κ := by
  intro hκ m hm
  obtain ⟨lam, hl⟩ := hdual hκ
  obtain ⟨C_G, hCG, hG⟩ := gaussSub_bound hκ hl (m := m) (by linarith)
  obtain ⟨C_tr, ν_tr, hCtr, hνtr, htr⟩ :=
    memLp_and_xNorm_movEulerAdj_trainDiff κ (seedLamGradPerSum κ) hκ hm
  obtain ⟨D_ker, hDker, hKerLin⟩ := DirectEulerSub.kerAdj_perLam_eq κ
  have hDiff := DirectEulerSub.perLam0Differentiable_of_seedLamGradPerSum κ (seedLamGradPerSum κ)
  refine ⟨lam, C_tr + C_G, 1, by positivity, le_rfl, fun b hb => ?_⟩
  have hD0 : 0 ≤ D_ker := by linarith
  refine ⟨min ν_tr (min 1 (1 / (D_ker + 1) ^ 2)),
    lt_min hνtr (lt_min zero_lt_one (by positivity)), fun ν hν tr hBUC r hr hθ => ?_⟩
  intro d
  have hν_pos : 0 < ν := hν.1
  have hν_tr : ν ≤ ν_tr := le_trans hν.2 (min_le_left _ _)
  have hν1 : ν ≤ 1 := le_trans hν.2 (le_trans (min_le_right _ _) (min_le_left _ _))
  have hνD : ν ≤ 1 / (D_ker + 1) ^ 2 :=
    le_trans hν.2 (le_trans (min_le_right _ _) (min_le_right _ _))
  have hθ1 : 1 ≤ clockTheta ν r := le_trans hb hθ
  have hθ_pos : 0 < clockTheta ν r := lt_of_lt_of_le zero_lt_one hθ1
  have hdD : D_ker ≤ d := cellLen_ge hD0 hν_pos hνD hb hr hθ
  have hd1 : 1 ≤ d := le_trans hDker hdD
  refine ⟨fun i y => ?_, fun j => ?_⟩
  · unfold ComplCouplingEuler.movEulerAdj
    rw [DirectEulerSub.transCx_perLam_eq_of_diff κ d (movingTrainV tr r) i y
        (hDiff hκ hd1 0 y) (hDiff hκ hd1 1 y),
      hKerLin ν ⟨hν_pos, hν1⟩ tr hBUC r hr hdD i y]
    simp only [Fin.sum_univ_two]
    ring
  · have h1 := htr ν ⟨hν_pos, hν_tr⟩ tr hBUC r hr hθ1 j
    have h2 := hG d hd1 j
    have hd2 : 1 / d ^ 2 = ν ^ 3 / clockTheta ν r :=
      ComplCouplingSub.inv_cellLen_sq_eq_nu_cube_div_theta hν_pos hr
    have h2' : xNorm d (-m) (movLam0EulerGaussSub κ lam d j) ≤
        ENNReal.ofReal (C_G * ν ^ 3 / clockTheta ν r) := by
      refine h2.2.trans (le_of_eq ?_)
      congr 1
      calc C_G / d ^ 2 = C_G * (1 / d ^ 2) := by ring
        _ = C_G * (ν ^ 3 / clockTheta ν r) := by rw [hd2]
        _ = C_G * ν ^ 3 / clockTheta ν r := by ring
    have hdecomp : ComplCouplingEuler.movLam0DualEulerSub κ lam tr r j = fun y =>
        (ComplCouplingEuler.movEulerAdj d (movingTrainV tr r) (movingTrainE tr r)
            (perLam0 κ d j) y - movEulerAdjGauss d (perLam0 κ d j) y) +
          movLam0EulerGaussSub κ lam d j y := by
      funext y
      unfold ComplCouplingEuler.movLam0DualEulerSub movLam0EulerGaussSub
      ring
    rw [hdecomp]
    obtain ⟨hm12, hx12⟩ := ComplCouplingHeat.memLp_and_xNorm_add_le (by positivity)
      (by positivity) h1.1 h2.1 h1.2 h2'
    refine ⟨hm12, hx12.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    have hν3 : ν ^ 3 ≤ 1 := pow_le_one₀ hν_pos.le hν1
    have : C_tr * ν ^ 3 / clockTheta ν r + C_G * ν ^ 3 / clockTheta ν r =
        (C_tr + C_G) * ν ^ 3 * (1 / clockTheta ν r) := by ring
    rw [this]
    have hinv : 0 ≤ 1 / clockTheta ν r := by positivity
    calc (C_tr + C_G) * ν ^ 3 * (1 / clockTheta ν r)
        ≤ (C_tr + C_G) * 1 * (1 / clockTheta ν r) := by gcongr
      _ = (C_tr + C_G) * (1 / clockTheta ν r) := by ring

/-- **Conditional assembly of `MovLamDualEulerSubBound κ`** (`PartIII-a:T21/c5/3/2`) from the
planar seed duality leaf `PlanarSeedEulerDual κ`. -/
theorem movLamDualEulerSubBound_of_dual (κ : PlanarFrameKernels)
    (hdual : PlanarSeedEulerDual κ) : MovLamDualEulerSubBound κ :=
  ComplCouplingEuler.movLamDualEulerSubBound_of κ (movLam0DualEulerSubBound_of_dual κ hdual)

end EulerSubCore

end UnforcedLeray.Short.IIIa
