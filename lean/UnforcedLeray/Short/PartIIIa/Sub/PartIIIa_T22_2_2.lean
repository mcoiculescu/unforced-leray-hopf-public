import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T22

/-!
# Part III-a, task `PartIII-a:T22/2/2`: physical-cylinder canonical residual (`CTCanonicalResidual`, SP 3129-3215)

Source of record: `the November 2 reference manuscript` (SP), lines 3129-3215
(`eq:ct-moving-period`, `eq:ct-base-error`, `eq:ct-long-residual`, `eq:ct-late-residual`).

## Mathematical structure and proved infrastructure in this file

1. **Standing regularity bridge `HasCanonicalSolutionRep P`**:
   `Blueprint.Planar.IsPlanarReference P` (`Blueprint/Construction/Planar.lean:116-124, 168-177`)
   records `P.canonical` only via `IsCanonicalBranch` (pointwise `MemXG` at `j = 0`, smoothness and
   pointwise PDE on `(0, ∞) × (0, ∞)` excluding `r = 0`, boundedness on `(0, 1]`, and `j = 0`
   asymptotic on `[θ₁, ∞)`), dropping the `X_G`-valued canonical curve `PartI.IsCanonicalSolution V`
   constructed in `Short/Spine/Sub/SP_CAN.lean:93`.
   `HasCanonicalSolutionRep P` restores that link (`P.canonical θ =ᵐ[xGMeasure] V θ` for `θ > 0`)
   and simultaneously supplies `Cons.C01.IsXGContinuous P.canonical` for `T22/2/1`.

2. **Unconditional Part I seed identification, uniqueness, `IsSmoothAllXGj`, and `X_{G,j}` bounds
   (`planarReference_seed_and_kappa`, `canonicalSolutionRep_smooth_and_bounds`)**:
   Without assuming any extra higher-norm hypothesis beyond `HasCanonicalSolutionRep P`, we prove:
   * `(P.eigenvalue, q_P, innerSL ℂ qdag_P)` is a Part I seed triple (`PartI.IsSeedXG`) with
     `q_P ∈ B0094.D.domain` and `PartI.seedKappa (innerSL ℂ qdag_P) q_P hq_P = P.kappa`;
   * by `T22Sub.canonicalBranch_unconditional` uniqueness and the Spine regularity bootstrap
     (`strongCanonicalIsMild`, `mildSpatialSmoothing`, `mildIsStrong`, `strongBootstrap`,
     `PartI.greenEllipticRegularity`), `V` satisfies `Spine.IsSmoothAllXGj V`, uniform zeroth-norm
     (`j = 0`) bounds WITHOUT `(1 + θ)` growth on `[b, ∞)`, polynomial `O((1 + θ)^4)` graph-norm
     bounds at order `j = 8` on `[b, ∞)`, and uniform compact-window `j = 0, 8` bounds on `[r, b]`.

3. **Fixed-period commutation, exact physical/heat scaling, and subinterval weak-FTC restriction**:
   * `jscale_periodizeC_cellLen` and `canonicalPhysColumn_eq_periodizeC_planar` express
     `canonicalPhysColumn P ν s` on the fixed period `c = ν ^ (-2 : ℝ)`;
   * `canonicalPhysResidual` splits the physical residual into `canonGaussRes` (`tr`-independent
     Gaussian-cylinder image + cross-cell error) and `canonTrainRes` (actual-vs-Gaussian train error),
     with `rescaled_xNorm_canonicalPhysResidual` cancelling `a(s)^2 / ‖P.gaugeFactor ν‖` exactly;
   * `weak_subinterval_of_zero` restricts the `[0, clockAge ν r]` weak identity and `X_{m,c}`
     continuity to `[coreEnd ν b, clockAge ν r]` via `intervalIntegral.integral_add_adjacent_intervals`.

4. **Unconditional exponential BUC train base-error bounds (`eq:ct-base-error`, SP 3162-3189)**:
   * `movingTrainV_sub_datum_exp_bound` and `movingTrainGradE_sub_datum_exp_bound` prove
     `O(ν³ exp(-2 a_tr θ / ν³))` bounds in moving coordinates for both `movingTrainV - Train.datum d`
     and `⟨y⟩^{2 k_w} (movingTrainGradE - ∇ curl(Train.datum d))` on any window `r_min ≤ θ ≤ ν⁻¹`,
     with exponential rate `a_tr > 0` independent of `r_min` and `b`.
   * `xNorm_canonTrainRes_le` bounds `xNorm d m (canonTrainRes P tr s)` unconditionally once the
     periodic `pdCx` and `kerVelCx` jet bounds of `CanonicalGaussAndJetBound` are given.

5. **Conditional assembly (`ctCanonicalResidual_at`)**:
   Proves the full conclusion of `CTCanonicalResidual` at `(P, hP, hRep : HasCanonicalSolutionRep P)`
   from the two R5-verified analytical leaves `CanonicalColumnWeakEq` and `CanonicalGaussAndJetBound`,
   absorbing all `(1 + θ)^4` and `(ν³)⁻¹` prefactors into the Gaussian error while keeping the
   `(ν³)² θ⁻²` image term purely controlled by the zeroth `X_G` norm (SP 3211-3215).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff InnerProductSpace ComplexConjugate

namespace UnforcedLeray.Short.IIIa.T22Sub

open UnforcedLeray.Short.IIIa

/-- Standing regularity bridge on `P : PlanarData` (`Short/Spine/Sub/SP_CAN.lean:93`,
`Short/Spine/PlanarFromC01.lean:30-45`): `P.canonical` is a profile representative on `(0, ∞)`
of a strong `X_G`-valued canonical solution `PartI.IsCanonicalSolution V`. -/
def HasCanonicalSolutionRep (P : PlanarData) : Prop :=
  ∃ V : ℝ → UnforcedLeray.B0010.XG,
    UnforcedLeray.Short.PartI.IsCanonicalSolution V ∧
      ∀ θ : ℝ, 0 < θ → P.canonical θ =ᵐ[UnforcedLeray.B0010.xGMeasure] (V θ : ℝ → ℂ)

namespace ResidualBoundAux

open EulerErrorSub DirectEulerSub

/-! ## 1. Explicit canonical velocity, residual decomposition, and scaling identities -/

/-- Physical-cylinder periodic Biot-Savart velocity `K_c(w_can(s))` on `cell (ν ^ (-2 : ℝ))`. -/
def canonicalPhysVel (P : PlanarData) (ν s : ℝ) : ℝ × ℝ → Fin 2 → ℂ :=
  kerVelCx (ν ^ (-2 : ℝ)) (canonicalPhysColumn P ν s)

/-- Heat-coordinate pure Gaussian-cylinder Euler defect (`tr`-independent, SP 3141-3160):
`P_d(movLPlanar (planarMode (P.canonical θ))) - movLGauss d (P_d (planarMode (P.canonical θ)))`. -/
def canonGaussRes (P : PlanarData) (d θ : ℝ) (y : ℝ × ℝ) : ℂ :=
  periodizeC d (movLPlanar (planarMode (P.canonical θ))) y -
    movLGauss d (periodizeC d (planarMode (P.canonical θ))) y

/-- Heat-coordinate actual-vs-Gaussian BUC train defect (`eq:ct-base-error`, SP 3162-3189):
`movLGauss d V_d(θ) - movL tr s V_d(θ)`. -/
def canonTrainRes (P : PlanarData) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (s : ℝ) (y : ℝ × ℝ) : ℂ :=
  let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν s)
  let W := periodizeC d (planarMode (P.canonical (clockTheta ν s)))
  movLGauss d W y - movL tr s W y

/-- Physical-cylinder canonical residual
`f_res(s, x) = N_ν a(s)^{-2} J_{a(s)}(canonGaussRes + canonTrainRes)(x)` (SP 3130-3140, 3198-3210). -/
def canonicalPhysResidual (P : PlanarData) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (s : ℝ) (x : ℝ × ℝ) : ℂ :=
  P.gaugeFactor ν * ((clockA ν s ^ (-2 : ℝ) : ℝ) : ℂ) *
    Jscale (clockA ν s)
      (fun y => canonGaussRes P (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (clockTheta ν s) y +
        canonTrainRes P tr s y) x

/-- Rescaling a `c / √a`-periodic sum by `Jscale a` commutes to a fixed `c`-periodic sum (SP 3138). -/
theorem jscale_periodizeC_cellLen {c a : ℝ} (ha : 0 < a) (g : ℝ × ℝ → ℂ) (x : ℝ × ℝ) :
    Jscale a (periodizeC (cellLen c a) g) x = periodizeC c (Jscale a g) x := by
  unfold Jscale periodizeC cellLen
  rw [← tsum_mul_left]
  congr 1
  funext n
  have hsq : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have hcoord : (x.1 / Real.sqrt a - (n : ℝ) * (c / Real.sqrt a), x.2 / Real.sqrt a) =
      ((x.1 - (n : ℝ) * c) / Real.sqrt a, x.2 / Real.sqrt a) := by
    apply Prod.ext
    · field_simp [hsq]
    · rfl
  rw [hcoord]

/-- Fixed-period representation of `canonicalPhysColumn P ν s` on `cell (ν ^ (-2 : ℝ))`. -/
theorem canonicalPhysColumn_eq_periodizeC_planar (P : PlanarData) {ν s : ℝ}
    (hν : 0 < ν) (ha : 0 < clockA ν s) (x : ℝ × ℝ) :
    canonicalPhysColumn P ν s x =
      P.gaugeFactor ν *
        periodizeC (ν ^ (-2 : ℝ))
          (Jscale (clockA ν s) (planarMode (P.canonical (clockTheta ν s)))) x := by
  unfold canonicalPhysColumn canonicalPeriodized
  rw [dOfTheta_eq_cellLen hν ha, jscale_periodizeC_cellLen ha]

theorem jscaleInv_jscale_eq {a : ℝ} (ha : 0 < a) (H : ℝ × ℝ → ℂ) (y : ℝ × ℝ) :
    JscaleInv a (Jscale a H) y = H y := by
  unfold JscaleInv Jscale
  have hsq : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have hpow : (a ^ 2 : ℝ) * a ^ (-2 : ℝ) = 1 := by
    rw [Real.rpow_neg ha.le, Real.rpow_two, mul_inv_cancel₀ (pow_ne_zero 2 ha.ne')]
  have hcoord : (Real.sqrt a * y.1 / Real.sqrt a, Real.sqrt a * y.2 / Real.sqrt a) = y := by
    apply Prod.ext <;> simp [mul_div_cancel_left₀ _ hsq]
  dsimp only
  rw [hcoord]
  calc ((a ^ 2 : ℝ) : ℂ) * (((a ^ (-2 : ℝ) : ℝ) : ℂ) * H y)
      = (((a ^ 2 * a ^ (-2 : ℝ) : ℝ)) : ℂ) * H y := by push_cast; ring
    _ = H y := by rw [hpow, Complex.ofReal_one, one_mul]

theorem jscaleInv_canonicalPhysResidual (P : PlanarData) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) {s : ℝ} (ha : 0 < clockA ν s) :
    JscaleInv (clockA ν s) (canonicalPhysResidual P tr s) =
      fun y => (P.gaugeFactor ν * ((clockA ν s ^ (-2 : ℝ) : ℝ) : ℂ)) *
        (canonGaussRes P (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (clockTheta ν s) y +
          canonTrainRes P tr s y) := by
  funext y
  unfold canonicalPhysResidual
  set α : ℂ := P.gaugeFactor ν * ((clockA ν s ^ (-2 : ℝ) : ℝ) : ℂ)
  set H : ℝ × ℝ → ℂ := fun y' =>
    canonGaussRes P (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (clockTheta ν s) y' +
      canonTrainRes P tr s y'
  have hmul : JscaleInv (clockA ν s) (fun x => α * Jscale (clockA ν s) H x) y =
      α * JscaleInv (clockA ν s) (Jscale (clockA ν s) H) y := by
    unfold JscaleInv
    ring
  change JscaleInv (clockA ν s) (fun x => α * Jscale (clockA ν s) H x) y = α * H y
  rw [hmul, jscaleInv_jscale_eq ha]

private theorem xNorm_const_mul {d m : ℝ} (α : ℂ) (R : ℝ × ℝ → ℂ) :
    xNorm d m (fun y => α * R y) = ENNReal.ofReal ‖α‖ * xNorm d m R := by
  have hsmul : (fun y => α * R y) = α • R := rfl
  unfold xNorm
  rw [hsmul, eLpNorm_const_smul, ← ofReal_norm]

/-- Exact cancellation of `(clockA ν s)^2 / ‖P.gaugeFactor ν‖` against `JscaleInv` of
`canonicalPhysResidual`. -/
theorem rescaled_xNorm_canonicalPhysResidual (P : PlanarData) {ν m : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) {θ : ℝ}
    (hν : 0 < ν) (hθ : 0 < θ) :
    let s := clockAge ν θ
    let a := clockA ν s
    ENNReal.ofReal (a ^ 2 / ‖P.gaugeFactor ν‖) *
        xNorm (dOfTheta ν θ) m (JscaleInv a (canonicalPhysResidual P tr s)) =
      xNorm (dOfTheta ν θ) m
        (fun y => canonGaussRes P (dOfTheta ν θ) θ y + canonTrainRes P tr s y) := by
  intro s a
  have ha_eq : a = (ν * θ)⁻¹ := clockA_clockAge hν hθ
  have ha : 0 < a := by rw [ha_eq]; exact inv_pos.2 (mul_pos hν hθ)
  have hθ_eq : clockTheta ν s = θ := clockTheta_clockAge hν hθ
  have hd_eq : cellLen (ν ^ (-2 : ℝ)) (clockA ν s) = dOfTheta ν θ := by
    rw [← dOfTheta_eq_cellLen hν ha, hθ_eq]
  have hgf_pos : 0 < ‖P.gaugeFactor ν‖ := norm_pos_iff.2 (gaugeFactor_ne_zero P hν)
  have ha_neg : 0 < a ^ (-2 : ℝ) := Real.rpow_pos_of_pos ha (-2)
  have hprod : (a ^ 2 / ‖P.gaugeFactor ν‖) *
      ‖P.gaugeFactor ν * ((a ^ (-2 : ℝ) : ℝ) : ℂ)‖ = 1 := by
    rw [norm_mul, Complex.norm_of_nonneg ha_neg.le, Real.rpow_neg ha.le, Real.rpow_two]
    have hgf_ne : ‖P.gaugeFactor ν‖ ≠ 0 := hgf_pos.ne'
    have ha_ne : a ^ 2 ≠ 0 := pow_ne_zero 2 ha.ne'
    field_simp [hgf_ne, ha_ne]
  rw [jscaleInv_canonicalPhysResidual P tr ha]
  have hfun : (fun y => (P.gaugeFactor ν * ((clockA ν s ^ (-2 : ℝ) : ℝ) : ℂ)) *
        (canonGaussRes P (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) (clockTheta ν s) y +
          canonTrainRes P tr s y)) =
      fun y => (P.gaugeFactor ν * ((a ^ (-2 : ℝ) : ℝ) : ℂ)) *
        (canonGaussRes P (dOfTheta ν θ) θ y + canonTrainRes P tr s y) := by
    funext y
    rw [hd_eq, hθ_eq]
  rw [hfun, xNorm_const_mul, ← mul_assoc,
    ← ENNReal.ofReal_mul (div_nonneg (sq_nonneg a) hgf_pos.le), hprod, ENNReal.ofReal_one, one_mul]

/-! ## 2. Clock calculus and subinterval weak-FTC restriction -/

theorem clockAge_antitone {ν θ₁ θ₂ : ℝ} (hν : 0 < ν) (hθ₁ : 0 < θ₁) (h12 : θ₁ ≤ θ₂) :
    clockAge ν θ₂ ≤ clockAge ν θ₁ := by
  have hθ₂ : 0 < θ₂ := lt_of_lt_of_le hθ₁ h12
  have hfmt : ∀ θ : ℝ, θ ≠ 0 → clockAge ν θ = (ν ^ 2)⁻¹ * θ⁻¹ - ν⁻¹ := by
    intro θ hθ
    unfold clockAge
    have hν_ne : ν ≠ 0 := hν.ne'
    field_simp [hν_ne, hθ]
  rw [hfmt θ₂ hθ₂.ne', hfmt θ₁ hθ₁.ne']
  have hinv : θ₂⁻¹ ≤ θ₁⁻¹ := inv_anti₀ hθ₁ h12
  have hmul : (ν ^ 2)⁻¹ * θ₂⁻¹ ≤ (ν ^ 2)⁻¹ * θ₁⁻¹ :=
    mul_le_mul_of_nonneg_left hinv (by positivity)
  linarith

theorem dOfTheta_sq {ν θ : ℝ} (hν : 0 < ν) (hθ : 0 ≤ θ) :
    (dOfTheta ν θ) ^ 2 = θ / ν ^ 3 := by
  unfold dOfTheta
  exact Real.sq_sqrt (div_nonneg hθ (by positivity))

theorem dOfTheta_rpow_neg_four {ν θ : ℝ} (hν : 0 < ν) (hθ : 0 < θ) :
    (dOfTheta ν θ) ^ (-4 : ℝ) = (ν ^ 3) ^ 2 * θ ^ (-2 : ℝ) := by
  have hd_pos : 0 < dOfTheta ν θ := by unfold dOfTheta; exact Real.sqrt_pos.2 (by positivity)
  have hd4 : (dOfTheta ν θ) ^ (-4 : ℝ) = (((dOfTheta ν θ) ^ 2) ^ 2)⁻¹ := by
    rw [Real.rpow_neg hd_pos.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  rw [hd4, dOfTheta_sq hν hθ.le, Real.rpow_neg hθ.le, Real.rpow_two]
  have hν_ne : ν ≠ 0 := hν.ne'
  have hθ_ne : θ ≠ 0 := hθ.ne'
  field_simp [hν_ne, hθ_ne]

theorem clockWindow_bounds {ν r_min s : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hr : 0 < r_min) (hνr : ν ≤ r_min) (hs : s ∈ Icc (0 : ℝ) (clockAge ν r_min)) :
    1 ≤ clockA ν s ∧ 0 < clockA ν s ∧
      clockTheta ν s ∈ Icc r_min ν⁻¹ ∧ 0 < clockTheta ν s ∧
      1 ≤ dOfTheta ν (clockTheta ν s) ∧
      clockA ν s ≤ (ν ^ (-2 : ℝ)) ^ 2 := by
  have hν3_le_r : ν ^ 3 ≤ r_min := by
    have hν2 : ν ^ 2 ≤ 1 := pow_le_one₀ hν.le hν1
    nlinarith
  have ha1 : 1 ≤ clockA ν s := by unfold clockA; nlinarith [hs.1]
  have ha0 : 0 < clockA ν s := lt_of_lt_of_le zero_lt_one ha1
  have hθ_upper : clockTheta ν s ≤ ν⁻¹ := by
    unfold clockTheta
    rw [mul_inv]
    have ha_inv : (clockA ν s)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ha1
    nlinarith [inv_pos.2 hν]
  have ha_upper : clockA ν s ≤ (ν * r_min)⁻¹ := by
    have hmax : clockA ν (clockAge ν r_min) = (ν * r_min)⁻¹ := clockA_clockAge hν hr
    rw [← hmax]
    unfold clockA
    nlinarith [hs.2]
  have hθ_lower : r_min ≤ clockTheta ν s := by
    unfold clockTheta
    have hmul : ν * clockA ν s ≤ r_min⁻¹ := by
      calc ν * clockA ν s ≤ ν * (ν * r_min)⁻¹ := mul_le_mul_of_nonneg_left ha_upper hν.le
        _ = r_min⁻¹ := by field_simp [hν.ne', hr.ne']
    exact (le_inv_comm₀ hr (mul_pos hν ha0)).2 hmul
  have hθ_pos : 0 < clockTheta ν s := lt_of_lt_of_le hr hθ_lower
  have hd1 : 1 ≤ dOfTheta ν (clockTheta ν s) :=
    one_le_dOfTheta hν (hν3_le_r.trans hθ_lower)
  have hac2 : clockA ν s ≤ (ν ^ (-2 : ℝ)) ^ 2 := by
    have hd_cell : dOfTheta ν (clockTheta ν s) = cellLen (ν ^ (-2 : ℝ)) (clockA ν s) :=
      dOfTheta_eq_cellLen hν ha0
    have hsq1 : 1 ≤ (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) ^ 2 := by
      rw [← hd_cell]
      nlinarith
    unfold cellLen at hsq1
    rw [div_pow, Real.sq_sqrt ha0.le, one_le_div ha0] at hsq1
    exact hsq1
  exact ⟨ha1, ha0, ⟨hθ_lower, hθ_upper⟩, hθ_pos, hd1, hac2⟩

/-- Restricting the weak canonical-column identity from `[0, s₂]` to `[s₁, s₂]` (`0 ≤ s₁ ≤ s₂`). -/
theorem weak_subinterval_of_zero {ν m s₁ s₂ : ℝ}
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    {w_0 : ℝ × ℝ → ℂ} {w_can : ℝ → ℝ × ℝ → ℂ}
    {u_can : ℝ → ℝ × ℝ → Fin 2 → ℂ} {f_res : ℝ → ℝ × ℝ → ℂ}
    (hs₁ : 0 ≤ s₁) (hs₁₂ : s₁ ≤ s₂)
    (hreg : ∀ s ∈ Icc (0 : ℝ) s₂,
      IsBiotSavart (ν ^ (-2 : ℝ)) (w_can s) (u_can s) ∧
      MemLp (f_res s) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) ∧
      HasZeroCirculation (ν ^ (-2 : ℝ)) (f_res s) ∧
      IsCentrallyEven (f_res s) ∧
      Tendsto (fun s' => xNorm (ν ^ (-2 : ℝ)) m (f_res s' - f_res s))
        (𝓝[Icc (0 : ℝ) s₂] s) (𝓝 0))
    (hwk : ∀ φ, B0579.IsCylTest (ν ^ (-2 : ℝ)) φ → ∀ s ∈ Icc (0 : ℝ) s₂,
      IntegrableOn (flowIntegrand tr (w_can s) (u_can s) s φ)
        (B0579.cell (ν ^ (-2 : ℝ))) ∧
      IntervalIntegrable (fun τ =>
        (∫ x in B0579.cell (ν ^ (-2 : ℝ)),
          flowIntegrand tr (w_can τ) (u_can τ) τ φ x) +
        (∫ x in B0579.cell (ν ^ (-2 : ℝ)), f_res τ x * (φ x : ℂ))) volume 0 s ∧
      ∫ x in B0579.cell (ν ^ (-2 : ℝ)), w_can s x * (φ x : ℂ) =
        (∫ x in B0579.cell (ν ^ (-2 : ℝ)), w_0 x * (φ x : ℂ)) +
        ∫ τ in (0 : ℝ)..s,
          ((∫ x in B0579.cell (ν ^ (-2 : ℝ)),
            flowIntegrand tr (w_can τ) (u_can τ) τ φ x) +
          (∫ x in B0579.cell (ν ^ (-2 : ℝ)), f_res τ x * (φ x : ℂ)))) :
    (∀ s ∈ Icc s₁ s₂,
      IsBiotSavart (ν ^ (-2 : ℝ)) (w_can s) (u_can s) ∧
      MemLp (f_res s) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) ∧
      HasZeroCirculation (ν ^ (-2 : ℝ)) (f_res s) ∧
      IsCentrallyEven (f_res s) ∧
      Tendsto (fun s' => xNorm (ν ^ (-2 : ℝ)) m (f_res s' - f_res s))
        (𝓝[Icc s₁ s₂] s) (𝓝 0)) ∧
    (∀ φ, B0579.IsCylTest (ν ^ (-2 : ℝ)) φ → ∀ s ∈ Icc s₁ s₂,
      IntegrableOn (flowIntegrand tr (w_can s) (u_can s) s φ)
        (B0579.cell (ν ^ (-2 : ℝ))) ∧
      IntervalIntegrable (fun τ =>
        (∫ x in B0579.cell (ν ^ (-2 : ℝ)),
          flowIntegrand tr (w_can τ) (u_can τ) τ φ x) +
        (∫ x in B0579.cell (ν ^ (-2 : ℝ)), f_res τ x * (φ x : ℂ))) volume s₁ s ∧
      ∫ x in B0579.cell (ν ^ (-2 : ℝ)), w_can s x * (φ x : ℂ) =
        (∫ x in B0579.cell (ν ^ (-2 : ℝ)), w_can s₁ x * (φ x : ℂ)) +
        ∫ τ in s₁..s,
          ((∫ x in B0579.cell (ν ^ (-2 : ℝ)),
            flowIntegrand tr (w_can τ) (u_can τ) τ φ x) +
          (∫ x in B0579.cell (ν ^ (-2 : ℝ)), f_res τ x * (φ x : ℂ)))) := by
  have hsub : Icc s₁ s₂ ⊆ Icc (0 : ℝ) s₂ := Icc_subset_Icc_left hs₁
  refine ⟨fun s hs => ?_, fun φ hφ s hs => ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hreg s (hsub hs)
    exact ⟨h1, h2, h3, h4, h5.mono_left (nhdsWithin_mono s hsub)⟩
  · have hs₀ : s ∈ Icc (0 : ℝ) s₂ := hsub hs
    have hs₁₀ : s₁ ∈ Icc (0 : ℝ) s₂ := ⟨hs₁, hs₁₂⟩
    obtain ⟨hint_s, hii_0s, heq_s⟩ := hwk φ hφ s hs₀
    obtain ⟨_, hii_0s₁, heq_s₁⟩ := hwk φ hφ s₁ hs₁₀
    have hii_s₁s : IntervalIntegrable (fun τ =>
        (∫ x in B0579.cell (ν ^ (-2 : ℝ)),
          flowIntegrand tr (w_can τ) (u_can τ) τ φ x) +
        (∫ x in B0579.cell (ν ^ (-2 : ℝ)), f_res τ x * (φ x : ℂ))) volume s₁ s := by
      refine hii_0s.mono_set ?_
      rw [uIcc_of_le hs.1, uIcc_of_le hs₀.1]
      exact Icc_subset_Icc_left hs₁
    refine ⟨hint_s, hii_s₁s, ?_⟩
    have hadj := intervalIntegral.integral_add_adjacent_intervals hii_0s₁ hii_s₁s
    rw [heq_s, heq_s₁, ← hadj]
    ring

/-! ## 3. Unconditional Part I seed, uniqueness, `IsSmoothAllXGj`, and `X_{G,j}` bounds -/

private theorem oscillatorD_const_mul_on_pos {f g : Profile} {μ : ℂ}
    (heq : EqOn f (fun r => μ * g r) (Ioi 0)) {r : ℝ} (hr : 0 < r) :
    oscillatorD f r = μ * oscillatorD g r := by
  have hd1 : EqOn (deriv f) (deriv (fun x => μ * g x)) (Ioi 0) := heq.deriv isOpen_Ioi
  have hd2 : EqOn (deriv (deriv f)) (deriv (deriv (fun x => μ * g x))) (Ioi 0) :=
    hd1.deriv isOpen_Ioi
  have hd1_r : deriv f r = μ * deriv g r := by
    rw [hd1 hr, deriv_const_mul_field]
  have hd2_r : deriv (deriv f) r = μ * deriv (deriv g) r := by
    rw [hd2 hr, deriv_const_mul_field', deriv_const_mul_field]
  unfold oscillatorD
  rw [hd1_r, hd2_r, heq hr]
  ring

/-- Any `IsPlanarReference P` induces a Part I seed triple `(P.eigenvalue, q_P, innerSL ℂ qdag_P)`
with `q_P ∈ B0094.D.domain` and `PartI.seedKappa (innerSL ℂ qdag_P) q_P hq_P = P.kappa`. -/
theorem planarReference_seed_and_kappa (P : PlanarData) (hP : IsPlanarReference P) :
    let q_P : UnforcedLeray.B0010.XG :=
      (UnforcedLeray.Cons.G3b.memLp_of_memXG hP.eigenpair.memXG).toLp P.mode
    let qdag_P : UnforcedLeray.B0010.XG :=
      (UnforcedLeray.Cons.G3b.memLp_of_memXG hP.adjoint.memXG).toLp P.adjointMode
    ∃ hq_P : q_P ∈ UnforcedLeray.B0094.D.domain,
      UnforcedLeray.Short.PartI.IsSeedXG P.eigenvalue q_P (innerSL ℂ qdag_P) ∧
        UnforcedLeray.Short.PartI.seedKappa (innerSL ℂ qdag_P) q_P hq_P = P.kappa := by
  intro q_P qdag_P
  let hm_q := UnforcedLeray.Cons.G3b.memLp_of_memXG hP.eigenpair.memXG
  let hm_qd := UnforcedLeray.Cons.G3b.memLp_of_memXG hP.adjoint.memXG
  obtain ⟨c, -, -, -, F, hF⟩ := UnforcedLeray.Cons.C01.exists_wholeLineData
  have hSeed0 : UnforcedLeray.Short.PartI.IsSeedXG (UnforcedLeray.Cons.G3b.lamMode c)
      (UnforcedLeray.Cons.G3b.qMode hF) (innerSL ℂ (UnforcedLeray.Cons.G3b.qdagMode hF)) :=
    UnforcedLeray.Short.Spine.wholeLineModeIsSeed c F hF
  have hq_P_eigen : UnforcedLeray.B0012.L0 q_P = P.eigenvalue • q_P := by
    change UnforcedLeray.B0012.L0 (hm_q.toLp P.mode) = P.eigenvalue • q_P
    rw [UnforcedLeray.B0012.L0_toLp hm_q]
    apply Lp.ext
    filter_upwards [UnforcedLeray.B0012.ae_xG_pos,
      (UnforcedLeray.B0012.memLp_L0Fun hm_q).coeFn_toLp,
      hm_q.coeFn_toLp, Lp.coeFn_smul P.eigenvalue q_P] with r hr hL hq hsmul
    have hq' : ((q_P : UnforcedLeray.B0010.XG) : ℝ → ℂ) r = P.mode r := hq
    rw [hL]
    change UnforcedLeray.B0012.L0Fun P.mode r =
      ((P.eigenvalue • q_P : UnforcedLeray.B0010.XG) : ℝ → ℂ) r
    rw [hsmul, Pi.smul_apply, smul_eq_mul, hq', ← UnforcedLeray.Cons.G3b.generatorL0_eq_L0Fun,
      hP.eigenpair.eigen r hr]
  have hq_P_ne : q_P ≠ 0 := by
    intro h0
    apply hP.eigenpair.nonzero
    have hzeroX : P.mode =ᵐ[UnforcedLeray.B0010.xGMeasure] (0 : ℝ → ℂ) := by
      filter_upwards [hm_q.coeFn_toLp,
        (show (⇑q_P : ℝ → ℂ) =ᵐ[UnforcedLeray.B0010.xGMeasure] 0 from by
          rw [h0]; exact Lp.coeFn_zero ℂ 2 UnforcedLeray.B0010.xGMeasure)] with r h1 h2
      rw [← h1, h2]
    exact UnforcedLeray.B0012.restrict_ac.ae_le hzeroX
  obtain ⟨hlam, μ, hμ⟩ := UnforcedLeray.Planar.L0_eigen_unique hSeed0.re_pos hP.eigenpair.re_pos
    hSeed0.eigen hq_P_eigen hSeed0.ne_zero hq_P_ne
  -- `qdag_P` is an adjoint eigenvector of `L0` for `conj P.eigenvalue`
  have hL_adj : ∀ v : UnforcedLeray.B0010.XG,
      inner ℂ qdag_P (UnforcedLeray.Planar.L0 v) = P.eigenvalue * inner ℂ qdag_P v := by
    intro v
    let p : Profile := (v : ℝ → ℂ)
    have hpMeas : AEStronglyMeasurable p (volume.restrict (Ioi (0 : ℝ))) :=
      (Lp.aestronglyMeasurable v).mono_ac UnforcedLeray.B0012.restrict_ac
    have hp : MemXG p := UnforcedLeray.Cons.G3b.memXG_of_memLp hpMeas (Lp.memLp v)
    have hgenAe : generatorL0 p =ᵐ[UnforcedLeray.B0010.xGMeasure]
        (UnforcedLeray.B0012.L0 v : ℝ → ℂ) := by
      filter_upwards [UnforcedLeray.B0012.coeFn_L0 v] with r hr
      rw [UnforcedLeray.Cons.G3b.generatorL0_eq_L0Fun]
      exact hr.symm
    have hgenLp : MemLp (generatorL0 p) 2 UnforcedLeray.B0010.xGMeasure :=
      (Lp.memLp (UnforcedLeray.B0012.L0 v)).ae_eq hgenAe.symm
    have hgenMeas : AEStronglyMeasurable (generatorL0 p) (volume.restrict (Ioi (0 : ℝ))) :=
      (UnforcedLeray.B0012.memXG_coe (UnforcedLeray.B0012.L0 v)).1.congr
        (UnforcedLeray.B0012.restrict_ac.ae_le hgenAe.symm)
    have hgen : MemXG (generatorL0 p) := UnforcedLeray.Cons.G3b.memXG_of_memLp hgenMeas hgenLp
    have hpRep : (UnforcedLeray.Cons.G3b.memLp_of_memXG hp).toLp p = v := by
      apply Lp.ext
      filter_upwards [(UnforcedLeray.Cons.G3b.memLp_of_memXG hp).coeFn_toLp] with r hr
      exact hr
    have hgenRep : (UnforcedLeray.Cons.G3b.memLp_of_memXG hgen).toLp (generatorL0 p) =
        UnforcedLeray.Planar.L0 v := by
      apply Lp.ext
      filter_upwards [(UnforcedLeray.Cons.G3b.memLp_of_memXG hgen).coeFn_toLp,
        UnforcedLeray.B0012.coeFn_L0 v] with r hr₁ hr₂
      rw [hr₁, UnforcedLeray.Cons.G3b.generatorL0_eq_L0Fun]
      exact hr₂.symm
    have hleft := hP.adjoint.left_eigen p hp
    rw [UnforcedLeray.Cons.G3b.gaussianPairing_eq_inner hp hP.adjoint.memXG,
      UnforcedLeray.Cons.G3b.gaussianPairing_eq_inner hgen hP.adjoint.memXG,
      hgenRep, hpRep] at hleft
    exact hleft
  have hadj_P : ContinuousLinearMap.adjoint UnforcedLeray.Planar.L0 qdag_P =
      (starRingEnd ℂ) (UnforcedLeray.Cons.G3b.lamMode c) • qdag_P := by
    apply ext_inner_right ℂ
    intro v
    rw [ContinuousLinearMap.adjoint_inner_left, inner_smul_left, starRingEnd_self_apply,
      hL_adj v, hlam]
  obtain ⟨ν_c, hν_c⟩ := UnforcedLeray.Short.PartI.adjoint_eigenvector_unique hSeed0
    (fun f => rfl) hadj_P
  have hnorm_P : inner ℂ qdag_P q_P = 1 := by
    rw [← UnforcedLeray.Cons.G3b.gaussianPairing_eq_inner hP.eigenpair.memXG hP.adjoint.memXG]
    exact hP.adjoint.normalized
  have hνμ : (starRingEnd ℂ) ν_c * μ = 1 := by
    have h1 := hnorm_P
    rw [hν_c, hμ, inner_smul_left, inner_smul_right,
      UnforcedLeray.Cons.G3b.inner_qdagMode_qMode hF, mul_one] at h1
    exact h1
  have hP_proj : UnforcedLeray.Infra.Dunford.rankOneProj (innerSL ℂ qdag_P) q_P =
      UnforcedLeray.Infra.Dunford.rankOneProj (innerSL ℂ (UnforcedLeray.Cons.G3b.qdagMode hF))
        (UnforcedLeray.Cons.G3b.qMode hF) := by
    ext x
    rw [UnforcedLeray.Infra.Dunford.rankOneProj_apply,
      UnforcedLeray.Infra.Dunford.rankOneProj_apply,
      innerSL_apply_apply, innerSL_apply_apply, hν_c, inner_smul_left, hμ, smul_smul]
    have hc : (starRingEnd ℂ) ν_c * inner ℂ (UnforcedLeray.Cons.G3b.qdagMode hF) x * μ =
        inner ℂ (UnforcedLeray.Cons.G3b.qdagMode hF) x := by
      linear_combination inner ℂ (UnforcedLeray.Cons.G3b.qdagMode hF) x * hνμ
    rw [hc]
  have hSeedP : UnforcedLeray.Short.PartI.IsSeedXG P.eigenvalue q_P (innerSL ℂ qdag_P) := by
    refine ⟨hP.eigenpair.re_pos, hq_P_ne, hq_P_eigen, ?_, ?_⟩
    · rw [innerSL_apply_apply]; exact hnorm_P
    · rw [hP_proj, hlam]; exact hSeed0.proj
  have hq0_dom := UnforcedLeray.Cons.G3b.qMode_mem_Ddomain hF
  have hq_P_dom : q_P ∈ UnforcedLeray.B0094.D.domain := by
    rw [hμ]
    exact Submodule.smul_mem _ μ hq0_dom
  refine ⟨hq_P_dom, hSeedP, ?_⟩
  -- Identify `seedKappa (innerSL ℂ qdag_P) q_P hq_P_dom = kapMode c F = P.kappa`
  have hsub_eq : (⟨q_P, hq_P_dom⟩ : UnforcedLeray.B0094.D.domain) =
      μ • ⟨UnforcedLeray.Cons.G3b.qMode hF, hq0_dom⟩ := Subtype.ext hμ
  have hsk_eq : UnforcedLeray.Short.PartI.seedKappa (innerSL ℂ qdag_P) q_P hq_P_dom =
      UnforcedLeray.Cons.G3b.kapMode c F := by
    unfold UnforcedLeray.Short.PartI.seedKappa
    rw [hsub_eq, LinearPMap.map_smul, innerSL_apply_apply, hν_c, inner_smul_left, inner_smul_right]
    have hkap0 := UnforcedLeray.Short.Spine.wholeLineModeKappa c F hF
    unfold UnforcedLeray.Short.PartI.seedKappa at hkap0
    rw [innerSL_apply_apply] at hkap0
    rw [hkap0]
    linear_combination UnforcedLeray.Cons.G3b.kapMode c F * hνμ
  -- Now show `P.kappa = kapMode c F` via pointwise equality of smooth eigenprofiles on `Ioi 0`
  have hmode_ae : P.mode =ᵐ[UnforcedLeray.B0010.xGMeasure]
      fun r => μ * UnforcedLeray.ComplexODEC.modeVort c F r := by
    have hcoe : (q_P : ℝ → ℂ) =ᵐ[UnforcedLeray.B0010.xGMeasure]
        ((μ • UnforcedLeray.Cons.G3b.qMode hF : UnforcedLeray.B0010.XG) : ℝ → ℂ) := by
      rw [hμ]
    filter_upwards [hm_q.coeFn_toLp, hcoe,
      Lp.coeFn_smul μ (UnforcedLeray.Cons.G3b.qMode hF),
      UnforcedLeray.Cons.G3b.coeFn_qMode hF] with r h1 h2 h3 h4
    rw [← h1, h2, h3, Pi.smul_apply, smul_eq_mul, h4]
  have hmode_eqOn : EqOn P.mode (fun r => μ * UnforcedLeray.ComplexODEC.modeVort c F r) (Ioi 0) :=
    UnforcedLeray.Short.Spine.aeEqOfContinuousOn_proof P.mode _
      hP.eigenpair.smooth.continuousOn
      (continuousOn_const.mul (UnforcedLeray.ComplexODEC.continuousOn_modeVort hF)) hmode_ae
  have hadj_ae_xG : P.adjointMode =ᵐ[UnforcedLeray.B0010.xGMeasure]
      fun r => ν_c * UnforcedLeray.Cons.C01.adjointMode c F r := by
    have hcoe : (qdag_P : ℝ → ℂ) =ᵐ[UnforcedLeray.B0010.xGMeasure]
        ((ν_c • UnforcedLeray.Cons.G3b.qdagMode hF : UnforcedLeray.B0010.XG) : ℝ → ℂ) := by
      rw [hν_c]
    filter_upwards [hm_qd.coeFn_toLp, hcoe,
      Lp.coeFn_smul ν_c (UnforcedLeray.Cons.G3b.qdagMode hF),
      (UnforcedLeray.Cons.G3b.memLp_of_memXG
        (UnforcedLeray.Cons.C01.memXG_adjointMode hF)).coeFn_toLp] with r h1 h2 h3 h4
    rw [← h1, h2, h3, Pi.smul_apply, smul_eq_mul]
    exact congrArg (ν_c * ·) h4
  have hadj_ae : P.adjointMode =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun r => ν_c * UnforcedLeray.Cons.C01.adjointMode c F r :=
    UnforcedLeray.B0012.restrict_ac.ae_le hadj_ae_xG
  have hPkap_eq : P.kappa = UnforcedLeray.Cons.G3b.kapMode c F := by
    unfold PlanarData.kappa UnforcedLeray.Cons.G3b.kapMode gaussianPairing
    have hae_int : (fun r : ℝ => oscillatorD P.mode r * conj (P.adjointMode r) *
          ((gaussianWeightInv r * r : ℝ) : ℂ)) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
        fun r : ℝ => ((starRingEnd ℂ) ν_c * μ) *
          (oscillatorD (UnforcedLeray.ComplexODEC.modeVort c F) r *
            conj (UnforcedLeray.Cons.C01.adjointMode c F r) *
            ((gaussianWeightInv r * r : ℝ) : ℂ)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi, hadj_ae] with r hr hadj_r
      rw [oscillatorD_const_mul_on_pos hmode_eqOn hr, hadj_r, map_mul]
      ring
    rw [integral_congr_ae hae_int, hνμ]
    simp only [one_mul]
  rw [hsk_eq, hPkap_eq]

/-- From `(IsPlanarReference P, HasCanonicalSolutionRep P)` alone, `V` is `C^∞` into all `X_{G,j}`
on `(0, ∞)` and satisfies:
* uniform zeroth-norm (`j = 0`) bounds WITHOUT `(1 + θ)` growth on `[b, ∞)`,
* polynomial `O((1 + θ)^4)` graph-norm bounds at order `j = 8` on `[b, ∞)`, and
* uniform compact-window `j = 0` and `j = 8` bounds on `[r_min, b]`. -/
theorem canonicalSolutionRep_smooth_and_bounds (P : PlanarData) (hP : IsPlanarReference P)
    (V : ℝ → UnforcedLeray.B0010.XG)
    (hVsol : UnforcedLeray.Short.PartI.IsCanonicalSolution V)
    (hVae : ∀ θ : ℝ, 0 < θ → P.canonical θ =ᵐ[UnforcedLeray.B0010.xGMeasure] (V θ : ℝ → ℂ)) :
    UnforcedLeray.Short.Spine.IsSmoothAllXGj V ∧
      ∃ b₀ : ℝ, 1 ≤ b₀ ∧ ∀ b : ℝ, b₀ ≤ b →
        (∃ M₀ M₈ : ℝ, 0 < M₀ ∧ 0 < M₈ ∧
          (∀ θ : ℝ, b ≤ θ →
            Real.exp (P.eigenvalue.re * θ) * θ ^ P.kappa.re * ‖V θ‖ ≤ M₀) ∧
          (∀ θ : ℝ, b ≤ θ →
            ∃ hj : V θ ∈ (UnforcedLeray.B0121.fracPow 8).domain,
              Real.exp (P.eigenvalue.re * θ) * θ ^ P.kappa.re *
                Real.sqrt (UnforcedLeray.B0121.graphNormSq 8 ⟨V θ, hj⟩) ≤
                M₈ * (1 + θ) ^ (4 : ℝ))) ∧
        (∀ r_min : ℝ, 0 < r_min → r_min ≤ b →
          ∃ M₀_r M₈_r : ℝ, 0 < M₀_r ∧ 0 < M₈_r ∧
            (∀ θ ∈ Icc r_min b, ‖V θ‖ ≤ M₀_r) ∧
            (∀ θ ∈ Icc r_min b,
              ∃ hj : V θ ∈ (UnforcedLeray.B0121.fracPow 8).domain,
                Real.sqrt (UnforcedLeray.B0121.graphNormSq 8 ⟨V θ, hj⟩) ≤ M₈_r)) := by
  -- 1. `IsSmoothAllXGj V` via the Spine mild/smoothing/bootstrap chain
  have hMild : UnforcedLeray.Short.Spine.IsMildOnPos V :=
    UnforcedLeray.Short.Spine.strongCanonicalIsMild V hVsol
  have hSmoothAll : UnforcedLeray.Short.Spine.IsSmoothAllXGj V :=
    UnforcedLeray.Short.Spine.strongBootstrap UnforcedLeray.Short.PartI.greenEllipticRegularity V
      (UnforcedLeray.Short.Spine.mildSpatialSmoothing
        UnforcedLeray.Short.PartI.greenEllipticRegularity V hMild)
      (UnforcedLeray.Short.Spine.mildIsStrong
        UnforcedLeray.Short.PartI.greenEllipticRegularity V hMild)
  refine ⟨hSmoothAll, ?_⟩
  -- 2. Identify `V` with Part I's unique canonical branch
  let hm_q := UnforcedLeray.Cons.G3b.memLp_of_memXG hP.eigenpair.memXG
  let q_P : UnforcedLeray.B0010.XG := hm_q.toLp P.mode
  let hm_qd := UnforcedLeray.Cons.G3b.memLp_of_memXG hP.adjoint.memXG
  let qdag_P : UnforcedLeray.B0010.XG := hm_qd.toLp P.adjointMode
  obtain ⟨hq_P, hSeedP, hkap_eq⟩ := planarReference_seed_and_kappa P hP
  obtain ⟨C₁, θ₁, hθ₁_pos, hasymP⟩ := hP.canonical.asymptotic
  have hAsymV : UnforcedLeray.Short.PartI.HasCanonicalAsymptotic P.eigenvalue
      (UnforcedLeray.Short.PartI.seedKappa (innerSL ℂ qdag_P) q_P hq_P) q_P V := by
    rw [hkap_eq]
    refine ⟨C₁, θ₁, hθ₁_pos, fun θ hθ => ?_⟩
    have hθ_pos : 0 < θ := lt_of_lt_of_le hθ₁_pos hθ
    set α : ℂ := Complex.exp (P.eigenvalue * (θ : ℂ)) * (θ : ℂ) ^ P.kappa
    have hsmul_eq : Complex.exp (P.eigenvalue * (θ : ℂ)) • (θ : ℂ) ^ P.kappa • V θ = α • V θ := by
      dsimp [α]; rw [mul_smul]
    rw [hsmul_eq]
    have hae_diff : (fun r => α * P.canonical θ r - P.mode r) =ᵐ[UnforcedLeray.B0010.xGMeasure]
        ((α • V θ - q_P : UnforcedLeray.B0010.XG) : ℝ → ℂ) := by
      filter_upwards [hVae θ hθ_pos, hm_q.coeFn_toLp,
        Lp.coeFn_sub (α • V θ) q_P, Lp.coeFn_smul α (V θ)] with r hV hq hsub hsm
      rw [hsub, Pi.sub_apply, hsm, Pi.smul_apply, smul_eq_mul, hV, hq]
    rw [← UnforcedLeray.Cons.G3b.gaussianNorm_eq_norm hae_diff]
    exact hasymP θ hθ
  obtain ⟨V_can, _, _, _, hUniq, hGraph⟩ :=
    canonicalBranch_unconditional P.eigenvalue q_P (innerSL ℂ qdag_P) hSeedP hq_P
  have hV_eq : ∀ θ : ℝ, 0 < θ → V θ = V_can θ := hUniq V hVsol hAsymV
  obtain ⟨C₈, b₈, hb₈_pos, hG₈⟩ := hGraph 8
  set b₀ : ℝ := max 1 (max θ₁ b₈)
  have hb₀_ge1 : 1 ≤ b₀ := le_max_left _ _
  refine ⟨b₀, hb₀_ge1, fun b hb => ⟨?_, ?_⟩⟩
  · -- Large-`θ` bounds (`b ≤ θ`)
    set M₀ : ℝ := ‖q_P‖ + max C₁ 0 + 1
    set M₈ : ℝ := |C₈| + 1
    have hM₀_pos : 0 < M₀ := by dsimp [M₀]; positivity
    have hM₈_pos : 0 < M₈ := by dsimp [M₈]; positivity
    refine ⟨M₀, M₈, hM₀_pos, hM₈_pos, ?_, ?_⟩
    · intro θ hθ_b
      have hθ_ge1 : 1 ≤ θ := le_trans hb₀_ge1 (le_trans hb hθ_b)
      have hθ_pos : 0 < θ := lt_of_lt_of_le zero_lt_one hθ_ge1
      have hθ_θ₁ : θ₁ ≤ θ :=
        le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_trans hb hθ_b)
      set α : ℂ := Complex.exp (P.eigenvalue * (θ : ℂ)) * (θ : ℂ) ^ P.kappa
      have hα_norm : ‖α‖ = Real.exp (P.eigenvalue.re * θ) * θ ^ P.kappa.re := by
        dsimp [α]
        rw [norm_mul, Complex.norm_exp, Complex.norm_cpow_eq_rpow_re_of_pos hθ_pos]
        simp
      have hae_diff : (fun r => α * P.canonical θ r - P.mode r) =ᵐ[UnforcedLeray.B0010.xGMeasure]
          ((α • V θ - q_P : UnforcedLeray.B0010.XG) : ℝ → ℂ) := by
        filter_upwards [hVae θ hθ_pos, hm_q.coeFn_toLp,
          Lp.coeFn_sub (α • V θ) q_P, Lp.coeFn_smul α (V θ)] with r hV hq hsub hsm
        rw [hsub, Pi.sub_apply, hsm, Pi.smul_apply, smul_eq_mul, hV, hq]
      have hrem : ‖α • V θ - q_P‖ ≤ C₁ / θ := by
        rw [← UnforcedLeray.Cons.G3b.gaussianNorm_eq_norm hae_diff]
        exact hasymP θ hθ_θ₁
      have hdiv : C₁ / θ ≤ max C₁ 0 := by
        calc C₁ / θ ≤ max C₁ 0 / θ := div_le_div_of_nonneg_right (le_max_left _ _) hθ_pos.le
          _ ≤ max C₁ 0 / 1 := div_le_div_of_nonneg_left (le_max_right _ _) zero_lt_one hθ_ge1
          _ = max C₁ 0 := div_one _
      have htri : ‖α • V θ‖ ≤ ‖α • V θ - q_P‖ + ‖q_P‖ := by
        simpa using norm_add_le (α • V θ - q_P) q_P
      rw [norm_smul, hα_norm] at htri
      dsimp [M₀]
      linarith
    · intro θ hθ_b
      have hθ_ge1 : 1 ≤ θ := le_trans hb₀_ge1 (le_trans hb hθ_b)
      have hθ_pos : 0 < θ := lt_of_lt_of_le zero_lt_one hθ_ge1
      have hθ_b₈ : b₈ ≤ θ :=
        le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_trans hb hθ_b)
      set α : ℂ := Complex.exp (P.eigenvalue * (θ : ℂ)) * (θ : ℂ) ^ P.kappa
      have hα_ne : α ≠ 0 := by
        dsimp [α]
        refine mul_ne_zero (Complex.exp_ne_zero _) ?_
        rw [Ne, Complex.cpow_eq_zero_iff]
        exact fun h => hθ_pos.ne' (Complex.ofReal_eq_zero.1 h.1)
      have hα_smul : Complex.exp (P.eigenvalue * (θ : ℂ)) • (θ : ℂ) ^ P.kappa • V θ =
          α • V θ := by dsimp [α]; rw [mul_smul]
      have hG₈_θ := hG₈ θ hθ_b₈
      rw [hkap_eq, ← hV_eq θ hθ_pos, hα_smul] at hG₈_θ
      obtain ⟨hj_can, hsq_can⟩ := hG₈_θ
      have hj_V : V θ ∈ (UnforcedLeray.B0121.fracPow 8).domain := by
        have h := Submodule.smul_mem (UnforcedLeray.B0121.fracPow 8).domain α⁻¹ hj_can
        rwa [inv_smul_smul₀ hα_ne] at h
      refine ⟨hj_V, ?_⟩
      have hα_norm : ‖α‖ = Real.exp (P.eigenvalue.re * θ) * θ ^ P.kappa.re := by
        dsimp [α]
        rw [norm_mul, Complex.norm_exp, Complex.norm_cpow_eq_rpow_re_of_pos hθ_pos]
        simp
      have hsmul_gn := UnforcedLeray.Short.PartI.graphNormSq_smul_mk 8 α (V θ) hj_V hj_can
      have hsqrt_le : Real.sqrt (UnforcedLeray.B0121.graphNormSq 8 ⟨α • V θ, hj_can⟩) ≤
          M₈ * (1 + θ) ^ (4 : ℝ) := by
        have hexp8 : ((8 : ℕ) : ℝ) / 2 = (4 : ℝ) := by norm_num
        rw [hexp8] at hsq_can
        have hsq_abs : (C₈ * (1 + θ) ^ (4 : ℝ)) ^ 2 = (|C₈| * (1 + θ) ^ (4 : ℝ)) ^ 2 := by
          rw [mul_pow, mul_pow, sq_abs]
        rw [hsq_abs] at hsq_can
        have hnn : 0 ≤ |C₈| * (1 + θ) ^ (4 : ℝ) := by positivity
        calc Real.sqrt (UnforcedLeray.B0121.graphNormSq 8 ⟨α • V θ, hj_can⟩)
            ≤ Real.sqrt ((|C₈| * (1 + θ) ^ (4 : ℝ)) ^ 2) := Real.sqrt_le_sqrt hsq_can
          _ = |C₈| * (1 + θ) ^ (4 : ℝ) := Real.sqrt_sq hnn
          _ ≤ M₈ * (1 + θ) ^ (4 : ℝ) :=
            mul_le_mul_of_nonneg_right (by dsimp [M₈]; linarith) (by positivity)
      rw [hsmul_gn, Real.sqrt_mul (sq_nonneg ‖α‖), Real.sqrt_sq (norm_nonneg α), hα_norm]
        at hsqrt_le
      exact hsqrt_le
  · -- Compact-window bounds (`θ ∈ Icc r_min b`) from `IsSmoothAllXGj V`
    intro r_min hr_pos hrb
    obtain ⟨U₈, hU₈_eq, hU₈_smooth⟩ := hSmoothAll 8
    have hK : IsCompact (Icc r_min b) := isCompact_Icc
    have hne : (Icc r_min b).Nonempty := ⟨r_min, le_rfl, hrb⟩
    have hsub : Icc r_min b ⊆ Ioi 0 := fun θ hθ => lt_of_lt_of_le hr_pos hθ.1
    have hcont0 : ContinuousOn (fun θ : ℝ => ‖V θ‖) (Icc r_min b) :=
      (hVsol.smooth.continuousOn.mono hsub).norm
    have hcont8 : ContinuousOn (fun θ : ℝ => Real.sqrt (‖V θ‖ ^ 2 + ‖U₈ θ‖ ^ 2)) (Icc r_min b) :=
      Continuous.comp_continuousOn Real.continuous_sqrt
        ((hcont0.pow 2).add (((hU₈_smooth.continuousOn.mono hsub).norm).pow 2))
    obtain ⟨θ₀, _, hmax0⟩ := hK.exists_isMaxOn hne hcont0
    obtain ⟨θ₈, _, hmax8⟩ := hK.exists_isMaxOn hne hcont8
    refine ⟨‖V θ₀‖ + 1, Real.sqrt (‖V θ₈‖ ^ 2 + ‖U₈ θ₈‖ ^ 2) + 1,
      by positivity, by positivity, fun θ hθ => ?_, fun θ hθ => ?_⟩
    · have hle : ‖V θ‖ ≤ ‖V θ₀‖ := hmax0 hθ
      linarith
    · have hθ_pos : 0 < θ := hsub hθ
      obtain ⟨hj_23, hID⟩ := hU₈_eq θ hθ_pos
      have hj_21 : V θ ∈ (UnforcedLeray.B0121.fracPow 8).domain :=
        (UnforcedLeray.B0123.XGj_eq_B0121 8).le hj_23
      refine ⟨hj_21, ?_⟩
      have hgn_eq : UnforcedLeray.B0121.graphNormSq 8 ⟨V θ, hj_21⟩ = ‖V θ‖ ^ 2 + ‖U₈ θ‖ ^ 2 := by
        rw [← UnforcedLeray.B0123.xgjNorm_sq_eq_graphNormSq 8 ⟨V θ, hj_23⟩]
        unfold UnforcedLeray.B0123.xgjNorm
        rw [Real.sq_sqrt (by positivity), hID]
      rw [hgn_eq]
      have hle : Real.sqrt (‖V θ‖ ^ 2 + ‖U₈ θ‖ ^ 2) ≤ Real.sqrt (‖V θ₈‖ ^ 2 + ‖U₈ θ₈‖ ^ 2) :=
        hmax8 hθ
      linarith

/-! ## 4. Unconditional exponential BUC train base-error bounds (`eq:ct-base-error`, SP 3162-3189) -/

theorem pow_mul_exp_neg_le (N : ℕ) {β u : ℝ} (hβ : 0 < β) (hu : 0 ≤ u) :
    u ^ N * Real.exp (-(β * u)) ≤ (N.factorial : ℝ) / β ^ N := by
  have hbu : 0 ≤ β * u := mul_nonneg hβ.le hu
  have hfac := Real.pow_div_factorial_le_exp (β * u) hbu N
  have hpos_exp : 0 < Real.exp (β * u) := Real.exp_pos _
  have hpos_fac : 0 < (N.factorial : ℝ) := Nat.cast_pos.2 (Nat.factorial_pos N)
  have hpos_βN : 0 < β ^ N := pow_pos hβ N
  rw [Real.exp_neg]
  have h1 : (β * u) ^ N * (Real.exp (β * u))⁻¹ ≤ (N.factorial : ℝ) := by
    rw [← div_eq_mul_inv, div_le_iff₀ hpos_exp, mul_comm (N.factorial : ℝ)]
    exact (div_le_iff₀ hpos_fac).1 hfac
  rw [mul_pow, mul_assoc] at h1
  exact (le_div_iff₀' hpos_βN).2 h1

theorem one_add_rpow_four_mul_exp_le {a₀ u : ℝ} (ha₀ : 0 < a₀) (hu : 0 ≤ u) :
    u * (1 + u) ^ (4 : ℝ) * Real.exp (-2 * a₀ * u) ≤
      ((16 : ℝ) * (Nat.factorial 1 : ℝ) / a₀ ^ 1 +
        (16 : ℝ) * (Nat.factorial 5 : ℝ) / a₀ ^ 5) * Real.exp (-a₀ * u) := by
  have h4 : (1 + u) ^ (4 : ℝ) = (1 + u) ^ (4 : ℕ) := Real.rpow_natCast (1 + u) 4
  have hexp_split : Real.exp (-2 * a₀ * u) = Real.exp (-(a₀ * u)) * Real.exp (-a₀ * u) := by
    rw [← Real.exp_add]; congr 1; ring
  have hpoly : u * (1 + u) ^ (4 : ℕ) ≤ 16 * u ^ 1 + 16 * u ^ 5 := by
    by_cases hu1 : u ≤ 1
    · have hle2 : (1 + u) ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
      nlinarith [pow_nonneg hu 5]
    · have hu1' : 1 < u := lt_of_not_ge hu1
      have hle2u : (1 + u) ^ 4 ≤ (2 * u) ^ 4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
      have hmul := mul_le_mul_of_nonneg_left hle2u hu
      nlinarith
  have hb1 := pow_mul_exp_neg_le 1 ha₀ hu
  have hb5 := pow_mul_exp_neg_le 5 ha₀ hu
  rw [h4, hexp_split, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
  calc u * (1 + u) ^ 4 * Real.exp (-(a₀ * u))
      ≤ (16 * u ^ 1 + 16 * u ^ 5) * Real.exp (-(a₀ * u)) :=
        mul_le_mul_of_nonneg_right hpoly (Real.exp_nonneg _)
    _ = 16 * (u ^ 1 * Real.exp (-(a₀ * u))) + 16 * (u ^ 5 * Real.exp (-(a₀ * u))) := by ring
    _ ≤ 16 * ((Nat.factorial 1 : ℝ) / a₀ ^ 1) + 16 * ((Nat.factorial 5 : ℝ) / a₀ ^ 5) := by
        linarith
    _ = 16 * (Nat.factorial 1 : ℝ) / a₀ ^ 1 + 16 * (Nat.factorial 5 : ℝ) / a₀ ^ 5 := by ring

theorem exists_one_add_rpow_four_mul_exp_le {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∃ K_abs : ℝ, 0 < K_abs ∧ ∀ u : ℝ, 0 ≤ u →
      u * (1 + u) ^ (4 : ℝ) * Real.exp (-2 * a₀ * u) ≤ K_abs * Real.exp (-a₀ * u) :=
  ⟨(16 : ℝ) * (Nat.factorial 1 : ℝ) / a₀ ^ 1 +
    (16 : ℝ) * (Nat.factorial 5 : ℝ) / a₀ ^ 5, by positivity,
    fun _ hu => one_add_rpow_four_mul_exp_le ha₀ hu⟩

private theorem le_one_add_of_sq_le {Y K : ℝ} (_hY : 0 ≤ Y) (h : Y ^ 2 ≤ K) : Y ≤ 1 + K := by
  nlinarith [sq_nonneg (Y - 1)]

/-- Unconditional exponential bound for `movingTrainV tr s y k - Train.datum d y k` (`eq:ct-base-error`
velocity part, SP 3164-3171): valid uniformly on every window `0 ≤ s` with `a(s) ≤ c^2`. -/
theorem movingTrainV_sub_datum_exp_bound :
    ∃ C_V a_V ν_V : ℝ, 0 < C_V ∧ 0 < a_V ∧ 0 < ν_V ∧
      ∀ ν ∈ Ioc 0 ν_V,
        ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
          UnforcedLeray.Short.PartI.IsBUCTrain tr →
          ∀ s : ℝ, 0 ≤ s → clockA ν s ≤ (ν ^ (-2 : ℝ)) ^ 2 →
          ∀ y : ℝ × ℝ, ∀ k : Fin 2,
            let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν s)
            |movingTrainV tr s y k - UnforcedLeray.Train.datum d y k| ≤
              C_V * ν ^ 3 * Real.exp (-2 * a_V * clockTheta ν s / ν ^ 3) := by
  obtain ⟨C0, β0, N0, hC0, hβ0, hN0, hbd⟩ :=
    UnforcedLeray.Short.PartI.trainComparison_proof 2 (by norm_num) 0
  obtain ⟨a_V, haV_eq⟩ : ∃ a : ℝ, a = β0 / 4 := ⟨_, rfl⟩
  have haV : 0 < a_V := by rw [haV_eq]; positivity
  obtain ⟨C_V, hCV_eq⟩ : ∃ C : ℝ, C = C0 * ((Nat.factorial 1 : ℝ) / (β0 / 2) ^ 1) + 1 := ⟨_, rfl⟩
  have hCV : 0 < C_V := by rw [hCV_eq]; positivity
  refine ⟨C_V, a_V, min 1 N0, hCV, haV, lt_min zero_lt_one hN0,
    fun ν hν tr hbuc s hs hac y k => ?_⟩
  intro d
  have hν_pos : 0 < ν := hν.1
  have hν_N0 : ν ≤ N0 := hν.2.trans (min_le_right _ _)
  have ha1 : 1 ≤ clockA ν s := by unfold clockA; nlinarith [hs]
  have ha0 : 0 < clockA ν s := lt_of_lt_of_le zero_lt_one ha1
  have hbj := (hbd ν hν_pos hν_N0 tr hbuc s hs hac).2
  let z : ℝ × ℝ := (Real.sqrt (clockA ν s) * y.1, Real.sqrt (clockA ν s) * y.2)
  have hM : 0 ≤ C0 * ν⁻¹ * clockA ν s ^ (-((5 + ((0 : ℕ) : ℝ)) / 2)) *
      Real.exp (-(β0 * (ν ^ (-2 : ℝ)) ^ 2 / clockA ν s)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC0.le (inv_nonneg.2 hν_pos.le))
      (Real.rpow_nonneg ha0.le _)) (Real.exp_nonneg _)
  have hpt := UnforcedLeray.B0277.norm_le_of_supNormD_le hM hbj z
  rw [norm_iteratedFDeriv_zero, Nat.cast_zero] at hpt
  have hcomp_le : |tr.v s z k - UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) s z k| ≤
      ‖tr.v s z - UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) s z‖ := by
    rw [← Real.norm_eq_abs]
    exact PiLp.norm_apply_le (tr.v s z - UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) s z) k
  have hdiff_eq : movingTrainV tr s y k - UnforcedLeray.Train.datum d y k =
      clockA ν s ^ (3 / 2 : ℝ) *
        (tr.v s z k - UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) s z k) := by
    rw [mul_sub, movingTrainV_Vc_eq_datum hν_pos hs y k]
    rfl
  have hd_sq : (ν ^ (-2 : ℝ)) ^ 2 / clockA ν s = clockTheta ν s / ν ^ 3 := by
    have hd_cell : dOfTheta ν (clockTheta ν s) = d := dOfTheta_eq_cellLen hν_pos ha0
    have hθ_pos : 0 < clockTheta ν s := by unfold clockTheta; positivity
    have h1 := dOfTheta_sq hν_pos hθ_pos.le
    rw [hd_cell] at h1
    dsimp [d, cellLen] at h1
    rwa [div_pow, Real.sq_sqrt ha0.le] at h1
  have ha_pow : clockA ν s ^ (3 / 2 : ℝ) * (ν⁻¹ * clockA ν s ^ (-((5 + (0 : ℝ)) / 2))) =
      clockTheta ν s := by
    have h1 : clockA ν s ^ (3 / 2 : ℝ) * clockA ν s ^ (-((5 + (0 : ℝ)) / 2)) =
        (clockA ν s)⁻¹ := by
      rw [← Real.rpow_add ha0, ← Real.rpow_neg_one]
      congr 1; norm_num
    unfold clockTheta
    rw [mul_inv]
    linear_combination ν⁻¹ * h1
  obtain ⟨u, hu_eq⟩ : ∃ u : ℝ, u = clockTheta ν s / ν ^ 3 := ⟨_, rfl⟩
  have hu_nn : 0 ≤ u := by rw [hu_eq]; unfold clockTheta; positivity
  have hθ_u : C0 * clockTheta ν s = C0 * ν ^ 3 * u := by
    rw [hu_eq]; field_simp [hν_pos.ne']
  have hexp_eq : Real.exp (-(β0 * (ν ^ (-2 : ℝ)) ^ 2 / clockA ν s)) =
      Real.exp (-((β0 / 2) * u)) * Real.exp (-2 * a_V * clockTheta ν s / ν ^ 3) := by
    rw [mul_div_assoc, hd_sq, ← Real.exp_add, hu_eq, haV_eq]
    congr 1; ring
  have hpow1 := pow_mul_exp_neg_le 1 (by positivity : 0 < β0 / 2) hu_nn
  rw [pow_one] at hpow1
  rw [hdiff_eq, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ha0 _)]
  calc clockA ν s ^ (3 / 2 : ℝ) * |tr.v s z k - UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) s z k|
      ≤ clockA ν s ^ (3 / 2 : ℝ) *
          (C0 * ν⁻¹ * clockA ν s ^ (-((5 + (0 : ℝ)) / 2)) *
            Real.exp (-(β0 * (ν ^ (-2 : ℝ)) ^ 2 / clockA ν s))) :=
        mul_le_mul_of_nonneg_left (hcomp_le.trans hpt) (Real.rpow_nonneg ha0.le _)
    _ = (C0 * clockTheta ν s) * Real.exp (-(β0 * (ν ^ (-2 : ℝ)) ^ 2 / clockA ν s)) := by
        linear_combination C0 * Real.exp (-(β0 * (ν ^ (-2 : ℝ)) ^ 2 / clockA ν s)) * ha_pow
    _ = C0 * ν ^ 3 * (u * Real.exp (-((β0 / 2) * u))) *
          Real.exp (-2 * a_V * clockTheta ν s / ν ^ 3) := by
        rw [hθ_u, hexp_eq]; ring
    _ ≤ C_V * ν ^ 3 * Real.exp (-2 * a_V * clockTheta ν s / ν ^ 3) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
        have hstep : C0 * (u * Real.exp (-((β0 / 2) * u))) ≤ C_V := by
          rw [hCV_eq]
          linarith [mul_le_mul_of_nonneg_left hpow1 hC0.le]
        calc C0 * ν ^ 3 * (u * Real.exp (-((β0 / 2) * u)))
            = (C0 * (u * Real.exp (-((β0 / 2) * u)))) * ν ^ 3 := by ring
          _ ≤ C_V * ν ^ 3 := mul_le_mul_of_nonneg_right hstep (pow_nonneg hν_pos.le 3)

private theorem vort_grad_alg {k_w Np Mx M_deg : ℕ}
    (hMx : Mx = 3 * Np + 2 * k_w) (hM_deg : M_deg = 12 + 8 * k_w + Mx)
    {a c x u_d R_inv s w jbv L D F F1 F2 Cm bm Cp G Qw Kx C_E a_E θ ν : ℝ}
    (hν0 : 0 < ν) (hx_eq : x = ν⁻¹) (ha1 : 1 ≤ a) (hx1 : 1 ≤ x)
    (hs0 : 0 ≤ s) (hjb0 : 0 ≤ jbv) (hL0 : 0 ≤ L) (hD0 : 0 ≤ D)
    (hF0 : 0 ≤ F) (hF2_0 : 0 ≤ F2)
    (hR1 : 1 ≤ R_inv) (hud0 : 0 ≤ u_d) (hCm : 0 < Cm) (hbm : 0 < bm)
    (hx_le : x ≤ R_inv * u_d) (ha_le : a ≤ R_inv * x) (hs_le : 1 + s ≤ 2 * R_inv * x ^ 2)
    (hc_eq : c = x ^ 2)
    (hQw : Qw = |Cp| * (2 * R_inv) ^ Np + |G| * R_inv ^ (2 * k_w))
    (hKx : Kx = 4 * 2 ^ (2 * k_w) * Qw * Cm * R_inv ^ (5 + M_deg))
    (hCE : C_E = 1 + Kx * ((M_deg.factorial : ℝ) / (bm / 2) ^ M_deg))
    (haE : a_E = bm / 8) (hu_d : u_d = θ / ν ^ 3)
    (hL_le : L ≤ (a ^ 2 * Real.sqrt a) * (jbv ^ k_w * D))
    (hjb_le : jbv ≤ (1 + c ^ 2) * (1 + w)) (hw0 : 0 ≤ w)
    (hD_le : D ≤ 2 * F) (hF_tri : F ≤ F1 + F2)
    (hF_sup : F ≤ Cm * x * Real.exp (-(bm * u_d)))
    (hraw1 : (1 + w) ^ (2 * k_w) * F1 ≤ Cp * x ^ Np * (1 + s) ^ Np)
    (hraw2 : (1 + w / a) ^ (2 * k_w) * F2 ≤ G * (a ^ (3 / 2 : ℝ) * Real.sqrt a ^ 2)⁻¹) :
    L ≤ C_E * ν ^ 3 * Real.exp (-2 * a_E * θ / ν ^ 3) := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hx0 : 0 ≤ x := zero_le_one.trans hx1
  have hR0 : 0 ≤ R_inv := zero_le_one.trans hR1
  have hQw0 : 0 ≤ Qw := by rw [hQw]; positivity
  have hKx0 : 0 ≤ Kx := by rw [hKx]; positivity
  have hW1 : (1 + w) ^ (2 * k_w) * F1 ≤ |Cp| * (2 * R_inv) ^ Np * x ^ Mx := by
    have hpow_s : (1 + s) ^ Np ≤ (2 * R_inv * x ^ 2) ^ Np :=
      pow_le_pow_left₀ (by linarith) hs_le Np
    have hx_pow : x ^ (3 * Np) ≤ x ^ Mx := pow_le_pow_right₀ hx1 (by rw [hMx]; omega)
    calc (1 + w) ^ (2 * k_w) * F1
        ≤ Cp * x ^ Np * (1 + s) ^ Np := hraw1
      _ = Cp * (x ^ Np * (1 + s) ^ Np) := by ring
      _ ≤ |Cp| * (x ^ Np * (1 + s) ^ Np) :=
          mul_le_mul_of_nonneg_right (le_abs_self Cp)
            (mul_nonneg (pow_nonneg hx0 Np) (pow_nonneg (by linarith) Np))
      _ ≤ |Cp| * (x ^ Np * (2 * R_inv * x ^ 2) ^ Np) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hpow_s (pow_nonneg hx0 Np)) (abs_nonneg _)
      _ = |Cp| * (2 * R_inv) ^ Np * x ^ (3 * Np) := by ring
      _ ≤ |Cp| * (2 * R_inv) ^ Np * x ^ Mx :=
          mul_le_mul_of_nonneg_left hx_pow (by positivity)
  have hW2 : (1 + w) ^ (2 * k_w) * F2 ≤ |G| * R_inv ^ (2 * k_w) * x ^ Mx := by
    have hq1 : (a ^ (3 / 2 : ℝ) * Real.sqrt a ^ 2)⁻¹ ≤ 1 := by
      apply inv_le_one_of_one_le₀
      exact one_le_mul_of_one_le_of_one_le (Real.one_le_rpow ha1 (by norm_num))
        (one_le_pow₀ ((Real.one_le_sqrt).mpr ha1))
    have hq0 : 0 ≤ (a ^ (3 / 2 : ℝ) * Real.sqrt a ^ 2)⁻¹ :=
      inv_nonneg.2 (mul_nonneg (Real.rpow_nonneg ha0.le _) (pow_nonneg (Real.sqrt_nonneg _) 2))
    have hsub : 1 + w ≤ a * (1 + w / a) := by
      have e : a * (1 + w / a) = a + w := by field_simp [ha0.ne']
      linarith
    have hpw : (1 + w) ^ (2 * k_w) ≤ a ^ (2 * k_w) * (1 + w / a) ^ (2 * k_w) := by
      calc (1 + w) ^ (2 * k_w) ≤ (a * (1 + w / a)) ^ (2 * k_w) :=
            pow_le_pow_left₀ (by linarith) hsub _
        _ = a ^ (2 * k_w) * (1 + w / a) ^ (2 * k_w) := mul_pow _ _ _
    have ha_pow : a ^ (2 * k_w) ≤ R_inv ^ (2 * k_w) * x ^ Mx := by
      calc a ^ (2 * k_w) ≤ (R_inv * x) ^ (2 * k_w) := pow_le_pow_left₀ ha0.le ha_le _
        _ = R_inv ^ (2 * k_w) * x ^ (2 * k_w) := mul_pow _ _ _
        _ ≤ R_inv ^ (2 * k_w) * x ^ Mx :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx1 (by rw [hMx]; omega)) (by positivity)
    have hGq : G * (a ^ (3 / 2 : ℝ) * Real.sqrt a ^ 2)⁻¹ ≤ |G| := by
      calc G * (a ^ (3 / 2 : ℝ) * Real.sqrt a ^ 2)⁻¹
          ≤ |G| * (a ^ (3 / 2 : ℝ) * Real.sqrt a ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right (le_abs_self G) hq0
        _ ≤ |G| * 1 := mul_le_mul_of_nonneg_left hq1 (abs_nonneg G)
        _ = |G| := mul_one _
    calc (1 + w) ^ (2 * k_w) * F2
        ≤ (a ^ (2 * k_w) * (1 + w / a) ^ (2 * k_w)) * F2 :=
          mul_le_mul_of_nonneg_right hpw hF2_0
      _ = a ^ (2 * k_w) * ((1 + w / a) ^ (2 * k_w) * F2) := by ring
      _ ≤ a ^ (2 * k_w) * |G| :=
          mul_le_mul_of_nonneg_left (hraw2.trans hGq) (pow_nonneg ha0.le _)
      _ ≤ (R_inv ^ (2 * k_w) * x ^ Mx) * |G| :=
          mul_le_mul_of_nonneg_right ha_pow (abs_nonneg G)
      _ = |G| * R_inv ^ (2 * k_w) * x ^ Mx := by ring
  have hW : (1 + w) ^ (2 * k_w) * F ≤ Qw * x ^ Mx := by
    calc (1 + w) ^ (2 * k_w) * F
        ≤ (1 + w) ^ (2 * k_w) * (F1 + F2) :=
          mul_le_mul_of_nonneg_left hF_tri (pow_nonneg (by linarith) _)
      _ = (1 + w) ^ (2 * k_w) * F1 + (1 + w) ^ (2 * k_w) * F2 := mul_add _ _ _
      _ ≤ |Cp| * (2 * R_inv) ^ Np * x ^ Mx + |G| * R_inv ^ (2 * k_w) * x ^ Mx :=
          add_le_add hW1 hW2
      _ = Qw * x ^ Mx := by rw [hQw]; ring
  have hc2k : (1 + c ^ 2) ^ (2 * k_w) ≤ 2 ^ (2 * k_w) * x ^ (8 * k_w) := by
    have hc2 : c ^ 2 = x ^ 4 := by rw [hc_eq]; ring
    have hc1 : 1 ≤ c ^ 2 := by rw [hc2]; exact one_le_pow₀ hx1
    calc (1 + c ^ 2) ^ (2 * k_w) ≤ (2 * c ^ 2) ^ (2 * k_w) :=
          pow_le_pow_left₀ (by linarith) (by linarith) _
      _ = 2 ^ (2 * k_w) * x ^ (8 * k_w) := by rw [mul_pow, hc2]; ring
  have ha5_le : (a ^ 2 * Real.sqrt a) ^ 2 ≤ R_inv ^ 5 * x ^ 5 := by
    have hsq : (a ^ 2 * Real.sqrt a) ^ 2 = a ^ 5 := by
      calc (a ^ 2 * Real.sqrt a) ^ 2 = a ^ 4 * (Real.sqrt a) ^ 2 := by ring
        _ = a ^ 4 * a := by rw [Real.sq_sqrt ha0.le]
        _ = a ^ 5 := by ring
    rw [hsq]
    calc a ^ 5 ≤ (R_inv * x) ^ 5 := pow_le_pow_left₀ ha0.le ha_le 5
      _ = R_inv ^ 5 * x ^ 5 := mul_pow _ _ _
  have hX2 : (jbv ^ k_w * D) ^ 2 ≤
      4 * 2 ^ (2 * k_w) * Qw * Cm * x ^ (8 * k_w + Mx + 1) * Real.exp (-(bm * u_d)) := by
    have hjbk : jbv ^ k_w ≤ (1 + c ^ 2) ^ k_w * (1 + w) ^ k_w := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ hjb0 hjb_le k_w
    have h1 : jbv ^ k_w * D ≤ ((1 + c ^ 2) ^ k_w * (1 + w) ^ k_w) * (2 * F) :=
      mul_le_mul hjbk hD_le hD0
        (mul_nonneg (pow_nonneg (by positivity) _) (pow_nonneg (by linarith) _))
    have h2 := pow_le_pow_left₀ (mul_nonneg (pow_nonneg hjb0 _) hD0) h1 2
    have h3 : (((1 + c ^ 2) ^ k_w * (1 + w) ^ k_w) * (2 * F)) ^ 2 =
        4 * (1 + c ^ 2) ^ (2 * k_w) * (((1 + w) ^ (2 * k_w) * F) * F) := by ring
    rw [h3] at h2
    have hprod_F : ((1 + w) ^ (2 * k_w) * F) * F ≤
        (Qw * x ^ Mx) * (Cm * x * Real.exp (-(bm * u_d))) :=
      mul_le_mul hW hF_sup hF0 (mul_nonneg hQw0 (pow_nonneg hx0 _))
    calc (jbv ^ k_w * D) ^ 2
        ≤ 4 * (1 + c ^ 2) ^ (2 * k_w) * (((1 + w) ^ (2 * k_w) * F) * F) := h2
      _ ≤ 4 * (2 ^ (2 * k_w) * x ^ (8 * k_w)) *
            ((Qw * x ^ Mx) * (Cm * x * Real.exp (-(bm * u_d)))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hc2k (by norm_num)) hprod_F
            (mul_nonneg (mul_nonneg (pow_nonneg (by linarith) _) hF0) hF0) (by positivity)
      _ = 4 * 2 ^ (2 * k_w) * Qw * Cm * x ^ (8 * k_w + Mx + 1) * Real.exp (-(bm * u_d)) := by
          ring
  have hY_sq : (L * x ^ 3 * Real.exp (2 * a_E * u_d)) ^ 2 ≤
      Kx * ((M_deg.factorial : ℝ) / (bm / 2) ^ M_deg) := by
    have hLx : L * x ^ 3 ≤ (a ^ 2 * Real.sqrt a) * (jbv ^ k_w * D) * x ^ 3 :=
      mul_le_mul_of_nonneg_right hL_le (pow_nonneg hx0 3)
    have hsq := pow_le_pow_left₀ (mul_nonneg hL0 (pow_nonneg hx0 3)) hLx 2
    have hx_deg : x ^ M_deg ≤ R_inv ^ M_deg * u_d ^ M_deg := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ hx0 hx_le M_deg
    have hexp_sq : (Real.exp (2 * a_E * u_d)) ^ 2 = Real.exp ((bm / 2) * u_d) := by
      rw [← Real.exp_nat_mul, haE]
      congr 1; push_cast; ring
    have hexp_prod : Real.exp (-(bm * u_d)) * Real.exp ((bm / 2) * u_d) =
        Real.exp (-((bm / 2) * u_d)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hpow_abs := pow_mul_exp_neg_le M_deg (by positivity : 0 < bm / 2) hud0
    calc (L * x ^ 3 * Real.exp (2 * a_E * u_d)) ^ 2
        = (L * x ^ 3) ^ 2 * (Real.exp (2 * a_E * u_d)) ^ 2 := by ring
      _ = (L * x ^ 3) ^ 2 * Real.exp ((bm / 2) * u_d) := by rw [hexp_sq]
      _ ≤ ((a ^ 2 * Real.sqrt a) * (jbv ^ k_w * D) * x ^ 3) ^ 2 *
            Real.exp ((bm / 2) * u_d) :=
          mul_le_mul_of_nonneg_right hsq (Real.exp_nonneg _)
      _ = ((a ^ 2 * Real.sqrt a) ^ 2 * (jbv ^ k_w * D) ^ 2 * x ^ 6) *
            Real.exp ((bm / 2) * u_d) := by ring
      _ ≤ ((R_inv ^ 5 * x ^ 5) *
            (4 * 2 ^ (2 * k_w) * Qw * Cm * x ^ (8 * k_w + Mx + 1) * Real.exp (-(bm * u_d))) *
            x ^ 6) * Real.exp ((bm / 2) * u_d) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul ha5_le hX2 (sq_nonneg _) (by positivity)) (pow_nonneg hx0 6))
            (Real.exp_nonneg _)
      _ = (4 * 2 ^ (2 * k_w) * Qw * Cm * R_inv ^ 5 * x ^ M_deg) *
            (Real.exp (-(bm * u_d)) * Real.exp ((bm / 2) * u_d)) := by
          rw [hM_deg]; ring
      _ = 4 * 2 ^ (2 * k_w) * Qw * Cm * R_inv ^ 5 * x ^ M_deg *
            Real.exp (-((bm / 2) * u_d)) := by rw [hexp_prod]
      _ ≤ 4 * 2 ^ (2 * k_w) * Qw * Cm * R_inv ^ 5 * (R_inv ^ M_deg * u_d ^ M_deg) *
            Real.exp (-((bm / 2) * u_d)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hx_deg (by positivity)) (Real.exp_nonneg _)
      _ = Kx * (u_d ^ M_deg * Real.exp (-((bm / 2) * u_d))) := by
          rw [hKx, pow_add]; ring
      _ ≤ Kx * ((M_deg.factorial : ℝ) / (bm / 2) ^ M_deg) :=
          mul_le_mul_of_nonneg_left hpow_abs hKx0
  have hY_nn : 0 ≤ L * x ^ 3 * Real.exp (2 * a_E * u_d) :=
    mul_nonneg (mul_nonneg hL0 (pow_nonneg hx0 3)) (Real.exp_nonneg _)
  have hY_le : L * x ^ 3 * Real.exp (2 * a_E * u_d) ≤ C_E := by
    rw [hCE]
    exact le_one_add_of_sq_le hY_nn hY_sq
  have hcancel : (L * x ^ 3 * Real.exp (2 * a_E * u_d)) *
      (ν ^ 3 * Real.exp (-2 * a_E * θ / ν ^ 3)) = L := by
    have hxν : x ^ 3 * ν ^ 3 = 1 := by rw [hx_eq]; field_simp [hν0.ne']
    have hexp_c : Real.exp (2 * a_E * u_d) * Real.exp (-2 * a_E * θ / ν ^ 3) = 1 := by
      rw [← Real.exp_add, hu_d]
      have h0 : 2 * a_E * (θ / ν ^ 3) + -2 * a_E * θ / ν ^ 3 = 0 := by ring
      rw [h0, Real.exp_zero]
    calc (L * x ^ 3 * Real.exp (2 * a_E * u_d)) * (ν ^ 3 * Real.exp (-2 * a_E * θ / ν ^ 3))
        = L * (x ^ 3 * ν ^ 3) * (Real.exp (2 * a_E * u_d) * Real.exp (-2 * a_E * θ / ν ^ 3)) := by
            ring
      _ = L := by rw [hxν, hexp_c, mul_one, mul_one]
  calc L = (L * x ^ 3 * Real.exp (2 * a_E * u_d)) *
          (ν ^ 3 * Real.exp (-2 * a_E * θ / ν ^ 3)) := hcancel.symm
    _ ≤ C_E * (ν ^ 3 * Real.exp (-2 * a_E * θ / ν ^ 3)) :=
        mul_le_mul_of_nonneg_right hY_le (mul_nonneg (pow_nonneg hν0.le 3) (Real.exp_nonneg _))
    _ = C_E * ν ^ 3 * Real.exp (-2 * a_E * θ / ν ^ 3) := by ring

/-- Unconditional weighted exponential bound for
`B0579.jb y ^ k_w * |movingTrainGradE tr s y k - B0579.pd k (Cyl.curl (Train.datum d)) y|`
on `B0579.cell d` (`eq:ct-base-error`, SP 3173-3189): the exponential rate `a_E > 0` depends ONLY
on `k_w` (independent of `r_min` and `b`), while `C_E` and `ν_E` may depend on `r_min > 0`. -/
theorem movingTrainGradE_sub_datum_exp_bound (k_w : ℕ) :
    ∃ a_E : ℝ, 0 < a_E ∧ ∀ r_min : ℝ, 0 < r_min →
      ∃ C_E ν_E : ℝ, 0 < C_E ∧ 0 < ν_E ∧
        ∀ ν ∈ Ioc 0 ν_E,
          ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
            UnforcedLeray.Short.PartI.IsBUCTrain tr →
            ∀ s : ℝ, s ∈ Icc (0 : ℝ) (clockAge ν r_min) →
            ∀ y ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)), ∀ k : Fin 2,
              let d := cellLen (ν ^ (-2 : ℝ)) (clockA ν s)
              B0579.jb y ^ k_w *
                |movingTrainGradE tr s y k -
                  B0579.pd k (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) y| ≤
                C_E * ν ^ 3 * Real.exp (-2 * a_E * clockTheta ν s / ν ^ 3) := by
  obtain ⟨Cm, bm, νm, hCm, hbm, hνm, hcm⟩ :=
    UnforcedLeray.Short.PartI.trainComparison_proof 2 (by norm_num) 2
  obtain ⟨Cp, Np, νp, hνp, hpl⟩ := trainWeightedJetPoly_uncond (2 * k_w) 2
  obtain ⟨G, hG⟩ := vcWeightedJet (2 * k_w) 2
  obtain ⟨a_E, haE_eq⟩ : ∃ a : ℝ, a = bm / 8 := ⟨_, rfl⟩
  have haE : 0 < a_E := by rw [haE_eq]; positivity
  refine ⟨a_E, haE, fun r_min hr_min => ?_⟩
  obtain ⟨R_inv, hR_eq⟩ : ∃ R : ℝ, R = max 1 r_min⁻¹ := ⟨_, rfl⟩
  have hR_ge1 : 1 ≤ R_inv := by rw [hR_eq]; exact le_max_left _ _
  have hr_inv_le : r_min⁻¹ ≤ R_inv := by rw [hR_eq]; exact le_max_right _ _
  obtain ⟨Mx, hMx⟩ : ∃ M : ℕ, M = 3 * Np + 2 * k_w := ⟨_, rfl⟩
  obtain ⟨M_deg, hM_deg⟩ : ∃ M : ℕ, M = 12 + 8 * k_w + Mx := ⟨_, rfl⟩
  obtain ⟨Qw, hQw⟩ : ∃ Q : ℝ, Q = |Cp| * (2 * R_inv) ^ Np + |G| * R_inv ^ (2 * k_w) := ⟨_, rfl⟩
  obtain ⟨Kx, hKx⟩ : ∃ K : ℝ, K = 4 * 2 ^ (2 * k_w) * Qw * Cm * R_inv ^ (5 + M_deg) := ⟨_, rfl⟩
  have hQw_nn : 0 ≤ Qw := by
    rw [hQw]
    have hR0 : 0 ≤ R_inv := zero_le_one.trans hR_ge1
    positivity
  have hKx_nn : 0 ≤ Kx := by
    rw [hKx]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hQw_nn) hCm.le)
      (pow_nonneg (zero_le_one.trans hR_ge1) _)
  obtain ⟨C_E, hCE⟩ : ∃ C : ℝ, C = 1 + Kx * ((M_deg.factorial : ℝ) / (bm / 2) ^ M_deg) := ⟨_, rfl⟩
  have hCE_pos : 0 < C_E := by
    rw [hCE]
    have hfac_nn : 0 ≤ Kx * ((M_deg.factorial : ℝ) / (bm / 2) ^ M_deg) :=
      mul_nonneg hKx_nn (div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by positivity) _))
    exact add_pos_of_pos_of_nonneg zero_lt_one hfac_nn
  refine ⟨C_E, min (min νm νp) (min 1 r_min), hCE_pos,
    lt_min (lt_min hνm hνp) (lt_min zero_lt_one hr_min), fun ν hν tr hbuc s hs y hy k => ?_⟩
  intro d
  have hν0 : 0 < ν := hν.1
  have hνm' : ν ≤ νm := hν.2.trans (le_trans (min_le_left _ _) (min_le_left _ _))
  have hνp' : ν ∈ Ioc 0 νp :=
    ⟨hν0, hν.2.trans (le_trans (min_le_left _ _) (min_le_right _ _))⟩
  have hν1 : ν ≤ 1 := hν.2.trans (le_trans (min_le_right _ _) (min_le_left _ _))
  have hνr : ν ≤ r_min := hν.2.trans (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨ha1, ha0, hθ_mem, hθ_pos, hd1, hac2⟩ := clockWindow_bounds hν0 hν1 hr_min hνr hs
  have hc_pos : 0 < vortC ν := Real.rpow_pos_of_pos hν0 _
  have hc_eq : vortC ν = (ν⁻¹) ^ 2 := vort_c_eq hν0
  obtain ⟨x, hx_eq⟩ : ∃ x : ℝ, x = ν⁻¹ := ⟨_, rfl⟩
  obtain ⟨a, ha_eq⟩ : ∃ a : ℝ, a = clockA ν s := ⟨_, rfl⟩
  have ha1' : 1 ≤ a := by rwa [ha_eq]
  have ha0' : 0 < a := by rwa [ha_eq]
  have hx1 : 1 ≤ x := by rw [hx_eq]; exact (one_le_inv₀ hν0).2 hν1
  have hx0 : 0 ≤ x := zero_le_one.trans hx1
  have hc_x2 : vortC ν = x ^ 2 := by rw [hc_eq, hx_eq]
  obtain ⟨u_d, hu_d⟩ : ∃ u : ℝ, u = clockTheta ν s / ν ^ 3 := ⟨_, rfl⟩
  have hud_ge1 : 1 ≤ u_d := by
    rw [hu_d, ← dOfTheta_sq hν0 hθ_pos.le]
    exact one_le_pow₀ hd1
  have hud_nn : 0 ≤ u_d := zero_le_one.trans hud_ge1
  have hx3_le : x ^ 3 ≤ R_inv * u_d := by
    have hx3 : x ^ 3 = (clockTheta ν s)⁻¹ * u_d := by
      rw [hx_eq, hu_d]
      field_simp [hν0.ne', hθ_pos.ne']
    rw [hx3]
    exact mul_le_mul_of_nonneg_right ((inv_anti₀ hr_min hθ_mem.1).trans hr_inv_le) hud_nn
  have hx_le : x ≤ R_inv * u_d := by
    have hx_le_x3 : x ≤ x ^ 3 := by
      calc x = x ^ 1 := (pow_one x).symm
        _ ≤ x ^ 3 := pow_le_pow_right₀ hx1 (by decide)
    exact hx_le_x3.trans hx3_le
  have ha_le_Rx : a ≤ R_inv * x := by
    have ha_inv : a = (clockTheta ν s)⁻¹ * x := by
      rw [ha_eq, hx_eq]
      unfold clockTheta
      field_simp [hν0.ne', ha0.ne']
    rw [ha_inv]
    exact mul_le_mul_of_nonneg_right ((inv_anti₀ hr_min hθ_mem.1).trans hr_inv_le) hx0
  have hs_le : 1 + s ≤ 2 * R_inv * x ^ 2 := by
    have hs_eq : s = a * x - x := by
      rw [ha_eq, hx_eq]
      unfold clockA
      field_simp [hν0.ne']
      ring
    have hs1 : s ≤ a * x := by
      rw [hs_eq]
      exact sub_le_self (a * x) hx0
    have hs2 : a * x ≤ R_inv * x ^ 2 := by
      calc a * x ≤ (R_inv * x) * x := mul_le_mul_of_nonneg_right ha_le_Rx hx0
        _ = R_inv * x ^ 2 := by ring
    have h1_le : 1 ≤ R_inv * x ^ 2 :=
      one_le_mul_of_one_le_of_one_le hR_ge1 (one_le_pow₀ hx1)
    calc 1 + s ≤ R_inv * x ^ 2 + R_inv * x ^ 2 := add_le_add h1_le (hs1.trans hs2)
      _ = 2 * R_inv * x ^ 2 := by ring
  let z0 : ℝ × ℝ := (Real.sqrt (clockA ν s) * y.1, Real.sqrt (clockA ν s) * y.2)
  have hf_smooth : ContDiff ℝ ∞ (tr.v s) := UnforcedLeray.B0238.contDiff_Vc tr hs.1
  have hg_smooth : ContDiff ℝ ∞ (UnforcedLeray.Train.Vc ν (vortC ν) s) :=
    UnforcedLeray.Short.Spine.vcReg_contDiff_Vc hc_pos ha0
  have hu_sm : ContDiff ℝ ∞ (fun z => tr.v s z - UnforcedLeray.Train.Vc ν (vortC ν) s z) :=
    hf_smooth.sub hg_smooth
  have hD_le := curlJetBound (fun z => tr.v s z - UnforcedLeray.Train.Vc ν (vortC ν) s z) hu_sm 1 z0
  have hF_tri :
      ‖iteratedFDeriv ℝ 2 (fun z => tr.v s z - UnforcedLeray.Train.Vc ν (vortC ν) s z) z0‖ ≤
        ‖iteratedFDeriv ℝ 2 (tr.v s) z0‖ +
          ‖iteratedFDeriv ℝ 2 (UnforcedLeray.Train.Vc ν (vortC ν) s) z0‖ := by
    have hA' : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) (tr.v s) := hf_smooth.of_le (by simp)
    have hB' : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) (UnforcedLeray.Train.Vc ν (vortC ν) s) :=
      hg_smooth.of_le (by simp)
    have hfn : iteratedFDeriv ℝ 2
        (fun z => tr.v s z - UnforcedLeray.Train.Vc ν (vortC ν) s z) z0 =
        iteratedFDeriv ℝ 2 (tr.v s) z0 -
          iteratedFDeriv ℝ 2 (UnforcedLeray.Train.Vc ν (vortC ν) s) z0 :=
      iteratedFDeriv_sub_apply hA'.contDiffAt hB'.contDiffAt
    rw [hfn]
    exact norm_sub_le _ _
  have hF_sup :
      ‖iteratedFDeriv ℝ 2 (fun z => tr.v s z - UnforcedLeray.Train.Vc ν (vortC ν) s z) z0‖ ≤
        Cm * x * Real.exp (-(bm * u_d)) := by
    have h := (hcm ν hν0 hνm' tr hbuc s hs.1 hac2).2
    have hM0 : 0 ≤ Cm * ν⁻¹ * (UnforcedLeray.Train.width ν s) ^ (-((5 + ((2 : ℕ) : ℝ)) / 2)) *
        Real.exp (-(bm * (UnforcedLeray.Short.PartI.trainPeriod 2 ν) ^ 2 /
          UnforcedLeray.Train.width ν s)) :=
      mul_nonneg (mul_nonneg (mul_nonneg hCm.le (inv_nonneg.2 hν0.le))
        (Real.rpow_nonneg ha0.le _)) (Real.exp_nonneg _)
    have hpt := UnforcedLeray.B0277.norm_le_of_supNormD_le hM0 h z0
    change ‖iteratedFDeriv ℝ 2 (fun z => tr.v s z - UnforcedLeray.Train.Vc ν (vortC ν) s z) z0‖ ≤
      Cm * ν⁻¹ * (clockA ν s) ^ (-((5 + ((2 : ℕ) : ℝ)) / 2)) *
        Real.exp (-(bm * (vortC ν) ^ 2 / clockA ν s)) at hpt
    rw [← hx_eq, ← ha_eq] at hpt
    have hc2_a : (vortC ν) ^ 2 / a = u_d := by
      rw [ha_eq, hu_d]
      have hd_cell : dOfTheta ν (clockTheta ν s) =
          cellLen (vortC ν) (clockA ν s) := dOfTheta_eq_cellLen hν0 ha0
      have h1 := dOfTheta_sq hν0 hθ_pos.le
      rw [hd_cell] at h1
      unfold cellLen at h1
      rwa [div_pow, Real.sq_sqrt ha0.le] at h1
    have ha_le1 : a ^ (-((5 + ((2 : ℕ) : ℝ)) / 2)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos ha1' (by norm_num)
    calc ‖iteratedFDeriv ℝ 2 (fun z => tr.v s z - UnforcedLeray.Train.Vc ν (vortC ν) s z) z0‖
        ≤ Cm * x * a ^ (-((5 + ((2 : ℕ) : ℝ)) / 2)) * Real.exp (-(bm * (vortC ν) ^ 2 / a)) := hpt
      _ = (Cm * x * Real.exp (-(bm * u_d))) * a ^ (-((5 + ((2 : ℕ) : ℝ)) / 2)) := by
          rw [mul_div_assoc, hc2_a]; ring
      _ ≤ (Cm * x * Real.exp (-(bm * u_d))) * 1 :=
          mul_le_mul_of_nonneg_left ha_le1 (by positivity)
      _ = Cm * x * Real.exp (-(bm * u_d)) := mul_one _
  have hraw1 : (1 + z0.2 ^ 2) ^ (2 * k_w) * ‖iteratedFDeriv ℝ 2 (tr.v s) z0‖ ≤
      Cp * x ^ Np * (1 + s) ^ Np := by
    rw [hx_eq]
    exact hpl ν hνp' tr hbuc s hs.1 z0
  have hraw2 : (1 + z0.2 ^ 2 / a) ^ (2 * k_w) *
      ‖iteratedFDeriv ℝ 2 (UnforcedLeray.Train.Vc ν (vortC ν) s) z0‖ ≤
      G * (a ^ (3 / 2 : ℝ) * Real.sqrt a ^ 2)⁻¹ := by
    rw [ha_eq]
    exact hG ν (vortC ν) s hν0 hc_pos hs.1 hac2 z0
  have hgrad_le_D :
      |movingTrainGradE tr s y k -
          B0579.pd k (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) y| ≤
        (a ^ 2 * Real.sqrt a) *
          ‖iteratedFDeriv ℝ 1
            (UnforcedLeray.Cyl.curl (fun z => tr.v s z - UnforcedLeray.Train.Vc ν (vortC ν) s z))
            z0‖ := by
    have hEc : UnforcedLeray.B0238.Ec tr s =
        fun z => UnforcedLeray.Cyl.curl (UnforcedLeray.Train.Vc ν (vortC ν) s) z +
          UnforcedLeray.Cyl.curl (fun z' => tr.v s z' - UnforcedLeray.Train.Vc ν (vortC ν) s z') z := by
      have hv : tr.v s = fun z => UnforcedLeray.Train.Vc ν (vortC ν) s z +
          (tr.v s z - UnforcedLeray.Train.Vc ν (vortC ν) s z) := by
        funext z; abel
      show UnforcedLeray.Cyl.curl (tr.v s) = _
      conv_lhs => rw [hv]
      exact curl_add_vort hg_smooth hu_sm
    have hsub_curl : UnforcedLeray.Cyl.curl
        (fun z => tr.v s z - UnforcedLeray.Train.Vc ν (vortC ν) s z) =
        UnforcedLeray.B0238.Ec tr s -
          UnforcedLeray.Cyl.curl (UnforcedLeray.Train.Vc ν (vortC ν) s) := by
      funext z
      show UnforcedLeray.Cyl.curl
          (fun z' => tr.v s z' - UnforcedLeray.Train.Vc ν (vortC ν) s z') z =
        UnforcedLeray.B0238.Ec tr s z -
          UnforcedLeray.Cyl.curl (UnforcedLeray.Train.Vc ν (vortC ν) s) z
      exact eq_sub_of_add_eq' (congrFun hEc z).symm
    have hpd_u : B0579.pd k (UnforcedLeray.Cyl.curl
          (fun z => tr.v s z - UnforcedLeray.Train.Vc ν (vortC ν) s z)) z0 =
        B0579.pd k (UnforcedLeray.B0238.Ec tr s) z0 -
          B0579.pd k (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.Vc ν (vortC ν) s)) z0 := by
      unfold B0579.pd
      rw [hsub_curl]
      have hd1' : DifferentiableAt ℝ (UnforcedLeray.B0238.Ec tr s) z0 :=
        ((curl_contDiff_vort hf_smooth).differentiable (by simp)).differentiableAt
      have hd2' : DifferentiableAt ℝ
          (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.Vc ν (vortC ν) s)) z0 :=
        ((curl_contDiff_vort hg_smooth).differentiable (by simp)).differentiableAt
      rw [fderiv_sub hd1' hd2', sub_apply]
    have hpow_a : (clockA ν s) ^ ((5 : ℝ) / 2) = a ^ 2 * Real.sqrt a := by
      rw [← ha_eq, Real.sqrt_eq_rpow, ← Real.rpow_natCast a 2, ← Real.rpow_add ha0']
      norm_num
    have hdiff_eq : movingTrainGradE tr s y k -
        B0579.pd k (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) y =
        (a ^ 2 * Real.sqrt a) * B0579.pd k (UnforcedLeray.Cyl.curl
          (fun z => tr.v s z - UnforcedLeray.Train.Vc ν (vortC ν) s z)) z0 := by
      rw [← hpow_a, hpd_u, mul_sub, movingTrainGradE_Vc_eq_pd_curl_datum hν0 hs.1 y k]
      rfl
    have hpd_le_D : |B0579.pd k (UnforcedLeray.Cyl.curl
          (fun z => tr.v s z - UnforcedLeray.Train.Vc ν (vortC ν) s z)) z0| ≤
        ‖iteratedFDeriv ℝ 1 (UnforcedLeray.Cyl.curl
          (fun z => tr.v s z - UnforcedLeray.Train.Vc ν (vortC ν) s z)) z0‖ := by
      unfold B0579.pd
      rw [norm_iteratedFDeriv_one, ← Real.norm_eq_abs]
      have hdir : ‖B0579.dir k‖ ≤ 1 := by fin_cases k <;> simp [B0579.dir]
      calc ‖fderiv ℝ (UnforcedLeray.Cyl.curl
              (fun z => tr.v s z - UnforcedLeray.Train.Vc ν (vortC ν) s z)) z0 (B0579.dir k)‖
          ≤ ‖fderiv ℝ (UnforcedLeray.Cyl.curl
              (fun z => tr.v s z - UnforcedLeray.Train.Vc ν (vortC ν) s z)) z0‖ *
              ‖B0579.dir k‖ :=
            (fderiv ℝ (UnforcedLeray.Cyl.curl
              (fun z => tr.v s z - UnforcedLeray.Train.Vc ν (vortC ν) s z)) z0).le_opNorm _
        _ ≤ ‖fderiv ℝ (UnforcedLeray.Cyl.curl
              (fun z => tr.v s z - UnforcedLeray.Train.Vc ν (vortC ν) s z)) z0‖ * 1 :=
            mul_le_mul_of_nonneg_left hdir (norm_nonneg _)
        _ = ‖fderiv ℝ (UnforcedLeray.Cyl.curl
              (fun z => tr.v s z - UnforcedLeray.Train.Vc ν (vortC ν) s z)) z0‖ := mul_one _
    rw [hdiff_eq, abs_mul, abs_of_pos (by positivity)]
    exact mul_le_mul_of_nonneg_left hpd_le_D (by positivity)
  have hjb_le : B0579.jb y ≤ (1 + (vortC ν) ^ 2) * (1 + z0.2 ^ 2) := by
    unfold B0579.jb
    exact vort_hjb ha1 rfl hy.1
  have hL_le : B0579.jb y ^ k_w *
      |movingTrainGradE tr s y k -
        B0579.pd k (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) y| ≤
      (a ^ 2 * Real.sqrt a) * (B0579.jb y ^ k_w *
        ‖iteratedFDeriv ℝ 1
          (UnforcedLeray.Cyl.curl (fun z => tr.v s z - UnforcedLeray.Train.Vc ν (vortC ν) s z))
          z0‖) := by
    calc B0579.jb y ^ k_w *
          |movingTrainGradE tr s y k -
            B0579.pd k (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) y|
        ≤ B0579.jb y ^ k_w * ((a ^ 2 * Real.sqrt a) *
            ‖iteratedFDeriv ℝ 1
              (UnforcedLeray.Cyl.curl (fun z => tr.v s z - UnforcedLeray.Train.Vc ν (vortC ν) s z))
              z0‖) :=
          mul_le_mul_of_nonneg_left hgrad_le_D (pow_nonneg (B0579.jb_pos y).le k_w)
      _ = (a ^ 2 * Real.sqrt a) * (B0579.jb y ^ k_w *
            ‖iteratedFDeriv ℝ 1
              (UnforcedLeray.Cyl.curl (fun z => tr.v s z - UnforcedLeray.Train.Vc ν (vortC ν) s z))
              z0‖) := by ring
  exact vort_grad_alg hMx hM_deg hν0 hx_eq ha1' hx1 hs.1 (B0579.jb_pos y).le
    (mul_nonneg (pow_nonneg (B0579.jb_pos y).le _) (abs_nonneg _))
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hR_ge1 hud_nn hCm hbm
    hx_le ha_le_Rx hs_le hc_x2 hQw hKx hCE haE_eq hu_d hL_le hjb_le (sq_nonneg _)
    hD_le hF_tri hF_sup hraw1 hraw2

/-! ## 5. Analytical leaves (`CanonicalColumnWeakEq`, `CanonicalGaussAndJetBound`) and train-defect assembly -/

/-- **Leaf 1 (`CanonicalColumnWeakEq`, SP 3130-3140)**:
Physical-cylinder Biot-Savart, `X_{m,c}` regularity/symmetry/time-continuity, and weak linearised
vorticity equation on `[0, clockAge ν r_min]` (moving-period commutation `eq:ct-moving-period` +
Reynolds cancellation of the moving cell seam) for a smooth canonical branch `V`. -/
def CanonicalColumnWeakEq : Prop :=
  ∀ (P : PlanarData), IsPlanarReference P →
    ∀ (V : ℝ → UnforcedLeray.B0010.XG),
      UnforcedLeray.Short.PartI.IsCanonicalSolution V →
      UnforcedLeray.Short.Spine.IsSmoothAllXGj V →
      (∀ θ : ℝ, 0 < θ → P.canonical θ =ᵐ[UnforcedLeray.B0010.xGMeasure] (V θ : ℝ → ℂ)) →
      ∀ (m : ℝ), 8 < m → ∀ (r_min : ℝ), 0 < r_min →
        ∀ (ν : ℝ), 0 < ν → ν ≤ min 1 r_min →
          ∀ (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))),
            UnforcedLeray.Short.PartI.IsBUCTrain tr →
            (∀ s ∈ Icc (0 : ℝ) (clockAge ν r_min),
              IsBiotSavart (ν ^ (-2 : ℝ)) (canonicalPhysColumn P ν s) (canonicalPhysVel P ν s) ∧
              MemLp (canonicalPhysResidual P tr s) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) ∧
              HasZeroCirculation (ν ^ (-2 : ℝ)) (canonicalPhysResidual P tr s) ∧
              IsCentrallyEven (canonicalPhysResidual P tr s) ∧
              Tendsto (fun s' => xNorm (ν ^ (-2 : ℝ)) m
                  (canonicalPhysResidual P tr s' - canonicalPhysResidual P tr s))
                (𝓝[Icc (0 : ℝ) (clockAge ν r_min)] s) (𝓝 0)) ∧
            (∀ φ, B0579.IsCylTest (ν ^ (-2 : ℝ)) φ → ∀ s ∈ Icc (0 : ℝ) (clockAge ν r_min),
              IntegrableOn (flowIntegrand tr (canonicalPhysColumn P ν s)
                  (canonicalPhysVel P ν s) s φ)
                (B0579.cell (ν ^ (-2 : ℝ))) ∧
              IntervalIntegrable (fun τ =>
                (∫ x in B0579.cell (ν ^ (-2 : ℝ)),
                  flowIntegrand tr (canonicalPhysColumn P ν τ) (canonicalPhysVel P ν τ) τ φ x) +
                (∫ x in B0579.cell (ν ^ (-2 : ℝ)),
                  canonicalPhysResidual P tr τ x * (φ x : ℂ))) volume 0 s ∧
              ∫ x in B0579.cell (ν ^ (-2 : ℝ)), canonicalPhysColumn P ν s x * (φ x : ℂ) =
                (∫ x in B0579.cell (ν ^ (-2 : ℝ)), preparedDatum P ν x * (φ x : ℂ)) +
                ∫ τ in (0 : ℝ)..s,
                  ((∫ x in B0579.cell (ν ^ (-2 : ℝ)),
                    flowIntegrand tr (canonicalPhysColumn P ν τ) (canonicalPhysVel P ν τ) τ φ x) +
                  (∫ x in B0579.cell (ν ^ (-2 : ℝ)),
                    canonicalPhysResidual P tr τ x * (φ x : ℂ))))

/-- **Leaf 2 (`CanonicalGaussAndJetBound`, SP 3141-3160, 3211-3214)**:
Pure `tr`-independent Gaussian-cylinder linearised Euler defect and periodic jet bounds for an
angular-two profile `f` representing `u ∈ X_{G,8}`:
* the even zero-mass zero-first-moment image error is `O(d⁻⁴) ‖u‖_{X_G}` (zeroth Gaussian norm ONLY)
  while cross-cell overlap is `O(exp(-2 a_g d²)) ‖u‖_{X_{G,8}}`;
* on `B0579.cell d` (`d ≥ 1`), `W = P_d (planarMode f)` has weighted gradient `jb^{k_w} ‖pdCx k W‖`
  and periodic Biot-Savart velocity `‖kerVelCx d W · k‖` controlled by `‖u‖_{X_{G,8}}`. -/
def CanonicalGaussAndJetBound : Prop :=
  ∀ (m : ℝ), 8 < m →
    let k_w : ℕ := Nat.ceil m + 2
    ∃ C_g a_g : ℝ, 0 < C_g ∧ 0 < a_g ∧
      ∀ (d : ℝ), 1 ≤ d →
        ∀ (f : Profile), MemXG f → ContDiffOn ℝ ∞ f (Ioi 0) →
          ∀ (u : UnforcedLeray.B0010.XG),
            f =ᵐ[UnforcedLeray.B0010.xGMeasure] (u : ℝ → ℂ) →
            ∀ (hu : u ∈ (UnforcedLeray.B0121.fracPow 8).domain),
              let W := periodizeC d (planarMode f)
              let G₈ := Real.sqrt (UnforcedLeray.B0121.graphNormSq 8 ⟨u, hu⟩)
              AEStronglyMeasurable
                (fun y => periodizeC d (movLPlanar (planarMode f)) y - movLGauss d W y)
                (B0579.cellMeasure d m) ∧
              xNorm d m (fun y => periodizeC d (movLPlanar (planarMode f)) y - movLGauss d W y) ≤
                ENNReal.ofReal (C_g * (d ^ (-4 : ℝ) * ‖u‖ + Real.exp (-2 * a_g * d ^ 2) * G₈)) ∧
              StronglyMeasurable W ∧
              (∀ k : Fin 2, StronglyMeasurable (pdCx k W)) ∧
              (∀ k : Fin 2, ∀ y ∈ B0579.cell d,
                B0579.jb y ^ k_w * ‖pdCx k W y‖ ≤ C_g * G₈ ∧
                  ‖kerVelCx d W y k‖ ≤ C_g * G₈)

private theorem exp_neg_two_mono {a₁ a₂ θ ν : ℝ}
    (hle : a₁ ≤ a₂) (hν : 0 < ν) (hθ : 0 ≤ θ) :
    Real.exp (-2 * a₂ * θ / ν ^ 3) ≤ Real.exp (-2 * a₁ * θ / ν ^ 3) := by
  apply Real.exp_le_exp.2
  have hquot : 0 ≤ θ / ν ^ 3 := div_nonneg hθ (pow_pos hν 3).le
  have hmul : 2 * a₁ * (θ / ν ^ 3) ≤ 2 * a₂ * (θ / ν ^ 3) :=
    mul_le_mul_of_nonneg_right (by linarith) hquot
  have e1 : -2 * a₂ * θ / ν ^ 3 = -(2 * a₂ * (θ / ν ^ 3)) := by ring
  have e2 : -2 * a₁ * θ / ν ^ 3 = -(2 * a₁ * (θ / ν ^ 3)) := by ring
  linarith

private theorem norm_four_sum_le {v0 v1 e0 e1 : ℝ} {p0 p1 k0 k1 : ℂ} :
    ‖((v0 : ℂ) * p0 + (v1 : ℂ) * p1) + (k0 * (e0 : ℂ) + k1 * (e1 : ℂ))‖ ≤
      |v0| * ‖p0‖ + |v1| * ‖p1‖ + ‖k0‖ * |e0| + ‖k1‖ * |e1| := by
  have ht1 := norm_add_le ((v0 : ℂ) * p0 + (v1 : ℂ) * p1) (k0 * (e0 : ℂ) + k1 * (e1 : ℂ))
  have ht2 := norm_add_le ((v0 : ℂ) * p0) ((v1 : ℂ) * p1)
  have ht3 := norm_add_le (k0 * (e0 : ℂ)) (k1 * (e1 : ℂ))
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs] at ht2
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs] at ht3
  linarith

private theorem four_term_jb_bound {jbw nrm v0 v1 p0 p1 k0 k1 e0 e1 EV EE Cg G8 : ℝ}
    (hjb : 0 ≤ jbw) (hp0_0 : 0 ≤ p0) (hp1_0 : 0 ≤ p1)
    (he0_0 : 0 ≤ e0) (he1_0 : 0 ≤ e1) (hEV : 0 ≤ EV) (hCg : 0 ≤ Cg) (hG8 : 0 ≤ G8)
    (hnrm : nrm ≤ v0 * p0 + v1 * p1 + k0 * e0 + k1 * e1)
    (hv0 : v0 ≤ EV) (hv1 : v1 ≤ EV)
    (hp0 : jbw * p0 ≤ Cg * G8) (hp1 : jbw * p1 ≤ Cg * G8)
    (hk0 : k0 ≤ Cg * G8) (hk1 : k1 ≤ Cg * G8)
    (he0 : jbw * e0 ≤ EE) (he1 : jbw * e1 ≤ EE) :
    jbw * nrm ≤ 2 * (EV + EE) * Cg * G8 := by
  have ht1 : v0 * (jbw * p0) ≤ EV * (Cg * G8) := mul_le_mul hv0 hp0 (mul_nonneg hjb hp0_0) hEV
  have ht2 : v1 * (jbw * p1) ≤ EV * (Cg * G8) := mul_le_mul hv1 hp1 (mul_nonneg hjb hp1_0) hEV
  have ht3 : k0 * (jbw * e0) ≤ (Cg * G8) * EE :=
    mul_le_mul hk0 he0 (mul_nonneg hjb he0_0) (mul_nonneg hCg hG8)
  have ht4 : k1 * (jbw * e1) ≤ (Cg * G8) * EE :=
    mul_le_mul hk1 he1 (mul_nonneg hjb he1_0) (mul_nonneg hCg hG8)
  calc jbw * nrm
      ≤ jbw * (v0 * p0 + v1 * p1 + k0 * e0 + k1 * e1) := mul_le_mul_of_nonneg_left hnrm hjb
    _ = v0 * (jbw * p0) + v1 * (jbw * p1) + k0 * (jbw * e0) + k1 * (jbw * e1) := by ring
    _ ≤ EV * (Cg * G8) + EV * (Cg * G8) + (Cg * G8) * EE + (Cg * G8) * EE := by linarith
    _ = 2 * (EV + EE) * Cg * G8 := by ring

private theorem weighted_two_sum_le {c1 c2 A B : ℝ}
    (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    c1 * A + c2 * B ≤ (c1 + c2 + 1) * (A + B) := by
  have h1 : 0 ≤ c1 * B := mul_nonneg hc1 hB
  have h2 : 0 ≤ c2 * A := mul_nonneg hc2 hA
  linarith

/-- Unconditional `AEStronglyMeasurable` and `X_{m,d}` bound for `canonTrainRes P tr s` from the
periodic `pdCx`/`kerVelCx` jet bounds of `CanonicalGaussAndJetBound` and our proved exponential
train comparison bounds `movingTrainV_sub_datum_exp_bound` and
`movingTrainGradE_sub_datum_exp_bound`. -/
theorem xNorm_canonTrainRes_le (P : PlanarData) (hP : IsPlanarReference P)
    (V : ℝ → UnforcedLeray.B0010.XG)
    (hVae : ∀ θ : ℝ, 0 < θ → P.canonical θ =ᵐ[UnforcedLeray.B0010.xGMeasure] (V θ : ℝ → ℂ))
    {m : ℝ} (hm : 8 < m) (hGauss : CanonicalGaussAndJetBound) :
    ∃ a_tr : ℝ, 0 < a_tr ∧ ∀ r_min : ℝ, 0 < r_min →
      ∃ C_tr ν_tr : ℝ, 0 < C_tr ∧ 0 < ν_tr ∧
        ∀ ν ∈ Ioc 0 ν_tr,
          ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
            UnforcedLeray.Short.PartI.IsBUCTrain tr →
            ∀ θ ∈ Icc r_min ν⁻¹,
              ∀ (hj : V θ ∈ (UnforcedLeray.B0121.fracPow 8).domain),
                let s := clockAge ν θ
                let d := dOfTheta ν θ
                let G₈ := Real.sqrt (UnforcedLeray.B0121.graphNormSq 8 ⟨V θ, hj⟩)
                AEStronglyMeasurable (canonTrainRes P tr s) (B0579.cellMeasure d m) ∧
                xNorm d m (canonTrainRes P tr s) ≤
                  ENNReal.ofReal
                    (C_tr * ν ^ 3 * Real.exp (-2 * a_tr * θ / ν ^ 3) * G₈) := by
  have hm0 : 0 ≤ m := by linarith
  obtain ⟨C_g, _, hCg_pos, _, hG_prop⟩ := hGauss m hm
  obtain ⟨C_V, a_V, ν_V, hCV, haV, hνV, hV_bd⟩ := movingTrainV_sub_datum_exp_bound
  obtain ⟨a_E, haE, hE_all⟩ := movingTrainGradE_sub_datum_exp_bound (Nat.ceil m + 2)
  obtain ⟨K_p, hKp_nn, hKp⟩ := xNorm_le_of_jb_pow (m := m) hm0
  obtain ⟨a_tr, hatr_eq⟩ : ∃ a : ℝ, a = min a_V a_E := ⟨_, rfl⟩
  have hatr_pos : 0 < a_tr := by rw [hatr_eq]; exact lt_min haV haE
  have hatr_le_V : a_tr ≤ a_V := by rw [hatr_eq]; exact min_le_left _ _
  have hatr_le_E : a_tr ≤ a_E := by rw [hatr_eq]; exact min_le_right _ _
  refine ⟨a_tr, hatr_pos, fun r_min hr_min => ?_⟩
  obtain ⟨C_E, ν_E, hCE, hνE, hE_bd⟩ := hE_all r_min hr_min
  obtain ⟨C_tr, hCtr_eq⟩ : ∃ C : ℝ, C = 2 * (C_V + C_E) * C_g * (K_p + 1) := ⟨_, rfl⟩
  have hCtr_pos : 0 < C_tr := by rw [hCtr_eq]; positivity
  refine ⟨C_tr, min (min ν_V ν_E) (min 1 r_min), hCtr_pos,
    lt_min (lt_min hνV hνE) (lt_min zero_lt_one hr_min), fun ν hν tr hbuc θ hθ hj => ?_⟩
  intro s d G₈
  have hν0 : 0 < ν := hν.1
  have hνV' : ν ∈ Ioc 0 ν_V :=
    ⟨hν0, hν.2.trans (le_trans (min_le_left _ _) (min_le_left _ _))⟩
  have hνE' : ν ∈ Ioc 0 ν_E :=
    ⟨hν0, hν.2.trans (le_trans (min_le_left _ _) (min_le_right _ _))⟩
  have hν1 : ν ≤ 1 := hν.2.trans (le_trans (min_le_right _ _) (min_le_left _ _))
  have hνr : ν ≤ r_min := hν.2.trans (le_trans (min_le_right _ _) (min_le_right _ _))
  have hθ_pos : 0 < θ := lt_of_lt_of_le hr_min hθ.1
  have hs_mem : s ∈ Icc (0 : ℝ) (clockAge ν r_min) :=
    ⟨clockAge_nonneg hν0 hθ_pos hθ.2, clockAge_antitone hν0 hr_min hθ.1⟩
  obtain ⟨_, ha0, _, _, hd1_s, hac2⟩ := clockWindow_bounds hν0 hν1 hr_min hνr hs_mem
  have hθ_s : clockTheta ν s = θ := clockTheta_clockAge hν0 hθ_pos
  have hd_s : cellLen (ν ^ (-2 : ℝ)) (clockA ν s) = d := by
    dsimp [d]
    rw [← dOfTheta_eq_cellLen hν0 ha0, hθ_s]
  have hd1 : 1 ≤ d := by rwa [hθ_s] at hd1_s
  have hd_pos : 0 < d := lt_of_lt_of_le zero_lt_one hd1
  have hf_smooth : ContDiffOn ℝ ∞ (P.canonical θ) (Ioi 0) :=
    hP.canonical.smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun r hr => ⟨hθ_pos, hr⟩)
  obtain ⟨_, _, hW_sm, hpd_sm, hjet⟩ :=
    hG_prop d hd1 (P.canonical θ) (hP.canonical.memXG θ hθ_pos) hf_smooth (V θ)
      (hVae θ hθ_pos) hj
  obtain ⟨W, hW_eq⟩ : ∃ W : ℝ × ℝ → ℂ, W = periodizeC d (planarMode (P.canonical θ)) := ⟨_, rfl⟩
  rw [← hW_eq] at hW_sm hpd_sm hjet
  have hfun_W : canonTrainRes P tr s = fun y =>
      (((movingTrainV tr s y 0 - UnforcedLeray.Train.datum d y 0 : ℝ) : ℂ) * pdCx 0 W y +
       ((movingTrainV tr s y 1 - UnforcedLeray.Train.datum d y 1 : ℝ) : ℂ) * pdCx 1 W y) +
      (kerVelCx d W y 0 *
        ((movingTrainGradE tr s y 0 -
          B0579.pd 0 (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) y : ℝ) : ℂ) +
       kerVelCx d W y 1 *
        ((movingTrainGradE tr s y 1 -
          B0579.pd 1 (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) y : ℝ) : ℂ)) := by
    funext y
    unfold canonTrainRes movLGauss movL
    dsimp only
    rw [hd_s, hθ_s, ← hW_eq]
    push_cast
    ring
  -- 1. `AEStronglyMeasurable (canonTrainRes P tr s)`
  have haesm : AEStronglyMeasurable (canonTrainRes P tr s) (B0579.cellMeasure d m) := by
    refine StronglyMeasurable.aestronglyMeasurable ?_
    rw [hfun_W]
    have hdatum_sm : ContDiff ℝ ∞ (UnforcedLeray.Train.datum d) :=
      UnforcedLeray.Train.datum_contDiff hd_pos.ne'
    have hcurl_datum_sm : ContDiff ℝ ∞ (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) :=
      curl_contDiff_vort hdatum_sm
    have hv : ∀ k : Fin 2, StronglyMeasurable
        (fun y => ((movingTrainV tr s y k - UnforcedLeray.Train.datum d y k : ℝ) : ℂ) *
          pdCx k W y) := fun k =>
      (Complex.continuous_ofReal.comp
        ((continuous_movingTrainV tr hs_mem.1 k).sub
          ((PiLp.continuous_apply 2 _ k).comp hdatum_sm.continuous))).stronglyMeasurable.mul
        (hpd_sm k)
    have hpd_curl_cont : ∀ k : Fin 2,
        Continuous (B0579.pd k (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d))) := fun k => by
      unfold B0579.pd
      exact (ContinuousLinearMap.apply ℝ ℝ (B0579.dir k)).continuous.comp
        (hcurl_datum_sm.continuous_fderiv (by simp))
    have he : ∀ k : Fin 2, StronglyMeasurable
        (fun y => kerVelCx d W y k *
          ((movingTrainGradE tr s y k -
            B0579.pd k (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) y : ℝ) : ℂ)) :=
      fun k => (stronglyMeasurable_kerVelCx d hW_sm k).mul
        (Complex.continuous_ofReal.comp
          ((continuous_movingTrainGradE tr hs_mem.1 k).sub (hpd_curl_cont k))).stronglyMeasurable
    exact ((hv 0).add (hv 1)).add ((he 0).add (he 1))
  refine ⟨haesm, ?_⟩
  -- 2. Bound `xNorm d m (canonTrainRes P tr s)` via `xNorm_le_of_jb_pow`
  obtain ⟨E_V, hEV_eq⟩ : ∃ E : ℝ, E = C_V * ν ^ 3 * Real.exp (-2 * a_tr * θ / ν ^ 3) := ⟨_, rfl⟩
  obtain ⟨E_E, hEE_eq⟩ : ∃ E : ℝ, E = C_E * ν ^ 3 * Real.exp (-2 * a_tr * θ / ν ^ 3) := ⟨_, rfl⟩
  have hEV_nn : 0 ≤ E_V := by rw [hEV_eq]; positivity
  have hEE_nn : 0 ≤ E_E := by rw [hEE_eq]; positivity
  have hG₈_nn : 0 ≤ G₈ := Real.sqrt_nonneg _
  have hM_nn : 0 ≤ 2 * (E_V + E_E) * C_g * G₈ := by positivity
  have hexp_V := exp_neg_two_mono hatr_le_V hν0 hθ_pos.le
  have hexp_E := exp_neg_two_mono hatr_le_E hν0 hθ_pos.le
  have hjb_bd : ∀ y ∈ B0579.cell d,
      B0579.jb y ^ (Nat.ceil m + 2) * ‖canonTrainRes P tr s y‖ ≤
        2 * (E_V + E_E) * C_g * G₈ := by
    intro y hy
    have hy' : y ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) := by rwa [hd_s]
    have hV0 := hV_bd ν hνV' tr hbuc s hs_mem.1 hac2 y 0
    have hV1 := hV_bd ν hνV' tr hbuc s hs_mem.1 hac2 y 1
    have hE0 := hE_bd ν hνE' tr hbuc s hs_mem y hy' 0
    have hE1 := hE_bd ν hνE' tr hbuc s hs_mem y hy' 1
    simp only [hd_s, hθ_s] at hV0 hV1 hE0 hE1
    have hV0' : |movingTrainV tr s y 0 - UnforcedLeray.Train.datum d y 0| ≤ E_V := by
      rw [hEV_eq]; exact hV0.trans (mul_le_mul_of_nonneg_left hexp_V (by positivity))
    have hV1' : |movingTrainV tr s y 1 - UnforcedLeray.Train.datum d y 1| ≤ E_V := by
      rw [hEV_eq]; exact hV1.trans (mul_le_mul_of_nonneg_left hexp_V (by positivity))
    have hE0' : B0579.jb y ^ (Nat.ceil m + 2) * |movingTrainGradE tr s y 0 -
        B0579.pd 0 (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) y| ≤ E_E := by
      rw [hEE_eq]; exact hE0.trans (mul_le_mul_of_nonneg_left hexp_E (by positivity))
    have hE1' : B0579.jb y ^ (Nat.ceil m + 2) * |movingTrainGradE tr s y 1 -
        B0579.pd 1 (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) y| ≤ E_E := by
      rw [hEE_eq]; exact hE1.trans (mul_le_mul_of_nonneg_left hexp_E (by positivity))
    obtain ⟨hpd0, hK0⟩ := hjet 0 y hy
    obtain ⟨hpd1, hK1⟩ := hjet 1 y hy
    have hnrm : ‖canonTrainRes P tr s y‖ ≤
        |movingTrainV tr s y 0 - UnforcedLeray.Train.datum d y 0| * ‖pdCx 0 W y‖ +
        |movingTrainV tr s y 1 - UnforcedLeray.Train.datum d y 1| * ‖pdCx 1 W y‖ +
        ‖kerVelCx d W y 0‖ * |movingTrainGradE tr s y 0 -
          B0579.pd 0 (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) y| +
        ‖kerVelCx d W y 1‖ * |movingTrainGradE tr s y 1 -
          B0579.pd 1 (UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d)) y| := by
      rw [congrFun hfun_W y]
      exact norm_four_sum_le
    exact four_term_jb_bound (pow_nonneg (B0579.jb_pos y).le _)
      (norm_nonneg _) (norm_nonneg _) (abs_nonneg _) (abs_nonneg _)
      hEV_nn hCg_pos.le hG₈_nn hnrm hV0' hV1' hpd0 hpd1 hK0 hK1 hE0' hE1'
  refine (hKp d (2 * (E_V + E_E) * C_g * G₈) (canonTrainRes P tr s) hM_nn hjb_bd).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hle_Kp : K_p ≤ K_p + 1 := by linarith
  calc 2 * (E_V + E_E) * C_g * G₈ * K_p
      ≤ 2 * (E_V + E_E) * C_g * G₈ * (K_p + 1) :=
        mul_le_mul_of_nonneg_left hle_Kp hM_nn
    _ = C_tr * ν ^ 3 * Real.exp (-2 * a_tr * θ / ν ^ 3) * G₈ := by
        rw [hCtr_eq, hEV_eq, hEE_eq]; ring

private theorem long_window_real_bound
    {g_θ d θ ν N0 G₈ C_g C_tr M₀ M₈ K_abs a_g a_tr a₀ C_long : ℝ}
    (hν0 : 0 < ν) (hν1 : ν ≤ 1) (hθ_ge1 : 1 ≤ θ)
    (hg_pos : 0 < g_θ) (hG8_nn : 0 ≤ G₈)
    (hCg_pos : 0 < C_g) (hCtr_pos : 0 < C_tr)
    (hM₀_pos : 0 < M₀) (hM₈_pos : 0 < M₈) (hKabs_pos : 0 < K_abs)
    (ha₀_g : a₀ ≤ a_g) (ha₀_tr : a₀ ≤ a_tr)
    (hd_sq : d ^ 2 = θ / ν ^ 3)
    (hd_m4 : d ^ (-4 : ℝ) = (ν ^ 3) ^ 2 * θ ^ (-2 : ℝ))
    (h0_bd : g_θ * N0 ≤ M₀)
    (hG8_bd : g_θ * G₈ ≤ M₈ * (1 + θ) ^ (4 : ℝ))
    (hKabs : ∀ u : ℝ, 0 ≤ u →
      u * (1 + u) ^ (4 : ℝ) * Real.exp (-2 * a₀ * u) ≤ K_abs * Real.exp (-a₀ * u))
    (hClong : C_long = C_g * M₀ + (C_g + C_tr) * M₈ * K_abs + 1) :
    g_θ * (C_g * (d ^ (-4 : ℝ) * N0 + Real.exp (-2 * a_g * d ^ 2) * G₈) +
        C_tr * ν ^ 3 * Real.exp (-2 * a_tr * θ / ν ^ 3) * G₈) ≤
      C_long * ((ν ^ 3) ^ 2 * θ ^ (-2 : ℝ) + ν ^ 3 * Real.exp (-a₀ * θ / ν ^ 3)) := by
  have hθ_pos : 0 < θ := lt_of_lt_of_le zero_lt_one hθ_ge1
  obtain ⟨u, hu_eq⟩ : ∃ u : ℝ, u = θ / ν ^ 3 := ⟨_, rfl⟩
  have hu_nn : 0 ≤ u := by rw [hu_eq]; positivity
  have hν3_le1 : ν ^ 3 ≤ 1 := pow_le_one₀ hν0.le hν1
  have hν3u_eq : ν ^ 3 * u = θ := by rw [hu_eq]; field_simp [hν0.ne']
  have h1_le_ν3u : 1 ≤ ν ^ 3 * u := by linarith
  have hθ_le_u : θ ≤ u := by
    have hmul : ν ^ 3 * u ≤ 1 * u := mul_le_mul_of_nonneg_right hν3_le1 hu_nn
    linarith
  have hu_ge1 : 1 ≤ u := le_trans hθ_ge1 hθ_le_u
  have h14_le : (1 + θ) ^ (4 : ℝ) ≤ (1 + u) ^ (4 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  have hexp_g : Real.exp (-2 * a_g * d ^ 2) ≤ Real.exp (-2 * a₀ * u) := by
    rw [hd_sq, ← hu_eq]
    apply Real.exp_le_exp.2
    have hmul : 2 * a₀ * u ≤ 2 * a_g * u := mul_le_mul_of_nonneg_right (by linarith) hu_nn
    linarith
  have hexp_t : Real.exp (-2 * a_tr * θ / ν ^ 3) ≤ Real.exp (-2 * a₀ * u) := by
    apply Real.exp_le_exp.2
    have he : -2 * a_tr * θ / ν ^ 3 = -(2 * a_tr * u) := by rw [hu_eq]; ring
    rw [he]
    have hmul : 2 * a₀ * u ≤ 2 * a_tr * u := mul_le_mul_of_nonneg_right (by linarith) hu_nn
    linarith
  have habs := hKabs u hu_nn
  have hu_exp : Real.exp (-a₀ * u) = Real.exp (-a₀ * θ / ν ^ 3) := by
    rw [hu_eq]; congr 1; ring
  have himg : C_g * (d ^ (-4 : ℝ) * (g_θ * N0)) ≤
      (C_g * M₀) * ((ν ^ 3) ^ 2 * θ ^ (-2 : ℝ)) := by
    rw [hd_m4]
    calc C_g * (((ν ^ 3) ^ 2 * θ ^ (-2 : ℝ)) * (g_θ * N0))
        = C_g * (g_θ * N0) * ((ν ^ 3) ^ 2 * θ ^ (-2 : ℝ)) := by ring
      _ ≤ (C_g * M₀) * ((ν ^ 3) ^ 2 * θ ^ (-2 : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h0_bd hCg_pos.le) (by positivity)
  have hexp1 : C_g * (Real.exp (-2 * a_g * d ^ 2) * (g_θ * G₈)) ≤
      (C_g * M₈ * K_abs) * (ν ^ 3 * Real.exp (-a₀ * θ / ν ^ 3)) := by
    have hstep1 : Real.exp (-2 * a_g * d ^ 2) * (g_θ * G₈) ≤
        M₈ * ((1 + u) ^ (4 : ℝ) * Real.exp (-2 * a₀ * u)) := by
      calc Real.exp (-2 * a_g * d ^ 2) * (g_θ * G₈)
          ≤ Real.exp (-2 * a₀ * u) * (M₈ * (1 + θ) ^ (4 : ℝ)) :=
            mul_le_mul hexp_g hG8_bd (mul_nonneg hg_pos.le hG8_nn) (Real.exp_nonneg _)
        _ ≤ Real.exp (-2 * a₀ * u) * (M₈ * (1 + u) ^ (4 : ℝ)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left h14_le hM₈_pos.le) (Real.exp_nonneg _)
        _ = M₈ * ((1 + u) ^ (4 : ℝ) * Real.exp (-2 * a₀ * u)) := by ring
    have hstep2 : (1 + u) ^ (4 : ℝ) * Real.exp (-2 * a₀ * u) ≤
        ν ^ 3 * (u * (1 + u) ^ (4 : ℝ) * Real.exp (-2 * a₀ * u)) := by
      have hnn : 0 ≤ (1 + u) ^ (4 : ℝ) * Real.exp (-2 * a₀ * u) := by positivity
      calc (1 + u) ^ (4 : ℝ) * Real.exp (-2 * a₀ * u)
          = 1 * ((1 + u) ^ (4 : ℝ) * Real.exp (-2 * a₀ * u)) := (one_mul _).symm
        _ ≤ (ν ^ 3 * u) * ((1 + u) ^ (4 : ℝ) * Real.exp (-2 * a₀ * u)) :=
            mul_le_mul_of_nonneg_right h1_le_ν3u hnn
        _ = ν ^ 3 * (u * (1 + u) ^ (4 : ℝ) * Real.exp (-2 * a₀ * u)) := by ring
    calc C_g * (Real.exp (-2 * a_g * d ^ 2) * (g_θ * G₈))
        ≤ C_g * (M₈ * ((1 + u) ^ (4 : ℝ) * Real.exp (-2 * a₀ * u))) :=
          mul_le_mul_of_nonneg_left hstep1 hCg_pos.le
      _ ≤ C_g * (M₈ * (ν ^ 3 * (u * (1 + u) ^ (4 : ℝ) * Real.exp (-2 * a₀ * u)))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hstep2 hM₈_pos.le) hCg_pos.le
      _ = C_g * M₈ * ν ^ 3 * (u * (1 + u) ^ (4 : ℝ) * Real.exp (-2 * a₀ * u)) := by ring
      _ ≤ C_g * M₈ * ν ^ 3 * (K_abs * Real.exp (-a₀ * u)) :=
          mul_le_mul_of_nonneg_left habs (by positivity)
      _ = (C_g * M₈ * K_abs) * (ν ^ 3 * Real.exp (-a₀ * θ / ν ^ 3)) := by
          rw [hu_exp]; ring
  have hexp2 : C_tr * ν ^ 3 * Real.exp (-2 * a_tr * θ / ν ^ 3) * (g_θ * G₈) ≤
      (C_tr * M₈ * K_abs) * (ν ^ 3 * Real.exp (-a₀ * θ / ν ^ 3)) := by
    have hstep1 : Real.exp (-2 * a_tr * θ / ν ^ 3) * (g_θ * G₈) ≤
        M₈ * (u * (1 + u) ^ (4 : ℝ) * Real.exp (-2 * a₀ * u)) := by
      calc Real.exp (-2 * a_tr * θ / ν ^ 3) * (g_θ * G₈)
          ≤ Real.exp (-2 * a₀ * u) * (M₈ * (1 + θ) ^ (4 : ℝ)) :=
            mul_le_mul hexp_t hG8_bd (mul_nonneg hg_pos.le hG8_nn) (Real.exp_nonneg _)
        _ ≤ Real.exp (-2 * a₀ * u) * (M₈ * (1 + u) ^ (4 : ℝ)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left h14_le hM₈_pos.le) (Real.exp_nonneg _)
        _ = M₈ * (1 * ((1 + u) ^ (4 : ℝ) * Real.exp (-2 * a₀ * u))) := by ring
        _ ≤ M₈ * (u * ((1 + u) ^ (4 : ℝ) * Real.exp (-2 * a₀ * u))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hu_ge1 (by positivity)) hM₈_pos.le
        _ = M₈ * (u * (1 + u) ^ (4 : ℝ) * Real.exp (-2 * a₀ * u)) := by ring
    calc C_tr * ν ^ 3 * Real.exp (-2 * a_tr * θ / ν ^ 3) * (g_θ * G₈)
        = C_tr * ν ^ 3 * (Real.exp (-2 * a_tr * θ / ν ^ 3) * (g_θ * G₈)) := by ring
      _ ≤ C_tr * ν ^ 3 * (M₈ * (u * (1 + u) ^ (4 : ℝ) * Real.exp (-2 * a₀ * u))) :=
          mul_le_mul_of_nonneg_left hstep1 (by positivity)
      _ = C_tr * M₈ * ν ^ 3 * (u * (1 + u) ^ (4 : ℝ) * Real.exp (-2 * a₀ * u)) := by ring
      _ ≤ C_tr * M₈ * ν ^ 3 * (K_abs * Real.exp (-a₀ * u)) :=
          mul_le_mul_of_nonneg_left habs (by positivity)
      _ = (C_tr * M₈ * K_abs) * (ν ^ 3 * Real.exp (-a₀ * θ / ν ^ 3)) := by
          rw [hu_exp]; ring
  have hw := weighted_two_sum_le
    (c1 := C_g * M₀) (c2 := (C_g + C_tr) * M₈ * K_abs)
    (A := (ν ^ 3) ^ 2 * θ ^ (-2 : ℝ)) (B := ν ^ 3 * Real.exp (-a₀ * θ / ν ^ 3))
    (by positivity) (by positivity) (by positivity) (by positivity)
  rw [hClong]
  calc g_θ * (C_g * (d ^ (-4 : ℝ) * N0 + Real.exp (-2 * a_g * d ^ 2) * G₈) +
          C_tr * ν ^ 3 * Real.exp (-2 * a_tr * θ / ν ^ 3) * G₈)
      = C_g * (d ^ (-4 : ℝ) * (g_θ * N0)) +
          C_g * (Real.exp (-2 * a_g * d ^ 2) * (g_θ * G₈)) +
          C_tr * ν ^ 3 * Real.exp (-2 * a_tr * θ / ν ^ 3) * (g_θ * G₈) := by ring
    _ ≤ (C_g * M₀) * ((ν ^ 3) ^ 2 * θ ^ (-2 : ℝ)) +
          (C_g * M₈ * K_abs) * (ν ^ 3 * Real.exp (-a₀ * θ / ν ^ 3)) +
          (C_tr * M₈ * K_abs) * (ν ^ 3 * Real.exp (-a₀ * θ / ν ^ 3)) := by linarith
    _ = (C_g * M₀) * ((ν ^ 3) ^ 2 * θ ^ (-2 : ℝ)) +
          ((C_g + C_tr) * M₈ * K_abs) * (ν ^ 3 * Real.exp (-a₀ * θ / ν ^ 3)) := by ring
    _ ≤ (C_g * M₀ + (C_g + C_tr) * M₈ * K_abs + 1) *
          ((ν ^ 3) ^ 2 * θ ^ (-2 : ℝ) + ν ^ 3 * Real.exp (-a₀ * θ / ν ^ 3)) := hw

private theorem compact_window_real_bound
    {d r θ ν N0 G₈ C_g C_tr M₀_r M₈_r K_abs a_g a_tr a₀ C_r : ℝ}
    (hν0 : 0 < ν) (hr_pos : 0 < r) (hrθ : r ≤ θ) (hG8_nn : 0 ≤ G₈)
    (hCg_pos : 0 < C_g) (hCtr_pos : 0 < C_tr)
    (hM₀_pos : 0 < M₀_r) (hM₈_pos : 0 < M₈_r) (hKabs_pos : 0 < K_abs)
    (ha₀_pos : 0 < a₀) (ha₀_g : a₀ ≤ a_g) (ha₀_tr : a₀ ≤ a_tr)
    (hd_sq : d ^ 2 = θ / ν ^ 3)
    (hd_m4 : d ^ (-4 : ℝ) = (ν ^ 3) ^ 2 * θ ^ (-2 : ℝ))
    (h0_bd : N0 ≤ M₀_r) (hG8_bd : G₈ ≤ M₈_r)
    (hKabs : ∀ u : ℝ, 0 ≤ u →
      u * (1 + u) ^ (4 : ℝ) * Real.exp (-2 * a₀ * u) ≤ K_abs * Real.exp (-a₀ * u))
    (hCr : C_r = C_g * M₀_r + (C_g * r⁻¹ * K_abs + C_tr) * M₈_r + 1) :
    C_g * (d ^ (-4 : ℝ) * N0 + Real.exp (-2 * a_g * d ^ 2) * G₈) +
        C_tr * ν ^ 3 * Real.exp (-2 * a_tr * θ / ν ^ 3) * G₈ ≤
      C_r * ((ν ^ 3) ^ 2 * θ ^ (-2 : ℝ) + ν ^ 3 * Real.exp (-a₀ * θ / ν ^ 3)) := by
  have hθ_pos : 0 < θ := lt_of_lt_of_le hr_pos hrθ
  obtain ⟨u, hu_eq⟩ : ∃ u : ℝ, u = θ / ν ^ 3 := ⟨_, rfl⟩
  have hu_nn : 0 ≤ u := by rw [hu_eq]; positivity
  have h1_le_ru : 1 ≤ r⁻¹ * ν ^ 3 * u := by
    have h1 : ν ^ 3 * u = θ := by rw [hu_eq]; field_simp [hν0.ne']
    rw [mul_assoc, h1]
    exact (one_le_inv_mul₀ hr_pos).2 hrθ
  have h1_le_14 : 1 ≤ (1 + u) ^ (4 : ℝ) :=
    Real.one_le_rpow (by linarith) (by norm_num)
  have hexp_g : Real.exp (-2 * a_g * d ^ 2) ≤ Real.exp (-2 * a₀ * u) := by
    rw [hd_sq, ← hu_eq]
    apply Real.exp_le_exp.2
    have hmul : 2 * a₀ * u ≤ 2 * a_g * u := mul_le_mul_of_nonneg_right (by linarith) hu_nn
    linarith
  have hexp_t : Real.exp (-2 * a_tr * θ / ν ^ 3) ≤ Real.exp (-a₀ * θ / ν ^ 3) := by
    apply Real.exp_le_exp.2
    have e1 : -2 * a_tr * θ / ν ^ 3 = -(2 * a_tr * u) := by rw [hu_eq]; ring
    have e2 : -a₀ * θ / ν ^ 3 = -(a₀ * u) := by rw [hu_eq]; ring
    rw [e1, e2]
    have hmul : a₀ * u ≤ 2 * a_tr * u := mul_le_mul_of_nonneg_right (by linarith [ha₀_pos]) hu_nn
    linarith
  have habs := hKabs u hu_nn
  have hu_exp : Real.exp (-a₀ * u) = Real.exp (-a₀ * θ / ν ^ 3) := by
    rw [hu_eq]; congr 1; ring
  have himg : C_g * (d ^ (-4 : ℝ) * N0) ≤
      (C_g * M₀_r) * ((ν ^ 3) ^ 2 * θ ^ (-2 : ℝ)) := by
    rw [hd_m4]
    calc C_g * (((ν ^ 3) ^ 2 * θ ^ (-2 : ℝ)) * N0)
        = (C_g * N0) * ((ν ^ 3) ^ 2 * θ ^ (-2 : ℝ)) := by ring
      _ ≤ (C_g * M₀_r) * ((ν ^ 3) ^ 2 * θ ^ (-2 : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h0_bd hCg_pos.le) (by positivity)
  have hexp1 : C_g * (Real.exp (-2 * a_g * d ^ 2) * G₈) ≤
      (C_g * r⁻¹ * K_abs * M₈_r) * (ν ^ 3 * Real.exp (-a₀ * θ / ν ^ 3)) := by
    have hstep : Real.exp (-2 * a_g * d ^ 2) ≤
        r⁻¹ * ν ^ 3 * (K_abs * Real.exp (-a₀ * θ / ν ^ 3)) := by
      calc Real.exp (-2 * a_g * d ^ 2)
          ≤ Real.exp (-2 * a₀ * u) := hexp_g
        _ = 1 * (1 * Real.exp (-2 * a₀ * u)) := by ring
        _ ≤ (r⁻¹ * ν ^ 3 * u) * ((1 + u) ^ (4 : ℝ) * Real.exp (-2 * a₀ * u)) :=
            mul_le_mul h1_le_ru
              (mul_le_mul_of_nonneg_right h1_le_14 (Real.exp_nonneg _))
              (by positivity) (by positivity)
        _ = r⁻¹ * ν ^ 3 * (u * (1 + u) ^ (4 : ℝ) * Real.exp (-2 * a₀ * u)) := by ring
        _ ≤ r⁻¹ * ν ^ 3 * (K_abs * Real.exp (-a₀ * u)) :=
            mul_le_mul_of_nonneg_left habs (by positivity)
        _ = r⁻¹ * ν ^ 3 * (K_abs * Real.exp (-a₀ * θ / ν ^ 3)) := by rw [hu_exp]
    calc C_g * (Real.exp (-2 * a_g * d ^ 2) * G₈)
        ≤ C_g * ((r⁻¹ * ν ^ 3 * (K_abs * Real.exp (-a₀ * θ / ν ^ 3))) * M₈_r) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hstep hG8_bd hG8_nn (by positivity)) hCg_pos.le
      _ = (C_g * r⁻¹ * K_abs * M₈_r) * (ν ^ 3 * Real.exp (-a₀ * θ / ν ^ 3)) := by ring
  have hexp2 : C_tr * ν ^ 3 * Real.exp (-2 * a_tr * θ / ν ^ 3) * G₈ ≤
      (C_tr * M₈_r) * (ν ^ 3 * Real.exp (-a₀ * θ / ν ^ 3)) := by
    calc C_tr * ν ^ 3 * Real.exp (-2 * a_tr * θ / ν ^ 3) * G₈
        ≤ C_tr * ν ^ 3 * Real.exp (-a₀ * θ / ν ^ 3) * M₈_r :=
          mul_le_mul (mul_le_mul_of_nonneg_left hexp_t (by positivity)) hG8_bd
            hG8_nn (by positivity)
      _ = (C_tr * M₈_r) * (ν ^ 3 * Real.exp (-a₀ * θ / ν ^ 3)) := by ring
  have hw := weighted_two_sum_le
    (c1 := C_g * M₀_r) (c2 := (C_g * r⁻¹ * K_abs + C_tr) * M₈_r)
    (A := (ν ^ 3) ^ 2 * θ ^ (-2 : ℝ)) (B := ν ^ 3 * Real.exp (-a₀ * θ / ν ^ 3))
    (by positivity) (by positivity) (by positivity) (by positivity)
  rw [hCr]
  calc C_g * (d ^ (-4 : ℝ) * N0 + Real.exp (-2 * a_g * d ^ 2) * G₈) +
          C_tr * ν ^ 3 * Real.exp (-2 * a_tr * θ / ν ^ 3) * G₈
      = C_g * (d ^ (-4 : ℝ) * N0) + C_g * (Real.exp (-2 * a_g * d ^ 2) * G₈) +
          C_tr * ν ^ 3 * Real.exp (-2 * a_tr * θ / ν ^ 3) * G₈ := by ring
    _ ≤ (C_g * M₀_r) * ((ν ^ 3) ^ 2 * θ ^ (-2 : ℝ)) +
          (C_g * r⁻¹ * K_abs * M₈_r) * (ν ^ 3 * Real.exp (-a₀ * θ / ν ^ 3)) +
          (C_tr * M₈_r) * (ν ^ 3 * Real.exp (-a₀ * θ / ν ^ 3)) := by linarith
    _ = (C_g * M₀_r) * ((ν ^ 3) ^ 2 * θ ^ (-2 : ℝ)) +
          ((C_g * r⁻¹ * K_abs + C_tr) * M₈_r) * (ν ^ 3 * Real.exp (-a₀ * θ / ν ^ 3)) := by ring
    _ ≤ (C_g * M₀_r + (C_g * r⁻¹ * K_abs + C_tr) * M₈_r + 1) *
          ((ν ^ 3) ^ 2 * θ ^ (-2 : ℝ) + ν ^ 3 * Real.exp (-a₀ * θ / ν ^ 3)) := hw

end ResidualBoundAux

/-- Full proof of `CTCanonicalResidual` at any planar reference `P` satisfying
`HasCanonicalSolutionRep P`, reduced to the two R5-verified analytical leaves
`ResidualBoundAux.CanonicalColumnWeakEq` and `ResidualBoundAux.CanonicalGaussAndJetBound`. -/
theorem ctCanonicalResidual_at (P : PlanarData) (hP : IsPlanarReference P)
    (hRep : HasCanonicalSolutionRep P)
    (hWeak : ResidualBoundAux.CanonicalColumnWeakEq)
    (hGauss : ResidualBoundAux.CanonicalGaussAndJetBound)
    (m : ℝ) (hm : 8 < m) :
    ∃ b₀ : ℝ, 0 < b₀ ∧ ∀ b : ℝ, b₀ ≤ b →
      (∃ (C a₀ ν₀ : ℝ), 0 < C ∧ 0 < a₀ ∧ 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
        ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
          UnforcedLeray.Short.PartI.IsBUCTrain tr →
          ∃ (u_can : ℝ → ℝ × ℝ → Fin 2 → ℂ) (f_res : ℝ → ℝ × ℝ → ℂ),
            (∀ s ∈ Icc (0 : ℝ) (coreEnd ν b),
              IsBiotSavart (ν ^ (-2 : ℝ)) (canonicalPhysColumn P ν s) (u_can s) ∧
              MemLp (f_res s) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) ∧
              HasZeroCirculation (ν ^ (-2 : ℝ)) (f_res s) ∧
              IsCentrallyEven (f_res s) ∧
              Tendsto (fun s' => xNorm (ν ^ (-2 : ℝ)) m (f_res s' - f_res s))
                (𝓝[Icc (0 : ℝ) (coreEnd ν b)] s) (𝓝 0)) ∧
            (∀ φ, B0579.IsCylTest (ν ^ (-2 : ℝ)) φ → ∀ s ∈ Icc (0 : ℝ) (coreEnd ν b),
              IntegrableOn (flowIntegrand tr (canonicalPhysColumn P ν s) (u_can s) s φ)
                (B0579.cell (ν ^ (-2 : ℝ))) ∧
              IntervalIntegrable (fun τ =>
                (∫ x in B0579.cell (ν ^ (-2 : ℝ)),
                  flowIntegrand tr (canonicalPhysColumn P ν τ) (u_can τ) τ φ x) +
                (∫ x in B0579.cell (ν ^ (-2 : ℝ)), f_res τ x * (φ x : ℂ))) volume 0 s ∧
              ∫ x in B0579.cell (ν ^ (-2 : ℝ)), canonicalPhysColumn P ν s x * (φ x : ℂ) =
                (∫ x in B0579.cell (ν ^ (-2 : ℝ)), preparedDatum P ν x * (φ x : ℂ)) +
                ∫ τ in (0 : ℝ)..s,
                  ((∫ x in B0579.cell (ν ^ (-2 : ℝ)),
                    flowIntegrand tr (canonicalPhysColumn P ν τ) (u_can τ) τ φ x) +
                  (∫ x in B0579.cell (ν ^ (-2 : ℝ)), f_res τ x * (φ x : ℂ)))) ∧
            (∀ θ ∈ Icc b ν⁻¹,
              ENNReal.ofReal (Real.exp (P.eigenvalue.re * θ) * θ ^ P.kappa.re *
                  (clockA ν (clockAge ν θ)) ^ 2 / ‖P.gaugeFactor ν‖) *
                xNorm (dOfTheta ν θ) m
                  (JscaleInv (clockA ν (clockAge ν θ)) (f_res (clockAge ν θ))) ≤
                ENNReal.ofReal (C * ((ν ^ 3) ^ 2 * θ ^ (-2 : ℝ) +
                  ν ^ 3 * Real.exp (-a₀ * θ / ν ^ 3))))) ∧
      (∀ r : ℝ, 0 < r → r ≤ b →
        ∃ (C_r a₀ ν_r : ℝ), 0 < C_r ∧ 0 < a₀ ∧ 0 < ν_r ∧ ∀ ν ∈ Ioc 0 ν_r,
          ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
            UnforcedLeray.Short.PartI.IsBUCTrain tr →
            ∃ (u_can : ℝ → ℝ × ℝ → Fin 2 → ℂ) (f_res : ℝ → ℝ × ℝ → ℂ),
              (∀ s ∈ Icc (coreEnd ν b) (clockAge ν r),
                IsBiotSavart (ν ^ (-2 : ℝ)) (canonicalPhysColumn P ν s) (u_can s) ∧
                MemLp (f_res s) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) ∧
                HasZeroCirculation (ν ^ (-2 : ℝ)) (f_res s) ∧
                IsCentrallyEven (f_res s) ∧
                Tendsto (fun s' => xNorm (ν ^ (-2 : ℝ)) m (f_res s' - f_res s))
                  (𝓝[Icc (coreEnd ν b) (clockAge ν r)] s) (𝓝 0)) ∧
              (∀ φ, B0579.IsCylTest (ν ^ (-2 : ℝ)) φ → ∀ s ∈ Icc (coreEnd ν b) (clockAge ν r),
                IntegrableOn (flowIntegrand tr (canonicalPhysColumn P ν s) (u_can s) s φ)
                  (B0579.cell (ν ^ (-2 : ℝ))) ∧
                IntervalIntegrable (fun τ =>
                  (∫ x in B0579.cell (ν ^ (-2 : ℝ)),
                    flowIntegrand tr (canonicalPhysColumn P ν τ) (u_can τ) τ φ x) +
                  (∫ x in B0579.cell (ν ^ (-2 : ℝ)), f_res τ x * (φ x : ℂ)))
                  volume (coreEnd ν b) s ∧
                ∫ x in B0579.cell (ν ^ (-2 : ℝ)), canonicalPhysColumn P ν s x * (φ x : ℂ) =
                  (∫ x in B0579.cell (ν ^ (-2 : ℝ)),
                    canonicalPhysColumn P ν (coreEnd ν b) x * (φ x : ℂ)) +
                  ∫ τ in (coreEnd ν b)..s,
                    ((∫ x in B0579.cell (ν ^ (-2 : ℝ)),
                      flowIntegrand tr (canonicalPhysColumn P ν τ) (u_can τ) τ φ x) +
                    (∫ x in B0579.cell (ν ^ (-2 : ℝ)), f_res τ x * (φ x : ℂ)))) ∧
              (∀ θ ∈ Icc r b,
                ENNReal.ofReal ((clockA ν (clockAge ν θ)) ^ 2 / ‖P.gaugeFactor ν‖) *
                  xNorm (dOfTheta ν θ) m
                    (JscaleInv (clockA ν (clockAge ν θ)) (f_res (clockAge ν θ))) ≤
                  ENNReal.ofReal (C_r * ((ν ^ 3) ^ 2 * θ ^ (-2 : ℝ) +
                    ν ^ 3 * Real.exp (-a₀ * θ / ν ^ 3))))) := by
  obtain ⟨V, hVsol, hVae⟩ := hRep
  obtain ⟨hSmoothAll, b₀, hb₀_ge1, hb_all⟩ :=
    ResidualBoundAux.canonicalSolutionRep_smooth_and_bounds P hP V hVsol hVae
  obtain ⟨C_g, a_g, hCg_pos, hag_pos, hG_prop⟩ := hGauss m hm
  obtain ⟨a_tr, hatr_pos, hTr_all⟩ :=
    ResidualBoundAux.xNorm_canonTrainRes_le P hP V hVae hm hGauss
  obtain ⟨a₀, ha₀_eq⟩ : ∃ a : ℝ, a = min a_g a_tr := ⟨_, rfl⟩
  have ha₀_pos : 0 < a₀ := by rw [ha₀_eq]; exact lt_min hag_pos hatr_pos
  have ha₀_g : a₀ ≤ a_g := by rw [ha₀_eq]; exact min_le_left _ _
  have ha₀_tr : a₀ ≤ a_tr := by rw [ha₀_eq]; exact min_le_right _ _
  obtain ⟨K_abs, hKabs_pos, hKabs⟩ :=
    ResidualBoundAux.exists_one_add_rpow_four_mul_exp_le ha₀_pos
  refine ⟨b₀, lt_of_lt_of_le zero_lt_one hb₀_ge1, fun b hb => ?_⟩
  obtain ⟨⟨M₀, M₈, hM₀_pos, hM₈_pos, hLong0, hLong8⟩, hComp_all⟩ := hb_all b hb
  have hb_ge1 : 1 ≤ b := le_trans hb₀_ge1 hb
  have hb_pos : 0 < b := lt_of_lt_of_le zero_lt_one hb_ge1
  refine ⟨?_, ?_⟩
  · -- Part A: Long comparison window `b ≤ θ ≤ ν⁻¹` (`[0, coreEnd ν b]`)
    obtain ⟨C_tr_b, ν_tr_b, hCtr_b, hνtr_b, hTr_b⟩ := hTr_all b hb_pos
    obtain ⟨C_long, hClong_eq⟩ :
        ∃ C : ℝ, C = C_g * M₀ + (C_g + C_tr_b) * M₈ * K_abs + 1 := ⟨_, rfl⟩
    have hClong_pos : 0 < C_long := by rw [hClong_eq]; positivity
    refine ⟨C_long, a₀, min (min ν_tr_b b⁻¹) (min 1 b), hClong_pos, ha₀_pos,
      lt_min (lt_min hνtr_b (inv_pos.2 hb_pos)) (lt_min zero_lt_one hb_pos),
      fun ν hν tr hbuc => ?_⟩
    have hν0 : 0 < ν := hν.1
    have hν_tr : ν ∈ Ioc 0 ν_tr_b :=
      ⟨hν0, hν.2.trans (le_trans (min_le_left _ _) (min_le_left _ _))⟩
    have hν_min1b : ν ≤ min 1 b := hν.2.trans (min_le_right _ _)
    have hν1 : ν ≤ 1 := hν_min1b.trans (min_le_left _ _)
    obtain ⟨hreg, hwk⟩ := hWeak P hP V hVsol hSmoothAll hVae m hm b hb_pos ν hν0 hν_min1b tr hbuc
    have hcore : clockAge ν b = coreEnd ν b := clockAge_eq_coreEnd hν0 hb_pos
    rw [hcore] at hreg hwk
    refine ⟨ResidualBoundAux.canonicalPhysVel P ν, ResidualBoundAux.canonicalPhysResidual P tr,
      hreg, hwk, fun θ hθ => ?_⟩
    have hθ_ge1 : 1 ≤ θ := le_trans hb_ge1 hθ.1
    have hθ_pos : 0 < θ := lt_of_lt_of_le zero_lt_one hθ_ge1
    obtain ⟨g_θ, hg_eq⟩ : ∃ g : ℝ, g = Real.exp (P.eigenvalue.re * θ) * θ ^ P.kappa.re := ⟨_, rfl⟩
    have hg_pos : 0 < g_θ := by
      rw [hg_eq]; exact mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hθ_pos _)
    have hmul_split :
        ENNReal.ofReal (Real.exp (P.eigenvalue.re * θ) * θ ^ P.kappa.re *
            (clockA ν (clockAge ν θ)) ^ 2 / ‖P.gaugeFactor ν‖) =
          ENNReal.ofReal g_θ *
            ENNReal.ofReal ((clockA ν (clockAge ν θ)) ^ 2 / ‖P.gaugeFactor ν‖) := by
      rw [← hg_eq, mul_div_assoc, ENNReal.ofReal_mul hg_pos.le]
    rw [hmul_split, mul_assoc,
      ResidualBoundAux.rescaled_xNorm_canonicalPhysResidual P tr hν0 hθ_pos]
    have hν3_le1 : ν ^ 3 ≤ 1 := pow_le_one₀ hν0.le hν1
    have hd1 : 1 ≤ dOfTheta ν θ := one_le_dOfTheta hν0 (hν3_le1.trans hθ_ge1)
    have hd_pos : 0 < dOfTheta ν θ := lt_of_lt_of_le zero_lt_one hd1
    obtain ⟨hj, hG₈_bd⟩ := hLong8 θ hθ.1
    have h0_bd := hLong0 θ hθ.1
    rw [← hg_eq] at h0_bd hG₈_bd
    have hf_smooth : ContDiffOn ℝ ∞ (P.canonical θ) (Ioi 0) :=
      hP.canonical.smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
        (fun r hr => ⟨hθ_pos, hr⟩)
    obtain ⟨haesm_G, hnorm_G, _, _, _⟩ :=
      hG_prop (dOfTheta ν θ) hd1 (P.canonical θ) (hP.canonical.memXG θ hθ_pos) hf_smooth (V θ)
        (hVae θ hθ_pos) hj
    obtain ⟨haesm_T, hnorm_T⟩ := hTr_b ν hν_tr tr hbuc θ hθ hj
    have htri : xNorm (dOfTheta ν θ) m
          (fun y => ResidualBoundAux.canonGaussRes P (dOfTheta ν θ) θ y +
            ResidualBoundAux.canonTrainRes P tr (clockAge ν θ) y) ≤
        xNorm (dOfTheta ν θ) m (ResidualBoundAux.canonGaussRes P (dOfTheta ν θ) θ) +
          xNorm (dOfTheta ν θ) m (ResidualBoundAux.canonTrainRes P tr (clockAge ν θ)) :=
      eLpNorm_add_le haesm_G haesm_T (by norm_num)
    obtain ⟨G₈, hG₈_eq⟩ :
        ∃ G : ℝ, G = Real.sqrt (UnforcedLeray.B0121.graphNormSq 8 ⟨V θ, hj⟩) := ⟨_, rfl⟩
    have hG₈_nn : 0 ≤ G₈ := by rw [hG₈_eq]; exact Real.sqrt_nonneg _
    rw [← hG₈_eq] at hG₈_bd
    change xNorm (dOfTheta ν θ) m (ResidualBoundAux.canonGaussRes P (dOfTheta ν θ) θ) ≤
      ENNReal.ofReal (C_g * ((dOfTheta ν θ) ^ (-4 : ℝ) * ‖V θ‖ +
        Real.exp (-2 * a_g * (dOfTheta ν θ) ^ 2) *
          Real.sqrt (UnforcedLeray.B0121.graphNormSq 8 ⟨V θ, hj⟩))) at hnorm_G
    change xNorm (dOfTheta ν θ) m (ResidualBoundAux.canonTrainRes P tr (clockAge ν θ)) ≤
      ENNReal.ofReal (C_tr_b * ν ^ 3 * Real.exp (-2 * a_tr * θ / ν ^ 3) *
        Real.sqrt (UnforcedLeray.B0121.graphNormSq 8 ⟨V θ, hj⟩)) at hnorm_T
    rw [← hG₈_eq] at hnorm_G hnorm_T
    calc ENNReal.ofReal g_θ *
          xNorm (dOfTheta ν θ) m
            (fun y => ResidualBoundAux.canonGaussRes P (dOfTheta ν θ) θ y +
              ResidualBoundAux.canonTrainRes P tr (clockAge ν θ) y)
        ≤ ENNReal.ofReal g_θ *
            (xNorm (dOfTheta ν θ) m (ResidualBoundAux.canonGaussRes P (dOfTheta ν θ) θ) +
              xNorm (dOfTheta ν θ) m (ResidualBoundAux.canonTrainRes P tr (clockAge ν θ))) :=
          mul_le_mul_of_nonneg_left htri (by positivity)
      _ ≤ ENNReal.ofReal g_θ *
            (ENNReal.ofReal (C_g * ((dOfTheta ν θ) ^ (-4 : ℝ) * ‖V θ‖ +
                Real.exp (-2 * a_g * (dOfTheta ν θ) ^ 2) * G₈)) +
              ENNReal.ofReal (C_tr_b * ν ^ 3 * Real.exp (-2 * a_tr * θ / ν ^ 3) * G₈)) :=
          mul_le_mul_of_nonneg_left (add_le_add hnorm_G hnorm_T) (by positivity)
      _ = ENNReal.ofReal (g_θ *
            (C_g * ((dOfTheta ν θ) ^ (-4 : ℝ) * ‖V θ‖ +
                Real.exp (-2 * a_g * (dOfTheta ν θ) ^ 2) * G₈) +
              C_tr_b * ν ^ 3 * Real.exp (-2 * a_tr * θ / ν ^ 3) * G₈)) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_mul hg_pos.le]
      _ ≤ ENNReal.ofReal (C_long * ((ν ^ 3) ^ 2 * θ ^ (-2 : ℝ) +
            ν ^ 3 * Real.exp (-a₀ * θ / ν ^ 3))) :=
          ENNReal.ofReal_le_ofReal
            (ResidualBoundAux.long_window_real_bound hν0 hν1 hθ_ge1 hg_pos hG₈_nn
              hCg_pos hCtr_b hM₀_pos hM₈_pos hKabs_pos ha₀_g ha₀_tr
              (ResidualBoundAux.dOfTheta_sq hν0 hθ_pos.le)
              (ResidualBoundAux.dOfTheta_rpow_neg_four hν0 hθ_pos)
              h0_bd hG₈_bd hKabs hClong_eq)
  · -- Part B: Late / compact window `r ≤ θ ≤ b` (`[coreEnd ν b, clockAge ν r]`)
    intro r hr_pos hrb
    obtain ⟨M₀_r, M₈_r, hM₀r_pos, hM₈r_pos, hComp0, hComp8⟩ := hComp_all r hr_pos hrb
    obtain ⟨C_tr_r, ν_tr_r, hCtr_r, hνtr_r, hTr_r⟩ := hTr_all r hr_pos
    obtain ⟨C_r, hCr_eq⟩ :
        ∃ C : ℝ, C = C_g * M₀_r + (C_g * r⁻¹ * K_abs + C_tr_r) * M₈_r + 1 := ⟨_, rfl⟩
    have hCr_pos : 0 < C_r := by rw [hCr_eq]; positivity
    refine ⟨C_r, a₀, min (min ν_tr_r b⁻¹) (min 1 r), hCr_pos, ha₀_pos,
      lt_min (lt_min hνtr_r (inv_pos.2 hb_pos)) (lt_min zero_lt_one hr_pos),
      fun ν hν tr hbuc => ?_⟩
    have hν0 : 0 < ν := hν.1
    have hν_tr : ν ∈ Ioc 0 ν_tr_r :=
      ⟨hν0, hν.2.trans (le_trans (min_le_left _ _) (min_le_left _ _))⟩
    have hν_binv : ν ≤ b⁻¹ := hν.2.trans (le_trans (min_le_left _ _) (min_le_right _ _))
    have hν_min1r : ν ≤ min 1 r := hν.2.trans (min_le_right _ _)
    have hν1 : ν ≤ 1 := hν_min1r.trans (min_le_left _ _)
    have hν_le_r : ν ≤ r := hν_min1r.trans (min_le_right _ _)
    have hb_le_inv : b ≤ ν⁻¹ := (le_inv_comm₀ hν0 hb_pos).1 hν_binv
    obtain ⟨hreg0, hwk0⟩ :=
      hWeak P hP V hVsol hSmoothAll hVae m hm r hr_pos ν hν0 hν_min1r tr hbuc
    have hs₁_nn : 0 ≤ coreEnd ν b := by
      rw [← clockAge_eq_coreEnd hν0 hb_pos]
      exact clockAge_nonneg hν0 hb_pos hb_le_inv
    have hs₁₂ : coreEnd ν b ≤ clockAge ν r := by
      rw [← clockAge_eq_coreEnd hν0 hb_pos]
      exact ResidualBoundAux.clockAge_antitone hν0 hr_pos hrb
    obtain ⟨hreg_sub, hwk_sub⟩ := ResidualBoundAux.weak_subinterval_of_zero hs₁_nn hs₁₂ hreg0 hwk0
    refine ⟨ResidualBoundAux.canonicalPhysVel P ν, ResidualBoundAux.canonicalPhysResidual P tr,
      hreg_sub, hwk_sub, fun θ hθ => ?_⟩
    have hθ_pos : 0 < θ := lt_of_lt_of_le hr_pos hθ.1
    have hθ_inv : θ ≤ ν⁻¹ := hθ.2.trans hb_le_inv
    rw [ResidualBoundAux.rescaled_xNorm_canonicalPhysResidual P tr hν0 hθ_pos]
    have hν2_le1 : ν ^ 2 ≤ 1 := pow_le_one₀ hν0.le hν1
    have hν3_le_ν : ν ^ 3 ≤ ν := by
      calc ν ^ 3 = ν ^ 2 * ν := by ring
        _ ≤ 1 * ν := mul_le_mul_of_nonneg_right hν2_le1 hν0.le
        _ = ν := one_mul _
    have hd1 : 1 ≤ dOfTheta ν θ := one_le_dOfTheta hν0 ((hν3_le_ν.trans hν_le_r).trans hθ.1)
    have hd_pos : 0 < dOfTheta ν θ := lt_of_lt_of_le zero_lt_one hd1
    obtain ⟨hj, hG₈_bd⟩ := hComp8 θ hθ
    have h0_bd := hComp0 θ hθ
    have hf_smooth : ContDiffOn ℝ ∞ (P.canonical θ) (Ioi 0) :=
      hP.canonical.smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
        (fun ρ hρ => ⟨hθ_pos, hρ⟩)
    obtain ⟨haesm_G, hnorm_G, _, _, _⟩ :=
      hG_prop (dOfTheta ν θ) hd1 (P.canonical θ) (hP.canonical.memXG θ hθ_pos) hf_smooth (V θ)
        (hVae θ hθ_pos) hj
    obtain ⟨haesm_T, hnorm_T⟩ := hTr_r ν hν_tr tr hbuc θ ⟨hθ.1, hθ_inv⟩ hj
    have htri : xNorm (dOfTheta ν θ) m
          (fun y => ResidualBoundAux.canonGaussRes P (dOfTheta ν θ) θ y +
            ResidualBoundAux.canonTrainRes P tr (clockAge ν θ) y) ≤
        xNorm (dOfTheta ν θ) m (ResidualBoundAux.canonGaussRes P (dOfTheta ν θ) θ) +
          xNorm (dOfTheta ν θ) m (ResidualBoundAux.canonTrainRes P tr (clockAge ν θ)) :=
      eLpNorm_add_le haesm_G haesm_T (by norm_num)
    obtain ⟨G₈, hG₈_eq⟩ :
        ∃ G : ℝ, G = Real.sqrt (UnforcedLeray.B0121.graphNormSq 8 ⟨V θ, hj⟩) := ⟨_, rfl⟩
    have hG₈_nn : 0 ≤ G₈ := by rw [hG₈_eq]; exact Real.sqrt_nonneg _
    rw [← hG₈_eq] at hG₈_bd
    change xNorm (dOfTheta ν θ) m (ResidualBoundAux.canonGaussRes P (dOfTheta ν θ) θ) ≤
      ENNReal.ofReal (C_g * ((dOfTheta ν θ) ^ (-4 : ℝ) * ‖V θ‖ +
        Real.exp (-2 * a_g * (dOfTheta ν θ) ^ 2) *
          Real.sqrt (UnforcedLeray.B0121.graphNormSq 8 ⟨V θ, hj⟩))) at hnorm_G
    change xNorm (dOfTheta ν θ) m (ResidualBoundAux.canonTrainRes P tr (clockAge ν θ)) ≤
      ENNReal.ofReal (C_tr_r * ν ^ 3 * Real.exp (-2 * a_tr * θ / ν ^ 3) *
        Real.sqrt (UnforcedLeray.B0121.graphNormSq 8 ⟨V θ, hj⟩)) at hnorm_T
    rw [← hG₈_eq] at hnorm_G hnorm_T
    calc xNorm (dOfTheta ν θ) m
            (fun y => ResidualBoundAux.canonGaussRes P (dOfTheta ν θ) θ y +
              ResidualBoundAux.canonTrainRes P tr (clockAge ν θ) y)
        ≤ ENNReal.ofReal (C_g * ((dOfTheta ν θ) ^ (-4 : ℝ) * ‖V θ‖ +
              Real.exp (-2 * a_g * (dOfTheta ν θ) ^ 2) * G₈)) +
            ENNReal.ofReal (C_tr_r * ν ^ 3 * Real.exp (-2 * a_tr * θ / ν ^ 3) * G₈) :=
          htri.trans (add_le_add hnorm_G hnorm_T)
      _ = ENNReal.ofReal (C_g * ((dOfTheta ν θ) ^ (-4 : ℝ) * ‖V θ‖ +
              Real.exp (-2 * a_g * (dOfTheta ν θ) ^ 2) * G₈) +
            C_tr_r * ν ^ 3 * Real.exp (-2 * a_tr * θ / ν ^ 3) * G₈) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity)]
      _ ≤ ENNReal.ofReal (C_r * ((ν ^ 3) ^ 2 * θ ^ (-2 : ℝ) +
            ν ^ 3 * Real.exp (-a₀ * θ / ν ^ 3))) :=
          ENNReal.ofReal_le_ofReal
            (ResidualBoundAux.compact_window_real_bound hν0 hr_pos hθ.1 hG₈_nn
              hCg_pos hCtr_r hM₀r_pos hM₈r_pos hKabs_pos ha₀_pos ha₀_g ha₀_tr
              (ResidualBoundAux.dOfTheta_sq hν0 hθ_pos.le)
              (ResidualBoundAux.dOfTheta_rpow_neg_four hν0 hθ_pos)
              h0_bd hG₈_bd hKabs hCr_eq)

/-- Conditional assembly of `CTCanonicalResidual` (`PartIII-a:T22/2/2`, composed in
`ResidualBound.lean`) from the three leaves:
* `PartIII-a:T22/2/2/1`: `∀ P : PlanarData, IsPlanarReference P → HasCanonicalSolutionRep P`
* `PartIII-a:T22/2/2/2`: `ResidualBoundAux.CanonicalColumnWeakEq`
* `PartIII-a:T22/2/2/3`: `ResidualBoundAux.CanonicalGaussAndJetBound` -/
theorem ctCanonicalResidual_of
    (hRep : ∀ P : PlanarData, IsPlanarReference P → HasCanonicalSolutionRep P)
    (hWeak : ResidualBoundAux.CanonicalColumnWeakEq)
    (hGauss : ResidualBoundAux.CanonicalGaussAndJetBound) :
    CTCanonicalResidual :=
  fun P hP m hm => ctCanonicalResidual_at P hP (hRep P hP) hWeak hGauss m hm

end UnforcedLeray.Short.IIIa.T22Sub
