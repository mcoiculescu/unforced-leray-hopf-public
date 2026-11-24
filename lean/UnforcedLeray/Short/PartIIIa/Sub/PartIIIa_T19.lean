import UnforcedLeray.Short.PartIIIa.FlatCausal
import UnforcedLeray.Short.PartIIIa.ComposeCorollary
import UnforcedLeray.Short.PartIIIa.Targets
import UnforcedLeray.Short.PartIIIa.T05_HardyKernel
import UnforcedLeray.Short.PartIIIa.Sub.T18
import UnforcedLeray.Short.PartIIIa.Sub.T18_3
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Lin

/-!
# Part III-a, task `PartIII-a:T19`: the polynomial causal inverse (`prop:short-polynomial-causal`)

Source of record: `the November 2 reference manuscript` (SP), lines 3426-3546.
Target (`FlatCausal.lean`):
`theorem polyCausal (hClock : FullClockWeakForward) (hFree : FreeCausalExistsUnique) (hHardy : HardyKernel) : PolyCausal`.

## Proof structure (SP 3442-3546)

Fix `m = 9 > 8` and let `b = max b₀ 1 ≥ 1` where `b₀` is the threshold of `prop:short-full-clock`
(`FullClockWeakForward`), with core endpoint `H = coreEnd ν b = ν⁻¹((νb)⁻¹ - 1)` and weak-source
degree `M_s = weakDegree 9 P.kappa`.

* **(P1) Free causal solution on `(0, ∞)`** (`free_causal_step`, proved here from
  `hFree : FreeCausalExistsUnique` and `kStar_ge`): for `T = g⁻¹F`, `u₀ = g⁻¹b₀` solves the free
  equation with `‖u₀‖_𝓗 + ‖∇u₀‖_𝒯 ≤ 2ν⁻¹‖T‖_𝒯` and `‖u₀‖_𝓗 + √ν‖∇u₀‖_𝒯 ≤ 2ν^{-1/2}‖T‖_𝒯`.
* **(P2) Core train coefficient bound** (`TrainCoreCoeffBound`, task `PartIII-a:T19/1`, SP 3466-3476):
  from the actual train transverse tail `sct:transverse` on `0 < s ≤ H`,
  `sup_{s≤H} ‖⟨x⟩^9(v, ∇v)(s)‖_∞ ≤ C ν^{-p_m}`.
* **(P3) Forward vorticity propagation and Hardy kernel bound on `(0, H)`** (`hardy_core_clock_bound`,
  proved here from `hHardy : HardyKernel` and `t05_integrableOn_beta`): using `1 + (s-t)^{-1/2} ≤
  (1 + √H)(s-t)^{-1/2}` on `0 < t < s < H` and the uniform beta bound `B(Re μ + 3/4, 1/2) ≤ B₀`
  for `Re μ > 0`, the `FullClockWeakForward` pointwise bound (`ClockBoundAt`) integrates to an
  `L²(s^{-3/2}ds; X_{9,c})` bound on `ω(s) = ∫_0^s (t/s)^μ (g(t)/g(s)) U(s,t) f(t) dt` with cost
  `C ν^{-M_s}(1 + √H) ≤ 2C ν^{-M_s - 1}`.
* **(P4) Core Biot-Savart reconstruction and velocity equation on `(0, H)`** (`CoreDuhamelBiotSavart`,
  task `PartIII-a:T19/2`, SP 3497-3515): `u_core = u₀ + K_c ω` satisfies `IsCoreCausalSolution` on
  `(0, H)` with `‖K_c ω‖_{H^1} ≤ C_m(1 + c)‖ω‖_{X_m}`, yielding the core energy bound with exponent
  `M_s + p_m + 5` (SP 3507-3509).
* **(P5) Tail energy continuation on `(H, ∞)`** (`TailEnergyContinuation`, task `PartIII-a:T19/3`,
  SP 3517-3540): selecting a strong trace time in `[H - 1, H - 1/2]` and continuing via the exact tail
  energy inequality `(AE)' + 2k_*AE/s + 2hAE + νAs^{-1/2}‖∇u‖² ≤ ν⁻¹As^{-1/2}‖T‖²` with
  `∫_H^∞ L ≤ Cb + Cν³` (`sct:integrated`) produces a global solution `(b, G)` on `(0, ∞)` at an
  additional polynomial cost `C_tail ν⁻¹`, giving total exponent `M = M_s + p_m + 6` (SP 3539).
* **(P6) Uniqueness** (`unique_of_homogeneous_zero`, proved here from `causalSolSub` and
  `TrainCausalHomogeneousZero` [task `PartIII-a:T19/4`], SP 3541-3545): the homogeneous difference
  vanishes by the tail energy inequality on `[δ_j, B]` as `δ_j ↓ 0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## Core-restricted norms and solution class on `(0, H)` -/

/-- `‖b‖_{𝓗(0, H)}`, the `𝓗` norm restricted to ages `s < H` (SP 3507). -/
def hCalNormOn (c H : ℝ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) : ℝ≥0∞ :=
  eLpNorm (fun p => vnorm2 (b p)) 2 ((ageμ c (-3 / 2)).restrict (Iio H ×ˢ univ))

/-- `‖T‖_{𝒯(0, H)}`, the `𝒯` norm restricted to ages `s < H` (SP 3508). -/
def tCalNormOn (c H : ℝ) (T : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) : ℝ≥0∞ :=
  eLpNorm (fun p => tnorm2 (T p)) 2 ((ageμ c (-1 / 2)).restrict (Iio H ×ˢ univ))

theorem hCalNormOn_le_hCalNorm (c H : ℝ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) :
    hCalNormOn c H b ≤ hCalNorm c b :=
  eLpNorm_mono_measure _ Measure.restrict_le_self

theorem tCalNormOn_le_tCalNorm (c H : ℝ) (T : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) :
    tCalNormOn c H T ≤ tCalNorm c T :=
  eLpNorm_mono_measure _ Measure.restrict_le_self

/-- The causal zero-entrance energy class and weak equation restricted to the core `(0, H)`
(SP 3490-3515): all clauses of `IsCausalEnergySolution` on `0 < s < H`, tested against flat tests
supported in `(0, H)`. -/
structure IsCoreCausalSolution (c ν H : ℝ) (μ : ℂ) (vel : ℝ → ℝ × ℝ → Fin 2 → ℝ)
    (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) : Prop where
  measurable : ∀ i, Measurable fun p => b p i
  gradMeasurable : ∀ i j, Measurable fun p => G p i j
  energyLoc : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ → s₂ < H →
    ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (vnorm2 (b p) ^ 2 + tnorm2 (G p) ^ 2) < ⊤
  zeroEntrance : ∃ δ : ℝ, 0 < δ ∧ ∫⁻ p, ENNReal.ofReal (vnorm2 (b p) ^ 2)
    ∂((ageμ c (-3 / 2)).restrict (Ioo 0 δ ×ˢ univ)) < ⊤
  divFree : ∀ s ∈ Ioo (0 : ℝ) H, ∀ ψ, B0579.IsCylTest c ψ →
    ∫ x in B0579.cell c, (b (s, x) 0 * (B0579.pd 0 ψ x : ℂ) + b (s, x) 1 * (B0579.pd 1 ψ x : ℂ)) = 0
  weakGrad : ∀ s ∈ Ioo (0 : ℝ) H, ∀ i j,
    HasWeakCellDerivC c j (fun x => b (s, x) i) (fun x => G (s, x) i j)
  integrable : ∀ Φ, IsFlatTest c Φ → (∀ s x i, H ≤ s → Φ s x i = 0) →
    IntegrableOn (flatIntegrand ν μ vel F b Φ) (Ioi (0 : ℝ) ×ˢ B0579.cell c)
  weak : ∀ Φ, IsFlatTest c Φ → (∀ s x i, H ≤ s → Φ s x i = 0) →
    ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, flatIntegrand ν μ vel F b Φ p = 0

/-- The weak-forward clock estimate at fixed `(P, m, b, C_clock, ν, tr)` (inner clause of
`FullClockWeakForward`, `FullClock.lean`). -/
def ClockBoundAt (P : PlanarData) (m b C_clock ν : ℝ)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) : Prop :=
  ∀ t s : ℝ, 0 < t → t < s → s ≤ coreEnd ν b →
    ∀ f : ℝ × ℝ → ℂ, MemLp f 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) →
      HasZeroCirculation (ν ^ (-2 : ℝ)) f →
      ∀ w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t f w u →
        ENNReal.ofReal (gainG P.eigenvalue.re ν t / gainG P.eigenvalue.re ν s) *
            xNorm (ν ^ (-2 : ℝ)) m (w s) ≤
          ENNReal.ofReal (C_clock * ν ^ (-(weakDegree m P.kappa : ℝ)) *
              (1 + (s - t) ^ (-1 / 2 : ℝ))) *
            negNorm (ν ^ (-2 : ℝ)) m f

/-! ## Core endpoint arithmetic (`H = coreEnd ν b`, SP 2829, 3444, 3488) -/

/-- For `b ≥ 1` and `0 < ν ≤ min (1/2) ((2b)⁻¹)`, `1 < coreEnd ν b ≤ ν⁻²` and
`1 + √(coreEnd ν b) ≤ 2ν⁻¹`. -/
theorem coreEnd_bounds {b ν : ℝ} (hb : 1 ≤ b) (hν0 : 0 < ν) (hν1 : ν ≤ 1 / 2)
    (hνb : ν ≤ (2 * b)⁻¹) :
    1 < coreEnd ν b ∧ coreEnd ν b ≤ ν ^ (-2 : ℝ) ∧
      Real.sqrt (coreEnd ν b) ≤ ν⁻¹ ∧ 1 + Real.sqrt (coreEnd ν b) ≤ 2 * ν⁻¹ := by
  have hbpos : 0 < b := by linarith
  have hνb_le : ν * b ≤ 1 / 2 := by
    calc ν * b ≤ (2 * b)⁻¹ * b := mul_le_mul_of_nonneg_right hνb hbpos.le
      _ = 1 / 2 := by field_simp
  have hinv_ge : 2 ≤ (ν * b)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) (mul_pos hν0 hbpos)]
    linarith
  have hνinv_ge : 2 ≤ ν⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hν0]
    linarith
  have hH_gt : 1 < coreEnd ν b := by
    unfold coreEnd
    have : 2 * 1 ≤ ν⁻¹ * ((ν * b)⁻¹ - 1) :=
      mul_le_mul hνinv_ge (by linarith) zero_le_one (by positivity)
    linarith
  have hinv_le : (ν * b)⁻¹ ≤ ν⁻¹ := by
    rw [mul_inv]
    have : b⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hb
    nlinarith [inv_pos.2 hν0]
  have hH_le_sq : coreEnd ν b ≤ (ν⁻¹) ^ 2 := by
    unfold coreEnd
    have : (ν * b)⁻¹ - 1 ≤ ν⁻¹ := by linarith
    calc ν⁻¹ * ((ν * b)⁻¹ - 1) ≤ ν⁻¹ * ν⁻¹ :=
          mul_le_mul_of_nonneg_left this (inv_nonneg.2 hν0.le)
      _ = (ν⁻¹) ^ 2 := (sq _).symm
  have hH_le : coreEnd ν b ≤ ν ^ (-2 : ℝ) := by
    refine hH_le_sq.trans_eq ?_
    rw [← Real.rpow_neg_one, ← Real.rpow_natCast, ← Real.rpow_mul hν0.le]
    norm_num
  have hsqrt : Real.sqrt (coreEnd ν b) ≤ ν⁻¹ := by
    calc Real.sqrt (coreEnd ν b) ≤ Real.sqrt ((ν⁻¹) ^ 2) := Real.sqrt_le_sqrt hH_le_sq
      _ = ν⁻¹ := Real.sqrt_sq (inv_nonneg.2 hν0.le)
  refine ⟨hH_gt, hH_le, hsqrt, by linarith⟩

/-! ## Step (P1): Free causal solution bounds (`FreeCausalExistsUnique`, SP 3447-3455) -/

/-- From `FreeCausalExistsUnique` and `k_* ≥ 1/4` (`kStar_ge`), for `0 < ν ≤ min ν_free 1` the free
solution `(b₀, G₀)` satisfies `‖g⁻¹b₀‖_𝓗 + ‖g⁻¹G₀‖_𝒯 ≤ 2ν⁻¹‖g⁻¹F‖_𝒯` and
`‖g⁻¹b₀‖_𝓗 + √ν‖g⁻¹G₀‖_𝒯 ≤ 2ν^{-1/2}‖g⁻¹F‖_𝒯`. -/
private theorem free_causal_step (hFree : FreeCausalExistsUnique) (P : PlanarData)
    (hP : IsPlanarReference P) (K : Set ℂ) (hK : IsAdmissibleK K) :
    ∃ ν_free : ℝ, 0 < ν_free ∧ ∀ ν ∈ Ioc 0 (min ν_free 1), ∀ μ ∈ K,
      ∀ F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ, (∀ p i j, F p i j = F p j i) →
        (∀ i j, Measurable fun p => F p i j) →
        tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν F) < ⊤ →
        ∃ b₀ G₀, IsCausalEnergySolution (ν ^ (-2 : ℝ)) ν μ (fun _ _ _ => 0) F b₀ G₀ ∧
          hCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν b₀) +
              tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν G₀) ≤
            ENNReal.ofReal (2 * ν⁻¹) *
              tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν F) ∧
          hCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν b₀) +
              ENNReal.ofReal (Real.sqrt ν) *
                tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν G₀) ≤
            ENNReal.ofReal (2 * ν ^ (-1 / 2 : ℝ)) *
              tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν F) := by
  obtain ⟨ν_free, hν_free, hF⟩ := hFree P hP K hK
  refine ⟨ν_free, hν_free, fun ν hν μ hμ F hsym hmeas hfin => ?_⟩
  have hν0 : 0 < ν := hν.1
  have hν1 : ν ≤ 1 := hν.2.trans (min_le_right _ _)
  have hνf : ν ∈ Ioc 0 ν_free := ⟨hν0, hν.2.trans (min_le_left _ _)⟩
  obtain ⟨b₀, G₀, hsol, hb₀, hG₀, -⟩ := hF ν hνf μ hμ F hsym hmeas hfin
  have hk : (1 / 4 : ℝ) ≤ ⨅ μ' : K, μ'.1.re + 1 / 4 :=
    kStar_ge hμ (fun μ' hμ' => (hK.2 μ' hμ').1)
  have hsqrt_ge : Real.sqrt ν ≤ 2 * Real.sqrt ((⨅ μ' : K, μ'.1.re + 1 / 4) * ν) := by
    calc Real.sqrt ν = 2 * Real.sqrt (1 / 4 * ν) := by
          rw [Real.sqrt_mul (by norm_num), Real.sqrt_div (by norm_num), Real.sqrt_one]
          ring
      _ ≤ 2 * Real.sqrt ((⨅ μ' : K, μ'.1.re + 1 / 4) * ν) := by
          gcongr
  have hinv_le_rpow : (2 * Real.sqrt ((⨅ μ' : K, μ'.1.re + 1 / 4) * ν))⁻¹ ≤ ν ^ (-1 / 2 : ℝ) := by
    calc (2 * Real.sqrt ((⨅ μ' : K, μ'.1.re + 1 / 4) * ν))⁻¹
        ≤ (Real.sqrt ν)⁻¹ := inv_anti₀ (Real.sqrt_pos.2 hν0) hsqrt_ge
      _ = ν ^ (-1 / 2 : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hν0.le]
        ring_nf
  have hrpow_le_inv : ν ^ (-1 / 2 : ℝ) ≤ ν⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_ge hν0 hν1 (by norm_num)
  have hsqrt_mul_inv : Real.sqrt ν * ν⁻¹ = ν ^ (-1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_add hν0]
    norm_num
  set TF := tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν F)
  have hb₀_rpow : hCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν b₀) ≤
      ENNReal.ofReal (ν ^ (-1 / 2 : ℝ)) * TF :=
    hb₀.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hinv_le_rpow) bot_le)
  have hb₀_inv : hCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν b₀) ≤
      ENNReal.ofReal ν⁻¹ * TF :=
    hb₀_rpow.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hrpow_le_inv) bot_le)
  have hG₀_rpow : ENNReal.ofReal (Real.sqrt ν) *
      tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν G₀) ≤
      ENNReal.ofReal (ν ^ (-1 / 2 : ℝ)) * TF := by
    calc ENNReal.ofReal (Real.sqrt ν) * tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν G₀)
        ≤ ENNReal.ofReal (Real.sqrt ν) * (ENNReal.ofReal ν⁻¹ * TF) :=
          mul_le_mul_of_nonneg_left hG₀ bot_le
      _ = ENNReal.ofReal (ν ^ (-1 / 2 : ℝ)) * TF := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _), hsqrt_mul_inv]
  refine ⟨b₀, G₀, hsol, ?_, ?_⟩
  · calc hCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν b₀) +
          tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν G₀)
        ≤ ENNReal.ofReal ν⁻¹ * TF + ENNReal.ofReal ν⁻¹ * TF := add_le_add hb₀_inv hG₀
      _ = ENNReal.ofReal (2 * ν⁻¹) * TF := by
          rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity), two_mul]
  · calc hCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν b₀) +
          ENNReal.ofReal (Real.sqrt ν) *
            tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν G₀)
        ≤ ENNReal.ofReal (ν ^ (-1 / 2 : ℝ)) * TF + ENNReal.ofReal (ν ^ (-1 / 2 : ℝ)) * TF :=
          add_le_add hb₀_rpow hG₀_rpow
      _ = ENNReal.ofReal (2 * ν ^ (-1 / 2 : ℝ)) * TF := by
          rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity), two_mul]

/-! ## Step (P3): Uniform Beta bound and Hardy + constant-kernel bound on `(0, H)` (SP 3482-3496) -/

/-- The uniform Beta constant `B(3/4, 1/2) = ∫_0^1 u^{-1/4}(1-u)^{-1/2}du` bounding
`B(Re μ + 3/4, 1/2)` for all `Re μ > 0`. -/
private def betaConst : ℝ := ∫ u in Ioo (0 : ℝ) 1, u ^ (-1 / 4 : ℝ) * (1 - u) ^ (-1 / 2 : ℝ)

private theorem betaConst_nonneg : 0 ≤ betaConst := by
  unfold betaConst
  refine setIntegral_nonneg measurableSet_Ioo fun u hu => ?_
  exact mul_nonneg (Real.rpow_nonneg hu.1.le _) (Real.rpow_nonneg (sub_pos.2 hu.2).le _)

private theorem beta_le_betaConst {σ : ℝ} (hσ : 0 < σ) :
    ∫ u in Ioo (0 : ℝ) 1, u ^ (σ + 3 / 4 - 1) * (1 - u) ^ (-1 / 2 : ℝ) ≤ betaConst := by
  unfold betaConst
  refine setIntegral_mono_on (t05_integrableOn_beta (by linarith) (by norm_num))
    (t05_integrableOn_beta (by norm_num) (by norm_num)) measurableSet_Ioo fun u hu => ?_
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (sub_pos.2 hu.2).le _)
  exact Real.rpow_le_rpow_of_exponent_ge hu.1 hu.2.le (by linarith)

/-- On `0 < t < s < H`, `1 + (s - t)^{-1/2} ≤ (1 + √H)(s - t)^{-1/2}` (SP 3488: "The kernel `1` on
`s < H` costs an additional `√H`"). -/
private theorem kernel_one_add_rpow_le {t s H : ℝ} (ht : 0 < t) (hts : t < s) (hsH : s < H) :
    1 + (s - t) ^ (-1 / 2 : ℝ) ≤ (1 + Real.sqrt H) * (s - t) ^ (-1 / 2 : ℝ) := by
  have hst : 0 < s - t := sub_pos.2 hts
  have hstH : s - t ≤ H := by linarith
  have hpos : 0 < (s - t) ^ (-1 / 2 : ℝ) := Real.rpow_pos_of_pos hst _
  have h1 : 1 ≤ Real.sqrt H * (s - t) ^ (-1 / 2 : ℝ) := by
    calc (1 : ℝ) = (s - t) ^ (1 / 2 : ℝ) * (s - t) ^ (-1 / 2 : ℝ) := by
          rw [← Real.rpow_add hst]; norm_num
      _ = Real.sqrt (s - t) * (s - t) ^ (-1 / 2 : ℝ) := by rw [Real.sqrt_eq_rpow]
      _ ≤ Real.sqrt H * (s - t) ^ (-1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hstH) hpos.le
  linarith

/-- **Core Hardy + weak-clock kernel bound** (SP 3482-3496), proved from `hHardy : HardyKernel`.
For `σ > 0`, `H > 0`, `D ≥ 0` and measurable `N : ℝ → ℝ≥0∞`, any profile `W : ℝ → ℝ≥0∞` satisfying
`W(s) ≤ ∫_0^s D (t/s)^σ (1 + (s-t)^{-1/2}) N(t) dt` on `s ∈ (0, H)` satisfies
`(∫_0^H s^{-3/2} W(s)² ds)^{1/2} ≤ B₀ D (1 + √H) (∫_0^H t^{-1/2} N(t)² dt)^{1/2}`. -/
private theorem hardy_core_clock_bound (hHardy : HardyKernel) {σ H D : ℝ} (hσ : 0 < σ) (hH : 0 < H)
    (hD : 0 ≤ D) {N W : ℝ → ℝ≥0∞} (hN : Measurable N)
    (hW : ∀ s ∈ Ioo (0 : ℝ) H,
      W s ≤ ∫⁻ t in Ioo (0 : ℝ) s,
        ENNReal.ofReal (D * (t / s) ^ σ * (1 + (s - t) ^ (-1 / 2 : ℝ))) * N t) :
    (∫⁻ s in Ioo (0 : ℝ) H, ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * W s ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (betaConst * D * (1 + Real.sqrt H)) *
        (∫⁻ t in Ioo (0 : ℝ) H, ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) * N t ^ (2 : ℝ)) ^
          (1 / 2 : ℝ) := by
  set NH : ℝ → ℝ≥0∞ := (Ioo (0 : ℝ) H).indicator N
  have hNH : Measurable NH := hN.indicator measurableSet_Ioo
  set K : ℝ := D * (1 + Real.sqrt H)
  have hK0 : 0 ≤ K := mul_nonneg hD (by positivity)
  have hpt : ∀ s ∈ Ioo (0 : ℝ) H,
      W s ≤ ENNReal.ofReal K * ∫⁻ t in Ioo (0 : ℝ) s,
        ENNReal.ofReal ((t / s) ^ σ * (s - t) ^ (-1 / 2 : ℝ)) * NH t := by
    intro s hs
    refine (hW s hs).trans ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Ioo fun t ht => ?_
    have htH : t ∈ Ioo (0 : ℝ) H := ⟨ht.1, ht.2.trans hs.2⟩
    have hNHt : NH t = N t := indicator_of_mem htH _
    rw [hNHt, ← mul_assoc, ← ENNReal.ofReal_mul hK0]
    refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
    have hts_pos : 0 ≤ D * (t / s) ^ σ :=
      mul_nonneg hD (Real.rpow_nonneg (div_pos ht.1 hs.1).le _)
    have hker := kernel_one_add_rpow_le ht.1 ht.2 hs.2
    calc D * (t / s) ^ σ * (1 + (s - t) ^ (-1 / 2 : ℝ))
        ≤ D * (t / s) ^ σ * ((1 + Real.sqrt H) * (s - t) ^ (-1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hker hts_pos
      _ = K * ((t / s) ^ σ * (s - t) ^ (-1 / 2 : ℝ)) := by unfold K; ring
  have hsq : ∫⁻ s in Ioo (0 : ℝ) H, ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * W s ^ (2 : ℝ) ≤
      ENNReal.ofReal K ^ (2 : ℝ) *
        ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) *
          (∫⁻ t in Ioo (0 : ℝ) s,
            ENNReal.ofReal ((t / s) ^ σ * (s - t) ^ (-1 / 2 : ℝ)) * NH t) ^ (2 : ℝ) := by
    calc ∫⁻ s in Ioo (0 : ℝ) H, ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * W s ^ (2 : ℝ)
        ≤ ∫⁻ s in Ioo (0 : ℝ) H, ENNReal.ofReal K ^ (2 : ℝ) *
            (ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) *
              (∫⁻ t in Ioo (0 : ℝ) s,
                ENNReal.ofReal ((t / s) ^ σ * (s - t) ^ (-1 / 2 : ℝ)) * NH t) ^ (2 : ℝ)) := by
          refine setLIntegral_mono' measurableSet_Ioo fun s hs => ?_
          have h1 := ENNReal.rpow_le_rpow (hpt s hs) (by norm_num : (0 : ℝ) ≤ 2)
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)] at h1
          calc ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * W s ^ (2 : ℝ)
              ≤ ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) *
                  (ENNReal.ofReal K ^ (2 : ℝ) *
                    (∫⁻ t in Ioo (0 : ℝ) s,
                      ENNReal.ofReal ((t / s) ^ σ * (s - t) ^ (-1 / 2 : ℝ)) * NH t) ^ (2 : ℝ)) :=
                mul_le_mul_of_nonneg_left h1 bot_le
            _ = _ := by ring
      _ = ENNReal.ofReal K ^ (2 : ℝ) *
            ∫⁻ s in Ioo (0 : ℝ) H, ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) *
              (∫⁻ t in Ioo (0 : ℝ) s,
                ENNReal.ofReal ((t / s) ^ σ * (s - t) ^ (-1 / 2 : ℝ)) * NH t) ^ (2 : ℝ) := by
          rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)]
      _ ≤ _ := mul_le_mul_of_nonneg_left (lintegral_mono_set Ioo_subset_Ioi_self) bot_le
  have hrpow := ENNReal.rpow_le_rpow hsq (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul,
    show (2 : ℝ) * (1 / 2 : ℝ) = 1 by norm_num, ENNReal.rpow_one] at hrpow
  have hH_app := hHardy σ (by linarith) NH hNH
  have hNH_int : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) * NH t ^ (2 : ℝ) =
      ∫⁻ t in Ioo (0 : ℝ) H, ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) * N t ^ (2 : ℝ) := by
    rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioo]
    congr 1 with t
    by_cases htH : t ∈ Ioo (0 : ℝ) H
    · have ht0 : t ∈ Ioi (0 : ℝ) := htH.1
      simp [NH, htH, ht0]
    · by_cases ht0 : t ∈ Ioi (0 : ℝ) <;> simp [NH, htH, ht0]
  rw [hNH_int] at hH_app
  have hbeta : ENNReal.ofReal (∫ u in Ioo (0 : ℝ) 1, u ^ (σ + 3 / 4 - 1) * (1 - u) ^ (-1 / 2 : ℝ)) ≤
      ENNReal.ofReal betaConst :=
    ENNReal.ofReal_le_ofReal (beta_le_betaConst hσ)
  calc (∫⁻ s in Ioo (0 : ℝ) H, ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * W s ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
      ≤ ENNReal.ofReal K *
          (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) *
            (∫⁻ t in Ioo (0 : ℝ) s,
              ENNReal.ofReal ((t / s) ^ σ * (s - t) ^ (-1 / 2 : ℝ)) * NH t) ^ (2 : ℝ)) ^
            (1 / 2 : ℝ) := hrpow
    _ ≤ ENNReal.ofReal K *
          (ENNReal.ofReal betaConst *
            (∫⁻ t in Ioo (0 : ℝ) H, ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) * N t ^ (2 : ℝ)) ^
              (1 / 2 : ℝ)) := by
        refine mul_le_mul_of_nonneg_left (hH_app.trans ?_) bot_le
        exact mul_le_mul_of_nonneg_right hbeta bot_le
    _ = ENNReal.ofReal (betaConst * D * (1 + Real.sqrt H)) *
          (∫⁻ t in Ioo (0 : ℝ) H, ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) * N t ^ (2 : ℝ)) ^
            (1 / 2 : ℝ) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hK0]
        congr 2
        unfold K
        ring

/-! ## Step (P6): Uniqueness from homogeneous vanishing (`causalSolSub`, SP 3541-3545) -/

/-- **Step (P6): Homogeneous vanishing for the linearised equation around the train**
(`PartIII-a:T19/4`, SP 3541-3545).
For any causal zero-entrance energy solution `(d, Gd)` with force `0` around a BUC train `tr` and
`μ ∈ K` (`Re μ > 0`), the weighted energy inequality `(AE)' + 2k_*AE/s + 2hAE + νAs^{-1/2}‖∇u‖² ≤ 0`
with `A(s) = exp(-2∫_0^s ‖sym ∇v‖_∞) > 0` on `[δ_j, B]` as `δ_j ↓ 0` yields `‖g⁻¹d‖_𝓗 = 0`. -/
def TrainCausalHomogeneousZero : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ K : Set ℂ, IsAdmissibleK K →
    ∀ ν : ℝ, 0 < ν → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ μ ∈ K,
      ∀ d Gd, IsCausalEnergySolution (ν ^ (-2 : ℝ)) ν μ (trainVel tr) (fun _ _ _ => 0) d Gd →
        hCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν d) = 0

/-- Uniqueness of causal zero-entrance energy solutions around `trainVel tr`, proved from
`causalSolSub` (`T18_FreeCausal/Lin.lean`) and `TrainCausalHomogeneousZero`. -/
private theorem unique_of_homogeneous_zero (hHom : TrainCausalHomogeneousZero)
    {P : PlanarData} (hP : IsPlanarReference P) {K : Set ℂ} (hK : IsAdmissibleK K)
    {ν : ℝ} (hν : 0 < ν) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr) {μ : ℂ} (hμ : μ ∈ K)
    {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {b b' : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G G' : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hsol : IsCausalEnergySolution (ν ^ (-2 : ℝ)) ν μ (trainVel tr) F b G)
    (hsol' : IsCausalEnergySolution (ν ^ (-2 : ℝ)) ν μ (trainVel tr) F b' G') :
    b' =ᵐ[volume.restrict (Ioi (0 : ℝ) ×ˢ B0579.cell (ν ^ (-2 : ℝ)))] b := by
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hdiff := causalSolSub (ν ^ (-2 : ℝ)) ν μ (trainVel tr) F F b' b G' G hsol' hsol
  have hF0 : (fun (p : ℝ × (ℝ × ℝ)) (i j : Fin 2) => F p i j - F p i j) =
      fun _ _ _ => (0 : ℂ) := by
    funext p i j
    exact sub_self _
  rw [hF0] at hdiff
  have h0 := hHom P hP K hK ν hν tr htr μ hμ
    (fun p i => b' p i - b p i) (fun p i j => G' p i j - G p i j) hdiff
  unfold hCalNorm at h0
  have hm : Measurable fun p : ℝ × (ℝ × ℝ) =>
      vnorm2 (gainConj P.eigenvalue.re ν (fun p i => b' p i - b p i) p) :=
    measurable_vnorm2_gainConj P.eigenvalue.re ν fun i => (hsol'.measurable i).sub (hsol.measurable i)
  have hae := (eLpNorm_eq_zero_iff hm.aestronglyMeasurable (by norm_num)).1 h0
  have hae' : b' =ᵐ[ageμ (ν ^ (-2 : ℝ)) (-3 / 2)] b := by
    filter_upwards [hae] with p hp
    have hp' : vnorm2 (gainConj P.eigenvalue.re ν (fun p i => b' p i - b p i) p) = 0 := hp
    have := eq_zero_of_vnorm2_gainConj hp'
    funext i
    have hi := congrFun this i
    simpa [sub_eq_zero] using hi
  exact (restrict_ac_ageμ hc).ae_eq hae'

/-! ## Remaining leaf statements for Steps (P2), (P4), (P5) -/

/-- **Step (P2): Polynomial train coefficient bound on the core `(0, H)`** (`PartIII-a:T19/1`,
SP 3466-3476).
For `m = 9` and any fixed `b ≥ 1`, there exist a degree `p_m : ℕ` and `C_coeff, ν_coeff > 0` such
that for `0 < ν ≤ ν_coeff` and every BUC train `tr` at `c = ν⁻²`, on `0 < s ≤ coreEnd ν b` and
`x ∈ B0579.cell c`:
`⟨x⟩^9 (‖v(s, x)‖ + ‖Dv(s, x)‖) ≤ C_coeff ν^{-p_m}`.
Follows from `PartI.TrainTransverseTails` (`sct:transverse`, SP 460-467) with `S_* = coreEnd ν b =
O(ν⁻²)` and `c = ν⁻²`, together with `PartI.TrainComparison` (`sct:comparison`, SP 291-303) and
`Train.Vc_bounds` on the interior band `|η| ≤ C'/ν + 2`. -/
def TrainCoreCoeffBound : Prop :=
  ∀ b : ℝ, 1 ≤ b → ∃ (p_m : ℕ) (C_coeff ν_coeff : ℝ), 0 ≤ C_coeff ∧ 0 < ν_coeff ∧
    ∀ ν ∈ Ioc 0 ν_coeff, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ s ∈ Ioc (0 : ℝ) (coreEnd ν b), ∀ x ∈ B0579.cell (ν ^ (-2 : ℝ)),
        B0579.bracket x ^ (9 : ℝ) * (‖tr.v s x‖ + ‖fderiv ℝ (tr.v s) x‖) ≤
          C_coeff * ν ^ (-(p_m : ℝ))

/-- **Steps (P2-duality), (P3-Duhamel), and (P4): Core Duhamel propagation and Biot-Savart velocity**
(`PartIII-a:T19/2`, SP 3462-3515). Given a planar reference `P`, admissible `K`, core parameter
`b ≥ 1`, train `tr` with core coefficient bound `A_m` on `(0, H)` (`H = coreEnd ν b`) and
weak-forward clock bound `ClockBoundAt P 9 b C_clock ν tr`, and the free causal solution `(b₀, G₀)`
of `F`, there exist a measurable normalized `Z^{-1}_{9,c}` source profile `N : ℝ → ℝ≥0∞`, a
normalized `X_{9,c}` Duhamel vorticity profile `W : ℝ → ℝ≥0∞`, and a core solution `(b_core, G_core)`
of `IsCoreCausalSolution` on `(0, H)` such that:
1. `(∫_0^H t^{-1/2} N(t)² dt)^{1/2} ≤ C_dual A_m (‖g⁻¹b₀‖_𝓗 + ‖g⁻¹G₀‖_𝒯)` (testing
   `f = -curl(v·∇u₀ + u₀·∇v)` against `H^1_{-9,c}` with `c^{-1/2}` cell normalization, SP 3456-3480);
2. `W(s) ≤ ∫_0^s |C_clock| ν^{-M_s} (t/s)^{Re μ} (1 + (s-t)^{-1/2}) N(t) dt` on `s ∈ (0, H)`
   (Minkowski and `ClockBoundAt` applied to `ω(s) = ∫_0^s (t/s)^μ (g(t)/g(s)) U(s,t) f(t) dt`,
   SP 3490-3496);
3. `‖g⁻¹b_core‖_{𝓗(0,H)} + √ν‖g⁻¹G_core‖_{𝒯(0,H)} ≤ (‖g⁻¹b₀‖_𝓗 + √ν‖g⁻¹G₀‖_𝒯) +
   C_BS (1 + c)(1 + √(νH)) (∫_0^H s^{-3/2} W(s)² ds)^{1/2}` (Biot-Savart `‖K_c ω‖_{H^1} ≤
   C_m(1 + c)‖ω‖_{X_m}` and `s^{-1/2} ≤ H s^{-3/2}` on `(0, H)`, SP 3497-3515). -/
def CoreDuhamelBiotSavart : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ K : Set ℂ, IsAdmissibleK K →
    ∀ b : ℝ, 1 ≤ b → ∃ (C_dual C_BS ν_core : ℝ), 0 ≤ C_dual ∧ 0 ≤ C_BS ∧ 0 < ν_core ∧
      ∀ ν ∈ Ioc 0 ν_core, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
        UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ μ ∈ K,
        ∀ A_m C_clock : ℝ, 0 ≤ A_m →
          (∀ s ∈ Ioc (0 : ℝ) (coreEnd ν b), ∀ x ∈ B0579.cell (ν ^ (-2 : ℝ)),
            B0579.bracket x ^ (9 : ℝ) * (‖tr.v s x‖ + ‖fderiv ℝ (tr.v s) x‖) ≤ A_m) →
          ClockBoundAt P 9 b C_clock ν tr →
          ∀ F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ, (∀ p i j, F p i j = F p j i) →
            (∀ i j, Measurable fun p => F p i j) →
            tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν F) < ⊤ →
            ∀ b₀ G₀, IsCausalEnergySolution (ν ^ (-2 : ℝ)) ν μ (fun _ _ _ => 0) F b₀ G₀ →
              ∃ (N W : ℝ → ℝ≥0∞) (b_core G_core : _),
                Measurable N ∧
                IsCoreCausalSolution (ν ^ (-2 : ℝ)) ν (coreEnd ν b) μ (trainVel tr) F
                  b_core G_core ∧
                (∫⁻ t in Ioo (0 : ℝ) (coreEnd ν b),
                    ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) * N t ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
                  ENNReal.ofReal (C_dual * A_m) *
                    (hCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν b₀) +
                      tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν G₀)) ∧
                (∀ s ∈ Ioo (0 : ℝ) (coreEnd ν b),
                  W s ≤ ∫⁻ t in Ioo (0 : ℝ) s,
                    ENNReal.ofReal (|C_clock| * ν ^ (-(weakDegree 9 P.kappa : ℝ)) *
                      (t / s) ^ μ.re * (1 + (s - t) ^ (-1 / 2 : ℝ))) * N t) ∧
                hCalNormOn (ν ^ (-2 : ℝ)) (coreEnd ν b) (gainConj P.eigenvalue.re ν b_core) +
                    ENNReal.ofReal (Real.sqrt ν) *
                      tCalNormOn (ν ^ (-2 : ℝ)) (coreEnd ν b)
                        (gainConj P.eigenvalue.re ν G_core) ≤
                  (hCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν b₀) +
                      ENNReal.ofReal (Real.sqrt ν) *
                        tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν G₀)) +
                    ENNReal.ofReal (C_BS * (1 + ν ^ (-2 : ℝ)) *
                        (1 + Real.sqrt (ν * coreEnd ν b))) *
                      (∫⁻ s in Ioo (0 : ℝ) (coreEnd ν b),
                        ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * W s ^ (2 : ℝ)) ^ (1 / 2 : ℝ)

/-- **Step (P5): Tail energy continuation across `s = H` to `(0, ∞)`** (`PartIII-a:T19/3`,
SP 3517-3540).
Given a core solution `(b_core, G_core)` on `(0, H)` (`H = coreEnd ν b > 1`), selecting a strong
trace time in `[H - 1, H - 1/2]` and continuing on `[t_*, ∞)` with the prescribed forcing `F` and
the exact tail energy inequality `(AE)' + 2k_*AE/s + 2hAE + νAs^{-1/2}‖∇u‖² ≤ ν⁻¹As^{-1/2}‖T‖²`
with `I_H = ∫_H^∞ ‖sym ∇v‖_∞ ds ≤ Cb + Cν³` (`PartI.TrainStrainIntegral`, `sct:integrated`, SP 318-319,
3528-3535) yields a global solution `(b, G)` of `IsCausalEnergySolution` on `(0, ∞)` with
`‖g⁻¹b‖_𝓗 + √ν‖g⁻¹G‖_𝒯 ≤ C_tail ν⁻¹ (‖g⁻¹b_core‖_{𝓗(0,H)} + √ν‖g⁻¹G_core‖_{𝒯(0,H)} + ‖g⁻¹F‖_𝒯)`. -/
def TailEnergyContinuation : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ K : Set ℂ, IsAdmissibleK K →
    ∀ b : ℝ, 1 ≤ b → ∃ (C_tail ν_tail : ℝ), 0 ≤ C_tail ∧ 0 < ν_tail ∧
      ∀ ν ∈ Ioc 0 ν_tail, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
        UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ μ ∈ K,
        ∀ F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ, (∀ p i j, F p i j = F p j i) →
          (∀ i j, Measurable fun p => F p i j) →
          tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν F) < ⊤ →
          ∀ b_core G_core,
            IsCoreCausalSolution (ν ^ (-2 : ℝ)) ν (coreEnd ν b) μ (trainVel tr) F b_core G_core →
            ∃ b_sol G_sol, IsCausalEnergySolution (ν ^ (-2 : ℝ)) ν μ (trainVel tr) F b_sol G_sol ∧
              hCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν b_sol) +
                  ENNReal.ofReal (Real.sqrt ν) *
                    tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν G_sol) ≤
                ENNReal.ofReal (C_tail * ν⁻¹) *
                  (hCalNormOn (ν ^ (-2 : ℝ)) (coreEnd ν b) (gainConj P.eigenvalue.re ν b_core) +
                    ENNReal.ofReal (Real.sqrt ν) *
                      tCalNormOn (ν ^ (-2 : ℝ)) (coreEnd ν b)
                        (gainConj P.eigenvalue.re ν G_core) +
                    tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν F))

/-! ## Assembly of `PolyCausal` with exponent `M = M_s + p_m + 6` (SP 3538-3545) -/

/-- Auxiliary power comparison: for `0 < ν ≤ 1` and `a ≤ b`, `ν ^ (-a) ≤ ν ^ (-b)`. -/
private theorem rpow_neg_le_rpow_neg {ν a b : ℝ} (hν0 : 0 < ν) (hν1 : ν ≤ 1) (hab : a ≤ b) :
    ν ^ (-a) ≤ ν ^ (-b) :=
  Real.rpow_le_rpow_of_exponent_ge hν0 hν1 (neg_le_neg hab)

/-- **Conditional assembly of `prop:short-polynomial-causal`** (target of `PartIII-a:T19`),
combining `hClock : FullClockWeakForward`, `hFree : FreeCausalExistsUnique`, `hHardy : HardyKernel`
(via `free_causal_step` and `hardy_core_clock_bound`) with `TrainCoreCoeffBound`,
`CoreDuhamelBiotSavart`, `TailEnergyContinuation`, and `TrainCausalHomogeneousZero` (via
`unique_of_homogeneous_zero`). The resulting degree is `M = weakDegree 9 P.kappa + p_m + 6`,
matching SP line 3539 (`M ≥ M_s + p_m + 6`). -/
theorem polyCausal_of (hClock : FullClockWeakForward) (hFree : FreeCausalExistsUnique)
    (hHardy : HardyKernel) (hCoeff : TrainCoreCoeffBound) (hCore : CoreDuhamelBiotSavart)
    (hTail : TailEnergyContinuation) (hHom : TrainCausalHomogeneousZero) : PolyCausal := by
  intro P hP K hK
  obtain ⟨b₀, hb₀_clock⟩ := hClock P hP 9 (by norm_num)
  set b : ℝ := max b₀ 1
  have hb1 : 1 ≤ b := le_max_right _ _
  have hb0 : b₀ ≤ b := le_max_left _ _
  obtain ⟨C_clock, ν_clock, hν_clock, hClock_b⟩ := hb₀_clock b hb0
  obtain ⟨ν_free, hν_free, hFree_step⟩ := free_causal_step hFree P hP K hK
  obtain ⟨p_m, C_coeff, ν_coeff, hC_coeff, hν_coeff, hCoeff_b⟩ := hCoeff b hb1
  obtain ⟨C_dual, C_BS, ν_core, hC_dual, hC_BS, hν_core, hCore_b⟩ := hCore P hP K hK b hb1
  obtain ⟨C_tail, ν_tail, hC_tail, hν_tail, hTail_b⟩ := hTail P hP K hK b hb1
  set Ms : ℕ := weakDegree 9 P.kappa
  set M : ℕ := Ms + p_m + 6
  set C_core_const : ℝ :=
    2 + C_BS * 4 * (betaConst * |C_clock| * 2 * (C_dual * C_coeff * 2))
  set C_total : ℝ := C_tail * (C_core_const + 1)
  set ν₀ : ℝ :=
    min (min (min ν_clock ν_free) (min ν_coeff ν_core)) (min ν_tail (min (1 / 2) ((2 * b)⁻¹)))
  have hν₀ : 0 < ν₀ := by
    refine lt_min (lt_min (lt_min hν_clock hν_free) (lt_min hν_coeff hν_core))
      (lt_min hν_tail (lt_min (by norm_num) (inv_pos.2 (by linarith))))
  refine ⟨M, C_total, ν₀, hν₀, fun ν hν tr htr μ hμ F hsym hmeas hfin => ?_⟩
  have hν0 : 0 < ν := hν.1
  have hν_le_clock : ν ≤ ν_clock :=
    hν.2.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hν_le_free : ν ≤ ν_free :=
    hν.2.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hν_le_coeff : ν ≤ ν_coeff :=
    hν.2.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hν_le_core : ν ≤ ν_core :=
    hν.2.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hν_le_tail : ν ≤ ν_tail :=
    hν.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν_le_half : ν ≤ 1 / 2 :=
    hν.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hν_le_2b : ν ≤ (2 * b)⁻¹ :=
    hν.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hν1 : ν ≤ 1 := hν_le_half.trans (by norm_num)
  obtain ⟨hH1, hH_le, hsqrtH, h1sqrtH⟩ := coreEnd_bounds hb1 hν0 hν_le_half hν_le_2b
  -- (P1) Free solution
  obtain ⟨b₀_sol, G₀_sol, hsol₀, hbG₀_inv, hbG₀_rpow⟩ :=
    hFree_step ν ⟨hν0, le_min hν_le_free hν1⟩ μ hμ F hsym hmeas hfin
  -- (P2) Train core coefficient bound and weak-clock bound
  have hAm_pos : 0 ≤ C_coeff * ν ^ (-(p_m : ℝ)) := by positivity
  have hAm := hCoeff_b ν ⟨hν0, hν_le_coeff⟩ tr htr
  have hClk : ClockBoundAt P 9 b C_clock ν tr :=
    fun t s ht hts hsH f hf hcirc w u hflow =>
      hClock_b ν ⟨hν0, hν_le_clock⟩ tr htr t s ht hts hsH f hf hcirc w u hflow
  -- (P2-P4) Core Duhamel + Biot-Savart
  obtain ⟨N, W, b_core, G_core, hNmeas, hCoreSol, hN_bd, hW_pt, hCore_bd⟩ :=
    hCore_b ν ⟨hν0, hν_le_core⟩ tr htr μ hμ (C_coeff * ν ^ (-(p_m : ℝ))) C_clock hAm_pos hAm hClk
      F hsym hmeas hfin b₀_sol G₀_sol hsol₀
  -- (P3) Apply Hardy kernel bound on `(0, coreEnd ν b)`
  have hμ_pos : 0 < μ.re := (hK.2 μ hμ).1
  have hH_pos : 0 < coreEnd ν b := by linarith
  have hD_pos : 0 ≤ |C_clock| * ν ^ (-(Ms : ℝ)) := by positivity
  have hW_hardy := hardy_core_clock_bound hHardy hμ_pos hH_pos hD_pos hNmeas hW_pt
  -- Combine Hardy + source bound + free bound on the core
  set TF := tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν F)
  have hβ_pos : 0 ≤ betaConst := betaConst_nonneg
  have hN_free :
      (∫⁻ t in Ioo (0 : ℝ) (coreEnd ν b),
          ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) * N t ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (C_dual * C_coeff * 2 * ν ^ (-((p_m : ℝ) + 1))) * TF := by
    calc (∫⁻ t in Ioo (0 : ℝ) (coreEnd ν b),
            ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) * N t ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
        ≤ ENNReal.ofReal (C_dual * (C_coeff * ν ^ (-(p_m : ℝ)))) *
            (ENNReal.ofReal (2 * ν⁻¹) * TF) :=
          hN_bd.trans (mul_le_mul_of_nonneg_left hbG₀_inv bot_le)
      _ = ENNReal.ofReal (C_dual * C_coeff * 2 * ν ^ (-((p_m : ℝ) + 1))) * TF := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          rw [← Real.rpow_neg_one, show -((p_m : ℝ) + 1) = -(p_m : ℝ) + (-1 : ℝ) by ring,
            Real.rpow_add hν0]
          ring
  have hW_total :
      (∫⁻ s in Ioo (0 : ℝ) (coreEnd ν b),
          ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * W s ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (betaConst * |C_clock| * 2 * (C_dual * C_coeff * 2) *
            ν ^ (-((Ms : ℝ) + (p_m : ℝ) + 2))) * TF := by
    have h1 : betaConst * (|C_clock| * ν ^ (-(Ms : ℝ))) * (1 + Real.sqrt (coreEnd ν b)) ≤
        betaConst * |C_clock| * 2 * ν ^ (-((Ms : ℝ) + 1)) := by
      calc betaConst * (|C_clock| * ν ^ (-(Ms : ℝ))) * (1 + Real.sqrt (coreEnd ν b))
          ≤ betaConst * (|C_clock| * ν ^ (-(Ms : ℝ))) * (2 * ν⁻¹) :=
            mul_le_mul_of_nonneg_left h1sqrtH (by positivity)
        _ = betaConst * |C_clock| * 2 * ν ^ (-((Ms : ℝ) + 1)) := by
            rw [← Real.rpow_neg_one, show -((Ms : ℝ) + 1) = -(Ms : ℝ) + (-1 : ℝ) by ring,
              Real.rpow_add hν0]
            ring
    calc (∫⁻ s in Ioo (0 : ℝ) (coreEnd ν b),
            ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * W s ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
        ≤ ENNReal.ofReal (betaConst * |C_clock| * 2 * ν ^ (-((Ms : ℝ) + 1))) *
            (ENNReal.ofReal (C_dual * C_coeff * 2 * ν ^ (-((p_m : ℝ) + 1))) * TF) := by
          refine hW_hardy.trans ?_
          exact mul_le_mul (ENNReal.ofReal_le_ofReal h1) hN_free bot_le bot_le
      _ = ENNReal.ofReal (betaConst * |C_clock| * 2 * (C_dual * C_coeff * 2) *
            ν ^ (-((Ms : ℝ) + (p_m : ℝ) + 2))) * TF := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          rw [show -((Ms : ℝ) + (p_m : ℝ) + 2) = -((Ms : ℝ) + 1) + -((p_m : ℝ) + 1) by ring,
            Real.rpow_add hν0]
          ring
  have hBS_factor :
      C_BS * (1 + ν ^ (-2 : ℝ)) * (1 + Real.sqrt (ν * coreEnd ν b)) ≤
        C_BS * 4 * ν ^ (-5 / 2 : ℝ) := by
    have h1c : 1 + ν ^ (-2 : ℝ) ≤ 2 * ν ^ (-2 : ℝ) := by
      have : (1 : ℝ) ≤ ν ^ (-2 : ℝ) := by
        simpa using rpow_neg_le_rpow_neg hν0 hν1 (by norm_num : (0 : ℝ) ≤ 2)
      linarith
    have h1νH : 1 + Real.sqrt (ν * coreEnd ν b) ≤ 2 * ν ^ (-1 / 2 : ℝ) := by
      have hmul : ν * coreEnd ν b ≤ ν ^ (-1 : ℝ) := by
        calc ν * coreEnd ν b ≤ ν * ν ^ (-2 : ℝ) :=
              mul_le_mul_of_nonneg_left hH_le hν0.le
          _ = ν ^ (1 : ℝ) * ν ^ (-2 : ℝ) := by rw [Real.rpow_one]
          _ = ν ^ (-1 : ℝ) := by rw [← Real.rpow_add hν0]; norm_num
      have hsq : Real.sqrt (ν * coreEnd ν b) ≤ ν ^ (-1 / 2 : ℝ) := by
        calc Real.sqrt (ν * coreEnd ν b) ≤ Real.sqrt (ν ^ (-1 : ℝ)) := Real.sqrt_le_sqrt hmul
          _ = (ν ^ (-1 : ℝ)) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
          _ = ν ^ (-1 / 2 : ℝ) := by rw [← Real.rpow_mul hν0.le]; norm_num
      have h1r : (1 : ℝ) ≤ ν ^ (-1 / 2 : ℝ) := by
        simpa using Real.rpow_le_rpow_of_exponent_ge hν0 hν1 (by norm_num : (-1 / 2 : ℝ) ≤ 0)
      linarith
    calc C_BS * (1 + ν ^ (-2 : ℝ)) * (1 + Real.sqrt (ν * coreEnd ν b))
        ≤ C_BS * (2 * ν ^ (-2 : ℝ)) * (2 * ν ^ (-1 / 2 : ℝ)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left h1c hC_BS) h1νH (by positivity) (by positivity)
      _ = C_BS * 4 * ν ^ (-5 / 2 : ℝ) := by
          rw [show (-5 / 2 : ℝ) = (-2 : ℝ) + (-1 / 2 : ℝ) by ring, Real.rpow_add hν0]
          ring
  have hCore_total :
      hCalNormOn (ν ^ (-2 : ℝ)) (coreEnd ν b) (gainConj P.eigenvalue.re ν b_core) +
          ENNReal.ofReal (Real.sqrt ν) *
            tCalNormOn (ν ^ (-2 : ℝ)) (coreEnd ν b) (gainConj P.eigenvalue.re ν G_core) ≤
        ENNReal.ofReal (C_core_const * ν ^ (-((Ms : ℝ) + (p_m : ℝ) + 5))) * TF := by
    have hpow1 : ν ^ (-1 / 2 : ℝ) ≤ ν ^ (-((Ms : ℝ) + (p_m : ℝ) + 5)) := by
      refine Real.rpow_le_rpow_of_exponent_ge hν0 hν1 ?_
      have : (0 : ℝ) ≤ (Ms : ℝ) + (p_m : ℝ) := by positivity
      linarith
    have hpow2 : ν ^ (-((Ms : ℝ) + (p_m : ℝ) + 9 / 2)) ≤ ν ^ (-((Ms : ℝ) + (p_m : ℝ) + 5)) :=
      rpow_neg_le_rpow_neg hν0 hν1 (by linarith)
    have hterm1 : hCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν b₀_sol) +
        ENNReal.ofReal (Real.sqrt ν) *
          tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν G₀_sol) ≤
        ENNReal.ofReal (2 * ν ^ (-((Ms : ℝ) + (p_m : ℝ) + 5))) * TF := by
      refine hbG₀_rpow.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le)
      exact mul_le_mul_of_nonneg_left hpow1 zero_le_two
    have hterm2 :
        ENNReal.ofReal (C_BS * (1 + ν ^ (-2 : ℝ)) * (1 + Real.sqrt (ν * coreEnd ν b))) *
          (∫⁻ s in Ioo (0 : ℝ) (coreEnd ν b),
            ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * W s ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (C_BS * 4 * (betaConst * |C_clock| * 2 * (C_dual * C_coeff * 2)) *
            ν ^ (-((Ms : ℝ) + (p_m : ℝ) + 5))) * TF := by
      calc ENNReal.ofReal (C_BS * (1 + ν ^ (-2 : ℝ)) * (1 + Real.sqrt (ν * coreEnd ν b))) *
              (∫⁻ s in Ioo (0 : ℝ) (coreEnd ν b),
                ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * W s ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
          ≤ ENNReal.ofReal (C_BS * 4 * ν ^ (-5 / 2 : ℝ)) *
              (ENNReal.ofReal (betaConst * |C_clock| * 2 * (C_dual * C_coeff * 2) *
                ν ^ (-((Ms : ℝ) + (p_m : ℝ) + 2))) * TF) :=
            mul_le_mul (ENNReal.ofReal_le_ofReal hBS_factor) hW_total bot_le bot_le
        _ = ENNReal.ofReal (C_BS * 4 * (betaConst * |C_clock| * 2 * (C_dual * C_coeff * 2)) *
              ν ^ (-((Ms : ℝ) + (p_m : ℝ) + 9 / 2))) * TF := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
            congr 2
            rw [show -((Ms : ℝ) + (p_m : ℝ) + 9 / 2) =
                  (-5 / 2 : ℝ) + -((Ms : ℝ) + (p_m : ℝ) + 2) by ring,
              Real.rpow_add hν0]
            ring
        _ ≤ ENNReal.ofReal (C_BS * 4 * (betaConst * |C_clock| * 2 * (C_dual * C_coeff * 2)) *
              ν ^ (-((Ms : ℝ) + (p_m : ℝ) + 5))) * TF := by
            refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
            exact mul_le_mul_of_nonneg_left hpow2 (by positivity)
    calc hCalNormOn (ν ^ (-2 : ℝ)) (coreEnd ν b) (gainConj P.eigenvalue.re ν b_core) +
            ENNReal.ofReal (Real.sqrt ν) *
              tCalNormOn (ν ^ (-2 : ℝ)) (coreEnd ν b) (gainConj P.eigenvalue.re ν G_core)
        ≤ ENNReal.ofReal (2 * ν ^ (-((Ms : ℝ) + (p_m : ℝ) + 5))) * TF +
            ENNReal.ofReal (C_BS * 4 * (betaConst * |C_clock| * 2 * (C_dual * C_coeff * 2)) *
              ν ^ (-((Ms : ℝ) + (p_m : ℝ) + 5))) * TF :=
          hCore_bd.trans (add_le_add hterm1 hterm2)
      _ = ENNReal.ofReal (C_core_const * ν ^ (-((Ms : ℝ) + (p_m : ℝ) + 5))) * TF := by
          rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 2
          unfold C_core_const
          ring
  -- (P5) Tail continuation across `s = coreEnd ν b`
  obtain ⟨b_sol, G_sol, hSol, hTail_bd⟩ :=
    hTail_b ν ⟨hν0, hν_le_tail⟩ tr htr μ hμ F hsym hmeas hfin b_core G_core hCoreSol
  refine ⟨b_sol, G_sol, hSol, ?_, fun b' G' hSol' =>
    unique_of_homogeneous_zero hHom hP hK hν0 tr htr hμ hSol hSol'⟩
  have h1_le_pow : (1 : ℝ) ≤ ν ^ (-((Ms : ℝ) + (p_m : ℝ) + 5)) := by
    simpa using rpow_neg_le_rpow_neg hν0 hν1 (by positivity : (0 : ℝ) ≤ (Ms : ℝ) + (p_m : ℝ) + 5)
  have hTF_le : TF ≤ ENNReal.ofReal (1 * ν ^ (-((Ms : ℝ) + (p_m : ℝ) + 5))) * TF := by
    rw [one_mul]
    exact le_mul_of_one_le_left bot_le (ENNReal.one_le_ofReal.2 h1_le_pow)
  calc hCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν b_sol) +
          ENNReal.ofReal (Real.sqrt ν) *
            tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν G_sol)
      ≤ ENNReal.ofReal (C_tail * ν⁻¹) *
          (ENNReal.ofReal (C_core_const * ν ^ (-((Ms : ℝ) + (p_m : ℝ) + 5))) * TF +
            ENNReal.ofReal (1 * ν ^ (-((Ms : ℝ) + (p_m : ℝ) + 5))) * TF) := by
        refine hTail_bd.trans (mul_le_mul_of_nonneg_left (add_le_add hCore_total hTF_le) bot_le)
    _ = ENNReal.ofReal (C_total * ν ^ (-(M : ℝ))) * TF := by
        have hC_core_pos : 0 ≤ C_core_const := by unfold C_core_const; positivity
        rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity), ← mul_assoc,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        have hM : (M : ℝ) = (Ms : ℝ) + (p_m : ℝ) + 6 := by unfold M; push_cast; ring
        rw [hM, ← Real.rpow_neg_one,
          show -((Ms : ℝ) + (p_m : ℝ) + 6) = (-1 : ℝ) + -((Ms : ℝ) + (p_m : ℝ) + 5) by ring,
          Real.rpow_add hν0]
        unfold C_total
        ring

end UnforcedLeray.Short.IIIa
