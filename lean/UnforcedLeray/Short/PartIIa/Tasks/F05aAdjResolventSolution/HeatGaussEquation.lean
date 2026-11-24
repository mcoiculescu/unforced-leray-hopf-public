import UnforcedLeray.Short.PartIIa.Sub.F05_1
import UnforcedLeray.Short.PartIIa.Tasks.F05aAdjResolventSolution.PhaseTestDerivBounded
import UnforcedLeray.Short.PartIIa.Tasks.F05aAdjResolventSolution.ParamIntegralSmooth

/-!
# Part II-a, task `PartII-a:F05a`: the heat Gaussian solves the heat equation in `w`

Target: `HeatGaussEquation` (defined in `Short/PartII-a/Sub/F05_1.lean`).

Source of record: `the November 2 reference manuscript`, lines 1403-1413
(the heat flow `e^{ν(1-e^{-t})Δ}`; `heatGauss` is the scaled Gaussian average of the slices).

Proof outline.
* `kernel_sq_smul`: `kernel (w^2) (w ξ) = |(w^3)⁻¹| · kernel 1 ξ`.
* `heatGauss_eq_average`: for `w ≠ 0`, `heatGauss Φ₀ w (τ, z) = Heat.average (w^2) (Φ₀(τ, ·)) z`
  (change of variables `y = w ξ`, `Measure.integral_comp_smul`).
* `heatGauss_contDiff`: joint `C^∞` smoothness of `heatGauss Φ₀ w`, from the parametric integral
  lemma `paramIntegralSmooth_proof` with the `ξ`-uniform derivative bound `M_k · kernel 1 ξ`.
* `lapT_eq_vlap_slice`: `lapT Φ (τ, z) = Heat.vlap (Φ(τ, ·)) z` for smooth `Φ`.
* Main theorem: `Heat.hasDerivAt_average_time` in `s = w^2`, composed with `w ↦ w^2`, and
  `Heat.vlap_average`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
open UnforcedLeray.PhaseSpace

namespace UnforcedLeray.Short.PartIIa

namespace HeatGaussEquationAux

/-! ### Kernel scaling and change of variables -/

/-- Pointwise scaling of the heat kernel: `kernel (w²) (w ξ) = |(w³)⁻¹| · kernel 1 ξ` for `w ≠ 0`. -/
theorem kernel_sq_smul {w : ℝ} (hw : w ≠ 0) (ξ : Space) :
    Heat.kernel (w ^ 2) (w • ξ) = |(w ^ 3)⁻¹| * Heat.kernel 1 ξ := by
  have h1 : (4 * Real.pi * w ^ 2) = (4 * Real.pi * 1) * (|w| ^ (2 : ℝ)) := by
    rw [Real.rpow_two, sq_abs]; ring
  have h2 : |(w ^ 3)⁻¹| = |w| ^ (-(3 : ℝ)) := by
    rw [abs_inv, abs_pow, Real.rpow_neg (abs_nonneg w),
      show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hpow : (4 * Real.pi * w ^ 2) ^ (-(3 : ℝ) / 2)
      = |(w ^ 3)⁻¹| * (4 * Real.pi * 1) ^ (-(3 : ℝ) / 2) := by
    rw [h1, Real.mul_rpow (x := 4 * Real.pi * 1) (y := |w| ^ (2 : ℝ))
        (by positivity) (by positivity),
      ← Real.rpow_mul (abs_nonneg w), h2]
    have h3 : (2 : ℝ) * (-(3 : ℝ) / 2) = -(3 : ℝ) := by norm_num
    rw [h3]
    ring
  have hexp : -(4 * w ^ 2)⁻¹ * ‖w • ξ‖ ^ 2 = -(4 * (1 : ℝ))⁻¹ * ‖ξ‖ ^ 2 := by
    have hw2 : w ^ 2 ≠ 0 := pow_ne_zero 2 hw
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    field_simp
  rw [Heat.kernel_formula, Heat.kernel_formula, hexp, hpow]
  ring

/-- Change of variables: for `w ≠ 0`, the scaled Gaussian average of the slice `Φ₀(τ, ·)` is the
heat average at time `w²`. -/
theorem heatGauss_eq_average (Φ₀ : ℝ × Space → CVec3) {w : ℝ} (hw : w ≠ 0) (τ : ℝ) (z : Space) :
    heatGauss Φ₀ w (τ, z) = Heat.average (w ^ 2) (fun y => Φ₀ (τ, y)) z := by
  have hc : |(w ^ 3)⁻¹| ≠ 0 := by simp [hw]
  have hscale : ∫ x : Space, Heat.kernel (w ^ 2) (w • x) • Φ₀ (τ, z - w • x)
      = |(w ^ 3)⁻¹| • ∫ y : Space, Heat.kernel (w ^ 2) y • Φ₀ (τ, z - y) := by
    have h := MeasureTheory.Measure.integral_comp_smul (volume : Measure Space)
      (fun y : Space => Heat.kernel (w ^ 2) y • Φ₀ (τ, z - y)) w
    rw [finrank_euclideanSpace_fin] at h
    exact h
  have hpt : ∀ x : Space, Heat.kernel (w ^ 2) (w • x) • Φ₀ (τ, z - w • x)
      = |(w ^ 3)⁻¹| • (Heat.kernel 1 x • Φ₀ (τ, z - w • x)) := by
    intro x
    rw [kernel_sq_smul hw x, mul_smul]
  have hint : ∫ x : Space, Heat.kernel (w ^ 2) (w • x) • Φ₀ (τ, z - w • x)
      = |(w ^ 3)⁻¹| • ∫ x : Space, Heat.kernel 1 x • Φ₀ (τ, z - w • x) := by
    simp_rw [hpt]
    rw [integral_smul]
  have key : |(w ^ 3)⁻¹| • ∫ x : Space, Heat.kernel 1 x • Φ₀ (τ, z - w • x)
      = |(w ^ 3)⁻¹| • ∫ y : Space, Heat.kernel (w ^ 2) y • Φ₀ (τ, z - y) := by
    rw [← hint, hscale]
  exact smul_right_injective _ hc key

/-! ### Slices of a phase test -/

/-- The slice `y ↦ Φ(τ, y)` has `k`-th derivative the `(0, ·)`-restriction of `D^kΦ(τ, z)`. -/
theorem slice_iteratedFDeriv_eq {Φ : ℝ × Space → CVec3} (hΦ : ContDiff ℝ ∞ Φ) (τ : ℝ)
    (k : ℕ) (x : Space) :
    iteratedFDeriv ℝ k (fun y => Φ (τ, y)) x
      = (iteratedFDeriv ℝ k Φ (τ, x)).compContinuousLinearMap
          (fun _ => ContinuousLinearMap.inr ℝ ℝ Space) := by
  have hc : ContDiff ℝ ∞ (fun q : ℝ × Space => (τ, (0 : Space)) + q) :=
    contDiff_const.add contDiff_id
  have hf : ContDiff ℝ ∞ (fun q : ℝ × Space => Φ ((τ, (0 : Space)) + q)) :=
    hΦ.comp hc
  have h1 : (fun y : Space => Φ (τ, y))
      = (fun q : ℝ × Space => Φ ((τ, (0 : Space)) + q)) ∘ ContinuousLinearMap.inr ℝ ℝ Space := by
    funext y
    simp
  rw [h1, ContinuousLinearMap.iteratedFDeriv_comp_right (i := k)
    (ContinuousLinearMap.inr ℝ ℝ Space) hf x (by exact_mod_cast le_top)]
  rw [iteratedFDeriv_comp_add_left (f := Φ)]
  simp

/-- The slice `y ↦ Φ(τ, y)` does not increase the norm of the `k`-th derivative. -/
theorem slice_norm_le {Φ : ℝ × Space → CVec3} (hΦ : ContDiff ℝ ∞ Φ) (τ : ℝ) (k : ℕ)
    (x : Space) :
    ‖iteratedFDeriv ℝ k (fun y => Φ (τ, y)) x‖ ≤ ‖iteratedFDeriv ℝ k Φ (τ, x)‖ := by
  rw [slice_iteratedFDeriv_eq hΦ τ k x]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  refine mul_le_of_le_one_right (norm_nonneg _)
    (Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => ?_))
  exact ContinuousLinearMap.norm_inr_le_one ℝ ℝ Space

/-- A uniform bound on the derivatives of order `≤ 2` of every slice `Φ₀(τ, ·)`. -/
theorem slice_bound {P : ℝ} {Φ₀ : ℝ × Space → CVec3} (hP : 0 < P) (hΦ : IsPhaseTest P Φ₀)
    (τ : ℝ) :
    ∃ M : ℝ, ∀ k : ℕ, k ≤ 2 → ∀ x : Space, ‖iteratedFDeriv ℝ k (fun y => Φ₀ (τ, y)) x‖ ≤ M := by
  obtain ⟨M0, h0, hM0⟩ := phaseTestDerivBounded_proof P hP Φ₀ hΦ 0
  obtain ⟨M1, h1, hM1⟩ := phaseTestDerivBounded_proof P hP Φ₀ hΦ 1
  obtain ⟨M2, h2, hM2⟩ := phaseTestDerivBounded_proof P hP Φ₀ hΦ 2
  refine ⟨M0 + M1 + M2, fun k hk x => ?_⟩
  refine (slice_norm_le hΦ.smooth τ k x).trans ?_
  interval_cases k
  · linarith [hM0 (τ, x)]
  · linarith [hM1 (τ, x)]
  · linarith [hM2 (τ, x)]

/-- Each slice `y ↦ Φ(τ, y)` of a smooth `Φ` is `C²`. -/
theorem slice_contDiff_two {Φ : ℝ × Space → CVec3} (hΦ : ContDiff ℝ ∞ Φ) (τ : ℝ) :
    ContDiff ℝ 2 (fun y : Space => Φ (τ, y)) := by
  have h : ContDiff ℝ ∞ (fun y : Space => ((τ, y) : ℝ × Space)) :=
    contDiff_const.prodMk contDiff_id
  exact (hΦ.comp h).of_le (by norm_num)

/-! ### Joint smoothness of `heatGauss` -/

/-- The `ξ`-integrand of `heatGauss`: `q ↦ kernel 1 ξ • Φ₀(q.1, q.2 - w ξ)`. -/
def heatFam (w : ℝ) (Φ₀ : ℝ × Space → CVec3) (ξ : Space) (q : ℝ × Space) : CVec3 :=
  Heat.kernel 1 ξ • Φ₀ (q.1, q.2 - w • ξ)

theorem heatFam_eq (w : ℝ) (Φ₀ : ℝ × Space → CVec3) (ξ : Space) :
    heatFam w Φ₀ ξ = fun q => Heat.kernel 1 ξ • Φ₀ (q + (0, -(w • ξ))) := by
  funext q
  have hq : (q.1, q.2 - w • ξ) = q + (0, -(w • ξ)) :=
    Prod.ext (by simp) (by simp [sub_eq_add_neg])
  simp only [heatFam, hq]

theorem heatFam_contDiff {P : ℝ} {Φ₀ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ₀)
    (w : ℝ) (ξ : Space) : ContDiff ℝ ∞ (heatFam w Φ₀ ξ) := by
  have hc : ContDiff ℝ ∞ (fun q : ℝ × Space => q + (0, -(w • ξ))) :=
    contDiff_id.add contDiff_const
  rw [heatFam_eq]
  exact (hΦ.smooth.comp hc).const_smul (Heat.kernel 1 ξ)

theorem iteratedFDeriv_heatFam {P : ℝ} {Φ₀ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ₀)
    (w : ℝ) (ξ : Space) (k : ℕ) (p : ℝ × Space) :
    iteratedFDeriv ℝ k (heatFam w Φ₀ ξ) p
      = Heat.kernel 1 ξ • iteratedFDeriv ℝ k Φ₀ (p + (0, -(w • ξ))) := by
  have hc : ContDiff ℝ ∞ (fun q : ℝ × Space => q + (0, -(w • ξ))) :=
    contDiff_id.add contDiff_const
  have hdiff : ContDiffAt ℝ k (fun q : ℝ × Space => Φ₀ (q + (0, -(w • ξ)))) p :=
    ((hΦ.smooth.comp hc).contDiffAt).of_le (by exact_mod_cast le_top)
  rw [heatFam_eq, iteratedFDeriv_const_smul_apply' hdiff,
    iteratedFDeriv_comp_add_right (f := Φ₀)]

theorem heatGauss_contDiff {P : ℝ} {Φ₀ : ℝ × Space → CVec3} (hP : 0 < P)
    (hΦ : IsPhaseTest P Φ₀) (w : ℝ) : ContDiff ℝ ∞ (heatGauss Φ₀ w) := by
  have hfam : ParamFamilyHyp volume (heatFam w Φ₀) := by
    refine ⟨Filter.Eventually.of_forall fun ξ => heatFam_contDiff hΦ w ξ, ?_, ?_⟩
    · intro k p
      have hfun : (fun ξ : Space => iteratedFDeriv ℝ k (heatFam w Φ₀ ξ) p)
          = fun ξ : Space => Heat.kernel 1 ξ • iteratedFDeriv ℝ k Φ₀ (p + (0, -(w • ξ))) :=
        funext fun ξ => iteratedFDeriv_heatFam hΦ w ξ k p
      rw [hfun]
      have hcont : Continuous fun ξ : Space => iteratedFDeriv ℝ k Φ₀ (p + (0, -(w • ξ))) :=
        (hΦ.smooth.continuous_iteratedFDeriv (by exact_mod_cast le_top)).comp
          (show Continuous fun ξ : Space => p + (0, -(w • ξ)) by fun_prop)
      exact (Heat.kernel_integrable one_pos).aestronglyMeasurable.smul
        hcont.aestronglyMeasurable
    · intro k
      obtain ⟨M, _, hM⟩ := phaseTestDerivBounded_proof P hP Φ₀ hΦ k
      refine ⟨fun ξ => M * Heat.kernel 1 ξ, (Heat.kernel_integrable one_pos).const_mul M,
        Filter.Eventually.of_forall fun ξ p => ?_⟩
      show ‖iteratedFDeriv ℝ k (heatFam w Φ₀ ξ) p‖ ≤ M * Heat.kernel 1 ξ
      rw [iteratedFDeriv_heatFam hΦ w ξ k p, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (Heat.kernel_nonneg one_pos ξ), mul_comm M]
      exact mul_le_mul_of_nonneg_left (hM _) (Heat.kernel_nonneg one_pos ξ)
  exact (paramIntegralSmooth_proof (ℝ × Space) Space volume (heatFam w Φ₀) hfam).1

/-! ### `lapT` of a smooth phase function is the Laplacian of its slice -/

/-- Directional derivative of a directional derivative: `∂_w ∂_v Φ = D²Φ(w, v)`. -/
theorem fderiv_fderiv_apply_eq {Φ : ℝ × Space → CVec3} (hΦ : ContDiff ℝ ∞ Φ)
    (p v w : ℝ × Space) :
    fderiv ℝ (fun q => fderiv ℝ Φ q v) p w = fderiv ℝ (fderiv ℝ Φ) p w v := by
  have hc : DifferentiableAt ℝ (fderiv ℝ Φ) p :=
    ((hΦ.fderiv_right (m := 1) (by norm_num)).differentiable (by simp)) p
  have hA : HasFDerivAt (fun q => fderiv ℝ Φ q v)
      ((ContinuousLinearMap.apply ℝ CVec3 v).comp (fderiv ℝ (fderiv ℝ Φ) p)) p :=
    (ContinuousLinearMap.apply ℝ CVec3 v).hasFDerivAt.comp p hc.hasFDerivAt
  rw [hA.fderiv]
  rfl

theorem lapT_eq_vlap_slice {Φ : ℝ × Space → CVec3} (hΦ : ContDiff ℝ ∞ Φ) (τ : ℝ) (z : Space) :
    lapT Φ (τ, z) = UnforcedLeray.Heat.vlap (fun y => Φ (τ, y)) z := by
  have hdy : ∀ (j : Fin 3) (p : ℝ × Space),
      dy j (dy j Φ) p
        = iteratedFDeriv ℝ 2 Φ p
            ![(0, UnforcedLeray.coordinateVector j), (0, UnforcedLeray.coordinateVector j)] := by
    intro j p
    rw [iteratedFDeriv_two_apply]
    simp only [dy, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact fderiv_fderiv_apply_eq hΦ p _ _
  have hslice : ∀ i : Fin 3,
      iteratedFDeriv ℝ 2 (fun y => Φ (τ, y)) z
          ![UnforcedLeray.coordinateVector i, UnforcedLeray.coordinateVector i]
        = iteratedFDeriv ℝ 2 Φ (τ, z)
          ![(0, UnforcedLeray.coordinateVector i), (0, UnforcedLeray.coordinateVector i)] := by
    intro i
    rw [slice_iteratedFDeriv_eq hΦ τ 2 z, ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext m
    fin_cases m <;> simp
  simp only [lapT, UnforcedLeray.Heat.vlap]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hdy j (τ, z), hslice j]

end HeatGaussEquationAux

/-- **The heat Gaussian solves the heat equation in `w`** (`P > 0`, `Φ₀` a phase test, `w > 0`):
`∂_w H(w; q) = 2w · ΔH(w; q)`. -/
theorem heatGaussEquation_proof : UnforcedLeray.Short.PartIIa.HeatGaussEquation := by
  intro P hP Φ₀ hΦ w hw q
  obtain ⟨τ, z⟩ := q
  have hw0 : w ≠ 0 := hw.ne'
  have hs : (0 : ℝ) < w ^ 2 := by positivity
  obtain ⟨M, hb⟩ := HeatGaussEquationAux.slice_bound hP hΦ τ
  have hu2 := HeatGaussEquationAux.slice_contDiff_two hΦ.smooth τ
  have h1 := Heat.hasDerivAt_average_time hu2 hb hs z
  have h2 : HasDerivAt (fun w' : ℝ => w' ^ 2) (2 * w) w := by
    simpa using hasDerivAt_pow 2 w
  have h3 := HasDerivAt.scomp (x := w) (h := fun w' : ℝ => w' ^ 2) h1 h2
  have h4 : HasDerivAt (fun w' : ℝ => heatGauss Φ₀ w' (τ, z))
      ((2 * w) • Heat.average (w ^ 2) (Heat.vlap (fun y => Φ₀ (τ, y))) z) w := by
    refine h3.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hw] with w' hw'
    exact HeatGaussEquationAux.heatGauss_eq_average Φ₀ (Set.mem_Ioi.mp hw').ne' τ z
  have hlap : lapT (heatGauss Φ₀ w) (τ, z)
      = Heat.average (w ^ 2) (Heat.vlap (fun y => Φ₀ (τ, y))) z := by
    rw [HeatGaussEquationAux.lapT_eq_vlap_slice
      (HeatGaussEquationAux.heatGauss_contDiff hP hΦ w) τ z]
    have hfun : (fun y : Space => heatGauss Φ₀ w (τ, y))
        = Heat.average (w ^ 2) (fun y => Φ₀ (τ, y)) :=
      funext fun y => HeatGaussEquationAux.heatGauss_eq_average Φ₀ hw0 τ y
    rw [hfun]
    exact Heat.vlap_average hs hu2 hb z
  rw [hlap]
  exact h4

end UnforcedLeray.Short.PartIIa
