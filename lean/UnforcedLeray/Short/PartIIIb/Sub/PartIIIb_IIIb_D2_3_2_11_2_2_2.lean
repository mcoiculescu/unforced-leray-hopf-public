import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_2_11_2_2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# `SepWSmoothTop` decomposed (`PartIII-b:IIIb-D2/3/2/11/2/2/2`, source 3604-3621)

Source of record: `the November 2 reference manuscript`.
All-order, joint-in-`(τ, y)` analogue of `sepWSmoothOn_of_of`.  `sepWSmoothTop_of` derives
`SepWSmoothTop` from four source facts:

* `ParamContDiffTop` (generic all-order parametric differentiation, parameter in `ℝ × Space`);
* `HeatLerayKSmoothTop` (`K_t` is `C^∞`, `t > 0`);
* `SepPhiMeasurableTop` (measurability of all `x`-derivatives of the integrand);
* `SepGapPointwiseTop` (the pointwise `sep:kernel` bound at every order; the majorant is
  `C_n l^{2Re μ+2} 1_{|z| ≤ Z}`, which is integrable on `(0,1) × ℝ³` because `2 Re μ + 2 > -1`,
  proved here as `sepTopMajorant_integrable`).

Smoothness of the integrand (`sepPhiJ_contDiff`) is proved here from `HeatLerayKSmoothTop`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- The integrand of `sepW` as a function of the joint parameter `x = (τ, y) ∈ ℝ × Space`. -/
def sepPhiJ (ν : ℝ) (μ : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3)
    (p : ℝ × Space) (x : ℝ × Space) : ℂ :=
  sepPhi ν μ T x.1 i p x.2

/-- **Generic all-order parametric differentiation** (parameter in `ℝ × Space`):
if each `F a` is `C^∞` on the open convex `U`, and for every order `n` the `n`-th derivatives are
measurable in `a` and dominated on `U` by an integrable `g n`, then `x ↦ ∫ F a x dm` is `C^∞` on
`U` (induction on the order with `hasFDerivAt_integral_of_dominated_of_fderiv_le`). -/
def ParamContDiffTop : Prop :=
  ∀ {α : Type} [MeasurableSpace α] (m : Measure α) (F : α → ℝ × Space → ℂ)
    (U : Set (ℝ × Space)) (g : ℕ → α → ℝ), IsOpen U → Convex ℝ U →
    (∀ᵐ a ∂m, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F a) U) →
    (∀ n, Integrable (g n) m) →
    (∀ n, ∀ᵐ a ∂m, ∀ x ∈ U, ‖iteratedFDeriv ℝ n (F a) x‖ ≤ g n a) →
    (∀ n, ∀ x ∈ U, AEStronglyMeasurable (fun a => iteratedFDeriv ℝ n (F a) x) m) →
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => ∫ a, F a x ∂m) U

/-- `K_t` is `C^∞` on `ℝ³` for `t > 0` (all-order analogue of `HeatLerayKSmooth`; source 3604-3610:
`heatG` is a Gaussian and `∫_t^∞ G_a da` is a smooth function of `|x|²/4` for `t > 0`). -/
def HeatLerayKSmoothTop : Prop :=
  ∀ t : ℝ, 0 < t → ∀ i j : Fin 3,
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => IIIa.heatLerayK t i j x)

/-- Measurability of the `x`-derivatives of the integrand on `(0,1) × Space`, every order
(joint smoothness of `(t,x) ↦ K_t(x)` for `t > 0`, all-order analogue of `SepPhiMeasurable`).
`T` is jointly `C^∞` (as in `SepWSmoothTop`): the `τ`-derivatives fall on `T(τ + 2 log l, z)`. -/
def SepPhiMeasurableTop : Prop :=
  ∀ (ν : ℝ) (μ : ℂ) (P rOut : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ),
    0 < ν → IIIa.IsSepSource P rOut T →
    (∀ j k : Fin 3, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => T x.1 x.2 j k)) →
    ∀ (i : Fin 3) (n : ℕ) (x : ℝ × Space),
      AEStronglyMeasurable (fun p => iteratedFDeriv ℝ n (sepPhiJ ν μ T i p) x) sepRho

/-- **`sep:kernel` at the gap, every order** (3604-3621): for `T` jointly `C^∞`, `P`-periodic
(hence all `τ`-derivatives bounded), supported in `|z| ≤ Z` and `ϱ z ≤ rOut`, and `x₀ = (τ₀, y₀)`
with `rOut < ϱ y₀`, there is `ε > 0` such that for each order `n` there is `C` with
`‖D^n_{(τ,y)} Φ(l,z;τ,y)‖ ≤ C l^{2Re μ+2} 1_{|z| ≤ Z}` for `|(τ,y) - x₀| < ε`, `l ∈ (0,1)`.
(Leibniz rule: `y`-derivatives fall on `K_{ν(1-l²)}(y - l z)` and are bounded by
`C_j |y - lz|^{-4-j}` with `|y - l z| ≥ ϱ y - rOut ≥ d > 0` on `supp T`
(`IIIa.SepKernelBounds`), `τ`-derivatives fall on `T(τ + 2 log l, z)`; off the support
`Φ(l,z;·,·) ≡ 0`.) -/
def SepGapPointwiseTop : Prop :=
  IIIa.SepKernelBounds → ∀ (ν : ℝ) (μ : ℂ) (rOut P : ℝ)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ), 0 < ν → -(1 / 4) < μ.re → 0 ≤ rOut → 0 < P →
    IIIa.IsSepSource P rOut T →
    (∀ j k : Fin 3, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => T x.1 x.2 j k)) →
    ∀ Z : ℝ, (∀ τ z, Z < ‖z‖ → T τ z = 0) → ∀ (i : Fin 3) (x₀ : ℝ × Space), rOut < ϱ x₀.2 →
      ∃ ε : ℝ, 0 < ε ∧ ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Metric.ball x₀ ε, ∀ l ∈ Ioo (0 : ℝ) 1,
        ∀ z : Space, ‖iteratedFDeriv ℝ n (sepPhiJ ν μ T i (l, z)) x‖ ≤
          C * (l ^ (2 * μ.re + 2) * (if ‖z‖ ≤ Z then 1 else 0))

theorem sepTopMajorant_integrable (a Z : ℝ) (ha : -1 < a) :
    Integrable (fun p : ℝ × Space => p.1 ^ a * (if ‖p.2‖ ≤ Z then (1 : ℝ) else 0)) sepRho := by
  unfold sepRho
  have h1 : Integrable (fun l : ℝ => l ^ a) (volume.restrict (Ioo (0 : ℝ) 1)) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)).2 ha
  have h2 : Integrable (fun z : Space => if ‖z‖ ≤ Z then (1 : ℝ) else 0) volume := by
    have : (fun z : Space => if ‖z‖ ≤ Z then (1 : ℝ) else 0) =
        (Metric.closedBall (0 : Space) Z).indicator (fun _ => (1 : ℝ)) := by
      funext z; simp [Set.indicator]
    rw [this, integrable_indicator_iff Metric.isClosed_closedBall.measurableSet]
    exact integrableOn_const (measure_closedBall_lt_top.ne)
  exact h1.mul_prod h2

theorem sepPhiJ_contDiff (h2 : HeatLerayKSmoothTop) (ν : ℝ) (μ : ℂ)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) (l : ℝ) (z : Space)
    (hν : 0 < ν) (hl : l ∈ Ioo (0 : ℝ) 1)
    (hT : ∀ j k : Fin 3, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => T x.1 x.2 j k)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (sepPhiJ ν μ T i (l, z)) := by
  have ht : 0 < ν * (1 - l ^ 2) := by
    have := hl.1; have := hl.2; nlinarith [mul_pos hν (sub_pos.2 (show l ^ 2 < 1 by nlinarith))]
  unfold sepPhiJ sepPhi
  refine contDiff_const.mul (ContDiff.sum fun j _ => ContDiff.sum fun k _ => ?_)
  refine ContDiff.mul ?_ ?_
  · have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x => fderiv ℝ (fun x => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x) x) :=
      (h2 _ ht i j).fderiv_right (by simp)
    have h3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => x.2 - l • z) :=
      contDiff_snd.sub contDiff_const
    exact Complex.ofRealCLM.contDiff.comp ((h1.comp h3).clm_apply contDiff_const)
  · have h4 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : ℝ × Space => (x.1 + 2 * Real.log l, z)) :=
      (contDiff_fst.add contDiff_const).prodMk contDiff_const
    exact Complex.ofRealCLM.contDiff.comp ((hT j k).comp h4)

theorem sepWSmoothTop_of (hK : IIIa.SepKernelBounds) (h1 : ParamContDiffTop)
    (h2 : HeatLerayKSmoothTop) (h3 : SepPhiMeasurableTop) (h4 : SepGapPointwiseTop) :
    SepWSmoothTop := by
  intro ν μ rOut P T hν hμ hr hP hS _hM hT hZ i
  obtain ⟨Z, hZ⟩ := hZ
  refine contDiffOn_of_locally_contDiffOn fun x₀ hx₀ => ?_
  obtain ⟨ε, hε, hb⟩ := h4 hK ν μ rOut P T hν hμ hr hP hS hT Z hZ i x₀ hx₀
  choose C hC0 hCb using hb
  refine ⟨Metric.ball x₀ ε, Metric.isOpen_ball, Metric.mem_ball_self hε, ?_⟩
  have ha : (-1 : ℝ) < 2 * μ.re + 2 := by linarith
  have hint : ∀ n : ℕ, Integrable
      (fun p : ℝ × Space => C n * (p.1 ^ (2 * μ.re + 2) * (if ‖p.2‖ ≤ Z then (1 : ℝ) else 0)))
      sepRho := fun n => (sepTopMajorant_integrable _ Z ha).const_mul (C n)
  have hbound : ∀ n : ℕ, ∀ᵐ p ∂sepRho, ∀ x ∈ Metric.ball x₀ ε,
      ‖iteratedFDeriv ℝ n (sepPhiJ ν μ T i p) x‖ ≤
        C n * (p.1 ^ (2 * μ.re + 2) * (if ‖p.2‖ ≤ Z then (1 : ℝ) else 0)) := by
    intro n
    filter_upwards [ae_mem_Ioo_sepRho] with p hp x hx
    exact hCb n x hx p.1 hp p.2
  have key : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => ∫ p, sepPhiJ ν μ T i p x ∂sepRho)
      (Metric.ball x₀ ε) :=
    h1 sepRho (sepPhiJ ν μ T i) (Metric.ball x₀ ε)
      (fun n p => C n * (p.1 ^ (2 * μ.re + 2) * (if ‖p.2‖ ≤ Z then (1 : ℝ) else 0)))
      Metric.isOpen_ball (convex_ball _ _)
      (by
        filter_upwards [ae_mem_Ioo_sepRho] with p hp
        exact (sepPhiJ_contDiff h2 ν μ T i p.1 p.2 hν hp hT).contDiffOn)
      hint hbound (fun n x _ => h3 ν μ P rOut T hν hS hT i n x)
  refine (key.mono inter_subset_right).congr fun x hx => ?_
  apply sepW_eq_integral
  have hm : AEStronglyMeasurable (fun p => sepPhiJ ν μ T i p x) sepRho := by
    have := (continuousMultilinearCurryFin0 ℝ (ℝ × Space) ℂ).continuous.comp_aestronglyMeasurable
      (h3 ν μ P rOut T hν hS hT i 0 x)
    refine this.congr (Filter.Eventually.of_forall fun p => ?_)
    simp [iteratedFDeriv_zero_eq_comp]
  refine Integrable.mono' (hint 0) hm ?_
  filter_upwards [hbound 0] with p hp
  have := hp x hx.2
  simpa [norm_iteratedFDeriv_zero, sepPhiJ] using this

end UnforcedLeray.Short.PartIIIb.Concrete
