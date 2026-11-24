import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_2
import UnforcedLeray.Short.PartIIIa.Defs

/-!
# `PartII-a:N01/9/1/2/4` (decomposition): `HeatIntEnergy`

Source `the November 2 reference manuscript`
lines 1650-1658, 1684-1689, 3379-3383, 3426-3430.  For a smooth, `c`-periodic force `F`
supported in `s ∈ [s₁,s₂]`, `|η| ≤ R`, the causal heat integral `u = smoothHeatInt c ν μ F`
vanishes for `s < s₁`, is `c`-periodic in `q`, is `C¹` in `(q,η)` with jointly continuous
derivative for `s > 0`, is divergence free when each slice `F(σ,·)` is, and has finite local
energy.  The classical divergence of `F(σ,·)` vanishes by `solenoidalHC 0 c` and continuity.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.B0220 (Profile HSpace measureH)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIIb.Concrete (Chart)
open UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst (IsEnergyFieldAE)
open UnforcedLeray.Short.PartIIIb.NearInst.Delta (velF)
open UnforcedLeray.Short.IIIa (vnorm2 tnorm2 HasWeakCellDerivC)

/-- The classical cell divergence of the slice `F(σ,·)` at `y = (q,η)`. -/
def slabDiv (F : Profile → MeridC) (σ : ℝ) (y : ℝ × ℝ) : ℂ :=
  ∑ j : Fin 2, fderiv ℝ (fun z : ℝ × ℝ => F (σ, z) j) y (UnforcedLeray.B0579.dir j)

/-- The cell gradient `G i j = ∂_j b_i` of a chart field at ages `s > 0` (zero otherwise). -/
def gradOf (b : Chart → Fin 2 → ℂ) : Chart → Fin 2 → Fin 2 → ℂ := fun x i j =>
  if 0 < x.1 then fderiv ℝ (fun y : ℝ × ℝ => b (x.1, y) i) x.2 (UnforcedLeray.B0579.dir j) else 0

/-- **(S1)** Classical solenoidality of a smooth force `F = g` a.e. with `g ∈ solenoidalHC 0 c`
(lines 1676, 3398-3400): `g ⟂ cgrad 0 Φ` for all profile tests is the weak equation
`∫ s^{-3/2}…(F_r ∂_qΦ + F_z ∂_ηΦ) = 0`; the weight depends on `s` only, `F` is smooth, so every
slice `F(σ,·)` has `∂_qF_r + ∂_ηF_z = 0` pointwise (for `σ < s₁` trivially since `F = 0`). -/
def SlabDivZero : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ g ∈ UnforcedLeray.Short.PartIIa.solenoidalHC 0 c, ∀ F : Profile → MeridC,
    IsSmoothForceFn c F → (g : Profile → MeridC) =ᵐ[measureH c] F →
      ∀ σ y, slabDiv F σ y = 0

/-- **(S2)** `q`-periodicity of the heat integral (`periodize F = F` for `c`-periodic `F`;
`planeHeat` commutes with the translation `(c,0)`; lines 3379-3383). -/
def HeatIntPeriodic : Prop :=
  ∀ (c ν : ℝ), 0 < c → 0 < ν → ∀ μ : ℂ, ∀ F : Profile → MeridC, IsSmoothForceFn c F →
    ∀ (s q η : ℝ), smoothHeatInt c ν μ F (s, q + c, η) = smoothHeatInt c ν μ F (s, q, η)

/-- **(S3)** Regularity of the heat integral: continuous on all of `ℝ × ℝ²` (it vanishes for
`s < s₁` since `F = 0` there; for `s > 0` change variable `σ = s t`, `t ∈ (0,1)`, differentiate
`planeHeat` under the integral — `F` is smooth, periodic, compactly supported in `η`, so all its
derivatives are bounded — dominated convergence), and for `s > 0` each component is `C¹` in `(q,η)`
with `(s,q,η) ↦ fderiv` continuous (lines 3379-3383). -/
def HeatIntRegular : Prop :=
  ∀ (c ν : ℝ), 0 < c → 0 < ν → ∀ μ : ℂ, ∀ F : Profile → MeridC, IsSmoothForceFn c F →
    Continuous (smoothHeatInt c ν μ F) ∧
    (∀ s : ℝ, 0 < s → ∀ i : Fin 2, Differentiable ℝ (fun y : ℝ × ℝ => smoothHeatInt c ν μ F (s, y) i)) ∧
    ∀ i : Fin 2, ContinuousOn
      (fun p : Chart => fderiv ℝ (fun y : ℝ × ℝ => smoothHeatInt c ν μ F (p.1, y) i) p.2)
      (Ioi (0 : ℝ) ×ˢ univ)

/-- **(S4)** The heat integral of a force with divergence free slices is divergence free for
`s > 0`: `∂_j` commutes with `planeHeat` and with `∫ dσ` (derivatives of `F` bounded, as in
`HeatIntRegular`), so `div u(s) = ∫₀^s (σ/s)^μ e^{ν(s-σ)Δ} div F(σ) dσ = 0` (lines 1684-1689). -/
def HeatIntDivZero : Prop :=
  ∀ (c ν : ℝ), 0 < c → 0 < ν → ∀ μ : ℂ, ∀ F : Profile → MeridC, IsSmoothForceFn c F →
    (∀ σ y, slabDiv F σ y = 0) →
      ∀ s : ℝ, 0 < s → ∀ y : ℝ × ℝ,
        ∑ j : Fin 2, fderiv ℝ (fun z : ℝ × ℝ => smoothHeatInt c ν μ F (s, z) j) y
          (UnforcedLeray.B0579.dir j) = 0

/-- **(S5)** A `C¹` `c`-periodic function has the classical derivative as weak cell derivative
(integration by parts on `[-c/2,c/2)`: the `q`-boundary terms cancel by periodicity and the test
function vanishes for `|η|` large; both integrands are continuous with `η`-compact support). -/
def PeriodicWeakDeriv : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ φ : ℝ × ℝ → ℂ, ContDiff ℝ 1 φ → (∀ x : ℝ × ℝ, φ (x.1 + c, x.2) = φ x) →
    ∀ j : Fin 2, HasWeakCellDerivC c j φ (fun x => fderiv ℝ φ x (UnforcedLeray.B0579.dir j))

/-- **(S6)** Local finite energy (lines 1650-1658, 1684-1689): for `s ∈ [s₁,s₂]`
`‖u(s)‖_{L²(cell)} ≤ ∫₀^s (σ/s)^{Re μ}‖F(σ)‖_{L²(cell)}dσ` and the same for `∇u` with `∇F`
(Minkowski plus the `L²` contraction of `planeHeat`, `HeatCylinder.memLp_planeHeat`), uniformly in
`s ∈ [s₁,s₂]`; `u`, `∇u` are continuous so the `lintegral` over the cell is finite. -/
def HeatIntEnergyLoc : Prop :=
  ∀ (c ν : ℝ), 0 < c → 0 < ν → ∀ μ : ℂ, ∀ F : Profile → MeridC, IsSmoothForceFn c F →
    ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      ∫⁻ p in Icc s₁ s₂ ×ˢ UnforcedLeray.B0579.cell c,
        ENNReal.ofReal (vnorm2 (velF c (smoothHeatInt c ν μ F) p) ^ 2 +
          tnorm2 (gradOf (velF c (smoothHeatInt c ν μ F)) p) ^ 2) < ⊤


theorem velF_of_periodic (c : ℝ) (u : Profile → MeridC)
    (hper : ∀ (s q η : ℝ), u (s, q + c, η) = u (s, q, η)) :
    velF c u = fun x i => u x i := by
  funext x i
  obtain ⟨s, q, η⟩ := x
  unfold velF UnforcedLeray.Short.PartIIIb.NearInst.Masked.cellPtInv
  by_cases h : 0 < q
  · simp [h]
  · simp [h, hper]

theorem heatIntEnergy_of (h1 : SlabDivZero) (h2 : HeatIntPeriodic) (h3 : HeatIntRegular)
    (h4 : HeatIntDivZero) (h5 : PeriodicWeakDeriv) (h6 : HeatIntEnergyLoc) :
    HeatIntEnergy := by
  intro c ν hc hν μ hμ g hg F hF hgF hzero
  have hdiv := h1 c hc g hg.1 F hF hgF
  obtain ⟨hcont, hdiff, hfc⟩ := h3 c ν hc hν μ F hF
  have hvel := velF_of_periodic c (smoothHeatInt c ν μ F) (h2 c ν hc hν μ F hF)
  have hD := h4 c ν hc hν μ F hF hdiv
  have h7 := h6 c ν hc hν μ F hF
  rw [hvel] at hzero h7
  refine ⟨gradOf (velF c (smoothHeatInt c ν μ F)), ?_⟩
  rw [hvel]
  -- weak derivative of each component at each age s > 0
  have hw : ∀ s : ℝ, 0 < s → ∀ i j : Fin 2, HasWeakCellDerivC c j
      (fun x => smoothHeatInt c ν μ F (s, x) i)
      (fun x => gradOf (fun x i => smoothHeatInt c ν μ F x i) (s, x) i j) := by
    intro s hs i j
    have hC1 : ContDiff ℝ 1 (fun y : ℝ × ℝ => smoothHeatInt c ν μ F (s, y) i) := by
      rw [contDiff_one_iff_fderiv]
      refine ⟨hdiff s hs i, ?_⟩
      exact (hfc i).comp_continuous (Continuous.prodMk continuous_const continuous_id)
        (fun y => ⟨hs, trivial⟩)
    have hp : ∀ x : ℝ × ℝ, smoothHeatInt c ν μ F (s, x.1 + c, x.2) i
        = smoothHeatInt c ν μ F (s, x.1, x.2) i := fun x => by
      have := h2 c ν hc hν μ F hF s x.1 x.2
      rw [this]
    have := h5 c hc _ hC1 hp j
    simpa [gradOf, hs] using this
  refine ⟨?_, ?_, h7, hzero, ?_, ?_⟩
  · intro i
    exact ((continuous_apply i).comp ((PiLp.continuous_ofLp 2 _).comp hcont)).measurable
  · intro i j
    have hA : ContinuousOn (fun x : Chart =>
        fderiv ℝ (fun y : ℝ × ℝ => smoothHeatInt c ν μ F (x.1, y) i) x.2
          (UnforcedLeray.B0579.dir j)) {x : Chart | 0 < x.1} := by
      have : {x : Chart | 0 < x.1} = Ioi (0 : ℝ) ×ˢ univ := by ext x; simp
      rw [this]
      exact (hfc i).clm_apply continuousOn_const
    have := hA.measurable_piecewise (g := fun _ => (0 : ℂ))
      (continuousOn_const) (measurableSet_lt measurable_const measurable_fst)
    convert this using 1
    funext x
    simp [gradOf, Set.piecewise]
  · refine Filter.Eventually.of_forall (fun s hs ψ hψ => ?_)
    have a0 := hw s hs 0 0
    have a1 := hw s hs 1 1
    obtain ⟨I0, J0⟩ := a0.1 ψ hψ
    obtain ⟨I1, J1⟩ := a1.1 ψ hψ
    have hz : ∀ x : ℝ × ℝ, gradOf (fun x i => smoothHeatInt c ν μ F x i) (s, x) 0 0 * (ψ x : ℂ)
        + gradOf (fun x i => smoothHeatInt c ν μ F x i) (s, x) 1 1 * (ψ x : ℂ) = 0 := by
      intro x
      have := hD s hs x
      rw [Fin.sum_univ_two] at this
      rw [← add_mul]
      simp only [gradOf, if_pos hs]
      simp [UnforcedLeray.B0579.dir] at this ⊢
      simp [this]
    beta_reduce
    rw [integral_add I0 I1, a0.2 ψ hψ, a1.2 ψ hψ, ← neg_add, ← integral_add J0 J1]
    simp [hz]
  · refine Filter.Eventually.of_forall (fun s hs i j => ?_)
    exact hw s hs i j

end UnforcedLeray.Short.PartIIa.N01
