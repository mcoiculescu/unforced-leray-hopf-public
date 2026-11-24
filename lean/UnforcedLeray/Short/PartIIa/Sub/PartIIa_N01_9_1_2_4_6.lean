import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_2_4
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_2_4_6.Slab

/-!
# `PartII-a:N01/9/1/2/4/6` (decomposition): `HeatIntEnergyLoc`

Source `the November 2 reference manuscript`
lines 1650-1658, 1684-1689 (finite local energy of the classical heat integral and of its gradient),
3379-3383, 3426-3430.  Reduction: `∇` of the heat integral is the heat integral of `∇F`
(`HeatGradIdentity`), `∇F` is again a smooth force (`DerivForceSmooth`), and the heat integral of a
smooth force has uniformly bounded `L²(cell)` slices for `s ∈ [s₁,s₂]` (`HeatIntSliceL2`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.B0220 (Profile HSpace measureH)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIIb.NearInst.Delta (velF)
open UnforcedLeray.Short.IIIa (vnorm2 tnorm2)

/-- The `j`-th cell derivative of a force, slice by slice: `(∂_j F)(σ,z) = ∂_{z_j} F(σ,·)(z)`. -/
def derivForce (j : Fin 2) (F : Profile → MeridC) : Profile → MeridC := fun p =>
  WithLp.toLp 2 (fun i : Fin 2 =>
    fderiv ℝ (fun z : ℝ × ℝ => F (p.1, z) i) p.2 (UnforcedLeray.B0579.dir j))

/-- **(D1)** The cell derivative of a smooth force is again a smooth force (smooth since `F` is;
`c`-periodic in `q` since `F` is; vanishing outside the slab `s ∈ [s₁, s₂+1]`, `|η| ≤ R+1`, where
`F` vanishes on an open neighbourhood). -/
def DerivForceSmooth : Prop :=
  ∀ (c : ℝ) (F : Profile → MeridC), IsSmoothForceFn c F → ∀ j : Fin 2,
    IsSmoothForceFn c (derivForce j F)

/-- **(D2)** `∇` commutes with the causal heat integral (lines 1684-1689, 3379-3383): `planeHeat` is
a Gaussian convolution and commutes with `∂_j`, and `∂_j` passes under `∫ dσ` (the derivatives of
`F` are bounded, as in `HeatIntRegular`). -/
def HeatGradIdentity : Prop :=
  ∀ (c ν : ℝ), 0 < c → 0 < ν → ∀ μ : ℂ, ∀ F : Profile → MeridC, IsSmoothForceFn c F →
    ∀ s : ℝ, 0 < s → ∀ (i j : Fin 2) (y : ℝ × ℝ),
      fderiv ℝ (fun z : ℝ × ℝ => smoothHeatInt c ν μ F (s, z) i) y (UnforcedLeray.B0579.dir j)
        = smoothHeatInt c ν μ (derivForce j F) (s, y) i

/-- **(D3)** Uniform `L²(cell)` bound of the heat integral on `s ∈ [s₁,s₂]` (lines 1650-1658,
1684-1689): Minkowski for the causal integral and the `L²(cell)` contraction of `planeHeat`
(`HeatCylinder.memLp_planeHeat`) give `‖u(s)‖_{L²(cell)} ≤ ∫₀^s (σ/s)^{Re μ}‖F(σ)/σ‖_{L²(cell)} dσ`,
bounded uniformly for `s ∈ [s₁,s₂]` since `F = 0` for `σ < s₁`. -/
def HeatIntSliceL2 : Prop :=
  ∀ (c ν : ℝ), 0 < c → 0 < ν → ∀ μ : ℂ, ∀ F : Profile → MeridC, IsSmoothForceFn c F →
    ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ → ∃ K : ENNReal, K ≠ ⊤ ∧
      ∀ s ∈ Icc s₁ s₂, ∀ i : Fin 2,
        ∫⁻ x in UnforcedLeray.B0579.cell c, ‖smoothHeatInt c ν μ F (s, x) i‖ₑ ^ 2 ≤ K

theorem heatIntEnergyLoc_of (hD1 : DerivForceSmooth) (hD2 : HeatGradIdentity)
    (hD3 : HeatIntSliceL2) (h2 : HeatIntPeriodic) (h3 : HeatIntRegular) :
    HeatIntEnergyLoc := by
  intro c ν hc hν μ F hF s₁ s₂ hs₁ hs₁₂
  have hvel := velF_of_periodic c _ (h2 c ν hc hν μ F hF)
  obtain ⟨K0, hK0, hb0⟩ := hD3 c ν hc hν μ F hF s₁ s₂ hs₁ hs₁₂
  have hK1 : ∀ j : Fin 2, ∃ K : ENNReal, K ≠ ⊤ ∧
      ∀ s ∈ Icc s₁ s₂, ∀ i : Fin 2, ∫⁻ x in UnforcedLeray.B0579.cell c,
        ‖smoothHeatInt c ν μ (derivForce j F) (s, x) i‖ₑ ^ 2 ≤ K :=
    fun j => hD3 c ν hc hν μ _ (hD1 c F hF j) s₁ s₂ hs₁ hs₁₂
  choose K1 hK1ne hb1 using hK1
  -- the integrand as a sum of squares of components
  let g : ℝ × (ℝ × ℝ) → ENNReal := fun p =>
    (∑ i : Fin 2, ‖smoothHeatInt c ν μ F p i‖ₑ ^ 2) +
      ∑ j : Fin 2, ∑ i : Fin 2, ‖smoothHeatInt c ν μ (derivForce j F) p i‖ₑ ^ 2
  have hcont : ∀ (G : Profile → MeridC), IsSmoothForceFn c G → ∀ i : Fin 2,
      Measurable (fun p : ℝ × (ℝ × ℝ) => ‖smoothHeatInt c ν μ G p i‖ₑ ^ 2) := by
    intro G hG i
    have := (h3 c ν hc hν μ G hG).1
    have h' : Continuous (fun p : ℝ × (ℝ × ℝ) => smoothHeatInt c ν μ G p i) :=
      (continuous_apply i).comp ((PiLp.continuous_ofLp 2 _).comp this)
    exact (h'.enorm.measurable).pow_const 2
  have hgm : Measurable g := by
    refine Measurable.add (Finset.measurable_sum _ fun i _ => hcont F hF i)
      (Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun i _ =>
        hcont _ (hD1 c F hF j) i)
  have hslice : ∀ s ∈ Icc s₁ s₂, ∫⁻ x in UnforcedLeray.B0579.cell c, g (s, x) ≤
      (∑ _i : Fin 2, K0) + ∑ j : Fin 2, ∑ _i : Fin 2, K1 j := by
    intro s hs
    have hm : ∀ (G : Profile → MeridC), IsSmoothForceFn c G → ∀ i : Fin 2,
        Measurable (fun x : ℝ × ℝ => ‖smoothHeatInt c ν μ G (s, x) i‖ₑ ^ 2) :=
      fun G hG i => (hcont G hG i).comp measurable_prodMk_left
    have hsum1 : Measurable (fun x : ℝ × ℝ =>
        ∑ i : Fin 2, ‖smoothHeatInt c ν μ F (s, x) i‖ₑ ^ 2) :=
      Finset.measurable_sum _ fun i _ => hm F hF i
    show ∫⁻ x in UnforcedLeray.B0579.cell c, ((∑ i : Fin 2, ‖smoothHeatInt c ν μ F (s, x) i‖ₑ ^ 2) +
      ∑ j : Fin 2, ∑ i : Fin 2, ‖smoothHeatInt c ν μ (derivForce j F) (s, x) i‖ₑ ^ 2) ≤ _
    rw [lintegral_add_left hsum1, lintegral_finset_sum _ (fun i _ => hm F hF i)]
    refine add_le_add (Finset.sum_le_sum fun i _ => hb0 s hs i) ?_
    rw [lintegral_finset_sum _ (fun j _ => Finset.measurable_sum _ fun i _ =>
      hm _ (hD1 c F hF j) i)]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [lintegral_finset_sum _ (fun i _ => hm _ (hD1 c F hF j) i)]
    exact Finset.sum_le_sum fun i _ => hb1 j s hs i
  have hKne : (∑ _i : Fin 2, K0) + ∑ j : Fin 2, ∑ _i : Fin 2, K1 j ≠ ⊤ := by
    refine ENNReal.add_ne_top.2 ⟨?_, ?_⟩
    · exact ENNReal.sum_ne_top.2 fun _ _ => hK0
    · exact ENNReal.sum_ne_top.2 fun j _ => ENNReal.sum_ne_top.2 fun _ _ => hK1ne j
  have hfin := slab_lintegral_lt_top c s₁ s₂ g hgm _ hKne hslice
  refine lt_of_le_of_lt (le_of_eq ?_) hfin
  refine setLIntegral_congr_fun
    (measurableSet_Icc.prod ?_) ?_
  · exact (measurableSet_Ico).prod MeasurableSet.univ
  · intro p hp
    obtain ⟨s, x⟩ := p
    have hs : 0 < s := lt_of_lt_of_le hs₁ hp.1.1
    rw [hvel]
    have hgrad : ∀ i j : Fin 2, gradOf (fun x i => smoothHeatInt c ν μ F x i) (s, x) i j =
        smoothHeatInt c ν μ (derivForce j F) (s, x) i := by
      intro i j
      simp only [gradOf, hs, if_true]
      exact hD2 c ν hc hν μ F hF s hs i j x
    have e1 : vnorm2 (fun i => smoothHeatInt c ν μ F (s, x) i) ^ 2 =
        ∑ i : Fin 2, ‖smoothHeatInt c ν μ F (s, x) i‖ ^ 2 := by
      unfold vnorm2
      rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
    have e2 : tnorm2 (gradOf (fun x i => smoothHeatInt c ν μ F x i) (s, x)) ^ 2 =
        ∑ j : Fin 2, ∑ i : Fin 2, ‖smoothHeatInt c ν μ (derivForce j F) (s, x) i‖ ^ 2 := by
      unfold tnorm2
      rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity)]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
      rw [hgrad i j]
    have key : ∀ z : ℂ, ENNReal.ofReal (‖z‖ ^ 2) = ‖z‖ₑ ^ 2 := by
      intro z
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    show ENNReal.ofReal _ = g (s, x)
    rw [e1, e2, ENNReal.ofReal_add (Finset.sum_nonneg fun i _ => by positivity)
      (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => by positivity),
      ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity),
      ENNReal.ofReal_sum_of_nonneg (fun j _ => Finset.sum_nonneg fun i _ => by positivity)]
    have hin : ∀ j : Fin 2, ENNReal.ofReal (∑ i : Fin 2,
        ‖smoothHeatInt c ν μ (derivForce j F) (s, x) i‖ ^ 2) =
        ∑ i : Fin 2, ‖smoothHeatInt c ν μ (derivForce j F) (s, x) i‖ₑ ^ 2 := fun j => by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
      simp only [key]
    simp only [key, hin]
    rfl

end UnforcedLeray.Short.PartIIa.N01
