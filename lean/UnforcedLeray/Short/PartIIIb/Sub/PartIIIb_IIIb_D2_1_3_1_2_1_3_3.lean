import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1_5
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.PairCont
import UnforcedLeray.Short.PartIIa.Tasks.F05aAdjResolventSolution.PhaseTestDerivBounded

/-!
# `intertwineLiouville`: decomposition

Source `the November 2 reference manuscript`
lines 1351-1362 (the adjoint at `r = 2` has the maximal graph; Coulomb stream potentials with the
Hardy bound) and 1470-1480 (radial cutoffs and mollification in this graph).

The defect `F(X) = ⟪wOpT X, ψ⟫ - ⟪X, w⟫` (`ψ, w` with `ψ/|y|, w/|y| ∈ Y_2`) vanishes on curls and
on gradients of phase tests; it vanishes on every phase test.

Route (Weyl's lemma by an approximate identity, as `WeylL2` of
`PartIII-b_IIIb-D2_1_3_1_2_1_3_1_5.lean`, whose kernel Props `RadialPotential`, `DilKerOK`,
`DilLap`, `ConvTest`, `ConvLap`, `ConvSub`, `CurlIsSolTest`, `DivIsPhaseTest`, `CurlCurlId`
are reused):
* (I) `ΔV = ∇ div V - curl curl V`, so `F(ΔV) = 0` for every vector phase test `V`
  (`defect_lap`); `F` is additive on phase tests (`defect_sub`, via `⟪X, f⟫ = ⟪|y|X, f/|y|⟫`).
* (II) With the radial kernels `b`, `u` (`Δu = b - b_{(2)}`), `g(s) = F(Θ * b_{(s)})` satisfies
  `g(s) = g(2s)`.
* (III) Large scale (`MolLarge`, `HardyPairBound`): `‖Θ * b_{(s)}‖_∞ + ‖wOpT(Θ * b_{(s)})‖_∞
  ≲ s⁻³` with `y`-support radius `≲ s` (the drift `y·∇` costs `s`, the derivative put on the
  kernel gains `s⁻¹`), and `|⟪X, f⟫| ≤ C ‖X‖_∞ ρ^{5/2}` by Cauchy–Schwarz against `f/|y|`;
  so `g(s) = O(s^{-1/2})`.
* (IV) Small scale (`MolSmall`): `Θ * b_{(s)} → Θ` together with `wOpT`, uniformly at rate `s`,
  inside a fixed ball, so `g(s) → F(Θ)`.  Hence `F(Θ) = 0`.

Status: every analytic Prop stated here is proved in this file (`hardyPairBound`, `convFDeriv`,
`convLapT`, `convDyKer`, `convSupBound`, `convSupport`, `phaseTestSliceL1`, `dilKBounds`,
`dilKIntegral`, `phaseTestLipY`, `convApprox_of`, `molLarge_of`, `molSmall_of`), and
`liouville_of_kernels` gives `IntertwineLiouville` from the nine reused kernel Props alone.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.Liou

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)
open UnforcedLeray.Short.PartIIIb.Concrete

/-! ## The analytic ingredients -/

/-- **Hardy pairing bound** (source 1351-1362: the stream potentials of `StreamPot` satisfy the
Hardy bound `ψ/|y| ∈ Y_2`).  For `f` with `f/|y| ∈ Y_2` there is `C` such that every phase test
`X` with `‖X‖ ≤ A` vanishing for `‖y‖ > ρ` has `‖⟪X, f⟫‖ ≤ C A ρ^{5/2}`.  Proof: `⟪X, f⟫ =
⟪|y| X, f/|y|⟫` (`pairF_weight`; `{y = 0}` is null), Cauchy–Schwarz in `Y_2` (`pair_enorm_le`,
`dot_integrable`), and `‖|y| X‖_{Y_2} ≤ A ρ |B_ρ|^{1/2} = A ρ^{5/2} |B_1|^{1/2}`. -/
def HardyPairBound : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ f : ℝ × Space → CVec3,
    UnforcedLeray.Short.IIb.IsInYr P 2 (fun x => (‖x.2‖⁻¹ : ℝ) • f x) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ × Space → CVec3, IsPhaseTest P X →
        ∀ A ρ : ℝ, 0 ≤ A → 0 < ρ → (∀ x, ‖X x‖ ≤ A) → (∀ x, ρ < ‖x.2‖ → X x = 0) →
          ‖pairF P X f‖ ≤ C * A * (ρ ^ 2 * Real.sqrt ρ)

/-- **Derivatives fall on the test** (source 1470-1480, mollification in `y`): for a smooth
compactly supported kernel `κ` and a phase test `Θ`, `D(κ * Θ)(p) v = (κ * (DΘ(·) v))(p)`
(Mathlib `hasFDerivAt_convolution_right_with_param`, the phase as parameter). -/
def ConvFDeriv : Prop :=
  ∀ (P : ℝ) (κ : Space → ℝ) (Θ : ℝ × Space → CVec3), KerOK κ → IsPhaseTest P Θ →
    ∀ v : ℝ × Space, (fun p => fderiv ℝ (convY κ Θ) p v) = convY κ (fun p => fderiv ℝ Θ p v)

/-- The Laplacian commutes with the convolution in `y` (source 1470-1480): `Δ(κ * Θ) = κ * ΔΘ`
(`ConvFDeriv` twice, and linearity of the integral over the three directions). -/
def ConvLapT : Prop :=
  ∀ (P : ℝ) (κ : Space → ℝ) (Θ : ℝ × Space → CVec3), KerOK κ → IsPhaseTest P Θ →
    lapT (convY κ Θ) = convY κ (lapT Θ)

/-- **A derivative put on the kernel** (source 1470-1480): `∂ⱼ(κ * Θ) = (∂ⱼκ) * Θ`
(`convY κ Θ (τ, ·) = κ ⋆ Θ(τ, ·)`, Mathlib `HasCompactSupport.hasFDerivAt_convolution_left`). -/
def ConvDyKer : Prop :=
  ∀ (P : ℝ) (κ : Space → ℝ) (Θ : ℝ × Space → CVec3), KerOK κ → IsPhaseTest P Θ →
    ∀ j : Fin 3, dy j (convY κ Θ) = convY (sd j κ) Θ

/-- Sup bound of the convolution by the sup of the kernel and the `L¹` norm of the slice
(source 1470-1480): `‖(κ * Θ)(τ, y)‖ ≤ ‖κ‖_∞ ∫ ‖Θ(τ, z)‖ dz`. -/
def ConvSupBound : Prop :=
  ∀ (P : ℝ) (κ : Space → ℝ) (Θ : ℝ × Space → CVec3) (K : ℝ), IsPhaseTest P Θ →
    (∀ z, |κ z| ≤ K) → ∀ x : ℝ × Space, ‖convY κ Θ x‖ ≤ K * ∫ z, ‖Θ (x.1, z)‖

/-- Support of the convolution (source 1470-1480): radii add. -/
def ConvSupport : Prop :=
  ∀ (κ : Space → ℝ) (Θ : ℝ × Space → CVec3) (r R : ℝ), (∀ z, r < ‖z‖ → κ z = 0) →
    (∀ τ y, R < ‖y‖ → Θ (τ, y) = 0) → ∀ x : ℝ × Space, R + r < ‖x.2‖ → convY κ Θ x = 0

/-- The slices of a phase test are uniformly bounded in `L¹(ℝ³)` (`P > 0`: bounded by
periodicity and compactness, `y`-support in a fixed ball). -/
def PhaseTestSliceL1 : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ Θ : ℝ × Space → CVec3, IsPhaseTest P Θ →
    ∃ M : ℝ, 0 ≤ M ∧ ∀ τ : ℝ, ∫ z, ‖Θ (τ, z)‖ ≤ M

/-- **Scaling of the mollifier** (source 1470-1480): `b_{(s)} = s⁻³ b(·/s)` has
`‖b_{(s)}‖_∞ ≲ s⁻³`, `‖∂ⱼ b_{(s)}‖_∞ ≲ s⁻⁴`, and both vanish for `‖z‖ > r s`. -/
def DilKBounds : Prop :=
  ∀ b : Space → ℝ, KerOK b → ∃ K r : ℝ, 0 ≤ K ∧ 0 < r ∧ ∀ s : ℝ, 0 < s → ∀ z : Space,
    |dilK b s z| ≤ K * (s⁻¹) ^ 3 ∧ (∀ j : Fin 3, |sd j (dilK b s) z| ≤ K * (s⁻¹) ^ 4) ∧
      (r * s < ‖z‖ → dilK b s z = 0 ∧ ∀ j : Fin 3, sd j (dilK b s) z = 0)

/-- The mass-preserving dilation preserves `∫ κ` and `∫ |κ|` (change of variables
`z = s z'`, Mathlib `Measure.integral_comp_inv_smul_of_nonneg`). -/
def DilKIntegral : Prop :=
  ∀ (κ : Space → ℝ) (s : ℝ), 0 < s →
    (∫ z, dilK κ s z) = ∫ z, κ z ∧ (∫ z, |dilK κ s z|) = ∫ z, |κ z|

/-- A phase test is uniformly Lipschitz in `y` (`P > 0`: its first derivative is bounded,
`phaseTestDerivBounded_proof`, then the mean value inequality on each slice). -/
def PhaseTestLipY : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ G : ℝ × Space → CVec3, IsPhaseTest P G →
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (τ : ℝ) (y y' : Space), ‖G (τ, y) - G (τ, y')‖ ≤ L * ‖y - y'‖

/-- **Approximate identity with rate** (source 1470-1480): for `∫ b = 1`,
`‖G * b_{(s)} - G‖_∞ ≤ C s` (`∫ b_{(s)} = 1`, `b_{(s)}` supported in `‖z‖ ≤ r s`,
`‖G(τ, y - z) - G(τ, y)‖ ≤ L ‖z‖`, `∫ |b_{(s)}| = ∫ |b|`). -/
def ConvApprox : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ (b : Space → ℝ) (G : ℝ × Space → CVec3), KerOK b → ∫ z, b z = 1 →
    IsPhaseTest P G → ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 < s → ∀ x : ℝ × Space,
      ‖convY (dilK b s) G x - G x‖ ≤ C * s

/-- **Large-scale bounds of the mollified test** (source 1470-1480: the drift commutator of a
dilated cutoff is bounded): for `s ≥ 1`, `X_s = convY (dilK b s) Θ` and `wOpT X_s` are
`O(s⁻³)` and vanish for `‖y‖ > ρ₀ s`.  (`∂_τ`, `Δ` fall on `Θ`: `ConvFDeriv`, `ConvLapT`;
`y·∇X_s = ∑ yⱼ (∂ⱼ b_{(s)}) * Θ` with `|y| ≤ ρ₀ s` and `‖∂ⱼ b_{(s)}‖_∞ ≲ s⁻⁴`: `ConvDyKer`,
`DilKBounds`; then `ConvSupBound`, `PhaseTestSliceL1`, `ConvSupport`, `wOpT_eq`,
`wOpT_support`.) -/
def MolLarge : Prop :=
  ∀ (P ν μ : ℝ), 0 < P → ∀ (b : Space → ℝ) (Θ : ℝ × Space → CVec3), KerOK b → IsPhaseTest P Θ →
    ∃ C ρ₀ : ℝ, 0 ≤ C ∧ 0 < ρ₀ ∧ ∀ s : ℝ, 1 ≤ s →
      (∀ x, ‖convY (dilK b s) Θ x‖ ≤ C * (s⁻¹) ^ 3) ∧
      (∀ x, ‖wOpT ν μ (convY (dilK b s) Θ) x‖ ≤ C * (s⁻¹) ^ 3) ∧
      (∀ x, ρ₀ * s < ‖x.2‖ → convY (dilK b s) Θ x = 0 ∧ wOpT ν μ (convY (dilK b s) Θ) x = 0)

/-- **Small-scale convergence of the mollified test** (source 1470-1480: mollification in `y`
converges in the graph): for `0 < s ≤ 1`, `X_s - Θ` and `wOpT X_s - wOpT Θ` are `O(s)` and vanish
for `‖y‖ > ρ₀`.  (`∂_τ`, `∂ⱼ`, `Δ` fall on `Θ`: `ConvFDeriv`, `ConvLapT`; `ConvApprox` for
`Θ, ∂_τΘ, ∂ⱼΘ, ΔΘ`; `|y| ≤ ρ₀` on the support: `ConvSupport`, `DilKBounds`, `wOpT_support`.) -/
def MolSmall : Prop :=
  ∀ (P ν μ : ℝ), 0 < P → ∀ (b : Space → ℝ) (Θ : ℝ × Space → CVec3), KerOK b →
    ∫ z, b z = 1 → IsPhaseTest P Θ →
    ∃ C ρ₀ : ℝ, 0 ≤ C ∧ 0 < ρ₀ ∧ ∀ s : ℝ, 0 < s → s ≤ 1 →
      (∀ x, ‖convY (dilK b s) Θ x - Θ x‖ ≤ C * s) ∧
      (∀ x, ‖wOpT ν μ (convY (dilK b s) Θ) x - wOpT ν μ Θ x‖ ≤ C * s) ∧
      (∀ x, ρ₀ < ‖x.2‖ → convY (dilK b s) Θ x - Θ x = 0 ∧
        wOpT ν μ (convY (dilK b s) Θ) x - wOpT ν μ Θ x = 0)

/-! ## Proven helpers -/

/-- `wOpT = ∂_τ - ½ y·∇ - νΔ + (μ - 1)`. -/
theorem wOpT_eq (ν μ : ℝ) (X : ℝ × Space → CVec3) (x : ℝ × Space) :
    wOpT ν μ X x = dτ X x - (1 / 2 : ℝ) • radialT X x - ν • lapT X x + ((μ : ℂ) - 1) • X x := by
  simp only [wOpT, L0, T0, sub_smul, one_smul]
  rw [show ((1 / 2 : ℝ) • X x) = ((((1 / 2 : ℝ)) : ℂ) • X x) from (Complex.coe_smul _ _).symm]
  have h2 : (((1 / 2 : ℝ)) : ℂ) • X x + (((1 / 2 : ℝ)) : ℂ) • X x = X x := by
    rw [← add_smul]; norm_num
  linear_combination (norm := module) (-1 : ℂ) • h2

theorem isPhaseTest_wOpT {P : ℝ} {Θ : ℝ × Space → CVec3} (hΘ : IsPhaseTest P Θ) (ν μ : ℝ) :
    IsPhaseTest P (wOpT ν μ Θ) := by
  have h := ((UnforcedLeray.Short.IIb.isPhaseTest_L0 hΘ ν).add (hΘ.const_smul (μ : ℂ))).sub
    (hΘ.const_smul (1 / 2 : ℝ))
  convert h using 1
  funext p
  simp [wOpT]

/-- A function vanishing on the open set `{‖y‖ > ρ}` has vanishing derivatives there. -/
theorem fderiv_eq_zero_of_vanish {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ρ : ℝ} {X : ℝ × Space → F} (hX : ∀ x : ℝ × Space, ρ < ‖x.2‖ → X x = 0)
    (x : ℝ × Space) (hx : ρ < ‖x.2‖) (v : ℝ × Space) : fderiv ℝ X x v = 0 := by
  have hopen : IsOpen {p : ℝ × Space | ρ < ‖p.2‖} :=
    isOpen_lt continuous_const (continuous_norm.comp continuous_snd)
  have hev : X =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hopen.mem_nhds hx] with p hp
    exact hX p hp
  simp [hev.fderiv_eq]

/-- `wOpT X` vanishes where `X` vanishes on a neighbourhood `{‖y‖ > ρ}`. -/
theorem wOpT_support (ν μ ρ : ℝ) {X : ℝ × Space → CVec3}
    (hX : ∀ x : ℝ × Space, ρ < ‖x.2‖ → X x = 0) (x : ℝ × Space) (hx : ρ < ‖x.2‖) :
    wOpT ν μ X x = 0 := by
  have hdy : ∀ j : Fin 3, ∀ p : ℝ × Space, ρ < ‖p.2‖ → dy j X p = 0 :=
    fun j p hp => fderiv_eq_zero_of_vanish hX p hp _
  have hτ : dτ X x = 0 := fderiv_eq_zero_of_vanish hX x hx _
  have hrad : radialT X x = 0 := by
    simp [radialT, hdy _ x hx]
  have hlap : lapT X x = 0 := by
    simp [lapT, fun j => fderiv_eq_zero_of_vanish (hdy j) x hx (0, coordinateVector j), dy]
  rw [wOpT_eq, hτ, hrad, hlap, hX x hx]
  simp

theorem differentiable_of_smooth {X : ℝ × Space → CVec3} (h : ContDiff ℝ ∞ X) :
    Differentiable ℝ X :=
  h.differentiable (by simp)

theorem smooth_dy {X : ℝ × Space → CVec3} (h : ContDiff ℝ ∞ X) (j : Fin 3) :
    ContDiff ℝ ∞ (dy j X) := by
  unfold dy
  exact (h.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem fderiv_sub_apply {A B : ℝ × Space → CVec3} (hA : Differentiable ℝ A)
    (hB : Differentiable ℝ B) (p v : ℝ × Space) :
    fderiv ℝ (fun x => A x - B x) p v = fderiv ℝ A p v - fderiv ℝ B p v := by
  rw [fderiv_fun_sub (hA p) (hB p)]
  rfl

theorem dτ_sub {A B : ℝ × Space → CVec3} (hA : Differentiable ℝ A) (hB : Differentiable ℝ B) :
    dτ (fun x => A x - B x) = fun x => dτ A x - dτ B x :=
  funext fun p => fderiv_sub_apply hA hB p _

theorem dy_sub {A B : ℝ × Space → CVec3} (hA : Differentiable ℝ A) (hB : Differentiable ℝ B)
    (j : Fin 3) : dy j (fun x => A x - B x) = fun x => dy j A x - dy j B x :=
  funext fun p => fderiv_sub_apply hA hB p _

theorem radialT_sub {A B : ℝ × Space → CVec3} (hA : Differentiable ℝ A)
    (hB : Differentiable ℝ B) :
    radialT (fun x => A x - B x) = fun x => radialT A x - radialT B x := by
  funext p
  simp only [radialT, dy_sub hA hB, smul_sub, Finset.sum_sub_distrib]

theorem lapT_sub {A B : ℝ × Space → CVec3} (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) :
    lapT (fun x => A x - B x) = fun x => lapT A x - lapT B x := by
  funext p
  simp only [lapT, dy_sub (differentiable_of_smooth hA) (differentiable_of_smooth hB),
    dy_sub (differentiable_of_smooth (smooth_dy hA _))
      (differentiable_of_smooth (smooth_dy hB _)), Finset.sum_sub_distrib]

/-- `wOpT` is additive on smooth fields. -/
theorem wOpT_sub (ν μ : ℝ) {A B : ℝ × Space → CVec3} (hA : ContDiff ℝ ∞ A)
    (hB : ContDiff ℝ ∞ B) :
    wOpT ν μ (fun x => A x - B x) = fun x => wOpT ν μ A x - wOpT ν μ B x := by
  funext p
  simp only [wOpT_eq, dτ_sub (differentiable_of_smooth hA) (differentiable_of_smooth hB),
    radialT_sub (differentiable_of_smooth hA) (differentiable_of_smooth hB), lapT_sub hA hB,
    smul_sub]
  abel

/-- The Hardy weight: `⟪X, f⟫ = ⟪|y| X, f/|y|⟫` (the integrands agree off the null set
`{y = 0}` of each slice). -/
theorem pairF_weight (P : ℝ) (X f : ℝ × Space → CVec3) :
    pairF P X f = pairF P (fun x => (‖x.2‖ : ℝ) • X x) (fun x => (‖x.2‖⁻¹ : ℝ) • f x) := by
  unfold pairF phaseInt
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  refine integral_congr_ae ?_
  filter_upwards [Measure.ae_ne (volume : Measure Space) 0] with y hy
  have hn : (‖y‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hy
  simp only [dotL_apply, PiLp.smul_apply, ← Complex.coe_smul, smul_eq_mul, Complex.ofReal_inv]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

/-- A weighted phase test `|y| X` lies in `Y_2` (continuous, periodic, bounded support). -/
theorem isInYr_weight {P : ℝ} {X : ℝ × Space → CVec3} (hX : IsPhaseTest P X) :
    UnforcedLeray.Short.IIb.IsInYr P 2 (fun x => (‖x.2‖ : ℝ) • X x) := by
  have hc : Continuous (fun x : ℝ × Space => (‖x.2‖ : ℝ) • X x) :=
    (continuous_norm.comp continuous_snd).smul hX.continuous
  refine ⟨Filter.Eventually.of_forall fun x => ?_, hc.aestronglyMeasurable, ?_⟩
  · show (‖x.2‖ : ℝ) • X (x.1 + P, x.2) = (‖x.2‖ : ℝ) • X x
    rw [hX.periodic x.1 x.2]
  obtain ⟨R, hR⟩ := hX.bounded_support
  have hK : IsCompact (Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) R) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  have hbd : ∀ t ∈ Ioc (0 : ℝ) P, ∀ y : Space,
      ‖(fun x : ℝ × Space => (‖x.2‖ : ℝ) • X x) (t, y)‖ₑ ^ (2 : ℝ) ≤
        (Metric.closedBall (0 : Space) R).indicator (fun _ => ENNReal.ofReal C ^ (2 : ℝ)) y := by
    intro t ht y
    by_cases hy : y ∈ Metric.closedBall (0 : Space) R
    · rw [Set.indicator_of_mem hy]
      gcongr
      have := hC (t, y) ⟨⟨ht.1.le, ht.2⟩, hy⟩
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal this
    · rw [Set.indicator_of_notMem hy]
      have : X (t, y) = 0 := hR t y (by simpa [mem_closedBall_zero_iff] using hy)
      simp [this]
  have hfin : ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space,
      ‖(fun x : ℝ × Space => (‖x.2‖ : ℝ) • X x) (t, y)‖ₑ ^ (2 : ℝ) < ⊤ := by
    calc ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space,
          ‖(fun x : ℝ × Space => (‖x.2‖ : ℝ) • X x) (t, y)‖ₑ ^ (2 : ℝ)
        ≤ ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space,
            (Metric.closedBall (0 : Space) R).indicator
              (fun _ => ENNReal.ofReal C ^ (2 : ℝ)) y := by
          refine setLIntegral_mono' measurableSet_Ioc fun t ht => ?_
          exact lintegral_mono fun y => hbd t ht y
      _ < ⊤ := by
          simp only [lintegral_indicator_const measurableSet_closedBall, setLIntegral_const]
          refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ?_ measure_closedBall_lt_top) ?_
          · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
          · simp
  show (ENNReal.ofReal P⁻¹ * _) ^ (1 / (2 : ℝ)) < ⊤
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin).ne

/-- Additivity of the pairing in the test slot against a Hardy field `f` (`f/|y| ∈ Y_2`). -/
theorem hardyPairSub {P : ℝ} (hP : 0 < P) {f : ℝ × Space → CVec3}
    (hf : UnforcedLeray.Short.IIb.IsInYr P 2 (fun x => (‖x.2‖⁻¹ : ℝ) • f x))
    {A B : ℝ × Space → CVec3} (hA : IsPhaseTest P A) (hB : IsPhaseTest P B) :
    pairF P (fun x => A x - B x) f = pairF P A f - pairF P B f := by
  have hAB : IsPhaseTest P (fun x => A x - B x) := hA.sub hB
  rw [pairF_weight P (fun x => A x - B x) f, pairF_weight P A f, pairF_weight P B f]
  have iA := dot_integrable hP (isInYr_weight hA) hf
  have iB := dot_integrable hP (isInYr_weight hB) hf
  have iAB := dot_integrable hP (isInYr_weight hAB) hf
  rw [pair_eq_integral P _ _ iAB, pair_eq_integral P _ _ iA, pair_eq_integral P _ _ iB,
    ← smul_sub, ← integral_sub iA iB]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp [smul_sub, map_sub]

/-- **`HardyPairBound` holds**: `⟪X, f⟫ = ⟪|y|X, f/|y|⟫`, Cauchy–Schwarz in `Y_2`, and
`‖|y|X‖_{Y_2} ≤ Aρ |B_ρ|^{1/2}`, `|B_ρ| = ρ³ |B_1|`. -/
theorem hardyPairBound : HardyPairBound := by
  intro P hP f hf
  set N : ℝ≥0∞ := UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => (‖x.2‖⁻¹ : ℝ) • f x)
    with hNdef
  have hN : N ≠ ⊤ := hf.finite.ne
  set V : ℝ≥0∞ := volume (Metric.ball (0 : Space) 1) with hVdef
  have hV : V ≠ ⊤ := measure_ball_lt_top.ne
  refine ⟨N.toReal * (V ^ (1 / 2 : ℝ)).toReal, by positivity, ?_⟩
  intro X hX A ρ hA hρ hXA hXs
  have hW := isInYr_weight hX
  have iX := dot_integrable hP hW hf
  have h1 := pair_enorm_le hP _ _ hW.meas hf.meas iX
  rw [← pairF_weight P X f] at h1
  have hpt : ∀ t : ℝ, ∀ y : Space,
      ‖(fun x : ℝ × Space => (‖x.2‖ : ℝ) • X x) (t, y)‖ₑ ^ (2 : ℝ) ≤
        (Metric.closedBall (0 : Space) ρ).indicator
          (fun _ => ENNReal.ofReal (A * ρ) ^ (2 : ℝ)) y := by
    intro t y
    by_cases hy : y ∈ Metric.closedBall (0 : Space) ρ
    · rw [Set.indicator_of_mem hy]
      gcongr
      rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      have hy' : ‖y‖ ≤ ρ := by simpa [mem_closedBall_zero_iff] using hy
      show ‖(‖y‖ : ℝ) • X (t, y)‖ ≤ A * ρ
      rw [norm_smul, Real.norm_eq_abs, abs_norm]
      calc ‖y‖ * ‖X (t, y)‖ ≤ ρ * A := mul_le_mul hy' (hXA _) (norm_nonneg _) hρ.le
        _ = A * ρ := mul_comm _ _
    · rw [Set.indicator_of_notMem hy]
      have : X (t, y) = 0 := hXs (t, y) (by simpa [mem_closedBall_zero_iff] using hy)
      simp [this]
  have hball : volume (Metric.closedBall (0 : Space) ρ) = ENNReal.ofReal (ρ ^ 3) * V := by
    rw [Measure.addHaar_closedBall volume (0 : Space) hρ.le, finrank_euclideanSpace,
      Fintype.card_fin]
  have hint : ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space,
      ‖(fun x : ℝ × Space => (‖x.2‖ : ℝ) • X x) (t, y)‖ₑ ^ (2 : ℝ) ≤
        ENNReal.ofReal P * (ENNReal.ofReal (A * ρ) ^ (2 : ℝ) * (ENNReal.ofReal (ρ ^ 3) * V)) := by
    calc ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space,
          ‖(fun x : ℝ × Space => (‖x.2‖ : ℝ) • X x) (t, y)‖ₑ ^ (2 : ℝ)
        ≤ ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, (Metric.closedBall (0 : Space) ρ).indicator
            (fun _ => ENNReal.ofReal (A * ρ) ^ (2 : ℝ)) y :=
          lintegral_mono fun t => lintegral_mono fun y => hpt t y
      _ = ENNReal.ofReal P *
            (ENNReal.ofReal (A * ρ) ^ (2 : ℝ) * (ENNReal.ofReal (ρ ^ 3) * V)) := by
          rw [lintegral_indicator_const measurableSet_closedBall, hball, setLIntegral_const,
            Real.volume_Ioc, sub_zero, mul_comm]
  have hP' : ENNReal.ofReal P⁻¹ * ENNReal.ofReal P = 1 := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hP.le), inv_mul_cancel₀ hP.ne', ENNReal.ofReal_one]
  have hnorm : UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => (‖x.2‖ : ℝ) • X x) ≤
      ENNReal.ofReal (A * ρ) * (ENNReal.ofReal (ρ ^ 3) * V) ^ (1 / 2 : ℝ) := by
    unfold UnforcedLeray.Short.IIb.phaseLpNorm
    calc _ ≤ (ENNReal.ofReal P⁻¹ * (ENNReal.ofReal P *
            (ENNReal.ofReal (A * ρ) ^ (2 : ℝ) * (ENNReal.ofReal (ρ ^ 3) * V)))) ^ (1 / (2 : ℝ)) := by
          gcongr
      _ = (ENNReal.ofReal (A * ρ) ^ (2 : ℝ) * (ENNReal.ofReal (ρ ^ 3) * V)) ^ (1 / (2 : ℝ)) := by
          rw [← mul_assoc, hP', one_mul]
      _ = ENNReal.ofReal (A * ρ) * (ENNReal.ofReal (ρ ^ 3) * V) ^ (1 / 2 : ℝ) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
          norm_num
  have hE : ‖pairF P X f‖ₑ ≤
      ENNReal.ofReal (A * ρ) * (ENNReal.ofReal (ρ ^ 3) * V) ^ (1 / 2 : ℝ) * N :=
    h1.trans (mul_le_mul_left hnorm N)
  have hfin : ENNReal.ofReal (A * ρ) * (ENNReal.ofReal (ρ ^ 3) * V) ^ (1 / 2 : ℝ) * N ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hV))) hN
  have hreal : ‖pairF P X f‖ ≤
      (ENNReal.ofReal (A * ρ) * (ENNReal.ofReal (ρ ^ 3) * V) ^ (1 / 2 : ℝ) * N).toReal := by
    rw [← ENNReal.ofReal_le_iff_le_toReal hfin, ofReal_norm]
    exact hE
  have hsq : (ρ ^ 3) ^ (1 / 2 : ℝ) = ρ * Real.sqrt ρ := by
    rw [← Real.sqrt_eq_rpow, show ρ ^ 3 = ρ ^ 2 * ρ by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hρ.le]
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.toReal_mul,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
    ENNReal.toReal_ofReal (by positivity), hsq] at hreal
  calc ‖pairF P X f‖ ≤ A * ρ * (ρ * Real.sqrt ρ * (V ^ (1 / 2 : ℝ)).toReal) * N.toReal := hreal
    _ = N.toReal * (V ^ (1 / 2 : ℝ)).toReal * A * (ρ ^ 2 * Real.sqrt ρ) := by ring

/-- **`ConvSupport` holds**: off `‖y‖ ≤ R + r` the integrand vanishes identically. -/
theorem convSupport : ConvSupport := by
  intro κ Θ r R hκ hΘ x hx
  unfold convY
  have hz : ∀ z : Space, ((κ z : ℝ) : ℂ) • Θ (x.1, x.2 - z) = 0 := by
    intro z
    by_cases hzr : r < ‖z‖
    · simp [hκ z hzr]
    · rw [not_lt] at hzr
      have h1 : ‖x.2‖ ≤ ‖x.2 - z‖ + ‖z‖ := by
        have := norm_add_le (x.2 - z) z
        rwa [sub_add_cancel] at this
      have : R < ‖x.2 - z‖ := by linarith
      simp [hΘ x.1 (x.2 - z) this]
  simp [hz]

/-- **`ConvSupBound` holds**: `‖∫ κ(z) Θ(τ, y - z) dz‖ ≤ K ∫ ‖Θ(τ, y - z)‖ dz` and translation
invariance. -/
theorem convSupBound : ConvSupBound := by
  intro P κ Θ K hΘ hK x
  have hcont : Continuous fun z : Space => Θ (x.1, x.2 - z) :=
    hΘ.continuous.comp (continuous_const.prodMk (continuous_const.sub continuous_id))
  have hcs : HasCompactSupport fun z : Space => Θ (x.1, x.2 - z) := by
    obtain ⟨R, hR⟩ := hΘ.bounded_support
    refine HasCompactSupport.intro (isCompact_closedBall x.2 R) fun z hz => hR x.1 (x.2 - z) ?_
    have h : R < dist z x.2 := not_le.mp hz
    rwa [dist_eq_norm, norm_sub_rev] at h
  have hint : Integrable fun z : Space => K * ‖Θ (x.1, x.2 - z)‖ :=
    (hcont.norm.integrable_of_hasCompactSupport hcs.norm).const_mul K
  calc ‖convY κ Θ x‖ = ‖∫ z, ((κ z : ℝ) : ℂ) • Θ (x.1, x.2 - z)‖ := rfl
    _ ≤ ∫ z, ‖((κ z : ℝ) : ℂ) • Θ (x.1, x.2 - z)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z, K * ‖Θ (x.1, x.2 - z)‖ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun z => norm_nonneg _) hint
          (Eventually.of_forall fun z => ?_)
        dsimp only
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hK z) (norm_nonneg _)
    _ = K * ∫ z, ‖Θ (x.1, z)‖ := by
        rw [integral_const_mul]
        congr 1
        exact integral_sub_left_eq_self (fun z => ‖Θ (x.1, z)‖) volume x.2

/-- **`PhaseTestSliceL1` holds**: `‖Θ‖ ≤ M` (`phaseTestDerivBounded_proof`, `k = 0`) on the
ball `‖y‖ ≤ R`, zero outside. -/
theorem phaseTestSliceL1 : PhaseTestSliceL1 := by
  intro P hP Θ hΘ
  obtain ⟨M, hM0, hM⟩ := UnforcedLeray.Short.PartIIa.phaseTestDerivBounded_proof P hP Θ hΘ 0
  obtain ⟨R, hR⟩ := hΘ.bounded_support
  set R' : ℝ := max R 0 with hR'
  set B : Set Space := Metric.closedBall (0 : Space) R' with hB
  refine ⟨M * (volume B).toReal, by positivity, fun τ => ?_⟩
  have hb : ∀ z, ‖Θ (τ, z)‖ ≤ B.indicator (fun _ => M) z := by
    intro z
    by_cases hz : z ∈ B
    · rw [Set.indicator_of_mem hz]
      have := hM (τ, z)
      rwa [norm_iteratedFDeriv_zero] at this
    · rw [Set.indicator_of_notMem hz]
      have hz' : R' < ‖z‖ := by simpa [hB, mem_closedBall_zero_iff] using hz
      rw [hR τ z (lt_of_le_of_lt (le_max_left _ _) hz'), norm_zero]
  have hiB : Integrable (B.indicator fun _ : Space => M) :=
    (integrable_indicator_iff measurableSet_closedBall).2
      (integrableOn_const measure_closedBall_lt_top.ne)
  calc ∫ z, ‖Θ (τ, z)‖ ≤ ∫ z, B.indicator (fun _ => M) z :=
        integral_mono_of_nonneg (Eventually.of_forall fun z => norm_nonneg _) hiB
          (Eventually.of_forall hb)
    _ = M * (volume B).toReal := by
        rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, measureReal_def,
          mul_comm]

/-- **`DilKIntegral` holds**: `∫ (s⁻¹)³ g(s⁻¹ z) dz = ∫ g` (`integral_comp_inv_smul_of_nonneg`,
`finrank ℝ³ = 3`). -/
theorem dilKIntegral : DilKIntegral := by
  intro κ s hs
  have hfr : Module.finrank ℝ Space = 3 := by
    simp [finrank_euclideanSpace]
  have key : ∀ g : Space → ℝ, ∫ z, (s⁻¹) ^ 3 * g (s⁻¹ • z) = ∫ z, g z := by
    intro g
    rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume g hs.le, hfr,
      smul_eq_mul, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hs.ne', one_pow, one_mul]
  refine ⟨key κ, ?_⟩
  have h : (fun z => |dilK κ s z|) = fun z => (s⁻¹) ^ 3 * |κ (s⁻¹ • z)| := by
    funext z
    simp only [dilK, abs_mul, abs_pow, abs_inv, abs_of_pos hs]
  rw [h]
  exact key (fun z => |κ z|)

/-- **`PhaseTestLipY` holds**: `‖DG‖ ≤ M` (`phaseTestDerivBounded_proof`, `k = 1`) and the mean
value inequality on the slice `y ↦ G(τ, y)`. -/
theorem phaseTestLipY : PhaseTestLipY := by
  intro P hP G hG
  obtain ⟨M, hM0, hM⟩ := UnforcedLeray.Short.PartIIa.phaseTestDerivBounded_proof P hP G hG 1
  refine ⟨M, hM0, fun τ y y' => ?_⟩
  have hd : Differentiable ℝ G := hG.smooth.differentiable (by simp)
  have hg : ∀ z : Space, HasFDerivAt (fun z : Space => G (τ, z))
      ((fderiv ℝ G (τ, z)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) z :=
    fun z => (hd (τ, z)).hasFDerivAt.comp z (hasFDerivAt_prodMk_right τ z)
  have hb : ∀ z : Space, ‖(fderiv ℝ G (τ, z)).comp (ContinuousLinearMap.inr ℝ ℝ Space)‖ ≤ M := by
    intro z
    have h1 : ‖fderiv ℝ G (τ, z)‖ ≤ M := by
      have := hM (τ, z)
      rwa [norm_iteratedFDeriv_one] at this
    calc _ ≤ ‖fderiv ℝ G (τ, z)‖ * ‖ContinuousLinearMap.inr ℝ ℝ Space‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ M * 1 := mul_le_mul h1 (ContinuousLinearMap.norm_inr_le_one ℝ ℝ Space)
          (norm_nonneg _) hM0
      _ = M := mul_one M
  exact convex_univ.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (hg z).hasFDerivWithinAt) (fun z _ => hb z) (mem_univ y') (mem_univ y)

/-! ### The convolution leaves -/

/-- `convY` is the Mathlib convolution in `y`, phase by phase. -/
theorem convY_eq_conv (κ : Space → ℝ) (Θ : ℝ × Space → CVec3) (q : ℝ × Space) :
    convY κ Θ q = (convolution κ (fun z : Space => Θ (q.1, z))
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] CVec3 →L[ℝ] CVec3) volume) q.2 := by
  simp only [convY, convolution, ContinuousLinearMap.lsmul_apply, Complex.coe_smul]

/-- The joint derivative of `convY κ Θ` (the derivative falls on `Θ`). -/
theorem convY_hasFDerivAt {P : ℝ} {κ : Space → ℝ} {Θ : ℝ × Space → CVec3} (hκ : KerOK κ)
    (hΘ : IsPhaseTest P Θ) (q₀ : ℝ × Space) :
    HasFDerivAt (convY κ Θ)
      ((convolution κ (fun x : Space => fderiv ℝ Θ (q₀.1, x))
        ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] CVec3 →L[ℝ] CVec3).precompR (ℝ × Space))
        volume) q₀.2) q₀ := by
  obtain ⟨R, hR⟩ := hΘ.bounded_support
  have hf : LocallyIntegrable κ volume := hκ.1.continuous.locallyIntegrable
  have hgs : ∀ p : ℝ, ∀ x : Space, p ∈ (univ : Set ℝ) → x ∉ Metric.closedBall (0 : Space) R →
      (fun (τ : ℝ) (z : Space) => Θ (τ, z)) p x = 0 := by
    intro p x _ hx
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
    exact hR p x hx
  have hg : ContDiffOn ℝ 1 (Function.uncurry fun (τ : ℝ) (z : Space) => Θ (τ, z))
      (univ ×ˢ univ) := (hΘ.smooth.of_le (by simp)).contDiffOn
  have key := MeasureTheory.hasFDerivAt_convolution_right_with_param (μ := volume) (f := κ)
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] CVec3 →L[ℝ] CVec3)
    isOpen_univ (isCompact_closedBall (0 : Space) R) hgs hf hg q₀ (mem_univ _)
  have heq : convY κ Θ = fun q : ℝ × Space =>
      (convolution κ ((fun (τ : ℝ) (z : Space) => Θ (τ, z)) q.1)
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] CVec3 →L[ℝ] CVec3) volume) q.2 :=
    funext fun q => convY_eq_conv κ Θ q
  rw [heq]
  exact key

/-- **`ConvFDeriv` holds.** -/
theorem convFDeriv : ConvFDeriv := by
  intro P κ Θ hκ hΘ v
  funext q₀
  rw [(convY_hasFDerivAt hκ hΘ q₀).fderiv]
  have hc : Continuous fun x : Space => fderiv ℝ Θ (q₀.1, x) :=
    (hΘ.smooth.continuous_fderiv (by simp)).comp (continuous_const.prodMk continuous_id)
  have hint := hκ.2.convolutionExists_left
    ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] CVec3 →L[ℝ] CVec3).precompR (ℝ × Space))
    (μ := volume) hκ.1.continuous hc.locallyIntegrable q₀.2
  rw [convolution_def, ContinuousLinearMap.integral_apply hint]
  simp [convY, Complex.coe_smul]

/-- Integrability of the `convY` integrand. -/
theorem convY_integrable {κ : Space → ℝ} (hκ : KerOK κ) {G : ℝ × Space → CVec3}
    (hG : Continuous G) (p : ℝ × Space) :
    Integrable fun z : Space => ((κ z : ℝ) : ℂ) • G (p.1, p.2 - z) := by
  have hcC : Continuous fun z => ((κ z : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp hκ.1.continuous
  have hcsC : HasCompactSupport fun z => ((κ z : ℝ) : ℂ) := hκ.2.comp_left Complex.ofReal_zero
  have hGc : Continuous fun z : Space => G (p.1, p.2 - z) :=
    hG.comp (continuous_const.prodMk (continuous_const.sub continuous_id))
  exact (hcC.smul hGc).integrable_of_hasCompactSupport hcsC.smul_right

/-- **`ConvLapT` holds.** -/
theorem convLapT : ConvLapT := by
  intro P κ Θ hκ hΘ
  have hdy : ∀ G : ℝ × Space → CVec3, IsPhaseTest P G → ∀ j : Fin 3,
      dy j (convY κ G) = convY κ (dy j G) :=
    fun G hG j => convFDeriv P κ G hκ hG (0, coordinateVector j)
  funext p
  have e1 : lapT (convY κ Θ) p = ∑ j : Fin 3, convY κ (dy j (dy j Θ)) p := by
    simp only [lapT]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hdy Θ hΘ j, hdy _ (hΘ.dy j) j]
  rw [e1]
  simp only [convY, lapT]
  rw [← integral_finsetSum _ (fun j _ => convY_integrable hκ ((hΘ.dy j).dy j).continuous p)]
  congr 1
  funext z
  rw [Finset.smul_sum]

/-- **`ConvDyKer` holds**: the `y`-slice derivative computed both ways (`convY_hasFDerivAt` and
`HasCompactSupport.hasFDerivAt_convolution_left`) agree. -/
theorem convDyKer : ConvDyKer := by
  intro P κ Θ hκ hΘ j
  funext q₀
  have hD := convY_hasFDerivAt hκ hΘ q₀
  have hD' : HasFDerivAt (convY κ Θ)
      ((convolution κ (fun x : Space => fderiv ℝ Θ (q₀.1, x))
        ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] CVec3 →L[ℝ] CVec3).precompR (ℝ × Space))
        volume) q₀.2) (q₀.1, q₀.2) := hD
  have h1 := hD'.comp q₀.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) q₀.1 q₀.2)
  have h2 : HasFDerivAt (fun y : Space => convY κ Θ (q₀.1, y))
      ((convolution (fderiv ℝ κ) (fun z : Space => Θ (q₀.1, z))
        ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] CVec3 →L[ℝ] CVec3).precompL Space)
        volume) q₀.2) q₀.2 := by
    have := hκ.2.hasFDerivAt_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] CVec3 →L[ℝ] CVec3) (μ := volume)
      (hκ.1.of_le (by simp)) (hΘ.continuous_slice q₀.1).locallyIntegrable q₀.2
    have e : (fun y : Space => convY κ Θ (q₀.1, y)) =
        convolution κ (fun z : Space => Θ (q₀.1, z))
          (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] CVec3 →L[ℝ] CVec3) volume :=
      funext fun y => convY_eq_conv κ Θ (q₀.1, y)
    rw [e]
    exact this
  have huniq := h1.unique h2
  show fderiv ℝ (convY κ Θ) q₀ (0, coordinateVector j) = convY (sd j κ) Θ q₀
  rw [hD.fderiv]
  have hcomp := congrArg (fun T : Space →L[ℝ] CVec3 => T (coordinateVector j)) huniq
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.inr_apply] at hcomp
  rw [hcomp]
  have hint := (hκ.2.fderiv (𝕜 := ℝ)).convolutionExists_left
    ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] CVec3 →L[ℝ] CVec3).precompL Space)
    (μ := volume) (hκ.1.continuous_fderiv (by simp))
    (hΘ.continuous_slice q₀.1).locallyIntegrable q₀.2
  rw [convolution_def, ContinuousLinearMap.integral_apply hint]
  simp [convY, sd, Complex.coe_smul]

/-- **`DilKBounds` holds**: chain rule for `z ↦ s⁻³ b(s⁻¹ z)`, bounds of `b`, `Db` by compact
support. -/
theorem dilKBounds : DilKBounds := by
  intro b hb
  have hbc : Continuous b := hb.1.continuous
  obtain ⟨K₀, hK₀⟩ := hbc.bounded_above_of_compact_support hb.2
  have hdc : Continuous (fderiv ℝ b) := hb.1.continuous_fderiv (by simp)
  obtain ⟨K₁, hK₁⟩ := hdc.bounded_above_of_compact_support (hb.2.fderiv (𝕜 := ℝ))
  obtain ⟨r₀, hr₀⟩ := hb.2.isCompact.isBounded.subset_closedBall (0 : Space)
  have hbd : Differentiable ℝ b := hb.1.differentiable (by simp)
  set K : ℝ := max (max K₀ K₁) 0 with hKdef
  set r : ℝ := max r₀ 0 + 1 with hrdef
  have hK0 : 0 ≤ K := le_max_right _ _
  have hK₀K : K₀ ≤ K := le_trans (le_max_left _ _) (le_max_left _ _)
  have hK₁K : K₁ ≤ K := le_trans (le_max_right _ _) (le_max_left _ _)
  have hr : 0 < r := by positivity
  refine ⟨K, r, hK0, hr, fun s hs z => ?_⟩
  have hsi : 0 < s⁻¹ := inv_pos.mpr hs
  have hfd : ∀ w : Space, HasFDerivAt (dilK b s)
      ((s⁻¹) ^ 3 • (fderiv ℝ b (s⁻¹ • w)).comp (s⁻¹ • ContinuousLinearMap.id ℝ Space)) w := by
    intro w
    have h_in : HasFDerivAt (fun z : Space => s⁻¹ • z) (s⁻¹ • ContinuousLinearMap.id ℝ Space) w :=
      (hasFDerivAt_id w).const_smul s⁻¹
    exact ((hbd _).hasFDerivAt.comp w h_in).const_mul ((s⁻¹) ^ 3)
  have hsd : ∀ (j : Fin 3) (w : Space),
      sd j (dilK b s) w = (s⁻¹) ^ 4 * fderiv ℝ b (s⁻¹ • w) (coordinateVector j) := by
    intro j w
    simp only [sd, (hfd w).fderiv, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_comp',
      Function.comp_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
    ring
  refine ⟨?_, fun j => ?_, fun hz => ?_⟩
  · have h1 : |b (s⁻¹ • z)| ≤ K := by
      have := hK₀ (s⁻¹ • z)
      rw [Real.norm_eq_abs] at this
      linarith
    calc |dilK b s z| = (s⁻¹) ^ 3 * |b (s⁻¹ • z)| := by
          simp only [dilK, abs_mul, abs_pow, abs_of_pos hsi]
      _ ≤ (s⁻¹) ^ 3 * K := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = K * (s⁻¹) ^ 3 := mul_comm _ _
  · rw [hsd j z, abs_mul, abs_of_pos (by positivity)]
    have h1 : |fderiv ℝ b (s⁻¹ • z) (coordinateVector j)| ≤ K := by
      rw [← Real.norm_eq_abs]
      calc ‖fderiv ℝ b (s⁻¹ • z) (coordinateVector j)‖
          ≤ ‖fderiv ℝ b (s⁻¹ • z)‖ * ‖coordinateVector j‖ := ContinuousLinearMap.le_opNorm _ _
        _ = ‖fderiv ℝ b (s⁻¹ • z)‖ := by
            simp [coordinateVector]
        _ ≤ K := (hK₁ _).trans hK₁K
    calc (s⁻¹) ^ 4 * |fderiv ℝ b (s⁻¹ • z) (coordinateVector j)| ≤ (s⁻¹) ^ 4 * K :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = K * (s⁻¹) ^ 4 := mul_comm _ _
  · have hw : s⁻¹ • z ∉ tsupport b := by
      intro hmem
      have h1 := hr₀ hmem
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos hsi] at h1
      have h2 : r < s⁻¹ * ‖z‖ := by
        rw [lt_inv_mul_iff₀ hs]
        linarith
      have h3 : r₀ < r := by
        rw [hrdef]
        linarith [le_max_left r₀ 0]
      linarith
    have hb0 : b (s⁻¹ • z) = 0 := image_eq_zero_of_notMem_tsupport hw
    have hdb0 : fderiv ℝ b (s⁻¹ • z) = 0 := by
      by_contra hne
      exact hw (support_fderiv_subset ℝ (Function.mem_support.mpr hne))
    refine ⟨by simp [dilK, hb0], fun j => ?_⟩
    rw [hsd j z, hdb0]
    simp

/-- Additivity of the defect on phase tests. -/
theorem defect_sub {P : ℝ} (hP : 0 < P) (ν μ : ℝ) {ψ w : ℝ × Space → CVec3}
    (hψ : UnforcedLeray.Short.IIb.IsInYr P 2 (fun x => (‖x.2‖⁻¹ : ℝ) • ψ x))
    (hw : UnforcedLeray.Short.IIb.IsInYr P 2 (fun x => (‖x.2‖⁻¹ : ℝ) • w x))
    {A B : ℝ × Space → CVec3} (hA : IsPhaseTest P A) (hB : IsPhaseTest P B) :
    IntertwineDefect P ν μ ψ w (fun x => A x - B x) =
      IntertwineDefect P ν μ ψ w A - IntertwineDefect P ν μ ψ w B := by
  unfold IntertwineDefect
  rw [wOpT_sub ν μ hA.smooth hB.smooth,
    hardyPairSub hP hψ (isPhaseTest_wOpT hA ν μ) (isPhaseTest_wOpT hB ν μ),
    hardyPairSub hP hw hA hB]
  ring

/-- (I) The defect vanishes on Laplacians of phase tests: `ΔV = ∇ div V - curl curl V`. -/
theorem defect_lap (g7 : CurlIsSolTest) (g8 : DivIsPhaseTest) (g9 : CurlCurlId)
    {P : ℝ} (hP : 0 < P) (ν μ : ℝ) {ψ w : ℝ × Space → CVec3}
    (hψ : UnforcedLeray.Short.IIb.IsInYr P 2 (fun x => (‖x.2‖⁻¹ : ℝ) • ψ x))
    (hw : UnforcedLeray.Short.IIb.IsInYr P 2 (fun x => (‖x.2‖⁻¹ : ℝ) • w x))
    (hcurl : ∀ Θ, IsPhaseTest P Θ → IntertwineDefect P ν μ ψ w (curlT Θ) = 0)
    (hgrad : ∀ φ : ℝ × Space → ℂ, IsPhaseTest P φ → IntertwineDefect P ν μ ψ w (gradT φ) = 0)
    {V : ℝ × Space → CVec3} (hV : IsPhaseTest P V) :
    IntertwineDefect P ν μ ψ w (lapT V) = 0 := by
  have hC : IsPhaseTest P (curlT V) := (g7 P V hV).1
  have hCC : IsPhaseTest P (curlT (curlT V)) := (g7 P _ hC).1
  have hD : IsPhaseTest P (divT V) := g8 P V hV
  have hG : IsPhaseTest P (gradT (divT V)) := hD.gradT
  have hid : lapT V = fun x => gradT (divT V) x - curlT (curlT V) x := by
    have := g9 V hV.smooth
    funext x
    rw [this]
    simp
  rw [hid, defect_sub hP ν μ hψ hw hG hCC, hgrad _ hD, hcurl _ hC, sub_zero]

/-! ## The mollifier bounds from the kernel facts -/

theorem coord_norm_le (y : Space) (j : Fin 3) : ‖y j‖ ≤ ‖y‖ := PiLp.norm_apply_le y j

/-- `‖∑ⱼ yⱼ vⱼ‖ ≤ ‖y‖ ∑ⱼ Bⱼ` when `‖vⱼ‖ ≤ Bⱼ`. -/
theorem radial_sum_le (y : Space) (v : Fin 3 → CVec3) (B : Fin 3 → ℝ)
    (hv : ∀ j, ‖v j‖ ≤ B j) : ‖∑ j : Fin 3, y j • v j‖ ≤ ‖y‖ * ∑ j : Fin 3, B j := by
  calc ‖∑ j : Fin 3, y j • v j‖ ≤ ∑ j : Fin 3, ‖y j • v j‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin 3, ‖y‖ * B j := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_smul]
        exact mul_le_mul (coord_norm_le y j) (hv j) (norm_nonneg _) (norm_nonneg _)
    _ = ‖y‖ * ∑ j : Fin 3, B j := (Finset.mul_sum _ _ _).symm

/-- The four-term bound of `wOpT` by its pieces. -/
theorem norm_wOpT_le (ν μ : ℝ) (X : ℝ × Space → CVec3) (x : ℝ × Space) :
    ‖wOpT ν μ X x‖ ≤ ‖dτ X x‖ + 1 / 2 * ‖radialT X x‖ + |ν| * ‖lapT X x‖
      + ‖(μ : ℂ) - 1‖ * ‖X x‖ := by
  have h1 : ‖(1 / 2 : ℝ) • radialT X x‖ = 1 / 2 * ‖radialT X x‖ := by
    rw [norm_smul]; norm_num
  have h2 : ‖ν • lapT X x‖ = |ν| * ‖lapT X x‖ := by rw [norm_smul, Real.norm_eq_abs]
  have h3 : ‖((μ : ℂ) - 1) • X x‖ = ‖(μ : ℂ) - 1‖ * ‖X x‖ := norm_smul _ _
  rw [wOpT_eq]
  calc ‖dτ X x - (1 / 2 : ℝ) • radialT X x - ν • lapT X x + ((μ : ℂ) - 1) • X x‖
      ≤ ‖dτ X x - (1 / 2 : ℝ) • radialT X x - ν • lapT X x‖ + ‖((μ : ℂ) - 1) • X x‖ :=
        norm_add_le _ _
    _ ≤ (‖dτ X x - (1 / 2 : ℝ) • radialT X x‖ + ‖ν • lapT X x‖) + ‖((μ : ℂ) - 1) • X x‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ ((‖dτ X x‖ + ‖(1 / 2 : ℝ) • radialT X x‖) + ‖ν • lapT X x‖)
          + ‖((μ : ℂ) - 1) • X x‖ :=
        add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl
    _ = _ := by rw [h1, h2, h3]

/-- `MolLarge` from the kernel facts. -/
theorem molLarge_of (k1 : ConvFDeriv) (k2 : ConvLapT) (k3 : ConvDyKer) (k4 : ConvSupBound)
    (k5 : ConvSupport) (k6 : PhaseTestSliceL1) (k7 : DilKBounds) (g2 : DilKerOK) :
    MolLarge := by
  intro P ν μ hP b Θ hb hΘ
  obtain ⟨K, r, hK0, hr, hKb⟩ := k7 b hb
  obtain ⟨R₁, hR₁⟩ := hΘ.bounded_support
  set R : ℝ := max R₁ 0 with hRdef
  have hR0 : 0 ≤ R := le_max_right _ _
  have hRΘ : ∀ τ y, R < ‖y‖ → Θ (τ, y) = 0 :=
    fun τ y h => hR₁ τ y (lt_of_le_of_lt (le_max_left _ _) h)
  obtain ⟨M₀, hM₀0, hM₀⟩ := k6 P hP Θ hΘ
  obtain ⟨Mτ, hMτ0, hMτ⟩ := k6 P hP (dτ Θ) hΘ.dτ
  obtain ⟨MΔ, hMΔ0, hMΔ⟩ := k6 P hP (lapT Θ) hΘ.lapT
  set ρ₀ : ℝ := R + r with hρ₀def
  have hρ₀ : 0 < ρ₀ := add_pos_of_nonneg_of_pos hR0 hr
  set C : ℝ := K * (Mτ + 3 / 2 * ρ₀ * M₀ + |ν| * MΔ + (‖(μ : ℂ) - 1‖ + 1) * M₀) with hCdef
  have hC0 : 0 ≤ C := by positivity
  refine ⟨C, ρ₀, hC0, hρ₀, ?_⟩
  intro s hs
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs
  have hbs : KerOK (dilK b s) := (g2 b s hb hs0).1
  have hsupp : ∀ x : ℝ × Space, ρ₀ * s < ‖x.2‖ → convY (dilK b s) Θ x = 0 := by
    intro x hx
    refine k5 (dilK b s) Θ (r * s) R (fun z hz => ((hKb s hs0 z).2.2 hz).1) hRΘ x ?_
    have : R * 1 ≤ R * s := mul_le_mul_of_nonneg_left hs hR0
    nlinarith
  have hk3 : 0 < (s⁻¹) ^ 3 := by positivity
  have hX : ∀ x, ‖convY (dilK b s) Θ x‖ ≤ K * (s⁻¹) ^ 3 * M₀ := fun x =>
    (k4 P (dilK b s) Θ _ hΘ (fun z => (hKb s hs0 z).1) x).trans
      (mul_le_mul_of_nonneg_left (hM₀ x.1) (by positivity))
  have hτ : ∀ x, ‖dτ (convY (dilK b s) Θ) x‖ ≤ K * (s⁻¹) ^ 3 * Mτ := by
    intro x
    have e : dτ (convY (dilK b s) Θ) = convY (dilK b s) (dτ Θ) := k1 P _ Θ hbs hΘ (1, 0)
    rw [e]
    exact (k4 P (dilK b s) (dτ Θ) _ hΘ.dτ (fun z => (hKb s hs0 z).1) x).trans
      (mul_le_mul_of_nonneg_left (hMτ x.1) (by positivity))
  have hΔ : ∀ x, ‖lapT (convY (dilK b s) Θ) x‖ ≤ K * (s⁻¹) ^ 3 * MΔ := by
    intro x
    rw [k2 P _ Θ hbs hΘ]
    exact (k4 P (dilK b s) (lapT Θ) _ hΘ.lapT (fun z => (hKb s hs0 z).1) x).trans
      (mul_le_mul_of_nonneg_left (hMΔ x.1) (by positivity))
  have hdy : ∀ j x, ‖dy j (convY (dilK b s) Θ) x‖ ≤ K * (s⁻¹) ^ 4 * M₀ := by
    intro j x
    rw [k3 P _ Θ hbs hΘ j]
    exact (k4 P (sd j (dilK b s)) Θ _ hΘ (fun z => (hKb s hs0 z).2.1 j) x).trans
      (mul_le_mul_of_nonneg_left (hM₀ x.1) (by positivity))
  have hCM : K * M₀ ≤ C := by
    rw [hCdef]
    refine mul_le_mul_of_nonneg_left ?_ hK0
    have h1 : 0 ≤ Mτ + 3 / 2 * ρ₀ * M₀ + |ν| * MΔ + ‖(μ : ℂ) - 1‖ * M₀ := by positivity
    nlinarith
  refine ⟨fun x => ?_, fun x => ?_, fun x hx => ⟨hsupp x hx, wOpT_support ν μ (ρ₀ * s) hsupp x hx⟩⟩
  · calc ‖convY (dilK b s) Θ x‖ ≤ K * (s⁻¹) ^ 3 * M₀ := hX x
      _ = (K * M₀) * (s⁻¹) ^ 3 := by ring
      _ ≤ C * (s⁻¹) ^ 3 := mul_le_mul_of_nonneg_right hCM hk3.le
  · by_cases hx : ρ₀ * s < ‖x.2‖
    · rw [wOpT_support ν μ (ρ₀ * s) hsupp x hx, norm_zero]
      positivity
    · rw [not_lt] at hx
      have hrad : ‖radialT (convY (dilK b s) Θ) x‖ ≤ ρ₀ * s * (3 * (K * (s⁻¹) ^ 4 * M₀)) := by
        refine (radial_sum_le x.2 (fun j => dy j (convY (dilK b s) Θ) x)
          (fun _ => K * (s⁻¹) ^ 4 * M₀) fun j => hdy j x).trans ?_
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        refine mul_le_mul_of_nonneg_right hx ?_
        positivity
      have hs4 : s * (s⁻¹) ^ 4 = (s⁻¹) ^ 3 := by
        field_simp
      refine (norm_wOpT_le ν μ _ x).trans ?_
      calc _ ≤ K * (s⁻¹) ^ 3 * Mτ + 1 / 2 * (ρ₀ * s * (3 * (K * (s⁻¹) ^ 4 * M₀)))
            + |ν| * (K * (s⁻¹) ^ 3 * MΔ) + ‖(μ : ℂ) - 1‖ * (K * (s⁻¹) ^ 3 * M₀) :=
            add_le_add (add_le_add (add_le_add (hτ x)
              (mul_le_mul_of_nonneg_left hrad (by norm_num)))
              (mul_le_mul_of_nonneg_left (hΔ x) (abs_nonneg ν)))
              (mul_le_mul_of_nonneg_left (hX x) (norm_nonneg _))
        _ = K * (Mτ + 3 / 2 * ρ₀ * M₀ + |ν| * MΔ + ‖(μ : ℂ) - 1‖ * M₀) * (s⁻¹) ^ 3 := by
            rw [show ρ₀ * s * (3 * (K * (s⁻¹) ^ 4 * M₀)) = 3 * ρ₀ * K * M₀ * (s * (s⁻¹) ^ 4)
              by ring, hs4]
            ring
        _ ≤ C * (s⁻¹) ^ 3 := by
            refine mul_le_mul_of_nonneg_right ?_ hk3.le
            rw [hCdef]
            refine mul_le_mul_of_nonneg_left ?_ hK0
            nlinarith

/-- `MolSmall` from the kernel facts. -/
theorem molSmall_of (k1 : ConvFDeriv) (k2 : ConvLapT) (k5 : ConvSupport) (k7 : DilKBounds)
    (k8 : ConvApprox) (g2 : DilKerOK) (g4 : ConvTest) : MolSmall := by
  intro P ν μ hP b Θ hb hint hΘ
  obtain ⟨K, r, hK0, hr, hKb⟩ := k7 b hb
  obtain ⟨R₁, hR₁⟩ := hΘ.bounded_support
  set R : ℝ := max R₁ 0 with hRdef
  have hR0 : 0 ≤ R := le_max_right _ _
  have hRΘ : ∀ τ y, R < ‖y‖ → Θ (τ, y) = 0 :=
    fun τ y h => hR₁ τ y (lt_of_le_of_lt (le_max_left _ _) h)
  obtain ⟨C₀, hC₀0, hC₀⟩ := k8 P hP b Θ hb hint hΘ
  obtain ⟨Cτ, hCτ0, hCτ⟩ := k8 P hP b (dτ Θ) hb hint hΘ.dτ
  obtain ⟨CΔ, hCΔ0, hCΔ⟩ := k8 P hP b (lapT Θ) hb hint hΘ.lapT
  have hCj : ∀ j : Fin 3, ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 < s → ∀ x : ℝ × Space,
      ‖convY (dilK b s) (dy j Θ) x - dy j Θ x‖ ≤ C * s :=
    fun j => k8 P hP b (dy j Θ) hb hint (hΘ.dy j)
  choose Cj hCj0 hCj using hCj
  set Cy : ℝ := ∑ j : Fin 3, Cj j with hCy
  have hCy0 : 0 ≤ Cy := Finset.sum_nonneg fun j _ => hCj0 j
  set ρ₀ : ℝ := R + r with hρ₀def
  have hρ₀ : 0 < ρ₀ := add_pos_of_nonneg_of_pos hR0 hr
  set C : ℝ := Cτ + 1 / 2 * ρ₀ * Cy + |ν| * CΔ + (‖(μ : ℂ) - 1‖ + 1) * C₀ with hCdef
  have hC0 : 0 ≤ C := by positivity
  refine ⟨C, ρ₀, hC0, hρ₀, ?_⟩
  intro s hs0 hs1
  have hbs : KerOK (dilK b s) := (g2 b s hb hs0).1
  have hX : IsPhaseTest P (convY (dilK b s) Θ) := g4 P _ Θ hbs hΘ
  have hsuppX : ∀ x : ℝ × Space, ρ₀ < ‖x.2‖ → convY (dilK b s) Θ x = 0 := by
    intro x hx
    refine k5 (dilK b s) Θ (r * s) R (fun z hz => ((hKb s hs0 z).2.2 hz).1) hRΘ x ?_
    have : r * s ≤ r * 1 := mul_le_mul_of_nonneg_left hs1 hr.le
    nlinarith
  have hsuppΘ : ∀ x : ℝ × Space, ρ₀ < ‖x.2‖ → Θ x = 0 :=
    fun x hx => hRΘ x.1 x.2 (by linarith)
  have hsuppD : ∀ x : ℝ × Space, ρ₀ < ‖x.2‖ → convY (dilK b s) Θ x - Θ x = 0 :=
    fun x hx => by rw [hsuppX x hx, hsuppΘ x hx, sub_zero]
  have hW : (fun x => wOpT ν μ (convY (dilK b s) Θ) x - wOpT ν μ Θ x) =
      wOpT ν μ (fun x => convY (dilK b s) Θ x - Θ x) :=
    (wOpT_sub ν μ hX.smooth hΘ.smooth).symm
  have hC₀C : C₀ ≤ C := by
    rw [hCdef]
    have h1 : 0 ≤ Cτ + 1 / 2 * ρ₀ * Cy + |ν| * CΔ + ‖(μ : ℂ) - 1‖ * C₀ := by positivity
    nlinarith
  refine ⟨fun x => ?_, fun x => ?_, fun x hx => ⟨hsuppD x hx, ?_⟩⟩
  · exact (hC₀ s hs0 x).trans (mul_le_mul_of_nonneg_right hC₀C hs0.le)
  · rw [show wOpT ν μ (convY (dilK b s) Θ) x - wOpT ν μ Θ x =
        wOpT ν μ (fun x => convY (dilK b s) Θ x - Θ x) x from congrFun hW x]
    by_cases hx : ρ₀ < ‖x.2‖
    · rw [wOpT_support ν μ ρ₀ hsuppD x hx, norm_zero]
      positivity
    · rw [not_lt] at hx
      have eτ : dτ (convY (dilK b s) Θ) = convY (dilK b s) (dτ Θ) := k1 P _ Θ hbs hΘ (1, 0)
      have eΔ : lapT (convY (dilK b s) Θ) = convY (dilK b s) (lapT Θ) := k2 P _ Θ hbs hΘ
      have edy : ∀ j, dy j (convY (dilK b s) Θ) = convY (dilK b s) (dy j Θ) :=
        fun j => k1 P _ Θ hbs hΘ (0, coordinateVector j)
      have hdX := differentiable_of_smooth hX.smooth
      have hdΘ := differentiable_of_smooth hΘ.smooth
      have hradb : ‖radialT (fun x => convY (dilK b s) Θ x - Θ x) x‖ ≤ ρ₀ * (Cy * s) := by
        have e : radialT (fun x => convY (dilK b s) Θ x - Θ x) x = ∑ j : Fin 3,
            x.2 j • (convY (dilK b s) (dy j Θ) x - dy j Θ x) := by
          rw [radialT_sub hdX hdΘ]
          simp only [radialT, edy, smul_sub, Finset.sum_sub_distrib]
        rw [e]
        refine (radial_sum_le x.2 _ (fun j => Cj j * s) fun j => hCj j s hs0 x).trans ?_
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right hx (by positivity)
      have hτb : ‖dτ (fun x => convY (dilK b s) Θ x - Θ x) x‖ ≤ Cτ * s := by
        rw [dτ_sub hdX hdΘ, eτ]
        exact hCτ s hs0 x
      have hΔb : ‖lapT (fun x => convY (dilK b s) Θ x - Θ x) x‖ ≤ CΔ * s := by
        rw [lapT_sub hX.smooth hΘ.smooth, eΔ]
        exact hCΔ s hs0 x
      refine (norm_wOpT_le ν μ _ x).trans ?_
      calc _ ≤ Cτ * s + 1 / 2 * (ρ₀ * (Cy * s)) + |ν| * (CΔ * s) + ‖(μ : ℂ) - 1‖ * (C₀ * s) :=
            add_le_add (add_le_add (add_le_add hτb
              (mul_le_mul_of_nonneg_left hradb (by norm_num)))
              (mul_le_mul_of_nonneg_left hΔb (abs_nonneg ν)))
              (mul_le_mul_of_nonneg_left (hC₀ s hs0 x) (norm_nonneg _))
        _ = (Cτ + 1 / 2 * ρ₀ * Cy + |ν| * CΔ + ‖(μ : ℂ) - 1‖ * C₀) * s := by ring
        _ ≤ C * s := by
            refine mul_le_mul_of_nonneg_right ?_ hs0.le
            rw [hCdef]
            nlinarith
  · rw [show wOpT ν μ (convY (dilK b s) Θ) x - wOpT ν μ Θ x =
        wOpT ν μ (fun x => convY (dilK b s) Θ x - Θ x) x from congrFun hW x]
    exact wOpT_support ν μ ρ₀ hsuppD x hx

/-- `ConvApprox` from the scaling facts and the Lipschitz bound. -/
theorem convApprox_of (k7 : DilKBounds) (k9 : DilKIntegral) (k10 : PhaseTestLipY) :
    ConvApprox := by
  intro P hP b G hb hint hG
  obtain ⟨K, r, hK0, hr, hKb⟩ := k7 b hb
  obtain ⟨L, hL0, hL⟩ := k10 P hP G hG
  set I : ℝ := ∫ z, |b z| with hI
  have hI0 : 0 ≤ I := integral_nonneg fun z => abs_nonneg _
  refine ⟨L * r * I, by positivity, fun s hs x => ?_⟩
  have hcont : Continuous (dilK b s) :=
    continuous_const.mul (hb.1.continuous.comp (continuous_const_smul _))
  have hcs : HasCompactSupport (dilK b s) :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Space) (r * s)) fun z hz =>
      ((hKb s hs z).2.2 (by simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hz)).1
  have hcC : Continuous fun z => ((dilK b s z : ℝ) : ℂ) := Complex.continuous_ofReal.comp hcont
  have hcsC : HasCompactSupport fun z => ((dilK b s z : ℝ) : ℂ) :=
    hcs.comp_left Complex.ofReal_zero
  have hGc : Continuous fun z : Space => G (x.1, x.2 - z) :=
    hG.continuous.comp (continuous_const.prodMk (continuous_const.sub continuous_id))
  have i1 : Integrable fun z => ((dilK b s z : ℝ) : ℂ) • G (x.1, x.2 - z) :=
    (hcC.smul hGc).integrable_of_hasCompactSupport (hcsC.smul_right)
  have iC : Integrable fun z => ((dilK b s z : ℝ) : ℂ) :=
    hcC.integrable_of_hasCompactSupport hcsC
  have i2 : Integrable fun z => ((dilK b s z : ℝ) : ℂ) • G x := iC.smul_const _
  have hint_s : ∫ z, dilK b s z = 1 := (k9 b s hs).1.trans hint
  have habs_s : ∫ z, |dilK b s z| = I := (k9 b s hs).2
  have hGx : G x = ∫ z, ((dilK b s z : ℝ) : ℂ) • G x := by
    rw [integral_smul_const, integral_complex_ofReal, hint_s]
    simp
  have hdiff : convY (dilK b s) G x - G x =
      ∫ z, ((dilK b s z : ℝ) : ℂ) • (G (x.1, x.2 - z) - G x) := by
    conv_lhs => rw [hGx]
    rw [convY, ← integral_sub i1 i2]
    congr 1
    funext z
    rw [smul_sub]
  rw [hdiff]
  have iR : Integrable fun z => |dilK b s z| * (L * (r * s)) :=
    ((hcont.integrable_of_hasCompactSupport hcs).abs).mul_const _
  calc ‖∫ z, ((dilK b s z : ℝ) : ℂ) • (G (x.1, x.2 - z) - G x)‖
      ≤ ∫ z, ‖((dilK b s z : ℝ) : ℂ) • (G (x.1, x.2 - z) - G x)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ z, |dilK b s z| * (L * (r * s)) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun z => norm_nonneg _) iR
          (Eventually.of_forall fun z => ?_)
        dsimp only
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
        by_cases hz : r * s < ‖z‖
        · rw [((hKb s hs z).2.2 hz).1]
          simp
        · rw [not_lt] at hz
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          have h1 := hL x.1 (x.2 - z) x.2
          have h2 : ‖x.2 - z - x.2‖ = ‖z‖ := by
            rw [sub_sub_cancel_left, norm_neg]
          rw [h2] at h1
          calc ‖G (x.1, x.2 - z) - G x‖ = ‖G (x.1, x.2 - z) - G (x.1, x.2)‖ := rfl
            _ ≤ L * ‖z‖ := h1
            _ ≤ L * (r * s) := mul_le_mul_of_nonneg_left hz hL0
    _ = L * r * I * s := by
        rw [integral_mul_const, habs_s]
        ring

/-- (IV) Small scale: `F(Θ * b_{(s)}) → F(Θ)` as `s → 0+`. -/
theorem defectSmall_of (h1 : HardyPairBound) (h2 : MolSmall) (g2 : DilKerOK) (g4 : ConvTest)
    {P : ℝ} (hP : 0 < P) (ν μ : ℝ) {ψ w : ℝ × Space → CVec3}
    (hψ : UnforcedLeray.Short.IIb.IsInYr P 2 (fun x => (‖x.2‖⁻¹ : ℝ) • ψ x))
    (hw : UnforcedLeray.Short.IIb.IsInYr P 2 (fun x => (‖x.2‖⁻¹ : ℝ) • w x))
    {b : Space → ℝ} (hb : KerOK b) (hint : ∫ z, b z = 1)
    {Θ : ℝ × Space → CVec3} (hΘ : IsPhaseTest P Θ) :
    Tendsto (fun s : ℝ => IntertwineDefect P ν μ ψ w (convY (dilK b s) Θ)) (𝓝[>] 0)
      (𝓝 (IntertwineDefect P ν μ ψ w Θ)) := by
  obtain ⟨Cψ, hCψ0, hCψ⟩ := h1 P hP ψ hψ
  obtain ⟨Cw, hCw0, hCw⟩ := h1 P hP w hw
  obtain ⟨C, ρ₀, hC0, hρ₀, hS⟩ := h2 P ν μ hP b Θ hb hint hΘ
  set K : ℝ := (Cψ + Cw) * C * (ρ₀ ^ 2 * Real.sqrt ρ₀) with hK
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) (g := fun s => K * s) ?_ ?_
  · filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with s hs
    obtain ⟨hs0, hs1⟩ := hs
    have hbs : KerOK (dilK b s) := (g2 b s hb hs0).1
    have hX : IsPhaseTest P (convY (dilK b s) Θ) := g4 P _ Θ hbs hΘ
    have hWX := isPhaseTest_wOpT hX ν μ
    have hWΘ := isPhaseTest_wOpT hΘ ν μ
    obtain ⟨hb1, hb2, hb3⟩ := hS s hs0 hs1
    have e : IntertwineDefect P ν μ ψ w (convY (dilK b s) Θ) - IntertwineDefect P ν μ ψ w Θ =
        pairF P (fun x => wOpT ν μ (convY (dilK b s) Θ) x - wOpT ν μ Θ x) ψ
          - pairF P (fun x => convY (dilK b s) Θ x - Θ x) w := by
      unfold IntertwineDefect
      rw [hardyPairSub hP hψ hWX hWΘ, hardyPairSub hP hw hX hΘ]
      ring
    have b1 := hCψ (fun x => wOpT ν μ (convY (dilK b s) Θ) x - wOpT ν μ Θ x) (hWX.sub hWΘ)
      (C * s) ρ₀ (by positivity) hρ₀ hb2 (fun x hx => (hb3 x hx).2)
    have b2 := hCw (fun x => convY (dilK b s) Θ x - Θ x) (hX.sub hΘ)
      (C * s) ρ₀ (by positivity) hρ₀ hb1 (fun x hx => (hb3 x hx).1)
    rw [e]
    calc _ ≤ ‖pairF P (fun x => wOpT ν μ (convY (dilK b s) Θ) x - wOpT ν μ Θ x) ψ‖
          + ‖pairF P (fun x => convY (dilK b s) Θ x - Θ x) w‖ := norm_sub_le _ _
      _ ≤ Cψ * (C * s) * (ρ₀ ^ 2 * Real.sqrt ρ₀) + Cw * (C * s) * (ρ₀ ^ 2 * Real.sqrt ρ₀) :=
          add_le_add b1 b2
      _ = K * s := by rw [hK]; ring
  · have h0 : Tendsto (fun s : ℝ => K * s) (𝓝 0) (𝓝 0) := by
      have := (tendsto_id (x := 𝓝 (0 : ℝ))).const_mul K
      simpa using this
    exact tendsto_nhdsWithin_of_tendsto_nhds h0

/-- `(ρ₀ s)² √(ρ₀ s) s⁻³ = ρ₀² √ρ₀ / √s`. -/
theorem scale_identity {ρ₀ s : ℝ} (hρ₀ : 0 ≤ ρ₀) (hs : 0 < s) :
    (s⁻¹) ^ 3 * ((ρ₀ * s) ^ 2 * Real.sqrt (ρ₀ * s)) =
      (ρ₀ ^ 2 * Real.sqrt ρ₀) * (Real.sqrt s)⁻¹ := by
  have ht : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hss : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
  rw [Real.sqrt_mul hρ₀, ← hss]
  rw [Real.sqrt_sq ht.le]
  field_simp

/-- (III) Large scale: `F(Θ * b_{(s)}) → 0` as `s → ∞` (rate `s^{-1/2}`). -/
theorem defectLarge_of (h1 : HardyPairBound) (h3 : MolLarge) (g2 : DilKerOK) (g4 : ConvTest)
    {P : ℝ} (hP : 0 < P) (ν μ : ℝ) {ψ w : ℝ × Space → CVec3}
    (hψ : UnforcedLeray.Short.IIb.IsInYr P 2 (fun x => (‖x.2‖⁻¹ : ℝ) • ψ x))
    (hw : UnforcedLeray.Short.IIb.IsInYr P 2 (fun x => (‖x.2‖⁻¹ : ℝ) • w x))
    {b : Space → ℝ} (hb : KerOK b) {Θ : ℝ × Space → CVec3} (hΘ : IsPhaseTest P Θ) :
    Tendsto (fun s : ℝ => IntertwineDefect P ν μ ψ w (convY (dilK b s) Θ)) atTop (𝓝 0) := by
  obtain ⟨Cψ, hCψ0, hCψ⟩ := h1 P hP ψ hψ
  obtain ⟨Cw, hCw0, hCw⟩ := h1 P hP w hw
  obtain ⟨C, ρ₀, hC0, hρ₀, hL⟩ := h3 P ν μ hP b Θ hb hΘ
  set K : ℝ := (Cψ + Cw) * C * (ρ₀ ^ 2 * Real.sqrt ρ₀) with hK
  refine squeeze_zero_norm' (a := fun s : ℝ => K * (Real.sqrt s)⁻¹) ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    have hs0 : 0 < s := lt_of_lt_of_le one_pos hs
    have hbs : KerOK (dilK b s) := (g2 b s hb hs0).1
    have hX : IsPhaseTest P (convY (dilK b s) Θ) := g4 P _ Θ hbs hΘ
    have hWX := isPhaseTest_wOpT hX ν μ
    obtain ⟨hb1, hb2, hb3⟩ := hL s hs
    have hρs : 0 < ρ₀ * s := mul_pos hρ₀ hs0
    have b1 := hCψ (wOpT ν μ (convY (dilK b s) Θ)) hWX (C * (s⁻¹) ^ 3) (ρ₀ * s)
      (by positivity) hρs hb2 (fun x hx => (hb3 x hx).2)
    have b2 := hCw (convY (dilK b s) Θ) hX (C * (s⁻¹) ^ 3) (ρ₀ * s)
      (by positivity) hρs hb1 (fun x hx => (hb3 x hx).1)
    have hid := scale_identity hρ₀.le hs0
    unfold IntertwineDefect
    calc _ ≤ ‖pairF P (wOpT ν μ (convY (dilK b s) Θ)) ψ‖ + ‖pairF P (convY (dilK b s) Θ) w‖ :=
          norm_sub_le _ _
      _ ≤ Cψ * (C * (s⁻¹) ^ 3) * ((ρ₀ * s) ^ 2 * Real.sqrt (ρ₀ * s))
          + Cw * (C * (s⁻¹) ^ 3) * ((ρ₀ * s) ^ 2 * Real.sqrt (ρ₀ * s)) := add_le_add b1 b2
      _ = (Cψ + Cw) * C * ((s⁻¹) ^ 3 * ((ρ₀ * s) ^ 2 * Real.sqrt (ρ₀ * s))) := by ring
      _ = K * (Real.sqrt s)⁻¹ := by rw [hid, hK]; ring
  · have := (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).const_mul K
    simpa using this

/-- **Assembly** (source 1351-1362, 1470-1480): Weyl's lemma for the defect by the radial
approximate identity. -/
theorem liouville_of (g1 : RadialPotential) (g2 : DilKerOK) (g3 : DilLap) (g4 : ConvTest)
    (g5 : ConvLap) (g6 : ConvSub) (g7 : CurlIsSolTest) (g8 : DivIsPhaseTest) (g9 : CurlCurlId)
    (h1 : HardyPairBound) (h2 : MolSmall) (h3 : MolLarge) : IntertwineLiouville := by
  intro P ν μ hP hP1 hν hμ Φ g ψ w Dψ Dw hdom hψ hw hcurl hgrad Θ hΘ
  have hψh := hψ.hardy
  have hwh := hw.hardy
  obtain ⟨b, u, hb0, hb, hu, hint, hlapu⟩ := g1
  set G : ℝ → ℂ := fun s => IntertwineDefect P ν μ ψ w (convY (dilK b s) Θ) with hG
  have hstep : ∀ s : ℝ, 0 < s → G s = G (s * 2) := by
    intro s hs
    have hb2 : KerOK (dilK b 2) := (g2 b 2 hb two_pos).1
    have hc : KerOK (fun z => b z - dilK b 2 z) := kerOK_sub hb hb2
    have hus : KerOK (dilU u s) := (g2 u s hu hs).2
    have hcs : KerOK (dilK (fun z => b z - dilK b 2 z) s) := (g2 _ s hc hs).1
    have hl := g3 u (fun z => b z - dilK b 2 z) s hu hs hlapu
    have hsb : KerOK (dilK b s) := (g2 b s hb hs).1
    have hsb2 : KerOK (dilK b (s * 2)) := (g2 b (s * 2) hb (by positivity)).1
    have hL := g5 P (dilU u s) (dilK (fun z => b z - dilK b 2 z) s) Θ hus hcs hΘ hl
    have hT := g4 P (dilU u s) Θ hus hΘ
    have h0 := defect_lap g7 g8 g9 hP ν μ hψh hwh hcurl hgrad hT
    rw [hL] at h0
    have hd : dilK (fun z => b z - dilK b 2 z) s = fun z => dilK b s z - dilK b (s * 2) z := by
      rw [dilK_sub, dilK_dilK]
    rw [hd, g6 P _ _ Θ hsb hsb2 hΘ,
      defect_sub hP ν μ hψh hwh (g4 P _ Θ hsb hΘ) (g4 P _ Θ hsb2 hΘ)] at h0
    simp only [hG]
    exact sub_eq_zero.mp h0
  have hpow : ∀ s : ℝ, 0 < s → ∀ k : ℕ, G s = G (s * 2 ^ k) := by
    intro s hs k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [ih, pow_succ, ← mul_assoc]
      exact hstep _ (by positivity)
  have hlarge := defectLarge_of h1 h3 g2 g4 hP ν μ hψh hwh hb hΘ
  have hzero : ∀ s : ℝ, 0 < s → G s = 0 := by
    intro s hs
    have hlim : Tendsto (fun k : ℕ => G (s * 2 ^ k)) atTop (𝓝 0) :=
      hlarge.comp (Tendsto.const_mul_atTop hs (tendsto_pow_atTop_atTop_of_one_lt (by norm_num)))
    have hc : Tendsto (fun k : ℕ => G (s * 2 ^ k)) atTop (𝓝 (G s)) :=
      tendsto_const_nhds.congr (fun k => hpow s hs k)
    exact tendsto_nhds_unique hc hlim
  have hsm := defectSmall_of h1 h2 g2 g4 hP ν μ hψh hwh hb hint hΘ
  have h0 : Tendsto G (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun s hs => (hzero s hs).symm)
  exact tendsto_nhds_unique hsm h0

/-- **Assembly** (source 1351-1362, 1470-1480): `IntertwineLiouville` from the nine kernel Props
of `PartIII-b_IIIb-D2_1_3_1_2_1_3_1_5.lean` (tasks `PartIII-b:IIIb-D2/1/3/1/2/1/3/1/5/1,2,3,5,6,7,
8,9,10`); every analytic ingredient of this file is proved above. -/
theorem liouville_of_kernels (g1 : RadialPotential) (g2 : DilKerOK) (g3 : DilLap)
    (g4 : ConvTest) (g5 : ConvLap) (g6 : ConvSub) (g7 : CurlIsSolTest) (g8 : DivIsPhaseTest)
    (g9 : CurlCurlId) : IntertwineLiouville :=
  liouville_of g1 g2 g3 g4 g5 g6 g7 g8 g9 hardyPairBound
    (molSmall_of convFDeriv convLapT convSupport dilKBounds
      (convApprox_of dilKBounds dilKIntegral phaseTestLipY) g2 g4)
    (molLarge_of convFDeriv convLapT convDyKer convSupBound convSupport phaseTestSliceL1
      dilKBounds g2)

end UnforcedLeray.Short.PartIIIb.Concrete.Liou
