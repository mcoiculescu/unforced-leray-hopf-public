import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollCommDefs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollMinkowskiProof
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import UnforcedLeray.Lib.ConvIneq.RadialKernelNorm

/-!
# `FriedrichsBound` decomposed (ratio-2 mollifiers)

Source `the November 2 reference manuscript` lines 1351-1362, 1556-1583.
Design note: Mathlib's `ContDiffBump (0 : ℝ × Space)` has an opaque profile (no monotonicity), so the
Friedrichs bound is only claimed for the mollifiers the proof uses, `rOut = 2 rIn`.  Every such
`ρ` is the dilate of `kapUnit` by `rIn` (`ContDiffBump.apply`), `kap ρ z = rIn⁻⁴ kap kapUnit (rIn⁻¹ z)`,
so `‖kap ρ‖_{L¹} = ‖kap kapUnit‖_{L¹}` is an absolute constant (the source only needs *an* absolute
constant, lines 1556-1583).  Young/Minkowski in the phase cell then bounds the commutator.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- The unit Friedrichs bump (`rIn = 1`, `rOut = 2`).  The mollifiers used in the proof all have
`rOut = 2 rIn` (see `fwuAdjMoll_of`), and then `ρ` is a dilate of `kapUnit`. -/
def kapUnit : ContDiffBump (0 : ℝ × Space) :=
  { rIn := 1, rOut := 2, rIn_pos := one_pos, rIn_lt_rOut := one_lt_two }

/-- (K1) Dilation covariance of the Friedrichs kernel (source 1556-1583; no monotone profile is
needed, only that every `ContDiffBump` of ratio `rOut/rIn = 2` is the dilate of the same function
`kapUnit` by `rIn`): `kap ρ z = rIn⁻⁴ · kap kapUnit (rIn⁻¹ z)`.
Proof: `ContDiffBump.apply` gives `ρ z = β 2 (rIn⁻¹ z)` with `β = someContDiffBumpBase`; hence
`ρ.normed z = rIn⁻⁴ · kapUnit.normed (rIn⁻¹ z)` (`integral_comp_smul`, `finrank (ℝ × ℝ³) = 4`),
and `kerDv` of a dilate: `fderiv (κ ∘ (rIn⁻¹ • ·))` chain rule, `z.2` scales along. -/
def KapScale : Prop :=
  ∀ ρ : ContDiffBump (0 : ℝ × Space), ρ.rOut = 2 * ρ.rIn → ∀ z : ℝ × Space,
    kap ρ z = (ρ.rIn ^ 4)⁻¹ * kap kapUnit (ρ.rIn⁻¹ • z)

/-- (K2) The Friedrichs kernel is integrable (`ρ.normed volume` is `C^∞` with compact support,
`ContDiffBump.contDiff_normed`, `hasCompactSupport_normed`; `kap ρ` is continuous with compact
support). -/
def KapIntegrable : Prop :=
  ∀ ρ : ContDiffBump (0 : ℝ × Space), Integrable (kap ρ) volume

/-- Scale invariance of the `L¹` norm of the Friedrichs kernel. -/
theorem kap_l1_eq_of (h1 : KapScale) (ρ : ContDiffBump (0 : ℝ × Space))
    (hρ : ρ.rOut = 2 * ρ.rIn) : ∫ z, ‖kap ρ z‖ = ∫ z, ‖kap kapUnit z‖ := by
  have hr : 0 < ρ.rIn := ρ.rIn_pos
  have hfr : Module.finrank ℝ (ℝ × Space) = 4 := by
    rw [Module.finrank_prod, UnforcedLeray.Conv.finrank_space]
    simp
  have h : ∀ z, ‖kap ρ z‖ = (ρ.rIn ^ 4)⁻¹ * ‖kap kapUnit (ρ.rIn⁻¹ • z)‖ := by
    intro z
    rw [h1 ρ hρ z, norm_mul, Real.norm_of_nonneg (by positivity)]
  simp_rw [h]
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul (μ := (volume : Measure (ℝ × Space)))
      (fun z => ‖kap kapUnit z‖) ρ.rIn, hfr, smul_eq_mul,
    abs_of_nonneg (by positivity)]
  field_simp

/-- (M1) Translation invariance of the phase norm for `F ∈ Y_2`: a shift `w ↦ w - z` of the
argument (in `τ` by `z.1`, which is invisible by `P`-periodicity of the cell integral; in `y` by
Lebesgue invariance) does not change `‖F‖_{Y_2}`. -/
def PhaseNormShiftInv : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ F : ℝ × Space → CVec3, UnforcedLeray.Short.IIb.IsInYr P 2 F →
    ∀ z : ℝ × Space,
      UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => F (x - z)) =
        UnforcedLeray.Short.IIb.phaseLpNorm P 2 F

/-- (M2) Minkowski's integral inequality in the cell `L²((0,P] × ℝ³)` for a signed integrable
real kernel: `‖∫ k(z) F(· - z) dz‖_{Y_2} ≤ ∫ |k(z)| ‖F(· - z)‖_{Y_2} dz`.  Proof: as
`mollMinkowski_core` (`MollMinkowskiProof.lean`, `MollIQ`, `UnforcedLeray.Conv.mixedNorm_lintegral_le`)
with kernel `‖k z‖ₑ` in place of `ρ.normed` and `F` in place of `g(· - z) - g`; replace `F` by a
strongly measurable a.e.-representative as in `mollMinkowski`; the pointwise bound is
`‖∫ k(z) F(x - z) dz‖ ≤ ∫ ‖k z‖ ‖F(x - z)‖ dz` (valid also if the integral is not convergent). -/
def PhaseMinkowskiSigned : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ k : ℝ × Space → ℝ, Integrable k volume →
    ∀ F : ℝ × Space → CVec3, UnforcedLeray.Short.IIb.IsInYr P 2 F →
      UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => ∫ z, k z • F (x - z)) ≤
        ∫⁻ z, ENNReal.ofReal ‖k z‖ *
          UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => F (x - z))

/-- The absolute constant: the `L¹` norm of the Friedrichs kernel of the unit bump. -/
def kapConst : ℝ := ∫ z, ‖kap kapUnit z‖

theorem kap_integrable_of (h2 : KapIntegrable) (ρ : ContDiffBump (0 : ℝ × Space)) :
    Integrable (fun z => (1 / 2 : ℝ) * kap ρ z) volume :=
  (h2 ρ).const_mul _

theorem friedrichsBound_of (h1 : KapScale) (h2 : KapIntegrable)
    (hM1 : PhaseNormShiftInv) (hM2 : PhaseMinkowskiSigned) : FriedrichsBound := by
  intro P hP _hP1
  refine ⟨kapConst / 2 + 1, by
    have : 0 ≤ kapConst := integral_nonneg fun _ => norm_nonneg _
    positivity, ?_⟩
  intro ρ hρ F hF
  have hk := kap_integrable_of h2 ρ
  have hL1 : ∫ z, ‖(1 / 2 : ℝ) * kap ρ z‖ ≤ kapConst / 2 + 1 := by
    have : ∫ z, ‖(1 / 2 : ℝ) * kap ρ z‖ = (1 / 2 : ℝ) * ∫ z, ‖kap ρ z‖ := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp [norm_mul]
    rw [this]
    have := kap_l1_eq_of h1 ρ hρ
    unfold kapConst
    linarith
  have hstep := hM2 P hP (fun z => (1 / 2 : ℝ) * kap ρ z) hk F hF
  have hshift : ∫⁻ z, ENNReal.ofReal ‖(1 / 2 : ℝ) * kap ρ z‖ *
        UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => F (x - z)) =
      ENNReal.ofReal (∫ z, ‖(1 / 2 : ℝ) * kap ρ z‖) *
        UnforcedLeray.Short.IIb.phaseLpNorm P 2 F := by
    have h : ∀ z, ENNReal.ofReal ‖(1 / 2 : ℝ) * kap ρ z‖ *
        UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => F (x - z)) =
        ENNReal.ofReal ‖(1 / 2 : ℝ) * kap ρ z‖ *
        UnforcedLeray.Short.IIb.phaseLpNorm P 2 F := fun z => by rw [hM1 P hP F hF z]
    simp only [h]
    rw [lintegral_mul_const' _ _ (ne_of_lt hF.finite),
      ← ofReal_integral_eq_lintegral_ofReal hk.norm (Filter.Eventually.of_forall fun z => norm_nonneg _)]
  calc UnforcedLeray.Short.IIb.phaseLpNorm P 2 (commK ρ F)
      ≤ ENNReal.ofReal (∫ z, ‖(1 / 2 : ℝ) * kap ρ z‖) *
        UnforcedLeray.Short.IIb.phaseLpNorm P 2 F := hshift ▸ hstep
    _ ≤ ENNReal.ofReal (kapConst / 2 + 1) * UnforcedLeray.Short.IIb.phaseLpNorm P 2 F := by
        gcongr

end UnforcedLeray.Short.PartIIIb.Concrete
