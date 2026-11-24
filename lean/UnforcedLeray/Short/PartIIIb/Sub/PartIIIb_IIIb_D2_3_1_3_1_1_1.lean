import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_3_1_1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2

/-!
# `SepFarDecay` decomposed (`PartIII-b:IIIb-D2/3/1/3/1/1/1`)

Source `the November 2 reference manuscript`
4155-4186 (far field of the old source), 3604-3621 (`sep:kernel`, `sep:resolvent`),
3631-3646 (Cauchy-Schwarz bookkeeping).

Route: `sepW = ∫ Φ dρ` on `ρ = (vol|_{(0,1)}) ⊗ vol` (`sepW_eq_integral`), a pointwise far-field
bound `|D^n Φ| ≤ C · farMaj_n` from `sep:kernel`, the bound `∫ farMaj_n ≤ C ϱ^{-3}`, and
differentiation under the integral sign.  For `rOut = 0` the source is supported on a null set
so `sepW = 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- The far-field majorant `l^{2Re μ+2} |y - l z|^{-4-n} |T(τ+2 log l, z)|` (at `y - l z = 0` the
power is `0`, harmless since then `T = 0` on the support). -/
def farMaj (μ : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (n : ℕ) (y : Space)
    (p : ℝ × Space) : ℝ :=
  p.1 ^ (2 * μ.re + 2) * ‖y - p.1 • p.2‖ ^ (-(4 + (n : ℝ))) *
    IIIa.tensorNorm (T (τ + 2 * Real.log p.1) p.2)

/-- **Leaf Z** (support on a null set): `rOut = 0` forces `T = 0` off the axis
`{z₀ = z₁ = 0}`, a Lebesgue-null set, so every `z`-integral in `sepW` vanishes. -/
def SepWZeroOfRoutZero : Prop :=
  ∀ (ν : ℝ) (μ : ℂ) (P : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ),
    IIIa.IsSepSource P 0 T → ∀ (y : Space) (τ : ℝ) (i : Fin 3), IIIa.sepW ν μ T y τ i = 0

/-- **Leaf A** (pointwise far bound; 3604-3621 with `|y - l z| ≥ ϱ y - rOut ≥ ϱ y / 2` on
`supp T`, `|D^j∇K_t(x)| ≤ C_j |x|^{-4-j}` uniformly in `t > 0`): for `0 < rOut`, `2 rOut ≤ ϱ y`,
`l ∈ (0,1)`: `|Φ(l,z,y)| ≤ C farMaj_0` and `|∇_y Φ(l,z,y)| ≤ C farMaj_1`, `C` independent of
`y, l, z`. -/
def FarPointwise : Prop :=
  IIIa.SepKernelBounds → ∀ (ν : ℝ) (μ : ℂ) (rOut P : ℝ)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ), 0 < ν → -(1 / 4) < μ.re → 0 < rOut → 0 < P →
    IIIa.IsSepSource P rOut T → ∀ τ : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : Fin 3) (y : Space),
      2 * rOut ≤ ϱ y → ∀ l ∈ Ioo (0 : ℝ) 1, ∀ z : Space,
        ‖sepPhi ν μ T τ i (l, z) y‖ ≤ C * farMaj μ T τ 0 y (l, z) ∧
        ‖fderiv ℝ (sepPhi ν μ T τ i (l, z)) y‖ ≤ C * farMaj μ T τ 1 y (l, z)

/-- **Leaf B** (integral of the majorant; 3631-3646: `∫_{cyl} (a² + (c - l z₃)²)^{-k} ≲ l⁻¹ a^{1-2k}`
on the cylinder `|z'| ≤ rOut`, Cauchy-Schwarz in `z` against the `L²_z` norm, then in `l` on each
period and the sum over periods, `2Re μ + 3/2 > 0`): for `0 < rOut`, `2 rOut ≤ ϱ y`,
`farMaj_n(y,·)` is `ρ`-integrable with integral `≤ C ϱ^{-3}` (`n = 0, 1`). -/
def FarMajorantBound : Prop :=
  ∀ (μ : ℂ) (rOut P : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ),
    -(1 / 4) < μ.re → 0 < rOut → 0 < P → IIIa.IsSepSource P rOut T → SepMoment P T →
    ∀ τ : ℝ, ∃ C : ℝ, ∀ (y : Space), 2 * rOut ≤ ϱ y → ∀ n : ℕ, n ≤ 1 →
      Integrable (farMaj μ T τ n y) sepRho ∧ ∫ p, farMaj μ T τ n y p ∂sepRho ≤ C * ϱ y ^ (-3 : ℝ)

/-- **Leaf C** (differentiation under the integral, `hasFDerivAt_integral_of_dominated_of_fderiv_le`
with the gap majorant `sepMajorant μ T τ 1` of `SepGapPointwise`/`SepGapMajorantIntegrable`): for
`0 < rOut` and `rOut < ϱ y` the integrand `Φ(·,y)` is `ρ`-integrable and
`∇_y W = ∫ ∇_y Φ dρ`. -/
def SepWFderivIntegral : Prop :=
  ∀ (ν : ℝ) (μ : ℂ) (rOut P : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ),
    0 < ν → -(1 / 4) < μ.re → 0 < rOut → 0 < P → IIIa.IsSepSource P rOut T → SepMoment P T →
    ∀ (τ : ℝ) (i : Fin 3) (y : Space), rOut < ϱ y →
      Integrable (fun p => sepPhi ν μ T τ i p y) sepRho ∧
      fderiv ℝ (fun y' => IIIa.sepW ν μ T y' τ i) y =
        ∫ p, fderiv ℝ (sepPhi ν μ T τ i p) y ∂sepRho

theorem sepFarDecay_of (hK : IIIa.SepKernelBounds) (hZ : SepWZeroOfRoutZero)
    (hA : FarPointwise) (hB : FarMajorantBound) (hC : SepWFderivIntegral) : SepFarDecay := by
  intro ν μ rOut P T hν hμ hr hP hT hM τ
  rcases hr.eq_or_lt with h0 | hpos
  · subst h0
    refine ⟨0, fun i y _ => ?_⟩
    have hz : ∀ y' : Space, IIIa.sepW ν μ T y' τ i = 0 := fun y' => hZ ν μ P T hT y' τ i
    have hf : (fun y' => IIIa.sepW ν μ T y' τ i) = fun _ => (0 : ℂ) := funext hz
    rw [hz, hf]
    simp
  obtain ⟨CA, hCA0, hAx⟩ := hA hK ν μ rOut P T hν hμ hpos hP hT τ
  obtain ⟨CB, hBx⟩ := hB μ rOut P T hμ hpos hP hT hM τ
  refine ⟨CA * CB, fun i y hy => ?_⟩
  have hgap : rOut < ϱ y := by
    have : 0 ≤ ϱ y := by unfold ϱ; exact Real.sqrt_nonneg _
    linarith
  obtain ⟨hint, hder⟩ := hC ν μ rOut P T hν hμ hpos hP hT hM τ i y hgap
  have hB0 := hBx y hy 0 (by norm_num)
  have hB1 := hBx y hy 1 (by norm_num)
  constructor
  · rw [sepW_eq_integral ν μ T τ i y hint]
    refine (norm_integral_le_of_norm_le (hB0.1.const_mul CA) ?_).trans ?_
    · filter_upwards [ae_mem_Ioo_sepRho] with p hp
      exact (hAx i y hy p.1 hp p.2).1
    · rw [integral_const_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left hB0.2 hCA0
  · rw [hder]
    refine (norm_integral_le_of_norm_le (hB1.1.const_mul CA) ?_).trans ?_
    · filter_upwards [ae_mem_Ioo_sepRho] with p hp
      exact (hAx i y hy p.1 hp p.2).2
    · rw [integral_const_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left hB1.2 hCA0

end UnforcedLeray.Short.PartIIIb.Concrete
