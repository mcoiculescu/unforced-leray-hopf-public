import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_18_3_4_2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.Int

/-!
# Decomposition of `SepBoxIntegrable` (`PartIII-b:C/near/masked/18/3/4/2/1`)

Source `the November 2 reference manuscript`
3611-3621 (`sep:resolvent`), 3594-3606 (kernel bounds).  Integrability of the `sepW` integrand
for a box tensor follows from: (A) `cartLift` is bounded with compact `z`-support; (B) the
uniform-in-`t` kernel gradient bound `|∇K_t(x)| ≤ C (|x|²+t)^{-2}`; (C) measurability; (D) the
integrability of the resulting radial majorant on `(0,1) × Space`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

open MeasureTheory Set UnforcedLeray.Axi UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Short.PartIIIb.Concrete
open UnforcedLeray.Short.PartIIIb.NearInst (cartLift IsBoxTensor hRad)

/-- (B) Uniform-in-`t` gradient bound of the heat–Leray kernel (3604-3610):
`|∇K_t(x)| ≤ C (|x|²+t)^{-2}` for all `t > 0`.  (From `|x|^{-4}` for `|x|² ≥ t` and scaling
`K_t(x) = t^{-3/2} K_1(x/√t)` with `∇K_1` bounded for `|x| ≤ 1`.) -/
def HeatLerayKGradBound : Prop :=
  ∃ C : ℝ, ∀ t : ℝ, 0 < t → ∀ (i j k : Fin 3) (x : Space),
    |fderiv ℝ (fun y => IIIa.heatLerayK t i j y) x (coordinateVector k)| ≤
      C * ((‖x‖ ^ 2 + t) ^ 2)⁻¹

/-- (A) `cartLift R c m` of a box tensor is entrywise bounded and supported in a compact set of
`z` (the band `s₁ ≤ R²/ϱ² ≤ s₂`, `|z₃| ≤ L ϱ/R`), for every phase `τ`. -/
def BoxCartLiftSupport : Prop :=
  ∀ (R c : ℝ), 0 < R → 0 < c → ∀ m : Chart → Ten3, IsBoxTensor m →
    ∃ (B : ℝ) (S : Set Space), IsCompact S ∧ ∀ (τ : ℝ) (z : Space),
      (∀ j k : Fin 3, |cartLift R c m τ z j k| ≤ B) ∧ (z ∉ S → cartLift R c m τ z = 0)

/-- (C) Measurability of the `sepW` integrand for box tensors. -/
def SepBoxMeasurable : Prop :=
  ∀ (ν R c μ : ℝ), 0 < ν → 0 < R → 0 < c → ∀ m : Chart → Ten3, IsBoxTensor m →
    ∀ (τ : ℝ) (y : Space) (i : Fin 3),
      MeasureTheory.AEStronglyMeasurable
        (fun p => sepPhi ν (μ : ℂ) (cartLift R c m) τ i p y) sepRho

/-- (D) The radial majorant is integrable on `(0,1) × Space` for compact `S` (3611-3621):
`∫_S |z| ... ≲ t^{-1/2}`, `t = ν(1-l²)`, `∫ (1-l)^{-1/2} dl < ∞` for `l ≥ 1/2`, and
`l^{2μ+2}` integrable at `0` (`μ > -3/2`, with `t ≥ 3ν/4` there). -/
def SepRadialMajorantIntegrable : Prop :=
  ∀ (ν μ : ℝ) (S : Set Space) (y : Space), 0 < ν → -(1 / 4 : ℝ) < μ → IsCompact S →
    Integrable (fun p : ℝ × Space =>
      p.1 ^ (2 * μ + 2) * S.indicator (fun _ => (1 : ℝ)) p.2 *
        ((‖y - p.1 • p.2‖ ^ 2 + ν * (1 - p.1 ^ 2)) ^ 2)⁻¹) sepRho

/-- `SepBoxIntegrable` from (A)-(D): the integrand is dominated by
`18 |C| |B|` times the radial majorant. -/
theorem sepBoxIntegrable_of (hA : BoxCartLiftSupport) (hB : HeatLerayKGradBound)
    (hC : SepBoxMeasurable) (hD : SepRadialMajorantIntegrable) : SepBoxIntegrable := by
  intro ν R c μ hν hR hc hμ m hm τ y _ i
  obtain ⟨C, hCb⟩ := hB
  obtain ⟨B, S, hS, hBS⟩ := hA R c hR hc m hm
  have hint := (hD ν μ S y hν hμ hS).const_mul (18 * |C| * |B|)
  refine Integrable.mono' hint (hC ν R c μ hν hR hc m hm τ y i) ?_
  filter_upwards [ae_mem_Ioo_sepRho] with p hp
  obtain ⟨hp0, hp1⟩ := hp
  have ht : 0 < ν * (1 - p.1 ^ 2) := mul_pos hν (by nlinarith)
  set w : ℝ := ((‖y - p.1 • p.2‖ ^ 2 + ν * (1 - p.1 ^ 2)) ^ 2)⁻¹ with hw
  have hw0 : 0 ≤ w := by positivity
  set ind : ℝ := S.indicator (fun _ => (1 : ℝ)) p.2 with hind
  have hind0 : 0 ≤ ind := by
    simp only [hind]; exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hT : ∀ j k : Fin 3, |cartLift R c m (τ + 2 * Real.log p.1) p.2 j k| ≤ |B| * ind := by
    intro j k
    by_cases hz : p.2 ∈ S
    · have : ind = 1 := by simp [hind, hz]
      rw [this, mul_one]
      exact (hBS _ _).1 j k |>.trans (le_abs_self B)
    · have : ind = 0 := by simp [hind, hz]
      rw [this, mul_zero]
      rw [(hBS (τ + 2 * Real.log p.1) p.2).2 hz]; simp
  have hK : ∀ j k : Fin 3,
      |fderiv ℝ (fun x => IIIa.heatLerayK (ν * (1 - p.1 ^ 2)) i j x) (y - p.1 • p.2)
        (coordinateVector k)| ≤ |C| * w := by
    intro j k
    refine (hCb _ ht i j k _).trans ?_
    exact mul_le_mul_of_nonneg_right (le_abs_self C) hw0
  have hterm : ∀ j k : Fin 3,
      ‖((fderiv ℝ (fun x => IIIa.heatLerayK (ν * (1 - p.1 ^ 2)) i j x) (y - p.1 • p.2)
        (coordinateVector k) : ℝ) : ℂ) *
        ((cartLift R c m (τ + 2 * Real.log p.1) p.2 j k : ℝ) : ℂ)‖ ≤ (|C| * w) * (|B| * ind) := by
    intro j k
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul (hK j k) (hT j k) (abs_nonneg _) (by positivity)
  have hsum : ‖∑ j : Fin 3, ∑ k : Fin 3,
      ((fderiv ℝ (fun x => IIIa.heatLerayK (ν * (1 - p.1 ^ 2)) i j x) (y - p.1 • p.2)
        (coordinateVector k) : ℝ) : ℂ) *
        ((cartLift R c m (τ + 2 * Real.log p.1) p.2 j k : ℝ) : ℂ)‖ ≤
      9 * ((|C| * w) * (|B| * ind)) := by
    refine (norm_sum_le _ _).trans ?_
    have h1 : ∀ j : Fin 3, ‖∑ k : Fin 3,
        ((fderiv ℝ (fun x => IIIa.heatLerayK (ν * (1 - p.1 ^ 2)) i j x) (y - p.1 • p.2)
          (coordinateVector k) : ℝ) : ℂ) *
          ((cartLift R c m (τ + 2 * Real.log p.1) p.2 j k : ℝ) : ℂ)‖ ≤
        3 * ((|C| * w) * (|B| * ind)) := by
      intro j
      refine (norm_sum_le _ _).trans ?_
      calc ∑ k : Fin 3, _ ≤ ∑ _k : Fin 3, ((|C| * w) * (|B| * ind)) :=
            Finset.sum_le_sum fun k _ => hterm j k
        _ = 3 * ((|C| * w) * (|B| * ind)) := by simp
    calc _ ≤ ∑ _j : Fin 3, 3 * ((|C| * w) * (|B| * ind)) := Finset.sum_le_sum fun j _ => h1 j
      _ = 9 * ((|C| * w) * (|B| * ind)) := by simp; ring
  have hpow : ‖((p.1 : ℝ) : ℂ) ^ (2 * (μ : ℂ) + 2)‖ = p.1 ^ (2 * μ + 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hp0]; simp
  have hpow0 : 0 ≤ p.1 ^ (2 * μ + 2) := Real.rpow_nonneg hp0.le _
  unfold sepPhi
  rw [norm_mul, norm_mul, hpow]
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  simp only [norm_neg, h2]
  calc 2 * p.1 ^ (2 * μ + 2) * _ ≤ 2 * p.1 ^ (2 * μ + 2) * (9 * ((|C| * w) * (|B| * ind))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 18 * |C| * |B| * (p.1 ^ (2 * μ + 2) * ind * w) := by ring

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
