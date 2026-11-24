import UnforcedLeray.Short.PartIIIa.Targets

/-!
# Part III-a: the outer-coordinate moment identity (SP 2790-2795)

`outerMoment_of_parts : OuterMomentOfParts`. From `PlaneRadialInv` (polar coordinates on `x' ∈ ℝ²`
with `u = |x'|^{-2}`) we get `OuterMomentIdentity`. Write `Φ(u)` for the `Y`-integral at age `u`.
For `u > 0` the substitution `η = Y√u` (Jacobian `u^{-1/2}`) gives
`Φ(u) = √u · ∫_η (1 + |η|/√u) N_q(u, η) dη`, where `N_q(u, η) = ‖T(u, ·, η)‖_{L²(dq/c)}`.
Then `u^{-2} Φ(u) = u^{-3/2} ∫_η (1 + |η|/√u) N_q(u, η) dη`, which is the integrand of
`firstMoment c 0 T`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- The transverse norm `N_q(u, η) = (∫_{q ∈ [-c/2, c/2)} c⁻¹ |T(u, q, η)|² dq)^{1/2}`, the factor of
`firstMoment`. -/
def t11Nq (c : ℝ) (T : ℝ × (ℝ × ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (u η : ℝ) : ℝ≥0∞ :=
  (∫⁻ q in Ico (-(c / 2)) (c / 2),
    ENNReal.ofReal c⁻¹ * ENNReal.ofReal (frobSq (T (u, (q, η))))) ^ (1 / 2 : ℝ)

/-- The `Y`-integral of `OuterMomentIdentity`, as a function of `u = |x'|^{-2}`. The physical
tensor `F = uT` contributes the factor `u²` inside the `q`-integral. -/
def t11Phi (c : ℝ) (T : ℝ × (ℝ × ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (u : ℝ) : ℝ≥0∞ :=
  ∫⁻ Y : ℝ, ENNReal.ofReal (1 + |Y|) *
    (∫⁻ q in Ico (-(c / 2)) (c / 2),
      ENNReal.ofReal c⁻¹ * ENNReal.ofReal (u ^ 2 * frobSq (T (u, (q, Y * Real.sqrt u))))) ^
        (1 / 2 : ℝ)

/-- Measurability of the Frobenius norm squared of a measurable tensor field. -/
lemma t11_frob_meas (T : ℝ × (ℝ × ℝ) → Matrix (Fin 3) (Fin 3) ℝ)
    (hT : ∀ a b, Measurable fun p => T p a b) : Measurable fun p => frobSq (T p) := by
  unfold frobSq
  exact Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => (hT a b).pow_const 2

/-- Measurability of `η ↦ N_q(u, η)`. -/
lemma t11_Nq_meas (c : ℝ) (T : ℝ × (ℝ × ℝ) → Matrix (Fin 3) (Fin 3) ℝ)
    (hT : ∀ a b, Measurable fun p => T p a b) (u : ℝ) : Measurable (t11Nq c T u) := by
  have hfrob : Measurable fun p => frobSq (T p) := t11_frob_meas T hT
  have hM : Measurable fun z : ℝ × ℝ => (u, (z.2, z.1)) := by fun_prop
  have hf : Measurable fun z : ℝ × ℝ =>
      ENNReal.ofReal c⁻¹ * ENNReal.ofReal (frobSq (T (u, (z.2, z.1)))) :=
    measurable_const.mul (ENNReal.measurable_ofReal.comp (hfrob.comp hM))
  unfold t11Nq
  exact (Measurable.lintegral_prod_right' hf).pow_const _

/-- Linear change of variables `η = Y a` in a lower integral (`a > 0`, Jacobian `a⁻¹`). -/
lemma t11_lintegral_scale (a : ℝ) (ha : 0 < a) (K : ℝ → ℝ≥0∞) (hK : Measurable K) :
    ∫⁻ Y : ℝ, K (Y * a) = ENNReal.ofReal a⁻¹ * ∫⁻ η : ℝ, K η := by
  have hm : Measurable fun Y : ℝ => Y * a := by fun_prop
  have hmap : Measure.map (fun Y : ℝ => Y * a) volume = ENNReal.ofReal |a⁻¹| • volume :=
    Real.map_volume_mul_right ha.ne'
  calc ∫⁻ Y : ℝ, K (Y * a)
      = ∫⁻ η : ℝ, K η ∂(Measure.map (fun Y : ℝ => Y * a) volume) :=
        (lintegral_map hK hm).symm
    _ = ∫⁻ η : ℝ, K η ∂(ENNReal.ofReal |a⁻¹| • volume) := by rw [hmap]
    _ = ENNReal.ofReal a⁻¹ * ∫⁻ η : ℝ, K η := by
        rw [lintegral_smul_measure, abs_of_pos (inv_pos.mpr ha), smul_eq_mul]

/-- `(ofReal u ^ 2)^{1/2} = ofReal u`. -/
lemma t11_sq_rpow_half (u : ℝ) : (ENNReal.ofReal u ^ 2) ^ (1 / 2 : ℝ) = ENNReal.ofReal u := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- The `q`-integral with the factor `u²` pulled out of the integrand (`u > 0`). -/
lemma t11_inner_step (c : ℝ) (T : ℝ × (ℝ × ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (u : ℝ) (hu : 0 < u)
    (Y : ℝ) :
    (∫⁻ q in Ico (-(c / 2)) (c / 2),
      ENNReal.ofReal c⁻¹ * ENNReal.ofReal (u ^ 2 * frobSq (T (u, (q, Y * Real.sqrt u))))) ^
        (1 / 2 : ℝ)
      = ENNReal.ofReal u * t11Nq c T u (Y * Real.sqrt u) := by
  unfold t11Nq
  have hrw : ∀ q : ℝ,
      ENNReal.ofReal c⁻¹ * ENNReal.ofReal (u ^ 2 * frobSq (T (u, (q, Y * Real.sqrt u))))
        = ENNReal.ofReal u ^ 2 *
          (ENNReal.ofReal c⁻¹ * ENNReal.ofReal (frobSq (T (u, (q, Y * Real.sqrt u))))) := by
    intro q
    rw [ENNReal.ofReal_mul (sq_nonneg u), ENNReal.ofReal_pow hu.le]
    ring
  simp_rw [hrw]
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2), t11_sq_rpow_half]

/-- Pointwise identity behind `firstMoment` (`u > 0`):
`Φ(u) = √u · ∫_η (1 + |η|/√u) N_q(u, η) dη`. -/
lemma t11_phi_eq (c : ℝ) (T : ℝ × (ℝ × ℝ) → Matrix (Fin 3) (Fin 3) ℝ)
    (hT : ∀ a b, Measurable fun p => T p a b) (u : ℝ) (hu : 0 < u) :
    t11Phi c T u = ENNReal.ofReal (Real.sqrt u) *
      ∫⁻ η : ℝ, ENNReal.ofReal (1 + |η| / Real.sqrt u) * t11Nq c T u η := by
  have hsqrt : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
  have hK : Measurable fun η : ℝ => ENNReal.ofReal (1 + |η| / Real.sqrt u) * t11Nq c T u η :=
    (ENNReal.measurable_ofReal.comp
      (by fun_prop : Measurable fun η : ℝ => 1 + |η| / Real.sqrt u)).mul
      (t11_Nq_meas c T hT u)
  have hKY : ∀ Y : ℝ, ENNReal.ofReal (1 + |Y|) * t11Nq c T u (Y * Real.sqrt u) =
      ENNReal.ofReal (1 + |Y * Real.sqrt u| / Real.sqrt u) * t11Nq c T u (Y * Real.sqrt u) := by
    intro Y
    rw [abs_mul, abs_of_pos hsqrt, mul_div_cancel_right₀ _ hsqrt.ne']
  have hkey : u * (Real.sqrt u)⁻¹ = Real.sqrt u := by
    calc u * (Real.sqrt u)⁻¹ = (Real.sqrt u * Real.sqrt u) * (Real.sqrt u)⁻¹ := by
          rw [Real.mul_self_sqrt hu.le]
      _ = Real.sqrt u * (Real.sqrt u * (Real.sqrt u)⁻¹) := by ring
      _ = Real.sqrt u := by rw [mul_inv_cancel₀ hsqrt.ne', mul_one]
  have h1 : ∀ Y : ℝ, ENNReal.ofReal (1 + |Y|) *
      (∫⁻ q in Ico (-(c / 2)) (c / 2),
        ENNReal.ofReal c⁻¹ * ENNReal.ofReal (u ^ 2 * frobSq (T (u, (q, Y * Real.sqrt u))))) ^
          (1 / 2 : ℝ)
      = ENNReal.ofReal u * (ENNReal.ofReal (1 + |Y|) * t11Nq c T u (Y * Real.sqrt u)) := by
    intro Y
    rw [t11_inner_step c T u hu Y]
    ring
  unfold t11Phi
  rw [lintegral_congr h1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_congr hKY,
    t11_lintegral_scale (Real.sqrt u) hsqrt _ hK, ← mul_assoc, ← ENNReal.ofReal_mul hu.le, hkey]

/-- Measurability of `Φ = t11Phi c T`: the `q`-integral and then the `Y`-integral are measurable
functions of the parameters (`Measurable.lintegral_prod_right'`). -/
lemma t11_phi_meas (c : ℝ) (T : ℝ × (ℝ × ℝ) → Matrix (Fin 3) (Fin 3) ℝ)
    (hT : ∀ a b, Measurable fun p => T p a b) : Measurable (t11Phi c T) := by
  have hfrob : Measurable fun p => frobSq (T p) := t11_frob_meas T hT
  have hM : Measurable fun z : (ℝ × ℝ) × ℝ => (z.1.1, (z.2, z.1.2 * Real.sqrt z.1.1)) := by
    fun_prop
  have hsq : Measurable fun z : (ℝ × ℝ) × ℝ => z.1.1 ^ 2 := by fun_prop
  have hF3 : Measurable fun z : (ℝ × ℝ) × ℝ =>
      ENNReal.ofReal c⁻¹ *
        ENNReal.ofReal (z.1.1 ^ 2 * frobSq (T (z.1.1, (z.2, z.1.2 * Real.sqrt z.1.1)))) :=
    measurable_const.mul (ENNReal.measurable_ofReal.comp (hsq.mul (hfrob.comp hM)))
  have hG : Measurable fun x : ℝ × ℝ => ∫⁻ q in Ico (-(c / 2)) (c / 2),
      ENNReal.ofReal c⁻¹ * ENNReal.ofReal (x.1 ^ 2 * frobSq (T (x.1, (q, x.2 * Real.sqrt x.1)))) :=
    Measurable.lintegral_prod_right' hF3
  have hA : Measurable fun x : ℝ × ℝ => ENNReal.ofReal (1 + |x.2|) :=
    ENNReal.measurable_ofReal.comp (by fun_prop : Measurable fun x : ℝ × ℝ => 1 + |x.2|)
  have hF2 : Measurable fun x : ℝ × ℝ => ENNReal.ofReal (1 + |x.2|) *
      (∫⁻ q in Ico (-(c / 2)) (c / 2),
        ENNReal.ofReal c⁻¹ * ENNReal.ofReal (x.1 ^ 2 * frobSq (T (x.1, (q, x.2 * Real.sqrt x.1)))))
        ^ (1 / 2 : ℝ) :=
    hA.mul (hG.pow_const _)
  unfold t11Phi
  exact Measurable.lintegral_prod_right' hF2

/-- **`OuterMomentIdentity` from `PlaneRadialInv`** (SP 2790-2795): the `Y`-integral is
`Φ(|x'|^{-2})`, `PlaneRadialInv` turns `∫_{ℝ²}` into `π∫_0^∞ u^{-2}Φ(u) du`, and the pointwise
identity `u^{-2}Φ(u) = u^{-3/2} ∫_η (...)` identifies the result with `π · firstMoment c 0 T`. -/
theorem outerMoment_of_parts : UnforcedLeray.Short.IIIa.OuterMomentOfParts := by
  unfold OuterMomentOfParts OuterMomentIdentity
  intro hP c _hc T hT
  unfold PlaneRadialInv at hP
  have hPR := hP (t11Phi c T) (t11_phi_meas c T hT)
  show ∫⁻ x' : ℝ × ℝ, t11Phi c T ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹) =
    ENNReal.ofReal Real.pi * firstMoment c 0 T
  rw [hPR]
  congr 1
  unfold firstMoment
  refine setLIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
  have hu' : (0 : ℝ) < u := hu
  have hexp : u ^ (-2 : ℝ) * Real.sqrt u = u ^ (-3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hu']
    norm_num
  rw [t11_phi_eq c T hT u hu', ← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hu'.le _), hexp]
  simp only [t11Nq]

end UnforcedLeray.Short.IIIa
