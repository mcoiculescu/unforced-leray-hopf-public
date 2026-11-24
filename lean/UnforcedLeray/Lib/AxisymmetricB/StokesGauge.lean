import UnforcedLeray.Lib.AxisymmetricB.Stream
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# AX06 (gauge): the Stokes stream function of a decaying solenoidal axisymmetric field


§5 Layer 3, target AX06 (`stokesGauge`). Blueprint unit served: B0846 (`eq:affine-4-99c`,
tex 12510–12522): with `X = X_{0,mt}`,
`Ψ₀(ρ, z) = −∫_ρ^∞ ρ' X_z(ρ', z) dρ'`, `X_z = ρ⁻¹ ∂_ρ Ψ₀`, `X_ρ = −ρ⁻¹ ∂_z Ψ₀`; the boundary
term at infinity vanishes by the decay `eq:affine-4-99b` (tex 12503–12507,
`|D^j X| ≤ C ρ^{-4-j}`), and the primitive bound `eq:affine-4-99d` (tex 12517–12520) at `j = 0`.

The field is the meridional lift `X = liftMer b`, `b = (X_ρ, X_z)`. Hypotheses
(`IsStokesData a C b`), all on the exterior half-plane `{ρ > a}`, `a ≥ 0` (the manuscript's
bounds hold there with `a = 0`; any exterior region is allowed):
* `b` is `C¹`;
* `X` is solenoidal: `∂_ρ X_ρ + X_ρ/ρ + ∂_z X_z = 0` (`div_zero`; equivalently
  `div (liftMer b) = 0` off the axis, `div_zero_of_divergence`);
* `‖b‖ ≤ C ρ^{-4}` and `‖Db‖ ≤ C ρ^{-5}` (`eq:affine-4-99b` for `j = 0, 1`; the profile
  derivative is a restriction of `D_y X`).

Main results:
* `hasDerivAt_integral_Ioi`: `d/dρ ∫_ρ^∞ f = −f(ρ)` for `f` continuous and integrable at `∞`;
* `IsStokesData.dρ_stokesGauge`, `IsStokesData.dz_stokesGauge`: `∂_ρ Ψ₀ = ρ X_z`,
  `∂_z Ψ₀ = −ρ X_ρ` (differentiation under the integral sign in `z`, dominated by `C ρ'^{-4}`;
  the divergence identity `∂_ρ(ρ X_ρ) = −ρ ∂_z X_z` and the vanishing of `ρ X_ρ` at infinity);
* `IsStokesData.hasStrictFDerivAt_stokesGauge`: `Ψ₀` is (strictly) Fréchet differentiable on
  `{ρ > a}` (continuous partial derivatives, Mathlib `hasStrictFDerivAt_uncurry_coprod`);
* `IsStokesData.streamLift_stokesGauge` (**B0846**): `X = streamLift Ψ₀` on `{ϱ > a}`;
* `IsStokesData.abs_stokesGauge_le`: `|Ψ₀| ≤ (C/2) ρ^{-2}` (`eq:affine-4-99d`, `j = 0`), and
  `abs_dρ_stokesGauge_le`, `abs_dz_stokesGauge_le`: `|∂Ψ₀| ≤ C ρ^{-3}` (`j = 1`). The
  orders `j ≥ 2` of `eq:affine-4-99d` are not built here.

Junk values: `Ψ₀` is a Bochner integral; it is the manuscript's integral where `ρ ↦ ρ X_z` is
integrable on `(ρ, ∞)`, which the decay hypothesis gives for every `ρ > a`. All conclusions are
stated for `ρ > a` only.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Real Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Axi

/-! ### Tail integrals -/

/-- `d/dρ ∫_ρ^∞ f = −f(ρ)` for `f` continuous on `(a, ∞)` and integrable at `∞`. -/
theorem hasDerivAt_integral_Ioi {a : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Ioi a))
    (hint : ∀ ρ, a < ρ → IntegrableOn f (Ioi ρ)) {ρ₀ : ℝ} (hρ₀ : a < ρ₀) :
    HasDerivAt (fun ρ => ∫ r in Ioi ρ, f r) (-f ρ₀) ρ₀ := by
  set ρ₁ := (a + ρ₀) / 2 with hρ₁
  have h1 : a < ρ₁ := by rw [hρ₁]; linarith
  have h2 : ρ₁ < ρ₀ := by rw [hρ₁]; linarith
  have hsub : uIcc ρ₁ ρ₀ ⊆ Ioi a := by
    rw [uIcc_of_le h2.le]
    intro x hx
    exact lt_of_lt_of_le h1 hx.1
  have hii : IntervalIntegrable f volume ρ₁ ρ₀ := (hf.mono hsub).intervalIntegrable
  have hd : HasDerivAt (fun u => ∫ x in ρ₁..u, f x) (f ρ₀) ρ₀ :=
    intervalIntegral.integral_hasDerivAt_right hii
      (hf.stronglyMeasurableAtFilter isOpen_Ioi ρ₀ hρ₀)
      (hf.continuousAt (isOpen_Ioi.mem_nhds hρ₀))
  have hd' := (hasDerivAt_const ρ₀ (∫ r in Ioi ρ₁, f r)).sub hd
  rw [zero_sub] at hd'
  refine hd'.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioi.mem_nhds h2] with ρ hρ
  have hρ' : ρ₁ ≤ ρ := le_of_lt hρ
  show ∫ r in Ioi ρ, f r = (∫ r in Ioi ρ₁, f r) - ∫ x in ρ₁..ρ, f x
  rw [intervalIntegral.integral_of_le hρ', ← Ioc_union_Ioi_eq_Ioi hρ',
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      ((hint ρ₁ h1).mono_set Ioc_subset_Ioi_self) (hint ρ (lt_trans h1 hρ))]
  ring

/-! ### The gauge and its hypotheses -/

/-- **AX06 `stokesGauge`** (B0846, tex 12512): `Ψ₀(ρ, z) = −∫_ρ^∞ ρ' X_z(ρ', z) dρ'` for the
profile `b = (X_ρ, X_z)`. -/
def stokesGauge (b : ℝ × ℝ → Merid) (p : ℝ × ℝ) : ℝ := -∫ r in Ioi p.1, r * b (r, p.2) 1

/-- The hypotheses of B0846 on the exterior half-plane `{ρ > a}`: `C¹`, solenoidal, and the
decay `eq:affine-4-99b` for `j = 0, 1`. -/
structure IsStokesData (a C : ℝ) (b : ℝ × ℝ → Merid) : Prop where
  nonneg : 0 ≤ a
  smooth : ContDiffOn ℝ 1 b (Ioi a ×ˢ univ)
  div_zero : ∀ p : ℝ × ℝ, a < p.1 → dρ b p 0 + b p 0 / p.1 + dz b p 1 = 0
  decay : ∀ p : ℝ × ℝ, a < p.1 → ‖b p‖ ≤ C * p.1 ^ (-4 : ℝ)
  decay_deriv : ∀ p : ℝ × ℝ, a < p.1 → ‖fderiv ℝ b p‖ ≤ C * p.1 ^ (-5 : ℝ)

theorem isOpen_halfPlane' (a : ℝ) : IsOpen (Ioi a ×ˢ (univ : Set ℝ)) :=
  isOpen_Ioi.prod isOpen_univ

theorem rpow_mul_self {r : ℝ} (hr : 0 < r) (k : ℝ) : r * r ^ k = r ^ (k + 1) := by
  rw [Real.rpow_add hr, Real.rpow_one, mul_comm]

/-- The solenoidal condition from the field: if `div (liftMer b) = 0` on `{ϱ > a}`, then the
profile form `∂_ρ b_r + b_r/ρ + ∂_z b_z = 0` holds on `{ρ > a}` (`divergence_liftMer`). -/
theorem div_zero_of_divergence {a : ℝ} (ha : 0 ≤ a) {b : ℝ × ℝ → Merid}
    (hb : ContDiffOn ℝ 1 b (Ioi a ×ˢ univ))
    (hdiv : ∀ y : Space, a < ϱ y → divergence (liftMer b) y = 0) :
    ∀ p : ℝ × ℝ, a < p.1 → dρ b p 0 + b p 0 / p.1 + dz b p 1 = 0 := by
  intro p hp
  have hp0 : 0 < p.1 := lt_of_le_of_lt ha hp
  set y : Space := !₂[p.1, 0, p.2] with hy_def
  have hρ : ϱ y = p.1 := by
    rw [ϱ]
    show √(p.1 ^ 2 + 0 ^ 2) = p.1
    rw [zero_pow two_ne_zero, add_zero, Real.sqrt_sq hp0.le]
  have hmer : mer y = p := by
    rw [mer, hρ]
    rfl
  have hy : y ∉ axis := by
    rw [mem_axis_iff, hρ]
    exact hp0.ne'
  have hdb : DifferentiableAt ℝ b (mer y) := by
    rw [hmer]
    exact (hb.contDiffAt ((isOpen_halfPlane' a).mem_nhds ⟨hp, trivial⟩)).differentiableAt
      one_ne_zero
  have hd := divergence_liftMer hy hdb
  rw [hmer, hρ] at hd
  rw [← hd]
  exact hdiv y (hρ ▸ hp)

namespace IsStokesData

variable {a C : ℝ} {b : ℝ × ℝ → Merid}

theorem differentiableAt (h : IsStokesData a C b) {p : ℝ × ℝ} (hp : a < p.1) :
    DifferentiableAt ℝ b p :=
  (h.smooth.contDiffAt ((isOpen_halfPlane' a).mem_nhds ⟨hp, trivial⟩)).differentiableAt
    one_ne_zero

theorem pos (h : IsStokesData a C b) {r : ℝ} (hr : a < r) : 0 < r :=
  lt_of_le_of_lt h.nonneg hr

theorem continuousOn_line (h : IsStokesData a C b) (z : ℝ) (i : Fin 2) :
    ContinuousOn (fun r => r * b (r, z) i) (Ioi a) := by
  have hc : ContinuousOn b (Ioi a ×ˢ univ) := h.smooth.continuousOn
  have hl : ContinuousOn (fun r : ℝ => (r, z)) (Ioi a) :=
    (continuous_id.prodMk continuous_const).continuousOn
  have hm : MapsTo (fun r : ℝ => (r, z)) (Ioi a) (Ioi a ×ˢ univ) := fun r hr => ⟨hr, trivial⟩
  have hb : ContinuousOn (fun r => b (r, z) i) (Ioi a) :=
    (EuclideanSpace.proj i : Merid →L[ℝ] ℝ).continuous.comp_continuousOn (hc.comp hl hm)
  exact continuousOn_id.mul hb

theorem abs_apply_le (v : Merid) (i : Fin 2) : |v i| ≤ ‖v‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le v i

theorem bound_line (h : IsStokesData a C b) {r : ℝ} (hr : a < r) (z : ℝ) (i : Fin 2) :
    |r * b (r, z) i| ≤ C * r ^ (-3 : ℝ) := by
  have hr0 := h.pos hr
  rw [abs_mul, abs_of_pos hr0]
  calc r * |b (r, z) i| ≤ r * (C * r ^ (-4 : ℝ)) :=
        mul_le_mul_of_nonneg_left ((abs_apply_le _ i).trans (h.decay (r, z) hr)) hr0.le
    _ = C * (r * r ^ (-4 : ℝ)) := by ring
    _ = C * r ^ (-3 : ℝ) := by rw [rpow_mul_self hr0]; norm_num

theorem abs_dz_le (h : IsStokesData a C b) {r : ℝ} (hr : a < r) (z : ℝ) :
    |r * dz b (r, z) 1| ≤ C * r ^ (-4 : ℝ) := by
  have hr0 := h.pos hr
  have h1 : |dz b (r, z) 1| ≤ ‖fderiv ℝ b (r, z)‖ := by
    calc |dz b (r, z) 1| ≤ ‖dz b (r, z)‖ := abs_apply_le _ 1
      _ ≤ ‖fderiv ℝ b (r, z)‖ * ‖((0 : ℝ), (1 : ℝ))‖ := (fderiv ℝ b (r, z)).le_opNorm _
      _ = ‖fderiv ℝ b (r, z)‖ := by simp
  rw [abs_mul, abs_of_pos hr0]
  calc r * |dz b (r, z) 1| ≤ r * (C * r ^ (-5 : ℝ)) :=
        mul_le_mul_of_nonneg_left (h1.trans (h.decay_deriv (r, z) hr)) hr0.le
    _ = C * (r * r ^ (-5 : ℝ)) := by ring
    _ = C * r ^ (-4 : ℝ) := by rw [rpow_mul_self hr0]; norm_num

theorem integrableOn_line (h : IsStokesData a C b) {ρ : ℝ} (hρ : a < ρ) (z : ℝ) (i : Fin 2) :
    IntegrableOn (fun r => r * b (r, z) i) (Ioi ρ) := by
  have hρ0 := h.pos hρ
  refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1)
    hρ0).const_mul C) (((h.continuousOn_line z i).mono (Ioi_subset_Ioi hρ.le)).aestronglyMeasurable
      measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  rw [Real.norm_eq_abs]
  exact h.bound_line (lt_trans hρ hr) z i

theorem measurable_dz_line (b : ℝ × ℝ → Merid) (z : ℝ) :
    Measurable fun r : ℝ => r * dz b (r, z) 1 := by
  have h1 : Measurable fun q : ℝ × ℝ => fderiv ℝ b q ((0 : ℝ), (1 : ℝ)) :=
    measurable_fderiv_apply_const ℝ b ((0 : ℝ), (1 : ℝ))
  have h2 : Measurable fun r : ℝ => fderiv ℝ b (r, z) ((0 : ℝ), (1 : ℝ)) :=
    h1.comp (measurable_id.prodMk measurable_const)
  have h3 : Measurable fun r : ℝ => (EuclideanSpace.proj (1 : Fin 2) : Merid →L[ℝ] ℝ)
      (fderiv ℝ b (r, z) ((0 : ℝ), (1 : ℝ))) :=
    (EuclideanSpace.proj (1 : Fin 2) : Merid →L[ℝ] ℝ).continuous.measurable.comp h2
  exact measurable_id.mul h3

theorem integrableOn_dz (h : IsStokesData a C b) {ρ : ℝ} (hρ : a < ρ) (z : ℝ) :
    IntegrableOn (fun r => r * dz b (r, z) 1) (Ioi ρ) := by
  have hρ0 := h.pos hρ
  refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-4 : ℝ) < -1)
    hρ0).const_mul C) (measurable_dz_line b z).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  rw [Real.norm_eq_abs]
  exact h.abs_dz_le (lt_trans hρ hr) z

theorem hasDerivAt_z (h : IsStokesData a C b) {r : ℝ} (hr : a < r) (z : ℝ) :
    HasDerivAt (fun z => r * b (r, z) 1) (r * dz b (r, z) 1) z := by
  have h1 := hasDerivAt_line_snd (h.differentiableAt (p := (r, z)) hr)
  have h2 := (EuclideanSpace.proj (1 : Fin 2) : Merid →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt z h1
  exact h2.const_mul r

theorem hasDerivAt_rho (h : IsStokesData a C b) {r : ℝ} (hr : a < r) (z : ℝ) :
    HasDerivAt (fun r => r * b (r, z) 0) (b (r, z) 0 + r * dρ b (r, z) 0) r := by
  have h1 := hasDerivAt_line_fst (h.differentiableAt (p := (r, z)) hr)
  have h2 := (EuclideanSpace.proj (0 : Fin 2) : Merid →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt r h1
  have h3 : HasDerivAt (fun r' => r' * b (r', z) 0) (1 * b (r, z) 0 + r * dρ b (r, z) 0) r :=
    (hasDerivAt_id r).mul h2
  rw [one_mul] at h3
  exact h3

/-- The divergence identity `∂_ρ(ρ X_ρ) = −ρ ∂_z X_z`. -/
theorem deriv_rho_eq (h : IsStokesData a C b) {r : ℝ} (hr : a < r) (z : ℝ) :
    b (r, z) 0 + r * dρ b (r, z) 0 = -(r * dz b (r, z) 1) := by
  have hr0 := h.pos hr
  have hd := h.div_zero (r, z) hr
  have e : r * (dρ b (r, z) 0 + b (r, z) 0 / r + dz b (r, z) 1) = 0 := by
    rw [hd, mul_zero]
  have hm : r * (b (r, z) 0 / r) = b (r, z) 0 := mul_div_cancel₀ _ hr0.ne'
  linear_combination e - hm

/-- `∫_ρ^∞ ρ' ∂_z X_z dρ' = ρ X_ρ(ρ, z)`: the divergence identity and `ρ' X_ρ → 0`. -/
theorem integral_dz (h : IsStokesData a C b) {ρ : ℝ} (hρ : a < ρ) (z : ℝ) :
    ∫ r in Ioi ρ, r * dz b (r, z) 1 = ρ * b (ρ, z) 0 := by
  have hcont : ContinuousWithinAt (fun r => r * b (r, z) 0) (Ici ρ) ρ :=
    ((h.continuousOn_line z 0).continuousAt (isOpen_Ioi.mem_nhds hρ)).continuousWithinAt
  have hderiv : ∀ x ∈ Ioi ρ, HasDerivAt (fun r => r * b (r, z) 0)
      (b (x, z) 0 + x * dρ b (x, z) 0) x := fun x hx => h.hasDerivAt_rho (lt_trans hρ hx) z
  have hint : IntegrableOn (fun r => b (r, z) 0 + r * dρ b (r, z) 0) (Ioi ρ) :=
    (h.integrableOn_dz hρ z).neg.congr_fun
      (fun r hr => (h.deriv_rho_eq (lt_trans hρ hr) z).symm) measurableSet_Ioi
  have htend : Tendsto (fun r => r * b (r, z) 0) atTop (𝓝 0) := by
    have hC : Tendsto (fun r : ℝ => C * r ^ (-(3 : ℝ))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3)).const_mul C
    refine squeeze_zero_norm' ?_ hC
    filter_upwards [eventually_gt_atTop ρ] with r hr
    rw [Real.norm_eq_abs]
    have := h.bound_line (lt_trans hρ hr) z 0
    simpa using this
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint htend
  have hcongr : ∫ r in Ioi ρ, r * dz b (r, z) 1 =
      -∫ r in Ioi ρ, (b (r, z) 0 + r * dρ b (r, z) 0) := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
    simp only [h.deriv_rho_eq (lt_trans hρ hr) z, neg_neg]
  rw [hcongr, hftc]
  ring

/-- `∂_ρ Ψ₀ = ρ X_z` (B0846). -/
theorem hasDerivAt_gauge_fst (h : IsStokesData a C b) {p : ℝ × ℝ} (hp : a < p.1) :
    HasDerivAt (fun ρ => stokesGauge b (ρ, p.2)) (p.1 * b p 1) p.1 := by
  have hd := hasDerivAt_integral_Ioi (h.continuousOn_line p.2 1)
    (fun ρ hρ => h.integrableOn_line hρ p.2 1) hp
  have := hd.neg
  simp only [neg_neg] at this
  exact this

/-- `∂_z Ψ₀ = −ρ X_ρ` (B0846): differentiation under the integral sign, dominated by
`C ρ'^{-4}`, and `integral_dz`. -/
theorem hasDerivAt_gauge_snd (h : IsStokesData a C b) {p : ℝ × ℝ} (hp : a < p.1) :
    HasDerivAt (fun z => stokesGauge b (p.1, z)) (-(p.1 * b p 0)) p.2 := by
  have hρ0 := h.pos hp
  obtain ⟨-, hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi p.1)) (F := fun z r => r * b (r, z) 1)
    (F' := fun z r => r * dz b (r, z) 1) (x₀ := p.2) (bound := fun r => C * r ^ (-4 : ℝ))
    (s := univ) Filter.univ_mem
    (Eventually.of_forall fun z => (h.integrableOn_line hp z 1).aestronglyMeasurable)
    (h.integrableOn_line hp p.2 1) (measurable_dz_line b p.2).aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr z _
      rw [Real.norm_eq_abs]
      exact h.abs_dz_le (lt_trans hp hr) z)
    ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-4 : ℝ) < -1) hρ0).const_mul C)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr z _
      exact h.hasDerivAt_z (lt_trans hp hr) z)
  have := hd.neg
  rw [h.integral_dz hp p.2] at this
  exact this

theorem toSpanSingleton_eq (c : ℝ) :
    ContinuousLinearMap.toSpanSingleton ℝ c = c • ContinuousLinearMap.id ℝ ℝ := by
  ext
  simp

/-- `Ψ₀` is strictly differentiable on `{ρ > a}`, with
`DΨ₀(ρ, z) = (ρ X_z, −ρ X_ρ)` (continuous partial derivatives). -/
theorem hasStrictFDerivAt_stokesGauge (h : IsStokesData a C b) {u : ℝ × ℝ} (hu : a < u.1) :
    HasStrictFDerivAt (stokesGauge b)
      (((u.1 * b u 1) • ContinuousLinearMap.id ℝ ℝ).coprod
        ((-(u.1 * b u 0)) • ContinuousLinearMap.id ℝ ℝ)) u := by
  have hev : ∀ᶠ v in 𝓝 u, a < v.1 :=
    (continuous_fst.isOpen_preimage _ isOpen_Ioi).mem_nhds hu
  have hbc : ContinuousAt b u := (h.differentiableAt hu).continuousAt
  have h1 : ContinuousAt (fun v : ℝ × ℝ => (v.1 * b v 1) • ContinuousLinearMap.id ℝ ℝ) u := by
    have : ContinuousAt (fun v : ℝ × ℝ => v.1 * b v 1) u :=
      continuous_fst.continuousAt.mul
        ((EuclideanSpace.proj (1 : Fin 2) : Merid →L[ℝ] ℝ).continuous.continuousAt.comp hbc)
    exact this.smul continuousAt_const
  have h2 : ContinuousAt (fun v : ℝ × ℝ => (-(v.1 * b v 0)) • ContinuousLinearMap.id ℝ ℝ) u := by
    have : ContinuousAt (fun v : ℝ × ℝ => -(v.1 * b v 0)) u :=
      (continuous_fst.continuousAt.mul
        ((EuclideanSpace.proj (0 : Fin 2) : Merid →L[ℝ] ℝ).continuous.continuousAt.comp hbc)).neg
    exact this.smul continuousAt_const
  have key := hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (u := u)
    (f := fun ρ z => stokesGauge b (ρ, z))
    (f₁ := fun ρ z => (ρ * b (ρ, z) 1) • ContinuousLinearMap.id ℝ ℝ)
    (f₂ := fun ρ z => (-(ρ * b (ρ, z) 0)) • ContinuousLinearMap.id ℝ ℝ)
    (by
      filter_upwards [hev] with v hv
      have := (h.hasDerivAt_gauge_fst hv).hasFDerivAt
      rw [toSpanSingleton_eq] at this
      exact this)
    (by
      filter_upwards [hev] with v hv
      have := (h.hasDerivAt_gauge_snd hv).hasFDerivAt
      rw [toSpanSingleton_eq] at this
      exact this)
    h1 h2
  exact key

theorem dρ_stokesGauge (h : IsStokesData a C b) {p : ℝ × ℝ} (hp : a < p.1) :
    dρ (stokesGauge b) p = p.1 * b p 1 := by
  rw [dρ, (h.hasStrictFDerivAt_stokesGauge hp).hasFDerivAt.fderiv]
  simp

theorem dz_stokesGauge (h : IsStokesData a C b) {p : ℝ × ℝ} (hp : a < p.1) :
    dz (stokesGauge b) p = -(p.1 * b p 0) := by
  rw [dz, (h.hasStrictFDerivAt_stokesGauge hp).hasFDerivAt.fderiv]
  simp

theorem streamProfile_stokesGauge (h : IsStokesData a C b) {p : ℝ × ℝ} (hp : a < p.1) :
    streamProfile (stokesGauge b) p = b p := by
  have hp0 : p.1 ≠ 0 := (h.pos hp).ne'
  rw [streamProfile, h.dz_stokesGauge hp, h.dρ_stokesGauge hp]
  ext i
  fin_cases i <;> simp [m0, m1, hp0]

/-- **AX06 `stokesGauge`** (B0846, tex 12510–12515). A `C¹` solenoidal meridional field
`X = liftMer b` with `|X| ≤ Cρ^{-4}`, `|DX| ≤ Cρ^{-5}` on `{ρ > a}` is the stream lift of its
gauge `Ψ₀(ρ, z) = −∫_ρ^∞ ρ' X_z(ρ', z) dρ'` there: `X_z = ρ⁻¹ ∂_ρ Ψ₀`, `X_ρ = −ρ⁻¹ ∂_z Ψ₀`. -/
theorem streamLift_stokesGauge (h : IsStokesData a C b) {y : Space} (hy : a < ϱ y) :
    streamLift (stokesGauge b) y = liftMer b y := by
  rw [streamLift, liftMer_eq_frameL, liftMer_eq_frameL,
    h.streamProfile_stokesGauge (p := mer y) hy]

/-- **The primitive bound** `eq:affine-4-99d` at `j = 0` (tex 12517–12520):
`|Ψ₀(ρ, z)| ≤ (C/2) ρ^{-2}`. -/
theorem abs_stokesGauge_le (h : IsStokesData a C b) {p : ℝ × ℝ} (hp : a < p.1) :
    |stokesGauge b p| ≤ C / 2 * p.1 ^ (-2 : ℝ) := by
  have hρ0 := h.pos hp
  have hI : IntegrableOn (fun r : ℝ => C * r ^ (-3 : ℝ)) (Ioi p.1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hρ0).const_mul C
  rw [stokesGauge, abs_neg]
  calc |∫ r in Ioi p.1, r * b (r, p.2) 1| ≤ ∫ r in Ioi p.1, C * r ^ (-3 : ℝ) := by
        rw [← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le hI ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        rw [Real.norm_eq_abs]
        exact h.bound_line (lt_trans hp hr) p.2 1
    _ = C / 2 * p.1 ^ (-2 : ℝ) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hρ0]
        have e : (-3 : ℝ) + 1 = -2 := by norm_num
        rw [e]
        ring

/-- The primitive bound `eq:affine-4-99d` at `j = 1` for the radial derivative:
`|∂_ρ Ψ₀| = ρ |X_z| ≤ C ρ^{-3}`. -/
theorem abs_dρ_stokesGauge_le (h : IsStokesData a C b) {p : ℝ × ℝ} (hp : a < p.1) :
    |dρ (stokesGauge b) p| ≤ C * p.1 ^ (-3 : ℝ) := by
  rw [h.dρ_stokesGauge hp]
  exact h.bound_line hp p.2 1

/-- The primitive bound `eq:affine-4-99d` at `j = 1` for the axial derivative:
`|∂_z Ψ₀| = ρ |X_ρ| ≤ C ρ^{-3}`. -/
theorem abs_dz_stokesGauge_le (h : IsStokesData a C b) {p : ℝ × ℝ} (hp : a < p.1) :
    |dz (stokesGauge b) p| ≤ C * p.1 ^ (-3 : ℝ) := by
  rw [h.dz_stokesGauge hp, abs_neg]
  exact h.bound_line hp p.2 0

end IsStokesData

end UnforcedLeray.Axi
