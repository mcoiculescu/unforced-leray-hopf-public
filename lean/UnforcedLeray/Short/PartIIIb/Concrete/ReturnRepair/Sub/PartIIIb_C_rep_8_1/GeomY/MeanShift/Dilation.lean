import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.MeanShift.Scale
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.MeanShift.Ibp

/-!
# The dilation identity for the inner integral and the Newton field (source 4776-4782, 5383-5387)

`t φ'(t) = -4 φ(t) - Θ(t)` for `φ(t) = G(t,x)`, `Θ(t) = x·∇_x G(t,x)`, with `φ` bounded and
continuous on `(0,1]`; then `ibp_pow_dilation` gives the shifted dilation identity
`(-½ x·∇ + μ + ½)(V_μ - V_{μ+1}) = V_μ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem Gint_bound {c ν : ℝ} {χo : ℝ → ℝ} {M : Chart → Mat3} (hc : 0 < c) (hν : 0 < ν)
    (hχ : IsOutwardCutoff χo) (hM : OldThinFinite c ν M) (i : Fin 3) {x : Vec3}
    (hx : 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2) :
    ∃ B : ℝ, ∀ t ∈ Ioc (0 : ℝ) 1, |Gint c ν χo M t i x| ≤ B := by
  obtain ⟨s, hs, hsU, C, hC⟩ := NewtonFam.locDom_unif c ν χo M hν hχ i 0 x hx
  have hint := NewtonFam.sigma_norm_sum_integrable c ν χo M hc hν hχ hM
  refine ⟨∫ a : ℝ × ℝ, (∑ j : Fin 3, ∑ k : Fin 3, ‖sigmaM c ν χo M a j k‖) * C, ?_⟩
  intro t ht
  have h := norm_integral_le_of_norm_le (hint.mul_const C)
    (Filter.Eventually.of_forall fun a => by
      have := hC t ht a x (mem_of_mem_nhds hs)
      rwa [norm_iteratedFDeriv_zero] at this)
  rw [Real.norm_eq_abs] at h
  exact h

theorem Gint_dilation_data {c ν : ℝ} {χo : ℝ → ℝ} {M : Chart → Mat3} (hc : 0 < c) (hν : 0 < ν)
    (hχ : IsOutwardCutoff χo) (hM : OldThinFinite c ν M) (i : Fin 3) {x : Vec3}
    (hx : 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2) :
    ContinuousOn (fun t : ℝ => Gint c ν χo M t i x) (Ioc (0 : ℝ) 1) ∧
    ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun s : ℝ => Gint c ν χo M s i x)
      (-(4 * Gint c ν χo M t i x + fderiv ℝ (Gint c ν χo M t i) x x) / t) t := by
  set G₁ : Vec3 → ℝ := Gint c ν χo M 1 i with hG₁def
  have hone : (1 : ℝ) ∈ Ioc (0 : ℝ) 1 := ⟨one_pos, le_rfl⟩
  have hG₁d : ∀ z : Vec3, 5 * ν / 6 < z 0 ^ 2 + z 1 ^ 2 → DifferentiableAt ℝ G₁ z :=
    fun z hz => Gint_differentiableAt hc hν hχ hM hone i hz
  -- the model function `ψ`
  have hψ : ∀ t ∈ Ioc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => (s ^ 4)⁻¹ * G₁ (s⁻¹ • x))
      ((-(4 * t ^ 3) / (t ^ 4) ^ 2) * G₁ (t⁻¹ • x) +
        (t ^ 4)⁻¹ * fderiv ℝ G₁ (t⁻¹ • x) ((-(t ^ 2)⁻¹) • x)) t := by
    intro t ht
    have htne : t ≠ 0 := ht.1.ne'
    have h1 : HasDerivAt (fun s : ℝ => (s ^ 4)⁻¹) (-(4 * t ^ 3) / (t ^ 4) ^ 2) t := by
      exact ((hasDerivAt_pow 4 t).inv (pow_ne_zero 4 htne)).congr_deriv (by norm_num)
    have h2 : HasDerivAt (fun s : ℝ => s⁻¹ • x) ((-(t ^ 2)⁻¹) • x) t :=
      (hasDerivAt_inv htne).smul_const x
    have h3 : HasFDerivAt G₁ (fderiv ℝ G₁ (t⁻¹ • x)) (t⁻¹ • x) :=
      (hG₁d _ (cyl_smul_gt hν ht hx)).hasFDerivAt
    have h4 : HasDerivAt (fun s : ℝ => G₁ (s⁻¹ • x))
        (fderiv ℝ G₁ (t⁻¹ • x) ((-(t ^ 2)⁻¹) • x)) t := HasFDerivAt.comp_hasDerivAt (l := G₁) (f := fun s : ℝ => s⁻¹ • x) t h3 h2
    exact h1.mul h4
  have hψc : ContinuousOn (fun s : ℝ => (s ^ 4)⁻¹ * G₁ (s⁻¹ • x)) (Ioc (0 : ℝ) 1) :=
    fun t ht => (hψ t ht).continuousAt.continuousWithinAt
  -- the identification with `φ`
  have hφψ : ∀ t ∈ Ioc (0 : ℝ) 1, Gint c ν χo M t i x = (t ^ 4)⁻¹ * G₁ (t⁻¹ • x) :=
    fun t ht => Gint_scale hν hχ ht i hx
  refine ⟨hψc.congr hφψ, ?_⟩
  intro t ht
  have htI : t ∈ Ioc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
  have htne : t ≠ 0 := ht.1.ne'
  -- `Θ t` through the scaling
  have hTheta : fderiv ℝ (Gint c ν χo M t i) x x = (t ^ 4)⁻¹ * (t⁻¹ * fderiv ℝ G₁ (t⁻¹ • x) x) := by
    have hev : Gint c ν χo M t i =ᶠ[𝓝 x] fun y : Vec3 => (t ^ 4)⁻¹ * G₁ (t⁻¹ • y) := by
      filter_upwards [(isOpen_newtonRegion ν).mem_nhds hx] with y hy
      exact Gint_scale hν hχ htI i hy
    rw [hev.fderiv_eq]
    have h3 : HasFDerivAt G₁ (fderiv ℝ G₁ (t⁻¹ • x)) (t⁻¹ • x) :=
      (hG₁d _ (cyl_smul_gt hν htI hx)).hasFDerivAt
    have h4 : HasFDerivAt (fun y : Vec3 => G₁ (t⁻¹ • y))
        ((fderiv ℝ G₁ (t⁻¹ • x)).comp (t⁻¹ • ContinuousLinearMap.id ℝ Vec3)) x :=
      h3.comp x ((hasFDerivAt_id x).const_smul t⁻¹)
    rw [(h4.const_mul ((t ^ 4)⁻¹)).fderiv]
    simp
  have hev2 : (fun s : ℝ => Gint c ν χo M s i x) =ᶠ[𝓝 t] fun s : ℝ => (s ^ 4)⁻¹ * G₁ (s⁻¹ • x) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact hφψ s ⟨hs.1, hs.2.le⟩
  refine ((hψ t htI).congr_of_eventuallyEq hev2).congr_deriv ?_
  rw [hTheta, hφψ t htI, map_smul, smul_eq_mul]
  field_simp
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
