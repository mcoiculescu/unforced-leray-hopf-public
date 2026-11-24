import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.MeanShift.Dilation

/-!
# The shifted dilation identity of the uncut Newton fields (source 4776-4782, 5383-5387)

`(-½ x·∇ + μ + ½)(V_μ - V_{μ+1}) = V_μ` off the old disc.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- One exponent: `x·∇V_p` and `V_p` in terms of the moments of `φ(t) = G(t,x)`. -/
theorem newtonV_moments {c ν p : ℝ} {χo : ℝ → ℝ} {M : Chart → Mat3} (hc : 0 < c) (hν : 0 < ν)
    (hp : 0 < p) (hχ : IsOutwardCutoff χo) (hM : OldThinFinite c ν M) (i : Fin 3) {x : Vec3}
    (hx : 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2) :
    newtonV c ν p χo M x i = -2 * ∫ t in Ioc (0 : ℝ) 1, t ^ (2 * p + 2) * Gint c ν χo M t i x ∧
    fderiv ℝ (newtonV c ν p χo M) x x i =
      -2 * ((2 * p + 2 - 3) * (∫ t in Ioc (0 : ℝ) 1, t ^ (2 * p + 2) * Gint c ν χo M t i x)
        - Gint c ν χo M 1 i x) := by
  refine ⟨by rw [newtonV_apply]; rfl, ?_⟩
  obtain ⟨B, hB⟩ := Gint_bound hc hν hχ hM i hx
  obtain ⟨hcont, hder⟩ := Gint_dilation_data hc hν hχ hM i hx
  have hq : 0 < 2 * p + 2 := by linarith
  have hfd : ∀ t ∈ Ioc (0 : ℝ) 1, fderiv ℝ (newtonFam c ν p χo M i t) x x =
      t ^ (2 * p + 2) * fderiv ℝ (Gint c ν χo M t i) x x := by
    intro t ht
    rw [newtonFam_eq_Gint]
    rw [fderiv_const_mul (Gint_differentiableAt hc hν hχ hM ht i hx)]
    simp
  have hint : IntegrableOn (fun t : ℝ => t ^ (2 * p + 2) * fderiv ℝ (Gint c ν χo M t i) x x)
      (Ioc (0 : ℝ) 1) := by
    exact IntegrableOn.congr_fun (newtonFam_fderiv_integrable hc hν hp hχ hM i hx x)
      (fun t ht => hfd t ht) measurableSet_Ioc
  have hibp := ibp_pow_dilation (φ := fun t => Gint c ν χo M t i x)
    (Θ := fun t => fderiv ℝ (Gint c ν χo M t i) x x) hq hB hcont hder hint
  rw [fderiv_newtonV_apply hc hν hp hχ hM hx x i]
  have : ∫ t in Ioc (0 : ℝ) 1, fderiv ℝ (newtonFam c ν p χo M i t) x x =
      ∫ t in Ioc (0 : ℝ) 1, t ^ (2 * p + 2) * fderiv ℝ (Gint c ν χo M t i) x x :=
    setIntegral_congr_fun measurableSet_Ioc hfd
  rw [this, hibp]

/-- **The shifted dilation identity** (component form, source 5383-5387). -/
theorem newtonV_shift_component {c ν μ : ℝ} {χo : ℝ → ℝ} {M : Chart → Mat3} (hc : 0 < c)
    (hν : 0 < ν) (hμ : 0 < μ) (hχ : IsOutwardCutoff χo) (hM : OldThinFinite c ν M) (i : Fin 3)
    {x : Vec3} (hx : 5 * ν / 6 < x 0 ^ 2 + x 1 ^ 2) :
    -(1 / 2 : ℝ) * (fderiv ℝ (newtonV c ν μ χo M) x x i - fderiv ℝ (newtonV c ν (μ + 1) χo M) x x i) +
      (μ + 1 / 2) * (newtonV c ν μ χo M x i - newtonV c ν (μ + 1) χo M x i) =
      newtonV c ν μ χo M x i := by
  obtain ⟨h1, h2⟩ := newtonV_moments (p := μ) hc hν hμ hχ hM i hx
  obtain ⟨h3, h4⟩ := newtonV_moments (p := μ + 1) hc hν (by linarith) hχ hM i hx
  rw [h1, h2, h3, h4]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
