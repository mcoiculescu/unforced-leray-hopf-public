import UnforcedLeray.Short.PartIIb.Sub.T12_6
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.FlatHeatContraction

/-!
# Part II-b, leaf `PartII-b:T12/6/9` (`DsolHeatAdjoint`): the planar heat flow is self-adjoint

Source of record: `the November 2 reference manuscript`, line 1924 (the heat flow
commutes with the divergence). The statement is `DsolHeatAdjoint` of `Sub/T12_6.lean`.

Proof outline.
* Kernel bound: `K_θ(w) ≤ (4πθ)⁻¹ e^{T/(4θ)} e^{-|y|²/(8θ)}` whenever `|y|²/2 - T ≤ |w|²`.
  Two instances: `y = z - w` (for the convergence of `flatHeat`), and `y` arbitrary with
  `|y + w|² ≤ S` on the support of `ρ` (for the Fubini bound).
* With `G(y, w) = K_θ(w) g(y)_i ρ(y + w)` on `ℝ² × ℝ²`, `G` is integrable (shear `(y,w) ↦ (y, y+w)`
  and `Integrable.mul_prod`). The shear `(z, w) ↦ (z - w, w)` preserves the product measure and
  turns `(z, w) ↦ K_θ(w) g(z - w)_i ρ(z)` into `G`.
* Fubini (`integral_prod`) and the change of variables give both integrability claims and the
  identity; the inner `w`-integral of `G` is `g(y)_i (K_θ * ρ)(y)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

/-! ## Elementary inequalities -/

lemma dsolHA_sq_le (a b : ℝ × ℝ) :
    (a.1 ^ 2 + a.2 ^ 2) / 2 - (b.1 ^ 2 + b.2 ^ 2) ≤ (a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2 := by
  nlinarith [sq_nonneg (a.1 - 2 * b.1), sq_nonneg (a.2 - 2 * b.2)]

/-! ## Gaussian-weighted fields (copies of the `GaussExtend` helpers) -/

lemma dsolHA_gauss_aesm {g : ℝ × ℝ → CMerid} (hg : DsolGaussInt g) :
    AEStronglyMeasurable g volume := by
  have h1 := (hg 1 one_pos).aestronglyMeasurable
  have hc : Continuous (fun y : ℝ × ℝ => Real.exp (-(-1 : ℝ) * (y.1 ^ 2 + y.2 ^ 2))) := by
    fun_prop
  have hsm : ∀ (c d : ℝ) (v : CMerid), c • d • v = (c * d) • v := fun c d v => smul_smul c d v
  have hone : ∀ v : CMerid, (1 : ℝ) • v = v := fun v => one_smul ℝ v
  refine (hc.aestronglyMeasurable.smul h1).congr (ae_of_all _ fun y => ?_)
  have h0 : Real.exp (-(-1 : ℝ) * (y.1 ^ 2 + y.2 ^ 2)) * Real.exp (-1 * (y.1 ^ 2 + y.2 ^ 2)) = 1 := by
    rw [← Real.exp_add, show -(-1 : ℝ) * (y.1 ^ 2 + y.2 ^ 2) + -1 * (y.1 ^ 2 + y.2 ^ 2) = 0 by ring,
      Real.exp_zero]
  show Real.exp (-(-1 : ℝ) * (y.1 ^ 2 + y.2 ^ 2)) • (Real.exp (-1 * (y.1 ^ 2 + y.2 ^ 2)) • g y) = g y
  rw [hsm, h0, hone]

lemma dsolHA_gauss_norm_integrable {g : ℝ × ℝ → CMerid} (hg : DsolGaussInt g) {a : ℝ} (ha : 0 < a) :
    Integrable (fun y : ℝ × ℝ => Real.exp (-a * (y.1 ^ 2 + y.2 ^ 2)) * ‖g y‖) := by
  refine (hg a ha).norm.congr (ae_of_all _ fun y => ?_)
  dsimp only
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-! ## The kernel bounds -/

lemma dsolHA_kernel_nonneg {θ : ℝ} (hθ : 0 < θ) (w : ℝ × ℝ) : 0 ≤ flatHeatKernel θ w := by
  unfold flatHeatKernel
  positivity

lemma dsolHA_kernel_continuous (θ : ℝ) : Continuous (flatHeatKernel θ) := by
  unfold flatHeatKernel
  fun_prop

/-- Kernel bound: if `|y|²/2 - T ≤ |w|²` then `K_θ(w) ≤ (4πθ)⁻¹ e^{T/(4θ)} e^{-|y|²/(8θ)}`. -/
lemma dsolHA_kernel_le {θ : ℝ} (hθ : 0 < θ) (y w : ℝ × ℝ) (T : ℝ)
    (hT : (y.1 ^ 2 + y.2 ^ 2) / 2 - T ≤ w.1 ^ 2 + w.2 ^ 2) :
    flatHeatKernel θ w ≤
      (4 * Real.pi * θ)⁻¹ * Real.exp (T / (4 * θ)) * Real.exp (-(8 * θ)⁻¹ * (y.1 ^ 2 + y.2 ^ 2)) := by
  have hθ0 : θ ≠ 0 := hθ.ne'
  have h4 : (0 : ℝ) < 4 * θ := by positivity
  have hexp : -(w.1 ^ 2 + w.2 ^ 2) / (4 * θ) ≤ T / (4 * θ) + -(8 * θ)⁻¹ * (y.1 ^ 2 + y.2 ^ 2) := by
    have h1 : -(w.1 ^ 2 + w.2 ^ 2) / (4 * θ) ≤ (T - (y.1 ^ 2 + y.2 ^ 2) / 2) / (4 * θ) :=
      div_le_div_of_nonneg_right (by linarith) h4.le
    have e : (T - (y.1 ^ 2 + y.2 ^ 2) / 2) / (4 * θ) =
        T / (4 * θ) + -(8 * θ)⁻¹ * (y.1 ^ 2 + y.2 ^ 2) := by
      field_simp
      ring
    linarith
  calc flatHeatKernel θ w
      = (4 * Real.pi * θ)⁻¹ * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / (4 * θ)) := rfl
    _ ≤ (4 * Real.pi * θ)⁻¹ * Real.exp (T / (4 * θ) + -(8 * θ)⁻¹ * (y.1 ^ 2 + y.2 ^ 2)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)
    _ = (4 * Real.pi * θ)⁻¹ * Real.exp (T / (4 * θ)) * Real.exp (-(8 * θ)⁻¹ * (y.1 ^ 2 + y.2 ^ 2)) := by
        rw [Real.exp_add]
        ring

/-- The bound on the support of `ρ`: with `‖y + w‖² ≤ S` where `ρ(y + w) ≠ 0`. -/
lemma dsolHA_abs_le {θ : ℝ} (hθ : 0 < θ) {ρ : ℝ × ℝ → ℝ} {S : ℝ}
    (hS : ∀ z, ρ z ≠ 0 → z.1 ^ 2 + z.2 ^ 2 ≤ S) (y w : ℝ × ℝ) :
    flatHeatKernel θ w * ‖ρ (y + w)‖ ≤
      (4 * Real.pi * θ)⁻¹ * Real.exp (S / (4 * θ)) * Real.exp (-(8 * θ)⁻¹ * (y.1 ^ 2 + y.2 ^ 2)) *
        ‖ρ (y + w)‖ := by
  by_cases h0 : ρ (y + w) = 0
  · simp [h0]
  · have hu := hS (y + w) h0
    have hT : (y.1 ^ 2 + y.2 ^ 2) / 2 - S ≤ w.1 ^ 2 + w.2 ^ 2 := by
      have h1 := dsolHA_sq_le y (y + w)
      simp only [Prod.fst_add, Prod.snd_add] at h1 hu
      nlinarith [h1, hu]
    have hK := dsolHA_kernel_le hθ y w S hT
    exact mul_le_mul_of_nonneg_right hK (norm_nonneg _)

/-- For fixed `z`, `w ↦ K_θ(w) g(z - w)` is Bochner integrable (`DsolGaussInt g`). -/
lemma dsolHA_integrable_kernel {θ : ℝ} (hθ : 0 < θ) {g : ℝ × ℝ → CMerid} (hg : DsolGaussInt g)
    (z : ℝ × ℝ) : Integrable (fun w : ℝ × ℝ => flatHeatKernel θ w • g (z - w)) := by
  have hf : Integrable (fun y : ℝ × ℝ => Real.exp (-(8 * θ)⁻¹ * (y.1 ^ 2 + y.2 ^ 2)) * ‖g y‖) :=
    dsolHA_gauss_norm_integrable hg (by positivity)
  have hbound := (hf.comp_sub_left z).const_mul
    ((4 * Real.pi * θ)⁻¹ * Real.exp ((z.1 ^ 2 + z.2 ^ 2) / (4 * θ)))
  have hgm : AEStronglyMeasurable (fun w : ℝ × ℝ => g (z - w)) volume :=
    (dsolHA_gauss_aesm hg).comp_quasiMeasurePreserving
      (Measure.measurePreserving_sub_left volume z).quasiMeasurePreserving
  refine Integrable.mono' hbound
    ((dsolHA_kernel_continuous θ).aestronglyMeasurable.smul hgm) (ae_of_all _ fun w => ?_)
  rw [norm_smul, Real.norm_of_nonneg (dsolHA_kernel_nonneg hθ w)]
  have hsq := dsolHA_sq_le (z - w) z
  simp only [Prod.fst_sub, Prod.snd_sub] at hsq
  have hk := dsolHA_kernel_le hθ (z - w) w (z.1 ^ 2 + z.2 ^ 2)
    (by simp only [Prod.fst_sub, Prod.snd_sub]; nlinarith [hsq])
  calc flatHeatKernel θ w * ‖g (z - w)‖
      ≤ (4 * Real.pi * θ)⁻¹ * Real.exp ((z.1 ^ 2 + z.2 ^ 2) / (4 * θ)) *
          Real.exp (-(8 * θ)⁻¹ * ((z - w).1 ^ 2 + (z - w).2 ^ 2)) * ‖g (z - w)‖ :=
        mul_le_mul_of_nonneg_right hk (norm_nonneg _)
    _ = (4 * Real.pi * θ)⁻¹ * Real.exp ((z.1 ^ 2 + z.2 ^ 2) / (4 * θ)) *
          (Real.exp (-(8 * θ)⁻¹ * ((z - w).1 ^ 2 + (z - w).2 ^ 2)) * ‖g (z - w)‖) := by ring

/-! ## The component of the heat flow -/

lemma dsolHA_flatHeat_comp {θ : ℝ} (hθ : 0 < θ) {g : ℝ × ℝ → CMerid} (hg : DsolGaussInt g)
    (z : ℝ × ℝ) (i : Fin 2) :
    flatHeat θ g z i = ∫ w : ℝ × ℝ, ((flatHeatKernel θ w : ℝ) : ℂ) * g (z - w) i := by
  have h := ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj i : CMerid →L[ℂ] ℂ)
    (dsolHA_integrable_kernel hθ hg z)
  unfold flatHeat
  rw [show (∫ w : ℝ × ℝ, flatHeatKernel θ w • g (z - w)) i =
      (EuclideanSpace.proj i : CMerid →L[ℂ] ℂ) (∫ w : ℝ × ℝ, flatHeatKernel θ w • g (z - w)) from rfl,
    ← h]
  congr 1

/-! ## The integrand on the product and the shear -/

/-- The integrand `(y, w) ↦ K_θ(w) g(y)_i ρ(y + w)`. -/
def dsolHAG (θ : ℝ) (g : ℝ × ℝ → CMerid) (ρ : ℝ × ℝ → ℝ) (i : Fin 2)
    (p : (ℝ × ℝ) × (ℝ × ℝ)) : ℂ :=
  ((flatHeatKernel θ p.2 : ℝ) : ℂ) * g p.1 i * ((ρ (p.1 + p.2) : ℝ) : ℂ)

/-- The shear `(z, w) ↦ (z - w, w)` as a measurable equivalence of the product. -/
def dsolHAshear : ((ℝ × ℝ) × (ℝ × ℝ)) ≃ᵐ ((ℝ × ℝ) × (ℝ × ℝ)) where
  toFun p := (p.1 - p.2, p.2)
  invFun q := (q.1 + q.2, q.2)
  left_inv p := by simp
  right_inv q := by simp
  measurable_toFun := (measurable_fst.sub measurable_snd).prodMk measurable_snd
  measurable_invFun := (measurable_fst.add measurable_snd).prodMk measurable_snd

/-! ## The target -/

/-- **Leaf `PartII-b:T12/6/9`** (SP 1924): the planar heat flow is self-adjoint against a
compactly supported continuous test. -/
theorem dsolHeatAdjoint : DsolHeatAdjoint := by
  intro θ g ρ i hθ hg hρc hρcs
  obtain ⟨S, hS⟩ : ∃ S : ℝ, ∀ z, ρ z ≠ 0 → z.1 ^ 2 + z.2 ^ 2 ≤ S := by
    obtain ⟨B, hB⟩ := hρcs.isCompact.isBounded.subset_closedBall (0 : ℝ × ℝ)
    refine ⟨2 * B ^ 2, fun z hz => ?_⟩
    have hzB : ‖z‖ ≤ B := by
      have hmem := hB (subset_tsupport ρ (Function.mem_support.mpr hz))
      simpa [Metric.mem_closedBall, dist_zero_right] using hmem
    have h1 : |z.1| ≤ B := by
      have := norm_fst_le z
      rw [Real.norm_eq_abs] at this
      exact this.trans hzB
    have h2 : |z.2| ≤ B := by
      have := norm_snd_le z
      rw [Real.norm_eq_abs] at this
      exact this.trans hzB
    rw [← sq_abs z.1, ← sq_abs z.2]
    nlinarith [abs_nonneg z.1, abs_nonneg z.2,
      mul_le_mul h1 h1 (abs_nonneg _) (le_trans (abs_nonneg _) h1),
      mul_le_mul h2 h2 (abs_nonneg _) (le_trans (abs_nonneg _) h2)]
  have hK0 : ∀ w, 0 ≤ flatHeatKernel θ w := dsolHA_kernel_nonneg hθ
  have hKc : Continuous (flatHeatKernel θ) := dsolHA_kernel_continuous θ
  have ha : (0 : ℝ) < (8 * θ)⁻¹ := by positivity
  have hf := dsolHA_gauss_norm_integrable hg ha
  have hρint : Integrable (fun u : ℝ × ℝ => ‖ρ u‖) :=
    (hρc.integrable_of_hasCompactSupport hρcs).norm
  have hgm := dsolHA_gauss_aesm hg
  -- pointwise bound for the integrand on the product
  have hGbound : ∀ p : (ℝ × ℝ) × (ℝ × ℝ),
      ‖dsolHAG θ g ρ i p‖ ≤ ((4 * Real.pi * θ)⁻¹ * Real.exp (S / (4 * θ))) *
        ((Real.exp (-(8 * θ)⁻¹ * (p.1.1 ^ 2 + p.1.2 ^ 2)) * ‖g p.1‖) * ‖ρ (p.1 + p.2)‖) := by
    intro p
    have hkey := dsolHA_abs_le hθ hS p.1 p.2
    have hgi : ‖g p.1 i‖ ≤ ‖g p.1‖ := PiLp.norm_apply_le (g p.1) i
    unfold dsolHAG
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (hK0 _)]
    calc flatHeatKernel θ p.2 * ‖g p.1 i‖ * ‖ρ (p.1 + p.2)‖
        ≤ flatHeatKernel θ p.2 * ‖g p.1‖ * ‖ρ (p.1 + p.2)‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgi (hK0 _)) (norm_nonneg _)
      _ = (flatHeatKernel θ p.2 * ‖ρ (p.1 + p.2)‖) * ‖g p.1‖ := by ring
      _ ≤ ((4 * Real.pi * θ)⁻¹ * Real.exp (S / (4 * θ)) *
            Real.exp (-(8 * θ)⁻¹ * (p.1.1 ^ 2 + p.1.2 ^ 2)) * ‖ρ (p.1 + p.2)‖) * ‖g p.1‖ :=
          mul_le_mul_of_nonneg_right hkey (norm_nonneg _)
      _ = _ := by ring
  have hGaesm : AEStronglyMeasurable (dsolHAG θ g ρ i)
      ((volume : Measure (ℝ × ℝ)).prod volume) := by
    unfold dsolHAG
    refine AEStronglyMeasurable.mul (AEStronglyMeasurable.mul ?_ ?_) ?_
    · exact (Complex.continuous_ofReal.comp (hKc.comp continuous_snd)).aestronglyMeasurable
    · exact ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_aestronglyMeasurable hgm.comp_fst)
    · exact (Complex.continuous_ofReal.comp
        (hρc.comp (continuous_fst.add continuous_snd))).aestronglyMeasurable
  have hGint : Integrable (dsolHAG θ g ρ i) ((volume : Measure (ℝ × ℝ)).prod volume) := by
    have hQ : Integrable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
        (Real.exp (-(8 * θ)⁻¹ * (q.1.1 ^ 2 + q.1.2 ^ 2)) * ‖g q.1‖) * ‖ρ q.2‖) :=
      hf.mul_prod hρint
    have hM : MeasurePreserving (fun p : (ℝ × ℝ) × (ℝ × ℝ) => (p.1, p.1 + p.2))
        ((volume : Measure (ℝ × ℝ)).prod volume) ((volume : Measure (ℝ × ℝ)).prod volume) :=
      measurePreserving_prod_add volume volume
    have hB : Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
        (Real.exp (-(8 * θ)⁻¹ * (p.1.1 ^ 2 + p.1.2 ^ 2)) * ‖g p.1‖) * ‖ρ (p.1 + p.2)‖)
        ((volume : Measure (ℝ × ℝ)).prod volume) :=
      hM.integrable_comp_of_integrable hQ
    exact Integrable.mono' (hB.const_mul ((4 * Real.pi * θ)⁻¹ * Real.exp (S / (4 * θ))))
      hGaesm (ae_of_all _ hGbound)
  have hsh : MeasurePreserving dsolHAshear ((volume : Measure (ℝ × ℝ)).prod volume)
      ((volume : Measure (ℝ × ℝ)).prod volume) :=
    measurePreserving_sub_prod volume volume
  have hFint : Integrable (fun p => dsolHAG θ g ρ i (dsolHAshear p))
      ((volume : Measure (ℝ × ℝ)).prod volume) :=
    hsh.integrable_comp_of_integrable hGint
  -- the pointwise identities
  have hFpt : ∀ z w : ℝ × ℝ, dsolHAG θ g ρ i (dsolHAshear (z, w)) =
      ((flatHeatKernel θ w : ℝ) : ℂ) * g (z - w) i * ((ρ z : ℝ) : ℂ) := by
    intro z w
    show ((flatHeatKernel θ w : ℝ) : ℂ) * g (z - w) i * ((ρ (z - w + w) : ℝ) : ℂ) = _
    rw [sub_add_cancel]
  have hLHS : ∀ z : ℝ × ℝ, ∫ w, dsolHAG θ g ρ i (dsolHAshear (z, w)) =
      flatHeat θ g z i * ((ρ z : ℝ) : ℂ) := by
    intro z
    simp_rw [hFpt]
    rw [integral_mul_const, dsolHA_flatHeat_comp hθ hg z i]
  have hWy : ∀ y : ℝ × ℝ, ∫ w, dsolHAG θ g ρ i (y, w) =
      g y i * ((dsolHeatConv θ ρ y : ℝ) : ℂ) := by
    intro y
    have e1 : ∀ w : ℝ × ℝ, dsolHAG θ g ρ i (y, w) =
        g y i * ((flatHeatKernel θ w * ρ (y + w) : ℝ) : ℂ) := by
      intro w
      show ((flatHeatKernel θ w : ℝ) : ℂ) * g y i * ((ρ (y + w) : ℝ) : ℂ) = _
      push_cast
      ring
    simp_rw [e1]
    have hc : ∫ w : ℝ × ℝ, ((flatHeatKernel θ w * ρ (y + w) : ℝ) : ℂ) =
        ((∫ w : ℝ × ℝ, flatHeatKernel θ w * ρ (y + w) : ℝ) : ℂ) := integral_ofReal
    rw [integral_const_mul, hc]
    rfl
  -- integrability of the left side
  have hA : Integrable (fun z => flatHeat θ g z i * ((ρ z : ℝ) : ℂ)) := by
    have h := hFint.integral_prod_left
    exact h.congr (ae_of_all _ fun z => hLHS z)
  -- the convolution bound
  have hconv : ∀ y : ℝ × ℝ, ‖dsolHeatConv θ ρ y‖ ≤
      ((4 * Real.pi * θ)⁻¹ * Real.exp (S / (4 * θ)) * (∫ u, ‖ρ u‖)) *
        Real.exp (-(8 * θ)⁻¹ * (y.1 ^ 2 + y.2 ^ 2)) := by
    intro y
    have hpt : ∀ w : ℝ × ℝ, ‖flatHeatKernel θ w * ρ (y + w)‖ ≤
        ((4 * Real.pi * θ)⁻¹ * Real.exp (S / (4 * θ)) * Real.exp (-(8 * θ)⁻¹ * (y.1 ^ 2 + y.2 ^ 2))) *
          ‖ρ (y + w)‖ := by
      intro w
      rw [norm_mul, Real.norm_of_nonneg (hK0 w)]
      exact dsolHA_abs_le hθ hS y w
    have hI := norm_integral_le_of_norm_le
      ((hρint.comp_add_left y).const_mul
        ((4 * Real.pi * θ)⁻¹ * Real.exp (S / (4 * θ)) * Real.exp (-(8 * θ)⁻¹ * (y.1 ^ 2 + y.2 ^ 2))))
      (ae_of_all _ hpt)
    have hshift : ∫ w : ℝ × ℝ, ‖ρ (y + w)‖ = ∫ u : ℝ × ℝ, ‖ρ u‖ :=
      integral_add_left_eq_self (fun u : ℝ × ℝ => ‖ρ u‖) y
    rw [integral_const_mul, hshift] at hI
    unfold dsolHeatConv
    exact hI.trans (le_of_eq (by ring))
  have hDm : AEStronglyMeasurable (fun y : ℝ × ℝ => dsolHeatConv θ ρ y) volume := by
    have hfm : AEStronglyMeasurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
        flatHeatKernel θ p.2 * ρ (p.1 + p.2)) ((volume : Measure (ℝ × ℝ)).prod volume) :=
      ((hKc.comp continuous_snd).mul (hρc.comp (continuous_fst.add continuous_snd))).aestronglyMeasurable
    exact hfm.integral_prod_right'
  -- integrability of the right side
  have hB2 : Integrable (fun y : ℝ × ℝ => g y i * ((dsolHeatConv θ ρ y : ℝ) : ℂ)) := by
    refine Integrable.mono'
      (hf.const_mul ((4 * Real.pi * θ)⁻¹ * Real.exp (S / (4 * θ)) * (∫ u, ‖ρ u‖))) ?_
      (ae_of_all _ fun y => ?_)
    · exact ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_aestronglyMeasurable hgm).mul
        (Complex.continuous_ofReal.comp_aestronglyMeasurable hDm)
    · rw [norm_mul, Complex.norm_real]
      have hgi : ‖g y i‖ ≤ ‖g y‖ := PiLp.norm_apply_le (g y) i
      calc ‖g y i‖ * ‖dsolHeatConv θ ρ y‖ ≤ ‖g y‖ * ‖dsolHeatConv θ ρ y‖ :=
            mul_le_mul_of_nonneg_right hgi (norm_nonneg _)
        _ ≤ ‖g y‖ * (((4 * Real.pi * θ)⁻¹ * Real.exp (S / (4 * θ)) * (∫ u, ‖ρ u‖)) *
              Real.exp (-(8 * θ)⁻¹ * (y.1 ^ 2 + y.2 ^ 2))) :=
            mul_le_mul_of_nonneg_left (hconv y) (norm_nonneg _)
        _ = ((4 * Real.pi * θ)⁻¹ * Real.exp (S / (4 * θ)) * (∫ u, ‖ρ u‖)) *
              (Real.exp (-(8 * θ)⁻¹ * (y.1 ^ 2 + y.2 ^ 2)) * ‖g y‖) := by ring
  -- the identity
  have hEq : ∫ z, flatHeat θ g z i * ((ρ z : ℝ) : ℂ) =
      ∫ y, g y i * ((dsolHeatConv θ ρ y : ℝ) : ℂ) := by
    calc ∫ z, flatHeat θ g z i * ((ρ z : ℝ) : ℂ)
        = ∫ z, ∫ w, dsolHAG θ g ρ i (dsolHAshear (z, w)) := by
          congr 1
          funext z
          rw [hLHS z]
      _ = ∫ p, dsolHAG θ g ρ i (dsolHAshear p) :=
          (integral_prod (fun p => dsolHAG θ g ρ i (dsolHAshear p)) hFint).symm
      _ = ∫ q, dsolHAG θ g ρ i q := hsh.integral_comp' (dsolHAG θ g ρ i)
      _ = ∫ y, ∫ w, dsolHAG θ g ρ i (y, w) := integral_prod (dsolHAG θ g ρ i) hGint
      _ = ∫ y, g y i * ((dsolHeatConv θ ρ y : ℝ) : ℂ) := by
          congr 1
          funext y
          exact hWy y
  exact ⟨hA, hB2, hEq⟩

end UnforcedLeray.Short.IIb
