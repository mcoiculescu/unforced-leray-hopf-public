import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_8.SigmaAdd
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_8.SigmaInt
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.NewtonD3

/-!
# Additivity of the zero-width Newton field on the receiver region (`NewtonVAdd`)

Source `shorter-proof-2026-11-02.tex` 4776-4782, 4917-4937.  The old tensor's Cartesian source
`Σ_M` vanishes for `ρ² > 5ν/6`, so on the receiver region `x₁² + x₂² > 5ν/6` the kernel
`∂³N(x - t(x',0))` is continuous on the compact set of `(t, x')` with `ρ² ≤ 5ν/6`, `t ∈ [0,1]`
(the horizontal part of `x - t(x',0)` never vanishes there).  The inner integrals are then
additive by `sigmaM_add_ae`, and the outer `t`-integral by `integral_add`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace NVA

theorem embPlane_continuous : Continuous embPlane := by
  unfold embPlane
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp <;> fun_prop

theorem affine_continuous (x : Vec3) (t : ℝ) :
    Continuous (fun x' : ℝ × ℝ => x - t • embPlane x') :=
  continuous_const.sub (embPlane_continuous.const_smul t)

theorem affine2_continuous (x : Vec3) :
    Continuous (fun p : ℝ × (ℝ × ℝ) => x - p.1 • embPlane p.2) :=
  continuous_const.sub (continuous_fst.smul (embPlane_continuous.comp continuous_snd))

theorem newtonD3_measurable (i j k : Fin 3) : Measurable (fun x : Vec3 => newtonD3 x i j k) := by
  unfold newtonD3
  exact measurable_fderiv_apply_const ℝ _ (Pi.single i 1 : Vec3)

/-- The disk `x'₁² + x'₂² ≤ r` in the source plane. -/
def diskSet (r : ℝ) : Set (ℝ × ℝ) := {x' | x'.1 ^ 2 + x'.2 ^ 2 ≤ r}

theorem not_zero_aux {x : Vec3} {r t : ℝ} (hx : r < x 0 ^ 2 + x 1 ^ 2) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {x' : ℝ × ℝ} (hx' : x'.1 ^ 2 + x'.2 ^ 2 ≤ r) : x - t • embPlane x' ≠ 0 := by
  intro h0
  have e0 : x 0 - t * x'.1 = 0 := by
    have := congrFun h0 0
    simpa [embPlane] using this
  have e1 : x 1 - t * x'.2 = 0 := by
    have := congrFun h0 1
    simpa [embPlane] using this
  have hx0 : x 0 = t * x'.1 := by linarith
  have hx1 : x 1 = t * x'.2 := by linarith
  have ht2 : t ^ 2 ≤ 1 := by nlinarith
  have hsq : x 0 ^ 2 + x 1 ^ 2 = t ^ 2 * (x'.1 ^ 2 + x'.2 ^ 2) := by
    rw [hx0, hx1]; ring
  have hnn : 0 ≤ x'.1 ^ 2 + x'.2 ^ 2 := by positivity
  have h3 : t ^ 2 * (x'.1 ^ 2 + x'.2 ^ 2) ≤ x'.1 ^ 2 + x'.2 ^ 2 := mul_le_of_le_one_left hnn ht2
  linarith

/-- The third Newton derivative is bounded on the moving disk `x - t(x',0)`, `t ∈ [0,1]`,
`x'` in the disk `ρ² ≤ r`, when `x₁² + x₂² > r`. -/
theorem newtonD3_bdd_disk (i j k : Fin 3) {r : ℝ} {x : Vec3} (hx : r < x 0 ^ 2 + x 1 ^ 2) :
    ∃ C : ℝ, ∀ t ∈ Icc (0:ℝ) 1, ∀ x' : ℝ × ℝ, x'.1 ^ 2 + x'.2 ^ 2 ≤ r →
      |newtonD3 (x - t • embPlane x') i j k| ≤ C := by
  have hclosed : IsClosed (diskSet r) := by
    unfold diskSet
    exact isClosed_le (by fun_prop) continuous_const
  have hsub : diskSet r ⊆ Icc (-Real.sqrt r) (Real.sqrt r) ×ˢ Icc (-Real.sqrt r) (Real.sqrt r) := by
    intro p hp
    have hp' : p.1 ^ 2 + p.2 ^ 2 ≤ r := hp
    have h1 : |p.1| ≤ Real.sqrt r := Real.abs_le_sqrt (by nlinarith [sq_nonneg p.2])
    have h2 : |p.2| ≤ Real.sqrt r := Real.abs_le_sqrt (by nlinarith [sq_nonneg p.1])
    exact ⟨abs_le.mp h1, abs_le.mp h2⟩
  have hcpt : IsCompact (diskSet r) :=
    IsCompact.of_isClosed_subset
      (isCompact_Icc.prod isCompact_Icc :
        IsCompact (Icc (-Real.sqrt r) (Real.sqrt r) ×ˢ Icc (-Real.sqrt r) (Real.sqrt r)))
      hclosed hsub
  have hP : IsCompact (Icc (0:ℝ) 1 ×ˢ diskSet r) := isCompact_Icc.prod hcpt
  have hS : IsCompact ((fun p : ℝ × (ℝ × ℝ) => x - p.1 • embPlane p.2) ''
      (Icc (0:ℝ) 1 ×ˢ diskSet r)) := hP.image (affine2_continuous x)
  have hsubS : (fun p : ℝ × (ℝ × ℝ) => x - p.1 • embPlane p.2) '' (Icc (0:ℝ) 1 ×ˢ diskSet r)
      ⊆ NewtonD3.punct := by
    rintro _ ⟨p, hp, rfl⟩
    exact not_zero_aux hx hp.1.1 hp.1.2 hp.2
  have hcont : ContinuousOn (fun y : Vec3 => newtonD3 y i j k)
      ((fun p : ℝ × (ℝ × ℝ) => x - p.1 • embPlane p.2) '' (Icc (0:ℝ) 1 ×ˢ diskSet r)) :=
    (NewtonD3.newtonD3_contDiffOn i j k).continuousOn.mono hsubS
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hcont
  refine ⟨C, fun t ht x' hx' => ?_⟩
  have h := hC (x - t • embPlane x') ⟨(t, x'), ⟨ht, hx'⟩, rfl⟩
  rw [Real.norm_eq_abs] at h
  exact h

/-- The Cartesian source vanishes off the disk `ρ² ≤ 5ν/6`. -/
theorem sigmaM_entry_zero (c : ℝ) {ν : ℝ} {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) (hν : 0 < ν)
    (M : Chart → Mat3) {x' : ℝ × ℝ} (hx' : 5 * ν / 6 < x'.1 ^ 2 + x'.2 ^ 2) (j k : Fin 3) :
    sigmaM c ν χo M x' j k = 0 := by
  have hs : 0 < x'.1 ^ 2 + x'.2 ^ 2 := by linarith
  have hle : ν * (x'.1 ^ 2 + x'.2 ^ 2)⁻¹ ≤ 6 / 5 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hs]
    linarith
  have hz : phaseMean c ν χo M (x'.1 ^ 2 + x'.2 ^ 2)⁻¹ = 0 := by
    ext a b
    simp [phaseMean, hχo.zero _ hle]
  simp [sigmaM, hz]

theorem term_bound (c ν : ℝ) {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) (hν : 0 < ν)
    (M : Chart → Mat3) (x : Vec3) (t : ℝ) (i j k : Fin 3) (C : ℝ)
    (hCt : ∀ x' : ℝ × ℝ, x'.1 ^ 2 + x'.2 ^ 2 ≤ 5 * ν / 6 →
      |newtonD3 (x - t • embPlane x') i j k| ≤ C)
    (x' : ℝ × ℝ) :
    |newtonD3 (x - t • embPlane x') i j k * sigmaM c ν χo M x' j k| ≤
      C * |sigmaM c ν χo M x' j k| := by
  by_cases h : x'.1 ^ 2 + x'.2 ^ 2 ≤ 5 * ν / 6
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hCt x' h) (abs_nonneg _)
  · rw [sigmaM_entry_zero c hχo hν M (not_le.mp h) j k]
    simp

theorem term_integrable (c ν : ℝ) {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) (hν : 0 < ν)
    (M : Chart → Mat3) (x : Vec3) (t : ℝ) (i j k : Fin 3) (C : ℝ)
    (hCt : ∀ x' : ℝ × ℝ, x'.1 ^ 2 + x'.2 ^ 2 ≤ 5 * ν / 6 →
      |newtonD3 (x - t • embPlane x') i j k| ≤ C)
    (hσ : Integrable (fun x' : ℝ × ℝ => sigmaM c ν χo M x' j k)) :
    Integrable (fun x' : ℝ × ℝ => newtonD3 (x - t • embPlane x') i j k * sigmaM c ν χo M x' j k) := by
  refine Integrable.mono' (hσ.norm.const_mul C) ?_ (Filter.Eventually.of_forall fun x' => ?_)
  · exact (((newtonD3_measurable i j k).comp (affine_continuous x t).measurable).aestronglyMeasurable).mul
      hσ.aestronglyMeasurable
  · simp only [Real.norm_eq_abs]
    exact term_bound c ν hχo hν M x t i j k C hCt x'

/-- The inner integrand of `V_{μ,M}(x)_i` at height `t`. -/
def innerF (c ν : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (i : Fin 3) (x : Vec3) (t : ℝ)
    (x' : ℝ × ℝ) : ℝ :=
  ∑ j, ∑ k, newtonD3 (x - t • embPlane x') i j k * sigmaM c ν χo M x' j k

theorem newtonV_eq (c ν μ : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (x : Vec3) (i : Fin 3) :
    newtonV c ν μ χo M x i =
      -2 * ∫ t in Ioc (0:ℝ) 1, t ^ (2 * μ + 2) * ∫ x', innerF c ν χo M i x t x' := rfl

theorem innerF_integrable (c ν : ℝ) {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) (hν : 0 < ν)
    {M : Chart → Mat3} (hσ : ∀ j k, Integrable (fun x' : ℝ × ℝ => sigmaM c ν χo M x' j k))
    (i : Fin 3) (x : Vec3) (t : ℝ) (C : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hC : ∀ i' j k : Fin 3, ∀ s ∈ Icc (0:ℝ) 1, ∀ x' : ℝ × ℝ, x'.1 ^ 2 + x'.2 ^ 2 ≤ 5 * ν / 6 →
      |newtonD3 (x - s • embPlane x') i' j k| ≤ C i' j k)
    (ht : t ∈ Icc (0:ℝ) 1) :
    Integrable (innerF c ν χo M i x t) := by
  unfold innerF
  exact integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
    term_integrable c ν hχo hν M x t i j k (C i j k) (fun x' hx' => hC i j k t ht x' hx') (hσ j k)

theorem innerF_integral_add (c ν : ℝ) {χo : ℝ → ℝ} (hc : 0 < c) (hν : 0 < ν)
    (hχo : IsOutwardCutoff χo) {M M' : Chart → Mat3} (hM : OldThinFinite c ν M)
    (hM' : OldThinFinite c ν M') (i : Fin 3) (x : Vec3) (t : ℝ)
    (h1 : Integrable (innerF c ν χo M i x t)) (h2 : Integrable (innerF c ν χo M' i x t)) :
    ∫ x', innerF c ν χo (M + M') i x t x' =
      (∫ x', innerF c ν χo M i x t x') + (∫ x', innerF c ν χo M' i x t x') := by
  have e := sigmaM_add_ae c ν χo hc hν hχo M M' hM hM'
  rw [← integral_add h1 h2]
  apply integral_congr_ae
  filter_upwards [e] with x' hx'
  have hxx : ∀ j k, sigmaM c ν χo (M + M') x' j k =
      sigmaM c ν χo M x' j k + sigmaM c ν χo M' x' j k :=
    fun j k => congrFun (congrFun hx' j) k
  simp only [innerF, hxx, mul_add, Finset.sum_add_distrib]

theorem outer_integrable (c ν : ℝ) {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) (hν : 0 < ν)
    (μ : ℝ) (hμ : 0 < μ) {M : Chart → Mat3}
    (hσ : ∀ j k, Integrable (fun x' : ℝ × ℝ => sigmaM c ν χo M x' j k))
    (i : Fin 3) (x : Vec3) (C : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hC : ∀ i' j k : Fin 3, ∀ s ∈ Icc (0:ℝ) 1, ∀ x' : ℝ × ℝ, x'.1 ^ 2 + x'.2 ^ 2 ≤ 5 * ν / 6 →
      |newtonD3 (x - s • embPlane x') i' j k| ≤ C i' j k) :
    IntegrableOn (fun t : ℝ => t ^ (2 * μ + 2) * ∫ x', innerF c ν χo M i x t x') (Ioc 0 1) := by
  have hgI : Integrable (fun x' : ℝ × ℝ => ∑ j, ∑ k, C i j k * ‖sigmaM c ν χo M x' j k‖) :=
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => (hσ j k).norm.const_mul _
  have hbound : ∀ t ∈ Ioc (0:ℝ) 1, ‖∫ x', innerF c ν χo M i x t x'‖ ≤
      ∫ x' : ℝ × ℝ, ∑ j, ∑ k, C i j k * ‖sigmaM c ν χo M x' j k‖ := by
    intro t ht
    refine norm_integral_le_of_norm_le hgI (Filter.Eventually.of_forall fun x' => ?_)
    show ‖∑ j, ∑ k, newtonD3 (x - t • embPlane x') i j k * sigmaM c ν χo M x' j k‖ ≤
      ∑ j, ∑ k, C i j k * ‖sigmaM c ν χo M x' j k‖
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ =>
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_))
    simp only [Real.norm_eq_abs]
    exact term_bound c ν hχo hν M x t i j k (C i j k)
      (fun x'' hx'' => hC i j k t (Ioc_subset_Icc_self ht) x'' hx'') x'
  generalize hBdef : (∫ x' : ℝ × ℝ, ∑ j, ∑ k, C i j k * ‖sigmaM c ν χo M x' j k‖) = B at hbound
  have hGm : AEStronglyMeasurable (fun p : ℝ × (ℝ × ℝ) => innerF c ν χo M i x p.1 p.2)
      (volume.prod volume) := by
    have hterm : ∀ j k : Fin 3, AEStronglyMeasurable
        (fun p : ℝ × (ℝ × ℝ) => newtonD3 (x - p.1 • embPlane p.2) i j k * sigmaM c ν χo M p.2 j k)
        (volume.prod volume) := by
      intro j k
      have hK : Measurable (fun p : ℝ × (ℝ × ℝ) => newtonD3 (x - p.1 • embPlane p.2) i j k) :=
        (newtonD3_measurable i j k).comp (affine2_continuous x).measurable
      have hσ' : AEStronglyMeasurable (fun p : ℝ × (ℝ × ℝ) => sigmaM c ν χo M p.2 j k)
          (volume.prod volume) :=
        (hσ j k).aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
      exact hK.aestronglyMeasurable.mul hσ'
    unfold innerF
    exact Finset.aestronglyMeasurable_sum Finset.univ fun j _ =>
      Finset.aestronglyMeasurable_sum Finset.univ fun k _ => hterm j k
  have hF : AEStronglyMeasurable (fun t : ℝ => ∫ x', innerF c ν χo M i x t x') volume :=
    hGm.integral_prod_right'
  show Integrable (fun t : ℝ => t ^ (2 * μ + 2) * ∫ x', innerF c ν χo M i x t x')
    (volume.restrict (Ioc (0:ℝ) 1))
  have hconst : Integrable (fun _ : ℝ => B) (volume.restrict (Ioc (0:ℝ) 1)) :=
    integrableOn_const (by simp)
  refine Integrable.mono' hconst ?_ ?_
  · exact ((measurable_id.pow_const _).aestronglyMeasurable.mul hF).restrict
  · refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun t ht => ?_)
    show ‖t ^ (2 * μ + 2) * ∫ x', innerF c ν χo M i x t x'‖ ≤ B
    have h0 : 0 ≤ t ^ (2 * μ + 2) := Real.rpow_nonneg ht.1.le _
    have h1 : t ^ (2 * μ + 2) ≤ 1 := Real.rpow_le_one ht.1.le ht.2 (by linarith)
    have h2 := hbound t ht
    have h4 : 0 ≤ ‖∫ x', innerF c ν χo M i x t x'‖ := norm_nonneg _
    rw [norm_mul, Real.norm_of_nonneg h0]
    nlinarith [mul_nonneg (sub_nonneg.2 h1) h4]

end NVA

end UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.PartIIIb.Concrete in
theorem newtonV_add : UnforcedLeray.Short.PartIIIb.Concrete.NewtonVAdd := by
  intro c ν μ χo hc hν hμ hχo M M' hM hM' x hx
  have hbd : ∀ i j k : Fin 3, ∃ C : ℝ, ∀ t ∈ Icc (0:ℝ) 1, ∀ x' : ℝ × ℝ,
      x'.1 ^ 2 + x'.2 ^ 2 ≤ 5 * ν / 6 → |newtonD3 (x - t • embPlane x') i j k| ≤ C :=
    fun i j k => NVA.newtonD3_bdd_disk i j k hx
  choose C hC using hbd
  have hσM : ∀ j k, Integrable (fun x' : ℝ × ℝ => sigmaM c ν χo M x' j k) :=
    fun j k => sigmaM_integrable c ν χo hc hν hχo M hM j k
  have hσM' : ∀ j k, Integrable (fun x' : ℝ × ℝ => sigmaM c ν χo M' x' j k) :=
    fun j k => sigmaM_integrable c ν χo hc hν hχo M' hM' j k
  funext i
  have hsplit : ∀ t ∈ Ioc (0:ℝ) 1,
      t ^ (2 * μ + 2) * ∫ x', NVA.innerF c ν χo (M + M') i x t x' =
        t ^ (2 * μ + 2) * (∫ x', NVA.innerF c ν χo M i x t x') +
          t ^ (2 * μ + 2) * (∫ x', NVA.innerF c ν χo M' i x t x') := by
    intro t ht
    rw [NVA.innerF_integral_add c ν hc hν hχo hM hM' i x t
      (NVA.innerF_integrable c ν hχo hν hσM i x t C hC (Ioc_subset_Icc_self ht))
      (NVA.innerF_integrable c ν hχo hν hσM' i x t C hC (Ioc_subset_Icc_self ht))]
    ring
  have key : ∫ t in Ioc (0:ℝ) 1, t ^ (2 * μ + 2) * ∫ x', NVA.innerF c ν χo (M + M') i x t x' =
      (∫ t in Ioc (0:ℝ) 1, t ^ (2 * μ + 2) * ∫ x', NVA.innerF c ν χo M i x t x') +
        ∫ t in Ioc (0:ℝ) 1, t ^ (2 * μ + 2) * ∫ x', NVA.innerF c ν χo M' i x t x' := by
    rw [setIntegral_congr_fun measurableSet_Ioc hsplit]
    exact integral_add (NVA.outer_integrable c ν hχo hν μ hμ hσM i x C hC)
      (NVA.outer_integrable c ν hχo hν μ hμ hσM' i x C hC)
  simp only [NVA.newtonV_eq, Pi.add_apply]
  rw [key]
  ring
