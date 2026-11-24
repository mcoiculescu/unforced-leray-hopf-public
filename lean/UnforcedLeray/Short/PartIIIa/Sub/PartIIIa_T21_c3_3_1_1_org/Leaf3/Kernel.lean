import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6_1_1_3.AdjFubini0

/-!
# Leaf (c) helpers: the periodic kernel against band-dominated fields

Source `the November 2 reference manuscript` lines 2863-2865 (the interaction
`(K_d W)·∇E_mov`), 2876-2881 (the periodic kernel `K_d`), 2953-2958.

A field `g` dominated on the cell by `M |ψ₀|` for a cylinder test `ψ₀` (bounded, vanishing outside
a band) has `sup_z ∫_{C_d} |g(x)| |K_d(x - z)| dx < ∞` (`kerNearFar0`, `kernel_test_bound0`).
Hence `(x, z) ↦ g(x) K_d(x - z) h(z)` is integrable on `C_d × C_d` for `h ∈ L¹(C_d)`, which gives
the Fubini identity `∫ g · K_d h = ∫ h · K_dᵀ g`, and `z ↦ ∫ g(x) K_d(x - z) dx` is bounded and
measurable.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa.ComplFreeRateSub.Leaf3Aux

open UnforcedLeray.Short.IIIa

/-- A band cutoff cylinder test: `ψ₀ ≥ 0` and `ψ₀ = 1` on `|η| ≤ R`. -/
theorem exists_band_cutoff (d R : ℝ) :
    ∃ ψ₀ : ℝ × ℝ → ℝ, B0579.IsCylTest d ψ₀ ∧ (∀ x, 0 ≤ ψ₀ x) ∧
      ∀ x : ℝ × ℝ, |x.2| ≤ R → ψ₀ x = 1 := by
  let b : ContDiffBump (0 : ℝ) := ⟨|R| + 1, |R| + 2, by positivity, by linarith⟩
  refine ⟨fun x => b x.2, ⟨b.contDiff.comp contDiff_snd, fun _ => rfl, ⟨|R| + 2, fun x hx =>
      b.zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact hx.le)⟩⟩, fun x => b.nonneg, ?_⟩
  intro x hx
  refine b.one_of_mem_closedBall ?_
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
  have := le_abs_self R
  show |x.2| ≤ |R| + 1
  linarith

/-- Uniform kernel bound against a cylinder test (`kernel_test_bound0` and `K_d(-z) = -K_d(z)`). -/
theorem kernel_bound {d : ℝ} (hd : 0 < d) {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest d ψ) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (z : ℝ × ℝ) (j : Fin 2),
      ∫⁻ x in B0579.cell d, ‖kerD d (x - z) j‖ₑ * ‖ψ x‖ₑ ≤ K := by
  obtain ⟨C, hC0, hmeas, hper, hodd, hnear, hfar⟩ := kerNearFar0 d hd
  obtain ⟨B, hB0, hB, hL⟩ := AdjFubiniAux.test_facts hd hψ
  refine ⟨ENNReal.ofReal B * ENNReal.ofReal C +
      ENNReal.ofReal C * ∫⁻ y in UnforcedLeray.Cyl.cell d, ‖ψ y‖ₑ, ?_, fun z j => ?_⟩
  · exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hL.ne⟩
  · have h := AdjFubiniAux.kernel_test_bound0 hd hC0 hper hnear hfar hmeas hψ hB hB0 j z
    refine le_trans (le_of_eq ?_) h
    refine lintegral_congr fun x => ?_
    have : x - z = -(z - x) := by abel
    rw [this, hodd, enorm_neg]

/-- Domination of a field by `M |ψ|` on the cell, inside a weighted lintegral. -/
theorem lintegral_dom_le {d M : ℝ} (hM : 0 ≤ M) {ψ : ℝ × ℝ → ℝ} {g : ℝ × ℝ → ℂ}
    (hg : ∀ x ∈ B0579.cell d, ‖g x‖ ≤ M * |ψ x|) (k : ℝ × ℝ → ℝ≥0∞) :
    ∫⁻ x in B0579.cell d, k x * ‖g x‖ₑ ≤
      ENNReal.ofReal M * ∫⁻ x in B0579.cell d, k x * ‖ψ x‖ₑ := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' (B0579.measurableSet_cell d) fun x hx => ?_
  have h1 : ‖g x‖ₑ ≤ ENNReal.ofReal M * ‖ψ x‖ₑ := by
    calc ‖g x‖ₑ = ENNReal.ofReal ‖g x‖ := (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal (M * |ψ x|) := ENNReal.ofReal_le_ofReal (hg x hx)
      _ = ENNReal.ofReal M * ‖ψ x‖ₑ := by
          rw [ENNReal.ofReal_mul hM, Real.enorm_eq_ofReal_abs]
  calc k x * ‖g x‖ₑ ≤ k x * (ENNReal.ofReal M * ‖ψ x‖ₑ) := by gcongr
    _ = ENNReal.ofReal M * (k x * ‖ψ x‖ₑ) := by ring

/-- The kernel integral `∫_{C_d} ‖g(x) K_d(x - z)‖ ≤ M K`. -/
theorem lintegral_ker_le {d M : ℝ} (hM : 0 ≤ M) {ψ : ℝ × ℝ → ℝ} {g : ℝ × ℝ → ℂ}
    (hg : ∀ x ∈ B0579.cell d, ‖g x‖ ≤ M * |ψ x|) {K : ℝ≥0∞}
    (hK : ∀ (z : ℝ × ℝ) (j : Fin 2), ∫⁻ x in B0579.cell d, ‖kerD d (x - z) j‖ₑ * ‖ψ x‖ₑ ≤ K)
    (z : ℝ × ℝ) (j : Fin 2) :
    ∫⁻ x in B0579.cell d, ‖g x * ((kerD d (x - z) j : ℝ) : ℂ)‖ₑ ≤ ENNReal.ofReal M * K := by
  calc ∫⁻ x in B0579.cell d, ‖g x * ((kerD d (x - z) j : ℝ) : ℂ)‖ₑ
      = ∫⁻ x in B0579.cell d, ‖kerD d (x - z) j‖ₑ * ‖g x‖ₑ := by
        refine lintegral_congr fun x => ?_
        rw [enorm_mul, AdjFubiniAux.enorm_ofReal_complex, mul_comm]
    _ ≤ ENNReal.ofReal M * ∫⁻ x in B0579.cell d, ‖kerD d (x - z) j‖ₑ * ‖ψ x‖ₑ :=
        lintegral_dom_le hM hg _
    _ ≤ ENNReal.ofReal M * K := by gcongr; exact hK z j

/-- For each `z`, `x ↦ g(x) K_d(x - z)` is integrable on the cell. -/
theorem integrable_ker_left {d M : ℝ} (hd : 0 < d) (hM : 0 ≤ M) {ψ : ℝ × ℝ → ℝ}
    (hψ : B0579.IsCylTest d ψ) {g : ℝ × ℝ → ℂ}
    (hgm : AEStronglyMeasurable g (volume.restrict (B0579.cell d)))
    (hg : ∀ x ∈ B0579.cell d, ‖g x‖ ≤ M * |ψ x|) (z : ℝ × ℝ) (j : Fin 2) :
    Integrable (fun x => g x * ((kerD d (x - z) j : ℝ) : ℂ)) (volume.restrict (B0579.cell d)) := by
  obtain ⟨C, hC0, hmeas, -, -, -, -⟩ := kerNearFar0 d hd
  obtain ⟨K, hK, hKb⟩ := kernel_bound hd hψ
  refine ⟨hgm.mul (Complex.measurable_ofReal.comp
    ((hmeas j).comp (measurable_id.sub measurable_const))).aestronglyMeasurable, ?_⟩
  exact lt_of_le_of_lt (lintegral_ker_le hM hg hKb z j)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.lt_top)

/-- Integrability of `(x, z) ↦ g(x) K_d(x - z) h(z)` on `C_d × C_d`. -/
theorem integrable_ker_prod {d M : ℝ} (hd : 0 < d) (hM : 0 ≤ M) {ψ : ℝ × ℝ → ℝ}
    (hψ : B0579.IsCylTest d ψ) {g h : ℝ × ℝ → ℂ}
    (hgm : AEStronglyMeasurable g (volume.restrict (B0579.cell d)))
    (hg : ∀ x ∈ B0579.cell d, ‖g x‖ ≤ M * |ψ x|) (hh : IntegrableOn h (B0579.cell d))
    (j : Fin 2) :
    Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => g p.1 * ((kerD d (p.1 - p.2) j : ℝ) : ℂ) * h p.2)
      ((volume.restrict (B0579.cell d)).prod (volume.restrict (B0579.cell d))) := by
  obtain ⟨C, hC0, hmeas, -, -, -, -⟩ := kerNearFar0 d hd
  obtain ⟨K, hK, hKb⟩ := kernel_bound hd hψ
  set μ := volume.restrict (B0579.cell d) with hμ
  have hkm : AEStronglyMeasurable
      (fun p : (ℝ × ℝ) × (ℝ × ℝ) => ((kerD d (p.1 - p.2) j : ℝ) : ℂ)) (μ.prod μ) :=
    (Complex.measurable_ofReal.comp
      ((hmeas j).comp (measurable_fst.sub measurable_snd))).aestronglyMeasurable
  have hm : AEStronglyMeasurable
      (fun p : (ℝ × ℝ) × (ℝ × ℝ) => g p.1 * ((kerD d (p.1 - p.2) j : ℝ) : ℂ) * h p.2)
      (μ.prod μ) :=
    ((hgm.comp_fst).mul hkm).mul (hh.aestronglyMeasurable.comp_snd)
  refine ⟨hm, ?_⟩
  unfold HasFiniteIntegral
  rw [lintegral_prod_symm _ hm.enorm]
  calc ∫⁻ z, ∫⁻ x, ‖g (x, z).1 * ((kerD d ((x, z).1 - (x, z).2) j : ℝ) : ℂ) * h (x, z).2‖ₑ ∂μ ∂μ
      ≤ ∫⁻ z, ENNReal.ofReal M * K * ‖h z‖ₑ ∂μ := by
        refine lintegral_mono fun z => ?_
        have e : ∀ x, ‖g (x, z).1 * ((kerD d ((x, z).1 - (x, z).2) j : ℝ) : ℂ) * h (x, z).2‖ₑ =
            ‖g x * ((kerD d (x - z) j : ℝ) : ℂ)‖ₑ * ‖h z‖ₑ := fun x => by
          rw [enorm_mul]
        simp_rw [e]
        rw [lintegral_mul_const' _ _ enorm_ne_top]
        gcongr
        exact lintegral_ker_le hM hg hKb z j
    _ = ENNReal.ofReal M * K * ∫⁻ z, ‖h z‖ₑ ∂μ :=
        lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hK)
    _ < ⊤ := ENNReal.mul_lt_top
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.lt_top) hh.2

/-- **Fubini for the kernel pairing**: `∫ g · (K_d h) = ∫ h · (K_dᵀ g)` on the cell, with both
integrands integrable. -/
theorem fubini_ker {d M : ℝ} (hd : 0 < d) (hM : 0 ≤ M) {ψ : ℝ × ℝ → ℝ}
    (hψ : B0579.IsCylTest d ψ) {g h : ℝ × ℝ → ℂ}
    (hgm : AEStronglyMeasurable g (volume.restrict (B0579.cell d)))
    (hg : ∀ x ∈ B0579.cell d, ‖g x‖ ≤ M * |ψ x|) (hh : IntegrableOn h (B0579.cell d))
    (j : Fin 2) :
    Integrable (fun y => g y * ∫ z in B0579.cell d, h z * ((kerD d (y - z) j : ℝ) : ℂ))
        (volume.restrict (B0579.cell d)) ∧
      Integrable (fun z => h z * ∫ y in B0579.cell d, g y * ((kerD d (y - z) j : ℝ) : ℂ))
        (volume.restrict (B0579.cell d)) ∧
      ∫ y in B0579.cell d, g y * (∫ z in B0579.cell d, h z * ((kerD d (y - z) j : ℝ) : ℂ)) =
        ∫ z in B0579.cell d, h z * ∫ y in B0579.cell d, g y * ((kerD d (y - z) j : ℝ) : ℂ) := by
  have I := integrable_ker_prod hd hM hψ hgm hg hh j
  have e1 : ∀ y, ∫ z in B0579.cell d, g y * ((kerD d (y - z) j : ℝ) : ℂ) * h z =
      g y * ∫ z in B0579.cell d, h z * ((kerD d (y - z) j : ℝ) : ℂ) := by
    intro y
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    show g y * ((kerD d (y - z) j : ℝ) : ℂ) * h z = g y * (h z * ((kerD d (y - z) j : ℝ) : ℂ))
    ring
  have e2 : ∀ z, ∫ y in B0579.cell d, g y * ((kerD d (y - z) j : ℝ) : ℂ) * h z =
      h z * ∫ y in B0579.cell d, g y * ((kerD d (y - z) j : ℝ) : ℂ) := by
    intro z
    rw [integral_mul_const, mul_comm]
  refine ⟨?_, ?_, ?_⟩
  · have := I.integral_prod_left
    simp only [e1] at this
    exact this
  · have := I.integral_prod_right
    simp only [e2] at this
    exact this
  · have hsw := integral_integral_swap
      (f := fun y z => g y * ((kerD d (y - z) j : ℝ) : ℂ) * h z) I
    simp only [e1, e2] at hsw
    exact hsw

/-- `z ↦ ∫_{C_d} g(x) K_d(x - z) dx` is strongly measurable for strongly measurable `g`. -/
theorem stronglyMeasurable_kerInt {d : ℝ} (hd : 0 < d) {g : ℝ × ℝ → ℂ}
    (hgs : StronglyMeasurable g) (j : Fin 2) :
    StronglyMeasurable (fun z => ∫ x in B0579.cell d, g x * ((kerD d (x - z) j : ℝ) : ℂ)) := by
  obtain ⟨C, hC0, hmeas, -, -, -, -⟩ := kerNearFar0 d hd
  refine StronglyMeasurable.integral_prod_right
    (f := fun z x => g x * ((kerD d (x - z) j : ℝ) : ℂ)) ?_
  exact (hgs.comp_measurable measurable_snd).mul
    (Complex.measurable_ofReal.comp
      ((hmeas j).comp (measurable_snd.sub measurable_fst))).stronglyMeasurable

/-- `z ↦ ∫_{C_d} g(x) K_d(x - z) dx` is integrable on every set of finite measure. -/
theorem integrableOn_kerInt {d M : ℝ} (hd : 0 < d) (hM : 0 ≤ M) {ψ : ℝ × ℝ → ℝ}
    (hψ : B0579.IsCylTest d ψ) {g : ℝ × ℝ → ℂ} (hgs : StronglyMeasurable g)
    (hg : ∀ x ∈ B0579.cell d, ‖g x‖ ≤ M * |ψ x|) (j : Fin 2) {s : Set (ℝ × ℝ)}
    (hs : volume s < ⊤) :
    IntegrableOn (fun z => ∫ x in B0579.cell d, g x * ((kerD d (x - z) j : ℝ) : ℂ)) s := by
  obtain ⟨K, hK, hKb⟩ := kernel_bound hd hψ
  have hne : ENNReal.ofReal M * K ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hK
  refine IntegrableOn.of_bound hs (stronglyMeasurable_kerInt hd hgs j).aestronglyMeasurable
    (ENNReal.ofReal M * K).toReal (Eventually.of_forall fun z => ?_)
  have h1 : ‖∫ x in B0579.cell d, g x * ((kerD d (x - z) j : ℝ) : ℂ)‖ₑ ≤
      ENNReal.ofReal M * K :=
    (enorm_integral_le_lintegral_enorm _).trans (lintegral_ker_le hM hg hKb z j)
  rw [← toReal_enorm]
  exact ENNReal.toReal_mono hne h1

end UnforcedLeray.Short.IIIa.ComplFreeRateSub.Leaf3Aux
