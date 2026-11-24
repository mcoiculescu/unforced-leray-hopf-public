import UnforcedLeray.Units.B0289.Semigroup

/-!
# B0289: the cutoff identity for the Duhamel integral

Unit B0289 (tex lines 4771–4775). The manuscript localizes the flat inverse `b = T̄F` to a
dyadic age window with a cutoff `χ` (tex lines 3788–3792): "Its zero extension solves the
ordinary heat equation with source `χ P₀F/s + (χ' - μχ/s) b`" (here `μ = 0`). In Duhamel form:

`duhamel_cutoff`: `∫_0^s e^{ν(s-t)Δ}[χ(t) g(t) + χ'(t) u(t)] dt = χ(s) u(s)` at every point
`z` where `∫_0^s heatAbs_{ν(s-t)} g(t) (z) dt < ∞`, for `u = duhamel ν g`.

The proof: the semigroup law (`heat_heat`) inside the age integral (`heat_duhamel`), Fubini on
the triangle `0 < r < t < s` and the fundamental theorem of calculus for `χ`
(`integral_deriv_smul_primitive`). Joint measurability of the Duhamel integral is
`stronglyMeasurable_duhamel`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Real
open scoped NNReal ENNReal

namespace UnforcedLeray.B0289

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.B0284

/-! ## Measurability -/

theorem stronglyMeasurable_slice {g : ℝ → Plane → Plane}
    (hg : StronglyMeasurable (Function.uncurry g)) (t : ℝ) : StronglyMeasurable (g t) :=
  hg.comp_measurable measurable_prodMk_left

/-- `(θ, t, z) ↦ e^{θΔ}(g t)(z)` is jointly strongly measurable. -/
theorem stronglyMeasurable_heat_family {g : ℝ → Plane → Plane}
    (hg : StronglyMeasurable (Function.uncurry g)) :
    StronglyMeasurable fun x : ℝ × ℝ × Plane => heat x.1 (g x.2.1) x.2.2 := by
  have hint : StronglyMeasurable fun x : ℝ × ℝ × Plane =>
      ∫ w : Plane, heatKernel2 x.1 w • g x.2.1 (x.2.2 - w) := by
    have h1 : Measurable fun q : (ℝ × ℝ × Plane) × Plane => heatKernel2 q.1.1 q.2 :=
      measurable_heatKernel2.comp (measurable_fst.fst.prodMk measurable_snd)
    have h2 : StronglyMeasurable fun q : (ℝ × ℝ × Plane) × Plane =>
        g q.1.2.1 (q.1.2.2 - q.2) :=
      hg.comp_measurable (measurable_fst.snd.fst.prodMk
        (measurable_fst.snd.snd.sub measurable_snd))
    exact (h1.stronglyMeasurable.smul h2).integral_prod_right'
  have hg' : StronglyMeasurable fun x : ℝ × ℝ × Plane => g x.2.1 x.2.2 :=
    hg.comp_measurable (measurable_snd.fst.prodMk measurable_snd.snd)
  have e : (fun x : ℝ × ℝ × Plane => heat x.1 (g x.2.1) x.2.2) = fun x =>
      if 0 < x.1 then ∫ w : Plane, heatKernel2 x.1 w • g x.2.1 (x.2.2 - w) else
        g x.2.1 x.2.2 := by
    funext x
    rfl
  rw [e]
  exact StronglyMeasurable.ite (measurableSet_lt measurable_const measurable_fst) hint hg'

/-- `(θ, t, z) ↦ heatAbs_θ (g t) z` is measurable. -/
theorem measurable_heatAbs_gen {g : ℝ → Plane → Plane}
    (hg : StronglyMeasurable (Function.uncurry g)) :
    Measurable fun x : ℝ × ℝ × Plane => heatAbs x.1 (g x.2.1) x.2.2 := by
  have h1 : Measurable fun q : (ℝ × ℝ × Plane) × Plane =>
      ENNReal.ofReal (heatKernel2 q.1.1 q.2) :=
    ENNReal.measurable_ofReal.comp
      (measurable_heatKernel2.comp (measurable_fst.fst.prodMk measurable_snd))
  have h2 : Measurable fun q : (ℝ × ℝ × Plane) × Plane => ‖g q.1.2.1 (q.1.2.2 - q.2)‖ₑ :=
    (hg.comp_measurable (measurable_fst.snd.fst.prodMk
      (measurable_fst.snd.snd.sub measurable_snd))).measurable.enorm
  exact (h1.mul h2).lintegral_prod_right'

theorem stronglyMeasurable_heat_age {ν s : ℝ} {g : ℝ → Plane → Plane}
    (hg : StronglyMeasurable (Function.uncurry g)) (z : Plane) :
    StronglyMeasurable fun t => heat (ν * (s - t)) (g t) z :=
  (stronglyMeasurable_heat_family hg).comp_measurable
    ((measurable_const.mul (measurable_const.sub measurable_id)).prodMk
      (measurable_id.prodMk measurable_const))

theorem measurable_heatAbs_age (θ : ℝ → ℝ) (hθ : Measurable θ) {g : ℝ → Plane → Plane}
    (hg : StronglyMeasurable (Function.uncurry g)) (z : Plane) :
    Measurable fun t => heatAbs (θ t) (g t) z :=
  (measurable_heatAbs_gen hg).comp (hθ.prodMk (measurable_id.prodMk measurable_const))

/-- The Duhamel integral of a jointly measurable source is jointly strongly measurable. -/
theorem stronglyMeasurable_duhamel {ν : ℝ} {g : ℝ → Plane → Plane}
    (hg : StronglyMeasurable (Function.uncurry g)) :
    StronglyMeasurable (Function.uncurry (duhamel ν g)) := by
  have hH := stronglyMeasurable_heat_family hg
  set S : Set ((ℝ × Plane) × ℝ) := {q | q.2 ∈ Ioo 0 q.1.1} with hS
  have hSm : MeasurableSet S :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_fst.fst)
  have hF : StronglyMeasurable fun q : (ℝ × Plane) × ℝ =>
      S.indicator (fun q => heat (ν * (q.1.1 - q.2)) (g q.2) q.1.2) q := by
    refine StronglyMeasurable.indicator ?_ hSm
    exact hH.comp_measurable ((measurable_const.mul (measurable_fst.fst.sub measurable_snd)).prodMk
      (measurable_snd.prodMk measurable_fst.snd))
  have heq : Function.uncurry (duhamel ν g) = fun x : ℝ × Plane =>
      ∫ t, S.indicator (fun q => heat (ν * (q.1.1 - q.2)) (g q.2) q.1.2) (x, t) := by
    funext x
    simp only [Function.uncurry, duhamel]
    rw [← integral_indicator measurableSet_Ioo]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [Set.indicator, hS, Set.mem_ofPred_eq]
  rw [heq]
  exact hF.integral_prod_right'

/-! ## Absolute bounds -/

theorem enorm_duhamel_le {ν : ℝ} (hν : 0 < ν) (g : ℝ → Plane → Plane) (t : ℝ) (x : Plane) :
    ‖duhamel ν g t x‖ₑ ≤ ∫⁻ r in Ioo 0 t, heatAbs (ν * (t - r)) (g r) x :=
  (enorm_integral_le_lintegral_enorm _).trans
    (setLIntegral_mono' measurableSet_Ioo fun r hr =>
      enorm_heat_le (mul_pos hν (sub_pos.2 hr.2)) _ x)

/-- `heatAbs_θ (u t) z ≤ ∫_0^t heatAbs_{θ+ν(t-r)} g(r) (z) dr` for `u = duhamel ν g`. -/
theorem heatAbs_duhamel_le {ν θ : ℝ} (hν : 0 < ν) (hθ : 0 < θ) {g : ℝ → Plane → Plane}
    (hg : StronglyMeasurable (Function.uncurry g)) (t : ℝ) (z : Plane) :
    heatAbs θ (duhamel ν g t) z ≤ ∫⁻ r in Ioo 0 t, heatAbs (θ + ν * (t - r)) (g r) z := by
  have hm : AEMeasurable (Function.uncurry fun (w : Plane) (r : ℝ) =>
      ENNReal.ofReal (heatKernel2 θ w) * heatAbs (ν * (t - r)) (g r) (z - w))
      ((volume : Measure Plane).prod (volume.restrict (Ioo 0 t))) := by
    refine (((measurable_ofReal_heatKernel2 θ).comp measurable_fst).mul ?_).aemeasurable
    exact (measurable_heatAbs_family hg ν t).comp
      ((measurable_const.sub measurable_fst).prodMk measurable_snd)
  calc heatAbs θ (duhamel ν g t) z
      = ∫⁻ w, ENNReal.ofReal (heatKernel2 θ w) * ‖duhamel ν g t (z - w)‖ₑ := rfl
    _ ≤ ∫⁻ w, ENNReal.ofReal (heatKernel2 θ w) *
          ∫⁻ r in Ioo 0 t, heatAbs (ν * (t - r)) (g r) (z - w) :=
        lintegral_mono fun w => by gcongr; exact enorm_duhamel_le hν g t (z - w)
    _ = ∫⁻ w, ∫⁻ r in Ioo 0 t, ENNReal.ofReal (heatKernel2 θ w) *
          heatAbs (ν * (t - r)) (g r) (z - w) := by
        refine lintegral_congr fun w => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ∫⁻ r in Ioo 0 t, ∫⁻ w, ENNReal.ofReal (heatKernel2 θ w) *
          heatAbs (ν * (t - r)) (g r) (z - w) := lintegral_lintegral_swap hm
    _ = ∫⁻ r in Ioo 0 t, heatAbs (θ + ν * (t - r)) (g r) z := by
        refine setLIntegral_congr_fun measurableSet_Ioo fun r hr => ?_
        exact lintegral_heatAbs hθ (mul_pos hν (sub_pos.2 hr.2))
          (stronglyMeasurable_slice hg r).aestronglyMeasurable z

/-! ## The heat semigroup inside the age integral -/

/-- `e^{θΔ}(u t)(z) = ∫_0^t e^{(θ+ν(t-r))Δ} g(r) (z) dr` for `u = duhamel ν g`, at a point
where the absolute integral is finite. -/
theorem heat_duhamel {ν θ : ℝ} (hν : 0 < ν) (hθ : 0 < θ) {g : ℝ → Plane → Plane}
    (hg : StronglyMeasurable (Function.uncurry g)) {t : ℝ} {z : Plane}
    (hfin : ∫⁻ r in Ioo 0 t, heatAbs (θ + ν * (t - r)) (g r) z ≠ ⊤) :
    heat θ (duhamel ν g t) z = ∫ r in Ioo 0 t, heat (θ + ν * (t - r)) (g r) z := by
  have hH := stronglyMeasurable_heat_family hg
  set f : Plane → ℝ → Plane :=
    fun w r => heatKernel2 θ w • heat (ν * (t - r)) (g r) (z - w) with hf
  have hfm : StronglyMeasurable (Function.uncurry f) := by
    refine ((measurable_heatKernel2_right θ).comp measurable_fst).stronglyMeasurable.smul ?_
    exact hH.comp_measurable ((measurable_const.mul (measurable_const.sub measurable_snd)).prodMk
      (measurable_snd.prodMk (measurable_const.sub measurable_fst)))
  have hm : Measurable (Function.uncurry fun (w : Plane) (r : ℝ) =>
      ENNReal.ofReal (heatKernel2 θ w) * heatAbs (ν * (t - r)) (g r) (z - w)) :=
    ((measurable_ofReal_heatKernel2 θ).comp measurable_fst).mul
      ((measurable_heatAbs_family hg ν t).comp
        ((measurable_const.sub measurable_fst).prodMk measurable_snd))
  have hint : Integrable (Function.uncurry f)
      ((volume : Measure Plane).prod (volume.restrict (Ioo 0 t))) := by
    refine ⟨hfm.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    calc ∫⁻ q, ‖Function.uncurry f q‖ₑ ∂((volume : Measure Plane).prod
          (volume.restrict (Ioo 0 t)))
        = ∫⁻ w, ∫⁻ r in Ioo 0 t, ‖f w r‖ₑ :=
          lintegral_prod _ hfm.aestronglyMeasurable.enorm
      _ ≤ ∫⁻ w, ∫⁻ r in Ioo 0 t, ENNReal.ofReal (heatKernel2 θ w) *
            heatAbs (ν * (t - r)) (g r) (z - w) := by
          refine lintegral_mono fun w => setLIntegral_mono' measurableSet_Ioo fun r hr => ?_
          simp only [hf]
          rw [enorm_smul, Real.enorm_of_nonneg (heatKernel2_nonneg hθ _)]
          gcongr
          exact enorm_heat_le (mul_pos hν (sub_pos.2 hr.2)) _ _
      _ = ∫⁻ r in Ioo 0 t, ∫⁻ w, ENNReal.ofReal (heatKernel2 θ w) *
            heatAbs (ν * (t - r)) (g r) (z - w) := lintegral_lintegral_swap hm.aemeasurable
      _ = ∫⁻ r in Ioo 0 t, heatAbs (θ + ν * (t - r)) (g r) z := by
          refine setLIntegral_congr_fun measurableSet_Ioo fun r hr => ?_
          exact lintegral_heatAbs hθ (mul_pos hν (sub_pos.2 hr.2))
            (stronglyMeasurable_slice hg r).aestronglyMeasurable z
      _ < ⊤ := lt_top_iff_ne_top.2 hfin
  have hae : ∀ᵐ r ∂(volume.restrict (Ioo 0 t)), heatAbs (θ + ν * (t - r)) (g r) z < ⊤ :=
    ae_lt_top (measurable_heatAbs_age (fun r => θ + ν * (t - r))
      (measurable_const.add (measurable_const.mul (measurable_const.sub measurable_id))) hg z)
      hfin
  rw [heat_apply_of_pos hθ]
  calc ∫ w, heatKernel2 θ w • duhamel ν g t (z - w) = ∫ w, ∫ r in Ioo 0 t, f w r := by
        refine integral_congr_ae (Eventually.of_forall fun w => ?_)
        simp only [hf, duhamel]
        rw [integral_smul]
    _ = ∫ r in Ioo 0 t, ∫ w, f w r := integral_integral_swap hint
    _ = ∫ r in Ioo 0 t, heat (θ + ν * (t - r)) (g r) z := by
        refine integral_congr_ae ?_
        filter_upwards [hae, ae_restrict_mem measurableSet_Ioo] with r hr hrt
        have hpos : 0 < ν * (t - r) := mul_pos hν (sub_pos.2 hrt.2)
        rw [← heat_heat hθ hpos (stronglyMeasurable_slice hg r).aestronglyMeasurable hr.ne,
          heat_apply_of_pos hθ]

/-! ## Fubini on the triangle -/

/-- `∫_0^s χ'(t) ∫_0^t Φ = ∫_0^s (χ(s) - χ(r)) Φ(r) dr`, with integrability of the left
integrand, for `χ` with a continuous bounded derivative and `Φ` integrable on `(0,s)`. -/
theorem integral_deriv_smul_primitive {s : ℝ} {χ χ' : ℝ → ℝ}
    (hχ : ∀ t, HasDerivAt χ (χ' t) t) (hχ'c : Continuous χ') {M : ℝ}
    (hM : ∀ t, |χ' t| ≤ M) {Φ : ℝ → Plane} (hΦ : IntegrableOn Φ (Ioo 0 s)) :
    IntegrableOn (fun t => χ' t • ∫ r in Ioo 0 t, Φ r) (Ioo 0 s) ∧
      ∫ t in Ioo 0 s, χ' t • ∫ r in Ioo 0 t, Φ r = ∫ r in Ioo 0 s, (χ s - χ r) • Φ r := by
  set μ : Measure ℝ := volume.restrict (Ioo 0 s) with hμ
  set T : Set (ℝ × ℝ) := {q | q.2 < q.1} with hT
  have hTm : MeasurableSet T := measurableSet_lt measurable_snd measurable_fst
  set K : ℝ × ℝ → Plane := T.indicator fun q => χ' q.1 • Φ q.2 with hK
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hKint : Integrable K (μ.prod μ) := by
    have hb : Integrable (fun q : ℝ × ℝ => (fun _ : ℝ => M) q.1 • Φ q.2) (μ.prod μ) :=
      (integrable_const M).smul_prod hΦ
    refine hb.mono ?_ (Eventually.of_forall fun q => ?_)
    · refine AEStronglyMeasurable.indicator ?_ hTm
      exact (hχ'c.measurable.comp measurable_fst).aestronglyMeasurable.smul
        hΦ.aestronglyMeasurable.comp_snd
    · simp only [hK, Set.indicator]
      split_ifs
      · rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hM0]
        exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
      · rw [norm_zero]
        exact norm_nonneg _
  have h1 : ∀ t ∈ Ioo 0 s, ∫ r, K (t, r) ∂μ = χ' t • ∫ r in Ioo 0 t, Φ r := by
    intro t ht
    have e1 : (fun r => K (t, r)) = (Iio t).indicator fun r => χ' t • Φ r := by
      funext r
      simp only [hK, hT, Set.indicator, Set.mem_ofPred_eq, Set.mem_Iio]
    have e2 : Ioo 0 s ∩ Iio t = Ioo 0 t := by
      ext r
      simp only [mem_inter_iff, mem_Ioo, mem_Iio]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩
        exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, h2.trans ht.2⟩, h2⟩
    rw [e1, hμ, setIntegral_indicator measurableSet_Iio, e2, integral_smul]
  have h2 : ∀ r ∈ Ioo 0 s, ∫ t, K (t, r) ∂μ = (χ s - χ r) • Φ r := by
    intro r hr
    have e1 : (fun t => K (t, r)) = (Ioi r).indicator fun t => χ' t • Φ r := by
      funext t
      simp only [hK, hT, Set.indicator, Set.mem_ofPred_eq, Set.mem_Ioi]
    have e2 : Ioo 0 s ∩ Ioi r = Ioo r s := by
      ext t
      simp only [mem_inter_iff, mem_Ioo, mem_Ioi]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩
        exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨hr.1.trans h1, h2⟩, h1⟩
    rw [e1, hμ, setIntegral_indicator measurableSet_Ioi, e2, integral_smul_const]
    congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.2.le,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hχ x)
        (hχ'c.intervalIntegrable _ _)]
  refine ⟨?_, ?_⟩
  · have hi := hKint.integral_prod_left
    refine hi.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact h1 t ht
  · calc ∫ t in Ioo 0 s, χ' t • ∫ r in Ioo 0 t, Φ r = ∫ t, ∫ r, K (t, r) ∂μ ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
          exact (h1 t ht).symm
      _ = ∫ r, ∫ t, K (t, r) ∂μ ∂μ := integral_integral_swap hKint
      _ = ∫ r in Ioo 0 s, (χ s - χ r) • Φ r := by
          refine integral_congr_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
          exact h2 r hr

/-! ## The cutoff identity -/

/-- **Cutoff identity** (tex lines 3788–3792, `μ = 0`): for `u = duhamel ν g`, a cutoff `χ`
with continuous derivative `χ'`, `|χ| ≤ 1`, `|χ'| ≤ M`, and a point `z` with
`∫_0^s heatAbs_{ν(s-t)} g(t) (z) dt < ∞`,
`∫_0^s e^{ν(s-t)Δ}[χ(t) g(t) + χ'(t) u(t)] dt (z) = χ(s) u(s)(z)`. -/
theorem duhamel_cutoff {ν : ℝ} (hν : 0 < ν) {g : ℝ → Plane → Plane}
    (hg : StronglyMeasurable (Function.uncurry g)) {χ χ' : ℝ → ℝ}
    (hχ : ∀ t, HasDerivAt χ (χ' t) t) (hχc : Continuous χ) (hχ'c : Continuous χ')
    (hχb : ∀ t, |χ t| ≤ 1) {M : ℝ} (hM : ∀ t, |χ' t| ≤ M) {s : ℝ} {z : Plane}
    (hA : ∫⁻ t in Ioo 0 s, heatAbs (ν * (s - t)) (g t) z ≠ ⊤) :
    duhamel ν (fun t x => χ t • g t x + χ' t • duhamel ν g t x) s z =
      χ s • duhamel ν g s z := by
  set u := duhamel ν g with hu
  set Ψ : ℝ → Plane := fun t => heat (ν * (s - t)) (g t) z with hΨ
  have hum : StronglyMeasurable (Function.uncurry u) := stronglyMeasurable_duhamel hg
  have ha : ∀ t ∈ Ioo 0 s, ∫⁻ r in Ioo 0 t, heatAbs (ν * (s - t) + ν * (t - r)) (g r) z ≤
      ∫⁻ t in Ioo 0 s, heatAbs (ν * (s - t)) (g t) z := by
    intro t ht
    calc ∫⁻ r in Ioo 0 t, heatAbs (ν * (s - t) + ν * (t - r)) (g r) z
        = ∫⁻ r in Ioo 0 t, heatAbs (ν * (s - r)) (g r) z := by
          refine setLIntegral_congr_fun measurableSet_Ioo fun r _ => ?_
          congr 1
          ring
      _ ≤ ∫⁻ t in Ioo 0 s, heatAbs (ν * (s - t)) (g t) z :=
          lintegral_mono_set (Ioo_subset_Ioo_right ht.2.le)
  have hb : ∀ t ∈ Ioo 0 s, heatAbs (ν * (s - t)) (u t) z ≠ ⊤ := fun t ht =>
    (((heatAbs_duhamel_le hν (mul_pos hν (sub_pos.2 ht.2)) hg t z).trans (ha t ht)).trans_lt
      (lt_top_iff_ne_top.2 hA)).ne
  have hae : ∀ᵐ t ∂(volume.restrict (Ioo 0 s)), heatAbs (ν * (s - t)) (g t) z < ⊤ :=
    ae_lt_top (measurable_heatAbs_age (fun t => ν * (s - t))
      (measurable_const.mul (measurable_const.sub measurable_id)) hg z) hA
  have hc : ∀ᵐ t ∂(volume.restrict (Ioo 0 s)),
      heat (ν * (s - t)) (fun x => χ t • g t x + χ' t • u t x) z =
        χ t • Ψ t + χ' t • ∫ r in Ioo 0 t, Ψ r := by
    filter_upwards [hae, ae_restrict_mem measurableSet_Ioo] with t ht hts
    have hpos : 0 < ν * (s - t) := mul_pos hν (sub_pos.2 hts.2)
    rw [heat_add_smul hpos (stronglyMeasurable_slice hg t).aestronglyMeasurable
      (stronglyMeasurable_slice hum t).aestronglyMeasurable (χ t) (χ' t) ht.ne (hb t hts)]
    congr 2
    rw [hu, heat_duhamel hν hpos hg ((ha t hts).trans_lt (lt_top_iff_ne_top.2 hA)).ne]
    refine setIntegral_congr_fun measurableSet_Ioo fun r _ => ?_
    simp only [hΨ]
    congr 1
    ring
  have hΨi : IntegrableOn Ψ (Ioo 0 s) := by
    refine ⟨(stronglyMeasurable_heat_age hg z).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    calc ∫⁻ t in Ioo 0 s, ‖Ψ t‖ₑ ≤ ∫⁻ t in Ioo 0 s, heatAbs (ν * (s - t)) (g t) z :=
          setLIntegral_mono' measurableSet_Ioo fun t ht =>
            enorm_heat_le (mul_pos hν (sub_pos.2 ht.2)) _ z
      _ < ⊤ := lt_top_iff_ne_top.2 hA
  obtain ⟨hint2, htri⟩ := integral_deriv_smul_primitive hχ hχ'c hM hΨi
  have hint1 : IntegrableOn (fun t => χ t • Ψ t) (Ioo 0 s) := by
    refine Integrable.mono hΨi (hχc.measurable.aestronglyMeasurable.smul
      hΨi.aestronglyMeasurable) (Eventually.of_forall fun t => ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (hχb t)
  have hint3 : IntegrableOn (fun r => (χ s - χ r) • Ψ r) (Ioo 0 s) := by
    have h := (hΨi.smul (χ s)).sub hint1
    refine h.congr (Eventually.of_forall fun r => ?_)
    simp only [Pi.sub_apply, Pi.smul_apply, sub_smul]
  calc duhamel ν (fun t x => χ t • g t x + χ' t • u t x) s z
      = ∫ t in Ioo 0 s, (χ t • Ψ t + χ' t • ∫ r in Ioo 0 t, Ψ r) := integral_congr_ae hc
    _ = (∫ t in Ioo 0 s, χ t • Ψ t) + ∫ t in Ioo 0 s, χ' t • ∫ r in Ioo 0 t, Ψ r :=
        integral_add hint1 hint2
    _ = (∫ t in Ioo 0 s, χ t • Ψ t) + ∫ r in Ioo 0 s, (χ s - χ r) • Ψ r := by rw [htri]
    _ = ∫ r in Ioo 0 s, (χ r • Ψ r + (χ s - χ r) • Ψ r) := (integral_add hint1 hint3).symm
    _ = ∫ r in Ioo 0 s, χ s • Ψ r := by
        refine integral_congr_ae (Eventually.of_forall fun r => ?_)
        simp only
        rw [← add_smul]
        congr 1
        ring
    _ = χ s • u s z := by
        rw [integral_smul]
        rfl

end UnforcedLeray.B0289
