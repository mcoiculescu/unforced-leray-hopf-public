import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_1

/-!
# Part III-a, task `PartIII-a:T18/3/1/1/4`: `L²` bounds for `q`-integrals and `q`-primitives

Target: `DfcQL2` (`Sub/T18_3_1_1.lean`): for `c > 0` and a continuous `f` with `f ∈ L²(cell)`,
`η ↦ ∫_{-c/2}^{c/2} f(t, η) dt` is in `L²(ℝ)` and `(q, η) ↦ ∫_{-c/2}^{q} f(t, η) dt` is in
`L²(cell)`. Source of record: `the November 2 reference manuscript` (the
divergence-free density argument, cited in `Sub/T18_3_1.lean`).

Mathematics (`a = -(c/2)`, `b = c/2`, `H(η) = ∫_a^b f(t,η)² dt` as a lintegral):

* Cauchy-Schwarz on an interval for a continuous `g`: `(∫_a^q g)² ≤ (q - a) ∫_a^q g²`
  (`ql2_cs`), proved from `∫ (g - k)² ≥ 0` with `k = I/(q - a)`; in ENNReal form
  (`ql2_ofReal_interval`).
* For `q ∈ [a, b]` and every `η`: `ofReal((∫_a^q f(t,η))²) ≤ ofReal c · H(η)` (`ql2_bound`), since
  `q - a ≤ c` and `Ioc a q ⊆ Ioc a b`.
* Tonelli on the cell: `∫⁻_η H(η) = ∫⁻_{cell} ofReal(f²) < ∞` (`ql2_lintegral_H`).
* `q`-integral: `∫⁻_η ofReal(Q²) ≤ ofReal c · ∫⁻ H < ∞`.
* `q`-primitive: `∫⁻_{cell} ofReal(P²) ≤ ofReal c · ∫⁻_{cell} H(η) = ofReal c² · ∫⁻ H < ∞`.
* Measurability: `dfcQInt` and `dfcQPrim` are continuous (parametric interval integrals of a
  continuous integrand); `H` is measurable (`Measurable.lintegral_prod_right'`).

Helpers are prefixed `ql2`; everything lives in this one file.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Cauchy-Schwarz on an interval for a continuous integrand:
`(∫_a^q g)² ≤ (q - a) ∫_a^q g²`. -/
theorem ql2_cs {g : ℝ → ℝ} (hg : Continuous g) {a q : ℝ} (haq : a ≤ q) :
    (∫ t in a..q, g t) ^ 2 ≤ (q - a) * ∫ t in a..q, g t ^ 2 := by
  rcases eq_or_lt_of_le haq with h | h
  · subst h
    simp
  have hL : 0 < q - a := sub_pos.mpr h
  obtain ⟨I, hI⟩ : ∃ I : ℝ, I = ∫ t in a..q, g t := ⟨_, rfl⟩
  obtain ⟨J, hJ⟩ : ∃ J : ℝ, J = ∫ t in a..q, g t ^ 2 := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = I / (q - a) := ⟨_, rfl⟩
  have hkL : k * (q - a) = I := by
    rw [hk]
    exact div_mul_cancel₀ I hL.ne'
  have hnn : 0 ≤ ∫ t in a..q, (g t - k) ^ 2 :=
    intervalIntegral.integral_nonneg haq (fun t _ => sq_nonneg _)
  have i1 : IntervalIntegrable (fun t => g t ^ 2) volume a q :=
    (hg.pow 2).intervalIntegrable a q
  have i2 : IntervalIntegrable (fun t => 2 * k * g t) volume a q :=
    (hg.const_mul _).intervalIntegrable a q
  have i3 : IntervalIntegrable (fun _ : ℝ => k ^ 2) volume a q := intervalIntegrable_const
  have hexp : ∫ t in a..q, (g t - k) ^ 2 = J - 2 * k * I + k ^ 2 * (q - a) := by
    have h1 : ∀ t, (g t - k) ^ 2 = g t ^ 2 - 2 * k * g t + k ^ 2 := fun t => by ring
    simp_rw [h1]
    rw [intervalIntegral.integral_add (i1.sub i2) i3, intervalIntegral.integral_sub i1 i2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, ← hI, ← hJ]
    simp only [smul_eq_mul]
    ring
  have hk2 : k ^ 2 * (q - a) = k * I := by
    rw [← hkL]
    ring
  have hkIJ : k * I ≤ J := by
    have h0 : 0 ≤ J - 2 * k * I + k ^ 2 * (q - a) := by
      rw [← hexp]
      exact hnn
    nlinarith [hk2, h0]
  have hfin : I ^ 2 = (q - a) * (k * I) := by
    rw [← hkL]
    ring
  rw [← hI, ← hJ, hfin]
  exact mul_le_mul_of_nonneg_left hkIJ hL.le

/-- ENNReal form of the interval Cauchy-Schwarz:
`ofReal((∫_a^q g)²) ≤ ofReal(q - a) · ∫⁻_{(a,q]} g²`. -/
theorem ql2_ofReal_interval {g : ℝ → ℝ} (hg : Continuous g) {a q : ℝ} (haq : a ≤ q) :
    ENNReal.ofReal ((∫ t in a..q, g t) ^ 2) ≤
      ENNReal.ofReal (q - a) * ∫⁻ t in Ioc a q, ENNReal.ofReal (g t ^ 2) := by
  have hi : IntegrableOn (fun t => g t ^ 2) (Ioc a q) := (hg.pow 2).integrableOn_Ioc
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc a q)] (fun t => g t ^ 2) :=
    ae_of_all _ (fun t => sq_nonneg _)
  have hint : ∫⁻ t in Ioc a q, ENNReal.ofReal (g t ^ 2) =
      ENNReal.ofReal (∫ t in a..q, g t ^ 2) := by
    rw [intervalIntegral.integral_of_le haq, ← ofReal_integral_eq_lintegral_ofReal hi hnn]
  rw [hint, ← ENNReal.ofReal_mul (sub_nonneg.mpr haq)]
  exact ENNReal.ofReal_le_ofReal (ql2_cs hg haq)

/-- The pointwise `L²` bound for the `q`-primitive, uniform in the upper limit `q` in the cell:
for `-c/2 ≤ q ≤ c/2`,
`ofReal((∫_{-c/2}^q f(t, η) dt)²) ≤ ofReal c · ∫⁻_{t ∈ (-c/2, c/2]} ofReal(f(t,η)²)`. -/
theorem ql2_bound {c : ℝ} {f : ℝ × ℝ → ℝ} (hf : Continuous f) {η q : ℝ}
    (hq : -(c / 2) ≤ q) (hqb : q ≤ c / 2) :
    ENNReal.ofReal ((∫ t in (-(c / 2))..q, f (t, η)) ^ 2) ≤
      ENNReal.ofReal c * ∫⁻ t in Ioc (-(c / 2)) (c / 2), ENNReal.ofReal (f (t, η) ^ 2) := by
  have hg : Continuous (fun t => f (t, η)) := hf.comp (continuous_id.prodMk continuous_const)
  refine (ql2_ofReal_interval hg hq).trans ?_
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) ?_
  · linarith
  · exact lintegral_mono_set (Ioc_subset_Ioc_right hqb)

/-- The `q`-integral is continuous in `η`. -/
theorem ql2_cont_Q {c : ℝ} {f : ℝ × ℝ → ℝ} (hf : Continuous f) :
    Continuous (dfcQInt c f) := by
  have hF : Continuous (Function.uncurry fun (η : ℝ) (t : ℝ) => f (t, η)) :=
    hf.comp (continuous_snd.prodMk continuous_fst)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
    hF _ _

/-- The `q`-primitive is continuous in `(q, η)`. -/
theorem ql2_cont_P {c : ℝ} {f : ℝ × ℝ → ℝ} (hf : Continuous f) :
    Continuous (dfcQPrim c f) := by
  have hF : Continuous (Function.uncurry fun (x : ℝ × ℝ) (t : ℝ) => f (t, x.2)) :=
    hf.comp (continuous_snd.prodMk (continuous_snd.comp continuous_fst))
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (μ := volume)
    (a₀ := -(c / 2)) hF continuous_fst

/-- The inner `t`-integral of `ofReal(f²)` over one period, as a function of `η`. -/
def ql2H (c : ℝ) (f : ℝ × ℝ → ℝ) (η : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioc (-(c / 2)) (c / 2), ENNReal.ofReal (f (t, η) ^ 2)

theorem ql2_meas_swap {f : ℝ × ℝ → ℝ} (hf : Continuous f) :
    Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (f (p.2, p.1) ^ 2)) :=
  (ENNReal.continuous_ofReal.comp ((hf.comp continuous_swap).pow 2)).measurable

theorem ql2H_measurable {c : ℝ} {f : ℝ × ℝ → ℝ} (hf : Continuous f) :
    Measurable (ql2H c f) :=
  Measurable.lintegral_prod_right' (ql2_meas_swap hf)

/-- Integration over the cell `[-c/2, c/2) × ℝ` as an iterated integral, `q` outside. -/
theorem ql2_cell_prod {c : ℝ} (G : ℝ × ℝ → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ x in B0579.cell c, G x =
      ∫⁻ q in Ico (-(c / 2)) (c / 2), ∫⁻ η, G (q, η) := by
  have key : volume.restrict (B0579.cell c) =
      (volume.restrict (Ico (-(c / 2)) (c / 2))).prod volume := by
    rw [B0579.cell, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  rw [key, lintegral_prod G hG.aemeasurable]

/-- Tonelli: `∫⁻_η H(η) = ∫⁻_{cell} ofReal(f²)`. -/
theorem ql2_lintegral_H {c : ℝ} {f : ℝ × ℝ → ℝ} (hf : Continuous f) :
    ∫⁻ η, ql2H c f η = ∫⁻ x in B0579.cell c, ENNReal.ofReal (f x ^ 2) := by
  have hm : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (f (p.2, p.1) ^ 2)) :=
    ql2_meas_swap hf
  have hm' : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (f p ^ 2)) :=
    ENNReal.continuous_ofReal.comp (hf.pow 2) |>.measurable
  calc ∫⁻ η, ql2H c f η
      = ∫⁻ η, ∫⁻ t in Ico (-(c / 2)) (c / 2), ENNReal.ofReal (f (t, η) ^ 2) := by
        refine lintegral_congr fun η => ?_
        exact (setLIntegral_congr Ico_ae_eq_Ioc).symm
    _ = ∫⁻ t in Ico (-(c / 2)) (c / 2), ∫⁻ η, ENNReal.ofReal (f (t, η) ^ 2) :=
        lintegral_lintegral_swap (f := fun η t => ENNReal.ofReal (f (t, η) ^ 2))
          hm.aemeasurable
    _ = ∫⁻ x in B0579.cell c, ENNReal.ofReal (f x ^ 2) :=
        (ql2_cell_prod (fun x => ENNReal.ofReal (f x ^ 2)) hm').symm

/-- `H` integrated over the cell (the `q`-direction contributes the length `c`). -/
theorem ql2_cell_H {c : ℝ} {f : ℝ × ℝ → ℝ} (hf : Continuous f) :
    ∫⁻ x in B0579.cell c, ql2H c f x.2 = ENNReal.ofReal c * ∫⁻ η, ql2H c f η := by
  rw [ql2_cell_prod (fun x => ql2H c f x.2) ((ql2H_measurable hf).comp measurable_snd)]
  simp only [setLIntegral_const]
  rw [Real.volume_Ico]
  have hlen : c / 2 - -(c / 2) = c := by ring
  rw [hlen, mul_comm]

/-- **Target** `PartIII-a:T18/3/1/1/4`: the `L²` bounds for `q`-integrals and `q`-primitives. -/
theorem dfcQL2 : UnforcedLeray.Short.IIIa.DfcQL2 := by
  unfold UnforcedLeray.Short.IIIa.DfcQL2
  intro c hc f hf hL2
  have hcell : ∫⁻ x in B0579.cell c, ENNReal.ofReal (f x ^ 2) < ⊤ := by
    have h := hL2.integrable_sq
    exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => sq_nonneg _)).mp
      h.hasFiniteIntegral
  have hHint : ∫⁻ η, ql2H c f η < ⊤ := by
    rw [ql2_lintegral_H hf]
    exact hcell
  have hq1 : -(c / 2) ≤ c / 2 := by linarith
  constructor
  · -- the `q`-integral
    have hQc : Continuous (dfcQInt c f) := ql2_cont_Q hf
    rw [memLp_two_iff_integrable_sq hQc.aestronglyMeasurable]
    refine ⟨(hQc.pow 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun η => sq_nonneg _)]
    calc ∫⁻ η, ENNReal.ofReal (dfcQInt c f η ^ 2)
        ≤ ∫⁻ η, ENNReal.ofReal c * ql2H c f η :=
          lintegral_mono fun η => ql2_bound hf hq1 le_rfl
      _ = ENNReal.ofReal c * ∫⁻ η, ql2H c f η :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hHint
  · -- the `q`-primitive on the cell
    have hPc : Continuous (dfcQPrim c f) := ql2_cont_P hf
    rw [memLp_two_iff_integrable_sq hPc.aestronglyMeasurable]
    refine ⟨(hPc.pow 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => sq_nonneg _)]
    have hbound : ∀ x ∈ B0579.cell c,
        ENNReal.ofReal (dfcQPrim c f x ^ 2) ≤ ENNReal.ofReal c * ql2H c f x.2 := by
      intro x hx
      have hx' : x.1 ∈ Ico (-(c / 2)) (c / 2) := (Set.mem_prod.mp hx).1
      have hx'' := Set.mem_Ico.mp hx'
      exact ql2_bound (η := x.2) hf hx''.1 hx''.2.le
    calc ∫⁻ x in B0579.cell c, ENNReal.ofReal (dfcQPrim c f x ^ 2)
        ≤ ∫⁻ x in B0579.cell c, ENNReal.ofReal c * ql2H c f x.2 :=
          setLIntegral_mono' (B0579.measurableSet_cell c) hbound
      _ = ENNReal.ofReal c * ∫⁻ x in B0579.cell c, ql2H c f x.2 :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal c * (ENNReal.ofReal c * ∫⁻ η, ql2H c f η) := by
          rw [ql2_cell_H hf]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hHint)

end UnforcedLeray.Short.IIIa
