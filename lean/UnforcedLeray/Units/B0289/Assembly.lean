import UnforcedLeray.Units.B0289.Dyadic

/-!
# B0289: assembly of the free graph bound

Unit B0289 (tex lines 4771–4775), proof of tex lines 3772–3819 for the flat map at `μ = 0`:

* `flatInverse_eq_duhamel_of_ae`: `T̄F` is the Duhamel integral of a periodic measurable
  version `Ĝ` of `t ↦ 𝕡₀(F(t)/t)`;
* `NG_bound`, `ae_lintegral_lt_top`, `ae_heatAbs_lt_top`: the Leray bound in age, and the
  finiteness of the absolute Duhamel integral for almost every `(s, z)`;
* `source_norm_le`: the cutoff source `χ Ĝ + χ' T̄F` on one dyadic window is bounded by
  `1_{[a/2,4a)} a^{-1} (2 t ‖Ĝ(t)‖ + M ‖T̄F(t)‖)` (tex lines 3792–3795);
* `exists_D2`: the weighted second-derivative bound `‖ν s D² T̄F‖_{H_p} ≤ 384 C ‖Z‖` from
  `CylHeatMaxReg` on every dyadic window (tex lines 3795–3804);
* `exists_D1`: the first derivatives from `CylGradInterp` (tex lines 3811–3815).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Real
open scoped NNReal ENNReal

namespace UnforcedLeray.B0289

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.B0284

/-! ## Cutoff facts -/

theorem abs_chi_le_one (a t : ℝ) : |chi a t| ≤ 1 := by
  show |cutoff (t / a)| ≤ 1
  exact abs_le.2 ⟨by linarith [cutoff_nonneg (t / a)], cutoff_le_one _⟩

theorem abs_chiD_le {a : ℝ} (ha : 0 < a) (t : ℝ) : |chiD a t| ≤ cutoffBound / a := by
  rw [chiD, abs_div, abs_of_pos ha]
  exact div_le_div_of_nonneg_right (abs_cutoffD_le _) ha.le

theorem chi_eq_one {a s : ℝ} (ha : 0 < a) (hs : s ∈ Ico a (2 * a)) : chi a s = 1 := by
  refine cutoff_eq_one ?_ ?_
  · rw [le_div_iff₀ ha]
    linarith [hs.1]
  · rw [div_le_iff₀ ha]
    linarith [hs.2]

theorem chi_eq_zero {a t : ℝ} (ha : 0 < a) (ht : t ∉ Ico (a / 2) (4 * a)) :
    chi a t = 0 ∧ chiD a t = 0 := by
  have h : t / a ∉ Icc (1 / 2) (5 / 2) := by
    intro h
    apply ht
    constructor
    · have h1 := h.1
      rw [le_div_iff₀ ha] at h1
      linarith
    · have h2 := h.2
      rw [div_le_iff₀ ha] at h2
      linarith
  refine ⟨cutoff_eq_zero fun h' => h (Ioo_subset_Icc_self h'), ?_⟩
  simp [chiD, cutoffD_eq_zero h]

/-! ## Measure-theoretic helpers -/

theorem restrict_ac_ageWeight (α : ℝ) : volume.restrict (Ioi (0 : ℝ)) ≪ ageWeight α := by
  unfold ageWeight
  refine withDensity_absolutelyContinuous'
    (ENNReal.measurable_ofReal.comp (measurable_id.pow_const α)).aemeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hs α)).ne'

theorem eLpNorm_sum_fintype_le {ι α : Type*} [Fintype ι] [MeasurableSpace α] {μ : Measure α}
    {p : ℝ≥0∞} (hp : 1 ≤ p) {f : ι → α → ℝ≥0∞} (hf : ∀ i, AEStronglyMeasurable (f i) μ) :
    eLpNorm (fun x => ∑ i, f i x) p μ ≤ ∑ i, eLpNorm (f i) p μ := by
  have h := eLpNorm_sum_le (s := Finset.univ) (fun i _ => hf i) hp
  rwa [Finset.sum_fn] at h

/-- Gluing countably many jointly measurable families along the dyadic index. -/
theorem stronglyMeasurable_glue {f : ℤ → ℝ → Plane → Plane}
    (hf : ∀ k, StronglyMeasurable (Function.uncurry (f k))) :
    StronglyMeasurable (Function.uncurry fun s z => f (dyIdx s) s z) := by
  have h1 : Measurable fun q : (ℝ × Plane) × ℤ => Function.uncurry (f q.2) q.1 :=
    measurable_from_prod_countable_left fun k => (hf k).measurable
  have h2 : Measurable fun q : ℝ × Plane => (q, dyIdx q.1) :=
    measurable_id.prodMk (measurable_dyIdx.comp measurable_fst)
  exact (h1.comp h2).stronglyMeasurable

/-! ## The flat inverse as a Duhamel integral of a measurable version -/

theorem flatInverse_eq_duhamel_of_ae {ν c : ℝ} (hν : 0 < ν) {F Ĝ : ℝ → Plane → Plane}
    (hĜ : ∀ᵐ t ∂(volume.restrict (Ioi 0)), Ĝ t =ᵐ[volume] flatLeray c (t⁻¹ • F t)) :
    flatInverse ν c F = duhamel ν Ĝ := by
  funext s z
  rw [flatInverse_eq_duhamel]
  unfold duhamel
  refine setIntegral_congr_ae measurableSet_Ioo ?_
  have h' := (ae_restrict_iff' measurableSet_Ioi).1 hĜ
  filter_upwards [h'] with t ht hts
  exact congrFun (heat_congr_ae (mul_pos hν (sub_pos.2 hts.2)) (ht hts.1)).symm z

/-- The Leray bound in age: `‖t ‖Ĝ(t)‖_p‖_{L^p(s^{a_p})} ≤ C ‖F‖_{H_p}` (B0284 step 2). -/
theorem NG_bound {c p : ℝ} (hp : 0 < p) {F Ĝ : ℝ → Plane → Plane} {CL : ℝ≥0}
    (hĜ : ∀ᵐ t ∂(volume.restrict (Ioi 0)), Ĝ t =ᵐ[volume] flatLeray c (t⁻¹ • F t))
    (hLeray : ∀ᵐ t ∂(volume.restrict (Ioi 0)),
      eLpNorm (flatLeray c (t⁻¹ • F t)) (ENNReal.ofReal p) (cellMeasure c) ≤
        CL * eLpNorm (t⁻¹ • F t) (ENNReal.ofReal p) (cellMeasure c)) :
    eLpNorm (fun t => ENNReal.ofReal t * eLpNorm (Ĝ t) (ENNReal.ofReal p) (cellMeasure c))
        (ENNReal.ofReal p) (ageWeight (p / 2 - 5 / 2)) ≤ CL * HpNorm c p F := by
  have hP0 : ENNReal.ofReal p ≠ 0 := by simp [hp]
  have hle : ∀ᵐ t ∂(ageWeight (p / 2 - 5 / 2)),
      ENNReal.ofReal t * eLpNorm (Ĝ t) (ENNReal.ofReal p) (cellMeasure c) ≤
        CL * eLpNorm (F t) (ENNReal.ofReal p) (cellMeasure c) := by
    have h1 := (ageWeight_ac (p / 2 - 5 / 2)).ae_le hLeray
    have h2 := (ageWeight_ac (p / 2 - 5 / 2)).ae_le hĜ
    filter_upwards [h1, h2, ae_ageWeight_pos (p / 2 - 5 / 2)] with t ht1 ht2 ht0
    rw [eLpNorm_congr_ae ((cellMeasure_ac c).ae_le ht2)]
    calc ENNReal.ofReal t * eLpNorm (flatLeray c (t⁻¹ • F t)) (ENNReal.ofReal p) (cellMeasure c)
        ≤ ENNReal.ofReal t * (CL * eLpNorm (t⁻¹ • F t) (ENNReal.ofReal p) (cellMeasure c)) := by
          gcongr
      _ = CL * eLpNorm (F t) (ENNReal.ofReal p) (cellMeasure c) := by
          rw [eLpNorm_const_smul, Real.enorm_of_nonneg (inv_nonneg.2 ht0.le)]
          rw [show ∀ a b d e : ℝ≥0∞, a * (b * (d * e)) = b * ((a * d) * e) by
              intro a b d e; ring,
            ← ENNReal.ofReal_mul ht0.le, mul_inv_cancel₀ ht0.ne', ENNReal.ofReal_one, one_mul]
  unfold HpNorm
  rw [← eLpNorm_const_mul_ennreal ENNReal.coe_ne_top _ hP0 ENNReal.ofReal_ne_top]
  refine eLpNorm_mono_enorm_ae ?_
  filter_upwards [hle] with t ht
  rw [enorm_eq_self, enorm_eq_self]
  exact ht

/-- `∫_0^s ψ < ∞` for almost every `s > 0` when `‖t ψ(t)‖_{L^p(s^{a_p})} < ∞` (Hardy). -/
theorem ae_lintegral_lt_top {p : ℝ} (hp1 : 1 ≤ p) (hp3 : p < 3) {ψ : ℝ → ℝ≥0∞}
    (hψ : Measurable ψ)
    (h : eLpNorm (fun t => ENNReal.ofReal t * ψ t) (ENNReal.ofReal p)
      (ageWeight (p / 2 - 5 / 2)) < ⊤) :
    ∀ᵐ s ∂(volume.restrict (Ioi 0)), ∫⁻ t in Ioo 0 s, ψ t < ⊤ := by
  have hp0 : 0 < p := by linarith
  have hφm : Measurable fun t => ENNReal.ofReal t * ψ t := ENNReal.measurable_ofReal.mul hψ
  have hH := eLpNorm_hardy_ageWeight_le hp1 hp3 hφm
  have hfin : eLpNorm (fun s => ∫⁻ u in Ioi 0, hardyKernel u *
      (ENNReal.ofReal (s * u) * ψ (s * u))) (ENNReal.ofReal p) (ageWeight (p / 2 - 5 / 2)) < ⊤ :=
    hH.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top h)
  have hmeasH : Measurable fun s => ∫⁻ u in Ioi 0, hardyKernel u *
      (ENNReal.ofReal (s * u) * ψ (s * u)) := by
    have hm : Measurable (Function.uncurry fun (s u : ℝ) =>
        hardyKernel u * (ENNReal.ofReal (s * u) * ψ (s * u))) :=
      (measurable_hardyKernel.comp measurable_snd).mul
        ((ENNReal.measurable_ofReal.comp (measurable_fst.mul measurable_snd)).mul
          (hψ.comp (measurable_fst.mul measurable_snd)))
    exact hm.lintegral_prod_right'
  have h1 := ae_lt_top_of_eLpNorm hp0 hmeasH.aemeasurable hfin
  filter_upwards [(restrict_ac_ageWeight (p / 2 - 5 / 2)).ae_le h1,
    ae_restrict_mem measurableSet_Ioi] with s hs hs0
  rw [lintegral_Ioo_eq_mellin hs0]
  exact hs

/-- For such `s`, the absolute Duhamel integral is finite at almost every point of the
plane. -/
theorem ae_heatAbs_lt_top {ν c p : ℝ} (hν : 0 < ν) (hc : 0 < c) (hp1 : 1 ≤ p)
    {Ĝ : ℝ → Plane → Plane} (hĜm : StronglyMeasurable (Function.uncurry Ĝ))
    (hĜper : ∀ t, IsQPeriodic c (Ĝ t)) {s : ℝ}
    (hs : ∫⁻ t in Ioo 0 s, eLpNorm (Ĝ t) (ENNReal.ofReal p) (cellMeasure c) < ⊤) :
    ∀ᵐ z ∂(volume : Measure Plane), ∫⁻ t in Ioo 0 s, heatAbs (ν * (s - t)) (Ĝ t) z < ⊤ := by
  have hp0 : 0 < p := by linarith
  have hP1 : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp1
  have hΦm : Measurable (Function.uncurry fun z t => heatAbs (ν * (s - t)) (Ĝ t) z) :=
    measurable_heatAbs_family hĜm ν s
  have hAm : Measurable fun z => ∫⁻ t in Ioo 0 s, heatAbs (ν * (s - t)) (Ĝ t) z :=
    hΦm.lintegral_prod_right'
  have hA : eLpNorm (fun z => ∫⁻ t in Ioo 0 s, heatAbs (ν * (s - t)) (Ĝ t) z)
      (ENNReal.ofReal p) (cellMeasure c) ≤
        ∫⁻ t in Ioo 0 s, eLpNorm (Ĝ t) (ENNReal.ofReal p) (cellMeasure c) := by
    calc eLpNorm (fun z => ∫⁻ t in Ioo 0 s, heatAbs (ν * (s - t)) (Ĝ t) z)
          (ENNReal.ofReal p) (cellMeasure c)
        ≤ ∫⁻ t in Ioo 0 s, eLpNorm (fun z => heatAbs (ν * (s - t)) (Ĝ t) z)
            (ENNReal.ofReal p) (cellMeasure c) :=
          NonUniqueEuler.Conv.eLpNorm_lintegral_le hΦm.aemeasurable hP1 ENNReal.ofReal_ne_top
      _ ≤ ∫⁻ t in Ioo 0 s, eLpNorm (Ĝ t) (ENNReal.ofReal p) (cellMeasure c) :=
          setLIntegral_mono' measurableSet_Ioo fun t ht =>
            eLpNorm_heatAbs_le hc (mul_pos hν (sub_pos.2 ht.2)) (hĜper t)
              (stronglyMeasurable_slice hĜm t).aestronglyMeasurable hP1 ENNReal.ofReal_ne_top
  have h1 := ae_lt_top_of_eLpNorm hp0 hAm.aemeasurable (hA.trans_lt hs)
  refine ae_of_ae_cellMeasure hc ?_ h1
  intro z
  have e : ∫⁻ t in Ioo 0 s, heatAbs (ν * (s - t)) (Ĝ t) (z.1 + c, z.2) =
      ∫⁻ t in Ioo 0 s, heatAbs (ν * (s - t)) (Ĝ t) z :=
    lintegral_congr fun t => heatAbs_periodic (hĜper t) z
  simp only
  rw [e]

/-! ## The cutoff source on one window -/

theorem source_norm_le {ν c p a : ℝ} (hp1 : 1 ≤ p) (ha : 0 < a) {Ĝ : ℝ → Plane → Plane}
    (hĜm : StronglyMeasurable (Function.uncurry Ĝ)) (t : ℝ) :
    eLpNorm (fun x => chi a t • Ĝ t x + chiD a t • duhamel ν Ĝ t x) (ENNReal.ofReal p)
        (cellMeasure c) ≤
      (Ico (a / 2) (4 * a)).indicator (fun t => ENNReal.ofReal a⁻¹ *
        (2 * (ENNReal.ofReal t * eLpNorm (Ĝ t) (ENNReal.ofReal p) (cellMeasure c)) +
          (cutoffBound : ℝ≥0∞) * eLpNorm (duhamel ν Ĝ t) (ENNReal.ofReal p) (cellMeasure c))) t := by
  have hP1 : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp1
  by_cases ht : t ∈ Ico (a / 2) (4 * a)
  · rw [Set.indicator_of_mem ht]
    have hG : AEStronglyMeasurable (Ĝ t) (cellMeasure c) :=
      (stronglyMeasurable_slice hĜm t).aestronglyMeasurable
    have hu : AEStronglyMeasurable (duhamel ν Ĝ t) (cellMeasure c) :=
      (stronglyMeasurable_slice (stronglyMeasurable_duhamel hĜm) t).aestronglyMeasurable
    have h1 : ‖chi a t‖ₑ ≤ ENNReal.ofReal a⁻¹ * (2 * ENNReal.ofReal t) := by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_ofNat 2,
        ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (inv_nonneg.2 ha.le)]
      refine ENNReal.ofReal_le_ofReal ((abs_chi_le_one a t).trans ?_)
      rw [← div_eq_inv_mul, le_div_iff₀ ha]
      linarith [ht.1]
    have h2 : ‖chiD a t‖ₑ ≤ ENNReal.ofReal a⁻¹ * cutoffBound := by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_coe_nnreal,
        ← ENNReal.ofReal_mul (inv_nonneg.2 ha.le)]
      refine ENNReal.ofReal_le_ofReal ((abs_chiD_le ha t).trans_eq ?_)
      rw [div_eq_inv_mul]
    have e : (fun x => chi a t • Ĝ t x + chiD a t • duhamel ν Ĝ t x) =
        chi a t • Ĝ t + chiD a t • duhamel ν Ĝ t := by
      funext x
      simp only [Pi.add_apply, Pi.smul_apply]
    rw [e]
    calc eLpNorm (chi a t • Ĝ t + chiD a t • duhamel ν Ĝ t) (ENNReal.ofReal p) (cellMeasure c)
        ≤ eLpNorm (chi a t • Ĝ t) (ENNReal.ofReal p) (cellMeasure c) +
            eLpNorm (chiD a t • duhamel ν Ĝ t) (ENNReal.ofReal p) (cellMeasure c) :=
          eLpNorm_add_le (hG.const_smul _) (hu.const_smul _) hP1
      _ = ‖chi a t‖ₑ * eLpNorm (Ĝ t) (ENNReal.ofReal p) (cellMeasure c) +
            ‖chiD a t‖ₑ * eLpNorm (duhamel ν Ĝ t) (ENNReal.ofReal p) (cellMeasure c) := by
          rw [eLpNorm_const_smul, eLpNorm_const_smul]
      _ ≤ ENNReal.ofReal a⁻¹ * (2 * ENNReal.ofReal t) *
              eLpNorm (Ĝ t) (ENNReal.ofReal p) (cellMeasure c) +
            ENNReal.ofReal a⁻¹ * cutoffBound *
              eLpNorm (duhamel ν Ĝ t) (ENNReal.ofReal p) (cellMeasure c) := by
          gcongr
      _ = _ := by ring
  · rw [Set.indicator_of_notMem ht]
    obtain ⟨h1, h2⟩ := chi_eq_zero ha ht
    simp [h1, h2]

/-! ## The second derivatives -/

/-- **The weighted second-derivative bound** (tex lines 3784–3810, `μ = 0`): from
`CylHeatMaxReg`, the Duhamel integral `u = duhamel ν Ĝ` has jointly measurable periodic weak
second derivatives with `‖ν s ∂_i∂_j u‖_{H_p} ≤ 384 C ‖Z‖_{L^p(s^{a_p})}`, where
`Z(t) = 2 t ‖Ĝ(t)‖_p + M ‖u(t)‖_p`. -/
theorem exists_D2 {ν c p : ℝ} (hν : 0 < ν) (hp1 : 1 ≤ p) (hp3 : p < 3)
    {Ĝ : ℝ → Plane → Plane} (hĜm : StronglyMeasurable (Function.uncurry Ĝ))
    (hĜper : ∀ t, IsQPeriodic c (Ĝ t))
    (hfinA : ∀ᵐ s ∂(volume.restrict (Ioi 0)), ∀ᵐ z ∂(volume : Measure Plane),
      ∫⁻ t in Ioo 0 s, heatAbs (ν * (s - t)) (Ĝ t) z < ⊤)
    {Z : ℝ → ℝ≥0∞}
    (hZdef : Z = fun t => 2 * (ENNReal.ofReal t * eLpNorm (Ĝ t) (ENNReal.ofReal p) (cellMeasure c)) +
        (cutoffBound : ℝ≥0∞) * eLpNorm (duhamel ν Ĝ t) (ENNReal.ofReal p) (cellMeasure c))
    (hZ : eLpNorm Z (ENNReal.ofReal p) (ageWeight (p / 2 - 5 / 2)) < ⊤)
    {CM : ℝ≥0} (hMR : CylHeatMaxReg ν c p CM) :
    ∃ D2 : Fin 2 → Fin 2 → ℝ → Plane → Plane,
      (∀ i j, StronglyMeasurable (Function.uncurry (D2 i j))) ∧
      (∀ i j s, IsQPeriodic c (D2 i j s)) ∧
      (∀ᵐ s ∂(volume.restrict (Ioi 0)), ∀ i j,
        Sob.HasWeakDeriv (Sob.cylinder c) [Sob.cylDir i, Sob.cylDir j] (duhamel ν Ĝ s)
          (D2 i j s)) ∧
      ∀ i j, HpNorm c p (fun s => (ν * s) • D2 i j s) ≤
        384 * CM * eLpNorm Z (ENNReal.ofReal p) (ageWeight (p / 2 - 5 / 2)) := by
  have hp0 : 0 < p := by linarith
  set h : ℤ → ℝ → Plane → Plane := fun k t x =>
    chi ((2 : ℝ) ^ k) t • Ĝ t x + chiD ((2 : ℝ) ^ k) t • duhamel ν Ĝ t x with hh
  have ha : ∀ k : ℤ, (0 : ℝ) < 2 ^ k := fun k => zpow_pos two_pos k
  have hY : ∀ k t, eLpNorm (h k t) (ENNReal.ofReal p) (cellMeasure c) ≤
      (Ico ((2 : ℝ) ^ k / 2) (4 * 2 ^ k)).indicator
        (fun t => ENNReal.ofReal ((2 : ℝ) ^ k)⁻¹ * Z t) t := by
    intro k t
    rw [hZdef]
    exact source_norm_le hp1 (ha k) hĜm t
  have hum := stronglyMeasurable_duhamel (ν := ν) hĜm
  have hhm : ∀ k, StronglyMeasurable (Function.uncurry (h k)) := by
    intro k
    have h1 : StronglyMeasurable fun q : ℝ × Plane => chi ((2 : ℝ) ^ k) q.1 :=
      ((continuous_chi _).measurable.comp measurable_fst).stronglyMeasurable
    have h2 : StronglyMeasurable fun q : ℝ × Plane => chiD ((2 : ℝ) ^ k) q.1 :=
      ((continuous_chiD _).measurable.comp measurable_fst).stronglyMeasurable
    exact (h1.smul hĜm).add (h2.smul hum)
  have hhper : ∀ k t, IsQPeriodic c (h k t) := by
    intro k t z
    simp only [hh]
    rw [hĜper t z, duhamel_periodic hĜper t z]
  have hhsupp : ∀ k, ∃ T₀ T₁ : ℝ, 0 < T₀ ∧ ∀ t, t ∉ Ioo T₀ T₁ → h k t = 0 := by
    intro k
    refine ⟨(2 : ℝ) ^ k / 4, 4 * 2 ^ k, by positivity, fun t ht => ?_⟩
    have ht' : t ∉ Ico ((2 : ℝ) ^ k / 2) (4 * 2 ^ k) := fun h' =>
      ht ⟨by linarith [h'.1, ha k], h'.2⟩
    obtain ⟨h1, h2⟩ := chi_eq_zero (ha k) ht'
    funext x
    simp [hh, h1, h2]
  have hZint : ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (p / 2 - 5 / 2)) * Z t ^ p =
      eLpNorm Z (ENNReal.ofReal p) (ageWeight (p / 2 - 5 / 2)) ^ p := by
    rw [eLpNorm_ageWeight _ hp0, ← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne',
      ENNReal.rpow_one]
    simp only [enorm_eq_self]
  have hZfin : ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (p / 2 - 5 / 2)) * Z t ^ p < ⊤ := by
    rw [hZint]
    exact ENNReal.rpow_lt_top_of_nonneg hp0.le hZ.ne
  have hstp : ∀ k, stNorm c p (h k) ^ p =
      ∫⁻ t in Ioi 0, eLpNorm (h k t) (ENNReal.ofReal p) (cellMeasure c) ^ p := by
    intro k
    unfold stNorm
    rw [eLpNorm_ofReal_rpow hp0]
    simp only [enorm_eq_self]
  have hhfin : ∀ k, stNorm c p (h k) < ⊤ := by
    intro k
    have hw := window_source hp1 hp3 (ha k) (hY k)
    have hpos : ENNReal.ofReal (((2 : ℝ) ^ k) ^ (p / 2 - 5 / 2 + p)) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos (ha k) _)).ne'
    have hsub : Ico ((2 : ℝ) ^ k / 2) (4 * 2 ^ k) ⊆ Ioi 0 := fun t ht =>
      lt_of_lt_of_le (by linarith [ha k]) ht.1
    have h2 : ENNReal.ofReal (((2 : ℝ) ^ k) ^ (p / 2 - 5 / 2 + p)) *
        ∫⁻ t in Ioi 0, eLpNorm (h k t) (ENNReal.ofReal p) (cellMeasure c) ^ p < ⊤ :=
      hw.trans_lt (ENNReal.mul_lt_top (by norm_num)
        ((lintegral_mono_set hsub).trans_lt hZfin))
    rw [← ENNReal.rpow_lt_top_iff_of_pos hp0, hstp]
    exact ENNReal.lt_top_of_mul_ne_top_right h2.ne hpos
  have hex : ∀ k, ∃ D2 : Fin 2 → Fin 2 → ℝ → Plane → Plane,
      (∀ i j, StronglyMeasurable (Function.uncurry (D2 i j))) ∧
      (∀ i j s, IsQPeriodic c (D2 i j s)) ∧
      (∀ᵐ s ∂(volume.restrict (Ioi 0)), ∀ i j,
        Sob.HasWeakDeriv (Sob.cylinder c) [Sob.cylDir i, Sob.cylDir j] (duhamel ν (h k) s)
          (D2 i j s)) ∧
      ∀ i j, stNorm c p (fun s => ν • D2 i j s) ≤ CM * stNorm c p (h k) :=
    fun k => hMR (h k) (hhm k) (hhper k) (hhsupp k) (hhfin k)
  choose D2f hD2m hD2per hD2w hD2b using hex
  refine ⟨fun i j s => D2f (dyIdx s) i j s, fun i j => stronglyMeasurable_glue
    (f := fun k => D2f k i j) (fun k => hD2m k i j), fun i j s => hD2per (dyIdx s) i j s, ?_, ?_⟩
  · have hwk : ∀ k : ℤ, ∀ᵐ s ∂(volume.restrict (Ioi 0)), s ∈ W k → ∀ i j,
        Sob.HasWeakDeriv (Sob.cylinder c) [Sob.cylDir i, Sob.cylDir j] (duhamel ν Ĝ s)
          (D2f k i j s) := by
      intro k
      filter_upwards [hD2w k, hfinA] with s hs hsA hsW
      have hsW' : s ∈ Ico ((2 : ℝ) ^ k) (2 * 2 ^ k) := by rw [← W_eq]; exact hsW
      have hae : duhamel ν (h k) s =ᵐ[volume] duhamel ν Ĝ s := by
        filter_upwards [hsA] with z hz
        have e := duhamel_cutoff hν hĜm (hasDerivAt_chi ((2 : ℝ) ^ k))
          (continuous_chi _) (continuous_chiD _) (abs_chi_le_one _) (abs_chiD_le (ha k)) hz.ne
        rw [chi_eq_one (ha k) hsW', one_smul] at e
        exact e
      intro i j
      exact (hs i j).congr_ae (ae_restrict_of_ae hae) (ae_of_all _ fun _ => rfl)
    filter_upwards [ae_all_iff.2 hwk, ae_restrict_mem measurableSet_Ioi] with s hs hs0 i j
    exact hs (dyIdx s) (mem_W_dyIdx hs0) i j
  · intro i j
    have hwin : ∀ k : ℤ, ∫⁻ s in W k, ENNReal.ofReal (s ^ (p / 2 - 5 / 2)) *
        eLpNorm ((ν * s) • D2f (dyIdx s) i j s) (ENNReal.ofReal p) (cellMeasure c) ^ p ≤
          128 * (CM : ℝ≥0∞) ^ p * ∫⁻ t in E k, ENNReal.ofReal (t ^ (p / 2 - 5 / 2)) * Z t ^ p := by
      intro k
      have hX : ∫⁻ s in W k, ENNReal.ofReal (s ^ (p / 2 - 5 / 2)) *
          eLpNorm ((ν * s) • D2f (dyIdx s) i j s) (ENNReal.ofReal p) (cellMeasure c) ^ p =
            ∫⁻ s in Ico ((2 : ℝ) ^ k) (2 * 2 ^ k), ENNReal.ofReal (s ^ (p / 2 - 5 / 2)) *
              (ENNReal.ofReal (ν * s) *
                eLpNorm (D2f k i j s) (ENNReal.ofReal p) (cellMeasure c)) ^ p := by
        rw [← W_eq k]
        refine setLIntegral_congr_fun (measurableSet_W k) fun s hs => ?_
        rw [dyIdx_eq hs, eLpNorm_const_smul,
          Real.enorm_of_nonneg (mul_nonneg hν.le (W_subset_Ioi k hs).le)]
      rw [hX]
      refine window_D2 hp1 hp3 (ha k) hν ?_ (hY k)
      have hb' := ENNReal.rpow_le_rpow (hD2b k i j) hp0.le
      rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, hstp k] at hb'
      unfold stNorm at hb'
      rw [eLpNorm_ofReal_rpow hp0] at hb'
      simpa only [enorm_eq_self, eLpNorm_const_smul, Real.enorm_of_nonneg hν.le] using hb'
    have hsum := lintegral_Ioi_le_of_windows hwin
    have hHp : HpNorm c p (fun s => (ν * s) • D2f (dyIdx s) i j s) =
        (∫⁻ s in Ioi 0, ENNReal.ofReal (s ^ (p / 2 - 5 / 2)) *
          eLpNorm ((ν * s) • D2f (dyIdx s) i j s) (ENNReal.ofReal p) (cellMeasure c) ^ p) ^
            (1 / p) := by
      unfold HpNorm
      rw [eLpNorm_ageWeight _ hp0]
      simp only [enorm_eq_self]
    have h384 : (384 : ℝ≥0∞) ^ (1 / p) ≤ 384 := by
      calc (384 : ℝ≥0∞) ^ (1 / p) ≤ 384 ^ (1 : ℝ) :=
            ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
              (by rw [div_le_one hp0]; exact hp1)
        _ = 384 := ENNReal.rpow_one _
    rw [hHp]
    calc (∫⁻ s in Ioi 0, ENNReal.ofReal (s ^ (p / 2 - 5 / 2)) *
          eLpNorm ((ν * s) • D2f (dyIdx s) i j s) (ENNReal.ofReal p) (cellMeasure c) ^ p) ^
            (1 / p)
        ≤ (3 * (128 * (CM : ℝ≥0∞) ^ p) *
            ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (p / 2 - 5 / 2)) * Z t ^ p) ^ (1 / p) :=
          ENNReal.rpow_le_rpow hsum (by positivity)
      _ = (384 : ℝ≥0∞) ^ (1 / p) *
            (CM * eLpNorm Z (ENNReal.ofReal p) (ageWeight (p / 2 - 5 / 2))) := by
          rw [hZint, show (3 : ℝ≥0∞) * (128 * (CM : ℝ≥0∞) ^ p) *
              eLpNorm Z (ENNReal.ofReal p) (ageWeight (p / 2 - 5 / 2)) ^ p =
                384 * (CM * eLpNorm Z (ENNReal.ofReal p) (ageWeight (p / 2 - 5 / 2))) ^ p by
              rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le]; ring,
            ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
            mul_one_div_cancel hp0.ne', ENNReal.rpow_one]
      _ ≤ 384 * (CM * eLpNorm Z (ENNReal.ofReal p) (ageWeight (p / 2 - 5 / 2))) := by
          gcongr
      _ = 384 * CM * eLpNorm Z (ENNReal.ofReal p) (ageWeight (p / 2 - 5 / 2)) := by ring

/-! ## The first derivatives -/

/-- **The gradient bound** (tex lines 3811–3815): from `CylGradInterp`,
`‖√(ν s) ∂_i u‖_{H_p} ≤ C (‖u‖_{H_p} + Σ_{k,l} ‖ν s ∂_k∂_l u‖_{H_p})`. -/
theorem exists_D1 {ν c p : ℝ} (hν : 0 < ν) (hp1 : 1 ≤ p) {u : ℝ → Plane → Plane}
    (hum : StronglyMeasurable (Function.uncurry u)) (huper : ∀ s, IsQPeriodic c (u s))
    (hu : HpNorm c p u < ⊤) {D2 : Fin 2 → Fin 2 → ℝ → Plane → Plane}
    (hD2m : ∀ i j, StronglyMeasurable (Function.uncurry (D2 i j)))
    (hD2per : ∀ i j s, IsQPeriodic c (D2 i j s))
    (hD2w : ∀ᵐ s ∂(volume.restrict (Ioi 0)), ∀ i j,
      Sob.HasWeakDeriv (Sob.cylinder c) [Sob.cylDir i, Sob.cylDir j] (u s) (D2 i j s))
    (hD2b : ∀ i j, HpNorm c p (fun s => (ν * s) • D2 i j s) < ⊤)
    {CI : ℝ≥0} (hGI : CylGradInterp c p CI) :
    ∃ D1 : Fin 2 → ℝ → Plane → Plane, (∀ i s, IsQPeriodic c (D1 i s)) ∧
      (∀ᵐ s ∂(volume.restrict (Ioi 0)), ∀ i,
        Sob.HasWeakDeriv (Sob.cylinder c) [Sob.cylDir i] (u s) (D1 i s)) ∧
      ∀ i, HpNorm c p (fun s => Real.sqrt (ν * s) • D1 i s) ≤
        CI * (HpNorm c p u + ∑ k, ∑ l, HpNorm c p (fun s => (ν * s) • D2 k l s)) := by
  have hp0 : 0 < p := by linarith
  have hP0 : ENNReal.ofReal p ≠ 0 := by simp [hp0]
  have hP1 : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp1
  have hac := restrict_ac_ageWeight (p / 2 - 5 / 2)
  have hNum : Measurable fun s => eLpNorm (u s) (ENNReal.ofReal p) (cellMeasure c) :=
    measurable_eLpNorm_slice hum c hP0 ENNReal.ofReal_ne_top
  have hm2 : ∀ k l, StronglyMeasurable (Function.uncurry fun s => (ν * s) • D2 k l s) := by
    intro k l
    have h := ((measurable_const.mul measurable_fst).stronglyMeasurable
      (f := fun q : ℝ × Plane => ν * q.1)).smul (hD2m k l)
    exact h
  have hN2m : ∀ k l, Measurable fun s =>
      eLpNorm ((ν * s) • D2 k l s) (ENNReal.ofReal p) (cellMeasure c) := fun k l =>
    measurable_eLpNorm_slice (hm2 k l) c hP0 ENNReal.ofReal_ne_top
  have hNu : ∀ᵐ s ∂(volume.restrict (Ioi 0)),
      eLpNorm (u s) (ENNReal.ofReal p) (cellMeasure c) < ⊤ :=
    hac.ae_le (ae_lt_top_of_eLpNorm hp0 hNum.aemeasurable hu)
  have hN2 : ∀ᵐ s ∂(volume.restrict (Ioi 0)), ∀ k l,
      eLpNorm (D2 k l s) (ENNReal.ofReal p) (cellMeasure c) < ⊤ := by
    rw [ae_all_iff]
    intro k
    rw [ae_all_iff]
    intro l
    have h1 := hac.ae_le (ae_lt_top_of_eLpNorm hp0 (hN2m k l).aemeasurable (hD2b k l))
    filter_upwards [h1, ae_restrict_mem measurableSet_Ioi] with s hs hs0
    rw [eLpNorm_const_smul] at hs
    have hne : ‖ν * s‖ₑ ≠ 0 := by
      rw [Real.enorm_of_nonneg (mul_nonneg hν.le (le_of_lt hs0))]
      exact (ENNReal.ofReal_pos.2 (mul_pos hν hs0)).ne'
    exact ENNReal.lt_top_of_mul_ne_top_right hs.ne hne
  have hex : ∀ s : ℝ, ∃ D1 : Fin 2 → Plane → Plane, (∀ i, IsQPeriodic c (D1 i)) ∧
      ((0 < s ∧ eLpNorm (u s) (ENNReal.ofReal p) (cellMeasure c) < ⊤ ∧
          (∀ k l, eLpNorm (D2 k l s) (ENNReal.ofReal p) (cellMeasure c) < ⊤) ∧
          ∀ k l, Sob.HasWeakDeriv (Sob.cylinder c) [Sob.cylDir k, Sob.cylDir l] (u s)
            (D2 k l s)) →
        (∀ i, Sob.HasWeakDeriv (Sob.cylinder c) [Sob.cylDir i] (u s) (D1 i)) ∧
        ∀ i, eLpNorm (D1 i) (ENNReal.ofReal p) (cellMeasure c) ≤
          CI * (eLpNorm (u s) (ENNReal.ofReal p) (cellMeasure c) *
            ∑ k, ∑ l, eLpNorm (D2 k l s) (ENNReal.ofReal p) (cellMeasure c)) ^ (1 / 2 : ℝ)) := by
    intro s
    by_cases hs : 0 < s ∧ eLpNorm (u s) (ENNReal.ofReal p) (cellMeasure c) < ⊤ ∧
        (∀ k l, eLpNorm (D2 k l s) (ENNReal.ofReal p) (cellMeasure c) < ⊤) ∧
        ∀ k l, Sob.HasWeakDeriv (Sob.cylinder c) [Sob.cylDir k, Sob.cylDir l] (u s) (D2 k l s)
    · obtain ⟨_, hus, hD2s, hws⟩ := hs
      obtain ⟨D1, hper, hw, hb⟩ := hGI (u s) (fun k l => D2 k l s) (huper s)
        (fun k l => hD2per k l s) ⟨(stronglyMeasurable_slice hum s).aestronglyMeasurable, hus⟩
        (fun k l => ⟨(stronglyMeasurable_slice (hD2m k l) s).aestronglyMeasurable, hD2s k l⟩) hws
      exact ⟨D1, hper, fun _ => ⟨hw, hb⟩⟩
    · exact ⟨fun _ => 0, fun _ _ => rfl, fun h => absurd h hs⟩
  choose D1f hD1per hD1 using hex
  have hgood : ∀ᵐ s ∂(volume.restrict (Ioi 0)), 0 < s ∧
      eLpNorm (u s) (ENNReal.ofReal p) (cellMeasure c) < ⊤ ∧
      (∀ k l, eLpNorm (D2 k l s) (ENNReal.ofReal p) (cellMeasure c) < ⊤) ∧
      ∀ k l, Sob.HasWeakDeriv (Sob.cylinder c) [Sob.cylDir k, Sob.cylDir l] (u s) (D2 k l s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi, hNu, hN2, hD2w] with s h0 h1 h2 h3
    exact ⟨h0, h1, h2, h3⟩
  refine ⟨fun i s => D1f s i, fun i s => hD1per s i, ?_, ?_⟩
  · filter_upwards [hgood] with s hs
    exact (hD1 s hs).1
  · intro i
    have hpt : ∀ᵐ s ∂(ageWeight (p / 2 - 5 / 2)),
        ‖eLpNorm (Real.sqrt (ν * s) • D1f s i) (ENNReal.ofReal p) (cellMeasure c)‖ₑ ≤
          ‖(CI : ℝ≥0∞) * (eLpNorm (u s) (ENNReal.ofReal p) (cellMeasure c) +
            ∑ k, ∑ l, eLpNorm ((ν * s) • D2 k l s) (ENNReal.ofReal p) (cellMeasure c))‖ₑ := by
      filter_upwards [(ageWeight_ac (p / 2 - 5 / 2)).ae_le hgood] with s hs
      rw [enorm_eq_self, enorm_eq_self]
      have hb := (hD1 s hs).2 i
      have hs0 : 0 ≤ ν * s := mul_nonneg hν.le hs.1.le
      have eS : ENNReal.ofReal (ν * s) *
          ∑ k, ∑ l, eLpNorm (D2 k l s) (ENNReal.ofReal p) (cellMeasure c) =
            ∑ k, ∑ l, eLpNorm ((ν * s) • D2 k l s) (ENNReal.ofReal p) (cellMeasure c) := by
        simp_rw [Finset.mul_sum, eLpNorm_const_smul, Real.enorm_of_nonneg hs0]
      have esq : ‖Real.sqrt (ν * s)‖ₑ = ENNReal.ofReal (ν * s) ^ (1 / 2 : ℝ) := by
        rw [Real.enorm_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
          ENNReal.ofReal_rpow_of_nonneg hs0 (by norm_num)]
      calc eLpNorm (Real.sqrt (ν * s) • D1f s i) (ENNReal.ofReal p) (cellMeasure c)
          = ‖Real.sqrt (ν * s)‖ₑ * eLpNorm (D1f s i) (ENNReal.ofReal p) (cellMeasure c) :=
            eLpNorm_const_smul _ _ _ _
        _ ≤ ENNReal.ofReal (ν * s) ^ (1 / 2 : ℝ) *
              (CI * (eLpNorm (u s) (ENNReal.ofReal p) (cellMeasure c) *
                ∑ k, ∑ l, eLpNorm (D2 k l s) (ENNReal.ofReal p) (cellMeasure c)) ^ (1 / 2 : ℝ)) := by
            rw [esq]
            gcongr
        _ = CI * (eLpNorm (u s) (ENNReal.ofReal p) (cellMeasure c) *
              (ENNReal.ofReal (ν * s) *
                ∑ k, ∑ l, eLpNorm (D2 k l s) (ENNReal.ofReal p) (cellMeasure c))) ^ (1 / 2 : ℝ) := by
            rw [mul_left_comm, ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
            congr 2
            ring
        _ = CI * (eLpNorm (u s) (ENNReal.ofReal p) (cellMeasure c) *
              ∑ k, ∑ l, eLpNorm ((ν * s) • D2 k l s) (ENNReal.ofReal p) (cellMeasure c)) ^
                (1 / 2 : ℝ) := by
            rw [eS]
        _ ≤ CI * (eLpNorm (u s) (ENNReal.ofReal p) (cellMeasure c) +
              ∑ k, ∑ l, eLpNorm ((ν * s) • D2 k l s) (ENNReal.ofReal p) (cellMeasure c)) := by
            gcongr
            exact rpow_half_mul_le_add _ _
    have hsum : eLpNorm (fun s => ∑ k, ∑ l,
        eLpNorm ((ν * s) • D2 k l s) (ENNReal.ofReal p) (cellMeasure c))
          (ENNReal.ofReal p) (ageWeight (p / 2 - 5 / 2)) ≤
        ∑ k, ∑ l, HpNorm c p (fun s => (ν * s) • D2 k l s) := by
      refine (eLpNorm_sum_fintype_le hP1 (f := fun k s => ∑ l,
        eLpNorm ((ν * s) • D2 k l s) (ENNReal.ofReal p) (cellMeasure c)) fun k =>
          (Finset.measurable_sum _ fun l _ => hN2m k l).aestronglyMeasurable).trans ?_
      refine Finset.sum_le_sum fun k _ => ?_
      exact eLpNorm_sum_fintype_le hP1 (f := fun l s =>
        eLpNorm ((ν * s) • D2 k l s) (ENNReal.ofReal p) (cellMeasure c))
          fun l => (hN2m k l).aestronglyMeasurable
    calc HpNorm c p (fun s => Real.sqrt (ν * s) • D1f s i)
        = eLpNorm (fun s => eLpNorm (Real.sqrt (ν * s) • D1f s i) (ENNReal.ofReal p)
            (cellMeasure c)) (ENNReal.ofReal p) (ageWeight (p / 2 - 5 / 2)) := rfl
      _ ≤ eLpNorm (fun s => (CI : ℝ≥0∞) * (eLpNorm (u s) (ENNReal.ofReal p) (cellMeasure c) +
            ∑ k, ∑ l, eLpNorm ((ν * s) • D2 k l s) (ENNReal.ofReal p) (cellMeasure c)))
            (ENNReal.ofReal p) (ageWeight (p / 2 - 5 / 2)) := eLpNorm_mono_enorm_ae hpt
      _ = CI * eLpNorm (fun s => eLpNorm (u s) (ENNReal.ofReal p) (cellMeasure c) +
            ∑ k, ∑ l, eLpNorm ((ν * s) • D2 k l s) (ENNReal.ofReal p) (cellMeasure c))
            (ENNReal.ofReal p) (ageWeight (p / 2 - 5 / 2)) :=
          eLpNorm_const_mul_ennreal ENNReal.coe_ne_top _ hP0 ENNReal.ofReal_ne_top
      _ ≤ CI * (HpNorm c p u + ∑ k, ∑ l, HpNorm c p (fun s => (ν * s) • D2 k l s)) := by
          gcongr
          refine (eLpNorm_add_le (f := fun s => eLpNorm (u s) (ENNReal.ofReal p) (cellMeasure c))
            hNum.aestronglyMeasurable ?_ hP1).trans ?_
          · exact (Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun l _ =>
              hN2m k l).aestronglyMeasurable
          · exact add_le_add le_rfl hsum

end UnforcedLeray.B0289
