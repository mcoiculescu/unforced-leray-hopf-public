import UnforcedLeray.Units.B0284.Defs
import UnforcedLeray.Units.B0284.Contraction
import UnforcedLeray.Units.B0284.Mellin

/-!
# B0284 `background:eq:2.24`: the flat (`ε = 0`) cylinder inverse

Unit B0284 of `paper/main.tex`, label `background:eq:2.24`, tex lines 5247–5250
(§`sec:st18-6052`); blueprint unit B0284 of


At `ε = 0` the cylinder inverse is
`T̄F(s) = ∫₀ˢ e^{ν(s-t)Δ} 𝕡₀(F(t)/t) dt`, `Δ = ∂_q² + ∂_η²` on `T_c × ℝ`, `𝕡₀` the flat
two-dimensional Leray projection. The blueprint statement adds that `T̄` is causal in age and
bounded on `H_p = L^p(s^{a_p} ds; L^p(dq/c dη))`, `a_p = p/2 - 5/2` (tex lines 4657–4660,
5229–5235), with `‖T̄F‖_{H_p} ≤ C_p γ_p^{-1} ‖F‖_{H_p}`, `γ_p = (3/p - 1)/2` (tex line 5216),
by heat contraction and Minkowski; `C_p` is the `L^p` bound of `𝕡₀`.

Contents.
* Definitions (`UnforcedLeray.Units.B0284.Defs`): `IsQPeriodic`, `cell`, `cellMeasure`
  (`dq/c dη`), `IsFlatLerayDecomp`, `flatLeray` (`𝕡₀`), `heatKernel2`, `heat` (`e^{θΔ}`),
  `flatInverse` (`T̄`), and the age norm `HpNorm` below. Conventions and junk values are listed
  in the docstring of `Defs`.
* Causality in age: `flatInverse_causal`, `flatInverse_indicator`, `flatInverse_congr_ae`;
  zero initial value `flatInverse_of_nonpos`; periodicity `flatInverse_periodic`.
* Heat contraction (`UnforcedLeray.Units.B0284.Contraction`): `eLpNorm_heat_le`.
* The pointwise-in-age bound `eLpNorm_flatInverse_le`:
  `‖T̄F(s)‖_{L^p_sp} ≤ ∫_0^s ‖𝕡₀(F(t)/t)‖_{L^p_sp} dt`, and with the Leray bound
  `eLpNorm_flatInverse_le_of_leray`: `‖T̄F(s)‖_{L^p_sp} ≤ C ∫_0^s t^{-1} ‖F(t)‖_{L^p_sp} dt`
  (the first line of tex eq. (C.22), lines 5022–5024).
* The `H_p` bound `flatInverse_Hp_le`: `‖T̄F‖_{H_p} ≤ C γ_p^{-1} ‖F‖_{H_p}`, `1 ≤ p < 3`.

What enters as hypotheses (not proved here). The `L^p` theory of `𝕡₀` on the cylinder
(Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8, transferred to `T_c × ℝ`; blueprint
INF01) is not formalized. It enters the two bounds as two explicit hypotheses about the actual
inputs `F(t)/t`, both consequences of that cited theorem for every `F ∈ H_p`, `1 < p < ∞`:
* `hLeray`: `‖𝕡₀(F(t)/t)‖_{L^p_sp} ≤ C ‖F(t)/t‖_{L^p_sp}` for almost every age `t > 0`
  (the cited `L^p` bound, with the manuscript's constant `C = C_p`);
* `hmeas`: `t ↦ 𝕡₀(F(t)/t)` has a jointly measurable version `G` (`G t = 𝕡₀(F(t)/t)` almost
  everywhere in space, for almost every age). This is the measurable dependence that a bounded
  linear `𝕡₀` gives on `H_p`; it is needed because `flatLeray` is defined by choice.
No other hypothesis is added: `ν > 0` and `c > 0` are the manuscript's viscosity and
circumference, `1 ≤ p < 3` makes `γ_p > 0` (the manuscript uses `p = 11/4`), and `F` needs no
measurability or finiteness assumption (both sides are `[0,∞]`-valued).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Real
open scoped NNReal ENNReal

namespace UnforcedLeray.B0284

open UnforcedLeray.GaussianVortex (Plane)

/-! ## The age norm `H_p` -/

/-- `γ_p = (3/p - 1)/2`, the decay rate of the free semigroup on `L^p`
(tex line 5216, `background:eq:2.18`). -/
def gammaP (p : ℝ) : ℝ := (3 / p - 1) / 2

/-- The norm of `H_p = L^p(s^{p/2-5/2} ds; L^p(dq/c dη))` (tex lines 4657–4660, 5232), as an
iterated `[0,∞]`-valued norm: age weight `s^{a_p}`, `a_p = p/2 - 5/2`, on `(0,∞)`, and the
normalized cylinder measure `dq/c dη` in space. -/
def HpNorm (c p : ℝ) (F : ℝ → Plane → Plane) : ℝ≥0∞ :=
  eLpNorm (fun s => eLpNorm (F s) (ENNReal.ofReal p) (cellMeasure c)) (ENNReal.ofReal p)
    (ageWeight (p / 2 - 5 / 2))

theorem gammaP_pos {p : ℝ} (hp : 0 < p) (hp3 : p < 3) : 0 < gammaP p := by
  unfold gammaP
  have : 1 < 3 / p := by rw [lt_div_iff₀ hp]; linarith
  linarith

/-- The dilation exponent of the age weight is `γ_p`: `-(a_p + 1)/p = γ_p`. -/
theorem neg_ageExponent_eq {p : ℝ} (hp : 0 < p) : -(p / 2 - 5 / 2 + 1) / p = gammaP p := by
  unfold gammaP
  field_simp
  ring

/-! ## Measurability of the Duhamel integrand -/

/-- The spatial `L^p` norm of a jointly measurable family is measurable in age. -/
theorem measurable_eLpNorm_slice {G : ℝ → Plane → Plane}
    (hG : StronglyMeasurable (Function.uncurry G)) (c : ℝ) {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (hp : p ≠ ⊤) : Measurable fun t => eLpNorm (G t) p (cellMeasure c) := by
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp]
  refine Measurable.pow_const ?_ _
  exact (hG.measurable.enorm.pow_const p.toReal).lintegral_prod_right'

/-- The absolute heat integral of a jointly measurable family, at heat time `ν(s-t)`, is
jointly measurable in `(z, t)`. -/
theorem measurable_heatAbs_family {G : ℝ → Plane → Plane}
    (hG : StronglyMeasurable (Function.uncurry G)) (ν s : ℝ) :
    Measurable (Function.uncurry fun (z : Plane) (t : ℝ) => heatAbs (ν * (s - t)) (G t) z) := by
  have hf : Measurable fun q : (Plane × ℝ) × Plane =>
      ENNReal.ofReal (heatKernel2 (ν * (s - q.1.2)) q.2) *
        ‖Function.uncurry G (q.1.2, q.1.1 - q.2)‖ₑ := by
    have hm1 : Measurable fun q : (Plane × ℝ) × Plane => ((ν * (s - q.1.2), q.2) : ℝ × Plane) := by
      fun_prop
    have hm2 : Measurable fun q : (Plane × ℝ) × Plane => ((q.1.2, q.1.1 - q.2) : ℝ × Plane) := by
      fun_prop
    have h1 : Measurable fun q : (Plane × ℝ) × Plane =>
        ENNReal.ofReal (heatKernel2 (ν * (s - q.1.2)) q.2) :=
      ENNReal.measurable_ofReal.comp (measurable_heatKernel2.comp hm1)
    have h2 : Measurable fun q : (Plane × ℝ) × Plane =>
        ‖Function.uncurry G (q.1.2, q.1.1 - q.2)‖ₑ :=
      hG.measurable.enorm.comp hm2
    exact h1.mul h2
  exact hf.lintegral_prod_right'

/-! ## The pointwise-in-age bound -/

/-- **Pointwise-in-age bound** (heat contraction and Minkowski in age; the first step of
tex eq. (C.22), lines 5020–5024):
`‖T̄F(s)‖_{L^p_sp} ≤ ∫_0^s ‖𝕡₀(F(t)/t)‖_{L^p_sp} dt`, for `1 ≤ p < ∞`, given a jointly
measurable version `G` of `t ↦ 𝕡₀(F(t)/t)`. -/
theorem eLpNorm_flatInverse_le {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hp' : p ≠ ⊤) {F G : ℝ → Plane → Plane} (hGm : StronglyMeasurable (Function.uncurry G))
    (hG : ∀ᵐ t ∂(volume.restrict (Ioi 0)), G t =ᵐ[volume] flatLeray c (t⁻¹ • F t)) (s : ℝ) :
    eLpNorm (flatInverse ν c F s) p (cellMeasure c) ≤
      ∫⁻ t in Ioo 0 s, eLpNorm (flatLeray c (t⁻¹ • F t)) p (cellMeasure c) := by
  set P : ℝ → Plane → Plane := fun t => flatLeray c (t⁻¹ • F t) with hPdef
  set Φ : Plane → ℝ → ℝ≥0∞ := fun z t => heatAbs (ν * (s - t)) (G t) z with hΦ
  have hGs : ∀ᵐ t ∂(volume.restrict (Ioo 0 s)), G t =ᵐ[volume] P t :=
    ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioi_self hG
  have hpos : ∀ t ∈ Ioo 0 s, 0 < ν * (s - t) := fun t ht => mul_pos hν (sub_pos.2 ht.2)
  -- pointwise domination of `T̄F(s)` by the absolute heat integral of `G`
  have hA : ∀ z, ‖flatInverse ν c F s z‖ₑ ≤ ∫⁻ t in Ioo 0 s, Φ z t := by
    intro z
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    calc ∫⁻ t in Ioo 0 s, ‖heat (ν * (s - t)) (P t) z‖ₑ
        ≤ ∫⁻ t in Ioo 0 s, heatAbs (ν * (s - t)) (P t) z :=
          setLIntegral_mono' measurableSet_Ioo fun t ht => enorm_heat_le (hpos t ht) _ z
      _ = ∫⁻ t in Ioo 0 s, Φ z t := by
          refine lintegral_congr_ae ?_
          filter_upwards [hGs] with t ht
          rw [hΦ, heatAbs_congr_ae ht.symm]
  have hΦm : Measurable (Function.uncurry Φ) := measurable_heatAbs_family hGm ν s
  calc eLpNorm (flatInverse ν c F s) p (cellMeasure c)
      ≤ eLpNorm (fun z => ∫⁻ t in Ioo 0 s, Φ z t) p (cellMeasure c) :=
        eLpNorm_mono_enorm fun z => (hA z).trans_eq (enorm_eq_self _).symm
    _ ≤ ∫⁻ t in Ioo 0 s, eLpNorm (fun z => Φ z t) p (cellMeasure c) :=
        NonUniqueEuler.Conv.eLpNorm_lintegral_le hΦm.aemeasurable hp hp'
    _ ≤ ∫⁻ t in Ioo 0 s, eLpNorm (P t) p (cellMeasure c) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hGs, ae_restrict_mem measurableSet_Ioo] with t ht hts
        have hPm : AEStronglyMeasurable (P t) volume :=
          (hGm.comp_measurable measurable_prodMk_left).aestronglyMeasurable.congr ht
        have hfun : (fun z => Φ z t) = heatAbs (ν * (s - t)) (P t) := by
          rw [hΦ]
          exact heatAbs_congr_ae ht
        rw [hfun]
        exact eLpNorm_heatAbs_le hc (hpos t hts) (flatLeray_periodic c _) hPm hp hp'

/-- **Pointwise-in-age bound with the Leray bound** (first line of tex eq. (C.22), lines
5022–5024): `‖T̄F(s)‖_{L^p_sp} ≤ C ∫_0^s t^{-1} ‖F(t)‖_{L^p_sp} dt`, where `C` is the
`L^p_sp` bound of `𝕡₀` on the inputs `F(t)/t` (Grafakos Cor. 5.2.8, hypothesis `hLeray`). -/
theorem eLpNorm_flatInverse_le_of_leray {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp' : p ≠ ⊤) {F : ℝ → Plane → Plane} (C : ℝ≥0)
    (hmeas : ∃ G : ℝ → Plane → Plane, StronglyMeasurable (Function.uncurry G) ∧
      ∀ᵐ t ∂(volume.restrict (Ioi 0)), G t =ᵐ[volume] flatLeray c (t⁻¹ • F t))
    (hLeray : ∀ᵐ t ∂(volume.restrict (Ioi 0)),
      eLpNorm (flatLeray c (t⁻¹ • F t)) p (cellMeasure c) ≤
        C * eLpNorm (t⁻¹ • F t) p (cellMeasure c)) (s : ℝ) :
    eLpNorm (flatInverse ν c F s) p (cellMeasure c) ≤
      C * ∫⁻ t in Ioo 0 s, ENNReal.ofReal t⁻¹ * eLpNorm (F t) p (cellMeasure c) := by
  obtain ⟨G, hGm, hG⟩ := hmeas
  refine (eLpNorm_flatInverse_le hν hc hp hp' hGm hG s).trans ?_
  rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioi_self hLeray,
    ae_restrict_mem measurableSet_Ioo] with t ht hts
  refine ht.trans (le_of_eq ?_)
  rw [eLpNorm_const_smul, Real.enorm_of_nonneg (inv_nonneg.2 hts.1.le)]

/-! ## The `H_p` bound -/

/-- The Hardy step in the age weight `s^{a_p} ds`: for measurable `φ ≥ 0` and `1 ≤ p < 3`,
`‖s ↦ ∫_0^1 u^{-1} φ(su) du‖_{L^p(s^{a_p} ds)} ≤ γ_p^{-1} ‖φ‖_{L^p(s^{a_p} ds)}`
(the dilation identity `‖φ(s e^{-τ})‖ = e^{-γ_p τ}‖φ‖` integrated against `dτ = du/u`). -/
theorem eLpNorm_hardy_ageWeight_le {p : ℝ} (hp1 : 1 ≤ p) (hp3 : p < 3) {φ : ℝ → ℝ≥0∞}
    (hφ : Measurable φ) :
    eLpNorm (fun s => ∫⁻ u in Ioi 0, hardyKernel u * φ (s * u)) (ENNReal.ofReal p)
        (ageWeight (p / 2 - 5 / 2)) ≤
      ENNReal.ofReal (gammaP p)⁻¹ * eLpNorm φ (ENNReal.ofReal p) (ageWeight (p / 2 - 5 / 2)) := by
  have hp0 : 0 < p := by linarith
  refine (eLpNorm_mellin_le_lintegral hp1 measurable_hardyKernel hφ).trans_eq ?_
  rw [neg_ageExponent_eq hp0, lintegral_hardyKernel_rpow (gammaP_pos hp0 hp3), one_div]

/-- **`T̄` is bounded on `H_p`** (blueprint statement of B0284; heat contraction and
Minkowski, with the dilation identity `‖F(s e^{-τ})‖_{H_p} = e^{-γ_p τ}‖F‖_{H_p}`):
for `ν > 0`, `c > 0`, `1 ≤ p < 3`,
`‖T̄F‖_{H_p} ≤ C γ_p^{-1} ‖F‖_{H_p}`,
where `C` is the `L^p_sp` bound of `𝕡₀` on the inputs `F(t)/t` (hypothesis `hLeray`,
Grafakos Cor. 5.2.8) and `hmeas` provides a jointly measurable version of `t ↦ 𝕡₀(F(t)/t)`.
Both hypotheses are consequences of the cited `L^p` theory of `𝕡₀`, which is not formalized
here. -/
theorem flatInverse_Hp_le {ν c p : ℝ} (hν : 0 < ν) (hc : 0 < c) (hp1 : 1 ≤ p) (hp3 : p < 3)
    {F : ℝ → Plane → Plane} (C : ℝ≥0)
    (hmeas : ∃ G : ℝ → Plane → Plane, StronglyMeasurable (Function.uncurry G) ∧
      ∀ᵐ t ∂(volume.restrict (Ioi 0)), G t =ᵐ[volume] flatLeray c (t⁻¹ • F t))
    (hLeray : ∀ᵐ t ∂(volume.restrict (Ioi 0)),
      eLpNorm (flatLeray c (t⁻¹ • F t)) (ENNReal.ofReal p) (cellMeasure c) ≤
        C * eLpNorm (t⁻¹ • F t) (ENNReal.ofReal p) (cellMeasure c)) :
    HpNorm c p (flatInverse ν c F) ≤ C * ENNReal.ofReal (gammaP p)⁻¹ * HpNorm c p F := by
  obtain ⟨G, hGm, hG⟩ := hmeas
  have hp0 : 0 < p := by linarith
  have hP0 : ENNReal.ofReal p ≠ 0 := by simp [hp0]
  have hP1 : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp1
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℝ → ℝ≥0∞,
      ψ = fun t => eLpNorm (G t) (ENNReal.ofReal p) (cellMeasure c) := ⟨_, rfl⟩
  have hψm : Measurable ψ := by
    rw [hψ]; exact measurable_eLpNorm_slice hGm c hP0 ENNReal.ofReal_ne_top
  have hφtm : Measurable fun t => ENNReal.ofReal t * ψ t := ENNReal.measurable_ofReal.mul hψm
  -- step 1: for `s > 0`, `‖T̄F(s)‖ ≤ ∫_0^s ψ = ∫_0^∞ k(u) (su) ψ(su) du`
  have hstep : ∀ s, 0 < s →
      eLpNorm (flatInverse ν c F s) (ENNReal.ofReal p) (cellMeasure c) ≤
        ∫⁻ u in Ioi 0, hardyKernel u * (ENNReal.ofReal (s * u) * ψ (s * u)) := by
    intro s hs
    refine (eLpNorm_flatInverse_le hν hc hP1 ENNReal.ofReal_ne_top hGm hG s).trans ?_
    rw [← lintegral_Ioo_eq_mellin hs ψ]
    refine le_of_eq (lintegral_congr_ae ?_)
    filter_upwards [ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioi_self hG] with t ht
    rw [hψ]
    exact eLpNorm_congr_ae ((cellMeasure_ac c).ae_le ht.symm)
  -- step 2: `t ψ(t) ≤ C ‖F(t)‖` almost everywhere in age
  have hφtle : ∀ᵐ t ∂(ageWeight (p / 2 - 5 / 2)), ENNReal.ofReal t * ψ t ≤
      (C : ℝ≥0∞) * eLpNorm (F t) (ENNReal.ofReal p) (cellMeasure c) := by
    have h1 := (ageWeight_ac (p / 2 - 5 / 2)).ae_le hLeray
    have h2 := (ageWeight_ac (p / 2 - 5 / 2)).ae_le hG
    filter_upwards [h1, h2, ae_ageWeight_pos (p / 2 - 5 / 2)] with t ht1 ht2 ht0
    have hψt : ψ t = eLpNorm (flatLeray c (t⁻¹ • F t)) (ENNReal.ofReal p) (cellMeasure c) := by
      rw [hψ]
      exact eLpNorm_congr_ae ((cellMeasure_ac c).ae_le ht2)
    rw [hψt]
    calc ENNReal.ofReal t * eLpNorm (flatLeray c (t⁻¹ • F t)) (ENNReal.ofReal p) (cellMeasure c)
        ≤ ENNReal.ofReal t * (C * eLpNorm (t⁻¹ • F t) (ENNReal.ofReal p) (cellMeasure c)) := by
          gcongr
      _ = C * eLpNorm (F t) (ENNReal.ofReal p) (cellMeasure c) := by
          rw [eLpNorm_const_smul, Real.enorm_of_nonneg (inv_nonneg.2 ht0.le)]
          rw [show ∀ a b d e : ℝ≥0∞, a * (b * (d * e)) = b * ((a * d) * e) by
              intro a b d e; ring,
            ← ENNReal.ofReal_mul ht0.le, mul_inv_cancel₀ ht0.ne', ENNReal.ofReal_one, one_mul]
  -- step 3: Mellin–Minkowski with the Hardy kernel
  have hA : HpNorm c p (flatInverse ν c F) ≤
      eLpNorm (fun s => ∫⁻ u in Ioi 0, hardyKernel u * (ENNReal.ofReal (s * u) * ψ (s * u)))
        (ENNReal.ofReal p) (ageWeight (p / 2 - 5 / 2)) := by
    unfold HpNorm
    refine eLpNorm_mono_enorm_ae ?_
    filter_upwards [ae_ageWeight_pos (p / 2 - 5 / 2)] with s hs
    rw [enorm_eq_self, enorm_eq_self]
    exact hstep s hs
  have hB := eLpNorm_hardy_ageWeight_le hp1 hp3 hφtm
  have hC : eLpNorm (fun t => ENNReal.ofReal t * ψ t) (ENNReal.ofReal p)
      (ageWeight (p / 2 - 5 / 2)) ≤ C * HpNorm c p F := by
    unfold HpNorm
    rw [← eLpNorm_const_mul_ennreal ENNReal.coe_ne_top _ hP0 ENNReal.ofReal_ne_top]
    refine eLpNorm_mono_enorm_ae ?_
    filter_upwards [hφtle] with t ht
    rw [enorm_eq_self, enorm_eq_self]
    exact ht
  calc HpNorm c p (flatInverse ν c F)
      ≤ ENNReal.ofReal (gammaP p)⁻¹ * eLpNorm (fun t => ENNReal.ofReal t * ψ t)
          (ENNReal.ofReal p) (ageWeight (p / 2 - 5 / 2)) := hA.trans hB
    _ ≤ ENNReal.ofReal (gammaP p)⁻¹ * (C * HpNorm c p F) := by gcongr
    _ = C * ENNReal.ofReal (gammaP p)⁻¹ * HpNorm c p F := by ring

end UnforcedLeray.B0284
