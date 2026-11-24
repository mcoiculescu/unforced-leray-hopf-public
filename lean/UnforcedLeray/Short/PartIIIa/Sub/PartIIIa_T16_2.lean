import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16
import NonUniqueEuler.P.Infra.ConvMinkowski.Minkowski

/-!
# `PartIII-a:T16/2` : `SepDomYoung` from five analytic lemmas (SP 3624-3646)

Source `the November 2 reference manuscript` lines 3624-3646.  The scalar dilation
integral `sepDom a j D g τ y = ∫_0^1 λ^a ∫ k(y-λz) g(τ+2log λ, z) dz dλ`, `k = sepKd j D`, is
estimated in three steps: (1) for fixed `τ`, Minkowski in `λ` for the `L^q_y` norm
(proved here from `lintegral_lintegral_rpow_le`); (2) Young's inequality with dilation
`λ^{-3+3/p}‖k‖_{L^b}‖g(τ+2logλ)‖_{L^p}` (`SepYoungDil`) and the tail integral `‖k‖_{L^b}`
(`SepKdLb`); (3) Minkowski in `λ` for the `L²_τ` norm together with `P`-periodicity (`SepPhaseMink`);
the remaining `λ`-integral is `∫_0^1 λ^{a-3+3/p} = 1/(a-2+3/p) ≤ 1/δ` (proved here).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- **Tail integral** (SP 3629-3630, 3631): for `b ≥ 1` (so `(4+j)b > 3`),
`‖1_{|x|≥D}|x|^{-4-j}‖_{L^b(ℝ³)} ≤ C₀ D^{-4-j+3/b}` (polar coordinates: the radial integral of
`r^{2-(4+j)b}` over `[D,∞)` is `D^{3-(4+j)b}/((4+j)b-3)`). -/
def SepKdLb : Prop :=
  ∀ (j : ℕ) (b : ℝ), 1 ≤ b → ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ D : ℝ, 0 < D →
    (∫⁻ x : Space, sepKd j D x ^ b) ^ (1 / b) ≤ ENNReal.ofReal (C0 * D ^ (-4 - (j : ℝ) + 3 / b))

/-- **Young's inequality with dilation** (SP 3631-3636): for measurable `k, G ≥ 0` on `ℝ³`,
`1 ≤ p,b,q`, `1 + 1/q = 1/p + 1/b`, `l > 0`:
`‖y ↦ ∫ k(y - l z) G(z) dz‖_{L^q} ≤ l^{-3+3/p} ‖k‖_{L^b} ‖G‖_{L^p}`
(substitute `w = l z`, `dz = l^{-3}dw`, Young's convolution inequality for `k` and `G(·/l)`,
`‖G(·/l)‖_{L^p} = l^{3/p}‖G‖_{L^p}`). -/
def SepYoungDil : Prop :=
  ∀ (p q b : ℝ), 1 ≤ p → 1 ≤ b → 1 ≤ q → 1 + 1 / q = 1 / p + 1 / b →
    ∀ k G : Space → ℝ≥0∞, Measurable k → Measurable G → ∀ l : ℝ, 0 < l →
      (∫⁻ y : Space, (∫⁻ z : Space, k (y - l • z) * G z) ^ q) ^ (1 / q) ≤
        ENNReal.ofReal (l ^ (-3 + 3 / p)) * (∫⁻ x : Space, k x ^ b) ^ (1 / b) *
          (∫⁻ z : Space, G z ^ p) ^ (1 / p)

/-- **Minkowski in `λ` and phase invariance** (SP 3637-3646): for measurable `W, n ≥ 0` with `n`
`P`-periodic, `‖τ ↦ ∫_0^1 W(λ) n(τ + 2 log λ) dλ‖_{L²(0,P], normalised}
 ≤ (∫_0^1 W) ‖n‖_{L²(0,P], normalised}`: Minkowski's integral inequality, then
`τ ↦ n(τ + 2 log λ)` has the same normalised `L²(0,P]` norm as `n` by periodicity. -/
def SepPhaseMink : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ W n : ℝ → ℝ≥0∞, Measurable W → Measurable n → (∀ τ, n (τ + P) = n τ) →
    ((ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc (0 : ℝ) P,
        (∫⁻ l in Ioo (0 : ℝ) 1, W l * n (τ + 2 * Real.log l)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
      (∫⁻ l in Ioo (0 : ℝ) 1, W l) *
        ((ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc (0 : ℝ) P, n τ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)

theorem measurable_sepKd (j : ℕ) (D : ℝ) : Measurable (sepKd j D) := by
  unfold sepKd
  refine Measurable.ite ?_ (ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _))
    measurable_const
  exact measurableSet_le measurable_const measurable_norm

theorem lintegral_Ioo_rpow (s : ℝ) (hs : -1 < s) :
    ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ s) = ENNReal.ofReal (1 / (s + 1)) := by
  have hint : IntervalIntegrable (fun x : ℝ => x ^ s) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' hs
  have h1 : ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ s) =
      ENNReal.ofReal (∫ l in Ioo (0 : ℝ) 1, l ^ s) := by
    rw [ofReal_integral_eq_lintegral_ofReal]
    · exact (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1 hint
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact Real.rpow_nonneg hx.1.le _
  have h2 : ∫ l in Ioo (0 : ℝ) 1, l ^ s = ∫ l in (0 : ℝ)..1, l ^ s := by
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  rw [h1, h2, integral_rpow (Or.inl hs)]
  have h0 : (0 : ℝ) ^ (s + 1) = 0 := Real.zero_rpow (by linarith)
  simp [h0]

theorem measurable_phaseNorm (p : ℝ) {g : ℝ → Space → ℝ≥0∞} (hg : Measurable (Function.uncurry g)) :
    Measurable (fun σ : ℝ => (∫⁻ z : Space, g σ z ^ p) ^ (1 / p)) := by
  have : Measurable (fun σ : ℝ => ∫⁻ z : Space, g σ z ^ p) :=
    Measurable.lintegral_prod_right (f := fun (σ : ℝ) (z : Space) => g σ z ^ p)
      (hg.pow_const p)
  exact this.pow_const _

theorem measurable_sepDomInner (j : ℕ) (D : ℝ) {g : ℝ → Space → ℝ≥0∞}
    (hg : Measurable (Function.uncurry g)) (τ : ℝ) :
    Measurable (fun r : Space × ℝ => ∫⁻ z : Space,
      sepKd j D (r.1 - r.2 • z) * g (τ + 2 * Real.log r.2) z) := by
  refine Measurable.lintegral_prod_right
    (f := fun (r : Space × ℝ) (z : Space) => sepKd j D (r.1 - r.2 • z) * g (τ + 2 * Real.log r.2) z) ?_
  refine Measurable.mul ?_ ?_
  · refine (measurable_sepKd j D).comp ?_
    exact (measurable_fst.comp measurable_fst).sub
      ((measurable_snd.comp measurable_fst).smul measurable_snd)
  · have : Measurable (fun r : (Space × ℝ) × Space => (τ + 2 * Real.log r.1.2, r.2)) :=
      (measurable_const.add (measurable_const.mul
        (Real.measurable_log.comp (measurable_snd.comp measurable_fst)))).prodMk measurable_snd
    exact hg.comp this

/-- Fixed-`τ` estimate: Minkowski in `λ` for the `L^q_y` norm, then Young with dilation. -/
theorem sepDom_slice (hYD : SepYoungDil) (j : ℕ) (p q b a D : ℝ) (hp : 1 ≤ p) (hb : 1 ≤ b)
    (hq : 1 ≤ q) (hrel : 1 + 1 / q = 1 / p + 1 / b) {g : ℝ → Space → ℝ≥0∞}
    (hg : Measurable (Function.uncurry g)) (τ : ℝ) :
    (∫⁻ y : Space, sepDom a j D g τ y ^ q) ^ (1 / q) ≤
      (∫⁻ x : Space, sepKd j D x ^ b) ^ (1 / b) *
        ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (a - 3 + 3 / p)) *
          (∫⁻ z : Space, g (τ + 2 * Real.log l) z ^ p) ^ (1 / p) := by
  have hq0 : 0 < q := by linarith
  have hHm := measurable_sepDomInner j D hg τ
  -- the integrand of Minkowski
  set F : Space → ℝ → ℝ≥0∞ := fun y l => ENNReal.ofReal (l ^ a) *
    ∫⁻ z : Space, sepKd j D (y - l • z) * g (τ + 2 * Real.log l) z with hF
  have hFm : Measurable (Function.uncurry F) := by
    have h1 : Measurable (fun r : Space × ℝ => ENNReal.ofReal (r.2 ^ a)) :=
      ENNReal.measurable_ofReal.comp (measurable_snd.pow_const a)
    exact h1.mul hHm
  have hmink := NonUniqueEuler.Conv.lintegral_lintegral_rpow_le
    (μ := (volume : Measure Space)) (ν := volume.restrict (Ioo (0 : ℝ) 1)) (F := F)
    hFm.aemeasurable hq
  have hsl : sepDom a j D g τ = fun y => ∫⁻ l in Ioo (0 : ℝ) 1, F y l := rfl
  rw [hsl]
  refine hmink.trans ?_
  have hnm := measurable_phaseNorm p hg
  have hnl : Measurable (fun l : ℝ => (∫⁻ z : Space, g (τ + 2 * Real.log l) z ^ p) ^ (1 / p)) :=
    hnm.comp (measurable_const.add (measurable_const.mul Real.measurable_log))
  have hWm : Measurable (fun l : ℝ => ENNReal.ofReal (l ^ (a - 3 + 3 / p))) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)
  have hfm : Measurable (fun l : ℝ => ENNReal.ofReal (l ^ (a - 3 + 3 / p)) *
      (∫⁻ z : Space, g (τ + 2 * Real.log l) z ^ p) ^ (1 / p)) := hWm.mul hnl
  rw [← lintegral_const_mul _ hfm]
  refine setLIntegral_mono' measurableSet_Ioo fun l hl => ?_
  have hl0 : 0 < l := hl.1
  -- pull out the weight
  have hGm : Measurable (g (τ + 2 * Real.log l)) :=
    hg.comp (measurable_const.prodMk measurable_id)
  have hy := hYD p q b hp hb hq hrel (sepKd j D) (g (τ + 2 * Real.log l))
    (measurable_sepKd j D) hGm l hl0
  have hw : (∫⁻ y : Space, F y l ^ q) ^ (1 / q) =
      ENNReal.ofReal (l ^ a) * (∫⁻ y : Space, (∫⁻ z : Space,
        sepKd j D (y - l • z) * g (τ + 2 * Real.log l) z) ^ q) ^ (1 / q) := by
    simp only [hF]
    simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le]
    rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq0.le ENNReal.ofReal_ne_top),
      ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul]
    rw [mul_one_div_cancel hq0.ne', ENNReal.rpow_one]
  rw [hw]
  have hexp : ENNReal.ofReal (l ^ (a - 3 + 3 / p)) =
      ENNReal.ofReal (l ^ a) * ENNReal.ofReal (l ^ (-3 + 3 / p)) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hl0.le _), ← Real.rpow_add hl0]
    congr 2; ring
  calc ENNReal.ofReal (l ^ a) * (∫⁻ y : Space, (∫⁻ z : Space,
        sepKd j D (y - l • z) * g (τ + 2 * Real.log l) z) ^ q) ^ (1 / q)
      ≤ ENNReal.ofReal (l ^ a) * (ENNReal.ofReal (l ^ (-3 + 3 / p)) *
          (∫⁻ x : Space, sepKd j D x ^ b) ^ (1 / b) *
          (∫⁻ z : Space, g (τ + 2 * Real.log l) z ^ p) ^ (1 / p)) := by gcongr
    _ = (∫⁻ x : Space, sepKd j D x ^ b) ^ (1 / b) * (ENNReal.ofReal (l ^ (a - 3 + 3 / p)) *
          (∫⁻ z : Space, g (τ + 2 * Real.log l) z ^ p) ^ (1 / p)) := by
        rw [hexp]; ring

theorem ltauLq_eq (P q : ℝ) (hq : 0 < q) (f : ℝ → Space → ℝ≥0∞) :
    ltauLq P q f = ((ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc (0 : ℝ) P,
      ((∫⁻ y : Space, f τ y ^ q) ^ (1 / q)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  unfold ltauLq
  congr 3
  funext τ
  rw [← ENNReal.rpow_mul]
  congr 1
  field_simp

/-- **`SepDomYoung` from the tail integral, Young with dilation, and Minkowski in `λ`**
(SP 3624-3646). -/
theorem sepDomYoung_of (h1 : SepKdLb) (h2 : SepYoungDil) (h3 : SepPhaseMink) : SepDomYoung := by
  intro j p q b δ hp hb hq hrel hδ
  obtain ⟨C0, hC0, hK⟩ := h1 j b hb
  refine ⟨C0 / δ, by positivity, ?_⟩
  intro a ha hδa D P hD hP g hgm hper
  have hq0 : 0 < q := by linarith
  have hp0 : 0 < p := by linarith
  set Kb : ℝ≥0∞ := (∫⁻ x : Space, sepKd j D x ^ b) ^ (1 / b) with hKb
  have hKbfin : Kb ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hK D hD)
  set n : ℝ → ℝ≥0∞ := fun σ => (∫⁻ z : Space, g σ z ^ p) ^ (1 / p) with hn
  set W : ℝ → ℝ≥0∞ := fun l => ENNReal.ofReal (l ^ (a - 3 + 3 / p)) with hW
  have hnm : Measurable n := measurable_phaseNorm p hgm
  have hWm : Measurable W := ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)
  have hnper : ∀ τ, n (τ + P) = n τ := by intro τ; simp only [hn, hper]
  have hPc : (ENNReal.ofReal P)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hP).ne'
  set I : ℝ → ℝ≥0∞ := fun τ => ∫⁻ l in Ioo (0 : ℝ) 1, W l * n (τ + 2 * Real.log l) with hI
  have hslice : ∀ τ, (∫⁻ y : Space, sepDom a j D g τ y ^ q) ^ (1 / q) ≤ Kb * I τ :=
    fun τ => sepDom_slice h2 j p q b a D hp hb hq hrel hgm τ
  have hlt : ltauLq P p g = ((ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc (0 : ℝ) P, n τ ^ (2 : ℝ)) ^
      (1 / 2 : ℝ) := ltauLq_eq P p hp0 g
  have hW1 : ∫⁻ l in Ioo (0 : ℝ) 1, W l = ENNReal.ofReal (1 / (a - 2 + 3 / p)) := by
    have hs : -1 < a - 3 + 3 / p := by linarith
    have := lintegral_Ioo_rpow (a - 3 + 3 / p) hs
    rw [show a - 3 + 3 / p + 1 = a - 2 + 3 / p by ring] at this
    exact this
  have hW2 : ENNReal.ofReal (1 / (a - 2 + 3 / p)) ≤ ENNReal.ofReal (1 / δ) := by
    apply ENNReal.ofReal_le_ofReal
    exact one_div_le_one_div_of_le hδ hδa
  have hmink := h3 P hP W n hWm hnm hnper
  calc ltauLq P q (sepDom a j D g)
      = ((ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc (0 : ℝ) P,
          ((∫⁻ y : Space, sepDom a j D g τ y ^ q) ^ (1 / q)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
        ltauLq_eq P q hq0 _
    _ ≤ ((ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc (0 : ℝ) P, (Kb * I τ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        gcongr with τ
        exact hslice τ
    _ = Kb * ((ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc (0 : ℝ) P, I τ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        simp_rw [ENNReal.mul_rpow_of_nonneg _ _ (show (0 : ℝ) ≤ 2 by norm_num)]
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hKbfin),
          mul_left_comm, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
        norm_num
    _ ≤ Kb * ((∫⁻ l in Ioo (0 : ℝ) 1, W l) *
          ((ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc (0 : ℝ) P, n τ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) := by
        gcongr
    _ ≤ ENNReal.ofReal (C0 * D ^ (-4 - (j : ℝ) + 3 / b)) *
          (ENNReal.ofReal (1 / δ) * ltauLq P p g) := by
        rw [hlt, hW1]
        gcongr
        exact hK D hD
    _ = ENNReal.ofReal (C0 / δ * D ^ (-4 - (j : ℝ) + 3 / b)) * ltauLq P p g := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring

end UnforcedLeray.Short.IIIa

end
