import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_10_1
import NonUniqueEuler.P.Infra.ConvMinkowski.Minkowski

/-!
# Helpers for `wardStreamCorrYoungL2_proved` (1): Young for a general cylinder kernel

Source of record: `the November 2 reference manuscript` (73 pages), 3624-3646,
3687-3713.  The dilation integral `∫_0^1 λ^a ∫ k(y-λz) g(τ+2log λ, z) dz dλ` for an arbitrary
measurable kernel `k` (copy of `IIIa.sepDom_slice`, `IIIa.sepDomYoung_of` with `p = q = 2`,
`b = 1`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- The dilation integral with a general kernel `k`. -/
def w2Dom (k : Space → ℝ≥0∞) (a : ℝ) (g : ℝ → Space → ℝ≥0∞) (τ : ℝ) (y : Space) : ℝ≥0∞ :=
  ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ a) *
    ∫⁻ z : Space, k (y - l • z) * g (τ + 2 * Real.log l) z

theorem w2_sepDom_eq (a : ℝ) (j : ℕ) (D : ℝ) (g : ℝ → Space → ℝ≥0∞) :
    IIIa.sepDom a j D g = w2Dom (IIIa.sepKd j D) a g := rfl

theorem w2_measurable_inner {k : Space → ℝ≥0∞} (hk : Measurable k) {g : ℝ → Space → ℝ≥0∞}
    (hg : Measurable (Function.uncurry g)) (τ : ℝ) :
    Measurable (fun r : Space × ℝ => ∫⁻ z : Space,
      k (r.1 - r.2 • z) * g (τ + 2 * Real.log r.2) z) := by
  refine Measurable.lintegral_prod_right
    (f := fun (r : Space × ℝ) (z : Space) => k (r.1 - r.2 • z) * g (τ + 2 * Real.log r.2) z) ?_
  refine Measurable.mul ?_ ?_
  · refine hk.comp ?_
    exact (measurable_fst.comp measurable_fst).sub
      ((measurable_snd.comp measurable_fst).smul measurable_snd)
  · have : Measurable (fun r : (Space × ℝ) × Space => (τ + 2 * Real.log r.1.2, r.2)) :=
      (measurable_const.add (measurable_const.mul
        (Real.measurable_log.comp (measurable_snd.comp measurable_fst)))).prodMk measurable_snd
    exact hg.comp this

/-- Fixed-`τ` estimate: Minkowski in `λ` for the `L^q_y` norm, then Young with dilation. -/
theorem w2_slice (hYD : IIIa.SepYoungDil) (p q b a : ℝ) (hp : 1 ≤ p) (hb : 1 ≤ b)
    (hq : 1 ≤ q) (hrel : 1 + 1 / q = 1 / p + 1 / b) {k : Space → ℝ≥0∞} (hk : Measurable k)
    {g : ℝ → Space → ℝ≥0∞}
    (hg : Measurable (Function.uncurry g)) (τ : ℝ) :
    (∫⁻ y : Space, w2Dom k a g τ y ^ q) ^ (1 / q) ≤
      (∫⁻ x : Space, k x ^ b) ^ (1 / b) *
        ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (a - 3 + 3 / p)) *
          (∫⁻ z : Space, g (τ + 2 * Real.log l) z ^ p) ^ (1 / p) := by
  have hq0 : 0 < q := by linarith
  have hHm := w2_measurable_inner hk hg τ
  set F : Space → ℝ → ℝ≥0∞ := fun y l => ENNReal.ofReal (l ^ a) *
    ∫⁻ z : Space, k (y - l • z) * g (τ + 2 * Real.log l) z with hF
  have hFm : Measurable (Function.uncurry F) := by
    have h1 : Measurable (fun r : Space × ℝ => ENNReal.ofReal (r.2 ^ a)) :=
      ENNReal.measurable_ofReal.comp (measurable_snd.pow_const a)
    exact h1.mul hHm
  have hmink := NonUniqueEuler.Conv.lintegral_lintegral_rpow_le
    (μ := (volume : Measure Space)) (ν := volume.restrict (Ioo (0 : ℝ) 1)) (F := F)
    hFm.aemeasurable hq
  have hsl : w2Dom k a g τ = fun y => ∫⁻ l in Ioo (0 : ℝ) 1, F y l := rfl
  rw [hsl]
  refine hmink.trans ?_
  have hnm := IIIa.measurable_phaseNorm p hg
  have hnl : Measurable (fun l : ℝ => (∫⁻ z : Space, g (τ + 2 * Real.log l) z ^ p) ^ (1 / p)) :=
    hnm.comp (measurable_const.add (measurable_const.mul Real.measurable_log))
  have hWm : Measurable (fun l : ℝ => ENNReal.ofReal (l ^ (a - 3 + 3 / p))) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)
  have hfm : Measurable (fun l : ℝ => ENNReal.ofReal (l ^ (a - 3 + 3 / p)) *
      (∫⁻ z : Space, g (τ + 2 * Real.log l) z ^ p) ^ (1 / p)) := hWm.mul hnl
  rw [← lintegral_const_mul _ hfm]
  refine setLIntegral_mono' measurableSet_Ioo fun l hl => ?_
  have hl0 : 0 < l := hl.1
  have hGm : Measurable (g (τ + 2 * Real.log l)) :=
    hg.comp (measurable_const.prodMk measurable_id)
  have hy := hYD p q b hp hb hq hrel k (g (τ + 2 * Real.log l)) hk hGm l hl0
  have hw : (∫⁻ y : Space, F y l ^ q) ^ (1 / q) =
      ENNReal.ofReal (l ^ a) * (∫⁻ y : Space, (∫⁻ z : Space,
        k (y - l • z) * g (τ + 2 * Real.log l) z) ^ q) ^ (1 / q) := by
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
        k (y - l • z) * g (τ + 2 * Real.log l) z) ^ q) ^ (1 / q)
      ≤ ENNReal.ofReal (l ^ a) * (ENNReal.ofReal (l ^ (-3 + 3 / p)) *
          (∫⁻ x : Space, k x ^ b) ^ (1 / b) *
          (∫⁻ z : Space, g (τ + 2 * Real.log l) z ^ p) ^ (1 / p)) := by gcongr
    _ = (∫⁻ x : Space, k x ^ b) ^ (1 / b) * (ENNReal.ofReal (l ^ (a - 3 + 3 / p)) *
          (∫⁻ z : Space, g (τ + 2 * Real.log l) z ^ p) ^ (1 / p)) := by
        rw [hexp]; ring

/-- **Young for the dilation integral with a general kernel**, `p = q = 2`, `b = 1`
(source 3624-3646). -/
theorem w2_young {k : Space → ℝ≥0∞} (hk : Measurable k) {a δ : ℝ} (hδ : 0 < δ)
    (hδa : δ ≤ a - 2 + 3 / 2) (hkfin : ∫⁻ x : Space, k x ≠ ⊤) (P : ℝ) (hP : 0 < P) {g : ℝ → Space → ℝ≥0∞}
    (hgm : Measurable (Function.uncurry g)) (hper : ∀ τ z, g (τ + P) z = g τ z) :
    IIIa.ltauLq P 2 (w2Dom k a g) ≤
      (∫⁻ x : Space, k x) * (ENNReal.ofReal (1 / δ) * IIIa.ltauLq P 2 g) := by
  have hp : (1 : ℝ) ≤ 2 := by norm_num
  have hrel : 1 + 1 / (2 : ℝ) = 1 / 2 + 1 / (1 : ℝ) := by norm_num
  have hq0 : (0 : ℝ) < 2 := by norm_num
  set Kb : ℝ≥0∞ := (∫⁻ x : Space, k x ^ (1 : ℝ)) ^ (1 / (1 : ℝ)) with hKb
  have hKb' : Kb = ∫⁻ x : Space, k x := by
    simp [hKb]
  set n : ℝ → ℝ≥0∞ := fun σ => (∫⁻ z : Space, g σ z ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) with hn
  set W : ℝ → ℝ≥0∞ := fun l => ENNReal.ofReal (l ^ (a - 3 + 3 / 2)) with hW
  have hnm : Measurable n := IIIa.measurable_phaseNorm 2 hgm
  have hWm : Measurable W := ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)
  have hnper : ∀ τ, n (τ + P) = n τ := by intro τ; simp only [hn, hper]
  set I : ℝ → ℝ≥0∞ := fun τ => ∫⁻ l in Ioo (0 : ℝ) 1, W l * n (τ + 2 * Real.log l) with hI
  have hslice : ∀ τ, (∫⁻ y : Space, w2Dom k a g τ y ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) ≤ Kb * I τ :=
    fun τ => w2_slice IIIa.sepYoungDil 2 2 1 a hp (le_refl _) hp hrel hk hgm τ
  have hlt : IIIa.ltauLq P 2 g = ((ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc (0 : ℝ) P, n τ ^ (2 : ℝ)) ^
      (1 / 2 : ℝ) := IIIa.ltauLq_eq P 2 hq0 g
  have hW1 : ∫⁻ l in Ioo (0 : ℝ) 1, W l = ENNReal.ofReal (1 / (a - 2 + 3 / 2)) := by
    have hs : -1 < a - 3 + 3 / 2 := by linarith
    have := IIIa.lintegral_Ioo_rpow (a - 3 + 3 / 2) hs
    rw [show a - 3 + 3 / 2 + 1 = a - 2 + 3 / 2 by ring] at this
    exact this
  have hW2 : ENNReal.ofReal (1 / (a - 2 + 3 / 2)) ≤ ENNReal.ofReal (1 / δ) := by
    apply ENNReal.ofReal_le_ofReal
    exact one_div_le_one_div_of_le hδ hδa
  have hmink := IIIa.sepPhaseMink P hP W n hWm hnm hnper
  have hKt : Kb ≠ ⊤ := by rw [hKb']; exact hkfin
  rw [← hKb']
  calc IIIa.ltauLq P 2 (w2Dom k a g)
      = ((ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc (0 : ℝ) P,
          ((∫⁻ y : Space, w2Dom k a g τ y ^ (2 : ℝ)) ^ (1 / (2 : ℝ))) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
        IIIa.ltauLq_eq P 2 hq0 _
    _ ≤ ((ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc (0 : ℝ) P, (Kb * I τ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        gcongr with τ
        exact hslice τ
    _ = Kb * ((ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc (0 : ℝ) P, I τ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        simp_rw [ENNReal.mul_rpow_of_nonneg _ _ (show (0 : ℝ) ≤ 2 by norm_num)]
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hKt),
          mul_left_comm, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
        norm_num
    _ ≤ Kb * ((∫⁻ l in Ioo (0 : ℝ) 1, W l) *
          ((ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc (0 : ℝ) P, n τ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) := by
        gcongr
    _ ≤ Kb * (ENNReal.ofReal (1 / δ) * IIIa.ltauLq P 2 g) := by
        rw [hlt, hW1]
        gcongr

end UnforcedLeray.Short.PartIIIb.Concrete
end
