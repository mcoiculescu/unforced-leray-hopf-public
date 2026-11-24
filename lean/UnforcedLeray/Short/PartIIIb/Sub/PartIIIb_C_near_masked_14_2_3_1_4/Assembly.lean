import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2_3_1_4

/-!
# Assembly of `OutChangeVarExp` from two elementary lemmas (`PartIII-b:C/near/masked/14/2/3/1/4`)

Source: `the November 2 reference manuscript`
(2683, 3604-3610, 3996-4011).  `OutChangeVarExp` is the composition of the periodic average in `q`
(`PeriodAvg`) and the half-plane-to-`ℝ³` change of variables with the weight `s^{-5/2}`
(`HalfPlaneToSpace`); the Fubini bookkeeping is proved here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

/-- **Periodic average** (source 3604-3610: the phase `τ = 2q/R + a` sweeps one period `2c/R` as `q`
runs over the cell `[-c/2, c/2)`, `dq = (R/2) dτ`): for a `2c/R`-periodic measurable `G`,
`∫_{q ∈ [-c/2,c/2)} G(2q/R + a) dq = (R/2) ∫_{τ ∈ (0, 2c/R]} G(τ) dτ`. -/
def PeriodAvg : Prop :=
  ∀ (R c : ℝ), 0 < R → 0 < c → ∀ G : ℝ → ℝ≥0∞, Measurable G → (∀ τ, G (τ + 2 * c / R) = G τ) →
    ∀ a : ℝ, ∫⁻ q in Ico (-c / 2) (c / 2), G (2 * q / R + a) =
      ENNReal.ofReal (R / 2) * ∫⁻ τ in Ioc (0 : ℝ) (2 * c / R), G τ

/-- **Half plane to `ℝ³`** (source 2683, 3996-4011): for measurable axisymmetric `H` (a function of
`(y₀²+y₁², y₂)`), with `y = (R/√s, 0, η/√s)`:
`∫_{s>0}∫_η s^{-5/2} H(y(s,η)) dη ds = (π R²)⁻¹ ∫_{ℝ³} H`.  (Proof: `ρ = R/√s`, `y₂ = η/√s`,
`s^{-5/2} ds dη = (2/R²) ρ dρ dy₂`; polar coordinates `∫_{ℝ³} H = 2π ∫∫ ρ H dρ dy₂`.) -/
def HalfPlaneToSpace : Prop :=
  ∀ R : ℝ, 0 < R → ∀ H : Space → ℝ≥0∞, Measurable H →
    (∀ y y' : Space, y 0 ^ 2 + y 1 ^ 2 = y' 0 ^ 2 + y' 1 ^ 2 → y 2 = y' 2 → H y = H y') →
      ∫⁻ s in Ioi (0 : ℝ), ∫⁻ η : ℝ,
          ENNReal.ofReal (s ^ (-5 / 2 : ℝ)) * H (chartY R (s, (0, η))) =
        ENNReal.ofReal (1 / (Real.pi * R ^ 2)) * ∫⁻ y : Space, H y

/-- The `ageμ` integral as an iterated integral `s`, `η`, `q`. -/
lemma ageμ_split (c a : ℝ) (hc : 0 < c) (g : Chart → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ x, g x ∂(ageμ c a) =
      ∫⁻ s in Ioi (0 : ℝ), ∫⁻ η : ℝ, ∫⁻ q in Ico (-c / 2) (c / 2),
        ENNReal.ofReal (c⁻¹ * s ^ a) * g (s, (q, η)) := by
  rw [lintegral_ageμ hc a hg]
  have hm : Measurable fun p : Chart => ENNReal.ofReal (c⁻¹ * p.1 ^ a) * g p :=
    ((ENNReal.measurable_ofReal.comp
      ((measurable_const.mul (measurable_fst.pow_const a))))).mul hg
  rw [Measure.volume_eq_prod, setLIntegral_prod _ hm.aemeasurable]
  refine lintegral_congr fun s => ?_
  have hq : qCell c = Ico (-c / 2) (c / 2) ×ˢ (univ : Set ℝ) := rfl
  have hm2 : Measurable fun y : ℝ × ℝ => ENNReal.ofReal (c⁻¹ * s ^ a) * g (s, y) :=
    measurable_const.mul (hg.comp (measurable_const.prodMk measurable_id))
  simp only []
  rw [hq, Measure.volume_eq_prod, setLIntegral_prod (fun y : ℝ × ℝ => ENNReal.ofReal (c⁻¹ * s ^ a) * g (s, y))
    hm2.aemeasurable]
  rw [lintegral_lintegral_swap]
  · simp [Measure.restrict_univ]
  · exact hm2.aemeasurable

lemma measurable_chartY_slice (R : ℝ) : Measurable fun p : ℝ × ℝ => chartY R (p.1, (0, p.2)) :=
  (measurable_chartY R).comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))

/-- Fubini for the triple integral `s, η, τ`. -/
lemma fubini3 (F : ℝ → ℝ → ℝ → ℝ≥0∞) (hF : Measurable fun q : (ℝ × ℝ) × ℝ => F q.1.1 q.1.2 q.2)
    (A B : Set ℝ) :
    ∫⁻ s in A, ∫⁻ η : ℝ, ∫⁻ τ in B, F s η τ =
      ∫⁻ τ in B, ∫⁻ s in A, ∫⁻ η : ℝ, F s η τ := by
  have h1 : ∀ s : ℝ, ∫⁻ η : ℝ, ∫⁻ τ in B, F s η τ = ∫⁻ τ in B, ∫⁻ η : ℝ, F s η τ := by
    intro s
    refine lintegral_lintegral_swap ?_
    exact (hF.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)).aemeasurable
  simp_rw [h1]
  refine lintegral_lintegral_swap ?_
  have hg : Measurable fun q : (ℝ × ℝ) × ℝ => F q.1.1 q.2 q.1.2 :=
    hF.comp (((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
      (measurable_snd.comp measurable_fst))
  exact (hg.lintegral_prod_right').aemeasurable

theorem outChangeVarExp_of (h1 : PeriodAvg) (h2 : HalfPlaneToSpace) : OutChangeVarExp := by
  intro R c hR hc
  refine ⟨ENNReal.ofReal (c⁻¹ * (R / 2) * (1 / (Real.pi * R ^ 2))), ENNReal.ofReal_ne_top, ?_⟩
  intro Q hQm hper hax
  have hmeas : Measurable fun x : Chart => Q (chartTau R x) (chartY R x) :=
    hQm.comp ((measurable_chartTau R).prodMk (measurable_chartY R))
  -- joint measurability of the integrand in `(s, η, τ)`
  have hJ : Measurable fun q : (ℝ × ℝ) × ℝ =>
      ENNReal.ofReal (q.1.1 ^ (-5 / 2 : ℝ)) * Q q.2 (chartY R (q.1.1, (0, q.1.2))) :=
    (ENNReal.measurable_ofReal.comp (measurable_fst.comp measurable_fst |>.pow_const _)).mul
      (hQm.comp (measurable_snd.prodMk ((measurable_chartY_slice R).comp measurable_fst)))
  have hK0 : ENNReal.ofReal (c⁻¹ * (R / 2) * (1 / (Real.pi * R ^ 2))) =
      ENNReal.ofReal (c⁻¹ * (R / 2)) * ENNReal.ofReal (1 / (Real.pi * R ^ 2)) :=
    ENNReal.ofReal_mul (by positivity)
  have hK0ne : ENNReal.ofReal (c⁻¹ * (R / 2)) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [ageμ_split c (-5 / 2) hc _ hmeas]
  have hy : ∀ s η : ℝ, ∫⁻ q in Ico (-c / 2) (c / 2),
        ENNReal.ofReal (c⁻¹ * s ^ (-5 / 2 : ℝ)) *
          Q (chartTau R (s, (q, η))) (chartY R (s, (q, η))) =
      ENNReal.ofReal (c⁻¹ * (R / 2)) *
        ∫⁻ τ in Ioc (0 : ℝ) (2 * c / R), ENNReal.ofReal (s ^ (-5 / 2 : ℝ)) *
          Q τ (chartY R (s, (0, η))) := by
    intro s η
    have hG : Measurable fun τ : ℝ => Q τ (chartY R (s, (0, η))) :=
      hQm.comp (measurable_id.prodMk measurable_const)
    have hmq : Measurable fun q : ℝ => Q (chartTau R (s, (q, η))) (chartY R (s, (q, η))) :=
      hmeas.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
    have e1 : ∫⁻ q in Ico (-c / 2) (c / 2), Q (chartTau R (s, (q, η))) (chartY R (s, (q, η))) =
        ENNReal.ofReal (R / 2) * ∫⁻ τ in Ioc (0 : ℝ) (2 * c / R), Q τ (chartY R (s, (0, η))) :=
      h1 R c hR hc (fun τ => Q τ (chartY R (s, (0, η)))) hG (fun τ => hper τ _) (Real.log s)
    rw [lintegral_const_mul _ hmq, e1, lintegral_const_mul _ hG,
      ENNReal.ofReal_mul (inv_nonneg.2 hc.le), ENNReal.ofReal_mul (inv_nonneg.2 hc.le)]
    ring
  simp_rw [hy]
  simp_rw [lintegral_const_mul' _ _ hK0ne]
  rw [fubini3 (fun s η τ => ENNReal.ofReal (s ^ (-5 / 2 : ℝ)) * Q τ (chartY R (s, (0, η)))) hJ]
  have hτ : ∀ τ : ℝ, ∫⁻ s in Ioi (0 : ℝ), ∫⁻ η : ℝ,
      ENNReal.ofReal (s ^ (-5 / 2 : ℝ)) * Q τ (chartY R (s, (0, η))) =
      ENNReal.ofReal (1 / (Real.pi * R ^ 2)) * ∫⁻ y : Space, Q τ y := fun τ =>
    h2 R hR (Q τ) (hQm.comp (measurable_const.prodMk measurable_id)) (hax τ)
  simp_rw [hτ]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hK0, mul_assoc]

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
