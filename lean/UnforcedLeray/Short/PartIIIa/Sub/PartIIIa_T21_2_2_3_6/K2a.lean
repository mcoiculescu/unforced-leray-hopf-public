import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6_1_2

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace K2aAux

open UnforcedLeray

/-- A bump in `η` that is positive on `|η| ≤ |R|` and compactly supported. -/
def bumpR (R : ℝ) : ContDiffBump (0 : ℝ) :=
  ⟨|R| + 1 / 2, |R| + 1, by positivity, by linarith⟩

/-- Product of a `d`-periodic smooth profile in `q` and a compactly supported profile in `η`
is a cylinder test. -/
theorem isCylTest_mul {d : ℝ} (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h)
    (hper : ∀ q, h (q + d) = h q) (b : ℝ → ℝ) (hb : ContDiff ℝ ∞ b) (R' : ℝ)
    (hR' : ∀ η, R' < |η| → b η = 0) :
    B0579.IsCylTest d (fun x => h x.1 * b x.2) where
  smooth := (hh.comp contDiff_fst).mul (hb.comp contDiff_snd)
  periodic x := by
    show h (x.1 + d) * b x.2 = h x.1 * b x.2
    rw [hper]
  band := ⟨R', fun x hx => by
    show h x.1 * b x.2 = 0
    rw [hR' x.2 hx, mul_zero]⟩

theorem contDiff_cos_q (d : ℝ) :
    ContDiff ℝ ∞ (fun q : ℝ => Real.cos (2 * Real.pi * q / d)) :=
  Real.contDiff_cos.comp (((contDiff_const (c := 2 * Real.pi)).mul contDiff_id).div_const d)

theorem contDiff_sin_q (d : ℝ) :
    ContDiff ℝ ∞ (fun q : ℝ => Real.sin (2 * Real.pi * q / d)) :=
  Real.contDiff_sin.comp (((contDiff_const (c := 2 * Real.pi)).mul contDiff_id).div_const d)

theorem cos_periodic {d : ℝ} (hd : 0 < d) (q : ℝ) :
    Real.cos (2 * Real.pi * (q + d) / d) = Real.cos (2 * Real.pi * q / d) := by
  have hd' : d ≠ 0 := hd.ne'
  have : 2 * Real.pi * (q + d) / d = 2 * Real.pi * q / d + 2 * Real.pi := by
    field_simp
  rw [this, Real.cos_add_two_pi]

theorem sin_periodic {d : ℝ} (hd : 0 < d) (q : ℝ) :
    Real.sin (2 * Real.pi * (q + d) / d) = Real.sin (2 * Real.pi * q / d) := by
  have hd' : d ≠ 0 := hd.ne'
  have : 2 * Real.pi * (q + d) / d = 2 * Real.pi * q / d + 2 * Real.pi := by
    field_simp
  rw [this, Real.sin_add_two_pi]

/-- On a measurable set where a cylinder test does not vanish, a field whose product with the
test is integrable on the cell is a.e. strongly measurable. -/
theorem aesm_of_ne_zero {d : ℝ} {f : ℝ × ℝ → ℂ} {ψ : ℝ × ℝ → ℝ}
    (hψ : B0579.IsCylTest d ψ)
    (hint : IntegrableOn (fun x => f x * (ψ x : ℂ)) (B0579.cell d))
    {S : Set (ℝ × ℝ)} (hSm : MeasurableSet S) (hS : S ⊆ B0579.cell d)
    (hne : ∀ x ∈ S, ψ x ≠ 0) :
    AEStronglyMeasurable f (volume.restrict S) := by
  have hψm : Measurable ψ := hψ.continuous.measurable
  have h1 : AEStronglyMeasurable (fun x => f x * (ψ x : ℂ)) (volume.restrict S) :=
    hint.aestronglyMeasurable.mono_set hS
  have hinv : Measurable (fun x => ((ψ x : ℂ))⁻¹) :=
    (Complex.measurable_ofReal.comp hψm).inv
  have h2 : AEStronglyMeasurable (fun x => f x * (ψ x : ℂ) * ((ψ x : ℂ))⁻¹)
      (volume.restrict S) :=
    h1.mul hinv.aestronglyMeasurable
  refine h2.congr ?_
  refine ae_restrict_of_forall_mem hSm (fun x hx => ?_)
  have hc : (ψ x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hne x hx)
  exact mul_inv_cancel_right₀ hc (f x)

theorem bandSet_measurable (d R : ℝ) :
    MeasurableSet (UnforcedLeray.Short.IIIa.AdjE1.bandSet d R) :=
  (B0579.measurableSet_cell d).inter (measurableSet_le (continuous_snd.abs).measurable
    measurable_const)

end K2aAux

open K2aAux UnforcedLeray in
/-- **Leaf K2a** (SP 3052-3058): a field integrable against every cylinder test is a.e.
strongly measurable on every band. -/
theorem testMeasF : UnforcedLeray.Short.IIIa.AdjE1.TestMeasF := by
  intro d f hd hint R
  have hR' : ∀ η, (bumpR R).rOut < |η| → bumpR R η = 0 := fun η hη =>
    (bumpR R).zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact hη.le)
  have hψ1 := isCylTest_mul (fun q => Real.cos (2 * Real.pi * q / d)) (contDiff_cos_q d)
    (cos_periodic hd) (bumpR R) (bumpR R).contDiff (bumpR R).rOut hR'
  have hψ2 := isCylTest_mul (fun q => Real.sin (2 * Real.pi * q / d)) (contDiff_sin_q d)
    (sin_periodic hd) (bumpR R) (bumpR R).contDiff (bumpR R).rOut hR'
  have hbpos : ∀ x : ℝ × ℝ, UnforcedLeray.Short.IIIa.AdjE1.bandSet d R x →
      bumpR R x.2 ≠ 0 := by
    intro x hx
    have hxR : |x.2| ≤ R := hx.2
    have hmem : x.2 ∈ Metric.ball (0 : ℝ) (bumpR R).rOut := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero]
      have : R ≤ |R| := le_abs_self R
      have : |x.2| < |R| + 1 := by
        have := hxR.trans this
        linarith
      exact this
    exact ((bumpR R).pos_of_mem_ball hmem).ne'
  set ψ1 := fun x : ℝ × ℝ => Real.cos (2 * Real.pi * x.1 / d) * bumpR R x.2 with hψ1def
  set ψ2 := fun x : ℝ × ℝ => Real.sin (2 * Real.pi * x.1 / d) * bumpR R x.2 with hψ2def
  have hcover : UnforcedLeray.Short.IIIa.AdjE1.bandSet d R ⊆
      (UnforcedLeray.Short.IIIa.AdjE1.bandSet d R ∩ {x | ψ1 x ≠ 0}) ∪
        (UnforcedLeray.Short.IIIa.AdjE1.bandSet d R ∩ {x | ψ2 x ≠ 0}) := by
    intro x hx
    have hb := hbpos x hx
    by_cases hc : Real.cos (2 * Real.pi * x.1 / d) = 0
    · right
      refine ⟨hx, ?_⟩
      have hs : Real.sin (2 * Real.pi * x.1 / d) ≠ 0 := by
        intro hs
        have := Real.sin_sq_add_cos_sq (2 * Real.pi * x.1 / d)
        rw [hs, hc] at this
        norm_num at this
      exact mul_ne_zero hs hb
    · left
      exact ⟨hx, mul_ne_zero hc hb⟩
  have hsub1 : UnforcedLeray.Short.IIIa.AdjE1.bandSet d R ∩ {x | ψ1 x ≠ 0} ⊆ B0579.cell d :=
    fun x hx => hx.1.1
  have hsub2 : UnforcedLeray.Short.IIIa.AdjE1.bandSet d R ∩ {x | ψ2 x ≠ 0} ⊆ B0579.cell d :=
    fun x hx => hx.1.1
  have hm1 : MeasurableSet (UnforcedLeray.Short.IIIa.AdjE1.bandSet d R ∩ {x | ψ1 x ≠ 0}) :=
    (bandSet_measurable d R).inter ((measurableSet_singleton (0 : ℝ)).compl |> fun hs =>
      hψ1.continuous.measurable hs)
  have hm2 : MeasurableSet (UnforcedLeray.Short.IIIa.AdjE1.bandSet d R ∩ {x | ψ2 x ≠ 0}) :=
    (bandSet_measurable d R).inter ((measurableSet_singleton (0 : ℝ)).compl |> fun hs =>
      hψ2.continuous.measurable hs)
  have hS1 := aesm_of_ne_zero hψ1 (hint _ hψ1) hm1 hsub1 (fun x hx => hx.2)
  have hS2 := aesm_of_ne_zero hψ2 (hint _ hψ2) hm2 hsub2 (fun x hx => hx.2)
  exact AEStronglyMeasurable.mono_set hcover (aestronglyMeasurable_union_iff.2 ⟨hS1, hS2⟩)

#print axioms testMeasF
