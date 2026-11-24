import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_3_3
import UnforcedLeray.Lib.Cylinder.IBP

/-!
# Part III-a, task `PartIII-a:T21/2/3/3/1`: smooth periodic functions have classical weak
cell derivatives (SP 3074-3075)

For `Φ` smooth and `d`-periodic in `q`, and a cylinder test `ψ` (`B0579.IsCylTest d ψ`), the
identity `∫_cell Φ ∂_j ψ = -∫_cell (∂_j Φ) ψ` is the partial integration of
`Lib/Cylinder/IBP` (`integral_cell_partialQ_mul` for `j = 0`, using the periodicity of `Φ` and
`ψ`; `integral_cell_partialEta_mul` for `j = 1`, using that `ψ` vanishes for `|η|` large).
The integrability on the cell follows from the vanishing of `ψ` and of its classical derivatives
for `|η|` large.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- A function vanishing for `|η| > R` has vanishing classical derivatives there. -/
lemma mpVanishFderiv {ψ : ℝ × ℝ → ℝ} {R : ℝ} (hR : ∀ x : ℝ × ℝ, R < |x.2| → ψ x = 0)
    (v : ℝ × ℝ) (x : ℝ × ℝ) (hx : R < |x.2|) : fderiv ℝ ψ x v = 0 := by
  have hopen : IsOpen {w : ℝ × ℝ | R < |w.2|} :=
    isOpen_lt continuous_const (continuous_abs.comp continuous_snd)
  have hev : ψ =ᶠ[𝓝 x] (0 : ℝ × ℝ → ℝ) := by
    filter_upwards [hopen.mem_nhds hx] with w hw
    exact hR w hw
  rw [hev.fderiv_eq]
  simp

/-- The classical derivative of a real function, viewed as complex valued. -/
lemma mpOfRealFderiv (ψ : ℝ × ℝ → ℝ) (hψ : Differentiable ℝ ψ) (z v : ℝ × ℝ) :
    fderiv ℝ (fun x => ((ψ x : ℝ) : ℂ)) z v = ((fderiv ℝ ψ z v : ℝ) : ℂ) := by
  have h : HasFDerivAt (fun x => ((ψ x : ℝ) : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ ψ z)) z :=
    Complex.ofRealCLM.hasFDerivAt.comp z (hψ z).hasFDerivAt
  rw [h.fderiv]
  rfl

lemma mpWeakCore (d : ℝ) (hd : 0 < d) (Φ : ℝ × ℝ → ℂ) (hΦs : ContDiff ℝ ∞ Φ)
    (hper : ∀ x : ℝ × ℝ, Φ (x.1 + d, x.2) = Φ x) (j : Fin 2) (ψ : ℝ × ℝ → ℝ)
    (hψ : B0579.IsCylTest d ψ) :
    IntegrableOn (fun x => Φ x * (B0579.pd j ψ x : ℂ)) (B0579.cell d) ∧
      IntegrableOn (fun x => pdCx j Φ x * (ψ x : ℂ)) (B0579.cell d) ∧
      ∫ x in B0579.cell d, Φ x * (B0579.pd j ψ x : ℂ) =
        -∫ x in B0579.cell d, pdCx j Φ x * (ψ x : ℂ) := by
  have hcell : B0579.cell d = UnforcedLeray.Cyl.cell d := by
    unfold B0579.cell UnforcedLeray.Cyl.cell
    rw [neg_div]
  rw [hcell]
  obtain ⟨R, hR⟩ := hψ.band
  have hψs : ContDiff ℝ ∞ ψ := hψ.smooth
  have hψd : Differentiable ℝ ψ := hψs.differentiable (by simp)
  have hΦd : Differentiable ℝ Φ := hΦs.differentiable (by simp)
  have hΦc : Continuous Φ := hΦs.continuous
  have hψc : Continuous ψ := hψs.continuous
  have hψk : Continuous (fun x => fderiv ℝ ψ x (B0579.dir j)) :=
    ((hψs.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  have hΦk : Continuous (fun x => fderiv ℝ Φ x (B0579.dir j)) :=
    ((hΦs.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  have hψC : Continuous (fun x => ((ψ x : ℝ) : ℂ)) := Complex.continuous_ofReal.comp hψc
  -- integrability of the two summands
  have i1 : IntegrableOn (fun x => Φ x * (B0579.pd j ψ x : ℂ)) (UnforcedLeray.Cyl.cell d) := by
    have hv : UnforcedLeray.Cyl.VanishesOutside R (fun x => Φ x * (B0579.pd j ψ x : ℂ)) :=
      fun x hx => by
        have h0 : fderiv ℝ ψ x (B0579.dir j) = 0 := mpVanishFderiv hR (B0579.dir j) x hx
        simp [B0579.pd, h0]
    exact hv.integrableOn_cell (hΦc.mul (Complex.continuous_ofReal.comp hψk)) d
  have i2 : IntegrableOn (fun x => pdCx j Φ x * (ψ x : ℂ)) (UnforcedLeray.Cyl.cell d) := by
    have hv : UnforcedLeray.Cyl.VanishesOutside R (fun x => pdCx j Φ x * (ψ x : ℂ)) :=
      fun x hx => by simp [hR x hx]
    exact hv.integrableOn_cell (hΦk.mul hψC) d
  refine ⟨i1, i2, ?_⟩
  have hψCd : Differentiable ℝ (fun x => ((ψ x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.differentiable.comp hψd
  have hψper : UnforcedLeray.Cyl.IsPeriodic d (fun x => ((ψ x : ℝ) : ℂ)) := fun z => by
    show ((ψ (z.1 + d, z.2) : ℝ) : ℂ) = ((ψ z : ℝ) : ℂ)
    rw [hψ.periodic z]
  have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  rcases hj with rfl | rfl
  · have eΦ : ∀ z, UnforcedLeray.Cyl.partialQ Φ z = pdCx 0 Φ z := fun z => by
      rw [UnforcedLeray.Cyl.partialQ_eq_fderiv hΦd z]
      rfl
    have eψ : ∀ z, UnforcedLeray.Cyl.partialQ (fun x => ((ψ x : ℝ) : ℂ)) z =
        ((B0579.pd 0 ψ z : ℝ) : ℂ) := fun z => by
      rw [UnforcedLeray.Cyl.partialQ_eq_fderiv hψCd z]
      exact mpOfRealFderiv ψ hψd z (1, 0)
    have h1 : IntegrableOn (fun z => UnforcedLeray.Cyl.partialQ Φ z * ((ψ z : ℝ) : ℂ))
        (UnforcedLeray.Cyl.cell d) := by
      have hv : UnforcedLeray.Cyl.VanishesOutside R (fun z => pdCx 0 Φ z * ((ψ z : ℝ) : ℂ)) :=
        fun x hx => by simp [hR x hx]
      have := hv.integrableOn_cell (hΦk.mul hψC) d
      simpa only [eΦ] using this
    have h2 : IntegrableOn
        (fun z => Φ z * UnforcedLeray.Cyl.partialQ (fun x => ((ψ x : ℝ) : ℂ)) z)
        (UnforcedLeray.Cyl.cell d) := by
      simpa only [eψ] using i1
    have hmain := UnforcedLeray.Cyl.integral_cell_partialQ_mul hd hΦd hψCd hper hψper h1 h2
    simp only [eΦ, eψ] at hmain
    rw [hmain, neg_neg]
  · have eΦ : ∀ z, UnforcedLeray.Cyl.partialEta Φ z = pdCx 1 Φ z := fun z => by
      rw [UnforcedLeray.Cyl.partialEta_eq_fderiv hΦd z]
      rfl
    have eψ : ∀ z, UnforcedLeray.Cyl.partialEta (fun x => ((ψ x : ℝ) : ℂ)) z =
        ((B0579.pd 1 ψ z : ℝ) : ℂ) := fun z => by
      rw [UnforcedLeray.Cyl.partialEta_eq_fderiv hψCd z]
      exact mpOfRealFderiv ψ hψd z (0, 1)
    have h0 : IntegrableOn (fun z => Φ z * ((ψ z : ℝ) : ℂ)) (UnforcedLeray.Cyl.cell d) := by
      have hv : UnforcedLeray.Cyl.VanishesOutside R (fun z => Φ z * ((ψ z : ℝ) : ℂ)) :=
        fun x hx => by simp [hR x hx]
      exact hv.integrableOn_cell (hΦc.mul hψC) d
    have h1 : IntegrableOn (fun z => UnforcedLeray.Cyl.partialEta Φ z * ((ψ z : ℝ) : ℂ))
        (UnforcedLeray.Cyl.cell d) := by
      have hv : UnforcedLeray.Cyl.VanishesOutside R (fun z => pdCx 1 Φ z * ((ψ z : ℝ) : ℂ)) :=
        fun x hx => by simp [hR x hx]
      have := hv.integrableOn_cell (hΦk.mul hψC) d
      simpa only [eΦ] using this
    have h2 : IntegrableOn
        (fun z => Φ z * UnforcedLeray.Cyl.partialEta (fun x => ((ψ x : ℝ) : ℂ)) z)
        (UnforcedLeray.Cyl.cell d) := by
      simpa only [eψ] using i1
    have hmain := UnforcedLeray.Cyl.integral_cell_partialEta_mul hΦd hψCd h0 h1 h2
    simp only [eΦ, eψ] at hmain
    rw [hmain, neg_neg]

/-- **Leaf** (SP 3074-3075): smooth periodic functions have classical weak cell derivatives. -/
theorem mpWeakFromSmooth : MpWeakFromSmooth := by
  intro d hd Φ hΦ hper j
  unfold HasWeakCellDerivC
  exact ⟨fun ψ hψ => ⟨(mpWeakCore d hd Φ hΦ hper j ψ hψ).1,
      (mpWeakCore d hd Φ hΦ hper j ψ hψ).2.1⟩,
    fun ψ hψ => (mpWeakCore d hd Φ hΦ hper j ψ hψ).2.2⟩

end UnforcedLeray.Short.IIIa
