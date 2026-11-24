import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.FlatWeakFromDensity.ErrorZero

/-!
# Part III-a, helper of `PartIII-a:T18/3/1/2`: the linear form of the extended integrand

The extended integrand `extWeakIntegrand ν μ F b G ψ φ p` is linear in the spatial test field:
it equals `∑ᵢ (coefA p i * φᵢ(x) + ∑ⱼ coefB p i j * ∂ⱼφᵢ(x))` with coefficients depending only on
`p` (and not on `φ`). Hence the difference of two such integrands is controlled by the difference of
the test fields and their gradients. The integrand vanishes off `Icc a u × cell` for the time support
`[a, u]` of `ψ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The coefficient of `φᵢ(x)` in `extWeakIntegrand`: `bᵢ (-ψ'(s) + (μ/s) ψ(s))` at `p = (s, x)`. -/
def coefA (μ : ℂ) (ψ : ℝ → ℝ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (p : ℝ × (ℝ × ℝ)) (i : Fin 2) : ℂ :=
  b p i * (-((deriv ψ p.1 : ℝ) : ℂ) + (μ / (p.1 : ℂ)) * ((ψ p.1 : ℝ) : ℂ))

/-- The coefficient of `∂ⱼφᵢ(x)` in `extWeakIntegrand`: `(ν Gᵢⱼ + Fᵢⱼ) ψ(s)` at `p = (s, x)`. -/
def coefB (ν : ℝ) (ψ : ℝ → ℝ) (F G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (p : ℝ × (ℝ × ℝ)) (i j : Fin 2) : ℂ :=
  ((ν : ℂ) * G p i j + F p i j) * (ψ p.1 : ℂ)

/-- The linear form of the extended integrand. -/
lemma extWeak_eq_lin (ν : ℝ) (μ : ℂ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (ψ : ℝ → ℝ) (φ : ℝ × ℝ → Fin 2 → ℝ) (p : ℝ × (ℝ × ℝ)) :
    extWeakIntegrand ν μ F b G ψ φ p =
      ∑ i : Fin 2, (coefA μ ψ b p i * (φ p.2 i : ℂ) +
        ∑ j : Fin 2, coefB ν ψ F G p i j * (B0579.pd j (fun y => φ y i) p.2 : ℂ)) := by
  simp only [extWeakIntegrand, coefA, coefB, Fin.sum_univ_two]
  push_cast
  ring

/-- The extended integrand vanishes at times outside the support interval `[a, u]` of `ψ`. -/
lemma extWeak_eq_zero_of_not_mem {ν : ℝ} {μ : ℂ} {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {ψ : ℝ → ℝ} {a u : ℝ} (hts : tsupport ψ ⊆ Icc a u) (φ : ℝ × ℝ → Fin 2 → ℝ)
    {p : ℝ × (ℝ × ℝ)} (hp : p.1 ∉ Icc a u) :
    extWeakIntegrand ν μ F b G ψ φ p = 0 := by
  obtain ⟨h0, h1⟩ := weight_zero_of_not_mem_Icc hts hp
  unfold extWeakIntegrand
  simp [h0, h1]

/-- The planar partial derivative of a smooth function is continuous. -/
lemma continuous_pd_of_contDiff {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (j : Fin 2) :
    Continuous (B0579.pd j f) := by
  unfold B0579.pd
  exact (hf.continuous_fderiv (by simp)).clm_apply continuous_const

/-- The extended integrand of a field whose components and partial derivatives are continuous is
measurable. -/
lemma measurable_extWeak {ν : ℝ} {μ : ℂ} {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (hb : ∀ i, Measurable fun p => b p i) (hG : ∀ i j, Measurable fun p => G p i j)
    (hF : ∀ i j, Measurable fun p => F p i j)
    {ψ : ℝ → ℝ} (hψ : Continuous ψ) (hdψ : Continuous (deriv ψ))
    {φ : ℝ × ℝ → Fin 2 → ℝ} (hφ : ∀ i, Continuous fun x => φ x i)
    (hpd : ∀ i j, Continuous fun x => B0579.pd j (fun y => φ y i) x) :
    Measurable (extWeakIntegrand ν μ F b G ψ φ) := by
  have hψC : Measurable fun p : ℝ × (ℝ × ℝ) => ((ψ p.1 : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (hψ.measurable.comp measurable_fst)
  have hdC : Measurable fun p : ℝ × (ℝ × ℝ) => ((deriv ψ p.1 : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (hdψ.measurable.comp measurable_fst)
  have hμm : Measurable fun p : ℝ × (ℝ × ℝ) => μ / (p.1 : ℂ) :=
    measurable_const.div (Complex.measurable_ofReal.comp measurable_fst)
  have hcA : ∀ i, Measurable fun p => coefA μ ψ b p i :=
    fun i => (hb i).mul (hdC.neg.add (hμm.mul hψC))
  have hcB : ∀ i j, Measurable fun p => coefB ν ψ F G p i j :=
    fun i j => (((measurable_const.mul (hG i j)).add (hF i j))).mul hψC
  have hφC : ∀ i, Measurable fun p : ℝ × (ℝ × ℝ) => (φ p.2 i : ℂ) :=
    fun i => Complex.measurable_ofReal.comp ((hφ i).measurable.comp measurable_snd)
  have hpdC : ∀ i j, Measurable fun p : ℝ × (ℝ × ℝ) => (B0579.pd j (fun y => φ y i) p.2 : ℂ) :=
    fun i j => Complex.measurable_ofReal.comp ((hpd i j).measurable.comp measurable_snd)
  have hfun : extWeakIntegrand ν μ F b G ψ φ = fun p => ∑ i : Fin 2,
      (coefA μ ψ b p i * (φ p.2 i : ℂ) +
        ∑ j : Fin 2, coefB ν ψ F G p i j * (B0579.pd j (fun y => φ y i) p.2 : ℂ)) :=
    funext fun p => extWeak_eq_lin ν μ F b G ψ φ p
  rw [hfun]
  exact Finset.measurable_sum _ fun i _ =>
    ((hcA i).mul (hφC i)).add (Finset.measurable_sum _ fun j _ => (hcB i j).mul (hpdC i j))

end UnforcedLeray.Short.IIIa
