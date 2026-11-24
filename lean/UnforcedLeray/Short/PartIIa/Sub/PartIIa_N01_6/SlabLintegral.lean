import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_6
import UnforcedLeray.Short.PartIIa.Tasks.F13EnergyIdentity

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.PhaseSpace

/-- `PartII-a:N01/6/4` slab inner product as an iterated lintegral (Tonelli; a phase test is
continuous with bounded support). -/
theorem slabToLintegral : UnforcedLeray.Short.PartIIa.N01.SlabToLintegral := by
  intro P _ T hT
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure (ℝ × Space),
      μ = (volume.restrict (Ioc (0 : ℝ) P)).prod (volume : Measure Space) := ⟨_, rfl⟩
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ × Space → ℝ,
      G = fun z => ∑ i : Fin 3, ∑ j : Fin 3, (T z.1 z.2 i j) ^ 2 := ⟨_, rfl⟩
  have hin : ∀ (i : Fin 3) (z : ℝ × Space),
      inner ℂ (cartRowsC T i z) (cartRowsC T i z) =
        ((∑ j : Fin 3, (T z.1 z.2 i j) ^ 2 : ℝ) : ℂ) := by
    intro i z
    simp only [cartRowsC, PiLp.inner_apply, RCLike.inner_apply, Complex.conj_ofReal,
      Complex.ofReal_sum, Complex.ofReal_mul, sq]
  have hsum_eq : ∀ z : ℝ × Space,
      ∑ i : Fin 3, inner ℂ (cartRowsC T i z) (cartRowsC T i z) = ((G z : ℝ) : ℂ) := by
    intro z
    simp only [hin, hGdef, Complex.ofReal_sum]
  have hGnn : ∀ z, 0 ≤ G z := by
    intro z
    rw [hGdef]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hIc : ∀ i : Fin 3, Continuous (fun z : ℝ × Space =>
      inner ℂ (cartRowsC T i z) (cartRowsC T i z)) :=
    fun i => (hT i).continuous.inner (hT i).continuous
  have hGc : Continuous G := by
    have hH : Continuous (fun z : ℝ × Space => ∑ i : Fin 3,
        inner ℂ (cartRowsC T i z) (cartRowsC T i z)) :=
      continuous_finsetSum _ fun i _ => hIc i
    have h := Complex.continuous_re.comp hH
    convert h using 1
    funext z
    simp only [Function.comp_apply, hsum_eq z, Complex.ofReal_re]
  have hIntI : ∀ i : Fin 3, Integrable (fun z : ℝ × Space =>
      inner ℂ (cartRowsC T i z) (cartRowsC T i z)) μ := by
    intro i
    rw [hμ]
    exact integrable_slab_of_test (isPhaseTest_inner (hT i) (hT i))
  have hIntG : Integrable (fun z : ℝ × Space => ((G z : ℝ) : ℂ)) μ := by
    have hfun : (fun z : ℝ × Space => ((G z : ℝ) : ℂ)) =
        fun z => ∑ i ∈ Finset.univ, inner ℂ (cartRowsC T i z) (cartRowsC T i z) :=
      funext fun z => (hsum_eq z).symm
    rw [hfun]
    exact integrable_finsetSum _ fun i _ => hIntI i
  have hGint : Integrable G μ := by
    have h := hIntG.re
    simpa using h
  have hsl : ∀ i : Fin 3, slabInner P (cartRowsC T i) (cartRowsC T i) =
      ∫ z, inner ℂ (cartRowsC T i z) (cartRowsC T i z) ∂μ := by
    intro i
    rw [hμ]
    exact slabInner_eq (hT i) (hT i)
  have hL : ∑ i : Fin 3, (slabInner P (cartRowsC T i) (cartRowsC T i)).re = ∫ z, G z ∂μ := by
    simp only [hsl]
    rw [← Complex.re_sum, ← integral_finsetSum Finset.univ (fun i _ => hIntI i)]
    simp only [hsum_eq]
    rw [integral_complex_ofReal, Complex.ofReal_re]
  rw [hL, ofReal_integral_eq_lintegral_ofReal hGint (ae_of_all _ hGnn), hμ,
    lintegral_prod _ (hGc.measurable.ennreal_ofReal.aemeasurable)]
  rw [hGdef]

end UnforcedLeray.Short.PartIIa.N01
