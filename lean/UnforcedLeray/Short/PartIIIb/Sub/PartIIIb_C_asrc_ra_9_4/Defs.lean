import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_van

/-!
# `PartIII-b:C/asrc/ra/9/4/org` : the leaves of `GradRemBound`

Source of record: `the November 2 reference manuscript`
(73 pages), lines 5039-5043 (`s^{3/2}∇_{q,η}Ψ_A = ∇_y(sΨ_A) + εs^{3/2}(𝒦+2)Ψ_A e_r`), 5076-5079
(derivative budget, Gaussian cell norms), 4978 (Gaussian decay of the lattice sums), 5024 (`Ψ_A`).

With `F = sΨ_A`, `gradRem = -ε(2s∂_sF + η∂_ηF) e_r = -ε s (𝒦+2)Ψ_A e_r`, hence
`‖gradRem‖ = ε s |(𝒦+2)Ψ_A|` and the cell bound of `gradRem` is the factor `ε s` times the
cell bound `≤ P_ν M(A)(s^{3/2}+s^{5/2})` of `(𝒦+2)Ψ_A`.

* `GradRemVanish` : `gradRem = 0` for `s > 1.1/ν`;
* `GradRemCont` : continuity of `gradRem` on `s > 0` (from `AffPsiC1`);
* `GradRemNorm` : the pointwise identity `‖gradRem‖ = ε s |(𝒦+2)Ψ_A|` on `s > 0`;
* `PsiKCellL2` : the Gaussian-summation cell `L²` bound of `(𝒦+2)Ψ_A`;
* `gradRemBound_of` : `GradRemBound` from the four and `AffPsiC1` (measure theory and algebra).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest Params)

/-- **Vanishing for `s > 1.1/ν`** (source 4978, 5039-5043): `Ψ_A = 0` for `ν s ≥ 1.1`
(`PsiA_eq_zero`), so `sΨ_A` vanishes on the open set `s > 1.1/ν` and its partial derivatives
`dS`, `dEta` vanish there; hence `gradRem = 0`. -/
def GradRemVanish (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (p : Params) (μ : ℝ) (A : ℝ → Mat3), IsAffElem as A →
    ∀ s : ℝ, (11 / 10) / p.ν < s → ∀ x : ℝ × ℝ, gradRem p μ χf A (s, x) = 0

/-- **Continuity of `gradRem` on `s > 0`** (source 5024, 5040-5043, 4978): `sΨ_A` is `C¹` on
`s > 0` (`AffPsiC1`), so `dS`, `dEta` of it are continuous there, and so is
`gradRem = (-ε(2s dS F + η dEta F), 0)`.  Consequence of `AffPsiC1`. -/
def GradRemCont (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  AffPsiC1 as χf → IsSourceCutoffC χf → ∀ (p : Params) (μ : ℝ) (A : ℝ → Mat3), IsAffElem as A →
    ContinuousOn (gradRem p μ χf A) (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)))

/-- **The pointwise identity** (source 5039-5043): on `s > 0`, where `sΨ_A` is `C¹`
(so `Ψ_A = (sΨ_A)/s` is `C¹`, and `2s dS(sΨ_A) + η dEta(sΨ_A) = s((𝒦+2)Ψ_A)` with
`𝒦Ψ = Kop Ψ = η∂_ηΨ + 2s∂_sΨ`), `‖gradRem‖ = ε s |(𝒦+2)Ψ_A|`. -/
def GradRemNorm (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  AffPsiC1 as χf → IsSourceCutoffC χf → ∀ (p : Params) (μ : ℝ) (A : ℝ → Mat3), IsAffElem as A →
    ∀ q : Chart, 0 < q.1 →
      ‖gradRem p μ χf A q‖ =
        p.ε * q.1 * |Kop (fun s' y => PsiA p.ν χf A s' y) q.1 q.2 + 2 * PsiA p.ν χf A q.1 q.2|

/-- **Gaussian summation** (source 5063-5071, 5076-5079): the cell `L²` norm of
`(𝒦+2)Ψ_A`, `Ψ_A = Σ_j (A^y_mer x_j)·∇p_j`, is `≤ P_ν M(A)(s^{3/2}+s^{5/2})` on
`0 < s ≤ 1.1/ν`, uniformly for small `ν` (normalized cell norm of the `Ψ_A`-type sums). -/
def PsiKCellL2 (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
    ∀ (ν : ℝ), 0 < ν → ν ≤ ν₀ → ∀ A : ℝ → Mat3, IsAffElem as A →
      ∀ s : ℝ, 0 < s → s ≤ (11 / 10) / ν →
        ∫⁻ x, ENNReal.ofReal (|Kop (fun s' y => PsiA ν χf A s' y) s x + 2 * PsiA ν χf A s x| ^ 2)
            ∂(UnforcedLeray.Cyl.avgμ (cOf ν))
          ≤ ENNReal.ofReal ((C * ν⁻¹ ^ k * affM ν χf A * (s ^ (3 / 2 : ℝ) + s ^ (5 / 2 : ℝ))) ^ 2)

theorem aesm_of_contOn_pos {g : Chart → Merid} (c : ℝ)
    (h : ContinuousOn g (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)))) :
    AEStronglyMeasurable g (srcMeasure c) := by
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    measurableSet_Ioi.prod MeasurableSet.univ
  have h1 : AEStronglyMeasurable g ((srcMeasure c).restrict (Ioi (0 : ℝ) ×ˢ univ)) :=
    h.aestronglyMeasurable hS
  have hae : ∀ᵐ q ∂(srcMeasure c), q ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) := by
    have := srcMeasure_nonpos c
    rw [ae_iff]
    refine measure_mono_null (fun q hq => ?_) this
    by_contra hpos
    have hp : 0 < q.1 := not_le.1 hpos
    exact hq ⟨hp, mem_univ _⟩
  rwa [Measure.restrict_eq_self_of_ae_mem hae] at h1

/-- **`GradRemBound` from the four leaves and `AffPsiC1`.** -/
theorem gradRemBound_of (as : ℝ) (χf : ℝ → ℝ) (h1 : GradRemVanish as χf) (h2 : GradRemCont as χf)
    (h3 : GradRemNorm as χf) (h4 : PsiKCellL2 as χf) (h5 : AffPsiC1 as χf) :
    GradRemBound as χf := by
  intro hχ K hK hKs dm dp hdm
  obtain ⟨C, k, ν₀, hν₀, H⟩ := h4 hχ
  refine ⟨C, k, ν₀, hν₀, fun p d hreg hν μ hμ A hA => ?_⟩
  have hcont := h2 h5 hχ p μ A hA
  have hc : p.c = cOf p.ν := hreg.c_eq
  have hε : 0 < p.ε := p.ε_pos
  refine ⟨aesm_of_contOn_pos p.c hcont, fun s hs x => h1 hχ p μ A hA s hs x,
    fun s hs => ?_, fun s hs hs1 => ?_⟩
  · have hco : Continuous (fun x : ℝ × ℝ => gradRem p μ χf A (s, x)) := by
      have hsub : Continuous (fun x : ℝ × ℝ => ((s, x) : Chart)) := by fun_prop
      exact (hcont.comp_continuous hsub (fun x => ⟨hs, mem_univ _⟩))
    exact hco.aestronglyMeasurable
  · have hH := H p.ν p.ν_pos hν A hA s hs hs1
    rw [← hc] at hH
    have hsum : s ^ (5 / 2 : ℝ) + s ^ (7 / 2 : ℝ) = s * (s ^ (3 / 2 : ℝ) + s ^ (5 / 2 : ℝ)) := by
      have e1 : s ^ (5 / 2 : ℝ) = s * s ^ (3 / 2 : ℝ) := by
        rw [show (5 / 2 : ℝ) = 1 + 3 / 2 by norm_num, Real.rpow_add hs, Real.rpow_one]
      have e2 : s ^ (7 / 2 : ℝ) = s * s ^ (5 / 2 : ℝ) := by
        rw [show (7 / 2 : ℝ) = 1 + 5 / 2 by norm_num, Real.rpow_add hs, Real.rpow_one]
      rw [e2, e1]; ring
    have hεs : 0 ≤ p.ε * s := by positivity
    have hn : ∀ x : ℝ × ℝ, ‖gradRem p μ χf A (s, x)‖ ^ 2 = (p.ε * s) ^ 2 *
        |Kop (fun s' y => PsiA p.ν χf A s' y) s x + 2 * PsiA p.ν χf A s x| ^ 2 := by
      intro x
      rw [h3 h5 hχ p μ A hA (s, x) hs, mul_pow]
    calc ∫⁻ x, ENNReal.ofReal (‖gradRem p μ χf A (s, x)‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ p.c)
        = ∫⁻ x, ENNReal.ofReal ((p.ε * s) ^ 2) * ENNReal.ofReal
            (|Kop (fun s' y => PsiA p.ν χf A s' y) s x + 2 * PsiA p.ν χf A s x| ^ 2)
              ∂(UnforcedLeray.Cyl.avgμ p.c) := by
          refine lintegral_congr fun x => ?_
          rw [hn x, ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal ((p.ε * s) ^ 2) * ∫⁻ x, ENNReal.ofReal
            (|Kop (fun s' y => PsiA p.ν χf A s' y) s x + 2 * PsiA p.ν χf A s x| ^ 2)
              ∂(UnforcedLeray.Cyl.avgμ p.c) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal ((p.ε * s) ^ 2) * ENNReal.ofReal
            ((C * p.ν⁻¹ ^ k * affM p.ν χf A * (s ^ (3 / 2 : ℝ) + s ^ (5 / 2 : ℝ))) ^ 2) := by
          gcongr
      _ = ENNReal.ofReal ((C * p.ν⁻¹ ^ k * p.ε * affM p.ν χf A *
            (s ^ (5 / 2 : ℝ) + s ^ (7 / 2 : ℝ))) ^ 2) := by
          rw [← ENNReal.ofReal_mul (by positivity), hsum]
          congr 1
          ring

end UnforcedLeray.Short.PartIIIb.Concrete
