import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_3_1.ViscIBP

/-!
# Combined energy integration by parts and `η`-cutoff error bound
(helper of `PartIII-b:C/flatset/col/7/1/1/3/1`)

Combines the scalar age IBP (`AgeIBP.lean`) and viscous cell IBP (`ViscIBP.lean`) across the
real and imaginary components of `b : Chart → Fin 2 → ℂ`, and bounds the `deriv (chiR R)` error
term by `C / R` using `sfcEnergy`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate InnerProductSpace ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0220 (Profile)
open UnforcedLeray.Short.IIIa (vnorm2 tnorm2)

theorem integrableOn_scalarResolvent {c s0 ν μ S R : ℝ} (hs0 : 0 < s0) (hR : 0 < R)
    {f : Profile → ℝ} (hf : ContDiff ℝ ∞ f) (hz : ∀ p : Profile, p.1 < s0 → f p = 0) :
    IntegrableOn (fun p : Chart => p.1 ^ (-(3 / 2 : ℝ)) * (scalarResolvent ν μ S R f p * f p))
      (Ioi (0 : ℝ) ×ˢ B0579.cell c) := by
  have h1 := integrableOn_ageIntegrand (c := c) (μ := μ) (S := S) hs0 hR hf hz
  have h2 := integrableOn_viscIntegrand (c := c) (ν := ν) (S := S) hs0 hR hf hz
  have h12 : IntegrableOn (fun p => ageIntegrand μ S R f p + viscIntegrand ν S R f p)
      (Ioi (0 : ℝ) ×ˢ B0579.cell c) := h1.add h2
  refine h12.congr_fun (fun p _ => ?_) (measurableSet_Ioi.prod (B0579.measurableSet_cell c))
  exact (scalarResolvent_mul_split ν μ S R f p).symm

theorem integral_scalarResolvent_ge {c s0 ν μ S R : ℝ} (hs0 : 0 < s0) (hR : 0 < R)
    {f : Profile → ℝ} (hf : ContDiff ℝ ∞ f)
    (hper : ∀ s q η : ℝ, f (s, (q + c, η)) = f (s, (q, η)))
    (hz : ∀ p : Profile, p.1 < s0 → f p = 0) :
    (∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
        p.1 ^ (-(3 / 2 : ℝ)) * ((μ + 1 / 4) * thetaS S p.1 * chiR R p.2.2 * (f p) ^ 2)) +
      (∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, viscMain ν S R f p) +
      (∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, viscErr ν S R f p) ≤
      ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
        p.1 ^ (-(3 / 2 : ℝ)) * (scalarResolvent ν μ S R f p * f p) := by
  have h1 := integrableOn_ageIntegrand (c := c) (μ := μ) (S := S) hs0 hR hf hz
  have h2 := integrableOn_viscIntegrand (c := c) (ν := ν) (S := S) hs0 hR hf hz
  have hsplit : ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
        p.1 ^ (-(3 / 2 : ℝ)) * (scalarResolvent ν μ S R f p * f p) =
      (∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, ageIntegrand μ S R f p) +
      (∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, viscIntegrand ν S R f p) := by
    rw [← integral_add h1 h2]
    exact setIntegral_congr_fun (measurableSet_Ioi.prod (B0579.measurableSet_cell c))
      (fun p _ => scalarResolvent_mul_split ν μ S R f p)
  rw [hsplit, integral_viscIntegrand_eq hs0 hR hf hper hz]
  linarith [integral_ageIntegrand_ge (c := c) (μ := μ) (S := S) hs0 hR hf hz]

/-- Coercive velocity density `(μ + 1/4) s^{-3/2} θ_S(s) χ_R(η) |b|²`. -/
def energyMainV (μ S R : ℝ) (b : Chart → Fin 2 → ℂ) (p : Chart) : ℝ :=
  p.1 ^ (-(3 / 2 : ℝ)) * ((μ + 1 / 4) * thetaS S p.1 * chiR R p.2.2 * vnorm2 (b p) ^ 2)

/-- Coercive gradient density `ν s^{-1/2} θ_S(s) χ_R(η) |∇b|²`. -/
def energyMainG (ν S R : ℝ) (b : Chart → Fin 2 → ℂ) (p : Chart) : ℝ :=
  p.1 ^ (-(1 / 2 : ℝ)) * (ν * thetaS S p.1 * chiR R p.2.2 *
    tnorm2 (fun i j => cellGrad b p i j) ^ 2)

/-- Total `η`-cutoff error density across the 4 real components of `b`. -/
def energyErr (ν S R : ℝ) (b : Chart → Fin 2 → ℂ) (p : Chart) : ℝ :=
  (viscErr ν S R (uRe b 0) p + viscErr ν S R (uIm b 0) p) +
  (viscErr ν S R (uRe b 1) p + viscErr ν S R (uIm b 1) p)

theorem integrableOn_energyMainV {c s0 μ S R : ℝ} {b : Chart → Fin 2 → ℂ}
    (hb : SmoothRep c b) (hs0 : 0 < s0) (hz : ∀ p : Chart, p.1 < s0 → b p = 0) (hR : 0 < R) :
    IntegrableOn (energyMainV μ S R b) (Ioi (0 : ℝ) ×ˢ B0579.cell c) := by
  have hcont := smoothRep_contDiff hb hs0 hz
  have h0r := integrableOn_agePiece1 (c := c) (S := S) hs0 hR (μ + 1 / 4) (contDiff_uRe (hcont 0))
    (fun p hp => by unfold uRe; rw [hz p hp]; simp)
  have h0i := integrableOn_agePiece1 (c := c) (S := S) hs0 hR (μ + 1 / 4) (contDiff_uIm (hcont 0))
    (fun p hp => by unfold uIm; rw [hz p hp]; simp)
  have h1r := integrableOn_agePiece1 (c := c) (S := S) hs0 hR (μ + 1 / 4) (contDiff_uRe (hcont 1))
    (fun p hp => by unfold uRe; rw [hz p hp]; simp)
  have h1i := integrableOn_agePiece1 (c := c) (S := S) hs0 hR (μ + 1 / 4) (contDiff_uIm (hcont 1))
    (fun p hp => by unfold uIm; rw [hz p hp]; simp)
  have hsum : IntegrableOn (fun p : Chart =>
      (p.1 ^ (-(3 / 2 : ℝ)) * ((μ + 1 / 4) * thetaS S p.1 * chiR R p.2.2 * (uRe b 0 p) ^ 2) +
       p.1 ^ (-(3 / 2 : ℝ)) * ((μ + 1 / 4) * thetaS S p.1 * chiR R p.2.2 * (uIm b 0 p) ^ 2)) +
      (p.1 ^ (-(3 / 2 : ℝ)) * ((μ + 1 / 4) * thetaS S p.1 * chiR R p.2.2 * (uRe b 1 p) ^ 2) +
       p.1 ^ (-(3 / 2 : ℝ)) * ((μ + 1 / 4) * thetaS S p.1 * chiR R p.2.2 * (uIm b 1 p) ^ 2)))
      (Ioi (0 : ℝ) ×ˢ B0579.cell c) := (h0r.add h0i).add (h1r.add h1i)
  refine hsum.congr_fun (fun p _ => ?_) (measurableSet_Ioi.prod (B0579.measurableSet_cell c))
  unfold energyMainV
  rw [vnorm2_sq_eq_sum_uRe_uIm, Fin.sum_univ_two]
  ring

theorem integrableOn_energyMainG {c s0 ν S R : ℝ} {b : Chart → Fin 2 → ℂ}
    (hb : SmoothRep c b) (hs0 : 0 < s0) (hz : ∀ p : Chart, p.1 < s0 → b p = 0) (hR : 0 < R) :
    IntegrableOn (energyMainG ν S R b) (Ioi (0 : ℝ) ×ˢ B0579.cell c) := by
  have hcont := smoothRep_contDiff hb hs0 hz
  have h0r := integrableOn_viscMain (c := c) (ν := ν) (S := S) hs0 hR (contDiff_uRe (hcont 0))
    (fun p hp => by unfold uRe; rw [hz p hp]; simp)
  have h0i := integrableOn_viscMain (c := c) (ν := ν) (S := S) hs0 hR (contDiff_uIm (hcont 0))
    (fun p hp => by unfold uIm; rw [hz p hp]; simp)
  have h1r := integrableOn_viscMain (c := c) (ν := ν) (S := S) hs0 hR (contDiff_uRe (hcont 1))
    (fun p hp => by unfold uRe; rw [hz p hp]; simp)
  have h1i := integrableOn_viscMain (c := c) (ν := ν) (S := S) hs0 hR (contDiff_uIm (hcont 1))
    (fun p hp => by unfold uIm; rw [hz p hp]; simp)
  have hsum : IntegrableOn (fun p : Chart =>
      (viscMain ν S R (uRe b 0) p + viscMain ν S R (uIm b 0) p) +
      (viscMain ν S R (uRe b 1) p + viscMain ν S R (uIm b 1) p))
      (Ioi (0 : ℝ) ×ˢ B0579.cell c) := (h0r.add h0i).add (h1r.add h1i)
  refine hsum.congr_fun (fun p _ => ?_) (measurableSet_Ioi.prod (B0579.measurableSet_cell c))
  unfold energyMainG viscMain
  rw [tnorm2_cellGrad_sq_eq_sum_uRe_uIm hcont, Fin.sum_univ_two]
  ring

theorem integrableOn_energyErr {c s0 ν S R : ℝ} {b : Chart → Fin 2 → ℂ}
    (hb : SmoothRep c b) (hs0 : 0 < s0) (hz : ∀ p : Chart, p.1 < s0 → b p = 0) (hR : 0 < R) :
    IntegrableOn (energyErr ν S R b) (Ioi (0 : ℝ) ×ˢ B0579.cell c) := by
  have hcont := smoothRep_contDiff hb hs0 hz
  have h0r := integrableOn_viscErr (c := c) (ν := ν) (S := S) hs0 hR (contDiff_uRe (hcont 0))
    (fun p hp => by unfold uRe; rw [hz p hp]; simp)
  have h0i := integrableOn_viscErr (c := c) (ν := ν) (S := S) hs0 hR (contDiff_uIm (hcont 0))
    (fun p hp => by unfold uIm; rw [hz p hp]; simp)
  have h1r := integrableOn_viscErr (c := c) (ν := ν) (S := S) hs0 hR (contDiff_uRe (hcont 1))
    (fun p hp => by unfold uRe; rw [hz p hp]; simp)
  have h1i := integrableOn_viscErr (c := c) (ν := ν) (S := S) hs0 hR (contDiff_uIm (hcont 1))
    (fun p hp => by unfold uIm; rw [hz p hp]; simp)
  exact (h0r.add h0i).add (h1r.add h1i)

theorem integral_resolventTest_zetaCut_ge {c s0 ν μ S R : ℝ} {b : Chart → Fin 2 → ℂ}
    (hb : SmoothRep c b) (hs0 : 0 < s0) (hz : ∀ p : Chart, p.1 < s0 → b p = 0) (hR : 0 < R) :
    (∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, energyMainV μ S R b p) +
      (∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, energyMainG ν S R b p) +
      (∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, energyErr ν S R b p) ≤
      ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
        p.1 ^ (-(3 / 2 : ℝ)) * (inner ℂ (resolventTest ν μ (zetaCut S R b) p) (bm b p)).re := by
  have hcont := smoothRep_contDiff hb hs0 hz
  have hper := smoothRep_periodic hb
  have hz_re : ∀ (i : Fin 2) (p : Profile), p.1 < s0 → uRe b i p = 0 :=
    fun i p hp => by unfold uRe; rw [hz p hp]; simp
  have hz_im : ∀ (i : Fin 2) (p : Profile), p.1 < s0 → uIm b i p = 0 :=
    fun i p hp => by unfold uIm; rw [hz p hp]; simp
  have hper_re : ∀ (i : Fin 2) (s q η : ℝ), uRe b i (s, (q + c, η)) = uRe b i (s, (q, η)) :=
    fun i s q η => by unfold uRe; rw [hper s q η]
  have hper_im : ∀ (i : Fin 2) (s q η : ℝ), uIm b i (s, (q + c, η)) = uIm b i (s, (q, η)) :=
    fun i s q η => by unfold uIm; rw [hper s q η]
  have hI0r := integral_scalarResolvent_ge (c := c) (ν := ν) (μ := μ) (S := S) hs0 hR
    (contDiff_uRe (hcont 0)) (hper_re 0) (hz_re 0)
  have hI0i := integral_scalarResolvent_ge (c := c) (ν := ν) (μ := μ) (S := S) hs0 hR
    (contDiff_uIm (hcont 0)) (hper_im 0) (hz_im 0)
  have hI1r := integral_scalarResolvent_ge (c := c) (ν := ν) (μ := μ) (S := S) hs0 hR
    (contDiff_uRe (hcont 1)) (hper_re 1) (hz_re 1)
  have hI1i := integral_scalarResolvent_ge (c := c) (ν := ν) (μ := μ) (S := S) hs0 hR
    (contDiff_uIm (hcont 1)) (hper_im 1) (hz_im 1)
  -- Integrability of each piece to combine integrals
  have iS0r := integrableOn_scalarResolvent (c := c) (ν := ν) (μ := μ) (S := S) hs0 hR (contDiff_uRe (hcont 0)) (hz_re 0)
  have iS0i := integrableOn_scalarResolvent (c := c) (ν := ν) (μ := μ) (S := S) hs0 hR (contDiff_uIm (hcont 0)) (hz_im 0)
  have iS1r := integrableOn_scalarResolvent (c := c) (ν := ν) (μ := μ) (S := S) hs0 hR (contDiff_uRe (hcont 1)) (hz_re 1)
  have iS1i := integrableOn_scalarResolvent (c := c) (ν := ν) (μ := μ) (S := S) hs0 hR (contDiff_uIm (hcont 1)) (hz_im 1)
  have iV0r := integrableOn_agePiece1 (c := c) (S := S) hs0 hR (μ + 1 / 4) (contDiff_uRe (hcont 0)) (hz_re 0)
  have iV0i := integrableOn_agePiece1 (c := c) (S := S) hs0 hR (μ + 1 / 4) (contDiff_uIm (hcont 0)) (hz_im 0)
  have iV1r := integrableOn_agePiece1 (c := c) (S := S) hs0 hR (μ + 1 / 4) (contDiff_uRe (hcont 1)) (hz_re 1)
  have iV1i := integrableOn_agePiece1 (c := c) (S := S) hs0 hR (μ + 1 / 4) (contDiff_uIm (hcont 1)) (hz_im 1)
  have iG0r := integrableOn_viscMain (c := c) (ν := ν) (S := S) hs0 hR (contDiff_uRe (hcont 0)) (hz_re 0)
  have iG0i := integrableOn_viscMain (c := c) (ν := ν) (S := S) hs0 hR (contDiff_uIm (hcont 0)) (hz_im 0)
  have iG1r := integrableOn_viscMain (c := c) (ν := ν) (S := S) hs0 hR (contDiff_uRe (hcont 1)) (hz_re 1)
  have iG1i := integrableOn_viscMain (c := c) (ν := ν) (S := S) hs0 hR (contDiff_uIm (hcont 1)) (hz_im 1)
  have iE0r := integrableOn_viscErr (c := c) (ν := ν) (S := S) hs0 hR (contDiff_uRe (hcont 0)) (hz_re 0)
  have iE0i := integrableOn_viscErr (c := c) (ν := ν) (S := S) hs0 hR (contDiff_uIm (hcont 0)) (hz_im 0)
  have iE1r := integrableOn_viscErr (c := c) (ν := ν) (S := S) hs0 hR (contDiff_uRe (hcont 1)) (hz_re 1)
  have iE1i := integrableOn_viscErr (c := c) (ν := ν) (S := S) hs0 hR (contDiff_uIm (hcont 1)) (hz_im 1)
  have hRHS : ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
        p.1 ^ (-(3 / 2 : ℝ)) * (inner ℂ (resolventTest ν μ (zetaCut S R b) p) (bm b p)).re =
      ((∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, p.1 ^ (-(3 / 2 : ℝ)) * (scalarResolvent ν μ S R (uRe b 0) p * uRe b 0 p)) +
       (∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, p.1 ^ (-(3 / 2 : ℝ)) * (scalarResolvent ν μ S R (uIm b 0) p * uIm b 0 p))) +
      ((∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, p.1 ^ (-(3 / 2 : ℝ)) * (scalarResolvent ν μ S R (uRe b 1) p * uRe b 1 p)) +
       (∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, p.1 ^ (-(3 / 2 : ℝ)) * (scalarResolvent ν μ S R (uIm b 1) p * uIm b 1 p))) := by
    have iS0 : IntegrableOn (fun p : Chart =>
        p.1 ^ (-(3 / 2 : ℝ)) * (scalarResolvent ν μ S R (uRe b 0) p * uRe b 0 p) +
        p.1 ^ (-(3 / 2 : ℝ)) * (scalarResolvent ν μ S R (uIm b 0) p * uIm b 0 p))
        (Ioi (0 : ℝ) ×ˢ B0579.cell c) := iS0r.add iS0i
    have iS1 : IntegrableOn (fun p : Chart =>
        p.1 ^ (-(3 / 2 : ℝ)) * (scalarResolvent ν μ S R (uRe b 1) p * uRe b 1 p) +
        p.1 ^ (-(3 / 2 : ℝ)) * (scalarResolvent ν μ S R (uIm b 1) p * uIm b 1 p))
        (Ioi (0 : ℝ) ×ˢ B0579.cell c) := iS1r.add iS1i
    rw [← integral_add iS0r iS0i, ← integral_add iS1r iS1i, ← integral_add iS0 iS1]
    refine setIntegral_congr_fun (measurableSet_Ioi.prod (B0579.measurableSet_cell c)) fun p _ => ?_
    rw [inner_resolventTest_zetaCut_re ν μ S R hcont p, Fin.sum_univ_two]
    ring
  have hV : ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, energyMainV μ S R b p =
      ((∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, p.1 ^ (-(3 / 2 : ℝ)) * ((μ + 1 / 4) * thetaS S p.1 * chiR R p.2.2 * (uRe b 0 p) ^ 2)) +
       (∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, p.1 ^ (-(3 / 2 : ℝ)) * ((μ + 1 / 4) * thetaS S p.1 * chiR R p.2.2 * (uIm b 0 p) ^ 2))) +
      ((∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, p.1 ^ (-(3 / 2 : ℝ)) * ((μ + 1 / 4) * thetaS S p.1 * chiR R p.2.2 * (uRe b 1 p) ^ 2)) +
       (∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, p.1 ^ (-(3 / 2 : ℝ)) * ((μ + 1 / 4) * thetaS S p.1 * chiR R p.2.2 * (uIm b 1 p) ^ 2))) := by
    have iV0 : IntegrableOn (fun p : Chart =>
        p.1 ^ (-(3 / 2 : ℝ)) * ((μ + 1 / 4) * thetaS S p.1 * chiR R p.2.2 * (uRe b 0 p) ^ 2) +
        p.1 ^ (-(3 / 2 : ℝ)) * ((μ + 1 / 4) * thetaS S p.1 * chiR R p.2.2 * (uIm b 0 p) ^ 2))
        (Ioi (0 : ℝ) ×ˢ B0579.cell c) := iV0r.add iV0i
    have iV1 : IntegrableOn (fun p : Chart =>
        p.1 ^ (-(3 / 2 : ℝ)) * ((μ + 1 / 4) * thetaS S p.1 * chiR R p.2.2 * (uRe b 1 p) ^ 2) +
        p.1 ^ (-(3 / 2 : ℝ)) * ((μ + 1 / 4) * thetaS S p.1 * chiR R p.2.2 * (uIm b 1 p) ^ 2))
        (Ioi (0 : ℝ) ×ˢ B0579.cell c) := iV1r.add iV1i
    rw [← integral_add iV0r iV0i, ← integral_add iV1r iV1i, ← integral_add iV0 iV1]
    refine setIntegral_congr_fun (measurableSet_Ioi.prod (B0579.measurableSet_cell c)) fun p _ => ?_
    unfold energyMainV
    rw [vnorm2_sq_eq_sum_uRe_uIm, Fin.sum_univ_two]
    ring
  have hG : ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, energyMainG ν S R b p =
      ((∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, viscMain ν S R (uRe b 0) p) +
       (∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, viscMain ν S R (uIm b 0) p)) +
      ((∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, viscMain ν S R (uRe b 1) p) +
       (∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, viscMain ν S R (uIm b 1) p)) := by
    have iG0 : IntegrableOn (fun p : Chart =>
        viscMain ν S R (uRe b 0) p + viscMain ν S R (uIm b 0) p)
        (Ioi (0 : ℝ) ×ˢ B0579.cell c) := iG0r.add iG0i
    have iG1 : IntegrableOn (fun p : Chart =>
        viscMain ν S R (uRe b 1) p + viscMain ν S R (uIm b 1) p)
        (Ioi (0 : ℝ) ×ˢ B0579.cell c) := iG1r.add iG1i
    rw [← integral_add iG0r iG0i, ← integral_add iG1r iG1i, ← integral_add iG0 iG1]
    refine setIntegral_congr_fun (measurableSet_Ioi.prod (B0579.measurableSet_cell c)) fun p _ => ?_
    unfold energyMainG viscMain
    rw [tnorm2_cellGrad_sq_eq_sum_uRe_uIm hcont, Fin.sum_univ_two]
    ring
  have hE : ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, energyErr ν S R b p =
      ((∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, viscErr ν S R (uRe b 0) p) +
       (∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, viscErr ν S R (uIm b 0) p)) +
      ((∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, viscErr ν S R (uRe b 1) p) +
       (∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, viscErr ν S R (uIm b 1) p)) := by
    have iE0 : IntegrableOn (fun p : Chart =>
        viscErr ν S R (uRe b 0) p + viscErr ν S R (uIm b 0) p)
        (Ioi (0 : ℝ) ×ˢ B0579.cell c) := iE0r.add iE0i
    have iE1 : IntegrableOn (fun p : Chart =>
        viscErr ν S R (uRe b 1) p + viscErr ν S R (uIm b 1) p)
        (Ioi (0 : ℝ) ×ˢ B0579.cell c) := iE1r.add iE1i
    rw [← integral_add iE0r iE0i, ← integral_add iE1r iE1i, ← integral_add iE0 iE1]
    rfl
  rw [hRHS, hV, hG, hE]
  linarith

/-- Pointwise bound on `|energyErr ν S R b p|` for `p.1 ≥ s0`. -/
theorem abs_energyErr_le {ν s0 S R B : ℝ} (hν : 0 < ν) (hs0 : 0 < s0) (hR : 0 < R)
    (hB : ∀ t, |deriv GradPerpCut.chi t| ≤ B) {b : Chart → Fin 2 → ℂ}
    (hb : ∀ i : Fin 2, ContDiff ℝ ∞ (fun p : Chart => b p i)) {p : Chart} (hp : s0 ≤ p.1) :
    |energyErr ν S R b p| ≤
      (ν * s0 ^ (-(1 / 2 : ℝ)) * B / R) *
        (vnorm2 (b p) ^ 2 + tnorm2 (fun i j => cellGrad b p i j) ^ 2) := by
  have hp0 : 0 < p.1 := lt_of_lt_of_le hs0 hp
  have hr : p.1 ^ (-(1 / 2 : ℝ)) ≤ s0 ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hs0 hp (by norm_num)
  have hr0 : 0 ≤ p.1 ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hp0.le _
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  have hch := abs_deriv_chiR_le hB hR p.2.2
  have hth0 := thetaS_nonneg S p.1
  have hth1 := thetaS_le_one S p.1
  have hcoef : p.1 ^ (-(1 / 2 : ℝ)) * (ν * thetaS S p.1 * |deriv (chiR R) p.2.2|) ≤
      ν * s0 ^ (-(1 / 2 : ℝ)) * B / R := by
    have h1 : ν * thetaS S p.1 ≤ ν * 1 := mul_le_mul_of_nonneg_left hth1 hν.le
    have h2 : p.1 ^ (-(1 / 2 : ℝ)) * (ν * thetaS S p.1) ≤ s0 ^ (-(1 / 2 : ℝ)) * ν := by
      calc p.1 ^ (-(1 / 2 : ℝ)) * (ν * thetaS S p.1)
          ≤ s0 ^ (-(1 / 2 : ℝ)) * (ν * 1) :=
            mul_le_mul hr h1 (mul_nonneg hν.le hth0) (Real.rpow_nonneg hs0.le _)
        _ = s0 ^ (-(1 / 2 : ℝ)) * ν := by ring
    calc p.1 ^ (-(1 / 2 : ℝ)) * (ν * thetaS S p.1 * |deriv (chiR R) p.2.2|)
        = (p.1 ^ (-(1 / 2 : ℝ)) * (ν * thetaS S p.1)) * |deriv (chiR R) p.2.2| := by ring
      _ ≤ (s0 ^ (-(1 / 2 : ℝ)) * ν) * (B / R) :=
          mul_le_mul h2 hch (abs_nonneg _) (by positivity)
      _ = ν * s0 ^ (-(1 / 2 : ℝ)) * B / R := by ring
  have hterm : ∀ f : Profile → ℝ,
      |viscErr ν S R f p| ≤
        (ν * s0 ^ (-(1 / 2 : ℝ)) * B / R) *
          (f p ^ 2 + (B0579.pd 0 (fun y => f (p.1, y)) p.2 ^ 2 +
            B0579.pd 1 (fun y => f (p.1, y)) p.2 ^ 2)) := by
    intro f
    unfold viscErr
    have had : |f p * B0579.pd 1 (fun y => f (p.1, y)) p.2| ≤
        f p ^ 2 + (B0579.pd 0 (fun y => f (p.1, y)) p.2 ^ 2 +
          B0579.pd 1 (fun y => f (p.1, y)) p.2 ^ 2) := by
      have hsq : 0 ≤ (|f p| - |B0579.pd 1 (fun y => f (p.1, y)) p.2|) ^ 2 := sq_nonneg _
      have h0 : 0 ≤ B0579.pd 0 (fun y => f (p.1, y)) p.2 ^ 2 := sq_nonneg _
      rw [abs_mul]
      nlinarith [sq_abs (f p), sq_abs (B0579.pd 1 (fun y => f (p.1, y)) p.2)]
    have heq_v : p.1 ^ (-(1 / 2 : ℝ)) * (ν * thetaS S p.1 * deriv (chiR R) p.2.2 *
        f p * B0579.pd 1 (fun y => f (p.1, y)) p.2) =
      (p.1 ^ (-(1 / 2 : ℝ)) * (ν * thetaS S p.1)) * deriv (chiR R) p.2.2 *
        (f p * B0579.pd 1 (fun y => f (p.1, y)) p.2) := by ring
    rw [heq_v, abs_mul, abs_mul, abs_of_nonneg (mul_nonneg hr0 (mul_nonneg hν.le hth0))]
    calc (p.1 ^ (-(1 / 2 : ℝ)) * (ν * thetaS S p.1) * |deriv (chiR R) p.2.2|) *
          |f p * B0579.pd 1 (fun y => f (p.1, y)) p.2|
        = (p.1 ^ (-(1 / 2 : ℝ)) * (ν * thetaS S p.1 * |deriv (chiR R) p.2.2|)) *
          |f p * B0579.pd 1 (fun y => f (p.1, y)) p.2| := by ring
      _ ≤ (ν * s0 ^ (-(1 / 2 : ℝ)) * B / R) *
          (f p ^ 2 + (B0579.pd 0 (fun y => f (p.1, y)) p.2 ^ 2 +
            B0579.pd 1 (fun y => f (p.1, y)) p.2 ^ 2)) :=
          mul_le_mul hcoef had (abs_nonneg _) (by positivity)
  unfold energyErr
  have h1 := (abs_add_le _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add (hterm (uRe b 0)) (hterm (uIm b 0))))
    ((abs_add_le _ _).trans (add_le_add (hterm (uRe b 1)) (hterm (uIm b 1)))))
  refine h1.trans (le_of_eq ?_)
  rw [vnorm2_sq_eq_sum_uRe_uIm, tnorm2_cellGrad_sq_eq_sum_uRe_uIm hb,
    Fin.sum_univ_two, Fin.sum_univ_two]
  ring

/-- Uniform `C / R` bound on the `η`-cutoff error integral for fixed `S`, using `sfcEnergy`. -/
theorem exists_energyErr_bound {c ν μ s0 : ℝ} {hc : 0 < c} {R0 : Hsp c →L[ℝ] Hsp c} {g : Hsp c}
    (hctx : ClassicalCtx c ν μ hc R0 g) {b : Chart → Fin 2 → ℂ} (hb : SmoothRep c b)
    (hbe : b =ᵐ[ageμ c (-3 / 2)] NearInst.velC (R0 g)) (hs0 : 0 < s0)
    (hz : ∀ p : Chart, p.1 < s0 → b p = 0) (S : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      -(C / R) ≤ ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, energyErr ν S R b p := by
  have hcont := smoothRep_contDiff hb hs0 hz
  obtain ⟨B, hB⟩ := GradPerpCut.exists_bound_deriv_chi
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  set s1 : ℝ := max (s0 + 1) (S + 1)
  have hs01 : s0 < s1 := lt_of_lt_of_le (by linarith) (le_max_left (s0 + 1) (S + 1))
  set K : Set Chart := Icc s0 s1 ×ˢ B0579.cell c
  have hKm : MeasurableSet K := measurableSet_Icc.prod (B0579.measurableSet_cell c)
  have hsub : K ⊆ Ioi (0 : ℝ) ×ˢ B0579.cell c :=
    fun p hp => ⟨lt_of_lt_of_le hs0 hp.1.1, hp.2⟩
  have hfin := sfcEnergy c ν μ hc R0 g hctx b hb hbe s0 s1 hs0 hs01
  set E : Chart → ℝ := fun p => vnorm2 (b p) ^ 2 + tnorm2 (fun i j => cellGrad b p i j) ^ 2
  have hE0 : ∀ p, 0 ≤ E p := fun p => add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hEcont : Continuous E := by
    have heq : E = fun p : Chart =>
        ((uRe b 0 p ^ 2 + uIm b 0 p ^ 2) + (uRe b 1 p ^ 2 + uIm b 1 p ^ 2)) +
        (((B0579.pd 0 (fun y => uRe b 0 (p.1, y)) p.2 ^ 2 +
           B0579.pd 1 (fun y => uRe b 0 (p.1, y)) p.2 ^ 2) +
          (B0579.pd 0 (fun y => uIm b 0 (p.1, y)) p.2 ^ 2 +
           B0579.pd 1 (fun y => uIm b 0 (p.1, y)) p.2 ^ 2)) +
         ((B0579.pd 0 (fun y => uRe b 1 (p.1, y)) p.2 ^ 2 +
           B0579.pd 1 (fun y => uRe b 1 (p.1, y)) p.2 ^ 2) +
          (B0579.pd 0 (fun y => uIm b 1 (p.1, y)) p.2 ^ 2 +
           B0579.pd 1 (fun y => uIm b 1 (p.1, y)) p.2 ^ 2))) := by
      funext p
      unfold E
      rw [vnorm2_sq_eq_sum_uRe_uIm, tnorm2_cellGrad_sq_eq_sum_uRe_uIm hcont,
        Fin.sum_univ_two, Fin.sum_univ_two]
    rw [heq]
    have c0r := (contDiff_uRe (hcont 0)).continuous
    have c0i := (contDiff_uIm (hcont 0)).continuous
    have c1r := (contDiff_uRe (hcont 1)).continuous
    have c1i := (contDiff_uIm (hcont 1)).continuous
    have d0r0 := continuous_pd_slice (contDiff_uRe (hcont 0)) 0
    have d0r1 := continuous_pd_slice (contDiff_uRe (hcont 0)) 1
    have d0i0 := continuous_pd_slice (contDiff_uIm (hcont 0)) 0
    have d0i1 := continuous_pd_slice (contDiff_uIm (hcont 0)) 1
    have d1r0 := continuous_pd_slice (contDiff_uRe (hcont 1)) 0
    have d1r1 := continuous_pd_slice (contDiff_uRe (hcont 1)) 1
    have d1i0 := continuous_pd_slice (contDiff_uIm (hcont 1)) 0
    have d1i1 := continuous_pd_slice (contDiff_uIm (hcont 1)) 1
    exact (((c0r.pow 2).add (c0i.pow 2)).add ((c1r.pow 2).add (c1i.pow 2))).add
      ((((d0r0.pow 2).add (d0r1.pow 2)).add ((d0i0.pow 2).add (d0i1.pow 2))).add
       (((d1r0.pow 2).add (d1r1.pow 2)).add ((d1i0.pow 2).add (d1i1.pow 2))))
  have hEint : IntegrableOn E K := by
    refine ⟨hEcont.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    refine (lintegral_congr fun p => ?_).trans_lt hfin
    exact Real.enorm_eq_ofReal (hE0 p)
  have hEK0 : 0 ≤ ∫ p in K, E p := setIntegral_nonneg hKm (fun p _ => hE0 p)
  have hν : 0 < ν := hctx.1
  refine ⟨ν * s0 ^ (-(1 / 2 : ℝ)) * B * ∫ p in K, E p, by positivity, fun R hR => ?_⟩
  have hsub_eq : ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, energyErr ν S R b p =
      ∫ p in K, energyErr ν S R b p := by
    rw [← integral_indicator (measurableSet_Ioi.prod (B0579.measurableSet_cell c)),
      ← integral_indicator hKm]
    congr 1
    funext p
    by_cases hpK : p ∈ K
    · rw [indicator_of_mem (hsub hpK), indicator_of_mem hpK]
    · rw [indicator_of_notMem hpK]
      by_cases hpS : p ∈ Ioi (0 : ℝ) ×ˢ B0579.cell c
      · rw [indicator_of_mem hpS]
        have hpnot : p.1 < s0 ∨ s1 < p.1 := by
          by_contra h
          push_neg at h
          exact hpK ⟨h, hpS.2⟩
        unfold energyErr viscErr
        rcases hpnot with hlt | hgt
        · have h0r : uRe b 0 p = 0 := by unfold uRe; rw [hz p hlt]; simp
          have h0i : uIm b 0 p = 0 := by unfold uIm; rw [hz p hlt]; simp
          have h1r : uRe b 1 p = 0 := by unfold uRe; rw [hz p hlt]; simp
          have h1i : uIm b 1 p = 0 := by unfold uIm; rw [hz p hlt]; simp
          rw [h0r, h0i, h1r, h1i]
          ring
        · have hS1 : S + 1 ≤ p.1 := le_trans (le_max_right (s0 + 1) (S + 1)) hgt.le
          rw [thetaS_eq_zero hS1]
          ring
      · rw [indicator_of_notMem hpS]
  rw [hsub_eq]
  have hErrK : IntegrableOn (energyErr ν S R b) K :=
    (integrableOn_energyErr hb hs0 hz hR).mono_set hsub
  have hle : ∫ p in K, -((ν * s0 ^ (-(1 / 2 : ℝ)) * B / R) * E p) ≤
      ∫ p in K, energyErr ν S R b p := by
    refine setIntegral_mono_on (hEint.const_mul _).neg hErrK hKm fun p hp => ?_
    have habs := abs_energyErr_le (S := S) hν hs0 hR hB hcont hp.1.1
    exact neg_le_of_abs_le habs
  rw [integral_neg, integral_const_mul] at hle
  have heq : -((ν * s0 ^ (-(1 / 2 : ℝ)) * B / R) * ∫ p in K, E p) =
      -((ν * s0 ^ (-(1 / 2 : ℝ)) * B * ∫ p in K, E p) / R) := by ring
  rw [heq] at hle
  exact hle

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
