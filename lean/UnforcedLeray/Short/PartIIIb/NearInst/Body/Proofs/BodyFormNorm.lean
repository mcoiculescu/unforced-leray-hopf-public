import UnforcedLeray.Short.PartIIIb.NearInst.Body.Forced

/-!
Proof of `BodyFormNorm` (source 1641-1646, 2676-2679: the two normalisations `dq` and `dq/c`
change every norm by the same factor `√c`, so a real form `R` of a complex body transport `R'`
satisfies `‖R f‖ ≤ ‖R'‖ ‖f‖`).  Route: `‖G‖² = c ‖g‖²` for `G = merC ∘ g ∘ cellPt`, applied to
`g = R f`, `G = R' (cplxH f)`, and to `f`, `cplxH f`.
-/

noncomputable section

open MeasureTheory Set UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Body

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Cons.C03.Concrete UnforcedLeray.B0223
open UnforcedLeray.B0220 (HSpace measureH Profile)

/-- `merC` is isometric. -/
theorem norm_merC_eq (b : Merid) : ‖merC b‖ = ‖b‖ := by
  simp [EuclideanSpace.norm_eq, merC, Complex.norm_real]

/-- The squared norm of an `L²` class is the integral of the squared enorm. -/
theorem lp_norm_sq_eq {E : Type*} [NormedAddCommGroup E] {α : Type*} [MeasurableSpace α]
    {ν : Measure α} (F : Lp E 2 ν) :
    ‖F‖ ^ 2 = (∫⁻ x, ‖(F : α → E) x‖ₑ ^ 2 ∂ν).toReal := by
  rw [Lp.norm_def, ← ENNReal.toReal_pow]
  congr 1
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- Transport of the squared norm along `φ ∘ · ∘ cellPt`: `‖G‖² = c ‖g‖²`. -/
theorem norm_sq_cellPt {c : ℝ} (hc : 0 ≤ c) (hH : Masked.CellPtH c)
    {E E' : Type*} [NormedAddCommGroup E] [NormedAddCommGroup E'] (φ : E → E')
    (hφ : ∀ b, ‖φ b‖ = ‖b‖) (g : Lp E 2 (ageμ c (-3 / 2))) (G : HSpace c E')
    (hG : (G : Profile → E') =ᵐ[measureH c] fun p => φ ((g : Chart → E) (cellPt c p))) :
    ‖G‖ ^ 2 = c * ‖g‖ ^ 2 := by
  have hH' : Measure.map (cellPt c) (measureH c) = ENNReal.ofReal c • ageμ c (-3 / 2) := hH
  have hgm : AEStronglyMeasurable (g : Chart → E) (ageμ c (-3 / 2)) := Lp.aestronglyMeasurable g
  have hm : AEMeasurable (fun x => ‖(g : Chart → E) x‖ₑ ^ 2)
      (Measure.map (cellPt c) (measureH c)) := by
    rw [hH']
    have h1 : AEMeasurable (fun x => ‖(g : Chart → E) x‖ₑ) (ageμ c (-3 / 2)) :=
      hgm.enorm
    exact ((h1).pow_const 2).smul_measure _
  have e1 : (fun p => ‖(G : Profile → E') p‖ₑ ^ 2) =ᵐ[measureH c]
      (fun p => ‖(g : Chart → E) (cellPt c p)‖ₑ ^ 2) := by
    filter_upwards [hG] with p hp
    rw [hp]
    have : ‖φ ((g : Chart → E) (cellPt c p))‖ₑ = ‖(g : Chart → E) (cellPt c p)‖ₑ := by
      rw [← ofReal_norm, ← ofReal_norm, hφ]
    rw [this]
  have hint : ∫⁻ p, ‖(g : Chart → E) (cellPt c p)‖ₑ ^ 2 ∂measureH c
      = ENNReal.ofReal c * ∫⁻ x, ‖(g : Chart → E) x‖ₑ ^ 2 ∂ageμ c (-3 / 2) := by
    calc ∫⁻ p, ‖(g : Chart → E) (cellPt c p)‖ₑ ^ 2 ∂measureH c
        = ∫⁻ x, ‖(g : Chart → E) x‖ₑ ^ 2 ∂(Measure.map (cellPt c) (measureH c)) :=
          (lintegral_map' hm (measurable_cellPt' c).aemeasurable).symm
      _ = ∫⁻ x, ‖(g : Chart → E) x‖ₑ ^ 2 ∂(ENNReal.ofReal c • ageμ c (-3 / 2)) := by rw [hH']
      _ = ENNReal.ofReal c * ∫⁻ x, ‖(g : Chart → E) x‖ₑ ^ 2 ∂ageμ c (-3 / 2) := by
          rw [lintegral_smul_measure, smul_eq_mul]
  rw [lp_norm_sq_eq G, lp_norm_sq_eq g, lintegral_congr_ae e1, hint, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hc]

theorem bodyFormNorm_of (hH : ∀ c : ℝ, 0 < c → Masked.CellPtH c)
    (hHi : ∀ c : ℝ, 0 < c → Masked.CellPtInvH c) : BodyFormNorm := by
  intro c hc R R' hR f
  clear hHi
  have hcf : cplxH c (hH c hc) f = cplxH c (hH c hc) f := rfl
  have hG := hR f (cplxH c (hH c hc) f) (cplxH_ae c (hH c hc) f)
  have key1 : ‖R' (cplxH c (hH c hc) f)‖ ^ 2 = c * ‖R f‖ ^ 2 :=
    norm_sq_cellPt hc.le (hH c hc) merC norm_merC_eq (R f) (R' (cplxH c (hH c hc) f)) hG
  have key2 : ‖cplxH c (hH c hc) f‖ ^ 2 = c * ‖f‖ ^ 2 :=
    norm_sq_cellPt hc.le (hH c hc) merC norm_merC_eq f (cplxH c (hH c hc) f)
      (cplxH_ae c (hH c hc) f)
  have hle : ‖R' (cplxH c (hH c hc) f)‖ ≤ ‖R'‖ * ‖cplxH c (hH c hc) f‖ :=
    R'.le_opNorm _
  have h2 : ‖R' (cplxH c (hH c hc) f)‖ ^ 2 ≤ (‖R'‖ * ‖cplxH c (hH c hc) f‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hle 2
  have h3 : c * ‖R f‖ ^ 2 ≤ c * (‖R'‖ * ‖f‖) ^ 2 := by
    rw [← key1]
    calc ‖R' (cplxH c (hH c hc) f)‖ ^ 2 ≤ (‖R'‖ * ‖cplxH c (hH c hc) f‖) ^ 2 := h2
      _ = ‖R'‖ ^ 2 * (c * ‖f‖ ^ 2) := by rw [mul_pow, key2]
      _ = c * (‖R'‖ * ‖f‖) ^ 2 := by ring
  have h4 : ‖R f‖ ^ 2 ≤ (‖R'‖ * ‖f‖) ^ 2 := le_of_mul_le_mul_left h3 hc
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h4

end UnforcedLeray.Short.PartIIIb.NearInst.Body
