import UnforcedLeray.Short.Spine.Sub.SP_EST
import UnforcedLeray.Lib.Train.VortexBounds
import UnforcedLeray.Lib.Train.Datum
import UnforcedLeray.Short.Spine.Proofs.EstDerivWordBridge
import UnforcedLeray.Short.Spine.Proofs.EstEuclidBridge

/-!
# Spine: the regularity of the periodized heat vortex (task `Spine:EstVcRegularity`)

Source of record: `the November 2 reference manuscript`, lines 327-336
(`‖D^j V_c^p‖_∞ ≤ C_j a^{-(3+j)/2}` for `1 ≤ a ≤ c²`, `a = 1 + ν s`).

Proof. Smoothness: with `r = √a`, the isolated vortex is a rescaled Gaussian profile,
`V(w) = r⁻³ • v₀(r⁻¹ • w)`, so `V_c(z) = r⁻³ • datum(c/r)(r⁻¹ • z)`, and `datum` is `C^∞`
(`Train.datum_contDiff`). Bounds: the word derivatives of each component are bounded by
`Train.Vc_bounds` (with `m = 0`), the generic bridge `norm_iteratedFDeriv_le_of_derivWord` gives
`‖D^j V_c^k‖ ≤ 2^j M`, and `norm_iteratedFDeriv_euclid2_le` sums the two components.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace UnforcedLeray.Short.Spine

/-- `a = 1 + ν s > 0` for `ν > 0`, `s ≥ 0`. -/
theorem vcReg_width_pos {ν s : ℝ} (hν : 0 < ν) (hs : 0 ≤ s) :
    0 < UnforcedLeray.Train.width ν s := by
  have := mul_nonneg hν.le hs
  unfold UnforcedLeray.Train.width
  linarith

/-- Scaling of the isolated vortex: with `r² = a`, `V(w) = r⁻³ • v₀(r⁻¹ • w)`. -/
theorem vcReg_isoV_scale (ν s r : ℝ) (hr2 : r ^ 2 = UnforcedLeray.Train.width ν s)
    (w : ℝ × ℝ) :
    UnforcedLeray.Train.isoV ν s w = r⁻¹ ^ 3 • UnforcedLeray.Train.v0 (r⁻¹ • w) := by
  have hG : UnforcedLeray.Train.gauss0 (r⁻¹ • w) =
      Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / (4 * r ^ 2)) := by
    unfold UnforcedLeray.Train.gauss0
    congr 1
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have hT : UnforcedLeray.Train.toVec (-(r⁻¹ • w).2, (r⁻¹ • w).1) =
      r⁻¹ • UnforcedLeray.Train.toVec (-w.2, w.1) := by
    rw [← UnforcedLeray.Train.toVec_smul]
    congr 1
    ext <;> simp
  rw [UnforcedLeray.Train.isoV_apply, ← hr2, UnforcedLeray.Train.v0, hG, hT, smul_smul,
    smul_smul]
  congr 1
  ring

/-- The periodized vortex is the rescaled periodized datum:
`V_c(z) = r⁻³ • datum(c/r)(r⁻¹ • z)` for `r² = a`. -/
theorem vcReg_Vc_scale (ν c s r : ℝ) (hr2 : r ^ 2 = UnforcedLeray.Train.width ν s)
    (z : ℝ × ℝ) :
    UnforcedLeray.Train.Vc ν c s z =
      r⁻¹ ^ 3 • UnforcedLeray.Train.datum (c / r) (r⁻¹ • z) := by
  have hpt : ∀ n : ℤ, r⁻¹ • (z.1 - n * c, z.2) =
      ((r⁻¹ • z).1 - n * (c / r), (r⁻¹ • z).2) := by
    intro n
    ext
    · simp only [Prod.smul_fst, smul_eq_mul]; ring
    · simp only [Prod.smul_snd, smul_eq_mul]
  unfold UnforcedLeray.Train.Vc UnforcedLeray.Train.datum UnforcedLeray.Gaussian.periodize
  rw [← tsum_const_smul'']
  refine tsum_congr fun n => ?_
  rw [vcReg_isoV_scale ν s r hr2, hpt n]

/-- Smoothness of the periodized vortex for `c > 0` and `a > 0`: `V_c` is `C^∞`. -/
theorem vcReg_contDiff_Vc {ν c s : ℝ} (hc : 0 < c) (ha : 0 < UnforcedLeray.Train.width ν s) :
    ContDiff ℝ ∞ (UnforcedLeray.Train.Vc ν c s) := by
  have hr : 0 < Real.sqrt (UnforcedLeray.Train.width ν s) := Real.sqrt_pos.2 ha
  have hr2 : Real.sqrt (UnforcedLeray.Train.width ν s) ^ 2 = UnforcedLeray.Train.width ν s :=
    Real.sq_sqrt ha.le
  have hfun : UnforcedLeray.Train.Vc ν c s = fun z : ℝ × ℝ =>
      (Real.sqrt (UnforcedLeray.Train.width ν s))⁻¹ ^ 3 •
        UnforcedLeray.Train.datum (c / Real.sqrt (UnforcedLeray.Train.width ν s))
          ((Real.sqrt (UnforcedLeray.Train.width ν s))⁻¹ • z) :=
    funext fun z => vcReg_Vc_scale ν c s _ hr2 z
  rw [hfun]
  have h1 : ContDiff ℝ ∞ (fun z : ℝ × ℝ => (Real.sqrt (UnforcedLeray.Train.width ν s))⁻¹ • z) :=
    contDiff_const_smul _
  have h2 : ContDiff ℝ ∞
      (UnforcedLeray.Train.datum (c / Real.sqrt (UnforcedLeray.Train.width ν s))) :=
    UnforcedLeray.Train.datum_contDiff (div_pos hc hr).ne'
  exact (h2.comp h1).const_smul _

/-- **`SP-EST/1`** (source lines 327-336): the regularity of the periodized heat vortex. -/
theorem vcRegularity_proof : UnforcedLeray.Short.Spine.VcRegularity := by
  unfold UnforcedLeray.Short.Spine.VcRegularity
  refine ⟨fun ν c s hν hc hs => ?_, fun j => ?_⟩
  · exact (vcReg_contDiff_Vc hc (vcReg_width_pos hν hs)).of_le (WithTop.coe_le_coe.2 le_top)
  · obtain ⟨C, b, hC, hb, h⟩ := UnforcedLeray.Train.Vc_bounds j 0
    refine ⟨2 ^ (j + 1) * C, fun ν c s hc ha1 hac z => ?_⟩
    have ha0 : (0 : ℝ) < UnforcedLeray.Train.width ν s := lt_of_lt_of_le one_pos ha1
    have hsm : ContDiff ℝ ∞ (UnforcedLeray.Train.Vc ν c s) := vcReg_contDiff_Vc hc ha0
    obtain ⟨h1, -, -⟩ := h ν c s hc ha1 hac
    have e : -(3 + (j : ℝ)) / 2 = -((3 + (j : ℝ)) / 2) := neg_div _ _
    have hk : ∀ k : Fin 2,
        ‖iteratedFDeriv ℝ j (fun x => UnforcedLeray.Train.Vc ν c s x k) z‖ ≤
          2 ^ j * (C * UnforcedLeray.B0113.heatWidth ν s ^ (-((3 + (j : ℝ)) / 2))) := by
      intro k
      have hfk : ContDiff ℝ ∞ (fun x => UnforcedLeray.Train.Vc ν c s x k) :=
        (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hsm
      refine norm_iteratedFDeriv_le_of_derivWord hfk j z ?_
      intro w hw
      have hw' := h1 w hw k z
      rw [pow_zero, one_mul, e] at hw'
      exact hw'
    calc ‖iteratedFDeriv ℝ j (UnforcedLeray.Train.Vc ν c s) z‖
        ≤ ‖iteratedFDeriv ℝ j (fun x => UnforcedLeray.Train.Vc ν c s x 0) z‖ +
            ‖iteratedFDeriv ℝ j (fun x => UnforcedLeray.Train.Vc ν c s x 1) z‖ :=
          norm_iteratedFDeriv_euclid2_le hsm j z
      _ ≤ 2 ^ j * (C * UnforcedLeray.B0113.heatWidth ν s ^ (-((3 + (j : ℝ)) / 2))) +
            2 ^ j * (C * UnforcedLeray.B0113.heatWidth ν s ^ (-((3 + (j : ℝ)) / 2))) :=
          add_le_add (hk 0) (hk 1)
      _ = 2 ^ (j + 1) * C * UnforcedLeray.B0113.heatWidth ν s ^ (-((3 + (j : ℝ)) / 2)) := by
          ring

end UnforcedLeray.Short.Spine
