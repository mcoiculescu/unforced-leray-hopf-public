import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradRecovery

/-!
# Physical profile graph bound with polynomial dependence on `Γ`

Source of record: `the November 2 reference manuscript`, lines 1912-1938 and
1992-1996. Refines `profileGraphPhys_of` (`Sub/PartII-b_T10.lean`) to expose the explicit
`O(Γ²)` dependence on `‖μ‖ ≤ Γ` and `(Re μ + (3/r - 1)/2)⁻¹ ≤ Γ`, together with the
`hMeas c r`-measurability of `Sb`, `√s Qb`, `√s Eb`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Short.PartIIa

theorem phys_graph_poly (r : ℝ) (hr1 : 1 < r) (hr3 : r < 3) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Γ ν c ε : ℝ) (μ : ℂ), 1 ≤ Γ → ‖μ‖ ≤ Γ → Γ⁻¹ ≤ μ.re + (3 / r - 1) / 2 →
        0 < ν → 0 < c → 0 < ε → ε ≤ 1 → 2 * ε * c ≤ 1 →
      ∀ F b : CProf, InHr c r F → IsResponse ν c ε μ r F b →
        ∃ Sb Qb Eb : CProf,
          HasWeakVec vS dZero b Sb ∧ HasWeakVec (vQ ε) (dQ ε) b Qb ∧
          HasWeakVec vEta dZero b Eb ∧
          AEStronglyMeasurable Sb (hMeas c r) ∧
          AEStronglyMeasurable (sqrtS Qb) (hMeas c r) ∧
          AEStronglyMeasurable (sqrtS Eb) (hMeas c r) ∧
          hNorm c r b + hNorm c r Sb +
              ENNReal.ofReal (Real.sqrt ν) * (hNorm c r (sqrtS Qb) + hNorm c r (sqrtS Eb)) ≤
            ENNReal.ofReal (C * Γ ^ 2) * hNorm c r F := by
  have hr0 : 0 < r := by linarith
  obtain ⟨C₁, hC₁0, hC₁⟩ := field_graph_bound lerayPairSol solSeparation hr1 hr3
  obtain ⟨K, hK, hKb⟩ := gradBound_proof r hr1 hr3
  have hRK : 0 < max 2 K := lt_max_of_lt_left (by norm_num)
  refine ⟨3 * max 2 K * C₁ + 1, by positivity, ?_⟩
  intro Γ ν c ε μ hΓ1 hμΓ hgap hν hc hε hε1 hP F b hF hb
  have hΓ0 : 0 < Γ := lt_of_lt_of_le one_pos hΓ1
  have hμ : 0 < μ.re + (3 / r - 1) / 2 := lt_of_lt_of_le (inv_pos.mpr hΓ0) hgap
  have hP0 : 0 < 2 * ε * c := by positivity
  set A : ℝ := 1 + (1 + ‖μ‖) / (μ.re + (3 / r - 1) / 2) with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hbY : IsInYr (2 * ε * c) r (NvC ε⁻¹ b) := hb.mem_w
  obtain ⟨b', hbb'p, hbb'h, hb'H, hNN⟩ := profileRegularize_proof c ε r b hc hε hr0 hbY
  have hb'R : IsFreeResponse ν μ r (2 * ε * c) (NvC ε⁻¹ F) (NvC ε⁻¹ b') :=
    freeResponseCongr_proof ν μ r _ _ _ _ _ hP0 Filter.EventuallyEq.rfl hNN.symm hb
  have hfY := nvCInYr_proof c ε r F hc hε hr0 hF
  obtain ⟨a, haY, hap⟩ := hb'R.lapl
  obtain ⟨d, hdY, hdp⟩ := hb'R.drift
  obtain ⟨g, hgY, hgp, hbound⟩ := hC₁ (2 * ε * c) ν μ _ _ hP0 hP hν hμ hfY hb'R
  have hbd := hbound a d haY hap hdY hdp
  obtain ⟨Sb, hSb, hSbH, hSbn⟩ := driftRecovery_proof c ε r b' d hc hε hr1 hb'H hdY hdp
  obtain ⟨Qb, Eb, hQ, hE, hQp, hQm, hEp, hEm⟩ :=
    gradWeak_proof c ε r b' g hc hε hr1 hr3 hb'H hgY hgp
  have hQEn :
      ENNReal.ofReal ((Real.pi * (ε⁻¹) ^ 2) ^ (1 / r)) *
          (hNorm c r (sqrtS Qb) + hNorm c r (sqrtS Eb)) ≤
        ENNReal.ofReal K * ∑ j, phaseLpNorm (2 * ε * c) r (g j) := by
    have e1 := phaseLpNorm_NvC hc hr0 hε (sqrtS Qb) hQp hQm
    have e2 := phaseLpNorm_NvC hc hr0 hε (sqrtS Eb) hEp hEm
    have := hKb c ε b' g Qb Eb hc hε hb'H hgY hgp hQ hE hQp hQm hEp hEm
    rw [e1, e2, ← mul_add] at this
    exact this
  have hNb : phaseLpNorm (2 * ε * c) r (NvC ε⁻¹ b') =
      ENNReal.ofReal ((Real.pi * (ε⁻¹) ^ 2) ^ (1 / r)) * hNorm c r b' :=
    phaseLpNorm_NvC hc hr0 hε b' hb'H.periodic hb'H.meas
  have hNF : phaseLpNorm (2 * ε * c) r (NvC ε⁻¹ F) =
      ENNReal.ofReal ((Real.pi * (ε⁻¹) ^ 2) ^ (1 / r)) * hNorm c r F :=
    phaseLpNorm_NvC hc hr0 hε F hF.periodic hF.meas
  have hbb : hNorm c r b = hNorm c r b' := eLpNorm_congr_ae hbb'h.symm
  have hsym : ∀ᵐ x ∂posReg, b x = b' x := hbb'p.mono fun x hx => hx.symm
  refine ⟨Sb, Qb, Eb,
    weakVecCongr_proof vS dZero b' b Sb hsym hSb,
    weakVecCongr_proof _ _ b' b Qb hsym hQ,
    weakVecCongr_proof _ _ b' b Eb hsym hE,
    hSbH.meas, hQm, hEm, ?_⟩
  rw [hbb]
  set κ : ℝ≥0∞ := ENNReal.ofReal ((Real.pi * (ε⁻¹) ^ 2) ^ (1 / r)) with hκ
  have hκ0 : κ ≠ 0 := by
    rw [hκ, Ne, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hκt : κ ≠ ⊤ := ENNReal.ofReal_ne_top
  have fw := hb'R.mem_w.finite
  have fd := hdY.finite
  have ff := hfY.finite
  have fg : ∀ j, phaseLpNorm (2 * ε * c) r (g j) ≠ ⊤ := fun j => (hgY j).finite.ne
  set Nw := phaseLpNorm (2 * ε * c) r (NvC ε⁻¹ b') with hNw
  set Nd := phaseLpNorm (2 * ε * c) r d with hNd
  set Nf := phaseLpNorm (2 * ε * c) r (NvC ε⁻¹ F) with hNf
  set G := ∑ j, phaseLpNorm (2 * ε * c) r (g j) with hG
  have step1 : κ * (hNorm c r b' + hNorm c r Sb +
        ENNReal.ofReal (Real.sqrt ν) * (hNorm c r (sqrtS Qb) + hNorm c r (sqrtS Eb))) ≤
      Nw + (Nd + Nw) + ENNReal.ofReal (Real.sqrt ν) * (ENNReal.ofReal K * G) := by
    rw [mul_add, mul_add, ← hNb, mul_left_comm]
    gcongr
  have hreal : Nw + (Nd + Nw) + ENNReal.ofReal (Real.sqrt ν) * (ENNReal.ofReal K * G) ≤
      ENNReal.ofReal (max 2 K * C₁ * A + 1) * Nf := by
    have hGr : G = ENNReal.ofReal (∑ j, (phaseLpNorm (2 * ε * c) r (g j)).toReal) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => ENNReal.toReal_nonneg)]
      exact Finset.sum_congr rfl fun j _ => (ENNReal.ofReal_toReal (fg j)).symm
    have hNwr : Nw = ENNReal.ofReal Nw.toReal := (ENNReal.ofReal_toReal fw.ne).symm
    have hNdr : Nd = ENNReal.ofReal Nd.toReal := (ENNReal.ofReal_toReal fd.ne).symm
    have hNfr : Nf = ENNReal.ofReal Nf.toReal := (ENNReal.ofReal_toReal ff.ne).symm
    set gr : ℝ := ∑ j, (phaseLpNorm (2 * ε * c) r (g j)).toReal with hgr
    have hgr0 : 0 ≤ gr := Finset.sum_nonneg fun j _ => ENNReal.toReal_nonneg
    have ha0 : 0 ≤ (phaseLpNorm (2 * ε * c) r a).toReal := ENNReal.toReal_nonneg
    have hsq : 0 ≤ Real.sqrt ν := Real.sqrt_nonneg ν
    have hnw : 0 ≤ Nw.toReal := ENNReal.toReal_nonneg
    have hnd : 0 ≤ Nd.toReal := ENNReal.toReal_nonneg
    have hnf : 0 ≤ Nf.toReal := ENNReal.toReal_nonneg
    have hmax2 : 2 ≤ max 2 K := le_max_left _ _
    have hmaxK : K ≤ max 2 K := le_max_right _ _
    have hT : Nw.toReal + Nd.toReal + Real.sqrt ν * gr ≤ C₁ * A * Nf.toReal := by
      have := hbd
      rw [hA]
      linarith
    have key : Nw.toReal + (Nd.toReal + Nw.toReal) + Real.sqrt ν * (K * gr) ≤
        (max 2 K * C₁ * A + 1) * Nf.toReal := by
      have e1 : Nw.toReal + (Nd.toReal + Nw.toReal) + Real.sqrt ν * (K * gr) ≤
          max 2 K * (Nw.toReal + Nd.toReal + Real.sqrt ν * gr) := by
        have h1 : Real.sqrt ν * (K * gr) ≤ max 2 K * (Real.sqrt ν * gr) := by
          have : K * (Real.sqrt ν * gr) ≤ max 2 K * (Real.sqrt ν * gr) :=
            mul_le_mul_of_nonneg_right hmaxK (mul_nonneg hsq hgr0)
          nlinarith
        nlinarith [mul_le_mul_of_nonneg_right hmax2 hnw, mul_le_mul_of_nonneg_right
          (show (1 : ℝ) ≤ max 2 K by linarith) hnd]
      have e2 := mul_le_mul_of_nonneg_left hT hRK.le
      nlinarith
    have e : Nw + (Nd + Nw) + ENNReal.ofReal (Real.sqrt ν) * (ENNReal.ofReal K * G) =
        ENNReal.ofReal (Nw.toReal + (Nd.toReal + Nw.toReal) + Real.sqrt ν * (K * gr)) := by
      rw [ENNReal.ofReal_add (add_nonneg hnw (add_nonneg hnd hnw))
        (mul_nonneg hsq (mul_nonneg hK.le hgr0)), ENNReal.ofReal_add hnw (add_nonneg hnd hnw),
        ENNReal.ofReal_add hnd hnw, ENNReal.ofReal_mul hsq, ENNReal.ofReal_mul hK.le,
        ← hNwr, ← hNdr, ← hGr]
    have hC0 : 0 ≤ max 2 K * C₁ * A + 1 :=
      add_nonneg (mul_nonneg (mul_nonneg hRK.le hC₁0) hA0) zero_le_one
    rw [e]
    calc _ ≤ ENNReal.ofReal ((max 2 K * C₁ * A + 1) * Nf.toReal) := ENNReal.ofReal_le_ofReal key
      _ = _ := by rw [ENNReal.ofReal_mul hC0, ← hNfr]
  have hfin : κ * (hNorm c r b' + hNorm c r Sb +
        ENNReal.ofReal (Real.sqrt ν) * (hNorm c r (sqrtS Qb) + hNorm c r (sqrtS Eb))) ≤
      κ * (ENNReal.ofReal (max 2 K * C₁ * A + 1) * hNorm c r F) := by
    refine step1.trans (hreal.trans (le_of_eq ?_))
    rw [hNF, mul_left_comm]
  have hbd_A := (ENNReal.mul_le_mul_iff_right hκ0 hκt).1 hfin
  refine hbd_A.trans ?_
  gcongr
  have hinv_le : (μ.re + (3 / r - 1) / 2)⁻¹ ≤ Γ := by
    have := inv_anti₀ (inv_pos.mpr hΓ0) hgap
    rwa [inv_inv] at this
  have hdiv_le : (1 + ‖μ‖) / (μ.re + (3 / r - 1) / 2) ≤ 2 * Γ ^ 2 := by
    rw [div_eq_mul_inv]
    calc (1 + ‖μ‖) * (μ.re + (3 / r - 1) / 2)⁻¹
        ≤ (2 * Γ) * Γ := mul_le_mul (by linarith) hinv_le (inv_nonneg.mpr hμ.le) (by linarith)
      _ = 2 * Γ ^ 2 := by ring
  have h1Γ2 : 1 ≤ Γ ^ 2 := by nlinarith
  have hA_le : A ≤ 3 * Γ ^ 2 := by
    rw [hA]
    linarith
  have hKC0 : 0 ≤ max 2 K * C₁ := mul_nonneg hRK.le hC₁0
  nlinarith [mul_le_mul_of_nonneg_left hA_le hKC0]

end UnforcedLeray.Short.IIb

end
