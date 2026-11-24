import UnforcedLeray.Short.PartIIIb.NearInst.Body.Forced

/-!
# The body column comparison (source 4119-4124): proof of `BodyColumnComparison`

`M_U R_ε f - M_0 R_0 f = (M_U - M_0) R_ε f + M_0 (R_ε - R_0) f`; the coefficient part
(`BodyCoeffColumn`, `‖R_ε f‖ ≤ 4‖f‖`) and the geometric part (`BodyGeomColumn` at `D = d₋`) are each
`P_ν e^{-c'/ν}` with `c' = min{a d₋/2, b d₋/2, (1/14 - K(a+b)) d₋, 3d₋/22 - m₀/2}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Body

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Cons.C03.Concrete UnforcedLeray.B0223
open UnforcedLeray.B0220 (HSpace measureH Profile)

/-! Copies of `Delta.regime_facts`, `Delta.rhoB_E_le` (`Delta/Assembly.lean`, source 4047-4049). -/

theorem regime_facts' {p : Params} {d dm dp : ℝ} (h : UnforcedLeray.Short.IIb.BgRegime p d dm dp) :
    p.ε < 1 ∧ Real.log p.ε = -d / p.ν := by
  have hd : 0 < d := lt_of_lt_of_le h.dm_pos h.dm_le
  have hν := p.ν_pos
  refine ⟨?_, ?_⟩
  · rw [h.eps_eq, Real.exp_lt_one_iff]
    exact div_neg_of_neg_of_pos (by linarith) hν
  · rw [h.eps_eq, Real.log_exp]

/-- `ρ_b e^{η/ν}` and `√ρ_b e^{η/ν}` are at most `(C₀+1)ν^{-k₀} ε^{3/22}e^{(η+m₀/2)/ν}`
(`ρ_b = C₀ν^{-k₀}e^{m₀/ν}ε^{3/11}`, `m₀ ≤ 3d/11`; source 4047-4049). -/
theorem rhoB_E_le' {p : Params} {d dm dp : ℝ} (h : UnforcedLeray.Short.IIb.BgRegime p d dm dp)
    {m0 C0 η : ℝ} (k0 : ℕ) (hm0 : m0 ≤ 3 * d / 11) (hC0 : 0 < C0) (hX : 1 ≤ p.ν⁻¹) :
    UnforcedLeray.Short.IIb.rhoB p m0 C0 k0 * Real.exp (η / p.ν) ≤
        (C0 + 1) * p.ν⁻¹ ^ k0 * (p.ε ^ (3 / 22 : ℝ) * Real.exp ((η + m0 / 2) / p.ν)) ∧
      Real.sqrt (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) * Real.exp (η / p.ν) ≤
        (C0 + 1) * p.ν⁻¹ ^ k0 * (p.ε ^ (3 / 22 : ℝ) * Real.exp ((η + m0 / 2) / p.ν)) := by
  have hν := p.ν_pos
  have hε := p.ε_pos
  obtain ⟨_, hlog⟩ := regime_facts' h
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = p.ε ^ (3 / 22 : ℝ) * Real.exp (m0 / (2 * p.ν)) := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; exact mul_pos (Real.rpow_pos_of_pos hε _) (Real.exp_pos _)
  have hu1 : u ≤ 1 := by
    rw [hu, Real.rpow_def_of_pos hε, hlog, ← Real.exp_add, Real.exp_le_one_iff]
    have e1 : -d / p.ν * (3 / 22) + m0 / (2 * p.ν) = (m0 / 2 - 3 * d / 22) * p.ν⁻¹ := by ring
    rw [e1]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (inv_nonneg.2 hν.le)
  have hY : 1 ≤ p.ν⁻¹ ^ k0 := one_le_pow₀ hX
  have hX0 : 0 ≤ p.ν⁻¹ ^ k0 := by linarith
  have hCX : 0 ≤ C0 * p.ν⁻¹ ^ k0 := mul_nonneg hC0.le hX0
  have hu2 : u ^ 2 = Real.exp (m0 / p.ν) * p.ε ^ (3 / 11 : ℝ) := by
    have e1 : (p.ε ^ (3 / 22 : ℝ)) ^ 2 = p.ε ^ (3 / 11 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]
      norm_num
    have e2 : Real.exp (m0 / (2 * p.ν)) ^ 2 = Real.exp (m0 / p.ν) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    rw [hu, mul_pow, e1, e2]
    ring
  have hρ : UnforcedLeray.Short.IIb.rhoB p m0 C0 k0 = C0 * p.ν⁻¹ ^ k0 * u ^ 2 := by
    unfold UnforcedLeray.Short.IIb.rhoB
    rw [hu2, ← inv_pow]
    ring
  have hT5 : p.ε ^ (3 / 22 : ℝ) * Real.exp ((η + m0 / 2) / p.ν) = u * Real.exp (η / p.ν) := by
    rw [hu, show (η + m0 / 2) / p.ν = m0 / (2 * p.ν) + η / p.ν by ring, Real.exp_add]
    ring
  have hE0 : 0 < Real.exp (η / p.ν) := Real.exp_pos _
  have huE : 0 ≤ u * Real.exp (η / p.ν) := (mul_pos hu0 hE0).le
  have hw1 : 1 ≤ (C0 + 1) * p.ν⁻¹ ^ k0 := by nlinarith
  have hCw : C0 * p.ν⁻¹ ^ k0 ≤ (C0 + 1) * p.ν⁻¹ ^ k0 := by nlinarith
  rw [hT5, hρ]
  refine ⟨?_, ?_⟩
  · have h1 : C0 * p.ν⁻¹ ^ k0 * u ^ 2 * Real.exp (η / p.ν) =
        (C0 * p.ν⁻¹ ^ k0 * u) * (u * Real.exp (η / p.ν)) := by ring
    rw [h1]
    refine mul_le_mul_of_nonneg_right ?_ huE
    calc C0 * p.ν⁻¹ ^ k0 * u ≤ C0 * p.ν⁻¹ ^ k0 * 1 := mul_le_mul_of_nonneg_left hu1 hCX
      _ ≤ (C0 + 1) * p.ν⁻¹ ^ k0 := by rw [mul_one]; exact hCw
  · have hsq : Real.sqrt (C0 * p.ν⁻¹ ^ k0 * u ^ 2) = Real.sqrt (C0 * p.ν⁻¹ ^ k0) * u := by
      rw [Real.sqrt_mul hCX, Real.sqrt_sq hu0.le]
    rw [hsq]
    have hs : Real.sqrt (C0 * p.ν⁻¹ ^ k0) ≤ (C0 + 1) * p.ν⁻¹ ^ k0 := by
      rw [Real.sqrt_le_left (by linarith)]
      have hww : (C0 + 1) * p.ν⁻¹ ^ k0 ≤ ((C0 + 1) * p.ν⁻¹ ^ k0) ^ 2 := by nlinarith
      linarith
    calc Real.sqrt (C0 * p.ν⁻¹ ^ k0) * u * Real.exp (η / p.ν)
        = Real.sqrt (C0 * p.ν⁻¹ ^ k0) * (u * Real.exp (η / p.ν)) := by ring
      _ ≤ (C0 + 1) * p.ν⁻¹ ^ k0 * (u * Real.exp (η / p.ν)) :=
          mul_le_mul_of_nonneg_right hs huE

/-- `ε^x ≤ e^{-c'/ν}` when `x ≥ 0` and `c' ≤ x d₋`. -/
theorem eps_rpow_le_exp {p : Params} {d dm dp : ℝ}
    (h : UnforcedLeray.Short.IIb.BgRegime p d dm dp) {x c' : ℝ} (hx : 0 ≤ x)
    (hc : c' ≤ x * dm) : p.ε ^ x ≤ Real.exp (-c' / p.ν) := by
  have hν := p.ν_pos
  have hlog := (regime_facts' h).2
  rw [Real.rpow_def_of_pos p.ε_pos, hlog]
  apply Real.exp_le_exp.2
  have h1 : c' ≤ x * d := hc.trans (mul_le_mul_of_nonneg_left h.dm_le hx)
  rw [show -d / p.ν * x = -(x * d) / p.ν by ring]
  exact div_le_div_of_nonneg_right (neg_le_neg h1) hν.le

theorem bodyColumnComparison_of (hC : BodyCoeffColumn) (hGeo : BodyGeomColumn)
    (hN : BodyFormNorm) : BodyColumnComparison := by
  intro Kset hK hKsub mZ hmZ dm dp hdm
  obtain ⟨K, hK'⟩ := hGeo Kset hK hKsub mZ hmZ dm dp hdm
  refine ⟨K, ?_⟩
  intro a b m0 ha hb hb1 hKab hm0 hm0dm C0 k0 hC0 Sig lam q hSig hq
  obtain ⟨C1, k1, ν1, hν1, h1⟩ := hC dm dp hdm mZ hmZ m0 C0 k0 hC0 Sig lam q hSig hq
  obtain ⟨C2, k2, ν2, hν2, h2⟩ := hK' a b dm ha hb hb1 hdm
  set e : ℝ := 1 / 14 - (K : ℝ) * (a + b) with he
  have he0 : 0 < e := by rw [he]; linarith
  set c' : ℝ := min (min (a * dm / 2) (b * dm / 2)) (min (e * dm) (3 * dm / 22 - m0 / 2)) with hc'
  have hc'pos : 0 < c' := by
    refine lt_min (lt_min (by positivity) (by positivity)) (lt_min (by positivity) ?_)
    linarith
  have hc1 : c' ≤ a * dm / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hc2 : c' ≤ b * dm / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hc3 : c' ≤ e * dm := (min_le_right _ _).trans (min_le_left _ _)
  have hc4 : c' ≤ 3 * dm / 22 - m0 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨c', 12 * |C1| * (C0 + 1) + 5 * |C2|, k1 + k2 + k0, min (min ν1 ν2) 1, hc'pos,
    lt_min (lt_min hν1 hν2) one_pos, ?_⟩
  intro p d hBG hpν hage hmode S_in V rb hsplit γ hγ μ hμ M0 MU hM0 hMU Reps R0 hReps hR0 f
  have hν := p.ν_pos
  have hν1' : p.ν ≤ ν1 := hpν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν2' : p.ν ≤ ν2 := hpν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν3 : p.ν ≤ 1 := hpν.trans (min_le_right _ _)
  have hX : 1 ≤ p.ν⁻¹ := by rw [le_inv_comm₀ one_pos hν, inv_one]; exact hν3
  have hXpos : ∀ j : ℕ, 0 < p.ν⁻¹ ^ j := fun j => pow_pos (inv_pos.2 hν) j
  have hρ : 0 < UnforcedLeray.Short.IIb.rhoB p m0 C0 k0 := by
    unfold UnforcedLeray.Short.IIb.rhoB
    have h1 := p.ν_pos
    have h2 := p.ε_pos
    positivity
  set E := Real.exp (-c' / p.ν) with hE
  have hE0 : 0 < E := Real.exp_pos _
  -- the five geometric rates and the three coefficient rates
  have rA : p.ε ^ (a / 2) ≤ E := eps_rpow_le_exp hBG (by positivity) (by linarith)
  have rB : p.ε ^ (b / 2) ≤ E := eps_rpow_le_exp hBG (by positivity) (by linarith)
  have rC : p.ε ≤ E := by
    have := eps_rpow_le_exp hBG (x := 1) (c' := c') zero_le_one (by
      have : c' ≤ dm := by linarith [hc4, hm0, hdm]
      linarith)
    simpa using this
  have rD : Real.exp (-dm / p.ν) ≤ E := by
    apply Real.exp_le_exp.2
    exact div_le_div_of_nonneg_right (neg_le_neg (by linarith)) hν.le
  have rE : p.ε ^ e ≤ E := eps_rpow_le_exp hBG he0.le hc3
  have hm0d : m0 ≤ 3 * d / 11 := by linarith [hBG.dm_le]
  obtain ⟨hρE, hsρE⟩ := rhoB_E_le' hBG (m0 := m0) (C0 := C0) (η := 0) k0 hm0d hC0 hX
  have hT : p.ε ^ (3 / 22 : ℝ) * Real.exp ((0 + m0 / 2) / p.ν) ≤ E := by
    have hlog := (regime_facts' hBG).2
    rw [Real.rpow_def_of_pos p.ε_pos, hlog, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have : -d / p.ν * (3 / 22) + (0 + m0 / 2) / p.ν = -(3 * d / 22 - m0 / 2) / p.ν := by ring
    rw [this]
    apply div_le_div_of_nonneg_right _ hν.le
    have : 3 * dm / 22 ≤ 3 * d / 22 := by linarith [hBG.dm_le]
    linarith
  simp only [zero_div, Real.exp_zero, mul_one] at hρE hsρE
  have hw : (C0 + 1) * p.ν⁻¹ ^ k0 * (p.ε ^ (3 / 22 : ℝ) * Real.exp ((0 + m0 / 2) / p.ν)) ≤
      (C0 + 1) * p.ν⁻¹ ^ k0 * E :=
    mul_le_mul_of_nonneg_left hT (mul_nonneg (by linarith) (hXpos _).le)
  have hρ1 : (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) ≤ (C0 + 1) * p.ν⁻¹ ^ k0 * E := hρE.trans hw
  have hρ2 : Real.sqrt (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) ≤ (C0 + 1) * p.ν⁻¹ ^ k0 * E := hsρE.trans hw
  have hw1 : 1 ≤ (C0 + 1) * p.ν⁻¹ ^ k0 := by
    have := one_le_pow₀ (n := k0) hX
    nlinarith
  have hcoef : p.ε + (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) + Real.sqrt (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) ≤ 3 * ((C0 + 1) * p.ν⁻¹ ^ k0) * E := by
    have : E ≤ (C0 + 1) * p.ν⁻¹ ^ k0 * E := le_mul_of_one_le_left hE0.le hw1
    linarith
  have hgeo : p.ε ^ (a / 2) + p.ε ^ (b / 2) + p.ε + Real.exp (-dm / p.ν) + p.ε ^ e ≤ 5 * E := by
    linarith
  -- the body form bound
  have hμI := hKsub hμ
  have hμpos : 0 < (μ : ℂ).re + 1 / 4 := by
    rw [Complex.ofReal_re]; linarith [hμI.1]
  have h4 : (μ + 1 / 4)⁻¹ ≤ 4 := by
    calc (μ + 1 / 4)⁻¹ ≤ (1 / 4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) (by linarith [hμI.1])
      _ = 4 := by norm_num
  have hRn := norm_RepsVec_le p.ν_pos p.ε_pos p.c_pos (P := p.period) rfl hμpos
  rw [Complex.ofReal_re] at hRn
  have hPe : ‖UnforcedLeray.Short.PartIIa.PepsC p.ε p.c‖ ≤ 1 := by
    unfold UnforcedLeray.Short.PartIIa.PepsC
    exact Submodule.starProjection_norm_le _
  have hT4 : ‖UnforcedLeray.Short.PartIIa.Teps (P := p.period) p.ν_pos p.ε_pos p.c_pos rfl
      (μ : ℂ)‖ ≤ 4 := by
    unfold UnforcedLeray.Short.PartIIa.Teps
    refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
    have := mul_le_mul (hRn.trans h4) hPe (norm_nonneg _) (by norm_num)
    linarith
  have hRf : ‖Reps f‖ ≤ 4 * ‖f‖ :=
    le_trans (hN p.c p.c_pos Reps _ hReps f) (mul_le_mul_of_nonneg_right hT4 (norm_nonneg _))
  -- the two parts
  have hA := h1 p d hBG hν1' hage hmode S_in V rb hsplit γ hγ M0 MU hM0 hMU (Reps f)
  have hB := h2 p d hBG hν2' (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) γ hρ hγ μ hμ M0 hM0 Reps R0 hReps hR0 f
  have hsplitEq : MU (Reps f) - M0 (R0 f) = (MU - M0) (Reps f) + M0 ((Reps - R0) f) := by
    simp [map_sub]
  rw [hsplitEq, map_add]
  refine (norm_add_le _ _).trans ?_
  have hX1 : 0 ≤ p.ν⁻¹ ^ k1 := (hXpos _).le
  have hX2 : 0 ≤ p.ν⁻¹ ^ k2 := (hXpos _).le
  have hX0 : 0 ≤ p.ν⁻¹ ^ k0 := (hXpos _).le
  have hCA : C1 * p.ν⁻¹ ^ k1 ≤ |C1| * p.ν⁻¹ ^ k1 := mul_le_mul_of_nonneg_right (le_abs_self _) hX1
  have hCB : C2 * p.ν⁻¹ ^ k2 ≤ |C2| * p.ν⁻¹ ^ k2 := mul_le_mul_of_nonneg_right (le_abs_self _) hX2
  have hAA : ‖(gainEquiv p.c mZ (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) γ p.ν_pos).symm ((MU - M0) (Reps f))‖ ≤
      |C1| * p.ν⁻¹ ^ k1 * (3 * ((C0 + 1) * p.ν⁻¹ ^ k0) * E) * (4 * ‖f‖) := by
    refine hA.trans ?_
    have hc0 : 0 ≤ |C1| * p.ν⁻¹ ^ k1 := mul_nonneg (abs_nonneg _) hX1
    have hs0 : 0 ≤ p.ε + (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) + Real.sqrt (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) := by
      have := p.ε_pos
      positivity
    exact mul_le_mul (mul_le_mul hCA hcoef hs0 hc0) hRf (norm_nonneg _)
      (mul_nonneg hc0 (by positivity))
  have hBB : ‖(gainEquiv p.c mZ (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) γ p.ν_pos).symm (M0 ((Reps - R0) f))‖ ≤
      |C2| * p.ν⁻¹ ^ k2 * (5 * E) * ‖f‖ := by
    refine hB.trans ?_
    have hc0 : 0 ≤ |C2| * p.ν⁻¹ ^ k2 := mul_nonneg (abs_nonneg _) hX2
    have hs0 : 0 ≤ p.ε ^ (a / 2) + p.ε ^ (b / 2) + p.ε + Real.exp (-dm / p.ν) + p.ε ^ e := by
      have := p.ε_pos
      positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul hCB hgeo hs0 hc0) (norm_nonneg _)
  have hP1 : p.ν⁻¹ ^ k1 * p.ν⁻¹ ^ k0 ≤ p.ν⁻¹ ^ (k1 + k2 + k0) := by
    rw [← pow_add]; exact pow_le_pow_right₀ hX (by omega)
  have hP2 : p.ν⁻¹ ^ k2 ≤ p.ν⁻¹ ^ (k1 + k2 + k0) :=
    pow_le_pow_right₀ hX (by omega)
  have hfn := norm_nonneg f
  refine le_trans (add_le_add hAA hBB) ?_
  have h12 : 0 ≤ 12 * |C1| * (C0 + 1) := by positivity
  have h5 : 0 ≤ 5 * |C2| := by positivity
  have s1 : 12 * |C1| * (C0 + 1) * (p.ν⁻¹ ^ k1 * p.ν⁻¹ ^ k0) ≤
      12 * |C1| * (C0 + 1) * p.ν⁻¹ ^ (k1 + k2 + k0) := mul_le_mul_of_nonneg_left hP1 h12
  have s2 : 5 * |C2| * p.ν⁻¹ ^ k2 ≤ 5 * |C2| * p.ν⁻¹ ^ (k1 + k2 + k0) :=
    mul_le_mul_of_nonneg_left hP2 h5
  have t1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right s1 hE0.le) hfn
  have t2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right s2 hE0.le) hfn
  have eq1 : |C1| * p.ν⁻¹ ^ k1 * (3 * ((C0 + 1) * p.ν⁻¹ ^ k0) * E) * (4 * ‖f‖) +
        |C2| * p.ν⁻¹ ^ k2 * (5 * E) * ‖f‖ =
      12 * |C1| * (C0 + 1) * (p.ν⁻¹ ^ k1 * p.ν⁻¹ ^ k0) * E * ‖f‖ +
        5 * |C2| * p.ν⁻¹ ^ k2 * E * ‖f‖ := by ring
  have eq2 : (12 * |C1| * (C0 + 1) + 5 * |C2|) * p.ν⁻¹ ^ (k1 + k2 + k0) * E * ‖f‖ =
      12 * |C1| * (C0 + 1) * p.ν⁻¹ ^ (k1 + k2 + k0) * E * ‖f‖ +
        5 * |C2| * p.ν⁻¹ ^ (k1 + k2 + k0) * E * ‖f‖ := by ring
  rw [eq1, eq2]
  exact add_le_add t1 t2

end UnforcedLeray.Short.PartIIIb.NearInst.Body
