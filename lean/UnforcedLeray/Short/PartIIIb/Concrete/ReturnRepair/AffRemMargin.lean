import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Estimates
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.EpsForm
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Seq

/-!
# The actual affine remainder margin (source 5527-5531, 5563-5567, 5624-5625)

`AffRemMargin` (the gain band `e^{-(γ/15 - 3m₀/2)/ν}`) follows from `AffineRemainder`
(`R⁻¹‖𝔯_{A_T}‖ ≤ P_ν ε³N(ε + ρ + δ_base)`) and `ThinMoment` (`N ≤ P_ν e^{γ/ν}‖T‖`):
`ε³e^{γ/ν}` is a power of `ν` (`NearInst.retEps_cube_mul`), `ε = C ν^r e^{-γ/(3ν)}`
(`retEps_eq_form`), `ρ = ε^{3/11}e^{m₀/ν}` and `δ_base = e^{C_Σ/ν - b_Σν^{-4}}` are at most
`P_ν e^{-(γ/15 - 3m₀/2)/ν}` for small `ν`.
-/

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Powers of `ν ∈ (0,1]` are dominated by powers of `ν⁻¹`. -/
theorem rpow_le_inv_pow_aux (p : ℝ) :
    ∃ j : ℕ, ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ν ^ p ≤ ν⁻¹ ^ j := by
  refine ⟨⌈-p⌉₊, fun ν hν0 hν1 => ?_⟩
  have h1 : ν ^ p ≤ ν ^ (-((⌈-p⌉₊ : ℕ) : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hν0 hν1 (by linarith [Nat.le_ceil (-p)])
  rw [Real.rpow_neg hν0.le, Real.rpow_natCast, ← inv_pow] at h1
  exact h1

/-- `e^{-(γ/3)/ν} ≤ e^{-(γ/15 - 3m₀/2)/ν}`. -/
theorem exp_le_gain (γ m0 ν : ℝ) (hν : 0 < ν) (hγ : 0 < γ) (hm0 : 0 < m0) :
    Real.exp (-(γ / 3) / ν) ≤ Real.exp (-(γ / 15 - 3 * m0 / 2) / ν) := by
  apply Real.exp_le_exp.2
  simp only [neg_div]
  have h : (γ / 15 - 3 * m0 / 2) / ν ≤ (γ / 3) / ν :=
    div_le_div_of_nonneg_right (by linarith) hν.le
  linarith

/-- `e^{-(γ/15)/ν} ≤ e^{-(γ/15 - 3m₀/2)/ν}`. -/
theorem exp_gain_mono (γ m0 ν : ℝ) (hν : 0 < ν) (hm0 : 0 < m0) :
    Real.exp (-(γ / 15) / ν) ≤ Real.exp (-(γ / 15 - 3 * m0 / 2) / ν) := by
  apply Real.exp_le_exp.2
  simp only [neg_div]
  have h : (γ / 15 - 3 * m0 / 2) / ν ≤ (γ / 15) / ν :=
    div_le_div_of_nonneg_right (by linarith) hν.le
  linarith

/-- The `ρ`-bound: `(c ν^r e^{-γ/(3ν)})^{3/11} e^{m₀/ν} ≤ c^{3/11} ν⁻¹^j e^{-(γ/15 - 3m₀/2)/ν}`
when `ν^{r·3/11} ≤ ν⁻¹^j`. -/
theorem rho_le_gain (γ m0 c r ν : ℝ) (hν : 0 < ν) (hc : 0 < c) (hγ : 0 < γ) (hm0 : 0 < m0)
    (j : ℕ) (hj : ν ^ (r * (3 / 11 : ℝ)) ≤ ν⁻¹ ^ j) :
    (c * ν ^ r * Real.exp (-(γ / 3) / ν)) ^ (3 / 11 : ℝ) * Real.exp (m0 / ν) ≤
      c ^ (3 / 11 : ℝ) * ν⁻¹ ^ j * Real.exp (-(γ / 15 - 3 * m0 / 2) / ν) := by
  have hνr : 0 ≤ ν ^ r := Real.rpow_nonneg hν.le _
  have hE : 0 ≤ Real.exp (-(γ / 3) / ν) := (Real.exp_pos _).le
  rw [Real.mul_rpow (mul_nonneg hc.le hνr) hE, Real.mul_rpow hc.le hνr, ← Real.rpow_mul hν.le,
    ← Real.exp_mul]
  have hexp : Real.exp (-(γ / 3) / ν * (3 / 11 : ℝ)) * Real.exp (m0 / ν) ≤
      Real.exp (-(γ / 15 - 3 * m0 / 2) / ν) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have key : -(γ / 3) / ν * (3 / 11 : ℝ) + m0 / ν = -((γ / 11 - m0) / ν) := by ring
    rw [key, neg_div]
    have h : (γ / 15 - 3 * m0 / 2) / ν ≤ (γ / 11 - m0) / ν :=
      div_le_div_of_nonneg_right (by linarith) hν.le
    linarith
  have hX : 0 ≤ c ^ (3 / 11 : ℝ) := Real.rpow_nonneg hc.le _
  calc c ^ (3 / 11 : ℝ) * ν ^ (r * (3 / 11 : ℝ)) * Real.exp (-(γ / 3) / ν * (3 / 11 : ℝ)) *
        Real.exp (m0 / ν)
      = (c ^ (3 / 11 : ℝ) * ν ^ (r * (3 / 11 : ℝ))) *
          (Real.exp (-(γ / 3) / ν * (3 / 11 : ℝ)) * Real.exp (m0 / ν)) := by ring
    _ ≤ (c ^ (3 / 11 : ℝ) * ν⁻¹ ^ j) * Real.exp (-(γ / 15 - 3 * m0 / 2) / ν) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hj hX) hexp (by positivity)
          (mul_nonneg hX (pow_nonneg (inv_nonneg.2 hν.le) _))

/-- Passing from `ENNReal` bounds to a real bound. -/
theorem ennreal_chain {X a b : ℝ} {M : ENNReal} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ENNReal.ofReal X ≤ ENNReal.ofReal a * M) (hM : M ≤ ENNReal.ofReal b) : X ≤ a * b := by
  have h1 : ENNReal.ofReal X ≤ ENNReal.ofReal a * ENNReal.ofReal b :=
    le_trans hA (mul_le_mul_of_nonneg_left hM (zero_le))
  rw [← ENNReal.ofReal_mul ha] at h1
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg ha hb)).1 h1

/-- The exponential comparison behind `δ_base`: if `(C_Σ + γ/15)ν³ ≤ b_Σ` then
`C_Σ/ν - b_Σ(ν⁻²)² ≤ -(γ/15)/ν`. -/
theorem delta_exp_le (Csig bsig γ ν : ℝ) (hν : 0 < ν) (h : (Csig + γ / 15) * ν ^ 3 ≤ bsig) :
    Csig / ν - bsig * ((ν ^ 2)⁻¹) ^ 2 ≤ -(γ / 15) / ν := by
  have e : Csig / ν - bsig * ((ν ^ 2)⁻¹) ^ 2 - (-(γ / 15) / ν) =
      ((Csig + γ / 15) * ν ^ 3 - bsig) / ν ^ 4 := by
    field_simp
    ring
  have h4 : ((Csig + γ / 15) * ν ^ 3 - bsig) / ν ^ 4 ≤ 0 :=
    div_nonpos_iff.mpr (Or.inr ⟨by linarith, by positivity⟩)
  linarith

/-- `δ_base ≤ e^{-(γ/15 - 3m₀/2)/ν}` once `(C_Σ + γ/15)ν³ ≤ b_Σ`. -/
theorem deltaBase_gain (Csig bsig γ m0 ν : ℝ) (hν : 0 < ν) (hm0 : 0 < m0)
    (h : (Csig + γ / 15) * ν ^ 3 ≤ bsig) :
    deltaBase Csig bsig ν ≤ Real.exp (-(γ / 15 - 3 * m0 / 2) / ν) := by
  refine le_trans ?_ (exp_gain_mono γ m0 ν hν hm0)
  apply Real.exp_le_exp.2
  unfold cOf
  exact delta_exp_le Csig bsig γ ν hν h

/-- The constant of `AffRemMargin`: `|C₁||C₂|(c + c^{3/11} + 1)/Q` with `c = Q^{-1/3}`. -/
def marginConst (C1 C2 Q : ℝ) : ℝ :=
  |C1| * |C2| * (Q ^ (-(1 / 3 : ℝ)) + (Q ^ (-(1 / 3 : ℝ))) ^ (3 / 11 : ℝ) + 1) / Q

/-- The real core of the estimate at one level, with the level data as real variables. -/
theorem core_margin (γ m0 C1 C2 c p Q δ ν ε t X : ℝ) (M : ENNReal)
    (k1 k2 j0 j1 j2 : ℕ)
    (hγ : 0 < γ) (hm0 : 0 < m0) (hc : 0 < c) (hQ : 0 < Q) (hν0 : 0 < ν) (hν1 : ν ≤ 1)
    (hεpos : 0 < ε) (ht : 0 ≤ t) (hδ0 : 0 ≤ δ)
    (hδle : δ ≤ Real.exp (-(γ / 15 - 3 * m0 / 2) / ν))
    (hj0 : ν ^ p ≤ ν⁻¹ ^ j0) (hj1 : ν ^ (p / 3) ≤ ν⁻¹ ^ j1)
    (hj2 : ν ^ (p / 3 * (3 / 11 : ℝ)) ≤ ν⁻¹ ^ j2)
    (hεform : ε = c * ν ^ (p / 3) * Real.exp (-(γ / 3) / ν))
    (hcube : ε ^ 3 * Real.exp (γ / ν) = ν ^ p / Q)
    (hAT : ENNReal.ofReal X ≤ ENNReal.ofReal (C1 * ν⁻¹ ^ k1 * ε ^ 3 *
      (ε + ε ^ (3 / 11 : ℝ) * Real.exp (m0 / ν) + δ)) * M)
    (hM : M ≤ ENNReal.ofReal (C2 * ν⁻¹ ^ k2 * Real.exp (γ / ν) * t)) :
    X ≤ |C1| * |C2| * (c + c ^ (3 / 11 : ℝ) + 1) / Q * ν⁻¹ ^ (k1 + k2 + j0 + (j0 + j1 + j2)) *
      Real.exp (-(γ / 15 - 3 * m0 / 2) / ν) * t := by
  have hNi : 0 ≤ ν⁻¹ := inv_nonneg.2 hν0.le
  have hN1 : 1 ≤ ν⁻¹ := (one_le_inv₀ hν0).2 hν1
  have hE0 : 0 ≤ Real.exp (-(γ / 15 - 3 * m0 / 2) / ν) := (Real.exp_pos _).le
  have hε_le : ε ≤ c * ν⁻¹ ^ j1 * Real.exp (-(γ / 15 - 3 * m0 / 2) / ν) := by
    rw [hεform]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hj1 hc.le)
      (exp_le_gain γ m0 ν hν0 hγ hm0) (Real.exp_pos _).le
      (mul_nonneg hc.le (pow_nonneg hNi _))
  have hρ_le : ε ^ (3 / 11 : ℝ) * Real.exp (m0 / ν) ≤
      c ^ (3 / 11 : ℝ) * ν⁻¹ ^ j2 * Real.exp (-(γ / 15 - 3 * m0 / 2) / ν) := by
    rw [hεform]
    exact rho_le_gain γ m0 c (p / 3) ν hν0 hc hγ hm0 j2 hj2
  have hρ0 : 0 ≤ ε ^ (3 / 11 : ℝ) * Real.exp (m0 / ν) :=
    mul_nonneg (Real.rpow_nonneg hεpos.le _) (Real.exp_pos _).le
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = ε + ε ^ (3 / 11 : ℝ) * Real.exp (m0 / ν) + δ := ⟨_, rfl⟩
  rw [← hSdef] at hAT
  have hS0 : 0 ≤ S := by rw [hSdef]; linarith
  have hS_le : S ≤ (c * ν⁻¹ ^ j1 + c ^ (3 / 11 : ℝ) * ν⁻¹ ^ j2 + 1) *
      Real.exp (-(γ / 15 - 3 * m0 / 2) / ν) := by
    rw [hSdef]
    linarith [hε_le, hρ_le, hδle]
  have hNJ1 : ν⁻¹ ^ j1 ≤ ν⁻¹ ^ (j0 + j1 + j2) := pow_le_pow_right₀ hN1 (by omega)
  have hNJ2 : ν⁻¹ ^ j2 ≤ ν⁻¹ ^ (j0 + j1 + j2) := pow_le_pow_right₀ hN1 (by omega)
  have hNJ0 : 1 ≤ ν⁻¹ ^ (j0 + j1 + j2) := one_le_pow₀ hN1
  have hsum : c * ν⁻¹ ^ j1 + c ^ (3 / 11 : ℝ) * ν⁻¹ ^ j2 + 1 ≤
      (c + c ^ (3 / 11 : ℝ) + 1) * ν⁻¹ ^ (j0 + j1 + j2) := by
    linarith [mul_le_mul_of_nonneg_left hNJ1 hc.le,
      mul_le_mul_of_nonneg_left hNJ2 (Real.rpow_nonneg hc.le (3 / 11 : ℝ))]
  have hS2 : S ≤ (c + c ^ (3 / 11 : ℝ) + 1) * ν⁻¹ ^ (j0 + j1 + j2) *
      Real.exp (-(γ / 15 - 3 * m0 / 2) / ν) :=
    le_trans hS_le (mul_le_mul_of_nonneg_right hsum hE0)
  have hcube_le : ε ^ 3 * Real.exp (γ / ν) ≤ ν⁻¹ ^ j0 / Q := by
    rw [hcube]
    exact div_le_div_of_nonneg_right hj0 hQ.le
  have hQ0 : 0 ≤ ν⁻¹ ^ j0 / Q := div_nonneg (pow_nonneg hNi _) hQ.le
  have hX : 0 ≤ |C1| * |C2| * ν⁻¹ ^ k1 * ν⁻¹ ^ k2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (pow_nonneg hNi _)) (pow_nonneg hNi _)
  have habs : C1 * ν⁻¹ ^ k1 * ε ^ 3 * S ≤ |C1| * ν⁻¹ ^ k1 * ε ^ 3 * S :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (le_abs_self C1) (pow_nonneg hNi _)) (pow_nonneg hεpos.le _)) hS0
  have hAT2 : ENNReal.ofReal X ≤ ENNReal.ofReal (|C1| * ν⁻¹ ^ k1 * ε ^ 3 * S) * M :=
    le_trans hAT (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal habs) (zero_le))
  have ha : 0 ≤ |C1| * ν⁻¹ ^ k1 * ε ^ 3 * S :=
    mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg hNi _))
      (pow_nonneg hεpos.le _)) hS0
  have hb : 0 ≤ |C2| * ν⁻¹ ^ k2 * Real.exp (γ / ν) * t :=
    mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg hNi _))
      (Real.exp_pos _).le) ht
  have hM' : M ≤ ENNReal.ofReal (|C2| * ν⁻¹ ^ k2 * Real.exp (γ / ν) * t) := by
    refine le_trans hM (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self C2) (pow_nonneg hNi _)) (Real.exp_pos _).le) ht
  have hchain := ennreal_chain ha hb hAT2 hM'
  have hprod : (|C1| * |C2| * ν⁻¹ ^ k1 * ν⁻¹ ^ k2) * (ε ^ 3 * Real.exp (γ / ν)) * S ≤
      (|C1| * |C2| * ν⁻¹ ^ k1 * ν⁻¹ ^ k2) * (ν⁻¹ ^ j0 / Q) *
        ((c + c ^ (3 / 11 : ℝ) + 1) * ν⁻¹ ^ (j0 + j1 + j2) *
          Real.exp (-(γ / 15 - 3 * m0 / 2) / ν)) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hcube_le hX) hS2 hS0 (mul_nonneg hX hQ0)
  calc X ≤ (|C1| * ν⁻¹ ^ k1 * ε ^ 3 * S) * (|C2| * ν⁻¹ ^ k2 * Real.exp (γ / ν) * t) := hchain
    _ = (|C1| * |C2| * ν⁻¹ ^ k1 * ν⁻¹ ^ k2) * (ε ^ 3 * Real.exp (γ / ν)) * S * t := by ring
    _ ≤ (|C1| * |C2| * ν⁻¹ ^ k1 * ν⁻¹ ^ k2) * (ν⁻¹ ^ j0 / Q) *
        ((c + c ^ (3 / 11 : ℝ) + 1) * ν⁻¹ ^ (j0 + j1 + j2) *
          Real.exp (-(γ / 15 - 3 * m0 / 2) / ν)) * t :=
        mul_le_mul_of_nonneg_right hprod ht
    _ = |C1| * |C2| * (c + c ^ (3 / 11 : ℝ) + 1) / Q * ν⁻¹ ^ (k1 + k2 + j0 + (j0 + j1 + j2)) *
        Real.exp (-(γ / 15 - 3 * m0 / 2) / ν) * t := by ring

theorem affRemMargin (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (h9 : D.AffineRemainder) (hm : D.ThinMoment) : D.AffRemMargin := by
  obtain ⟨C1, k1, Csig, bsig, hbs, hA⟩ := h9
  obtain ⟨C2, k2, hB⟩ := hm
  have hγ : 0 < gRate D.Pl := hst.gamma_pos
  have hm0 : 0 < D.K.m0 := hst.m0_pos
  have h2c : 0 < 2 * ‖D.Pl.signedCoeff D.σ₀‖ := mul_pos two_pos (norm_pos_iff.2 D.coeff_ne)
  obtain ⟨j0, hj0⟩ := rpow_le_inv_pow_aux (D.Pl.kappa.re - 5 - 2 * D.σ₀)
  obtain ⟨j1, hj1⟩ := rpow_le_inv_pow_aux ((D.Pl.kappa.re - 5 - 2 * D.σ₀) / 3)
  obtain ⟨j2, hj2⟩ := rpow_le_inv_pow_aux ((D.Pl.kappa.re - 5 - 2 * D.σ₀) / 3 * (3 / 11 : ℝ))
  have hc0 : 0 < (2 * ‖D.Pl.signedCoeff D.σ₀‖) ^ (-(1 / 3 : ℝ)) :=
    Real.rpow_pos_of_pos h2c _
  have hν1 : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n ≤ 1 :=
    ((retNu_tendsto D.σ₀ hst.omega_ne).eventually_lt_const one_pos).mono fun n h => h.le
  have hδ : ∀ᶠ n : ℕ in atTop, (Csig + gRate D.Pl / 15) * retNu D.Pl D.σ₀ n ^ 3 < bsig := by
    have ht : Tendsto (fun n : ℕ => (Csig + gRate D.Pl / 15) * retNu D.Pl D.σ₀ n ^ 3) atTop
        (nhds 0) := by
      have := ((retNu_tendsto D.σ₀ hst.omega_ne).pow 3).const_mul (Csig + gRate D.Pl / 15)
      simpa using this
    exact ht.eventually (gt_mem_nhds hbs)
  refine ⟨marginConst C1 C2 (2 * ‖D.Pl.signedCoeff D.σ₀‖),
    k1 + k2 + j0 + (j0 + j1 + j2), ?_⟩
  filter_upwards [hA, hB, hν1, hδ] with n hAn hBn hν1n hδn
  intro z hz
  unfold AffRemMarginAt
  intro T
  have hAz := hAn z hz
  unfold AffineRemainderAt at hAz
  have hAT := hAz T
  unfold ThinMomentAt at hBn
  have hBT := hBn T
  unfold rhoRep at hAT
  have hν0 : 0 < (D.level n).ν := (D.level n).ν_pos
  have hεpos : 0 < (D.level n).ε := (D.level n).ε_pos
  have hδle := deltaBase_gain Csig bsig (gRate D.Pl) D.K.m0 (D.level n).ν hν0 hm0 hδn.le
  have hδ0 : 0 ≤ deltaBase Csig bsig (D.level n).ν := (Real.exp_pos _).le
  unfold marginConst
  exact core_margin (gRate D.Pl) D.K.m0 C1 C2 ((2 * ‖D.Pl.signedCoeff D.σ₀‖) ^ (-(1 / 3 : ℝ)))
    (D.Pl.kappa.re - 5 - 2 * D.σ₀) (2 * ‖D.Pl.signedCoeff D.σ₀‖)
    (deltaBase Csig bsig (D.level n).ν) (D.level n).ν (D.level n).ε ‖T‖
    _ (oldN1 D.Pl D.K (D.level n) T) k1 k2 j0 j1 j2 hγ hm0 hc0 h2c hν0 hν1n
    hεpos (norm_nonneg _) hδ0 hδle (hj0 _ hν0 hν1n) (hj1 _ hν0 hν1n)
    (hj2 _ hν0 hν1n) (retEps_eq_form D.coeff_ne n) (NearInst.retEps_cube_mul D.coeff_ne n)
    hAT hBT

end UnforcedLeray.Short.PartIIIb.Concrete
