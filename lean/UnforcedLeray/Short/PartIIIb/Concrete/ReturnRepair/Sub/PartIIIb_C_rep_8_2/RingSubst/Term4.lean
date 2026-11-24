import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_6

/-!
# Term 4 of the four-term substitution (`PartIII-b:C/rep/8/2/6/4`)

Source `the November 2 reference manuscript` 5470-5477: `(DX+DXᵀ)∇p` equals
`(A_T+A_Tᵀ)∇_flat p_cyl` up to `P_ν ε⁴ s^{5/2} 𝔴₄ N` in chart-coefficient units.
With `E_j = ∂_jX - A_T e_j` the mean-jet error, `G = ∇p_lift`, `G₀ = s^{3/2} ∇_flat p_cyl`,
component `i` of the difference is
`Σ_j [(A_T+A_Tᵀ)_{ij}(G-G₀)_j + (E_j i + E_i j) G_j]`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-! ## Bounds with a common factor `N` -/

/-- `‖x‖ₑ ≤ ofReal a · N`. -/
def NBd4 (N : ℝ≥0∞) (x a : ℝ) : Prop := ‖x‖ₑ ≤ ENNReal.ofReal a * N

theorem nbd4_add {N : ℝ≥0∞} {x y a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : NBd4 N x a)
    (hy : NBd4 N y b) : NBd4 N (x + y) (a + b) := by
  unfold NBd4 at *
  calc ‖x + y‖ₑ ≤ ‖x‖ₑ + ‖y‖ₑ := enorm_add_le _ _
    _ ≤ ENNReal.ofReal a * N + ENNReal.ofReal b * N := add_le_add hx hy
    _ = ENNReal.ofReal (a + b) * N := by rw [ENNReal.ofReal_add ha hb, add_mul]

theorem nbd4_mul {N : ℝ≥0∞} {x a w c : ℝ} (ha : 0 ≤ a) (hw : |w| ≤ c) (hx : NBd4 N x a) :
    NBd4 N (x * w) (a * c) := by
  unfold NBd4 at *
  rw [enorm_mul]
  have hw' : ‖w‖ₑ ≤ ENNReal.ofReal c := by
    rw [← ofReal_norm, Real.norm_eq_abs]; exact ENNReal.ofReal_le_ofReal hw
  calc ‖x‖ₑ * ‖w‖ₑ ≤ (ENNReal.ofReal a * N) * ENNReal.ofReal c := mul_le_mul' hx hw'
    _ = ENNReal.ofReal (a * c) * N := by rw [ENNReal.ofReal_mul ha]; ring

theorem nbd4_mono {N : ℝ≥0∞} {x a a' : ℝ} (h : a ≤ a') (hx : NBd4 N x a) : NBd4 N x a' :=
  hx.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal h) _)

theorem sum_bound4 {N : ℝ≥0∞} {cA c1 cE cG : ℝ} (hA0 : 0 ≤ cA) (c10 : 0 ≤ c1) (hE0 : 0 ≤ cE)
    (hG0 : 0 ≤ cG) (A E : Fin 3 → Fin 3 → ℝ) (Gd G : Fin 3 → ℝ)
    (hA : ∀ i j, NBd4 N (A i j) cA) (hE : ∀ j i, NBd4 N (E j i) cE)
    (hGd : ∀ j, |Gd j| ≤ c1) (hG : ∀ j, |G j| ≤ cG) (i : Fin 3) :
    NBd4 N (∑ j, ((A i j + A j i) * Gd j + (E j i + E i j) * G j))
      (3 * (2 * cA * c1 + 2 * cE * cG)) := by
  have per : ∀ j, NBd4 N ((A i j + A j i) * Gd j + (E j i + E i j) * G j)
      (2 * cA * c1 + 2 * cE * cG) := fun j => by
    have h1 := nbd4_mul (by linarith) (hGd j) (nbd4_add hA0 hA0 (hA i j) (hA j i))
    have h2 := nbd4_mul (by linarith) (hG j) (nbd4_add hE0 hE0 (hE j i) (hE i j))
    have := nbd4_add (by positivity) (by positivity) h1 h2
    exact nbd4_mono (le_of_eq (by ring)) this
  rw [Fin.sum_univ_three]
  have := nbd4_add (by positivity) (by positivity)
    (nbd4_add (by positivity) (by positivity) (per 0) (per 1)) (per 2)
  exact nbd4_mono (le_of_eq (by ring)) this

theorem enorm_merid_le4 (v : Merid) : ‖v‖ₑ ≤ ‖v 0‖ₑ + ‖v 1‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_add (norm_nonneg _)
    (norm_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  calc √(‖v 0‖ ^ 2 + ‖v 1‖ ^ 2) ≤ √((‖v 0‖ + ‖v 1‖) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [norm_nonneg (v 0), norm_nonneg (v 1)])
    _ = ‖v 0‖ + ‖v 1‖ := Real.sqrt_sq (by positivity)

/-! ## The pressure gradient is bounded by the weight -/

theorem trainFp_contDiffAt4 (L : ReturnLevel) (z : ℝ × (ℝ × ℝ)) :
    ContDiffAt ℝ ∞ (trainFp L) z := by
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hmem : (Ici (0 : ℝ)) ×ˢ (univ : Set (ℝ × ℝ)) ∈ 𝓝 (Real.exp z.1, z.2) :=
    Filter.mem_of_superset
      (hopen.mem_nhds (show (Real.exp z.1, z.2) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) from
        ⟨Real.exp_pos _, mem_univ _⟩))
      (prod_mono Ioi_subset_Ici_self (subset_refl _))
  have hc := L.train.isTrain.smooth_p.contDiffAt hmem
  have hφ : ContDiffAt ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => (Real.exp z.1, z.2)) z :=
    ((Real.contDiff_exp.comp contDiff_fst).contDiffAt).prodMk contDiff_snd.contDiffAt
  exact hc.comp z hφ

theorem norm_mgrad_trainP_le4 (L : ReturnLevel) {p : Chart} (hp : 0 < p.1) :
    ‖emb (mgrad (trainP L p.1) p.2)‖ ≤ trainWeight 3 L p := by
  have hι : HasFDerivAt (fun y : ℝ × ℝ => (Real.log p.1, y))
      (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) p.2 :=
    hasFDerivAt_prodMk_right (Real.log p.1) p.2
  have hF : HasFDerivAt (trainFp L) (fderiv ℝ (trainFp L) (Real.log p.1, p.2))
      (Real.log p.1, p.2) :=
    ((trainFp_contDiffAt4 L (Real.log p.1, p.2)).differentiableAt (by simp)).hasFDerivAt
  have hcomp := hF.comp p.2 hι
  have hP : trainP L p.1 = fun y => trainFp L (Real.log p.1, y) := by
    funext y; simp [trainP, trainFp, Real.exp_log hp]
  have hd : fderiv ℝ (trainP L p.1) p.2 =
      (fderiv ℝ (trainFp L) (Real.log p.1, p.2)).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) := by
    rw [hP]; exact hcomp.fderiv
  set d := ‖fderiv ℝ (trainFp L) (Real.log p.1, p.2)‖ with hdd
  have hcomp_le : ∀ a : Fin 2, |fderiv ℝ (trainP L p.1) p.2 (ei a)| ≤ d := fun a => by
    rw [hd]
    simp only [ContinuousLinearMap.comp_apply]
    have h1 : ‖(ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) (ei a)‖ ≤ 1 := by
      simp only [ContinuousLinearMap.inr_apply]
      refine norm_prod_le_iff.2 ⟨by simp, ?_⟩
      fin_cases a <;> simp [ei]
    calc |fderiv ℝ (trainFp L) (Real.log p.1, p.2) ((ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) (ei a))|
        = ‖fderiv ℝ (trainFp L) (Real.log p.1, p.2) ((ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) (ei a))‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ d * ‖(ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) (ei a)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ d * 1 := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = d := mul_one _
  have hm : ‖mgrad (trainP L p.1) p.2‖ ≤ d := by
    unfold mgrad
    refine norm_prod_le_iff.2 ⟨?_, ?_⟩
    · rw [Real.norm_eq_abs]; exact hcomp_le 0
    · rw [Real.norm_eq_abs]; exact hcomp_le 1
  have hstep3 : d ≤ ∑ k ∈ Finset.range 5,
        (‖iteratedFDeriv ℝ k (trainFv L) (Real.log p.1, p.2)‖ +
          ‖iteratedFDeriv ℝ k (trainFp L) (Real.log p.1, p.2)‖ +
          ‖iteratedFDeriv ℝ k (trainFpsi L) (Real.log p.1, p.2)‖) := by
    rw [hdd, ← norm_iteratedFDeriv_one (trainFp L)]
    have hsingle := Finset.single_le_sum
      (f := fun k : ℕ => ‖iteratedFDeriv ℝ k (trainFv L) (Real.log p.1, p.2)‖ +
        ‖iteratedFDeriv ℝ k (trainFp L) (Real.log p.1, p.2)‖ +
        ‖iteratedFDeriv ℝ k (trainFpsi L) (Real.log p.1, p.2)‖)
      (fun k _ => by positivity) (Finset.mem_range.2 (by norm_num : (1 : ℕ) < 5))
    have hB := norm_nonneg (iteratedFDeriv ℝ 1 (trainFv L) (Real.log p.1, p.2))
    have hC := norm_nonneg (iteratedFDeriv ℝ 1 (trainFpsi L) (Real.log p.1, p.2))
    linarith
  have hpow : (1 : ℝ) ≤ (1 + |p.2.2|) ^ 3 :=
    one_le_pow₀ (by linarith [abs_nonneg p.2.2])
  have hnn : 0 ≤ ∑ k ∈ Finset.range 5,
      (‖iteratedFDeriv ℝ k (trainFv L) (Real.log p.1, p.2)‖ +
        ‖iteratedFDeriv ℝ k (trainFp L) (Real.log p.1, p.2)‖ +
        ‖iteratedFDeriv ℝ k (trainFpsi L) (Real.log p.1, p.2)‖) :=
    Finset.sum_nonneg (fun k _ => by positivity)
  unfold trainWeight
  exact (norm_emb_le _).trans (hm.trans (hstep3.trans (le_mul_of_one_le_left hnn hpow)))

/-! ## Real arithmetic -/

theorem real_final4 {r P e W3 W4 eta a b c : ℝ} {kA kE k1 : ℕ} (hr : 0 < r) (hP : 1 ≤ P)
    (hr2 : r ^ 2 ≤ P) (he : 0 ≤ e) (hW3 : 0 ≤ W3) (hW34 : W3 ≤ W4) (hη : 0 ≤ eta)
    (hηW : eta * W3 ≤ W4) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    2 * (3 * (2 * (a * P ^ kA * e ^ 3 * r ^ 5) * (b * P ^ k1 * e * r ^ 3 * W3) +
        2 * (c * P ^ kE * e ^ 4 * r ^ 5 * eta) * (r ^ 3 * ((2 + b * P ^ k1) * W3)))) * r⁻¹ ≤
      12 * (a * b + c * (2 + b)) * P ^ (kA + kE + k1 + 1) * e ^ 4 * r ^ 5 * W4 := by
  have hP0 : 0 ≤ P := by linarith
  have hW4 : 0 ≤ W4 := hW3.trans hW34
  have hPk1 : 1 ≤ P ^ k1 := one_le_pow₀ hP
  have hPk1' : 0 ≤ P ^ k1 := by positivity
  have hpA : P ^ kA * P ^ k1 * P ≤ P ^ (kA + kE + k1 + 1) := by
    rw [← pow_add, ← pow_succ]
    exact pow_le_pow_right₀ hP (by omega)
  have hpE : P ^ kE * P ^ k1 * P ≤ P ^ (kA + kE + k1 + 1) := by
    rw [← pow_add, ← pow_succ]
    exact pow_le_pow_right₀ hP (by omega)
  have hbk : 2 + b * P ^ k1 ≤ (2 + b) * P ^ k1 := by nlinarith
  have hrr : r⁻¹ * r ^ 8 = r ^ 7 := by field_simp
  have hPpow : 0 ≤ P ^ kA := by positivity
  have hPpowE : 0 ≤ P ^ kE := by positivity
  have hr7 : r ^ 7 = r ^ 5 * r ^ 2 := by ring
  -- term A
  have tA : 2 * (3 * (2 * (a * P ^ kA * e ^ 3 * r ^ 5) * (b * P ^ k1 * e * r ^ 3 * W3))) * r⁻¹ =
      12 * (a * b * P ^ kA * P ^ k1 * e ^ 4 * r ^ 5) * (r ^ 2 * W3) := by
    field_simp; ring
  have tA' : 12 * (a * b * P ^ kA * P ^ k1 * e ^ 4 * r ^ 5) * (r ^ 2 * W3) ≤
      12 * (a * b) * P ^ (kA + kE + k1 + 1) * e ^ 4 * r ^ 5 * W4 := by
    have h1 : r ^ 2 * W3 ≤ P * W4 := mul_le_mul hr2 hW34 hW3 hP0
    have h0 : 0 ≤ 12 * (a * b * P ^ kA * P ^ k1 * e ^ 4 * r ^ 5) := by positivity
    calc 12 * (a * b * P ^ kA * P ^ k1 * e ^ 4 * r ^ 5) * (r ^ 2 * W3)
        ≤ 12 * (a * b * P ^ kA * P ^ k1 * e ^ 4 * r ^ 5) * (P * W4) :=
          mul_le_mul_of_nonneg_left h1 h0
      _ = 12 * (a * b) * (P ^ kA * P ^ k1 * P) * e ^ 4 * r ^ 5 * W4 := by ring
      _ ≤ 12 * (a * b) * P ^ (kA + kE + k1 + 1) * e ^ 4 * r ^ 5 * W4 := by
          gcongr
  -- term E
  have tE : 2 * (3 * (2 * (c * P ^ kE * e ^ 4 * r ^ 5 * eta) *
        (r ^ 3 * ((2 + b * P ^ k1) * W3)))) * r⁻¹ =
      12 * (c * P ^ kE * (2 + b * P ^ k1) * e ^ 4 * r ^ 5) * (r ^ 2 * (eta * W3)) := by
    field_simp; ring
  have tE' : 12 * (c * P ^ kE * (2 + b * P ^ k1) * e ^ 4 * r ^ 5) * (r ^ 2 * (eta * W3)) ≤
      12 * (c * (2 + b)) * P ^ (kA + kE + k1 + 1) * e ^ 4 * r ^ 5 * W4 := by
    have h1 : r ^ 2 * (eta * W3) ≤ P * W4 := mul_le_mul hr2 hηW (by positivity) hP0
    have h0 : 0 ≤ 12 * (c * P ^ kE * (2 + b * P ^ k1) * e ^ 4 * r ^ 5) := by positivity
    calc 12 * (c * P ^ kE * (2 + b * P ^ k1) * e ^ 4 * r ^ 5) * (r ^ 2 * (eta * W3))
        ≤ 12 * (c * P ^ kE * (2 + b * P ^ k1) * e ^ 4 * r ^ 5) * (P * W4) :=
          mul_le_mul_of_nonneg_left h1 h0
      _ ≤ 12 * (c * P ^ kE * ((2 + b) * P ^ k1) * e ^ 4 * r ^ 5) * (P * W4) := by
          gcongr
      _ = 12 * (c * (2 + b)) * (P ^ kE * P ^ k1 * P) * e ^ 4 * r ^ 5 * W4 := by ring
      _ ≤ 12 * (c * (2 + b)) * P ^ (kA + kE + k1 + 1) * e ^ 4 * r ^ 5 * W4 := by
          gcongr
  have split : ∀ x y : ℝ, 2 * (3 * (x + y)) * r⁻¹ = 2 * (3 * x) * r⁻¹ + 2 * (3 * y) * r⁻¹ :=
    fun x y => by ring
  rw [split, tA, tE]
  calc _ ≤ 12 * (a * b) * P ^ (kA + kE + k1 + 1) * e ^ 4 * r ^ 5 * W4 +
        12 * (c * (2 + b)) * P ^ (kA + kE + k1 + 1) * e ^ 4 * r ^ 5 * W4 := add_le_add tA' tE'
    _ = _ := by ring

theorem norm_vecSp_le4 (w : Vec3) : ‖vecSp w‖ ≤ 2 * ‖w‖ := by
  rw [EuclideanSpace.norm_eq]
  have hM := norm_nonneg w
  have h : ∀ i, ‖(vecSp w) i‖ ^ 2 ≤ ‖w‖ ^ 2 := fun i =>
    pow_le_pow_left₀ (norm_nonneg _) (by simpa [vecSp] using norm_le_pi_norm w i) 2
  calc √(∑ i, ‖(vecSp w) i‖ ^ 2) ≤ √((2 * ‖w‖) ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        rw [Fin.sum_univ_three]
        nlinarith [h 0, h 1, h 2]
    _ = 2 * ‖w‖ := Real.sqrt_sq (by positivity)

theorem trainWeight_three_le_four4 (L : ReturnLevel) (p : Chart) :
    trainWeight 3 L p ≤ trainWeight 4 L p := by
  unfold trainWeight
  refine mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by linarith [abs_nonneg p.2.2]) (by norm_num)) ?_
  exact Finset.sum_nonneg fun j _ => by positivity

theorem eta_weight4 (L : ReturnLevel) (p : Chart) :
    |p.2.2| * trainWeight 3 L p ≤ trainWeight 4 L p := by
  unfold trainWeight
  have hS : 0 ≤ ∑ j ∈ Finset.range 5,
    (‖iteratedFDeriv ℝ j (trainFv L) (Real.log p.1, p.2)‖ +
      ‖iteratedFDeriv ℝ j (trainFp L) (Real.log p.1, p.2)‖ +
      ‖iteratedFDeriv ℝ j (trainFpsi L) (Real.log p.1, p.2)‖) :=
    Finset.sum_nonneg fun j _ => by positivity
  have h0 := abs_nonneg p.2.2
  have : |p.2.2| * (1 + |p.2.2|) ^ 3 ≤ (1 + |p.2.2|) ^ 4 := by
    have : (1 + |p.2.2|) ^ 4 = (1 + |p.2.2|) ^ 3 * (1 + |p.2.2|) := by ring
    rw [this]
    have : 0 ≤ (1 + |p.2.2|) ^ 3 := by positivity
    nlinarith
  calc |p.2.2| * ((1 + |p.2.2|) ^ 3 * _) = (|p.2.2| * (1 + |p.2.2|) ^ 3) * _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right this hS

theorem rpow_three_half4 (s : ℝ) (hs : 0 ≤ s) : s ^ (3 / 2 : ℝ) = Real.sqrt s ^ 3 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hs]; norm_num

theorem rpow_five_half4 (s : ℝ) (hs : 0 ≤ s) : s ^ (5 / 2 : ℝ) = Real.sqrt s ^ 5 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hs]; norm_num

section Pointwise4

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

set_option maxHeartbeats 1600000 in
/-- **Term 4 at one regime** (source 5470-5477). -/
theorem ringTerm4At_of {C1 CE CA : ℝ} {k1 kE kA : ℕ} (hν1 : L.ν ≤ 1) (hε1 : L.ε ≤ 1)
    (hχ : ∀ t : ℝ, t ≤ 1 → K.χf t = 1)
    (h1 : RingChartRulesAt Pl L C1 k1) (h2 : MeanJetAt Pl K L μ CE kE)
    (hA : ActualJetAt Pl K L μ CA kA) :
    RingTerm4At Pl K L μ (12 * (|CA| * |C1| + |CE| * (2 + |C1|))) (kA + kE + k1 + 1) := by
  intro T p hp hp1
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hP1 : 1 ≤ L.ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hsp : 0 < Real.sqrt p.1 := Real.sqrt_pos.2 hp
  have hrr : Real.sqrt p.1 ^ 2 = p.1 := Real.sq_sqrt hp.le
  have h32 : p.1 ^ (3 / 2 : ℝ) = Real.sqrt p.1 ^ 3 := rpow_three_half4 p.1 hp.le
  have h52 : p.1 ^ (5 / 2 : ℝ) = Real.sqrt p.1 ^ 5 := rpow_five_half4 p.1 hp.le
  have hAy : Ay L.ν K.χf (LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T) p.1 =
      LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T p.1 := by
    have : L.ν * p.1 ≤ 1 := by
      rw [le_div_iff₀ hν, mul_comm] at hp1; exact hp1
    simp [Ay, hχ _ this]
  have hr2 : Real.sqrt p.1 ^ 2 ≤ L.ν⁻¹ := by
    rw [hrr]; simpa [one_div] using hp1
  have hW3 := trainWeight_nonneg 3 L p
  have hW34 := trainWeight_three_le_four4 L p
  have hηW := eta_weight4 L p
  have hη0 := abs_nonneg p.2.2
  have hP0 : 0 ≤ L.ν⁻¹ ^ k1 := by positivity
  have hP1k : 1 ≤ L.ν⁻¹ ^ k1 := one_le_pow₀ hP1
  set r := Real.sqrt p.1 with hr
  set A := LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T p.1 with hAdef
  set τ := NearInst.chartTau L.ε⁻¹ p with hτ
  set y := NearInst.chartY L.ε⁻¹ p with hy
  set X := Xmean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) τ with hX
  set g := mgrad (trainP L p.1) p.2 with hg
  set G := physGrad (liftP L τ) y with hG
  set G0 : Space := p.1 ^ (3 / 2 : ℝ) • vecSp (emb g) with hG0
  set N := oldN1 Pl K L T with hN
  set W3 := trainWeight 3 L p with hW3d
  set W4 := trainWeight 4 L p with hW4d
  -- chart rules for the pressure gradient
  have hGd : ‖G - G0‖ ≤ C1 * L.ν⁻¹ ^ k1 * L.ε * p.1 ^ (3 / 2 : ℝ) * W3 :=
    (h1 p hp hp1).2.2.2
  have hC1 : C1 * L.ν⁻¹ ^ k1 * L.ε * p.1 ^ (3 / 2 : ℝ) * W3 ≤
      |C1| * L.ν⁻¹ ^ k1 * L.ε * p.1 ^ (3 / 2 : ℝ) * W3 := by
    have : 0 ≤ L.ν⁻¹ ^ k1 * L.ε * p.1 ^ (3 / 2 : ℝ) * W3 := by positivity
    nlinarith [le_abs_self C1]
  set c1 : ℝ := |C1| * L.ν⁻¹ ^ k1 * L.ε * p.1 ^ (3 / 2 : ℝ) * W3 with hc1
  have hc10 : 0 ≤ c1 := by positivity
  -- bound on G
  have hgW : ‖emb g‖ ≤ W3 := norm_mgrad_trainP_le4 L hp
  have hG0n : ‖G0‖ ≤ p.1 ^ (3 / 2 : ℝ) * (2 * W3) := by
    rw [hG0, norm_smul, Real.norm_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact (norm_vecSp_le4 _).trans (by linarith)
  have hc1' : c1 ≤ |C1| * L.ν⁻¹ ^ k1 * p.1 ^ (3 / 2 : ℝ) * W3 := by
    rw [hc1]
    have : 0 ≤ |C1| * L.ν⁻¹ ^ k1 * p.1 ^ (3 / 2 : ℝ) * W3 := by positivity
    nlinarith
  have hGn : ‖G‖ ≤ p.1 ^ (3 / 2 : ℝ) * ((2 + |C1| * L.ν⁻¹ ^ k1) * W3) := by
    have e : G = G0 + (G - G0) := by abel
    calc ‖G‖ = ‖G0 + (G - G0)‖ := by rw [← e]
      _ ≤ ‖G0‖ + ‖G - G0‖ := norm_add_le _ _
      _ ≤ _ := by nlinarith
  set cG : ℝ := p.1 ^ (3 / 2 : ℝ) * ((2 + |C1| * L.ν⁻¹ ^ k1) * W3) with hcG
  have hcG0 : 0 ≤ cG := by positivity
  -- A bound
  set cA : ℝ := |CA| * L.ν⁻¹ ^ kA * L.ε ^ 3 * p.1 ^ (5 / 2 : ℝ) with hcA
  have hcA0 : 0 ≤ cA := by positivity
  have hAij : ∀ i j, NBd4 N (A i j) cA := fun i j => by
    have h0 := (hA T).1 0 (by norm_num) p.1 hp
    have h0' : ENNReal.ofReal (frob A) ≤ ENNReal.ofReal cA * N := by
      refine h0.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
      rw [hcA]
      have : 0 ≤ L.ν⁻¹ ^ kA * L.ε ^ 3 * p.1 ^ (5 / 2 : ℝ) := by positivity
      nlinarith [le_abs_self CA]
    unfold NBd4
    refine le_trans ?_ h0'
    rw [← ofReal_norm, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal (abs_le_frob A i j)
  set cE : ℝ := |CE| * L.ν⁻¹ ^ kE * L.ε ^ 4 * p.1 ^ (5 / 2 : ℝ) * |p.2.2| with hcE
  have hcE0 : 0 ≤ cE := by positivity
  have hEij : ∀ j i, NBd4 N (physPd X j y i - A i j) cE := fun j i => by
    have h0 := (h2 T p hp hp1).1 j
    unfold NBd4
    have hle : ‖physPd X j y i - A i j‖ₑ ≤
        ‖physPd X j y - vecSp (fun i => LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε
          μ K.χo K.χy T p.1 i j)‖ₑ := by
      rw [← ofReal_norm, ← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      have := PiLp.norm_apply_le (physPd X j y - vecSp (fun i => LjFun (cOf L.ν) K.mZ
        (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T p.1 i j)) i
      simpa [vecSp] using this
    refine hle.trans (h0.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _))
    rw [hcE]
    have : 0 ≤ L.ν⁻¹ ^ kE * L.ε ^ 4 * p.1 ^ (5 / 2 : ℝ) * |p.2.2| := by positivity
    nlinarith [le_abs_self CE]
  have hGj : ∀ j, G j = fderiv ℝ (liftP L τ) y (coordinateVector j) := fun j => rfl
  have hid : ∀ i : Fin 3, (physDXp X (liftP L τ) y) i -
      p.1 ^ (3 / 2 : ℝ) * mv (fun a b => A a b + A b a) (emb g) i =
      ∑ j, ((A i j + A j i) * (G j - G0 j) +
        ((physPd X j y i - A i j) + (physPd X i y j - A j i)) * G j) := by
    intro i
    simp only [physDXp, mv]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e1 : G0 j = p.1 ^ (3 / 2 : ℝ) * emb g j := by simp [hG0, vecSp]
    rw [e1, ← hGj j]
    simp only [PiLp.toLp_apply]
    ring
  have hGdj : ∀ j, |G j - G0 j| ≤ c1 := fun j => by
    have : |(G - G0) j| ≤ ‖G - G0‖ := by
      rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le _ _
    simpa using this.trans (hGd.trans hC1)
  have hGjj : ∀ j, |G j| ≤ cG := fun j => by
    have : |G j| ≤ ‖G‖ := by
      rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le _ _
    exact this.trans hGn
  have hsb := fun i => sum_bound4 hcA0 hc10 hcE0 hcG0 (fun a b => A a b)
    (fun j i => physPd X j y i - A i j) (fun j => G j - G0 j) (fun j => G j) hAij hEij hGdj hGjj i
  set B : ℝ := 3 * (2 * cA * c1 + 2 * cE * cG) with hB
  have hB0 : 0 ≤ B := by positivity
  have hD : ∀ i : Fin 3, NBd4 N ((physDXp X (liftP L τ) y) i -
      p.1 ^ (3 / 2 : ℝ) * mv (fun a b => A a b + A b a) (emb g) i) B := fun i => by
    rw [hid i]; exact hsb i
  have hR : ∀ i : Fin 3, ‖r⁻¹ * ((physDXp X (liftP L τ) y) i -
      p.1 ^ (3 / 2 : ℝ) * mv (fun a b => A a b + A b a) (emb g) i)‖ₑ ≤
      ENNReal.ofReal (B * r⁻¹) * N := fun i => by
    have := nbd4_mul hB0 (show |r⁻¹| ≤ r⁻¹ from (abs_of_pos (inv_pos.2 hsp)).le) (hD i)
    unfold NBd4 at this
    rwa [mul_comm] at this
  have hdiff : wardC4 Pl K L μ T p - ringT3 Pl K L μ T p =
      !₂[r⁻¹ * ((physDXp X (liftP L τ) y) 0 -
        p.1 ^ (3 / 2 : ℝ) * mv (fun a b => A a b + A b a) (emb g) 0),
        r⁻¹ * ((physDXp X (liftP L τ) y) 2 -
        p.1 ^ (3 / 2 : ℝ) * mv (fun a b => A a b + A b a) (emb g) 2)] := by
    ext k
    fin_cases k <;> simp [wardC4, ringT3, coefOf, merOf, hAy, hr, hτ, hy, hX, hg, mul_sub]
  have hfin : ‖wardC4 Pl K L μ T p - ringT3 Pl K L μ T p‖ₑ ≤
      ENNReal.ofReal (2 * (B * r⁻¹)) * N := by
    rw [hdiff]
    refine (enorm_merid_le4 _).trans ?_
    have e : ENNReal.ofReal (2 * (B * r⁻¹)) * N =
        ENNReal.ofReal (B * r⁻¹) * N + ENNReal.ofReal (B * r⁻¹) * N := by
      rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
    rw [e]
    exact add_le_add (by simpa using hR 0) (by simpa using hR 2)
  refine hfin.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
  have key := real_final4 (r := r) (P := L.ν⁻¹) (e := L.ε) (W3 := W3) (W4 := W4)
    (eta := |p.2.2|) (a := |CA|) (b := |C1|) (c := |CE|) (kA := kA) (kE := kE) (k1 := k1)
    hsp hP1 hr2 hε.le hW3 hW34 hη0 hηW (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
  rw [h52]
  have e1 : 2 * (B * r⁻¹) = 2 * B * r⁻¹ := by ring
  rw [e1, hB, hcA, hc1, hcE, hcG, h32, h52]
  exact key

end Pointwise4

/-- **Term 4 along the sequence** (source 5470-5477). -/
theorem ringTerm4_of (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (h6 : D.ActualJet) (h7 : D.JetClock) (h1 : D.RingChartRules) (h2 : D.MeanJet)
    (h3 : D.TrainMoment) : D.RingTerm4 := by
  obtain ⟨C1, k1, e1⟩ := h1
  obtain ⟨CE, kE, e2⟩ := h2
  obtain ⟨CA, kA, e6⟩ := h6
  have hle := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  refine ⟨12 * (|CA| * |C1| + |CE| * (2 + |C1|)), kA + kE + k1 + 1, ?_⟩
  filter_upwards [e1, e2, e6, hle] with n a1 a2 a6 hν z hz
  exact ringTerm4At_of D.Pl D.K (D.level n) (D.mu n z) hν.1 hν.2 (fun t ht => hst.chiF.one t ht)
    a1 (a2 z hz) (a6 z hz)

end UnforcedLeray.Short.PartIIIb.Concrete
