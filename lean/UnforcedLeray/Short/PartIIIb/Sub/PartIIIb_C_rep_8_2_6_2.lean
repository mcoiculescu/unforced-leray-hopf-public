import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_6
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.RingSubst.Term3

/-!
# `PartIII-b:C/rep/8/2/6/2` (decomposition): Term 2 of the four-term substitution

Source `the November 2 reference manuscript` 5470-5475: `-2νC_diff` has leading part
`-2ν A_T:D²_flat v` and the rest is an error.  The three train-derivative facts about the flat
profile `v` of the level (source 5462-5465, weights 5464-5465) are the sub-statements; everything
else (hessian contraction identity, `Ay = A_T` on the young range, the bookkeeping) is proved here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

theorem emb_add (x y : ℝ × ℝ) : emb (x + y) = emb x + emb y := by
  funext k; fin_cases k <;> simp [emb]

theorem emb_smul (c : ℝ) (x : ℝ × ℝ) : emb (c • x) = c • emb x := by
  funext k; fin_cases k <;> simp [emb]

theorem emb_zero : emb (0 : ℝ × ℝ) = 0 := by
  funext k; fin_cases k <;> simp [emb]

section Hess

variable (L : ReturnLevel)

theorem flatDir_one : flatDir 1 = 0 := by
  ext <;> simp [flatDir]

theorem flatD2_mid_left (s : ℝ) (x : ℝ × ℝ) (l : Fin 3) : flatD2 L s x 1 l = 0 := by
  simp [flatD2, flatDir_one, emb_zero]

theorem flatD2_mid_right (s : ℝ) (x : ℝ × ℝ) (j : Fin 3) : flatD2 L s x j 1 = 0 := by
  simp [flatD2, flatDir_one, emb_zero]

theorem flatD2_mi (s : ℝ) (x : ℝ × ℝ) (a b : Fin 2) :
    flatD2 L s x (mi a) (mi b) =
      emb (fderiv ℝ (fun y => fderiv ℝ (trainV L s) y (ei b)) x (ei a)) := by
  fin_cases a <;> fin_cases b <;> simp [flatD2, flatDir, mi, ei]

/-- The hessian contraction as a sum over Cartesian indices, given the symmetry of the second flat
derivatives (`A_{lj}∂_j∂_l v = A_{jl}∂_j∂_l v`). -/
theorem hessContr_eq_sum (A : Mat3) (s : ℝ) (x : ℝ × ℝ)
    (hsymm : ∀ j l : Fin 3, flatD2 L s x j l = flatD2 L s x l j) :
    hessContr A (trainV L s) x = ∑ j : Fin 3, ∑ l : Fin 3, A l j • flatD2 L s x j l := by
  unfold hessContr
  simp only [Fin.sum_univ_two, emb_add, emb_smul]
  rw [← flatD2_mi L s x 0 0, ← flatD2_mi L s x 0 1, ← flatD2_mi L s x 1 0,
    ← flatD2_mi L s x 1 1]
  simp only [Fin.sum_univ_three, flatD2_mid_left, flatD2_mid_right, smul_zero, add_zero, zero_add]
  simp only [mi, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hsymm 2 0]
  abel

end Hess


/-! ## The three sub-statements on the flat train profile -/

/-- **Sub-statement 1** (source 5462, 5464-5465): `|D_flat v| ≤ 𝔴₃` — the first transverse and
`q`-derivatives of the flat velocity `v(s,q,η) = v(e^σ, ·)` are bounded by the weighted train
coefficient (they are among the `(σ,q,η)`-derivatives of order `1` in `trainWeight`). -/
def TrainFlatD1Bound (L : ReturnLevel) : Prop :=
  ∀ p : Chart, 0 < p.1 → ∀ j : Fin 3, ‖flatD1 L p.1 p.2 j‖ ≤ trainWeight 3 L p

/-- **Sub-statement 2** (source 5463, 5464-5465): `|D²_flat v| ≤ 𝔴₃`. -/
def TrainFlatD2Bound (L : ReturnLevel) : Prop :=
  ∀ p : Chart, 0 < p.1 → ∀ j l : Fin 3, ‖flatD2 L p.1 p.2 j l‖ ≤ trainWeight 3 L p

/-- **Sub-statement 3** (the train is smooth, source 5464-5465): the second flat derivatives of
`v` are symmetric, `∂_j∂_l v = ∂_l∂_j v`. -/
def TrainFlatD2Symm (L : ReturnLevel) : Prop :=
  ∀ s : ℝ, 0 < s → ∀ (x : ℝ × ℝ) (j l : Fin 3), flatD2 L s x j l = flatD2 L s x l j

theorem eta_mul_weight_le (L : ReturnLevel) (p : Chart) :
    |p.2.2| * trainWeight 3 L p ≤ trainWeight 4 L p := by
  unfold trainWeight
  have hS : 0 ≤ ∑ j ∈ Finset.range 5,
      (‖iteratedFDeriv ℝ j (trainFv L) (Real.log p.1, p.2)‖ +
        ‖iteratedFDeriv ℝ j (trainFp L) (Real.log p.1, p.2)‖ +
        ‖iteratedFDeriv ℝ j (trainFpsi L) (Real.log p.1, p.2)‖) :=
    Finset.sum_nonneg fun j _ => by positivity
  have h : |p.2.2| * (1 + |p.2.2|) ^ 3 ≤ (1 + |p.2.2|) ^ 4 := by
    have := abs_nonneg p.2.2
    nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ 1 + |p.2.2|) 3]
  calc |p.2.2| * ((1 + |p.2.2|) ^ 3 * _) = (|p.2.2| * (1 + |p.2.2|) ^ 3) * _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h hS

theorem rpow_three_half (s : ℝ) (hs : 0 ≤ s) : s ^ (3 / 2 : ℝ) = Real.sqrt s ^ 3 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hs]; norm_num

theorem bound_of_close (u w : Space) (c W C P ε : ℝ) (hc : 0 ≤ c) (hW : 0 ≤ W) (hP : 1 ≤ P)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hw : ‖w‖ ≤ 2 * W)
    (hu : ‖u - c • w‖ ≤ C * P * ε * c * W) : ‖u‖ ≤ (2 + |C|) * P * c * W := by
  have h1 := norm_le_insert' u (c • w)
  rw [norm_smul, Real.norm_of_nonneg hc] at h1
  have h2 : c * ‖w‖ ≤ 2 * W * c := by nlinarith
  have hP0 : 0 ≤ P := by linarith
  have h3 : C * P * ε * c * W ≤ |C| * P * c * W := by
    have : C * P * ε ≤ |C| * P := by
      calc C * P * ε ≤ |C| * P * ε :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) hP0) hε0
        _ ≤ |C| * P * 1 := mul_le_mul_of_nonneg_left hε1 (by positivity)
        _ = |C| * P := mul_one _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hc) hW
  have h4 : 2 * W * c ≤ 2 * P * c * W := by
    have : 2 * W * c * 1 ≤ 2 * W * c * P := mul_le_mul_of_nonneg_left hP (by positivity)
    nlinarith
  nlinarith


section Pointwise

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

/-- One summand of the Term 2 combination: `(∂_jU)_l ∂_{jl}X - (∂_jX)_l ∂_{jl}U + A_{lj}·s^{3/2}F_{jl}`. -/
def ward2Term (Uf X : Space → Space) (Af : Mat3) (S : ℝ) (F : Fin 3 → Fin 3 → Space) (y : Space)
    (j l : Fin 3) : Space :=
  ((physPd Uf j y) l • physPd2 X j l y - (physPd X j y) l • physPd2 Uf j l y) +
    Af l j • (S • F j l)

/-- The exact algebraic identity of Term 2 (source 4280-4282, 5470-5475). -/
theorem wardC2_add_ringT2 (T : LStr Pl K L) (p : Chart)
    (hsy : ∀ j l : Fin 3, flatD2 L p.1 p.2 j l = flatD2 L p.1 p.2 l j)
    (hAy : Ay L.ν K.χf (LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T) p.1 =
      LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T p.1) :
    wardC2 Pl K L μ T p + ringT2 Pl K L μ T p =
      ((Real.sqrt p.1)⁻¹ * (2 * L.ν)) •
        (!₂[(∑ j : Fin 3, ∑ l : Fin 3, ward2Term (rawU Pl L (NearInst.chartTau L.ε⁻¹ p))
            (Xmean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) (NearInst.chartTau L.ε⁻¹ p))
            (LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T p.1)
            (p.1 ^ (3 / 2 : ℝ)) (fun j l => vecSp (flatD2 L p.1 p.2 j l))
            (NearInst.chartY L.ε⁻¹ p) j l) 0,
          (∑ j : Fin 3, ∑ l : Fin 3, ward2Term (rawU Pl L (NearInst.chartTau L.ε⁻¹ p))
            (Xmean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) (NearInst.chartTau L.ε⁻¹ p))
            (LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T p.1)
            (p.1 ^ (3 / 2 : ℝ)) (fun j l => vecSp (flatD2 L p.1 p.2 j l))
            (NearInst.chartY L.ε⁻¹ p) j l) 2] : Merid) := by
  unfold wardC2 ringT2
  rw [hAy, hessContr_eq_sum L _ _ _ hsy]
  ext i
  fin_cases i <;>
    simp [coefOf, merOf, physCdiff, ward2Term, vecSp, Finset.sum_apply, Finset.mul_sum,
      Finset.sum_add_distrib, mul_add, mul_sub] <;> ring_nf

/-- **Term 2 at one regime** (source 5470-5475). -/
theorem ringTerm2At_of {C1 C2 C4 : ℝ} {k1 k2 k4 : ℕ} (hν1 : L.ν ≤ 1) (hε1 : L.ε ≤ 1)
    (h1 : RingChartRulesAt Pl L C1 k1) (h2 : MeanJetAt Pl K L μ C2 k2)
    (h4 : ActualJetAt Pl K L μ C4 k4) (hχ : ∀ t : ℝ, t ≤ 1 → K.χf t = 1)
    (hD1 : TrainFlatD1Bound L) (hD2 : TrainFlatD2Bound L) (hS : TrainFlatD2Symm L) :
    RingTerm2At Pl K L μ (18 * (2 * (2 + |C1|) * |C2| + |C4| * |C1|)) (k1 + k2 + k4) := by
  intro T p hp hp1
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hP1 : 1 ≤ L.ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hsp : 0 < Real.sqrt p.1 := Real.sqrt_pos.2 hp
  have hrr : Real.sqrt p.1 ^ 2 = p.1 := Real.sq_sqrt hp.le
  have h6 : p.1 ^ (3 : ℝ) = Real.sqrt p.1 ^ 6 := by
    have : Real.sqrt p.1 ^ 6 = (Real.sqrt p.1 ^ 2) ^ 3 := by ring
    rw [this, hrr]; norm_cast
  have h52 : p.1 ^ (5 / 2 : ℝ) = Real.sqrt p.1 ^ 5 := rpow_five_half p.1 hp.le
  have h32 : p.1 ^ (3 / 2 : ℝ) = Real.sqrt p.1 ^ 3 := rpow_three_half p.1 hp.le
  have hνs : L.ν * p.1 ≤ 1 := by
    rw [le_div_iff₀ hν] at hp1; linarith
  have hAy : Ay L.ν K.χf (LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T)
      p.1 = LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T p.1 := by
    unfold Ay; rw [hχ _ hνs, one_smul]
  rw [wardC2_add_ringT2 Pl K L μ T p (hS p.1 hp p.2) hAy]
  obtain ⟨hU0, hU1, hU2, -⟩ := h1 p hp hp1
  obtain ⟨hX1, -, hX2⟩ := h2 T p hp hp1
  have hAj := (h4 T).1 0 (Nat.zero_le _) p.1 hp
  set r := Real.sqrt p.1 with hr
  set y := NearInst.chartY L.ε⁻¹ p with hy
  set Uf := rawU Pl L (NearInst.chartTau L.ε⁻¹ p) with hUf
  set X := Xmean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) (NearInst.chartTau L.ε⁻¹ p) with hX
  set Af := LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T p.1 with hAf
  set W3 := trainWeight 3 L p with hW3
  set W4 := trainWeight 4 L p with hW4
  set N := oldN1 Pl K L T with hN
  set η := |p.2.2| with hη
  have hW30 : 0 ≤ W3 := trainWeight_nonneg 3 L p
  have hW34 : W3 ≤ W4 := trainWeight_three_le_four L p
  have hηW : η * W3 ≤ W4 := eta_mul_weight_le L p
  have hη0 : 0 ≤ η := abs_nonneg _
  have hP1k : ∀ k : ℕ, 1 ≤ L.ν⁻¹ ^ k := fun k => one_le_pow₀ hP1
  -- bounds on U
  have dU : ∀ j : Fin 3, ‖physPd Uf j y‖ ≤ (2 + |C1|) * L.ν⁻¹ ^ k1 * p.1 * W3 := fun j => by
    refine bound_of_close _ (vecSp (flatD1 L p.1 p.2 j)) p.1 W3 C1 _ L.ε hp.le hW30 (hP1k k1)
      hε.le hε1 ((norm_vecSp_le _).trans (by linarith [hD1 p hp j])) (hU1 j)
  have ddU : ∀ j l : Fin 3, ‖physPd2 Uf j l y‖ ≤
      (2 + |C1|) * L.ν⁻¹ ^ k1 * p.1 ^ (3 / 2 : ℝ) * W3 := fun j l => by
    refine bound_of_close _ (vecSp (flatD2 L p.1 p.2 j l)) (p.1 ^ (3 / 2 : ℝ)) W3 C1 _ L.ε
      (by positivity) hW30 (hP1k k1) hε.le hε1 ((norm_vecSp_le _).trans (by linarith [hD2 p hp j l]))
      (hU2 j l)
  have e2 : ∀ j l : Fin 3, ‖physPd2 Uf j l y - p.1 ^ (3 / 2 : ℝ) • vecSp (flatD2 L p.1 p.2 j l)‖ ≤
      |C1| * L.ν⁻¹ ^ k1 * L.ε * p.1 ^ (3 / 2 : ℝ) * W3 := fun j l =>
    (hU2 j l).trans (by
      have : C1 * L.ν⁻¹ ^ k1 ≤ |C1| * L.ν⁻¹ ^ k1 :=
        mul_le_mul_of_nonneg_right (le_abs_self C1) (by positivity)
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right this hε.le) (by positivity : (0:ℝ) ≤ p.1 ^ (3 / 2 : ℝ)))
        hW30
      exact this)
  have hterm : ∀ j l : Fin 3,
      ward2Term Uf X Af (p.1 ^ (3 / 2 : ℝ)) (fun j l => vecSp (flatD2 L p.1 p.2 j l)) y j l =
        (physPd Uf j y) l • physPd2 X j l y -
          ((physPd X j y) l - Af l j) • physPd2 Uf j l y -
          Af l j • (physPd2 Uf j l y - p.1 ^ (3 / 2 : ℝ) • vecSp (flatD2 L p.1 p.2 j l)) := by
    intro j l
    unfold ward2Term
    module
  -- ENNReal bounds on the pieces
  have bU : ∀ j l : Fin 3, ‖(physPd Uf j y) l‖ₑ ≤
      ENNReal.ofReal ((2 + |C1|) * L.ν⁻¹ ^ k1 * p.1 * W3) := fun j l => by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal ((PiLp.norm_apply_le _ l).trans (dU j))
  have bX2 : ∀ j l : Fin 3, ‖physPd2 X j l y‖ₑ ≤
      ENNReal.ofReal (|C2| * L.ν⁻¹ ^ k2 * L.ε ^ 4 * r ^ 6) * N := fun j l => by
    refine (hX2 j l).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
    rw [h6]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (le_abs_self C2) (by positivity)) (by positivity)) (by positivity)
  have bE1 : ∀ j l : Fin 3, ‖(physPd X j y) l - Af l j‖ₑ ≤
      ENNReal.ofReal (|C2| * L.ν⁻¹ ^ k2 * L.ε ^ 4 * r ^ 5 * η) * N := fun j l => by
    have h := hX1 j
    have hc : ‖(physPd X j y) l - Af l j‖ₑ ≤
        ‖physPd X j y - vecSp (fun i => LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ
          K.χo K.χy T p.1 i j)‖ₑ := by
      rw [← ofReal_norm, ← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      refine le_trans (le_of_eq ?_) (PiLp.norm_apply_le _ l)
      simp [vecSp, hAf]
    refine hc.trans (h.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _))
    rw [h52]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self C2) (by positivity)) (by positivity))
      (by positivity)) hη0
  have bA : ∀ j l : Fin 3, ‖Af l j‖ₑ ≤
      ENNReal.ofReal (|C4| * L.ν⁻¹ ^ k4 * L.ε ^ 3 * r ^ 5) * N := fun j l => by
    have h : ENNReal.ofReal (frob Af) ≤
        ENNReal.ofReal (C4 * L.ν⁻¹ ^ k4 * L.ε ^ 3 * p.1 ^ (5 / 2 : ℝ)) * N := hAj
    rw [Real.enorm_eq_ofReal_abs]
    refine (ENNReal.ofReal_le_ofReal (abs_le_frob Af l j)).trans (h.trans
      (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _))
    rw [h52]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (le_abs_self C4) (by positivity)) (by positivity)) (by positivity)
  have bU2 : ∀ j l : Fin 3, ‖physPd2 Uf j l y‖ₑ ≤
      ENNReal.ofReal ((2 + |C1|) * L.ν⁻¹ ^ k1 * r ^ 3 * W3) := fun j l => by
    rw [← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ((ddU j l).trans ?_)
    rw [h32]
  have bE2 : ∀ j l : Fin 3, ‖physPd2 Uf j l y - p.1 ^ (3 / 2 : ℝ) • vecSp (flatD2 L p.1 p.2 j l)‖ₑ ≤
      ENNReal.ofReal (|C1| * L.ν⁻¹ ^ k1 * L.ε * r ^ 3 * W3) := fun j l => by
    rw [← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ((e2 j l).trans ?_)
    rw [h32]
  set MdU := (2 + |C1|) * L.ν⁻¹ ^ k1 * p.1 * W3 with hMdU
  set b2 := |C2| * L.ν⁻¹ ^ k2 * L.ε ^ 4 * r ^ 6 with hb2
  set b1 := |C2| * L.ν⁻¹ ^ k2 * L.ε ^ 4 * r ^ 5 * η with hb1
  set a4 := |C4| * L.ν⁻¹ ^ k4 * L.ε ^ 3 * r ^ 5 with ha4
  set MddU := (2 + |C1|) * L.ν⁻¹ ^ k1 * r ^ 3 * W3 with hMddU
  set be2 := |C1| * L.ν⁻¹ ^ k1 * L.ε * r ^ 3 * W3 with hbe2
  have hMdU0 : 0 ≤ MdU := by positivity
  have hb20 : 0 ≤ b2 := by positivity
  have hb10 : 0 ≤ b1 := by positivity
  have ha40 : 0 ≤ a4 := by positivity
  have hMddU0 : 0 ≤ MddU := by positivity
  have hbe20 : 0 ≤ be2 := by positivity
  set Q := MdU * b2 + b1 * MddU + a4 * be2 with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hT : ∀ j l : Fin 3, ‖ward2Term Uf X Af (p.1 ^ (3 / 2 : ℝ))
      (fun j l => vecSp (flatD2 L p.1 p.2 j l)) y j l‖ₑ ≤ ENNReal.ofReal Q * N := fun j l => by
    rw [hterm j l]
    refine (enorm_sub_le.trans (add_le_add enorm_sub_le le_rfl)).trans ?_
    rw [enorm_smul, enorm_smul, enorm_smul]
    have c1 := mul_le_mul' (bU j l) (bX2 j l)
    have c2 := mul_le_mul' (bE1 j l) (bU2 j l)
    have c3 := mul_le_mul' (bA j l) (bE2 j l)
    have : ENNReal.ofReal Q * N = ENNReal.ofReal MdU * (ENNReal.ofReal b2 * N) +
        ENNReal.ofReal b1 * N * ENNReal.ofReal MddU + ENNReal.ofReal a4 * N * ENNReal.ofReal be2 := by
      rw [hQ, ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hMdU0,
        ENNReal.ofReal_mul hb10, ENNReal.ofReal_mul ha40]
      ring
    rw [this]
    exact add_le_add (add_le_add c1 c2) c3
  set G : Space := ∑ j : Fin 3, ∑ l : Fin 3, ward2Term Uf X Af (p.1 ^ (3 / 2 : ℝ))
    (fun j l => vecSp (flatD2 L p.1 p.2 j l)) y j l with hG
  have hGn : ‖G‖ₑ ≤ 9 * (ENNReal.ofReal Q * N) := by
    calc ‖G‖ₑ ≤ ∑ j : Fin 3, ‖∑ l : Fin 3, ward2Term Uf X Af (p.1 ^ (3 / 2 : ℝ))
          (fun j l => vecSp (flatD2 L p.1 p.2 j l)) y j l‖ₑ := enorm_sum_le _ _
      _ ≤ ∑ j : Fin 3, ∑ l : Fin 3, ‖ward2Term Uf X Af (p.1 ^ (3 / 2 : ℝ))
          (fun j l => vecSp (flatD2 L p.1 p.2 j l)) y j l‖ₑ :=
          Finset.sum_le_sum fun j _ => enorm_sum_le _ _
      _ ≤ ∑ j : Fin 3, ∑ l : Fin 3, ENNReal.ofReal Q * N :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ => hT j l
      _ = 9 * (ENNReal.ofReal Q * N) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  have hc0 : 0 ≤ r⁻¹ * (2 * L.ν) := by positivity
  unfold ringBound
  rw [enorm_smul, Real.enorm_of_nonneg hc0]
  have hm : ‖(!₂[G 0, G 2] : Merid)‖ₑ ≤ ‖G‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (norm_meridPair_le G)
  refine (mul_le_mul_right (hm.trans hGn) _).trans ?_
  -- the real inequality
  set Pk := L.ν⁻¹ ^ (k1 + k2 + k4) with hPk
  have hP12 : L.ν⁻¹ ^ k1 * L.ν⁻¹ ^ k2 ≤ Pk := by
    rw [← pow_add]; exact pow_le_pow_right₀ hP1 (by omega)
  have hP41 : L.ν⁻¹ ^ k4 * L.ν⁻¹ ^ k1 ≤ Pk := by
    rw [← pow_add]; exact pow_le_pow_right₀ hP1 (by omega)
  set κ := 2 * (2 + |C1|) * |C2| + |C4| * |C1| with hκ
  have hηW' : η * W3 ≤ W4 := hηW
  have hQle : Q ≤ L.ε ^ 4 * r ^ 8 * W4 * Pk * κ := by
    have hp1r : p.1 = r ^ 2 := hrr.symm
    have e : Q = L.ε ^ 4 * r ^ 8 * ((2 + |C1|) * |C2| * (L.ν⁻¹ ^ k1 * L.ν⁻¹ ^ k2) * W3 +
        (2 + |C1|) * |C2| * (L.ν⁻¹ ^ k1 * L.ν⁻¹ ^ k2) * (η * W3) +
        |C4| * |C1| * (L.ν⁻¹ ^ k4 * L.ν⁻¹ ^ k1) * W3) := by
      rw [hQ, hMdU, hb2, hb1, ha4, hMddU, hbe2, hp1r]; ring
    rw [e]
    have hE : 0 ≤ L.ε ^ 4 * r ^ 8 := by positivity
    have h12 : (2 + |C1|) * |C2| * (L.ν⁻¹ ^ k1 * L.ν⁻¹ ^ k2) * W3 ≤ (2 + |C1|) * |C2| * Pk * W4 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hP12 (by positivity)) hW34 hW30 (by positivity)
    have h13 : (2 + |C1|) * |C2| * (L.ν⁻¹ ^ k1 * L.ν⁻¹ ^ k2) * (η * W3) ≤
        (2 + |C1|) * |C2| * Pk * W4 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hP12 (by positivity)) hηW' (by positivity)
        (by positivity)
    have h14 : |C4| * |C1| * (L.ν⁻¹ ^ k4 * L.ν⁻¹ ^ k1) * W3 ≤ |C4| * |C1| * Pk * W4 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hP41 (by positivity)) hW34 hW30 (by positivity)
    calc L.ε ^ 4 * r ^ 8 * ((2 + |C1|) * |C2| * (L.ν⁻¹ ^ k1 * L.ν⁻¹ ^ k2) * W3 +
        (2 + |C1|) * |C2| * (L.ν⁻¹ ^ k1 * L.ν⁻¹ ^ k2) * (η * W3) +
        |C4| * |C1| * (L.ν⁻¹ ^ k4 * L.ν⁻¹ ^ k1) * W3)
        ≤ L.ε ^ 4 * r ^ 8 * ((2 + |C1|) * |C2| * Pk * W4 + (2 + |C1|) * |C2| * Pk * W4 +
          |C4| * |C1| * Pk * W4) := mul_le_mul_of_nonneg_left (add_le_add (add_le_add h12 h13) h14) hE
      _ = L.ε ^ 4 * r ^ 8 * W4 * Pk * κ := by rw [hκ]; ring
  have hκ0 : 0 ≤ κ := by rw [hκ]; positivity
  have hPk0 : 0 ≤ Pk := by rw [hPk]; positivity
  have hW40 : 0 ≤ W4 := trainWeight_nonneg 4 L p
  have hνr2 : L.ν * r ^ 2 ≤ 1 := by rw [hrr]; exact hνs
  have hreal : r⁻¹ * (2 * L.ν) * (9 * Q) ≤ 18 * (2 * (2 + |C1|) * |C2| + |C4| * |C1|) *
      L.ν⁻¹ ^ (k1 + k2 + k4) * L.ε ^ 4 * p.1 ^ (5 / 2 : ℝ) * W4 := by
    have hc : 0 ≤ r⁻¹ * (2 * L.ν) := hc0
    calc r⁻¹ * (2 * L.ν) * (9 * Q) ≤ r⁻¹ * (2 * L.ν) * (9 * (L.ε ^ 4 * r ^ 8 * W4 * Pk * κ)) :=
          mul_le_mul_of_nonneg_left (by linarith) hc
      _ = (18 * κ * Pk * L.ε ^ 4 * W4 * r ^ 5) * (L.ν * r ^ 2) := by field_simp; ring
      _ ≤ (18 * κ * Pk * L.ε ^ 4 * W4 * r ^ 5) * 1 :=
          mul_le_mul_of_nonneg_left hνr2 (by positivity)
      _ = _ := by rw [h52, hκ, hPk]; ring
  calc ENNReal.ofReal (r⁻¹ * (2 * L.ν)) * (9 * (ENNReal.ofReal Q * N))
      = ENNReal.ofReal (r⁻¹ * (2 * L.ν) * (9 * Q)) * N := by
        have h9 : ENNReal.ofReal (9 * Q) = 9 * ENNReal.ofReal Q := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
        rw [ENNReal.ofReal_mul hc0, h9]
        ring
    _ ≤ _ := mul_le_mul_left (ENNReal.ofReal_le_ofReal hreal) _

end Pointwise


/-- **Term 2 along the sequence from the three train-derivative facts**
(source 5470-5475). -/
theorem ringTerm2_of_of (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (h6 : D.ActualJet) (_h7 : D.JetClock) (h1 : D.RingChartRules) (h2 : D.MeanJet)
    (_h3 : D.TrainMoment) (hD1 : ∀ L : ReturnLevel, TrainFlatD1Bound L)
    (hD2 : ∀ L : ReturnLevel, TrainFlatD2Bound L) (hS : ∀ L : ReturnLevel, TrainFlatD2Symm L) :
    D.RingTerm2 := by
  obtain ⟨C1, k1, e1⟩ := h1
  obtain ⟨C2, k2, e2⟩ := h2
  obtain ⟨C4, k4, e4⟩ := h6
  have hle := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  refine ⟨18 * (2 * (2 + |C1|) * |C2| + |C4| * |C1|), k1 + k2 + k4, ?_⟩
  filter_upwards [e1, e2, e4, hle] with n a1 a2 a4 hν z hz
  exact ringTerm2At_of D.Pl D.K (D.level n) (D.mu n z) hν.1 hν.2 a1 (a2 z hz) (a4 z hz)
    (fun t ht => hst.chiF.one t ht) (hD1 _) (hD2 _) (hS _)

end UnforcedLeray.Short.PartIIIb.Concrete
