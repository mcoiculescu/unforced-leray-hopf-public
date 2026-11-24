import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2Org

/-!
# `PartIII-b:C/rep/8/2/6` (decomposition): substitution into the four Ward terms

Source `the November 2 reference manuscript` 5460-5477 (ring-chart rules and the
four-term substitution; "The error in `2U·∇Y` has size `P_ν ε⁴ s³ N`... The errors in `DXD²U`,
`DX∇p`, `DUD²X` and `(U⊗U):D²X` have size `P_ν ε⁴ s⁴ N`"), 5438-5448 (mean jets), 5449-5453
(clock).

`wardEXY = E₁ - E₂ + E₃ - E₄` with `E₁ = 2 DY·U`, `E₂ = 2ν C_diff`, `E₃ = (U⊗U):D²X`,
`E₄ = (DX+DXᵀ)∇p`.  At a young chart point the chart coefficients `c_k = coefOf E_k` are compared
with the three pieces `T₁, T₂, T₃` of the jet ring expression `ringAffJet = T₁ + T₂ - T₃`:

* `c₁ ≈ T₁`   (`2B_jv`; ring-chart rules for `U`, `MeanJetAt` for `∂Y`),
* `c₂ ≈ -T₂`  (`C_diff = DU·D²X - DX·D²U`: the first part is an error, the second gives
  `-A_T:D²_flat v`; `Ay = A_T` on the young range since `χ_f(νs) = 1`, `A_T = 0` beyond `1/ν`),
* `c₃ ≈ 0`    (`(U⊗U):D²X`, `U = O(√s)`, `|D²X| ≤ ε⁴s³N`),
* `c₄ ≈ T₃`   (`(A_T+A_Tᵀ)∇_flat p`).

The hypotheses of `ringSubst_of` below are the four term estimates; each is proved separately.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

section Terms

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

/-- Chart coefficient of the term `E₁ = 2 DY·U` of the raw mean Ward residual. -/
def wardC1 (T : LStr Pl K L) : Chart → Merid :=
  coefOf L.ε⁻¹ (fun τ y => (2 : ℝ) • fderiv ℝ (Ymean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) τ) y
    (rawU Pl L τ y))

/-- Chart coefficient of the term `E₂ = 2ν C_diff`. -/
def wardC2 (T : LStr Pl K L) : Chart → Merid :=
  coefOf L.ε⁻¹ (fun τ y => (2 * L.ν) • physCdiff (rawU Pl L τ)
    (Xmean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) τ) y)

/-- Chart coefficient of the term `E₃ = (U⊗U):D²X`. -/
def wardC3 (T : LStr Pl K L) : Chart → Merid :=
  coefOf L.ε⁻¹ (fun τ y => physUUD2 (rawU Pl L τ)
    (Xmean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) τ) y)

/-- Chart coefficient of the term `E₄ = (DX+DXᵀ)∇p_lift`. -/
def wardC4 (T : LStr Pl K L) : Chart → Merid :=
  coefOf L.ε⁻¹ (fun τ y => physDXp (Xmean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) τ)
    (liftP L τ) y)

/-- The piece `2B_jv` of `ringAffJet` (chart coefficient `s^{-1/2}·s^{3/2}·`). -/
def ringT1 (T : LStr Pl K L) : Chart → Merid := fun p =>
  merOf ((Real.sqrt p.1)⁻¹ • (p.1 ^ (3 / 2 : ℝ) • ((2 : ℝ) •
    mv (Bjet (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) p.1) (emb (trainV L p.1 p.2)))))

/-- The piece `2ν A_T:D²_flat v` of `ringAffJet`. -/
def ringT2 (T : LStr Pl K L) : Chart → Merid := fun p =>
  merOf ((Real.sqrt p.1)⁻¹ • (p.1 ^ (3 / 2 : ℝ) • ((2 * L.ν) •
    hessContr (Ay L.ν K.χf (LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T)
      p.1) (trainV L p.1) p.2)))

/-- The piece `(A_T + A_Tᵀ)∇_flat p_cyl` of `ringAffJet`. -/
def ringT3 (T : LStr Pl K L) : Chart → Merid := fun p =>
  merOf ((Real.sqrt p.1)⁻¹ • (p.1 ^ (3 / 2 : ℝ) •
    mv (fun a b =>
      Ay L.ν K.χf (LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T) p.1 a b +
      Ay L.ν K.χf (LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T) p.1 b a)
      (emb (mgrad (trainP L p.1) p.2))))

theorem merOf_comb (r s : ℝ) (a b c : Vec3) :
    merOf (r • (s • (a + b - c))) = merOf (r • (s • a)) + merOf (r • (s • b)) -
      merOf (r • (s • c)) := by
  ext i; fin_cases i <;> simp [merOf] <;> ring

theorem meanERaw_eq (T : LStr Pl K L) (p : Chart) :
    meanERaw Pl K L μ T p =
      wardC1 Pl K L μ T p - wardC2 Pl K L μ T p + wardC3 Pl K L μ T p - wardC4 Pl K L μ T p := by
  ext i; fin_cases i <;>
    simp [meanERaw, wardEXY, wardC1, wardC2, wardC3, wardC4, coefOf] <;> ring

theorem ringAffJet_eq (T : LStr Pl K L) (p : Chart) :
    ringAffJet Pl K L μ T p = ringT1 Pl K L μ T p + ringT2 Pl K L μ T p - ringT3 Pl K L μ T p := by
  unfold ringAffJet ringAffB ringT1 ringT2 ringT3
  have := merOf_comb (Real.sqrt p.1)⁻¹ (p.1 ^ (3 / 2 : ℝ))
    ((2 : ℝ) • mv (Bjet (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) p.1) (emb (trainV L p.1 p.2)))
    ((2 * L.ν) • hessContr (Ay L.ν K.χf (LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ
      K.χo K.χy T) p.1) (trainV L p.1) p.2)
    (mv (fun a b => Ay L.ν K.χf (LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T)
      p.1 a b + Ay L.ν K.χf (LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T)
      p.1 b a) (emb (mgrad (trainP L p.1) p.2)))
  rw [this]

/-- The common bound of the four term estimates (source 5470-5477). -/
def ringBound (C : ℝ) (k : ℕ) (T : LStr Pl K L) (p : Chart) : ℝ≥0∞ :=
  ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ 4 * p.1 ^ (5 / 2 : ℝ) * trainWeight 4 L p) *
    oldN1 Pl K L T

/-- Term 1 (`2U·∇Y`, source 5470-5472: error `P_ν ε⁴ s³ N 𝔴`). -/
def RingTerm1At (C : ℝ) (k : ℕ) : Prop :=
  ∀ T : LStr Pl K L, ∀ p : Chart, 0 < p.1 → p.1 ≤ 1 / L.ν →
    ‖wardC1 Pl K L μ T p - ringT1 Pl K L μ T p‖ₑ ≤ ringBound Pl K L C k T p

/-- Term 2 (`-2νC_diff`, leading part `-A_T:D²_flat v`; `Ay = A_T` on the young range). -/
def RingTerm2At (C : ℝ) (k : ℕ) : Prop :=
  ∀ T : LStr Pl K L, ∀ p : Chart, 0 < p.1 → p.1 ≤ 1 / L.ν →
    ‖wardC2 Pl K L μ T p + ringT2 Pl K L μ T p‖ₑ ≤ ringBound Pl K L C k T p

/-- Term 3 (`(U⊗U):D²X` is an error, source 5473-5475). -/
def RingTerm3At (C : ℝ) (k : ℕ) : Prop :=
  ∀ T : LStr Pl K L, ∀ p : Chart, 0 < p.1 → p.1 ≤ 1 / L.ν →
    ‖wardC3 Pl K L μ T p‖ₑ ≤ ringBound Pl K L C k T p

/-- Term 4 (`(DX+DXᵀ)∇p`, leading part `(A_T+A_Tᵀ)∇_flat p_cyl`). -/
def RingTerm4At (C : ℝ) (k : ℕ) : Prop :=
  ∀ T : LStr Pl K L, ∀ p : Chart, 0 < p.1 → p.1 ≤ 1 / L.ν →
    ‖wardC4 Pl K L μ T p - ringT3 Pl K L μ T p‖ₑ ≤ ringBound Pl K L C k T p

theorem real_mono (C a e s w : ℝ) (k K : ℕ) (ha : 1 ≤ a) (hk : k ≤ K) (he : 0 ≤ e) (hs : 0 ≤ s)
    (hw : 0 ≤ w) : C * a ^ k * e * s * w ≤ |C| * a ^ K * e * s * w := by
  have ha0 : 0 ≤ a := by linarith
  have h1 : a ^ k ≤ a ^ K := pow_le_pow_right₀ ha hk
  have h2 : C * a ^ k ≤ |C| * a ^ K :=
    calc C * a ^ k ≤ |C| * a ^ k := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ ≤ |C| * a ^ K := mul_le_mul_of_nonneg_left h1 (abs_nonneg C)
  have := mul_le_mul_of_nonneg_right h2 he
  have := mul_le_mul_of_nonneg_right this hs
  exact mul_le_mul_of_nonneg_right this hw

theorem ringBound_mono (C : ℝ) (k KK : ℕ) (T : LStr Pl K L) (p : Chart) (hp : 0 < p.1)
    (hν1 : L.ν ≤ 1) (hk : k ≤ KK) :
    ringBound Pl K L C k T p ≤ ringBound Pl K L |C| KK T p := by
  unfold ringBound
  refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
  have ha : 1 ≤ L.ν⁻¹ := one_le_inv₀ L.ν_pos |>.2 hν1
  exact real_mono C L.ν⁻¹ (L.ε ^ 4) (p.1 ^ (5 / 2 : ℝ)) (trainWeight 4 L p) k KK ha hk
    (by have := L.ε_pos; positivity) (by positivity) (trainWeight_nonneg _ _ _)

theorem ringBound_add (C₁ C₂ C₃ C₄ : ℝ) (KK : ℕ) (T : LStr Pl K L) (p : Chart) (hp : 0 < p.1) :
    ringBound Pl K L |C₁| KK T p + ringBound Pl K L |C₂| KK T p + ringBound Pl K L |C₃| KK T p +
      ringBound Pl K L |C₄| KK T p ≤
      ringBound Pl K L (|C₁| + |C₂| + |C₃| + |C₄|) KK T p := by
  unfold ringBound
  rw [← add_mul, ← add_mul, ← add_mul]
  refine mul_le_mul_left ?_ _
  rw [← ENNReal.ofReal_add, ← ENNReal.ofReal_add, ← ENNReal.ofReal_add]
  · refine ENNReal.ofReal_le_ofReal (le_of_eq ?_); ring
  all_goals
    have := L.ε_pos
    have := trainWeight_nonneg 4 L p
    have : 0 ≤ L.ν⁻¹ := inv_nonneg.2 L.ν_pos.le
    positivity

theorem ringSubstAt_of_terms {C₁ C₂ C₃ C₄ : ℝ} {k₁ k₂ k₃ k₄ : ℕ}
    (h1 : RingTerm1At Pl K L μ C₁ k₁) (h2 : RingTerm2At Pl K L μ C₂ k₂)
    (h3 : RingTerm3At Pl K L μ C₃ k₃) (h4 : RingTerm4At Pl K L μ C₄ k₄)
    (hν1 : L.ν ≤ 1) :
    RingSubstAt Pl K L μ (|C₁| + |C₂| + |C₃| + |C₄|) (k₁ + k₂ + k₃ + k₄) := by
  intro T p hp hp1
  have e : meanERaw Pl K L μ T p - ringAffJet Pl K L μ T p =
      (wardC1 Pl K L μ T p - ringT1 Pl K L μ T p) - (wardC2 Pl K L μ T p + ringT2 Pl K L μ T p) +
        wardC3 Pl K L μ T p - (wardC4 Pl K L μ T p - ringT3 Pl K L μ T p) := by
    rw [meanERaw_eq, ringAffJet_eq]; abel
  rw [e]
  have b1 := (h1 T p hp hp1).trans (ringBound_mono Pl K L C₁ k₁ (k₁ + k₂ + k₃ + k₄) T p hp hν1
    (by omega))
  have b2 := (h2 T p hp hp1).trans (ringBound_mono Pl K L C₂ k₂ (k₁ + k₂ + k₃ + k₄) T p hp hν1
    (by omega))
  have b3 := (h3 T p hp hp1).trans (ringBound_mono Pl K L C₃ k₃ (k₁ + k₂ + k₃ + k₄) T p hp hν1
    (by omega))
  have b4 := (h4 T p hp hp1).trans (ringBound_mono Pl K L C₄ k₄ (k₁ + k₂ + k₃ + k₄) T p hp hν1
    (by omega))
  refine (enorm_sub_le.trans (add_le_add ((enorm_add_le _ _).trans (add_le_add
    ((enorm_sub_le).trans (add_le_add b1 b2)) b3)) b4)).trans ?_
  refine le_trans (le_of_eq ?_) (ringBound_add Pl K L C₁ C₂ C₃ C₄ _ T p hp)
  rfl

end Terms

namespace SeqData

variable (D : SeqData)

/-- Term 1 along the sequence. -/
def RingTerm1 : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    RingTerm1At D.Pl D.K (D.level n) (D.mu n z) C k

/-- Term 2 along the sequence. -/
def RingTerm2 : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    RingTerm2At D.Pl D.K (D.level n) (D.mu n z) C k

/-- Term 3 along the sequence. -/
def RingTerm3 : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    RingTerm3At D.Pl D.K (D.level n) (D.mu n z) C k

/-- Term 4 along the sequence. -/
def RingTerm4 : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    RingTerm4At D.Pl D.K (D.level n) (D.mu n z) C k

/-- `RingSubst` from the four term estimates. -/
theorem ringSubst_of_terms {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (h1 : D.RingTerm1) (h2 : D.RingTerm2) (h3 : D.RingTerm3) (h4 : D.RingTerm4) :
    D.RingSubst := by
  obtain ⟨C₁, k₁, e1⟩ := h1
  obtain ⟨C₂, k₂, e2⟩ := h2
  obtain ⟨C₃, k₃, e3⟩ := h3
  obtain ⟨C₄, k₄, e4⟩ := h4
  have hle := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  refine ⟨|C₁| + |C₂| + |C₃| + |C₄|, k₁ + k₂ + k₃ + k₄, ?_⟩
  filter_upwards [e1, e2, e3, e4, hle] with n a1 a2 a3 a4 hν z hz
  exact ringSubstAt_of_terms D.Pl D.K (D.level n) (D.mu n z) (a1 z hz) (a2 z hz) (a3 z hz)
    (a4 z hz) hν.1

end SeqData

end UnforcedLeray.Short.PartIIIb.Concrete
