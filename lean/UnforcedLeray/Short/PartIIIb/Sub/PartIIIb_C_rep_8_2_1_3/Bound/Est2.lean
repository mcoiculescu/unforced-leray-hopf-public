import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_3.Bound.Est1

/-!
# The four second-order entries against their leading terms
(`PartIII-b:C/rep/8/2/1/3/b`, helper 6)

Source lines 5460-5465.  For smooth `v, h` and `b = v + ε h`, with `ω = 1 + |η|`:
`‖P₂P₁ b - ∂_q∂_q v‖`, `‖P₂ ∂_η b - ∂_q∂_η v‖`, `‖∂_η P₁ b - ∂_η∂_q v‖`, `‖∂_η∂_η b - ∂_η∂_η v‖`
are bounded by `ε` times jets of `v` (order 2) and `h` (order 2), with powers of `ω`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.RingFrameD2BoundAux

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Axi

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Step bounds, `ε ∈ [0,1]`, `F` smooth. -/
theorem s_T2P1 {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {F : Zc → E} (hF : ContDiff ℝ ∞ F) (z : Zc) :
    ‖Gop 0 2 0 1 2 (Pm ε 1 F) z‖ ≤ 49 * (1 + |z.2.2|) ^ 2 * J 2 F z := by
  have a1 := norm_le_J 0 (Gop 0 2 0 1 2 (Pm ε 1 F)) z
  have a2 := J_T (m := 2) (by norm_num) (n := 0) (by norm_num) (contDiff_Pm ε 1 hF) z
  have a3 := J_Pm h0 h1 (m := 1) (by norm_num) (n := 1) (by norm_num) hF z
  have hω : 0 ≤ 1 + |z.2.2| := by positivity
  have := mul_le_mul_of_nonneg_left a3 (by positivity : (0:ℝ) ≤ 7 * (1 + |z.2.2|))
  norm_num at a2 a3 this ⊢
  nlinarith

theorem s_DqT1 {F : Zc → E} (hF : ContDiff ℝ ∞ F) (z : Zc) :
    ‖Gop 1 0 0 0 0 (Gop 0 2 0 1 1 F) z‖ ≤ 7 * (1 + |z.2.2|) * J 2 F z := by
  have a1 := norm_le_J 0 (Gop 1 0 0 0 0 (Gop 0 2 0 1 1 F)) z
  have a2 := J_Dq (n := 0) (contDiff_Gop 0 2 0 1 1 hF) z
  have a3 := J_T (m := 1) (by norm_num) (n := 1) (by norm_num) hF z
  norm_num at a2 a3 ⊢
  linarith

theorem s_P2P1 {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {F : Zc → E} (hF : ContDiff ℝ ∞ F) (z : Zc) :
    ‖Pm ε 2 (Pm ε 1 F) z‖ ≤ 49 * (1 + |z.2.2|) ^ 2 * J 2 F z := by
  have a1 := norm_le_J 0 (Pm ε 2 (Pm ε 1 F)) z
  have a2 := J_Pm h0 h1 (m := 2) (by norm_num) (n := 0) (by norm_num) (contDiff_Pm ε 1 hF) z
  have a3 := J_Pm h0 h1 (m := 1) (by norm_num) (n := 1) (by norm_num) hF z
  have hω : 0 ≤ 1 + |z.2.2| := by positivity
  have := mul_le_mul_of_nonneg_left a3 (by positivity : (0:ℝ) ≤ 7 * (1 + |z.2.2|))
  norm_num at a2 a3 this ⊢
  nlinarith

theorem s_T2Zo {F : Zc → E} (hF : ContDiff ℝ ∞ F) (z : Zc) :
    ‖Gop 0 2 0 1 2 (Zo F) z‖ ≤ 7 * (1 + |z.2.2|) * J 2 F z := by
  have a1 := norm_le_J 0 (Gop 0 2 0 1 2 (Zo F)) z
  have a2 := J_T (m := 2) (by norm_num) (n := 0) (by norm_num) (contDiff_Zo hF) z
  have a3 := J_Zo (n := 1) hF z
  have hω : 0 ≤ 1 + |z.2.2| := by positivity
  have := mul_le_mul_of_nonneg_left a3 (by positivity : (0:ℝ) ≤ 7 * (1 + |z.2.2|))
  norm_num at a2 a3 this ⊢
  nlinarith

theorem s_P2Zo {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {F : Zc → E} (hF : ContDiff ℝ ∞ F) (z : Zc) :
    ‖Pm ε 2 (Zo F) z‖ ≤ 7 * (1 + |z.2.2|) * J 2 F z := by
  have a1 := norm_le_J 0 (Pm ε 2 (Zo F)) z
  have a2 := J_Pm h0 h1 (m := 2) (by norm_num) (n := 0) (by norm_num) (contDiff_Zo hF) z
  have a3 := J_Zo (n := 1) hF z
  have hω : 0 ≤ 1 + |z.2.2| := by positivity
  have := mul_le_mul_of_nonneg_left a3 (by positivity : (0:ℝ) ≤ 7 * (1 + |z.2.2|))
  norm_num at a2 a3 this ⊢
  nlinarith

theorem s_ZoT1 {F : Zc → E} (hF : ContDiff ℝ ∞ F) (z : Zc) :
    ‖Zo (Gop 0 2 0 1 1 F) z‖ ≤ 7 * (1 + |z.2.2|) * J 2 F z := by
  have a1 := norm_le_J 0 (Zo (Gop 0 2 0 1 1 F)) z
  have a2 := J_Zo (n := 0) (contDiff_Gop 0 2 0 1 1 hF) z
  have a3 := J_T (m := 1) (by norm_num) (n := 1) (by norm_num) hF z
  norm_num at a2 a3 ⊢
  linarith

theorem s_ZoP1 {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {F : Zc → E} (hF : ContDiff ℝ ∞ F) (z : Zc) :
    ‖Zo (Pm ε 1 F) z‖ ≤ 7 * (1 + |z.2.2|) * J 2 F z := by
  have a1 := norm_le_J 0 (Zo (Pm ε 1 F)) z
  have a2 := J_Zo (n := 0) (contDiff_Pm ε 1 hF) z
  have a3 := J_Pm h0 h1 (m := 1) (by norm_num) (n := 1) (by norm_num) hF z
  norm_num at a2 a3 ⊢
  linarith

theorem s_ZoZo {F : Zc → E} (hF : ContDiff ℝ ∞ F) (z : Zc) :
    ‖Zo (Zo F) z‖ ≤ J 2 F z := by
  have a1 := norm_le_J 0 (Zo (Zo F)) z
  have a2 := J_Zo (n := 0) (contDiff_Zo hF) z
  have a3 := J_Zo (n := 1) hF z
  norm_num at a2 a3 ⊢
  linarith

/-! ### Exact identities -/

theorem key00 (ε : ℝ) {F : Zc → E} (hF : ContDiff ℝ ∞ F) (z : Zc) :
    Pm ε 2 (Pm ε 1 F) z - Gop 1 0 0 0 0 (Gop 1 0 0 0 0 F) z =
      (-ε) • Gop 0 2 0 1 2 (Pm ε 1 F) z + (-ε) • Gop 1 0 0 0 0 (Gop 0 2 0 1 1 F) z := by
  have h2 : Pm ε 2 (Pm ε 1 F) z =
      Gop 1 0 0 0 0 (Pm ε 1 F) z + (-ε) • Gop 0 2 0 1 2 (Pm ε 1 F) z :=
    congrFun (Pm_eq_fun ε 2 (Pm ε 1 F)) z
  have h3 : Gop 1 0 0 0 0 (Pm ε 1 F) z = Gop 1 0 0 0 0 (Gop 1 0 0 0 0 F) z +
      (-ε) • Gop 1 0 0 0 0 (Gop 0 2 0 1 1 F) z := by
    rw [Pm_eq_fun ε 1 F]
    exact congrFun (Gop_add_smul 1 0 0 0 0 (contDiff_Gop 1 0 0 0 0 hF)
      (contDiff_Gop 0 2 0 1 1 hF) (-ε)) z
  rw [h2, h3]
  abel

theorem key02 (ε : ℝ) {F : Zc → E} (hF : ContDiff ℝ ∞ F) (z : Zc) :
    Pm ε 2 (Zo F) z - Gop 1 0 0 0 0 (Zo F) z = (-ε) • Gop 0 2 0 1 2 (Zo F) z := by
  rw [congrFun (Pm_eq_fun ε 2 (Zo F)) z]
  abel

theorem key20 (ε : ℝ) {F : Zc → E} (hF : ContDiff ℝ ∞ F) (z : Zc) :
    Zo (Pm ε 1 F) z - Zo (Gop 1 0 0 0 0 F) z = (-ε) • Zo (Gop 0 2 0 1 1 F) z := by
  have h3 : Zo (Pm ε 1 F) z = Zo (Gop 1 0 0 0 0 F) z + (-ε) • Zo (Gop 0 2 0 1 1 F) z := by
    rw [Pm_eq_fun ε 1 F]
    exact congrFun (Zo_add_smul (-ε) (contDiff_Gop 1 0 0 0 0 hF) (contDiff_Gop 0 2 0 1 1 hF)) z
  rw [h3]
  abel

/-! ### The four entries for `b = v + ε h` -/

theorem entry00_gen {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {v h : Zc → E} (hv : ContDiff ℝ ∞ v)
    (hh : ContDiff ℝ ∞ h) (z : Zc) :
    ‖Pm ε 2 (Pm ε 1 (fun z => v z + ε • h z)) z - Gop 1 0 0 0 0 (Gop 1 0 0 0 0 v) z‖ ≤
      ε * (49 * (1 + |z.2.2|) ^ 2 + 7 * (1 + |z.2.2|)) * J 2 v z +
        ε * (49 * (1 + |z.2.2|) ^ 2) * J 2 h z := by
  have e1 := Pm_add_smul ε 1 ε hv hh
  have e2 := Pm_add_smul ε 2 ε (contDiff_Pm ε 1 hv) (contDiff_Pm ε 1 hh)
  rw [e1, e2]
  simp only []
  have k := key00 ε hv z
  have : Pm ε 2 (Pm ε 1 v) z + ε • Pm ε 2 (Pm ε 1 h) z - Gop 1 0 0 0 0 (Gop 1 0 0 0 0 v) z =
      ((-ε) • Gop 0 2 0 1 2 (Pm ε 1 v) z + (-ε) • Gop 1 0 0 0 0 (Gop 0 2 0 1 1 v) z) +
        ε • Pm ε 2 (Pm ε 1 h) z := by
    rw [← k]; abel
  rw [this]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
  simp only [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg h0]
  have t1 := s_T2P1 h0 h1 hv z
  have t2 := s_DqT1 hv z
  have t3 := s_P2P1 h0 h1 hh z
  nlinarith [mul_le_mul_of_nonneg_left t1 h0, mul_le_mul_of_nonneg_left t2 h0,
    mul_le_mul_of_nonneg_left t3 h0]

theorem entry02_gen {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {v h : Zc → E} (hv : ContDiff ℝ ∞ v)
    (hh : ContDiff ℝ ∞ h) (z : Zc) :
    ‖Pm ε 2 (Zo (fun z => v z + ε • h z)) z - Gop 1 0 0 0 0 (Zo v) z‖ ≤
      ε * (7 * (1 + |z.2.2|)) * J 2 v z + ε * (7 * (1 + |z.2.2|)) * J 2 h z := by
  have e1 := Zo_add_smul ε hv hh
  have e2 := Pm_add_smul ε 2 ε (contDiff_Zo hv) (contDiff_Zo hh)
  rw [e1, e2]
  simp only []
  have k := key02 ε hv z
  have : Pm ε 2 (Zo v) z + ε • Pm ε 2 (Zo h) z - Gop 1 0 0 0 0 (Zo v) z =
      (-ε) • Gop 0 2 0 1 2 (Zo v) z + ε • Pm ε 2 (Zo h) z := by
    rw [← k]; abel
  rw [this]
  refine (norm_add_le _ _).trans ?_
  simp only [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg h0]
  have t1 := s_T2Zo hv z
  have t3 := s_P2Zo h0 h1 hh z
  nlinarith [mul_le_mul_of_nonneg_left t1 h0, mul_le_mul_of_nonneg_left t3 h0]

theorem entry20_gen {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {v h : Zc → E} (hv : ContDiff ℝ ∞ v)
    (hh : ContDiff ℝ ∞ h) (z : Zc) :
    ‖Zo (Pm ε 1 (fun z => v z + ε • h z)) z - Zo (Gop 1 0 0 0 0 v) z‖ ≤
      ε * (7 * (1 + |z.2.2|)) * J 2 v z + ε * (7 * (1 + |z.2.2|)) * J 2 h z := by
  have e1 := Pm_add_smul ε 1 ε hv hh
  have e2 := Zo_add_smul ε (contDiff_Pm ε 1 hv) (contDiff_Pm ε 1 hh)
  rw [e1, e2]
  simp only []
  have k := key20 ε hv z
  have : Zo (Pm ε 1 v) z + ε • Zo (Pm ε 1 h) z - Zo (Gop 1 0 0 0 0 v) z =
      (-ε) • Zo (Gop 0 2 0 1 1 v) z + ε • Zo (Pm ε 1 h) z := by
    rw [← k]; abel
  rw [this]
  refine (norm_add_le _ _).trans ?_
  simp only [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg h0]
  have t1 := s_ZoT1 hv z
  have t3 := s_ZoP1 h0 h1 hh z
  nlinarith [mul_le_mul_of_nonneg_left t1 h0, mul_le_mul_of_nonneg_left t3 h0]

theorem entry22_gen {ε : ℝ} (h0 : 0 ≤ ε) {v h : Zc → E} (hv : ContDiff ℝ ∞ v)
    (hh : ContDiff ℝ ∞ h) (z : Zc) :
    ‖Zo (Zo (fun z => v z + ε • h z)) z - Zo (Zo v) z‖ ≤ ε * J 2 h z := by
  have e1 := Zo_add_smul ε hv hh
  have e2 := Zo_add_smul ε (contDiff_Zo hv) (contDiff_Zo hh)
  rw [e1, e2]
  simp only []
  have : Zo (Zo v) z + ε • Zo (Zo h) z - Zo (Zo v) z = ε • Zo (Zo h) z := by abel
  rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg h0]
  exact mul_le_mul_of_nonneg_left (s_ZoZo hh z) h0

end

end UnforcedLeray.Short.PartIIIb.Concrete.RingFrameD2BoundAux
