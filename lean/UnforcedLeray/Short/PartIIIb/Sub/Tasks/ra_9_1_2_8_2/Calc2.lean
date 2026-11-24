import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_8_2.Calc

/-!
# `ringRem` pointwise bound by conormal words of order `≤ 2` (task `PartIII-b:C/asrc/ra/9/1/2/8/2`)

Source `the November 2 reference manuscript` lines 5034-5039, 4979-4980.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Words of length at most `n`. -/
def wordsLE (n : ℕ) : Finset (List (Fin 3)) :=
  (Finset.range (n + 1)).biUnion fun k => (Finset.univ : Finset (Fin k → Fin 3)).image List.ofFn

theorem mem_wordsLE {n : ℕ} {w : List (Fin 3)} : w ∈ wordsLE n ↔ w.length ≤ n := by
  unfold wordsLE
  constructor
  · intro h
    obtain ⟨k, hk, hw⟩ := Finset.mem_biUnion.1 h
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.1 hw
    have := Finset.mem_range.1 hk
    simp; omega
  · intro h
    exact Finset.mem_biUnion.2 ⟨w.length, Finset.mem_range.2 (by omega),
      Finset.mem_image.2 ⟨w.get, Finset.mem_univ _, List.ofFn_get w⟩⟩

theorem budgetWords_eq : budgetWords = wordsLE 4 := rfl

theorem wordsLE_mono {n m : ℕ} (h : n ≤ m) : wordsLE n ⊆ wordsLE m := by
  intro w hw
  rw [mem_wordsLE] at hw ⊢
  omega

/-- `Σ_{|w| ≤ n} ‖wordW w F p‖`. -/
def SW {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) (F : Chart → E) (p : Chart) : ℝ :=
  ∑ w ∈ wordsLE n, ‖wordW w F p‖

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_le_SW {n : ℕ} {w : List (Fin 3)} (h : w.length ≤ n) (F : Chart → E) (p : Chart) :
    ‖wordW w F p‖ ≤ SW n F p :=
  Finset.single_le_sum (f := fun w => ‖wordW w F p‖) (fun _ _ => norm_nonneg _)
    (mem_wordsLE.2 h)

theorem SW_nonneg (n : ℕ) (F : Chart → E) (p : Chart) : 0 ≤ SW n F p :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem eta_leib (a : Fin 3) {f : Chart → E} (hf : ContDiffOn ℝ 1 f UC) :
    ∀ p ∈ UC, opW a (fun p => p.2.2 • f p) p
      = p.2.2 • opW a f p + (if a = 2 then f p else 0) := by
  intro p hp
  have hd := diffAt_of_cd hf hp
  have hc : HasFDerivAt (fun q : Chart => q.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) p :=
    (hasFDerivAt_snd).comp p (hasFDerivAt_snd)
  have h : fderiv ℝ (fun q : Chart => q.2.2 • f q) p = p.2.2 • fderiv ℝ f p
      + (ContinuousLinearMap.snd ℝ ℝ ℝ ∘L ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).smulRight (f p) :=
    (hc.smul hd.hasFDerivAt).fderiv
  fin_cases a <;> simp [opW, UnforcedLeray.Axi.dS, UnforcedLeray.Axi.dQ, UnforcedLeray.Axi.dEta, h,
    smul_add, smul_smul, mul_comm]

/-- `𝒦 F = 2 SF + η EF`. -/
theorem Kc_eq (F : Chart → E) (p : Chart) :
    Kc F p = (2 : ℝ) • opW 0 F p + p.2.2 • opW 2 F p := by
  simp [Kc, opW, smul_smul]

theorem K1_Q_bound (F : Chart → E) (p : Chart) :
    ‖K1 (UnforcedLeray.Axi.dQ F) p‖ ≤ 4 * (1 + |p.2.2|) * SW 2 F p := by
  have e : K1 (UnforcedLeray.Axi.dQ F) p
      = (2 : ℝ) • wordW [0, 1] F p + p.2.2 • wordW [2, 1] F p + wordW [1] F p := by
    simp [K1, Kc_eq, wordW, opW]
  have h1 := norm_le_SW (n := 2) (w := [0, 1]) (by simp) F p
  have h2 := norm_le_SW (n := 2) (w := [2, 1]) (by simp) F p
  have h3 := norm_le_SW (n := 2) (w := [1]) (by simp) F p
  have hT := SW_nonneg 2 F p
  rw [e]
  calc _ ≤ ‖(2 : ℝ) • wordW [0, 1] F p‖ + ‖p.2.2 • wordW [2, 1] F p‖ + ‖wordW [1] F p‖ :=
        norm_add₃_le
    _ ≤ 2 * SW 2 F p + |p.2.2| * SW 2 F p + SW 2 F p := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_two]
        gcongr
    _ ≤ _ := by nlinarith [abs_nonneg p.2.2]

theorem K1K1_eq {F : Chart → E} (hF : ContDiffOn ℝ 2 F UC) {p : Chart} (hp : p ∈ UC) :
    K1 (K1 F) p = (4 : ℝ) • wordW [0, 0] F p + (2 * p.2.2) • wordW [0, 2] F p
      + (2 * p.2.2) • wordW [2, 0] F p + (p.2.2 * p.2.2) • wordW [2, 2] F p
      + (4 : ℝ) • wordW [0] F p + (3 * p.2.2) • wordW [2] F p + F p := by
  have c1 : ContDiffOn ℝ 1 F UC := cd_mono (by norm_num) hF
  have cS : ContDiffOn ℝ 1 (opW 0 F) UC := cd_opW 0 (n := 1) (by simpa using hF)
  have cE : ContDiffOn ℝ 1 (opW 2 F) UC := cd_opW 2 (n := 1) (by simpa using hF)
  have cEta : ContDiffOn ℝ 1 (fun p : Chart => p.2.2 • opW 2 F p) UC :=
    (contDiff_snd.comp contDiff_snd).contDiffOn.smul cE
  have e : K1 F = ((2 : ℝ) • opW 0 F + fun p : Chart => p.2.2 • opW 2 F p) + F := by
    funext q; simp [K1, Kc_eq]
  have hK : ∀ a : Fin 3, ∀ q ∈ UC, opW a (K1 F) q
      = (2 : ℝ) • opW a (opW 0 F) q + (q.2.2 • opW a (opW 2 F) q + (if a = 2 then opW 2 F q else 0))
        + opW a F q := by
    intro a q hq
    have cS2 : ContDiffOn ℝ 1 ((2 : ℝ) • opW 0 F) UC := cS.const_smul (2 : ℝ)
    have cA : ContDiffOn ℝ 1 ((2 : ℝ) • opW 0 F + fun p : Chart => p.2.2 • opW 2 F p) UC :=
      cS2.add cEta
    rw [e, opW_add a cA c1 q hq, opW_add a cS2 cEta q hq, opW_smul a 2 cS q hq,
      eta_leib a cE q hq]
  have hKc : ∀ q, K1 (K1 F) q = (2 : ℝ) • opW 0 (K1 F) q + q.2.2 • opW 2 (K1 F) q + K1 F q := by
    intro q; simp [K1, Kc_eq]
  rw [hKc, hK 0 p hp, hK 2 p hp]
  have hF' : K1 F p = (2 : ℝ) • opW 0 F p + p.2.2 • opW 2 F p + F p := by simp [K1, Kc_eq]
  rw [hF']
  simp only [wordW]
  simp
  module

theorem norm_add7_le (a b c d e f g : E) :
    ‖a + b + c + d + e + f + g‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ + ‖g‖ := by
  have h1 := norm_add_le (a + b + c + d + e + f) g
  have h2 := norm_add_le (a + b + c + d + e) f
  have h3 := norm_add_le (a + b + c + d) e
  have h4 := norm_add_le (a + b + c) d
  have h5 := norm_add_le (a + b) c
  have h6 := norm_add_le a b
  linarith

theorem K1K1_bound {F : Chart → E} (hF : ContDiffOn ℝ 2 F UC) {p : Chart} (hp : p ∈ UC) :
    ‖K1 (K1 F) p‖ ≤ 9 * (1 + |p.2.2|) ^ 2 * SW 2 F p := by
  rw [K1K1_eq hF hp]
  have b := fun (w : List (Fin 3)) (h : w.length ≤ 2) => norm_le_SW h F p
  have h00 := b [0, 0] (by simp)
  have h02 := b [0, 2] (by simp)
  have h20 := b [2, 0] (by simp)
  have h22 := b [2, 2] (by simp)
  have h0 := b [0] (by simp)
  have h2 := b [2] (by simp)
  have h := b [] (by simp)
  have hT := SW_nonneg 2 F p
  simp only [wordW] at h00 h02 h20 h22 h0 h2 h ⊢
  have hx0 : 0 ≤ |p.2.2| := abs_nonneg _
  have n1 : ∀ (c : ℝ) (v : E), ‖c • v‖ = |c| * ‖v‖ := fun c v => by rw [norm_smul, Real.norm_eq_abs]
  refine (norm_add7_le _ _ _ _ _ _ _).trans ?_
  simp only [n1, abs_mul, abs_two]
  have e4 : |(4 : ℝ)| = 4 := by norm_num
  have e3 : |(3 : ℝ)| = 3 := by norm_num
  rw [e4, e3]
  have m1 := mul_le_mul_of_nonneg_left h02 (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hx0)
  have m2 := mul_le_mul_of_nonneg_left h20 (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hx0)
  have m3 := mul_le_mul_of_nonneg_left h22 (mul_nonneg hx0 hx0)
  have m4 := mul_le_mul_of_nonneg_left h2 (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) hx0)
  have m5 := mul_le_mul_of_nonneg_left h00 (by norm_num : (0:ℝ) ≤ 4)
  have m6 := mul_le_mul_of_nonneg_left h0 (by norm_num : (0:ℝ) ≤ 4)
  nlinarith [mul_nonneg hx0 hT, mul_nonneg (mul_nonneg hx0 hx0) hT]

theorem erProj_norm_le (v : Merid) : ‖erProj v‖ ≤ ‖v‖ := by
  have : ‖erProj v‖ = |v 0| := by
    simp [erProj, EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sqrt_sq_eq_abs]
  rw [this]
  simpa using PiLp.norm_apply_le v 0

end

theorem ringRem_pt {F : Chart → Merid} (hF : ContDiffOn ℝ 2 F UC) {p : Chart} (hp : p ∈ UC)
    {ν ε : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ‖ringRem ν ε F p‖ ≤ 18 * (1 + |p.2.2|) ^ 2 * SW 2 F p := by
  have hq := K1_Q_bound F p
  have hk := K1K1_bound hF hp
  have he := erProj_norm_le (F p)
  have h0 : ‖F p‖ ≤ SW 2 F p := norm_le_SW (n := 2) (w := []) (by simp) F p
  have hT := SW_nonneg 2 F p
  have hx := abs_nonneg p.2.2
  have hx2 : 1 ≤ (1 + |p.2.2|) ^ 2 := by nlinarith
  have hTx : SW 2 F p ≤ (1 + |p.2.2|) ^ 2 * SW 2 F p := by nlinarith
  show ‖ν • ((2 : ℝ) • K1 (UnforcedLeray.Axi.dQ F) p - ε • K1 (K1 F) p + ε • erProj (F p))‖ ≤ _
  have n1 : ‖(2 : ℝ) • K1 (UnforcedLeray.Axi.dQ F) p - ε • K1 (K1 F) p + ε • erProj (F p)‖
      ≤ 2 * ‖K1 (UnforcedLeray.Axi.dQ F) p‖ + ε * ‖K1 (K1 F) p‖ + ε * ‖erProj (F p)‖ := by
    have a1 := norm_add_le ((2 : ℝ) • K1 (UnforcedLeray.Axi.dQ F) p - ε • K1 (K1 F) p) (ε • erProj (F p))
    have a2 := norm_sub_le ((2 : ℝ) • K1 (UnforcedLeray.Axi.dQ F) p) (ε • K1 (K1 F) p)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε] at a1
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_two, abs_of_pos hε] at a2
    linarith
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hν]
  have hKn := norm_nonneg (K1 (K1 F) p)
  have hQn := norm_nonneg (K1 (UnforcedLeray.Axi.dQ F) p)
  have hEn := norm_nonneg (erProj (F p))
  have c2 : ε * ‖K1 (K1 F) p‖ ≤ ‖K1 (K1 F) p‖ := by nlinarith
  have c3 : ε * ‖erProj (F p)‖ ≤ ‖F p‖ := by nlinarith
  have hs : 2 * ‖K1 (UnforcedLeray.Axi.dQ F) p‖ + ε * ‖K1 (K1 F) p‖ + ε * ‖erProj (F p)‖
      ≤ 18 * (1 + |p.2.2|) ^ 2 * SW 2 F p := by
    nlinarith [mul_nonneg hx hT, mul_nonneg (mul_nonneg hx hx) hT]
  have hs0 : 0 ≤ 2 * ‖K1 (UnforcedLeray.Axi.dQ F) p‖ + ε * ‖K1 (K1 F) p‖ + ε * ‖erProj (F p)‖ := by
    positivity
  calc ν * ‖(2 : ℝ) • K1 (UnforcedLeray.Axi.dQ F) p - ε • K1 (K1 F) p + ε • erProj (F p)‖
      ≤ 1 * (2 * ‖K1 (UnforcedLeray.Axi.dQ F) p‖ + ε * ‖K1 (K1 F) p‖ + ε * ‖erProj (F p)‖) :=
        (mul_le_mul hν1 n1 (norm_nonneg _) zero_le_one)
    _ ≤ _ := by linarith

end UnforcedLeray.Short.PartIIIb.Concrete
