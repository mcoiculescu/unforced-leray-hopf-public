import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1_4_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1_4_1.RawCalc

/-!
# `PartIII-b:C/ward/12/3/1/2/5/1/1/3/1/4/1`: `RawProfJetGen`

Source `the November 2 reference manuscript` 1206-1222 (`b_raw = (v₁, v₂ + εH)`,
`H = ψ - η∂_ηψ - 2s∂_sψ`).  Generic calculus, no train data.  On `U = {m | 0 < m.1}` the raw
profile is `v + (ε R) • e₁` with `R = F - (η · ∂_ηF + (2s) · ∂_sF)`, `F = ψ`.  The class
`GoodOn s₀ f K N` records `‖D^k f(y)‖ ≤ K (1+|η|)^N` for `k ≤ 2` and `0 < y.1 ≤ s₀` (within `U`);
it is closed under products (Leibniz, `norm_iteratedFDerivWithin_mul_le`), sums and constant
multiples, and the coordinate factors `η`, `2s` and the partial derivatives `∂_η F`, `∂_s F`
(`ContDiffOn.fderiv_of_isOpen`, `norm_iteratedFDeriv_clm_apply_const`) are inside it.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `‖D^{k+1} L‖ ≤ ‖L‖` for a continuous linear functional `L` (its derivative is the constant
map `L`, so all derivatives of order `≥ 2` vanish). -/
theorem norm_iteratedFDeriv_clm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) (k : ℕ) (y : E) :
    ‖iteratedFDeriv ℝ (k + 1) (⇑L) y‖ ≤ ‖L‖ := by
  have hfd : fderiv ℝ (⇑L) = fun _ => L := funext fun x => L.fderiv
  rw [← norm_iteratedFDeriv_fderiv, hfd]
  cases k with
  | zero => simp
  | succ k => rw [iteratedFDeriv_succ_const]; simp

/-- Bound on all derivatives of a continuous linear functional. -/
theorem norm_iteratedFDeriv_coord {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) (k : ℕ) (y : E) :
    ‖iteratedFDeriv ℝ k (⇑L) y‖ ≤ (1 + ‖L‖) * (1 + |L y|) := by
  have h0 : (0 : ℝ) ≤ ‖L‖ := norm_nonneg L
  have h1 : (0 : ℝ) ≤ |L y| := abs_nonneg _
  cases k with
  | zero =>
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    nlinarith
  | succ k =>
    have := norm_iteratedFDeriv_clm_le L k y
    nlinarith

/-- The class of functions with polynomially bounded derivatives of order `≤ 2` on
`{0 < s ≤ s₀}` (within the open set `U = {m | 0 < m.1}`). -/
def GoodOn (s0 : ℝ) (f : ℝ × (ℝ × ℝ) → ℝ) (K : ℝ) (N : ℕ) : Prop :=
  ∀ k : ℕ, k ≤ 2 → ∀ y : ℝ × (ℝ × ℝ), 0 < y.1 → y.1 ≤ s0 →
    ‖iteratedFDerivWithin ℝ k f {m : ℝ × (ℝ × ℝ) | 0 < m.1} y‖ ≤ K * (1 + |y.2.2|) ^ N

theorem isOpen_ageSet' : IsOpen {m : ℝ × (ℝ × ℝ) | 0 < m.1} :=
  isOpen_lt continuous_const continuous_fst

/-- The coordinate `η`. -/
def Lη : ℝ × (ℝ × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

/-- The coordinate `2s`. -/
def Ls : ℝ × (ℝ × ℝ) →L[ℝ] ℝ :=
  (2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)

theorem Lη_apply (x : ℝ × (ℝ × ℝ)) : Lη x = x.2.2 := rfl

theorem Ls_apply (x : ℝ × (ℝ × ℝ)) : Ls x = 2 * x.1 := by
  simp [Ls]

theorem good_eta (s0 : ℝ) : GoodOn s0 (fun x => x.2.2) (1 + ‖Lη‖) 1 := by
  intro k _ y hy0 _
  have hyU : y ∈ {m : ℝ × (ℝ × ℝ) | 0 < m.1} := hy0
  have e := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := fun x : ℝ × (ℝ × ℝ) => x.2.2) k isOpen_ageSet' hyU
  rw [e]
  have h := norm_iteratedFDeriv_coord Lη k y
  simp only [Lη_apply] at h
  rw [pow_one]
  have hh : (fun x : ℝ × (ℝ × ℝ) => x.2.2) = ⇑Lη := rfl
  rw [hh]
  have hy : |y.2.2| = |y.2.2| := rfl
  nlinarith [h, hy]

theorem good_s (s0 : ℝ) : GoodOn s0 (fun x => 2 * x.1) ((1 + ‖Ls‖) * (1 + 2 * |s0|)) 0 := by
  intro k _ y hy0 hys
  have hyU : y ∈ {m : ℝ × (ℝ × ℝ) | 0 < m.1} := hy0
  have e := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := fun x : ℝ × (ℝ × ℝ) => 2 * x.1) k isOpen_ageSet' hyU
  rw [e]
  have h := norm_iteratedFDeriv_coord Ls k y
  have hfun : (fun x : ℝ × (ℝ × ℝ) => 2 * x.1) = ⇑Ls := funext fun x => (Ls_apply x).symm
  rw [hfun]
  have hpos : |Ls y| = 2 * y.1 := by
    rw [Ls_apply, abs_of_pos (by linarith)]
  have hb : (1 + |Ls y|) ≤ 1 + 2 * |s0| := by
    rw [hpos]
    linarith [le_abs_self s0]
  rw [pow_zero, mul_one]
  have hn : (0 : ℝ) ≤ 1 + ‖Ls‖ := by positivity
  calc ‖iteratedFDeriv ℝ k (⇑Ls) y‖ ≤ (1 + ‖Ls‖) * (1 + |Ls y|) := h
    _ ≤ (1 + ‖Ls‖) * (1 + 2 * |s0|) := mul_le_mul_of_nonneg_left hb hn

/-- Partial derivative in a fixed direction is controlled by the next derivative of `F`. -/
theorem good_fderiv_dir {s0 : ℝ} {F : ℝ × (ℝ × ℝ) → ℝ} {Cψ : ℝ} {M : ℕ}
    (hF : ContDiffOn ℝ ∞ F {m : ℝ × (ℝ × ℝ) | 0 < m.1})
    (hb : ∀ l : ℕ, l ≤ 3 → ∀ y : ℝ × (ℝ × ℝ), 0 < y.1 → y.1 ≤ s0 →
      ‖iteratedFDeriv ℝ l F y‖ ≤ Cψ * (1 + |y.2.2|) ^ M) (w : ℝ × (ℝ × ℝ)) :
    GoodOn s0 (fun x => fderiv ℝ F x w) (‖w‖ * |Cψ|) M := by
  intro k hk y hy0 hys
  have hyU : y ∈ {m : ℝ × (ℝ × ℝ) | 0 < m.1} := hy0
  have e := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := fun x => fderiv ℝ F x w) k isOpen_ageSet' hyU
  rw [e]
  have hfd : ContDiffOn ℝ ∞ (fderiv ℝ F) {m : ℝ × (ℝ × ℝ) | 0 < m.1} :=
    hF.fderiv_of_isOpen isOpen_ageSet' (m := ∞) (by simp)
  have hdiff : ContDiffAt ℝ ∞ (fderiv ℝ F) y :=
    hfd.contDiffAt (isOpen_ageSet'.mem_nhds hyU)
  have h1 := norm_iteratedFDeriv_clm_apply_const (f := fderiv ℝ F) (c := w) (x := y)
    (N := ∞) (n := k) hdiff (by exact_mod_cast le_top)
  rw [norm_iteratedFDeriv_fderiv] at h1
  have hb' := hb (k + 1) (by omega) y hy0 hys
  have hpos : (0 : ℝ) ≤ (1 + |y.2.2|) ^ M := by positivity
  calc ‖iteratedFDeriv ℝ k (fun x => fderiv ℝ F x w) y‖
      ≤ ‖w‖ * ‖iteratedFDeriv ℝ (k + 1) F y‖ := h1
    _ ≤ ‖w‖ * (|Cψ| * (1 + |y.2.2|) ^ M) :=
        mul_le_mul_of_nonneg_left (hb'.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hpos))
          (norm_nonneg _)
    _ = (‖w‖ * |Cψ|) * (1 + |y.2.2|) ^ M := by ring

theorem good_F {s0 : ℝ} {F : ℝ × (ℝ × ℝ) → ℝ} {Cψ : ℝ} {M : ℕ}
    (hb : ∀ l : ℕ, l ≤ 3 → ∀ y : ℝ × (ℝ × ℝ), 0 < y.1 → y.1 ≤ s0 →
      ‖iteratedFDeriv ℝ l F y‖ ≤ Cψ * (1 + |y.2.2|) ^ M) :
    GoodOn s0 F (|Cψ|) M := by
  intro k hk y hy0 hys
  have hyU : y ∈ {m : ℝ × (ℝ × ℝ) | 0 < m.1} := hy0
  rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := F) k isOpen_ageSet' hyU]
  have hpos : (0 : ℝ) ≤ (1 + |y.2.2|) ^ M := by positivity
  exact (hb k (by omega) y hy0 hys).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hpos)

theorem good_const {s0 : ℝ} (c : ℝ) : GoodOn s0 (fun _ => c) |c| 0 := by
  intro k _ y _ _
  rcases k with _ | k
  · rw [norm_iteratedFDerivWithin_zero, pow_zero, mul_one, Real.norm_eq_abs]
  · rw [iteratedFDerivWithin_succ_const]
    simp

theorem good_mul {s0 : ℝ} {f g : ℝ × (ℝ × ℝ) → ℝ} {K1 K2 : ℝ} {N1 N2 : ℕ}
    (hf : ContDiffOn ℝ ∞ f {m : ℝ × (ℝ × ℝ) | 0 < m.1})
    (hg : ContDiffOn ℝ ∞ g {m : ℝ × (ℝ × ℝ) | 0 < m.1})
    (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2)
    (hF : GoodOn s0 f K1 N1) (hG : GoodOn s0 g K2 N2) :
    GoodOn s0 (fun x => f x * g x) (4 * K1 * K2) (N1 + N2) := by
  intro k hk y hy0 hys
  have hyU : y ∈ {m : ℝ × (ℝ × ℝ) | 0 < m.1} := hy0
  have hC := norm_iteratedFDerivWithin_mul_le (N := ∞) hf hg isOpen_ageSet'.uniqueDiffOn hyU
    (n := k) (by exact_mod_cast le_top)
  have hW : (0 : ℝ) ≤ (1 + |y.2.2|) := by positivity
  have hWN : (0 : ℝ) ≤ (1 + |y.2.2|) ^ (N1 + N2) := by positivity
  refine hC.trans ?_
  have hbound : ∀ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i f {m : ℝ × (ℝ × ℝ) | 0 < m.1} y‖ *
        ‖iteratedFDerivWithin ℝ (k - i) g {m : ℝ × (ℝ × ℝ) | 0 < m.1} y‖ ≤
      (k.choose i : ℝ) * (K1 * K2 * (1 + |y.2.2|) ^ (N1 + N2)) := by
    intro i hi
    have hi2 : i ≤ 2 := by have := Finset.mem_range.mp hi; omega
    have h1 := hF i hi2 y hy0 hys
    have h2 := hG (k - i) (by omega) y hy0 hys
    have hch : (0 : ℝ) ≤ (k.choose i : ℝ) := by positivity
    have hm := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    calc (k.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i f {m : ℝ × (ℝ × ℝ) | 0 < m.1} y‖ *
          ‖iteratedFDerivWithin ℝ (k - i) g {m : ℝ × (ℝ × ℝ) | 0 < m.1} y‖
        = (k.choose i : ℝ) * (‖iteratedFDerivWithin ℝ i f {m : ℝ × (ℝ × ℝ) | 0 < m.1} y‖ *
          ‖iteratedFDerivWithin ℝ (k - i) g {m : ℝ × (ℝ × ℝ) | 0 < m.1} y‖) := by ring
      _ ≤ (k.choose i : ℝ) * ((K1 * (1 + |y.2.2|) ^ N1) * (K2 * (1 + |y.2.2|) ^ N2)) :=
          mul_le_mul_of_nonneg_left hm hch
      _ = (k.choose i : ℝ) * (K1 * K2 * (1 + |y.2.2|) ^ (N1 + N2)) := by rw [pow_add]; ring
  refine (Finset.sum_le_sum hbound).trans ?_
  rw [← Finset.sum_mul]
  have hsum : (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)) = (2 : ℝ) ^ k := by
    exact_mod_cast Nat.sum_range_choose k
  rw [hsum]
  have h2k : (2 : ℝ) ^ k ≤ 4 := by
    interval_cases k <;> norm_num
  have hX : (0 : ℝ) ≤ K1 * K2 * (1 + |y.2.2|) ^ (N1 + N2) := by positivity
  calc (2 : ℝ) ^ k * (K1 * K2 * (1 + |y.2.2|) ^ (N1 + N2))
      ≤ 4 * (K1 * K2 * (1 + |y.2.2|) ^ (N1 + N2)) := mul_le_mul_of_nonneg_right h2k hX
    _ = 4 * K1 * K2 * (1 + |y.2.2|) ^ (N1 + N2) := by ring

theorem good_mono {s0 : ℝ} {f : ℝ × (ℝ × ℝ) → ℝ} {K : ℝ} {N N' : ℕ}
    (hK : 0 ≤ K) (hN : N ≤ N') (hf : GoodOn s0 f K N) : GoodOn s0 f K N' := by
  intro k hk y hy0 hys
  have hW : (1 : ℝ) ≤ 1 + |y.2.2| := by linarith [abs_nonneg y.2.2]
  refine (hf k hk y hy0 hys).trans ?_
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hW hN) hK

theorem good_add {s0 : ℝ} {f g : ℝ × (ℝ × ℝ) → ℝ} {K1 K2 : ℝ} {N1 N2 N : ℕ}
    (hf : ContDiffOn ℝ ∞ f {m : ℝ × (ℝ × ℝ) | 0 < m.1})
    (hg : ContDiffOn ℝ ∞ g {m : ℝ × (ℝ × ℝ) | 0 < m.1})
    (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2)
    (hF : GoodOn s0 f K1 N1) (hG : GoodOn s0 g K2 N2) (h1 : N1 ≤ N) (h2 : N2 ≤ N) :
    GoodOn s0 (fun x => f x + g x) (K1 + K2) N := by
  intro k hk y hy0 hys
  have hyU : y ∈ {m : ℝ × (ℝ × ℝ) | 0 < m.1} := hy0
  have e : (fun x => f x + g x) = f + g := rfl
  have hfw : ContDiffWithinAt ℝ (k : WithTop ℕ∞) f {m : ℝ × (ℝ × ℝ) | 0 < m.1} y :=
    (hf.contDiffWithinAt hyU).of_le (by exact_mod_cast le_top)
  have hgw : ContDiffWithinAt ℝ (k : WithTop ℕ∞) g {m : ℝ × (ℝ × ℝ) | 0 < m.1} y :=
    (hg.contDiffWithinAt hyU).of_le (by exact_mod_cast le_top)
  rw [e, iteratedFDerivWithin_add_apply hfw hgw isOpen_ageSet'.uniqueDiffOn hyU]
  have hW : (1 : ℝ) ≤ 1 + |y.2.2| := by linarith [abs_nonneg y.2.2]
  refine (norm_add_le _ _).trans ?_
  have a1 := hF k hk y hy0 hys
  have a2 := hG k hk y hy0 hys
  have b1 : K1 * (1 + |y.2.2|) ^ N1 ≤ K1 * (1 + |y.2.2|) ^ N :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hW h1) hK1
  have b2 : K2 * (1 + |y.2.2|) ^ N2 ≤ K2 * (1 + |y.2.2|) ^ N :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hW h2) hK2
  linarith

theorem good_sub {s0 : ℝ} {f g : ℝ × (ℝ × ℝ) → ℝ} {K1 K2 : ℝ} {N1 N2 N : ℕ}
    (hf : ContDiffOn ℝ ∞ f {m : ℝ × (ℝ × ℝ) | 0 < m.1})
    (hg : ContDiffOn ℝ ∞ g {m : ℝ × (ℝ × ℝ) | 0 < m.1})
    (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2)
    (hF : GoodOn s0 f K1 N1) (hG : GoodOn s0 g K2 N2) (h1 : N1 ≤ N) (h2 : N2 ≤ N) :
    GoodOn s0 (fun x => f x - g x) (K1 + K2) N := by
  intro k hk y hy0 hys
  have hyU : y ∈ {m : ℝ × (ℝ × ℝ) | 0 < m.1} := hy0
  have e : (fun x => f x - g x) = f - g := rfl
  have hfw : ContDiffWithinAt ℝ (k : WithTop ℕ∞) f {m : ℝ × (ℝ × ℝ) | 0 < m.1} y :=
    (hf.contDiffWithinAt hyU).of_le (by exact_mod_cast le_top)
  have hgw : ContDiffWithinAt ℝ (k : WithTop ℕ∞) g {m : ℝ × (ℝ × ℝ) | 0 < m.1} y :=
    (hg.contDiffWithinAt hyU).of_le (by exact_mod_cast le_top)
  rw [e, iteratedFDerivWithin_sub_apply hfw hgw isOpen_ageSet'.uniqueDiffOn hyU]
  have hW : (1 : ℝ) ≤ 1 + |y.2.2| := by linarith [abs_nonneg y.2.2]
  refine (norm_sub_le _ _).trans ?_
  have a1 := hF k hk y hy0 hys
  have a2 := hG k hk y hy0 hys
  have b1 : K1 * (1 + |y.2.2|) ^ N1 ≤ K1 * (1 + |y.2.2|) ^ N :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hW h1) hK1
  have b2 : K2 * (1 + |y.2.2|) ^ N2 ≤ K2 * (1 + |y.2.2|) ^ N :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hW h2) hK2
  linarith

/-- The constant-vector multiple of a scalar function, in the jet norm. -/
theorem norm_iter_smul_const {f : ℝ × (ℝ × ℝ) → ℝ}
    (hf : ContDiffOn ℝ ∞ f {m : ℝ × (ℝ × ℝ) | 0 < m.1})
    (c : EuclideanSpace ℝ (Fin 2)) (k : ℕ) {y : ℝ × (ℝ × ℝ)} (hy : 0 < y.1) :
    ‖iteratedFDerivWithin ℝ k (fun x => f x • c) {m : ℝ × (ℝ × ℝ) | 0 < m.1} y‖ ≤
      ‖(ContinuousLinearMap.id ℝ ℝ).smulRight c‖ *
        ‖iteratedFDerivWithin ℝ k f {m : ℝ × (ℝ × ℝ) | 0 < m.1} y‖ := by
  have hyU : y ∈ {m : ℝ × (ℝ × ℝ) | 0 < m.1} := hy
  have hfw : ContDiffWithinAt ℝ (k : WithTop ℕ∞) f {m : ℝ × (ℝ × ℝ) | 0 < m.1} y :=
    (hf.contDiffWithinAt hyU).of_le (by exact_mod_cast le_top)
  rw [iteratedFDerivWithin_smul_const_apply hfw isOpen_ageSet'.uniqueDiffOn hyU]
  exact ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _

/-- **`RawProfJetGen`** (generic calculus; SP 1206-1222). -/
theorem rawProfJetGen : RawProfJetGen := by
  intro ε v ψ s0 hv hψ hvb hψb
  obtain ⟨Cv, hCv⟩ := hvb
  obtain ⟨Cψ, M, hCψ⟩ := hψb
  have hU := isOpen_ageSet'
  have hψU : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2)
      {m : ℝ × (ℝ × ℝ) | 0 < m.1} :=
    hψ.mono (fun m hm => ⟨show (0 : ℝ) < m.1 from hm, mem_univ _⟩)
  have hvU : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => v x.1 x.2)
      {m : ℝ × (ℝ × ℝ) | 0 < m.1} :=
    hv.mono (fun m hm => ⟨le_of_lt (show (0 : ℝ) < m.1 from hm), mem_univ _⟩)
  have hη : ContDiff ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => x.2.2) := by fun_prop
  have hs2 : ContDiff ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => 2 * x.1) := by fun_prop
  -- the pieces of `R = F - (η ∂_η F + 2s ∂_s F)`
  have gF := good_F (s0 := s0) (F := fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) hCψ
  have cG1 : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) x
      (0, (0, 1))) {m : ℝ × (ℝ × ℝ) | 0 < m.1} :=
    fderiv_dir_contDiffOn hU hψU _
  have cG2 : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) x
      (1, (0, 0))) {m : ℝ × (ℝ × ℝ) | 0 < m.1} :=
    fderiv_dir_contDiffOn hU hψU _
  have gG1 := good_fderiv_dir (s0 := s0) (F := fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) hψU hCψ
    (0, (0, 1))
  have gG2 := good_fderiv_dir (s0 := s0) (F := fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) hψU hCψ
    (1, (0, 0))
  have gη := good_eta s0
  have gs := good_s s0
  have gA := good_mul (s0 := s0) (f := fun x : ℝ × (ℝ × ℝ) => x.2.2)
    (g := fun x : ℝ × (ℝ × ℝ) => fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) x (0, (0, 1)))
    hη.contDiffOn cG1 (by positivity) (by positivity) gη gG1
  have gB := good_mul (s0 := s0) (f := fun x : ℝ × (ℝ × ℝ) => 2 * x.1)
    (g := fun x : ℝ × (ℝ × ℝ) => fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) x (1, (0, 0)))
    hs2.contDiffOn cG2 (by positivity) (by positivity) gs gG2
  have cA := hη.contDiffOn.mul cG1
  have cB := hs2.contDiffOn.mul cG2
  have gAB := good_add (s0 := s0) (N := M + 1)
    (f := fun x : ℝ × (ℝ × ℝ) => x.2.2 * fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) x (0, (0, 1)))
    (g := fun x : ℝ × (ℝ × ℝ) => 2 * x.1 * fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) x (1, (0, 0)))
    cA cB (by positivity) (by positivity) gA gB (by omega) (by omega)
  have cAB := cA.add cB
  have gR := good_sub (s0 := s0) (N := M + 1)
    (f := fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2)
    (g := fun x : ℝ × (ℝ × ℝ) => x.2.2 * fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) x (0, (0, 1)) +
      2 * x.1 * fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) x (1, (0, 0)))
    hψU cAB (by positivity) (by positivity) gF gAB (by omega) (by omega)
  have cR := hψU.sub cAB
  have gc := good_const (s0 := s0) ε
  have gE := good_mul (s0 := s0) (f := fun _ : ℝ × (ℝ × ℝ) => ε)
    (g := fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2 - (x.2.2 * fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) x
      (0, (0, 1)) + 2 * x.1 * fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) x (1, (0, 0))))
    contDiffOn_const cR (by positivity) (by positivity) gc gR
  have cE := (contDiffOn_const (c := ε)).mul cR
  obtain ⟨Kε, hKε0, hKε⟩ : ∃ K : ℝ, 0 ≤ K ∧ GoodOn s0
      (fun x : ℝ × (ℝ × ℝ) => ε * (ψ x.1 x.2 - (x.2.2 * fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) x
        (0, (0, 1)) + 2 * x.1 * fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) x (1, (0, 0)))))
      K (M + 1) :=
    ⟨_, by positivity, good_mono (by positivity) (by omega) gE⟩
  refine ⟨|Cv| + ‖(ContinuousLinearMap.id ℝ ℝ).smulRight
      (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))‖ * Kε, M + 1, ?_⟩
  intro m hm0 hms l hl
  have hmU : m ∈ {m : ℝ × (ℝ × ℝ) | 0 < m.1} := hm0
  have hW : (1 : ℝ) ≤ 1 + |m.2.2| := by linarith [abs_nonneg m.2.2]
  have hW1 : (1 : ℝ) ≤ (1 + |m.2.2|) ^ (M + 1) := one_le_pow₀ hW
  have hE : iteratedFDeriv ℝ l (UnforcedLeray.Cons.C03.rawProfile ε v ψ) m =
      iteratedFDerivWithin ℝ l (UnforcedLeray.Cons.C03.rawProfile ε v ψ)
        {m : ℝ × (ℝ × ℝ) | 0 < m.1} m :=
    (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := UnforcedLeray.Cons.C03.rawProfile ε v ψ)
      l hU hmU).symm
  have hEq : iteratedFDerivWithin ℝ l (UnforcedLeray.Cons.C03.rawProfile ε v ψ)
      {m : ℝ × (ℝ × ℝ) | 0 < m.1} m =
      iteratedFDerivWithin ℝ l (fun x : ℝ × (ℝ × ℝ) => v x.1 x.2 +
        (ε * (ψ x.1 x.2 - (x.2.2 * fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) x (0, (0, 1)) +
          2 * x.1 * fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) x (1, (0, 0))))) •
          EuclideanSpace.single (1 : Fin 2) (1 : ℝ))
        {m : ℝ × (ℝ × ℝ) | 0 < m.1} m :=
    iteratedFDerivWithin_congr (fun p hp => rawProfile_eq_fderiv ε v ψ hψU hp) hmU l
  have hvw : ContDiffWithinAt ℝ (l : WithTop ℕ∞) (fun x : ℝ × (ℝ × ℝ) => v x.1 x.2)
      {m : ℝ × (ℝ × ℝ) | 0 < m.1} m :=
    (hvU.contDiffWithinAt hmU).of_le (by exact_mod_cast le_top)
  have hsw : ContDiffWithinAt ℝ (l : WithTop ℕ∞) (fun x : ℝ × (ℝ × ℝ) =>
      (ε * (ψ x.1 x.2 - (x.2.2 * fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) x (0, (0, 1)) +
        2 * x.1 * fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) x (1, (0, 0))))) •
        EuclideanSpace.single (1 : Fin 2) (1 : ℝ))
      {m : ℝ × (ℝ × ℝ) | 0 < m.1} m :=
    ((cE.smul contDiffOn_const).contDiffWithinAt hmU).of_le (by exact_mod_cast le_top)
  have hsplit : iteratedFDerivWithin ℝ l (fun x : ℝ × (ℝ × ℝ) => v x.1 x.2 +
        (ε * (ψ x.1 x.2 - (x.2.2 * fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) x (0, (0, 1)) +
          2 * x.1 * fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) x (1, (0, 0))))) •
          EuclideanSpace.single (1 : Fin 2) (1 : ℝ))
        {m : ℝ × (ℝ × ℝ) | 0 < m.1} m =
      iteratedFDerivWithin ℝ l (fun x : ℝ × (ℝ × ℝ) => v x.1 x.2)
        {m : ℝ × (ℝ × ℝ) | 0 < m.1} m +
      iteratedFDerivWithin ℝ l (fun x : ℝ × (ℝ × ℝ) =>
        (ε * (ψ x.1 x.2 - (x.2.2 * fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) x (0, (0, 1)) +
          2 * x.1 * fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) x (1, (0, 0))))) •
          EuclideanSpace.single (1 : Fin 2) (1 : ℝ))
        {m : ℝ × (ℝ × ℝ) | 0 < m.1} m := by
    have e : (fun x : ℝ × (ℝ × ℝ) => v x.1 x.2 +
        (ε * (ψ x.1 x.2 - (x.2.2 * fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) x (0, (0, 1)) +
          2 * x.1 * fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) x (1, (0, 0))))) •
          EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) =
        (fun x : ℝ × (ℝ × ℝ) => v x.1 x.2) + (fun x : ℝ × (ℝ × ℝ) =>
          (ε * (ψ x.1 x.2 - (x.2.2 * fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) x (0, (0, 1)) +
            2 * x.1 * fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) x (1, (0, 0))))) •
            EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) := rfl
    rw [e, iteratedFDerivWithin_add_apply hvw hsw isOpen_ageSet'.uniqueDiffOn hmU]
  have b1 : ‖iteratedFDerivWithin ℝ l (fun x : ℝ × (ℝ × ℝ) => v x.1 x.2)
      {m : ℝ × (ℝ × ℝ) | 0 < m.1} m‖ ≤ |Cv| * (1 + |m.2.2|) ^ (M + 1) := by
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := fun x : ℝ × (ℝ × ℝ) => v x.1 x.2) l hU hmU]
    have h0 := hCv l hl m hm0
    have hc : Cv ≤ |Cv| := le_abs_self Cv
    have hab : (0 : ℝ) ≤ |Cv| := abs_nonneg Cv
    calc ‖iteratedFDeriv ℝ l (fun x : ℝ × (ℝ × ℝ) => v x.1 x.2) m‖ ≤ Cv := h0
      _ ≤ |Cv| := hc
      _ = |Cv| * 1 := (mul_one _).symm
      _ ≤ |Cv| * (1 + |m.2.2|) ^ (M + 1) := mul_le_mul_of_nonneg_left hW1 hab
  have b2 : ‖iteratedFDerivWithin ℝ l (fun x : ℝ × (ℝ × ℝ) =>
        (ε * (ψ x.1 x.2 - (x.2.2 * fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) x (0, (0, 1)) +
          2 * x.1 * fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) x (1, (0, 0))))) •
          EuclideanSpace.single (1 : Fin 2) (1 : ℝ))
        {m : ℝ × (ℝ × ℝ) | 0 < m.1} m‖ ≤
      (‖(ContinuousLinearMap.id ℝ ℝ).smulRight
        (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))‖ * Kε) * (1 + |m.2.2|) ^ (M + 1) := by
    have h1 := norm_iter_smul_const (f := fun x : ℝ × (ℝ × ℝ) =>
        ε * (ψ x.1 x.2 - (x.2.2 * fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) x (0, (0, 1)) +
          2 * x.1 * fderiv ℝ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) x (1, (0, 0)))))
      (cE) (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) l (y := m) hm0
    have h2 := hKε l hl m hm0 hms
    have hc : (0 : ℝ) ≤ ‖(ContinuousLinearMap.id ℝ ℝ).smulRight
        (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))‖ := norm_nonneg _
    calc _ ≤ _ := h1
      _ ≤ ‖(ContinuousLinearMap.id ℝ ℝ).smulRight
          (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))‖ * (Kε * (1 + |m.2.2|) ^ (M + 1)) :=
          mul_le_mul_of_nonneg_left h2 hc
      _ = _ := by ring
  rw [hE, hEq, hsplit]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ |Cv| * (1 + |m.2.2|) ^ (M + 1) + (‖(ContinuousLinearMap.id ℝ ℝ).smulRight
          (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))‖ * Kε) * (1 + |m.2.2|) ^ (M + 1) :=
        add_le_add b1 b2
    _ = (|Cv| + ‖(ContinuousLinearMap.id ℝ ℝ).smulRight
          (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))‖ * Kε) * (1 + |m.2.2|) ^ (M + 1) := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
