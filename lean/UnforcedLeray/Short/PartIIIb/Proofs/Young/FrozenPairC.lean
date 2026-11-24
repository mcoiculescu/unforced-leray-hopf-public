import UnforcedLeray.Short.PartIIIb.Concrete.YoungFlat

/-!
# Young frozen pair, concrete version (source 4407-4412)

Proves `ConcreteYF.YoungFrozenPairC` from the laws, the bounds, the hypotheses and the block
estimates. The argument: resolve the identity at `t` and at `H = Σ/ν` (`Pc` is the complement
projector), expand `𝒰(H,t)` into block entries, and bound every block by `|C| ν |F_+(H,t)|`.
The error of `eq:young-frozen-pair` is relative to `|F_+(H,t)|` at the same `t`, which is
exactly the scale of `YoungBlockEstimates`; no comparison with `|F_+(H,0)|` is used.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb

open ConcreteYF

lemma yfc_norm_smul {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (a : ℂ) (v : X) (A V : ℝ) (hA : 0 ≤ A) (ha : ‖a‖ ≤ A) (hv : ‖v‖ ≤ V) :
    ‖a • v‖ ≤ A * V := by
  rw [norm_smul]
  exact mul_le_mul ha hv (norm_nonneg _) hA

lemma yfc_pc_resolve (pk : YoungPkg) (t : ℝ) (x : pk.X) :
    x = ∑ j : Bool, (pk.ell j t x) • pk.q j t + ConcreteYF.Pc pk t x := by
  unfold ConcreteYF.Pc
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply]
  abel

/-- Abstract block estimate: the algebra of the resolution of the identity, with all
constants explicit. -/
lemma yfc_abstract {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (T : X →L[ℂ] X) (qH qt : Bool → X) (ℓH ℓt : Bool → X →L[ℂ] ℂ)
    (PH Pt : X →L[ℂ] X) (F : Bool → ℂ) (B c : ℝ) (hB : 0 ≤ B) (hc : 0 ≤ c)
    (hresH : ∀ y : X, y = ∑ i, ℓH i y • qH i + PH y)
    (hres : ∀ y : X, y = ∑ j, ℓt j y • qt j + Pt y)
    (hq : ∀ i, ‖qH i‖ ≤ B) (hℓ : ∀ j, ‖ℓt j‖ ≤ B)
    (hb1 : ∀ i j, ‖ℓH i (T (qt j)) - (if i = j then F j else 0)‖ ≤ c)
    (hb2 : ∀ j, ‖PH (T (qt j))‖ ≤ c)
    (hb3 : ∀ i y, ‖ℓH i (T (Pt y))‖ ≤ c * ‖y‖)
    (hb4 : ∀ y, ‖PH (T (Pt y))‖ ≤ c * ‖y‖) (x : X) :
    ‖T x - ∑ j, F j • (ℓt j x • qH j)‖ ≤ (4 * B ^ 2 + 4 * B + 1) * c * ‖x‖ := by
  have hx1 : T x = ∑ j, ℓt j x • T (qt j) + T (Pt x) := by
    conv_lhs => rw [hres x]
    simp [map_add, map_sum, map_smul]
  have hs : ∀ j, ∑ i, (ℓH i (T (qt j)) - (if i = j then F j else 0)) • qH i
      = ∑ i, ℓH i (T (qt j)) • qH i - F j • qH j := by
    intro j
    simp [sub_smul, Finset.sum_sub_distrib, ite_smul]
  have hu : ∀ j, T (qt j) - F j • qH j
      = ∑ i, (ℓH i (T (qt j)) - (if i = j then F j else 0)) • qH i + PH (T (qt j)) := by
    intro j
    rw [hs j]
    conv_lhs => rw [hresH (T (qt j))]
    abel
  have hA : ∀ j, ‖T (qt j) - F j • qH j‖ ≤ 2 * (c * B) + c := by
    intro j
    rw [hu j]
    refine (norm_add_le _ _).trans (add_le_add ?_ (hb2 j))
    refine (norm_sum_le _ _).trans ?_
    simp only [Fintype.sum_bool]
    have e1 := yfc_norm_smul _ (qH true) c B hc (hb1 true j) (hq true)
    have e2 := yfc_norm_smul _ (qH false) c B hc (hb1 false j) (hq false)
    linarith
  have hTP : ‖T (Pt x)‖ ≤ (2 * (c * B) + c) * ‖x‖ := by
    have hc' : 0 ≤ c * ‖x‖ := mul_nonneg hc (norm_nonneg x)
    rw [hresH (T (Pt x))]
    refine (norm_add_le _ _).trans ?_
    have hS : ‖∑ i, ℓH i (T (Pt x)) • qH i‖ ≤ 2 * (c * ‖x‖ * B) := by
      refine (norm_sum_le _ _).trans ?_
      simp only [Fintype.sum_bool]
      have e1 := yfc_norm_smul _ (qH true) (c * ‖x‖) B hc' (hb3 true x) (hq true)
      have e2 := yfc_norm_smul _ (qH false) (c * ‖x‖) B hc' (hb3 false x) (hq false)
      linarith
    have h4 := hb4 x
    linarith
  have hℓx : ∀ j, ‖ℓt j x‖ ≤ B * ‖x‖ := fun j =>
    (ContinuousLinearMap.le_opNorm (ℓt j) x).trans
      (mul_le_mul_of_nonneg_right (hℓ j) (norm_nonneg x))
  have hterm : ∀ j, ‖ℓt j x • (T (qt j) - F j • qH j)‖ ≤ (B * ‖x‖) * (2 * (c * B) + c) :=
    fun j => yfc_norm_smul _ _ _ _ (mul_nonneg hB (norm_nonneg x)) (hℓx j) (hA j)
  have hD : T x - ∑ j, F j • (ℓt j x • qH j)
      = ∑ j, ℓt j x • (T (qt j) - F j • qH j) + T (Pt x) := by
    rw [hx1]
    have hcomm : ∀ j, F j • (ℓt j x • qH j) = ℓt j x • (F j • qH j) :=
      fun j => smul_comm _ _ _
    simp only [hcomm, smul_sub, Finset.sum_sub_distrib]
    abel
  rw [hD]
  refine (norm_add_le _ _).trans ?_
  have hsum : ‖∑ j, ℓt j x • (T (qt j) - F j • qH j)‖
      ≤ 2 * ((B * ‖x‖) * (2 * (c * B) + c)) := by
    refine (norm_sum_le _ _).trans ?_
    simp only [Fintype.sum_bool]
    linarith [hterm true, hterm false]
  linarith [hTP, hsum]

/-- `eq:young-frozen-pair` (source 4407-4412), concrete version. -/
theorem youngFrozenPairC_holds (pk : ℕ → YoungPkg) (conjX : ∀ n, (pk n).X → (pk n).X)
    (ν : ℕ → ℝ) (lam κ : ℂ) (Sg α : ℝ) : ConcreteYF.YoungFrozenPairC pk conjX ν lam κ Sg α := by
  unfold ConcreteYF.YoungFrozenPairC
  intro _hL hH hB hE
  unfold YoungHyp at hH
  unfold YoungBounded at hB
  unfold YoungBlockEstimates at hE
  obtain ⟨hνpos, -, -, hα0, hαS⟩ := hH
  obtain ⟨Cb, hCb⟩ := hB
  obtain ⟨Ce, Ne, hCe⟩ := hE
  have hSg : 0 < Sg := lt_trans hα0 hαS
  have hCb0 : 0 ≤ Cb := by
    have h := (hCb 0 0 ⟨le_rfl, div_nonneg hSg.le (hνpos 0).le⟩ true).1
    exact le_trans (norm_nonneg _) h
  refine ⟨(4 * Cb ^ 2 + 4 * Cb + 1) * |Ce|, Ne, ?_⟩
  intro n hn t ht
  have hνn : 0 ≤ ν n := (hνpos n).le
  have hH0 : (0 : ℝ) ≤ Sg / ν n := div_nonneg hSg.le hνn
  have hHmem : Sg / ν n ∈ Icc (0 : ℝ) (Sg / ν n) := ⟨hH0, le_rfl⟩
  have htS : t ∈ Icc (0 : ℝ) (Sg / ν n) :=
    ⟨ht.1, ht.2.trans (div_le_div_of_nonneg_right hαS.le hνn)⟩
  obtain ⟨b1, b2, b3, b4⟩ := hCe n hn t ht
  have hF0 : 0 ≤ ‖Fpm true lam κ (ν n) (Sg / ν n) t‖ := norm_nonneg _
  have hm : Ce * ν n * ‖Fpm true lam κ (ν n) (Sg / ν n) t‖
      ≤ |Ce| * ν n * ‖Fpm true lam κ (ν n) (Sg / ν n) t‖ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self Ce) hνn) (norm_nonneg _)
  have hc0 : 0 ≤ |Ce| * ν n * ‖Fpm true lam κ (ν n) (Sg / ν n) t‖ :=
    mul_nonneg (mul_nonneg (abs_nonneg _) hνn) hF0
  have hK : 0 ≤ 4 * Cb ^ 2 + 4 * Cb + 1 := by nlinarith
  have hq : ∀ i, ‖(pk n).q i (Sg / ν n)‖ ≤ Cb := fun i => (hCb n (Sg / ν n) hHmem i).1
  have hℓ : ∀ j, ‖(pk n).ell j t‖ ≤ Cb := fun j => (hCb n t htS j).2
  have hb1 : ∀ i j, ‖(pk n).ell i (Sg / ν n) ((pk n).Uev (Sg / ν n) t ((pk n).q j t))
      - (if i = j then Fpm j lam κ (ν n) (Sg / ν n) t else 0)‖
      ≤ |Ce| * ν n * ‖Fpm true lam κ (ν n) (Sg / ν n) t‖ :=
    fun i j => (b1 i j).trans hm
  have hb2 : ∀ j, ‖ConcreteYF.Pc (pk n) (Sg / ν n) ((pk n).Uev (Sg / ν n) t ((pk n).q j t))‖
      ≤ |Ce| * ν n * ‖Fpm true lam κ (ν n) (Sg / ν n) t‖ :=
    fun j => (b2 j).trans hm
  have hb3 : ∀ i y, ‖(pk n).ell i (Sg / ν n) ((pk n).Uev (Sg / ν n) t
      (ConcreteYF.Pc (pk n) t y))‖ ≤ |Ce| * ν n * ‖Fpm true lam κ (ν n) (Sg / ν n) t‖ * ‖y‖ :=
    fun i y => (b3 i y).trans (mul_le_mul_of_nonneg_right hm (norm_nonneg y))
  have hb4 : ∀ y, ‖ConcreteYF.Pc (pk n) (Sg / ν n)
      (((pk n).Uev (Sg / ν n) t) (ConcreteYF.Pc (pk n) t y))‖
      ≤ |Ce| * ν n * ‖Fpm true lam κ (ν n) (Sg / ν n) t‖ * ‖y‖ := fun y =>
    (ContinuousLinearMap.le_opNorm
        ((ConcreteYF.Pc (pk n) (Sg / ν n)).comp (((pk n).Uev (Sg / ν n) t).comp
          (ConcreteYF.Pc (pk n) t))) y).trans
      (mul_le_mul_of_nonneg_right (b4.trans hm) (norm_nonneg y))
  have key := yfc_abstract ((pk n).Uev (Sg / ν n) t)
    (fun j => (pk n).q j (Sg / ν n)) (fun j => (pk n).q j t)
    (fun i => (pk n).ell i (Sg / ν n)) (fun j => (pk n).ell j t)
    (ConcreteYF.Pc (pk n) (Sg / ν n)) (ConcreteYF.Pc (pk n) t)
    (fun j => Fpm j lam κ (ν n) (Sg / ν n) t) Cb
    (|Ce| * ν n * ‖Fpm true lam κ (ν n) (Sg / ν n) t‖)
    hCb0 hc0 (fun y => yfc_pc_resolve (pk n) (Sg / ν n) y)
    (fun y => yfc_pc_resolve (pk n) t y) hq hℓ hb1 hb2 hb3 hb4
  have hMnn : 0 ≤ (4 * Cb ^ 2 + 4 * Cb + 1) * |Ce| * ν n
      * ‖Fpm true lam κ (ν n) (Sg / ν n) t‖ :=
    mul_nonneg (mul_nonneg (mul_nonneg hK (abs_nonneg _)) hνn) (norm_nonneg _)
  refine ContinuousLinearMap.opNorm_le_bound _ hMnn (fun x => ?_)
  have hEq : ((pk n).Uev (Sg / ν n) t - ∑ j : Bool, Fpm j lam κ (ν n) (Sg / ν n) t
      • ((pk n).ell j t).smulRight ((pk n).q j (Sg / ν n))) x
      = (pk n).Uev (Sg / ν n) t x - ∑ j : Bool, Fpm j lam κ (ν n) (Sg / ν n) t
      • ((pk n).ell j t x • (pk n).q j (Sg / ν n)) := by
    simp [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply]
  rw [hEq]
  refine le_trans (key x) (le_of_eq ?_)
  ring
