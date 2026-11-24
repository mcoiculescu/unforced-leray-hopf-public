import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.YoungW2.RawProfileSmooth

/-!
# Weighted jets of the raw profile on the young band (source 1206-1222, 5461-5464)

Source of record: `the November 2 reference manuscript` (73 pages).

Leaf of `PartIII-b:C/ward/12` (`BgRawProfileYoungJets`, `Ward/Bg/YoungW2/Defs.lean`).
From the weighted train-stream jets `BgTrainStreamYoungJets` (order `≤ 3`, weight `(1+|η|)³`), the
raw profile `rawProfile ε v ψ = (−∂_ηΨ, ∂_qΨ) + ε(Ψ − η∂_ηΨ − 2s∂_sΨ) e_z`
(`bgRawProfile_eq_on`) has order `≤ 2` with weight `(1+|η|)²`.  The work is done on the open set
`U = {s > 0}`: `fderivWithin ℝ Ψ U` is smooth with `D^l(fderivWithin Ψ U) = D^(l+1)Ψ`, the linear
pieces are bounded by composition with continuous linear maps, the products `η · ∂Ψ` and
`(2s) · ∂Ψ` by the Leibniz rule, and the `η`-weights by `|η| ≤ 1 + |η|`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace RawYoung

/-- Scalar-product weight `T ↦ (−T(0,(0,1)), T(0,(1,0)))` into the plane. -/
def rawLam : (ℝ × (ℝ × ℝ) →L[ℝ] ℝ) →L[ℝ] UnforcedLeray.Train.Vec :=
  (UnforcedLeray.Train.toVecL.toContinuousLinearMap).comp
    ((-(ContinuousLinearMap.apply ℝ ℝ ((0, (0, 1)) : ℝ × (ℝ × ℝ)))).prod
      (ContinuousLinearMap.apply ℝ ℝ ((0, (1, 0)) : ℝ × (ℝ × ℝ))))

lemma rawLam_apply (T : ℝ × (ℝ × ℝ) →L[ℝ] ℝ) :
    rawLam T = UnforcedLeray.Train.toVec (-(T (0, (0, 1))), T (0, (1, 0))) := rfl

/-- The scalar `η ∂_η Ψ`-type coefficient function `Φ` of the raw profile. -/
def Tt (Ψ : ℝ × (ℝ × ℝ) → ℝ) (U : Set (ℝ × (ℝ × ℝ))) : ℝ × (ℝ × ℝ) → ℝ :=
  fun y => y.2.2 * fderivWithin ℝ Ψ U y (0, (0, 1)) + 2 * y.1 * fderivWithin ℝ Ψ U y (1, (0, 0))

def Phi (Ψ : ℝ × (ℝ × ℝ) → ℝ) (U : Set (ℝ × (ℝ × ℝ))) : ℝ × (ℝ × ℝ) → ℝ :=
  fun y => Ψ y - Tt Ψ U y

/-- The scalar-to-plane embedding `r ↦ r • e₁`. -/
def smulE : ℝ →L[ℝ] UnforcedLeray.Train.Vec :=
  ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))

lemma smulE_apply (r : ℝ) : smulE r = r • EuclideanSpace.single (1 : Fin 2) (1 : ℝ) := by
  simp [smulE]

/-- The raw profile on `U` as a function of the stream derivative. -/
def Gfun (ε : ℝ) (Ψ : ℝ × (ℝ × ℝ) → ℝ) (U : Set (ℝ × (ℝ × ℝ))) :
    ℝ × (ℝ × ℝ) → UnforcedLeray.Train.Vec :=
  fun y => rawLam (fderivWithin ℝ Ψ U y) + smulE (ε * Phi Ψ U y)

/-- Weighted product step: `w² ‖a·b‖ ≤ K K'` from `‖a‖ ≤ K w` and `w³‖b‖ ≤ K'`. -/
lemma tb_bound {a b w K K' : ℝ} (hw : 0 ≤ w) (hb : 0 ≤ b) (hK : 0 ≤ K)
    (h1 : a ≤ K * w) (h2 : w ^ 3 * b ≤ K') : w ^ 2 * (a * b) ≤ K * K' := by
  have h3 : a * b ≤ K * w * b := mul_le_mul_of_nonneg_right h1 hb
  have h4 : w ^ 2 * (a * b) ≤ w ^ 2 * (K * w * b) :=
    mul_le_mul_of_nonneg_left h3 (sq_nonneg w)
  have h5 : w ^ 2 * (K * w * b) = K * (w ^ 3 * b) := by ring
  have h6 : K * (w ^ 3 * b) ≤ K * K' := mul_le_mul_of_nonneg_left h2 hK
  linarith

/-- Second and higher derivatives of a continuous linear functional vanish on an open set. -/
lemma iter_lin2 {L : ℝ × (ℝ × ℝ) →L[ℝ] ℝ} {s : Set (ℝ × (ℝ × ℝ))} (hs : IsOpen s)
    {x : ℝ × (ℝ × ℝ)} (hx : x ∈ s) {n : ℕ} (hn : 2 ≤ n) :
    iteratedFDerivWithin ℝ n (fun y => L y) s x = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : m ≠ 0 := by omega
  have e2 : iteratedFDerivWithin ℝ m (fderivWithin ℝ (fun y => L y) s) s x
      = iteratedFDerivWithin ℝ m (fun _ : ℝ × (ℝ × ℝ) => L) s x :=
    iteratedFDerivWithin_congr (fun y hy => L.fderivWithin (hs.uniqueDiffOn y hy)) hx m
  have h0 : iteratedFDerivWithin ℝ m (fun _ : ℝ × (ℝ × ℝ) => L) s x = 0 := by
    rw [iteratedFDerivWithin_const_of_ne hm]
    rfl
  have hn0 : ‖iteratedFDerivWithin ℝ (m + 1) (fun y => L y) s x‖ = 0 := by
    rw [← norm_iteratedFDerivWithin_fderivWithin hs.uniqueDiffOn hx, e2, h0, norm_zero]
  exact norm_eq_zero.mp hn0

/-- Bound for a continuous linear functional and its first derivative, with weight. -/
lemma coord_bound {L : ℝ × (ℝ × ℝ) →L[ℝ] ℝ} {U : Set (ℝ × (ℝ × ℝ))} (hU : IsOpen U)
    {x : ℝ × (ℝ × ℝ)} (hx : x ∈ U) {K0 w : ℝ} (hK0 : 0 ≤ K0) (hL : ‖L‖ ≤ K0) (hw : 1 ≤ w)
    (hval : |L x| ≤ K0 * w) {i : ℕ} (hi : i ≤ 2) :
    ‖iteratedFDerivWithin ℝ i (fun y => L y) U x‖ ≤ K0 * w := by
  interval_cases i
  · rw [norm_iteratedFDerivWithin_zero, Real.norm_eq_abs]
    exact hval
  · have hfd : fderivWithin ℝ (fun y => L y) U x = L := L.fderivWithin (hU.uniqueDiffOn x hx)
    rw [norm_iteratedFDerivWithin_one _ (hU.uniqueDiffOn x hx), hfd]
    exact le_trans hL (le_mul_of_one_le_right hK0 hw)
  · rw [iter_lin2 hU hx (by norm_num), norm_zero]
    exact mul_nonneg hK0 (by linarith)

def Lη : ℝ × (ℝ × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

def L1 : ℝ × (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)

def L2 : ℝ × (ℝ × ℝ) →L[ℝ] ℝ := (2 : ℝ) • L1

lemma coord_eta {U : Set (ℝ × (ℝ × ℝ))} (hU : IsOpen U) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ U, ∀ i ≤ 2,
      ‖iteratedFDerivWithin ℝ i (fun y : ℝ × (ℝ × ℝ) => y.2.2) U x‖ ≤ K * (1 + |x.2.2|) := by
  refine ⟨1 + ‖Lη‖, by positivity, fun x hx i hi => ?_⟩
  refine coord_bound (L := Lη) hU hx (by positivity) (by linarith) (by linarith [abs_nonneg x.2.2]) ?_ hi
  show |x.2.2| ≤ _
  nlinarith [abs_nonneg x.2.2, norm_nonneg Lη,
    mul_nonneg (norm_nonneg Lη) (by linarith [abs_nonneg x.2.2] : (0:ℝ) ≤ 1 + |x.2.2|)]

lemma coord_s {U : Set (ℝ × (ℝ × ℝ))} (hU : IsOpen U) (S : ℝ) (hS : 0 ≤ S)
    (hUpos : ∀ x ∈ U, 0 < x.1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ U, x.1 ≤ S → ∀ i ≤ 2,
      ‖iteratedFDerivWithin ℝ i (fun y : ℝ × (ℝ × ℝ) => 2 * y.1) U x‖ ≤ K * (1 + |x.2.2|) := by
  refine ⟨2 * S + ‖L2‖ + 1, by linarith [norm_nonneg L2], fun x hx hxS i hi => ?_⟩
  refine coord_bound (L := L2) hU hx (by linarith [norm_nonneg L2]) (by linarith)
    (by linarith [abs_nonneg x.2.2]) ?_ hi
  have h2 : L2 x = 2 * x.1 := by simp [L2, L1]
  rw [show |L2 x| = |2 * x.1| from by rw [h2], abs_of_pos (by linarith [hUpos x hx])]
  nlinarith [norm_nonneg L2, abs_nonneg x.2.2,
    mul_nonneg (by linarith [norm_nonneg L2] : (0:ℝ) ≤ 2 * S + ‖L2‖ + 1) (abs_nonneg x.2.2)]

/-- Leibniz bound for a product with weights: `w² ‖D^n (f g)‖ ≤ 4 K K'` for `n ≤ 2`. -/
lemma prod_weight {f g : ℝ × (ℝ × ℝ) → ℝ} {s : Set (ℝ × (ℝ × ℝ))} (hs : IsOpen s)
    (hf : ContDiffOn ℝ ∞ f s) (hg : ContDiffOn ℝ ∞ g s) {x : ℝ × (ℝ × ℝ)} (hx : x ∈ s)
    {w K K' : ℝ} (hw : 1 ≤ w) (hK : 0 ≤ K)
    (hfb : ∀ i ≤ 2, ‖iteratedFDerivWithin ℝ i f s x‖ ≤ K * w)
    (hgb : ∀ k ≤ 2, w ^ 3 * ‖iteratedFDerivWithin ℝ k g s x‖ ≤ K') {n : ℕ} (hn : n ≤ 2) :
    w ^ 2 * ‖iteratedFDerivWithin ℝ n (fun y => f y * g y) s x‖ ≤ 4 * (K * K') := by
  have hmul := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ) hf hg hs.uniqueDiffOn hx
    (n := n) (by simp)
  have hab : ∀ i ≤ 2, ∀ k ≤ 2, w ^ 2 * (‖iteratedFDerivWithin ℝ i f s x‖ *
      ‖iteratedFDerivWithin ℝ k g s x‖) ≤ K * K' :=
    fun i hi k hk => tb_bound (by linarith) (norm_nonneg _) hK (hfb i hi) (hgb k hk)
  have hK' : 0 ≤ K' := by
    have := hgb 0 (by norm_num)
    have h3 : (0:ℝ) ≤ w ^ 3 * ‖iteratedFDerivWithin ℝ 0 g s x‖ :=
      mul_nonneg (pow_nonneg (by linarith) 3) (norm_nonneg _)
    linarith
  have hKK : 0 ≤ K * K' := mul_nonneg hK hK'
  have hsq := mul_le_mul_of_nonneg_left hmul (sq_nonneg w)
  interval_cases n
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_self,
      Nat.cast_one, Nat.sub_self, one_mul] at hsq
    nlinarith [hab 0 (by norm_num) 0 (by norm_num)]
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_zero_right,
      Nat.choose_one_right, Nat.choose_self, Nat.cast_one, Nat.cast_ofNat, Nat.reduceSub,
      one_mul] at hsq
    nlinarith [hab 0 (by norm_num) 1 (by norm_num), hab 1 (by norm_num) 0 (by norm_num)]
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_zero_right,
      Nat.choose_one_right, Nat.choose_self, Nat.cast_one, Nat.cast_ofNat, Nat.reduceSub,
      one_mul] at hsq
    nlinarith [hab 0 (by norm_num) 2 (by norm_num), hab 1 (by norm_num) 1 (by norm_num),
      hab 2 (by norm_num) 0 (by norm_num)]

/-- Composition with a fixed continuous linear map: `w³ ‖D^k (Λ ∘ Dψ)‖ ≤ ‖Λ‖ M₀`. -/
lemma comp_bound {Ψ : ℝ × (ℝ × ℝ) → ℝ} {U : Set (ℝ × (ℝ × ℝ))} (hU : IsOpen U)
    (hΨ : ContDiffOn ℝ ∞ Ψ U) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Λ : (ℝ × (ℝ × ℝ) →L[ℝ] ℝ) →L[ℝ] F) {x : ℝ × (ℝ × ℝ)} (hx : x ∈ U) {w M₀ : ℝ} (hw : 1 ≤ w)
    (hΨb : ∀ j ≤ 3, w ^ 3 * ‖iteratedFDerivWithin ℝ j Ψ U x‖ ≤ M₀) {k : ℕ} (hk : k ≤ 2) :
    w ^ 3 * ‖iteratedFDerivWithin ℝ k (fun y => Λ (fderivWithin ℝ Ψ U y)) U x‖ ≤ ‖Λ‖ * M₀ := by
  have hD : ContDiffOn ℝ ∞ (fderivWithin ℝ Ψ U) U := hΨ.fderivWithin hU.uniqueDiffOn (by simp)
  have hD' : ContDiffWithinAt ℝ ∞ (fderivWithin ℝ Ψ U) U x := hD.contDiffWithinAt hx
  have h1 := Λ.norm_iteratedFDerivWithin_comp_left (f := fderivWithin ℝ Ψ U) (N := ∞) hD'
    hU.uniqueDiffOn hx (n := k) (by simp)
  rw [norm_iteratedFDerivWithin_fderivWithin hU.uniqueDiffOn hx] at h1
  have h2 := hΨb (k + 1) (by omega)
  have hw3 : (0:ℝ) ≤ w ^ 3 := pow_nonneg (by linarith) 3
  calc w ^ 3 * ‖iteratedFDerivWithin ℝ k (fun y => Λ (fderivWithin ℝ Ψ U y)) U x‖
      ≤ w ^ 3 * (‖Λ‖ * ‖iteratedFDerivWithin ℝ (k + 1) Ψ U x‖) :=
        mul_le_mul_of_nonneg_left h1 hw3
    _ = ‖Λ‖ * (w ^ 3 * ‖iteratedFDerivWithin ℝ (k + 1) Ψ U x‖) := by ring
    _ ≤ ‖Λ‖ * M₀ := mul_le_mul_of_nonneg_left h2 (norm_nonneg Λ)

lemma iter_add_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : ℝ × (ℝ × ℝ) → F}
    {U : Set (ℝ × (ℝ × ℝ))} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    {x : ℝ × (ℝ × ℝ)} (hx : x ∈ U) (n : ℕ) :
    ‖iteratedFDerivWithin ℝ n (fun y => f y + g y) U x‖ ≤
      ‖iteratedFDerivWithin ℝ n f U x‖ + ‖iteratedFDerivWithin ℝ n g U x‖ := by
  have hf' : ContDiffWithinAt ℝ n f U x := (hf.contDiffWithinAt hx).of_le (by simp)
  have hg' : ContDiffWithinAt ℝ n g U x := (hg.contDiffWithinAt hx).of_le (by simp)
  have e : (fun y => f y + g y) = f + g := rfl
  rw [e, iteratedFDerivWithin_add_apply hf' hg' hU.uniqueDiffOn hx]
  exact norm_add_le _ _

lemma iter_sub_le {f g : ℝ × (ℝ × ℝ) → ℝ} {U : Set (ℝ × (ℝ × ℝ))} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    {x : ℝ × (ℝ × ℝ)} (hx : x ∈ U) (n : ℕ) :
    ‖iteratedFDerivWithin ℝ n (fun y => f y - g y) U x‖ ≤
      ‖iteratedFDerivWithin ℝ n f U x‖ + ‖iteratedFDerivWithin ℝ n g U x‖ := by
  have hf' : ContDiffWithinAt ℝ n f U x := (hf.contDiffWithinAt hx).of_le (by simp)
  have hg' : ContDiffWithinAt ℝ n g U x := (hg.contDiffWithinAt hx).of_le (by simp)
  have e : (fun y => f y - g y) = f - g := rfl
  rw [e, iteratedFDerivWithin_sub_apply hf' hg' hU.uniqueDiffOn hx]
  exact norm_sub_le _ _

lemma iter_const_mul {f : ℝ × (ℝ × ℝ) → ℝ} {U : Set (ℝ × (ℝ × ℝ))} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (c : ℝ) {x : ℝ × (ℝ × ℝ)} (hx : x ∈ U) (n : ℕ) :
    ‖iteratedFDerivWithin ℝ n (fun y => c * f y) U x‖ ≤
      ‖c‖ * ‖iteratedFDerivWithin ℝ n f U x‖ := by
  have hf' : ContDiffWithinAt ℝ n f U x := (hf.contDiffWithinAt hx).of_le (by simp)
  have e : (fun y => c * f y) = c • f := by
    funext y
    simp [smul_eq_mul]
  rw [e, iteratedFDerivWithin_const_smul_apply hf' hU.uniqueDiffOn hx, norm_smul]

lemma smulE_comp_bound {c : ℝ × (ℝ × ℝ) → ℝ} {U : Set (ℝ × (ℝ × ℝ))} (hU : IsOpen U)
    (hc : ContDiffOn ℝ ∞ c U) {x : ℝ × (ℝ × ℝ)} (hx : x ∈ U) (n : ℕ) :
    ‖iteratedFDerivWithin ℝ n (fun y => smulE (c y)) U x‖ ≤
      ‖smulE‖ * ‖iteratedFDerivWithin ℝ n c U x‖ := by
  have hc' : ContDiffWithinAt ℝ n c U x := (hc.contDiffWithinAt hx).of_le (by simp)
  exact smulE.norm_iteratedFDerivWithin_comp_left hc' hU.uniqueDiffOn hx (by simp)

set_option maxHeartbeats 1000000 in
/-- Core estimate on `U = {s > 0}`: the raw profile has weighted order-`≤ 2` bounds on `s ≤ S`. -/
theorem rawYoung_core {Ψ : ℝ × (ℝ × ℝ) → ℝ} {U : Set (ℝ × (ℝ × ℝ))} (hU : IsOpen U)
    (hΨ : ContDiffOn ℝ ∞ Ψ U) (ε S M₀ : ℝ) (hS : 0 ≤ S) (hUpos : ∀ x ∈ U, 0 < x.1)
    (hΨb : ∀ x ∈ U, x.1 ≤ S → ∀ j ≤ 3, (1 + |x.2.2|) ^ 3 * ‖iteratedFDerivWithin ℝ j Ψ U x‖ ≤ M₀) :
    ∃ M : ℝ, ∀ x ∈ U, x.1 ≤ S → ∀ l ≤ 2,
      (1 + |x.2.2|) ^ 2 * ‖iteratedFDerivWithin ℝ l (Gfun ε Ψ U) U x‖ ≤ M := by
  obtain ⟨Kη, hKη0, hKη⟩ := coord_eta hU
  obtain ⟨Ks, hKs0, hKs⟩ := coord_s hU S hS hUpos
  have hD : ContDiffOn ℝ ∞ (fderivWithin ℝ Ψ U) U := hΨ.fderivWithin hU.uniqueDiffOn (by simp)
  have hva : ContDiffOn ℝ ∞ (fun y : ℝ × (ℝ × ℝ) => fderivWithin ℝ Ψ U y (0, (0, 1))) U :=
    hD.clm_apply contDiffOn_const
  have hvc : ContDiffOn ℝ ∞ (fun y : ℝ × (ℝ × ℝ) => fderivWithin ℝ Ψ U y (1, (0, 0))) U :=
    hD.clm_apply contDiffOn_const
  have hη_s : ContDiffOn ℝ ∞ (fun y : ℝ × (ℝ × ℝ) => y.2.2) U := contDiffOn_snd.snd
  have hs_s : ContDiffOn ℝ ∞ (fun y : ℝ × (ℝ × ℝ) => 2 * y.1) U :=
    contDiffOn_const.mul contDiffOn_fst
  have hTa : ContDiffOn ℝ ∞
      (fun y : ℝ × (ℝ × ℝ) => y.2.2 * fderivWithin ℝ Ψ U y (0, (0, 1))) U := hη_s.mul hva
  have hTc : ContDiffOn ℝ ∞
      (fun y : ℝ × (ℝ × ℝ) => 2 * y.1 * fderivWithin ℝ Ψ U y (1, (0, 0))) U := hs_s.mul hvc
  have hTt : ContDiffOn ℝ ∞ (Tt Ψ U) U := hTa.add hTc
  have hΦ : ContDiffOn ℝ ∞ (Phi Ψ U) U := hΨ.sub hTt
  have hP : ContDiffOn ℝ ∞ (fun y => rawLam (fderivWithin ℝ Ψ U y)) U :=
    rawLam.contDiff.comp_contDiffOn hD
  have hQ : ContDiffOn ℝ ∞ (fun y => smulE (ε * Phi Ψ U y)) U :=
    smulE.contDiff.comp_contDiffOn (contDiffOn_const.mul hΦ)
  refine ⟨‖rawLam‖ * M₀ + ‖smulE‖ * (‖ε‖ * (M₀ + 4 * (Kη * (‖ContinuousLinearMap.apply ℝ ℝ
      ((0, (0, 1)) : ℝ × (ℝ × ℝ))‖ * M₀)) + 4 * (Ks * (‖ContinuousLinearMap.apply ℝ ℝ
      ((1, (0, 0)) : ℝ × (ℝ × ℝ))‖ * M₀)))), fun x hx hxS l hl => ?_⟩
  have hx0 : 0 < x.1 := hUpos x hx
  have hw : (1 : ℝ) ≤ 1 + |x.2.2| := by linarith [abs_nonneg x.2.2]
  have hsq : (1 + |x.2.2|) ^ 2 ≤ (1 + |x.2.2|) ^ 3 := by nlinarith
  have hΨb' : ∀ j ≤ 3, (1 + |x.2.2|) ^ 3 * ‖iteratedFDerivWithin ℝ j Ψ U x‖ ≤ M₀ :=
    fun j hj => hΨb x hx hxS j hj
  have ha : ∀ k ≤ 2, (1 + |x.2.2|) ^ 3 *
      ‖iteratedFDerivWithin ℝ k (fun y => fderivWithin ℝ Ψ U y (0, (0, 1))) U x‖ ≤
        ‖ContinuousLinearMap.apply ℝ ℝ ((0, (0, 1)) : ℝ × (ℝ × ℝ))‖ * M₀ :=
    fun k hk => comp_bound hU hΨ (ContinuousLinearMap.apply ℝ ℝ ((0, (0, 1)) : ℝ × (ℝ × ℝ))) hx hw hΨb' hk
  have hc : ∀ k ≤ 2, (1 + |x.2.2|) ^ 3 *
      ‖iteratedFDerivWithin ℝ k (fun y => fderivWithin ℝ Ψ U y (1, (0, 0))) U x‖ ≤
        ‖ContinuousLinearMap.apply ℝ ℝ ((1, (0, 0)) : ℝ × (ℝ × ℝ))‖ * M₀ :=
    fun k hk => comp_bound hU hΨ (ContinuousLinearMap.apply ℝ ℝ ((1, (0, 0)) : ℝ × (ℝ × ℝ))) hx hw hΨb' hk
  have hpa : (1 + |x.2.2|) ^ 2 * ‖iteratedFDerivWithin ℝ l
      (fun y : ℝ × (ℝ × ℝ) => y.2.2 * fderivWithin ℝ Ψ U y (0, (0, 1))) U x‖ ≤
        4 * (Kη * (‖ContinuousLinearMap.apply ℝ ℝ ((0, (0, 1)) : ℝ × (ℝ × ℝ))‖ * M₀)) :=
    prod_weight hU hη_s hva hx hw hKη0 (fun i hi => hKη x hx i hi) ha hl
  have hpc : (1 + |x.2.2|) ^ 2 * ‖iteratedFDerivWithin ℝ l
      (fun y : ℝ × (ℝ × ℝ) => 2 * y.1 * fderivWithin ℝ Ψ U y (1, (0, 0))) U x‖ ≤
        4 * (Ks * (‖ContinuousLinearMap.apply ℝ ℝ ((1, (0, 0)) : ℝ × (ℝ × ℝ))‖ * M₀)) :=
    prod_weight hU hs_s hvc hx hw hKs0 (fun i hi => hKs x hx hxS i hi) hc hl
  have hΨl : (1 + |x.2.2|) ^ 2 * ‖iteratedFDerivWithin ℝ l Ψ U x‖ ≤ M₀ :=
    le_trans (mul_le_mul_of_nonneg_right hsq (norm_nonneg _)) (hΨb' l (le_trans hl (by norm_num)))
  have hsub : ‖iteratedFDerivWithin ℝ l (Phi Ψ U) U x‖ ≤
      ‖iteratedFDerivWithin ℝ l Ψ U x‖ + ‖iteratedFDerivWithin ℝ l (Tt Ψ U) U x‖ :=
    iter_sub_le hU hΨ hTt hx l
  have hadd : ‖iteratedFDerivWithin ℝ l (Tt Ψ U) U x‖ ≤
      ‖iteratedFDerivWithin ℝ l (fun y : ℝ × (ℝ × ℝ) => y.2.2 * fderivWithin ℝ Ψ U y (0, (0, 1))) U x‖ +
      ‖iteratedFDerivWithin ℝ l
        (fun y : ℝ × (ℝ × ℝ) => 2 * y.1 * fderivWithin ℝ Ψ U y (1, (0, 0))) U x‖ :=
    iter_add_le hU hTa hTc hx l
  have hΦl : (1 + |x.2.2|) ^ 2 * ‖iteratedFDerivWithin ℝ l (Phi Ψ U) U x‖ ≤
      M₀ + 4 * (Kη * (‖ContinuousLinearMap.apply ℝ ℝ ((0, (0, 1)) : ℝ × (ℝ × ℝ))‖ * M₀))
        + 4 * (Ks * (‖ContinuousLinearMap.apply ℝ ℝ ((1, (0, 0)) : ℝ × (ℝ × ℝ))‖ * M₀)) := by
    have h1 := mul_le_mul_of_nonneg_left hsub (sq_nonneg (1 + |x.2.2|))
    have h2 := mul_le_mul_of_nonneg_left hadd (sq_nonneg (1 + |x.2.2|))
    rw [mul_add] at h1
    linarith [hΨl, hpa, hpc]
  have hPl : (1 + |x.2.2|) ^ 2 *
      ‖iteratedFDerivWithin ℝ l (fun y => rawLam (fderivWithin ℝ Ψ U y)) U x‖ ≤ ‖rawLam‖ * M₀ :=
    le_trans (mul_le_mul_of_nonneg_right hsq (norm_nonneg _)) (comp_bound hU hΨ rawLam hx hw hΨb' hl)
  have hQl : (1 + |x.2.2|) ^ 2 * ‖iteratedFDerivWithin ℝ l
      (fun y => smulE (ε * Phi Ψ U y)) U x‖ ≤
      ‖smulE‖ * (‖ε‖ * ((1 + |x.2.2|) ^ 2 * ‖iteratedFDerivWithin ℝ l (Phi Ψ U) U x‖)) := by
    have h1 := smulE_comp_bound (c := fun y => ε * Phi Ψ U y) hU (contDiffOn_const.mul hΦ) hx l
    have h2 := iter_const_mul hU hΦ ε hx l
    calc (1 + |x.2.2|) ^ 2 * ‖iteratedFDerivWithin ℝ l
          (fun y => smulE (ε * Phi Ψ U y)) U x‖
        ≤ (1 + |x.2.2|) ^ 2 * (‖smulE‖ * (‖ε‖ * ‖iteratedFDerivWithin ℝ l (Phi Ψ U) U x‖)) :=
          mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _)))
            (sq_nonneg _)
      _ = ‖smulE‖ * (‖ε‖ * ((1 + |x.2.2|) ^ 2 * ‖iteratedFDerivWithin ℝ l (Phi Ψ U) U x‖)) := by
          ring
  have hG := mul_le_mul_of_nonneg_left (iter_add_le hU hP hQ hx l) (sq_nonneg (1 + |x.2.2|))
  rw [mul_add] at hG
  have hfin : ‖smulE‖ * (‖ε‖ * ((1 + |x.2.2|) ^ 2 * ‖iteratedFDerivWithin ℝ l (Phi Ψ U) U x‖))
      ≤ ‖smulE‖ * (‖ε‖ * (M₀ + 4 * (Kη * (‖ContinuousLinearMap.apply ℝ ℝ ((0, (0, 1)) : ℝ × (ℝ × ℝ))‖ * M₀))
        + 4 * (Ks * (‖ContinuousLinearMap.apply ℝ ℝ ((1, (0, 0)) : ℝ × (ℝ × ℝ))‖ * M₀)))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hΦl (norm_nonneg _)) (norm_nonneg _)
  show (1 + |x.2.2|) ^ 2 * ‖iteratedFDerivWithin ℝ l
      (fun y => rawLam (fderivWithin ℝ Ψ U y) + smulE (ε * Phi Ψ U y)) U x‖ ≤ _
  linarith [hG, hPl, hQl, hfin]

end RawYoung

open RawYoung

/-- **`BgRawProfileYoungJets`** from the weighted train-stream jets (source 1206-1222, 5461-5464). -/
theorem bgRawProfileYoungJets_of (h : BgTrainStreamYoungJets) : BgRawProfileYoungJets := by
  intro dm dp hdm
  obtain ⟨ν₀, hν₀, hM⟩ := h dm dp hdm
  refine ⟨ν₀, hν₀, fun p d hreg hν => ?_⟩
  obtain ⟨M₀, hM₀⟩ := hM p d hreg hν
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hΨ : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => p.train.ψ x.1 x.2) (Ioi 0 ×ˢ univ) :=
    hreg.train_stream_smooth
  have hUpos : ∀ x ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))), 0 < x.1 := fun x hx => hx.1
  have hΨb : ∀ x ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))), x.1 ≤ max p.ν⁻¹ 0 → ∀ j ≤ 3,
      (1 + |x.2.2|) ^ 3 *
        ‖iteratedFDerivWithin ℝ j (fun x : ℝ × (ℝ × ℝ) => p.train.ψ x.1 x.2)
          (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) x‖ ≤ M₀ := by
    intro x hx hxS j hj
    have hx0 : 0 < x.1 := hx.1
    have hle : x.1 ≤ p.ν⁻¹ := by
      rcases max_choice p.ν⁻¹ 0 with h0 | h0
      · rw [h0] at hxS
        exact hxS
      · rw [h0] at hxS
        linarith
    rw [iteratedFDerivWithin_of_isOpen j hU hx]
    exact hM₀ j hj x hx0 hle
  obtain ⟨M, hMb⟩ := rawYoung_core hU hΨ p.ε (max p.ν⁻¹ 0) M₀ (le_max_right _ _) hUpos hΨb
  refine ⟨M, fun l hl x hx0 hxle => ?_⟩
  have hxU : x ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := ⟨hx0, trivial⟩
  have hxS : x.1 ≤ max p.ν⁻¹ 0 := le_max_of_le_left hxle
  have hEq : EqOn (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ)
      (Gfun p.ε (fun x : ℝ × (ℝ × ℝ) => p.train.ψ x.1 x.2) (Ioi 0 ×ˢ univ))
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := by
    intro y hy
    rw [bgRawProfile_eq_on hreg hy]
    simp only [Gfun, Phi, Tt, rawLam_apply, smulE_apply, fderivWithin_of_isOpen hU hy]
  rw [← iteratedFDerivWithin_of_isOpen l hU hxU, iteratedFDerivWithin_congr hEq hxU l]
  exact hMb x hxU hxS l hl

end UnforcedLeray.Short.PartIIIb.Concrete

#print axioms UnforcedLeray.Short.PartIIIb.Concrete.bgRawProfileYoungJets_of
