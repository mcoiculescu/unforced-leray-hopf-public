import UnforcedLeray.Lib.CZCore.Gauge

/-!
# Anisotropic dyadic boxes with integer weights (INF01 T8)


target T8, and §4.9 ("integer weights make anisotropic dyadic boxes nest, side ratio
`2^{a_i}`"); decision D4 of `scoping/README.md` §3. Used by the Calderón–Zygmund decomposition
(T9) behind the `L^q` bounds of blueprint units B0414 (`paper/main.tex` lines 7336–7344) and
B0423 (lines 7447–7477).

* `dyLen k = 2^{-k}`; `dyadicBox a k m = Π_i [m_i ℓ_i, (m_i+1) ℓ_i)` with `ℓ_i = dyLen k ^ a_i`.
* `mem_dyadicBox_iff`: `x ∈ dyadicBox a k m ↔ dyIdx a k x = m`, `dyIdx a k x i = ⌊x_i / ℓ_i⌋`.
* `dyIdx_eq_of_le`, `dyadicBox_subset_of_le`: nesting across generations.
* `volume_dyadicBox`, `volume_dyadicBox_pred` (parent volume `2^{|a|}|Q|`).
* `anisoNorm_sub_dyCenter_le`, `volume_dyStar`: the closed box lies in the gauge ball of radius
  `dyLen k` about its centre; the ball of radius `2 dyLen k` has volume `2^{N+|a|} |Q|`.
* `dist_le_of_dyIdx_eq`, `finite_dyIdx_image`.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace UnforcedLeray.CZ

set_option autoImplicit false

variable {N : ℕ}

/-- The dyadic length `2^{-k}` of generation `k`. -/
def dyLen (k : ℤ) : ℝ := (2 : ℝ) ^ (-k)

theorem dyLen_pos (k : ℤ) : 0 < dyLen k := zpow_pos (by norm_num) _

theorem dyLen_sub_one (k : ℤ) : dyLen (k - 1) = 2 * dyLen k := by
  unfold dyLen
  rw [show -(k - 1) = 1 + -k by ring, zpow_add₀ two_ne_zero, zpow_one]

theorem dyLen_eq_pow_mul (k : ℤ) (d : ℕ) : dyLen k = 2 ^ d * dyLen (k + d) := by
  unfold dyLen
  rw [← zpow_natCast, ← zpow_add₀ two_ne_zero]
  congr 1; ring

theorem dyLen_le_one {k : ℤ} (hk : 0 ≤ k) : dyLen k ≤ 1 :=
  zpow_le_one_of_nonpos₀ (by norm_num) (by linarith)

theorem dyLen_neg_natCast (n : ℕ) : dyLen (-(n : ℤ)) = 2 ^ n := by
  unfold dyLen; simp

variable (a : Fin N → ℕ+)

/-- The index of the generation-`k` box containing `x`: `⌊x_i / ℓ_i⌋`, `ℓ_i = 2^{-k a_i}`. -/
def dyIdx (k : ℤ) (x : Fin N → ℝ) : Fin N → ℤ := fun i => ⌊x i / dyLen k ^ (a i : ℕ)⌋

/-- **T8 (INF01 §5).** The anisotropic dyadic box of generation `k` and index `m`:
`Π_i [m_i 2^{-k a_i}, (m_i+1) 2^{-k a_i})`. -/
def dyadicBox (k : ℤ) (m : Fin N → ℤ) : Set (Fin N → ℝ) :=
  univ.pi fun i => Ico ((m i : ℝ) * dyLen k ^ (a i : ℕ)) (((m i : ℝ) + 1) * dyLen k ^ (a i : ℕ))

/-- The closed box. -/
def dyadicBoxClosed (k : ℤ) (m : Fin N → ℤ) : Set (Fin N → ℝ) :=
  univ.pi fun i => Icc ((m i : ℝ) * dyLen k ^ (a i : ℕ)) (((m i : ℝ) + 1) * dyLen k ^ (a i : ℕ))

/-- The centre of a box. -/
def dyCenter (k : ℤ) (m : Fin N → ℤ) : Fin N → ℝ :=
  fun i => ((m i : ℝ) + 1 / 2) * dyLen k ^ (a i : ℕ)

theorem side_pos (k : ℤ) (i : Fin N) : 0 < dyLen k ^ (a i : ℕ) := pow_pos (dyLen_pos k) _

theorem mem_dyadicBox_iff {k : ℤ} {m : Fin N → ℤ} {x : Fin N → ℝ} :
    x ∈ dyadicBox a k m ↔ dyIdx a k x = m := by
  simp only [dyadicBox, mem_univ_pi, mem_Ico, funext_iff, dyIdx, Int.floor_eq_iff]
  refine forall_congr' fun i => ?_
  rw [le_div_iff₀ (side_pos a k i), div_lt_iff₀ (side_pos a k i)]

theorem mem_dyadicBox_self (k : ℤ) (x : Fin N → ℝ) : x ∈ dyadicBox a k (dyIdx a k x) :=
  (mem_dyadicBox_iff a).2 rfl

theorem measurableSet_dyadicBox (k : ℤ) (m : Fin N → ℤ) : MeasurableSet (dyadicBox a k m) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico

theorem dyadicBox_subset_closed (k : ℤ) (m : Fin N → ℤ) :
    dyadicBox a k m ⊆ dyadicBoxClosed a k m :=
  pi_mono fun _ _ => Ico_subset_Icc_self

theorem isCompact_dyadicBoxClosed (k : ℤ) (m : Fin N → ℤ) :
    IsCompact (dyadicBoxClosed a k m) :=
  isCompact_univ_pi fun _ => isCompact_Icc

/-- The lower corner lies in the box. -/
theorem corner_mem_dyadicBox (k : ℤ) (m : Fin N → ℤ) :
    (fun i => (m i : ℝ) * dyLen k ^ (a i : ℕ)) ∈ dyadicBox a k m := by
  intro i _
  exact ⟨le_rfl, by nlinarith [side_pos a k i]⟩

theorem dyadicBox_nonempty (k : ℤ) (m : Fin N → ℤ) : (dyadicBox a k m).Nonempty :=
  ⟨_, corner_mem_dyadicBox a k m⟩

/-- `|Q| = (2^{-k})^{|a|}`. -/
theorem volume_dyadicBox (k : ℤ) (m : Fin N → ℤ) :
    volume (dyadicBox a k m) = ENNReal.ofReal (dyLen k ^ homDim a) := by
  rw [dyadicBox, Real.volume_pi_Ico]
  have : ∀ i, ((m i : ℝ) + 1) * dyLen k ^ (a i : ℕ) - m i * dyLen k ^ (a i : ℕ) =
      dyLen k ^ (a i : ℕ) := fun i => by ring
  simp_rw [this]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (side_pos a k i).le),
    Finset.prod_pow_eq_pow_sum, homDim]

theorem volume_dyadicBox_pos (k : ℤ) (m : Fin N → ℤ) : volume (dyadicBox a k m) ≠ 0 := by
  rw [volume_dyadicBox]
  exact (ENNReal.ofReal_pos.2 (pow_pos (dyLen_pos k) _)).ne'

theorem volume_dyadicBox_ne_top (k : ℤ) (m : Fin N → ℤ) : volume (dyadicBox a k m) ≠ ⊤ := by
  rw [volume_dyadicBox]; exact ENNReal.ofReal_ne_top

/-- The parent generation has volume `2^{|a|}` times larger. -/
theorem volume_dyadicBox_pred (k : ℤ) (m m' : Fin N → ℤ) :
    volume (dyadicBox a (k - 1) m') = 2 ^ homDim a * volume (dyadicBox a k m) := by
  rw [volume_dyadicBox, volume_dyadicBox, dyLen_sub_one, mul_pow,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]

/-- **Nesting.** Points in one box of generation `k'` lie in one box of every generation
`k ≤ k'` (integer weights). -/
theorem dyIdx_eq_of_le {k k' : ℤ} (hk : k ≤ k') {x y : Fin N → ℝ}
    (h : dyIdx a k' x = dyIdx a k' y) : dyIdx a k x = dyIdx a k y := by
  obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 hk)
  have hk' : k' = k + d := by omega
  subst hk'
  have key : ∀ z : Fin N → ℝ, ∀ i, dyIdx a k z i =
      dyIdx a (k + d) z i / ((2 ^ (d * (a i : ℕ)) : ℕ) : ℤ) := by
    intro z i
    simp only [dyIdx]
    rw [← Int.floor_div_natCast]
    congr 1
    rw [dyLen_eq_pow_mul k d, mul_pow, ← pow_mul]
    push_cast
    ring
  funext i
  rw [key x i, key y i, h]

theorem dyadicBox_subset_of_le {k k' : ℤ} (hk : k ≤ k') {m m' : Fin N → ℤ}
    (hne : (dyadicBox a k' m' ∩ dyadicBox a k m).Nonempty) :
    dyadicBox a k' m' ⊆ dyadicBox a k m := by
  obtain ⟨x, hx1, hx2⟩ := hne
  intro z hz
  rw [mem_dyadicBox_iff] at hx1 hx2 hz ⊢
  rw [← hx2]
  exact dyIdx_eq_of_le a hk (hz.trans hx1.symm)

/-- The closed box lies in the gauge ball of radius `2^{-k}` about its centre. -/
theorem anisoNorm_sub_dyCenter_le {k : ℤ} {m : Fin N → ℤ} {y : Fin N → ℝ}
    (hy : y ∈ dyadicBoxClosed a k m) : anisoNorm a (y - dyCenter a k m) ≤ dyLen k := by
  rw [anisoNorm_le_iff_abs a (dyLen_pos k).le]
  intro i
  have h := hy i (mem_univ i)
  have hs := side_pos a k i
  simp only [dyCenter, Pi.sub_apply]
  rw [abs_le]
  constructor <;> nlinarith [h.1, h.2]

theorem measurableSet_dyStar (k : ℤ) (m : Fin N → ℤ) :
    MeasurableSet {x : Fin N → ℝ | anisoNorm a (x - dyCenter a k m) ≤ 2 * dyLen k} :=
  measurableSet_anisoClosedBall_sub a _ _

/-- The expanded set `Q* = {ρ(· - c_Q) ≤ 2·2^{-k}}` has volume `2^{N+|a|} |Q|`. -/
theorem volume_dyStar (k : ℤ) (m : Fin N → ℤ) :
    volume {x : Fin N → ℝ | anisoNorm a (x - dyCenter a k m) ≤ 2 * dyLen k} =
      2 ^ (N + homDim a) * volume (dyadicBox a k m) := by
  have h0 : (0 : ℝ) ≤ 2 * dyLen k := by have := dyLen_pos k; positivity
  rw [volume_anisoClosedBall_sub a _ h0, volume_dyadicBox, mul_pow, ← mul_assoc, ← pow_add,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]

/-- Two points of one box of generation `k ≥ 0` are within `2^{-k}` (sup distance). -/
theorem dist_le_of_dyIdx_eq {k : ℤ} (hk : 0 ≤ k) {x y : Fin N → ℝ}
    (h : dyIdx a k x = dyIdx a k y) : dist x y ≤ dyLen k := by
  have hx := mem_dyadicBox_self a k x
  have hy : y ∈ dyadicBox a k (dyIdx a k x) := by rw [h]; exact mem_dyadicBox_self a k y
  rw [dist_pi_le_iff (dyLen_pos k).le]
  intro i
  have h1 := hx i (mem_univ i)
  have h2 := hy i (mem_univ i)
  have hs : dyLen k ^ (a i : ℕ) ≤ dyLen k :=
    pow_le_of_le_one (dyLen_pos k).le (dyLen_le_one hk) (a i).ne_zero
  rw [Real.dist_eq, abs_le]
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

/-- A bounded set meets only finitely many boxes of a given generation. -/
theorem finite_dyIdx_image (k : ℤ) {S : Set (Fin N → ℝ)} {R : ℝ}
    (hS : S ⊆ Metric.closedBall 0 R) : (dyIdx a k '' S).Finite := by
  refine (Set.finite_Icc (fun i => ⌊-R / dyLen k ^ (a i : ℕ)⌋)
    (fun i => ⌊R / dyLen k ^ (a i : ℕ)⌋)).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  have hxR : ∀ i, |x i| ≤ R := fun i => by
    have h1 := norm_le_pi_norm x i
    have h2 : ‖x‖ ≤ R := by simpa using hS hx
    rw [Real.norm_eq_abs] at h1
    linarith
  refine ⟨fun i => ?_, fun i => ?_⟩
  · exact Int.floor_mono (div_le_div_of_nonneg_right
      (by linarith [neg_abs_le (x i), hxR i]) (side_pos a k i).le)
  · exact Int.floor_mono (div_le_div_of_nonneg_right
      (by linarith [le_abs_self (x i), hxR i]) (side_pos a k i).le)

end UnforcedLeray.CZ
