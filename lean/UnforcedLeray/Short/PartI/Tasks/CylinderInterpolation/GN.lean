import UnforcedLeray.Short.PartI.Sub.T07
import UnforcedLeray.Short.PartI.Tasks.CylinderInterpolation.LogConvexChain
import UnforcedLeray.Short.PartI.Tasks.CylinderInterpolation.MixedGN
import UnforcedLeray.Short.PartI.Tasks.CylinderInterpolation.JetWord
import UnforcedLeray.Short.PartI.Tasks.CylinderInterpolation.DerivFinite

/-!
# Part I, task `PartI:T07`, target `cylGN_proof`: the period-independent Gagliardo-Nirenberg chain

Source of record: `the November 2 reference manuscript`, lines 355-357 ("its
constants are independent of the period: integration by parts gives
`‖D^l f‖_{2m/l} ≤ C_m ‖f‖_∞^{1-l/m} ‖D^m f‖_2^{l/m}`"). The Prop is `CylGN` in `Sub/T07.lean`.

Proof. Fix `m ≥ 1`, `c ≥ 1` and `f`; write `μ = Cyl.cellμ c`, `p_j = 2m/j` for `j ≥ 1` and `p_0 = ∞`,
and let `a_j` be the largest `L^{p_j}(μ)` norm of a derivative word of length `j`.

1. Mixed step (`CylMixedGN` with `r = p_j`, `s = p_{j-1}`, `t = p_{j+1}`, which satisfy
   `s⁻¹ + t⁻¹ = 2 r⁻¹`): `a_j² ≤ (p_j - 1) a_{j-1} a_{j+1} ≤ 2m a_{j-1} a_{j+1}`.
2. Log-convex chain (`LogConvexChain` with `K = 2m`): `a_l ≤ K^{l(m-l)/2} a_0^{1-l/m} a_m^{l/m}`.
3. Jets (`CylJetWord`, `CylDerivFinite`): `‖D^l f‖_{p_l} ≤ 2^m a_l`, `a_0 ≤ ‖f‖_∞`, `a_m ≤ ‖D^m f‖_2`.

The constant `C_m = 2^m (2m)^{m²}` depends only on `m`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-! ### Words, exponents and elementary facts -/

theorem cgn_mem_wordsOfLength {j : ℕ} {w : List Bool} :
    w ∈ wordsOfLength j ↔ w.length = j := by
  unfold wordsOfLength
  constructor
  · intro h
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 h
    exact List.length_ofFn
  · intro h
    subst h
    exact Finset.mem_image.2 ⟨w.get, Finset.mem_univ _, List.ofFn_get w⟩

theorem cgn_nonempty_wordsOfLength (j : ℕ) : (wordsOfLength j).Nonempty :=
  ⟨List.replicate j true, cgn_mem_wordsOfLength.2 (by simp)⟩

theorem cgn_eq_nil_of_mem {w : List Bool} (h : w ∈ wordsOfLength 0) : w = [] :=
  List.eq_nil_of_length_eq_zero (cgn_mem_wordsOfLength.1 h)

theorem cgn_card_wordsOfLength (l : ℕ) : (wordsOfLength l).card ≤ 2 ^ l := by
  unfold wordsOfLength
  exact Finset.card_image_le.trans (by simp)

theorem cgn_dw_one (v : Bool) (w : List Bool) (g : Cyl.Plane → ℝ) :
    B0151.derivWord [v] (B0151.derivWord w g) = B0151.derivWord (v :: w) g := by
  cases v <;> rfl

theorem cgn_dw_two (v : Bool) (w : List Bool) (g : Cyl.Plane → ℝ) :
    B0151.derivWord [v, v] (B0151.derivWord w g) = B0151.derivWord (v :: v :: w) g := by
  cases v <;> rfl

/-- The exponent `p_j = 2m/j` for `j ≥ 1`, and `p_0 = ∞`. -/
def cgnP (m j : ℕ) : ℝ≥0∞ :=
  if j = 0 then ⊤ else ENNReal.ofReal (2 * (m : ℝ) / (j : ℝ))

/-- `a_j`: the largest `L^{p_j}(μ)` norm of a derivative word of length `j`. -/
def cgnN (m j : ℕ) (μ : Measure Cyl.Plane) (f : Cyl.Plane → ℝ) : ℝ≥0∞ :=
  (wordsOfLength j).sup (fun w => eLpNorm (B0151.derivWord w f) (cgnP m j) μ)

theorem cgnP_zero (m : ℕ) : cgnP m 0 = ⊤ := by
  simp [cgnP]

theorem cgnP_of_ne (m : ℕ) {j : ℕ} (hj : j ≠ 0) :
    cgnP m j = ENNReal.ofReal (2 * (m : ℝ) / (j : ℝ)) := by
  simp [cgnP, hj]

theorem cgnP_inv (m : ℕ) (hm : 0 < m) (k : ℕ) :
    (cgnP m k)⁻¹ = ENNReal.ofReal ((k : ℝ) / (2 * (m : ℝ))) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [cgnP_zero]
  · have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hpos : (0 : ℝ) < 2 * (m : ℝ) / (k : ℝ) := div_pos (by linarith) hk'
    rw [cgnP_of_ne m hk.ne', ← ENNReal.ofReal_inv_of_pos hpos, inv_div]

theorem cgn_two_le (m k : ℕ) (hk : k ≠ 0) (hkm : k ≤ m) : (2 : ℝ≥0∞) ≤ cgnP m k := by
  rw [cgnP_of_ne m hk]
  have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hkm' : (k : ℝ) ≤ m := by exact_mod_cast hkm
  have h2k : (2 : ℝ) ≤ 2 * (m : ℝ) / (k : ℝ) := by
    rw [le_div_iff₀ hkpos]
    linarith
  calc (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
    _ ≤ ENNReal.ofReal (2 * (m : ℝ) / (k : ℝ)) := ENNReal.ofReal_le_ofReal h2k

theorem cgnP_le_pred (m i : ℕ) : cgnP m (i + 1) ≤ cgnP m i := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [cgnP_zero]
    exact le_top
  · have hi' : (0 : ℝ) < i := by exact_mod_cast hi
    rw [cgnP_of_ne m (by omega : i + 1 ≠ 0), cgnP_of_ne m hi.ne']
    apply ENNReal.ofReal_le_ofReal
    push_cast
    gcongr
    linarith

theorem cgn_eLpNorm_top_le (g : Cyl.Plane → ℝ) (μ : Measure Cyl.Plane) :
    eLpNorm g ⊤ μ ≤ ⨆ z, ‖g z‖ₑ := by
  rw [eLpNorm_exponent_top]
  exact eLpNormEssSup_le_of_ae_enorm_bound
    (Filter.Eventually.of_forall fun x => le_iSup (fun z => ‖g z‖ₑ) x)

/-- The real-variable finish: from `a_l ≤ K^e a_0^x a_m^y` (in `ℝ`) and finiteness, the
extended-real bound with the sup `G` of `f` and the cell norm `H` of `D^m f`. -/
theorem cgn_final_bound (K e x y : ℝ) (hK : 0 ≤ K) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (N0 Nm Nl G H : ℝ≥0∞) (hN0 : N0 ≠ ⊤) (hNm : Nm ≠ ⊤) (hNl : Nl ≠ ⊤)
    (h0 : N0 ≤ G) (hmH : Nm ≤ H)
    (hl : Nl.toReal ≤ K ^ e * N0.toReal ^ x * Nm.toReal ^ y) :
    Nl ≤ ENNReal.ofReal (K ^ e) * G ^ x * H ^ y := by
  have ha0 : 0 ≤ N0.toReal := ENNReal.toReal_nonneg
  have ham : 0 ≤ Nm.toReal := ENNReal.toReal_nonneg
  have hp1 : 0 ≤ K ^ e * N0.toReal ^ x :=
    mul_nonneg (Real.rpow_nonneg hK e) (Real.rpow_nonneg ha0 x)
  calc Nl = ENNReal.ofReal Nl.toReal := (ENNReal.ofReal_toReal hNl).symm
    _ ≤ ENNReal.ofReal (K ^ e * N0.toReal ^ x * Nm.toReal ^ y) := ENNReal.ofReal_le_ofReal hl
    _ = ENNReal.ofReal (K ^ e) * N0 ^ x * Nm ^ y := by
        rw [ENNReal.ofReal_mul hp1, ENNReal.ofReal_mul (Real.rpow_nonneg hK e),
          ← ENNReal.ofReal_rpow_of_nonneg ha0 hx, ← ENNReal.ofReal_rpow_of_nonneg ham hy,
          ENNReal.ofReal_toReal hN0, ENNReal.ofReal_toReal hNm]
    _ ≤ ENNReal.ofReal (K ^ e) * G ^ x * H ^ y :=
        mul_le_mul' (mul_le_mul_right (ENNReal.rpow_le_rpow h0 hx) _)
          (ENNReal.rpow_le_rpow hmH hy)

/-! ### The target -/

theorem cylGN_proof : UnforcedLeray.Short.PartI.CylGN := by
  unfold UnforcedLeray.Short.PartI.CylGN
  intro m hm
  have hm0 : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hK1 : (1 : ℝ) ≤ 2 * (m : ℝ) := by linarith
  have hK0 : (0 : ℝ) ≤ 2 * (m : ℝ) := by linarith
  refine ⟨2 ^ m * (2 * (m : ℝ)) ^ ((m : ℝ) * (m : ℝ)), by positivity, ?_⟩
  intro c hc f hf hper hL l hl1 hlm
  have hc0 : 0 < c := by linarith
  have hl0 : l ≠ 0 := by omega
  have hlmR : (l : ℝ) ≤ m := by exact_mod_cast hlm
  have hfB : B0151.IsPeriodicQ c f := fun q η => hper (q, η)
  have hgP : ∀ w : List Bool, Cyl.IsPeriodic c (B0151.derivWord w f) :=
    fun w z => B0151.periodic_derivWord hfB w z.1 z.2
  -- the compiled inputs `CylDerivFinite`, `CylMixedGN`, `LogConvexChain`, `CylJetWord`
  have hD : ∀ w : List Bool, (⨆ z, ‖B0151.derivWord w f z‖ₑ) ≠ ⊤ ∧
      ∀ p : ℝ≥0∞, 2 ≤ p → MemLp (B0151.derivWord w f) p (Cyl.cellμ c) := by
    have h := cylDerivFinite_proof
    unfold CylDerivFinite at h
    exact fun w => h c hc f hf hper hL w
  have hMix := cylMixedGN_proof
  unfold CylMixedGN at hMix
  have hLCC := logConvexChain_proof
  unfold LogConvexChain at hLCC
  have hJ := cylJetWord_proof
  unfold CylJetWord at hJ
  -- memberships `D_w f ∈ L^{p_k}` for `k ≤ m`
  have hMem : ∀ (w : List Bool) (k : ℕ), k ≤ m →
      MemLp (B0151.derivWord w f) (cgnP m k) (Cyl.cellμ c) := by
    intro w k hk
    by_cases hk0 : k = 0
    · subst hk0
      rw [cgnP_zero]
      refine ⟨(B0151.contDiff_derivWord hf w).continuous.aestronglyMeasurable, ?_⟩
      exact lt_of_le_of_lt (cgn_eLpNorm_top_le _ _) (lt_top_iff_ne_top.2 (hD w).1)
    · exact (hD w).2 _ (cgn_two_le m k hk0 hk)
  have hNtop : ∀ k, k ≤ m → cgnN m k (Cyl.cellμ c) f ≠ ⊤ := by
    intro k hk
    unfold cgnN
    exact ((Finset.sup_lt_iff (by simp : (⊥ : ℝ≥0∞) < ⊤)).2
      (fun w _ => (hMem w k hk).eLpNorm_lt_top)).ne
  -- the mixed step for a word `v :: w` of length `i + 1`
  have hstep : ∀ (i : ℕ) (v : Bool) (w : List Bool), i + 2 ≤ m → w.length = i →
      eLpNorm (B0151.derivWord (v :: w) f) (cgnP m (i + 1)) (Cyl.cellμ c) ^ 2 ≤
        ENNReal.ofReal (2 * (m : ℝ)) *
          (eLpNorm (B0151.derivWord w f) (cgnP m i) (Cyl.cellμ c) *
            eLpNorm (B0151.derivWord (v :: v :: w) f) (cgnP m (i + 2)) (Cyl.cellμ c)) := by
    intro i v w him hw
    have hi1 : i + 1 ≠ 0 := by omega
    have hr_ne : cgnP m (i + 1) ≠ ⊤ := by
      rw [cgnP_of_ne m hi1]
      exact ENNReal.ofReal_ne_top
    have hr2 : (2 : ℝ≥0∞) ≤ cgnP m (i + 1) := cgn_two_le m (i + 1) hi1 (by omega)
    have hrs : cgnP m (i + 1) ≤ cgnP m i := cgnP_le_pred m i
    have hexp : (cgnP m i)⁻¹ + (cgnP m (i + 2))⁻¹ = 2 * (cgnP m (i + 1))⁻¹ := by
      rw [cgnP_inv m hm0 i, cgnP_inv m hm0 (i + 2), cgnP_inv m hm0 (i + 1)]
      have h1 : (0 : ℝ) ≤ (i : ℝ) / (2 * (m : ℝ)) := by positivity
      have h2 : (0 : ℝ) ≤ ((i + 2 : ℕ) : ℝ) / (2 * (m : ℝ)) := by positivity
      rw [← ENNReal.ofReal_add h1 h2, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
        ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num)]
      congr 1
      push_cast
      ring
    have hu : ContDiff ℝ ∞ (B0151.derivWord w f) := B0151.contDiff_derivWord hf w
    have hm1 : MemLp (B0151.derivWord [v] (B0151.derivWord w f)) (cgnP m (i + 1))
        (Cyl.cellμ c) := by
      rw [cgn_dw_one]
      exact hMem (v :: w) (i + 1) (by omega)
    have hm2 : MemLp (B0151.derivWord [v, v] (B0151.derivWord w f)) (cgnP m (i + 2))
        (Cyl.cellμ c) := by
      rw [cgn_dw_two]
      exact hMem (v :: v :: w) (i + 2) (by omega)
    have hmix := hMix c hc0 (B0151.derivWord w f) hu (hgP w) v (cgnP m (i + 1)) (cgnP m i)
      (cgnP m (i + 2)) hr_ne hr2 hrs hexp (hMem w i (by omega)) hm1 hm2
    rw [cgn_dw_one, cgn_dw_two] at hmix
    have htoR : (cgnP m (i + 1)).toReal ≤ 2 * (m : ℝ) := by
      rw [cgnP_of_ne m hi1, ENNReal.toReal_ofReal
        (show (0 : ℝ) ≤ 2 * (m : ℝ) / ((i + 1 : ℕ) : ℝ) by positivity)]
      refine div_le_self ?_ ?_
      · positivity
      · push_cast
        have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
        linarith
    have hrr : ENNReal.ofReal ((cgnP m (i + 1)).toReal - 1) ≤ ENNReal.ofReal (2 * (m : ℝ)) :=
      ENNReal.ofReal_le_ofReal (by linarith)
    exact hmix.trans (mul_le_mul_left hrr _)
  -- the maximal word of length `i + 1`
  have hsup : ∀ i, i + 2 ≤ m → cgnN m (i + 1) (Cyl.cellμ c) f ^ 2 ≤
      ENNReal.ofReal (2 * (m : ℝ)) *
        (cgnN m i (Cyl.cellμ c) f * cgnN m (i + 2) (Cyl.cellμ c) f) := by
    intro i him
    obtain ⟨w0, hw0, hmax⟩ := Finset.exists_mem_eq_sup (wordsOfLength (i + 1))
      (cgn_nonempty_wordsOfLength (i + 1))
      (fun w => eLpNorm (B0151.derivWord w f) (cgnP m (i + 1)) (Cyl.cellμ c))
    obtain ⟨v, w, rfl⟩ : ∃ v w, w0 = v :: w := by
      cases w0 with
      | nil => exact absurd (cgn_mem_wordsOfLength.1 hw0) (by simp)
      | cons v w => exact ⟨v, w, rfl⟩
    have hlen : w.length = i := by
      have h := cgn_mem_wordsOfLength.1 hw0
      simpa using h
    have hN : cgnN m (i + 1) (Cyl.cellμ c) f =
        eLpNorm (B0151.derivWord (v :: w) f) (cgnP m (i + 1)) (Cyl.cellμ c) := hmax
    have hA : eLpNorm (B0151.derivWord w f) (cgnP m i) (Cyl.cellμ c) ≤
        cgnN m i (Cyl.cellμ c) f :=
      Finset.le_sup (f := fun w => eLpNorm (B0151.derivWord w f) (cgnP m i) (Cyl.cellμ c))
        (cgn_mem_wordsOfLength.2 hlen)
    have hB : eLpNorm (B0151.derivWord (v :: v :: w) f) (cgnP m (i + 2)) (Cyl.cellμ c) ≤
        cgnN m (i + 2) (Cyl.cellμ c) f :=
      Finset.le_sup (f := fun w => eLpNorm (B0151.derivWord w f) (cgnP m (i + 2)) (Cyl.cellμ c))
        (cgn_mem_wordsOfLength.2 (by simp [hlen]))
    rw [hN]
    exact (hstep i v w him hlen).trans (mul_le_mul_right (mul_le_mul' hA hB) _)
  -- the real-variable chain
  have key : ∀ i, i + 2 ≤ m → (cgnN m (i + 1) (Cyl.cellμ c) f).toReal ^ 2 ≤
      2 * (m : ℝ) * ((cgnN m i (Cyl.cellμ c) f).toReal *
        (cgnN m (i + 2) (Cyl.cellμ c) f).toReal) := by
    intro i him
    have hA : cgnN m (i + 1) (Cyl.cellμ c) f ^ 2 ≠ ⊤ :=
      ENNReal.pow_ne_top (hNtop (i + 1) (by omega))
    have hB : ENNReal.ofReal (2 * (m : ℝ)) *
        (cgnN m i (Cyl.cellμ c) f * cgnN m (i + 2) (Cyl.cellμ c) f) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top (hNtop i (by omega)) (hNtop (i + 2) him))
    have h' := (ENNReal.toReal_le_toReal hA hB).2 (hsup i him)
    rw [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (show (0 : ℝ) ≤ 2 * (m : ℝ) by positivity)] at h'
    exact h'
  have hconv : ∀ j, 1 ≤ j → j < m →
      (fun j => (cgnN m j (Cyl.cellμ c) f).toReal) j ^ 2 ≤
        2 * (m : ℝ) * ((fun j => (cgnN m j (Cyl.cellμ c) f).toReal) (j - 1) *
          (fun j => (cgnN m j (Cyl.cellμ c) f).toReal) (j + 1)) := by
    intro j hj1 hjm
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    exact key i (by omega)
  have hnn : ∀ j, 0 ≤ (fun j => (cgnN m j (Cyl.cellμ c) f).toReal) j :=
    fun j => ENNReal.toReal_nonneg
  have hchain : ∀ l, l ≤ m → (cgnN m l (Cyl.cellμ c) f).toReal ≤
      (2 * (m : ℝ)) ^ ((l : ℝ) * ((m : ℝ) - l) / 2) *
        (cgnN m 0 (Cyl.cellμ c) f).toReal ^ (1 - (l : ℝ) / m) *
        (cgnN m m (Cyl.cellμ c) f).toReal ^ ((l : ℝ) / m) :=
    fun l hl => hLCC m (2 * (m : ℝ)) (fun j => (cgnN m j (Cyl.cellμ c) f).toReal) hK1 hnn hconv l hl
  -- the endpoint norms `a_0 ≤ ‖f‖_∞` and `a_m ≤ ‖D^m f‖_2`
  have hPm : cgnP m m = 2 := by
    have hm' : (m : ℝ) ≠ 0 := ne_of_gt hmR
    rw [cgnP_of_ne m (by omega : m ≠ 0), mul_div_assoc, div_self hm', mul_one,
      ENNReal.ofReal_ofNat]
  have hNm_le : cgnN m m (Cyl.cellμ c) f ≤ Train.cellL2 c (Train.jet m f) := by
    unfold cgnN
    apply Finset.sup_le
    intro w hw
    show eLpNorm (B0151.derivWord w f) (cgnP m m) (Cyl.cellμ c) ≤
      eLpNorm (Train.jet m f) 2 (Cyl.cellμ c)
    rw [hPm]
    apply eLpNorm_mono
    intro z
    rw [Real.norm_eq_abs]
    exact (hJ f hf m z).1 w (cgn_mem_wordsOfLength.1 hw)
  have hN0_le : cgnN m 0 (Cyl.cellμ c) f ≤ ⨆ z, ‖f z‖ₑ := by
    unfold cgnN
    apply Finset.sup_le
    intro w hw
    show eLpNorm (B0151.derivWord w f) (cgnP m 0) (Cyl.cellμ c) ≤ ⨆ z, ‖f z‖ₑ
    rw [cgn_eq_nil_of_mem hw, cgnP_zero]
    exact cgn_eLpNorm_top_le f (Cyl.cellμ c)
  -- the jet bound `‖D^l f‖_{p_l} ≤ 2^m a_l`
  have hPl : (1 : ℝ≥0∞) ≤ cgnP m l := le_trans one_le_two (cgn_two_le m l hl0 hlm)
  have hjet : eLpNorm (Train.jet l f) (cgnP m l) (Cyl.cellμ c) ≤
      ∑ w ∈ wordsOfLength l, eLpNorm (B0151.derivWord w f) (cgnP m l) (Cyl.cellμ c) := by
    calc eLpNorm (Train.jet l f) (cgnP m l) (Cyl.cellμ c)
        ≤ eLpNorm (fun z => ∑ w ∈ wordsOfLength l, ‖B0151.derivWord w f z‖) (cgnP m l)
            (Cyl.cellμ c) := by
          apply eLpNorm_mono
          intro z
          have hnn' : 0 ≤ ∑ w ∈ wordsOfLength l, ‖B0151.derivWord w f z‖ :=
            Finset.sum_nonneg fun w _ => norm_nonneg _
          rw [Real.norm_of_nonneg hnn']
          refine (hJ f hf l z).2.trans_eq (Finset.sum_congr rfl fun w _ => ?_)
          exact (Real.norm_eq_abs _).symm
      _ = eLpNorm (∑ w ∈ wordsOfLength l, fun z => ‖B0151.derivWord w f z‖) (cgnP m l)
            (Cyl.cellμ c) := by
          congr 1
          funext z
          simp [Finset.sum_apply]
      _ ≤ ∑ w ∈ wordsOfLength l, eLpNorm (fun z => ‖B0151.derivWord w f z‖) (cgnP m l)
            (Cyl.cellμ c) := by
          apply eLpNorm_sum_le
          · intro w _
            exact ((B0151.contDiff_derivWord hf w).continuous.norm).aestronglyMeasurable
          · exact hPl
      _ = ∑ w ∈ wordsOfLength l, eLpNorm (B0151.derivWord w f) (cgnP m l) (Cyl.cellμ c) := by
          simp only [eLpNorm_norm]
  have hcardE : ((wordsOfLength l).card : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ m := by
    have h1 : (wordsOfLength l).card ≤ 2 ^ m :=
      (cgn_card_wordsOfLength l).trans (Nat.pow_le_pow_right (by norm_num) hlm)
    exact_mod_cast h1
  have hF1 : eLpNorm (Train.jet l f) (cgnP m l) (Cyl.cellμ c) ≤
      (2 : ℝ≥0∞) ^ m * cgnN m l (Cyl.cellμ c) f := by
    calc eLpNorm (Train.jet l f) (cgnP m l) (Cyl.cellμ c)
        ≤ ∑ w ∈ wordsOfLength l, eLpNorm (B0151.derivWord w f) (cgnP m l) (Cyl.cellμ c) :=
          hjet
      _ ≤ (wordsOfLength l).card • cgnN m l (Cyl.cellμ c) f :=
          Finset.sum_le_card_nsmul _ _ _ (fun w hw =>
            Finset.le_sup (f := fun w => eLpNorm (B0151.derivWord w f) (cgnP m l)
              (Cyl.cellμ c)) hw)
      _ = ((wordsOfLength l).card : ℝ≥0∞) * cgnN m l (Cyl.cellμ c) f := nsmul_eq_mul _ _
      _ ≤ (2 : ℝ≥0∞) ^ m * cgnN m l (Cyl.cellμ c) f := mul_le_mul_left hcardE _
  -- the final real-to-extended bound for `a_l`
  have hratio : (l : ℝ) / m ≤ 1 := (div_le_one hmR).2 hlmR
  have hratio0 : (0 : ℝ) ≤ (l : ℝ) / m := by positivity
  have hfin : cgnN m l (Cyl.cellμ c) f ≤
      ENNReal.ofReal ((2 * (m : ℝ)) ^ ((l : ℝ) * ((m : ℝ) - l) / 2)) *
        (⨆ z, ‖f z‖ₑ) ^ (1 - (l : ℝ) / m) * Train.cellL2 c (Train.jet m f) ^ ((l : ℝ) / m) :=
    cgn_final_bound (2 * (m : ℝ)) ((l : ℝ) * ((m : ℝ) - l) / 2) (1 - (l : ℝ) / m) ((l : ℝ) / m)
      hK0 (by linarith) hratio0 (cgnN m 0 (Cyl.cellμ c) f) (cgnN m m (Cyl.cellμ c) f)
      (cgnN m l (Cyl.cellμ c) f) (⨆ z, ‖f z‖ₑ) (Train.cellL2 c (Train.jet m f))
      (hNtop 0 (Nat.zero_le m)) (hNtop m le_rfl) (hNtop l hlm) hN0_le hNm_le (hchain l hlm)
  -- the exponent `l(m-l)/2` is at most `m²`, and `K ≥ 1`
  have hKe : ENNReal.ofReal ((2 * (m : ℝ)) ^ ((l : ℝ) * ((m : ℝ) - l) / 2)) ≤
      ENNReal.ofReal ((2 * (m : ℝ)) ^ ((m : ℝ) * (m : ℝ))) := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.rpow_le_rpow_of_exponent_le hK1
    have hl0R : (0 : ℝ) ≤ l := Nat.cast_nonneg l
    have hm0R : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith [mul_nonneg hl0R (sub_nonneg.2 hlmR), mul_nonneg hm0R (sub_nonneg.2 hlmR),
      mul_nonneg hm0R hm0R, sq_nonneg (l : ℝ)]
  have hbig := hfin.trans (mul_le_mul_left (mul_le_mul_left hKe _) _)
  have hCm : ENNReal.ofReal (2 ^ m * (2 * (m : ℝ)) ^ ((m : ℝ) * (m : ℝ))) =
      (2 : ℝ≥0∞) ^ m * ENNReal.ofReal ((2 * (m : ℝ)) ^ ((m : ℝ) * (m : ℝ))) := by
    rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 ^ m by positivity),
      ENNReal.ofReal_pow (show (0 : ℝ) ≤ 2 by norm_num), ENNReal.ofReal_ofNat]
  rw [← cgnP_of_ne m hl0]
  calc eLpNorm (Train.jet l f) (cgnP m l) (Cyl.cellμ c)
      ≤ (2 : ℝ≥0∞) ^ m * cgnN m l (Cyl.cellμ c) f := hF1
    _ ≤ (2 : ℝ≥0∞) ^ m * (ENNReal.ofReal ((2 * (m : ℝ)) ^ ((m : ℝ) * (m : ℝ))) *
          (⨆ z, ‖f z‖ₑ) ^ (1 - (l : ℝ) / m) * Train.cellL2 c (Train.jet m f) ^ ((l : ℝ) / m)) :=
        mul_le_mul_right hbig _
    _ = ENNReal.ofReal (2 ^ m * (2 * (m : ℝ)) ^ ((m : ℝ) * (m : ℝ))) *
          (⨆ z, ‖f z‖ₑ) ^ (1 - (l : ℝ) / m) * Train.cellL2 c (Train.jet m f) ^ ((l : ℝ) / m) := by
        rw [hCm]
        ring

end UnforcedLeray.Short.PartI
