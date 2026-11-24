import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_5_2
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_5_3
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_5_4
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_5_5
import Mathlib.Analysis.Calculus.ContDiff.Bounds

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete.T56

open UnforcedLeray.Short.PartIIIb.Concrete.T53

abbrev UU : Set Chart := Ioi 0 ×ˢ univ

def bnd (C : ℝ) (P : ℕ) (c : ℝ) (j : ℤ) : ℝ := C * (1 + |(j : ℝ)|) ^ P * Real.exp (-c * (j : ℝ) ^ 2)

theorem bnd_nonneg {C : ℝ} (hC : 0 ≤ C) (P : ℕ) (c : ℝ) (j : ℤ) : 0 ≤ bnd C P c j := by
  unfold bnd; positivity

theorem bnd_mono {C C' : ℝ} {P P' : ℕ} {c c' : ℝ} (j : ℤ) (hC0 : 0 ≤ C) (hC : C ≤ C')
    (hP : P ≤ P') (hc : c' ≤ c) : bnd C P c j ≤ bnd C' P' c' j := by
  unfold bnd
  have h1 : (1 : ℝ) ≤ 1 + |(j : ℝ)| := by linarith [abs_nonneg (j : ℝ)]
  have h2 : (1 + |(j : ℝ)|) ^ P ≤ (1 + |(j : ℝ)|) ^ P' := pow_le_pow_right₀ h1 hP
  have h3 : Real.exp (-c * (j : ℝ) ^ 2) ≤ Real.exp (-c' * (j : ℝ) ^ 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (j : ℝ)]
  have h4 : 0 ≤ (1 + |(j : ℝ)|) ^ P := by positivity
  have h5 : 0 ≤ Real.exp (-c * (j : ℝ) ^ 2) := by positivity
  have h6 : 0 ≤ (1 + |(j : ℝ)|) ^ P' := by positivity
  have h7 : 0 ≤ Real.exp (-c' * (j : ℝ) ^ 2) := by positivity
  calc C * (1 + |(j : ℝ)|) ^ P * Real.exp (-c * (j : ℝ) ^ 2)
      ≤ C' * (1 + |(j : ℝ)|) ^ P' * Real.exp (-c' * (j : ℝ) ^ 2) := by
        apply mul_le_mul _ h3 h5 (by nlinarith)
        exact mul_le_mul hC h2 h4 (by linarith)

theorem bnd_mul (C C' : ℝ) (P P' : ℕ) (c c' : ℝ) (j : ℤ) :
    bnd C P c j * bnd C' P' c' j = bnd (C * C') (P + P') (c + c') j := by
  unfold bnd
  have : Real.exp (-(c + c') * (j : ℝ) ^ 2) =
      Real.exp (-c * (j : ℝ) ^ 2) * Real.exp (-c' * (j : ℝ) ^ 2) := by
    rw [← Real.exp_add]; ring_nf
  rw [this, pow_add]; ring

theorem bnd_smul (a C : ℝ) (P : ℕ) (c : ℝ) (j : ℤ) : a * bnd C P c j = bnd (a * C) P c j := by
  unfold bnd; ring

theorem bnd_add (C C' : ℝ) (P : ℕ) (c : ℝ) (j : ℤ) :
    bnd C P c j + bnd C' P c j = bnd (C + C') P c j := by
  unfold bnd; ring

/-- The majorant class. -/
def Maj {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℝ) (K : Set Chart)
    (f : ℤ → Chart → E) : Prop :=
  (∀ j, ContDiffOn ℝ 4 (f j) UU) ∧ ∃ (C : ℝ) (P : ℕ), 0 ≤ C ∧
    ∀ j : ℤ, ∀ p ∈ K, ∀ k : ℕ, k ≤ 4 → ‖iteratedFDeriv ℝ k (f j) p‖ ≤ bnd C P c j

theorem Maj.mono {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {c c' : ℝ} {K : Set Chart}
    {f : ℤ → Chart → E} (h : Maj c K f) (hc : c' ≤ c) : Maj c' K f := by
  obtain ⟨h0, C, P, hC, hb⟩ := h
  exact ⟨h0, C, P, hC, fun j p hp k hk =>
    (hb j p hp k hk).trans (bnd_mono j hC le_rfl le_rfl hc)⟩

theorem Maj.of_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {c : ℝ} {K : Set Chart}
    {f g : ℤ → Chart → E} (h : f = g) (hf : Maj c K f) : Maj c K g := h ▸ hf

theorem Maj.add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {c1 c2 : ℝ} {K : Set Chart}
    (hK : K ⊆ UU) {f g : ℤ → Chart → E} (hf : Maj c1 K f) (hg : Maj c2 K g) :
    Maj (min c1 c2) K (fun j q => f j q + g j q) := by
  obtain ⟨hf0, C1, P1, hC1, hb1⟩ := hf
  obtain ⟨hg0, C2, P2, hC2, hb2⟩ := hg
  refine ⟨fun j => (hf0 j).add (hg0 j), C1 + C2, max P1 P2, by positivity, ?_⟩
  intro j p hp k hk
  have hpU : UU ∈ 𝓝 p := isOpen_U.mem_nhds (hK hp)
  have e : iteratedFDeriv ℝ k (fun q => f j q + g j q) p =
      iteratedFDeriv ℝ k (f j) p + iteratedFDeriv ℝ k (g j) p :=
    iteratedFDeriv_add_apply ((hf0 j).contDiffAt hpU |>.of_le (by exact_mod_cast hk))
      ((hg0 j).contDiffAt hpU |>.of_le (by exact_mod_cast hk))
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have a1 := (hb1 j p hp k hk).trans (bnd_mono j hC1 le_rfl
    (le_max_left P1 P2) (min_le_left c1 c2))
  have a2 := (hb2 j p hp k hk).trans (bnd_mono j hC2 le_rfl
    (le_max_right P1 P2) (min_le_right c1 c2))
  have := add_le_add a1 a2
  rwa [bnd_add] at this

theorem Maj.bil {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] {c1 c2 : ℝ} {K : Set Chart}
    (hK : K ⊆ UU) (B : E →L[ℝ] F →L[ℝ] G) {f : ℤ → Chart → E} {g : ℤ → Chart → F}
    (hf : Maj c1 K f) (hg : Maj c2 K g) :
    Maj (c1 + c2) K (fun j q => B (f j q) (g j q)) := by
  obtain ⟨hf0, C1, P1, hC1, hb1⟩ := hf
  obtain ⟨hg0, C2, P2, hC2, hb2⟩ := hg
  refine ⟨fun j => B.isBoundedBilinearMap.contDiff.comp_contDiffOn ((hf0 j).prodMk (hg0 j)),
    ‖B‖ * 16 * (C1 * C2), P1 + P2, by positivity, ?_⟩
  intro j p hp k hk
  have hpU : p ∈ UU := hK hp
  rw [← iteratedFDerivWithin_of_isOpen k isOpen_U hpU]
  have key := B.norm_iteratedFDerivWithin_le_of_bilinear (hf0 j) (hg0 j)
    isOpen_U.uniqueDiffOn hpU (n := k) (N := 4) (by exact_mod_cast hk)
  refine key.trans ?_
  set X := bnd C1 P1 c1 j with hX
  set Y := bnd C2 P2 c2 j with hY
  have hX0 : 0 ≤ X := bnd_nonneg hC1 _ _ _
  have hY0 : 0 ≤ Y := bnd_nonneg hC2 _ _ _
  have step : ∀ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i (f j) UU p‖ *
        ‖iteratedFDerivWithin ℝ (k - i) (g j) UU p‖ ≤ (k.choose i : ℝ) * X * Y := by
    intro i hi
    have hi' : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [iteratedFDerivWithin_of_isOpen i isOpen_U hpU,
      iteratedFDerivWithin_of_isOpen (k - i) isOpen_U hpU]
    have a1 := hb1 j p hp i (hi'.trans hk)
    have a2 := hb2 j p hp (k - i) ((Nat.sub_le k i).trans hk)
    have : (0 : ℝ) ≤ k.choose i := Nat.cast_nonneg _
    gcongr
  have hsum : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * X * Y = 2 ^ k * (X * Y) := by
    have : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) = 2 ^ k := by
      exact_mod_cast Nat.sum_range_choose k
    rw [← Finset.sum_mul, ← Finset.sum_mul, this]; ring
  have h2k : (2 : ℝ) ^ k ≤ 16 := by
    calc (2 : ℝ) ^ k ≤ 2 ^ 4 := pow_le_pow_right₀ (by norm_num) hk
      _ = 16 := by norm_num
  calc ‖B‖ * (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i (f j) UU p‖ *
        ‖iteratedFDerivWithin ℝ (k - i) (g j) UU p‖)
      ≤ ‖B‖ * (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * X * Y) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum step) (by positivity)
    _ = ‖B‖ * (2 ^ k * (X * Y)) := by rw [hsum]
    _ ≤ ‖B‖ * (16 * (X * Y)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right h2k (mul_nonneg hX0 hY0)) (by positivity)
    _ = bnd (‖B‖ * 16 * (C1 * C2)) (P1 + P2) (c1 + c2) j := by
        rw [hX, hY, bnd_mul, ← bnd_smul]; unfold bnd; ring

theorem Maj.compL {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {c : ℝ} {K : Set Chart} (hK : K ⊆ UU) (L : E →L[ℝ] F) {f : ℤ → Chart → E}
    (hf : Maj c K f) : Maj c K (fun j q => L (f j q)) := by
  obtain ⟨hf0, C1, P1, hC1, hb1⟩ := hf
  refine ⟨fun j => L.contDiff.comp_contDiffOn (hf0 j), ‖L‖ * C1, P1, by positivity, ?_⟩
  intro j p hp k hk
  have hpU : UU ∈ 𝓝 p := isOpen_U.mem_nhds (hK hp)
  have := L.norm_iteratedFDeriv_comp_left (f := f j) (x := p) (N := 4) (n := k)
    ((hf0 j).contDiffAt hpU) (by exact_mod_cast hk)
  refine this.trans ?_
  rw [← bnd_smul]
  exact mul_le_mul_of_nonneg_left (hb1 j p hp k hk) (norm_nonneg _)

theorem Maj.const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set Chart}
    (hK : IsCompact K) (hKU : K ⊆ UU) {g : Chart → E} (hg : ContDiffOn ℝ 4 g UU) :
    Maj 0 K (fun _ => g) := by
  have hc : ContinuousOn (fun p => ∑ k ∈ Finset.range 5, ‖iteratedFDerivWithin ℝ k g UU p‖) UU := by
    refine continuousOn_finset_sum _ (fun k hk => ?_)
    have hk4 : k ≤ 4 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    exact (hg.continuousOn_iteratedFDerivWithin (m := k) (by exact_mod_cast hk4)
      isOpen_U.uniqueDiffOn).norm
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hc.mono hKU)
  refine ⟨fun _ => hg, |C|, 0, abs_nonneg _, ?_⟩
  intro j p hp k hk
  rw [← iteratedFDerivWithin_of_isOpen k isOpen_U (hKU hp)]
  have h1 : ‖iteratedFDerivWithin ℝ k g UU p‖ ≤
      ∑ k ∈ Finset.range 5, ‖iteratedFDerivWithin ℝ k g UU p‖ :=
    Finset.single_le_sum (f := fun k => ‖iteratedFDerivWithin ℝ k g UU p‖)
      (fun i _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
  have h2 := hC p hp
  have h3 : ∑ k ∈ Finset.range 5, ‖iteratedFDerivWithin ℝ k g UU p‖ ≤ |C| :=
    (Real.le_norm_self _).trans (h2.trans (le_abs_self C))
  unfold bnd
  simpa using h1.trans h3

theorem Maj.constVec {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set Chart}
    (v : ℤ → E) (C : ℝ) (P : ℕ) (hC : 0 ≤ C) (hv : ∀ j, ‖v j‖ ≤ bnd C P 0 j) :
    Maj 0 K (fun j _ => v j) := by
  refine ⟨fun j => contDiffOn_const, C, P, hC, ?_⟩
  intro j p hp k hk
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simpa using hv j
  · rw [iteratedFDeriv_const_of_ne hk0.ne']
    simpa using bnd_nonneg hC P 0 j

theorem bnd_le_abs (C : ℝ) (P : ℕ) (c : ℝ) (j : ℤ) : bnd C P c j ≤ bnd |C| P c j := by
  unfold bnd
  have h1 : 0 ≤ (1 + |(j : ℝ)|) ^ P := by positivity
  have h2 : 0 ≤ Real.exp (-c * (j : ℝ) ^ 2) := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) h1) h2

theorem vpBound (ν : ℝ) (hν : 0 < ν) (K : Set Chart) (hK : IsCompact K) (hKs : K ⊆ UU) (N : ℕ) :
    ∃ (C c : ℝ) (P : ℕ), 0 ≤ C ∧ 0 < c ∧ ∀ j : ℤ, ∀ p ∈ K, ∀ k : ℕ, k ≤ N →
      ‖iteratedFDeriv ℝ k (fun q : Chart => Vj ν q.1 j q.2) p‖ ≤ bnd C P c j ∧
      ‖iteratedFDeriv ℝ k (fun q : Chart => psij ν q.1 j q.2) p‖ ≤ bnd C P c j := by
  induction N with
  | zero =>
    obtain ⟨C, c, P, hc, h⟩ := vjPsijMajor ν hν K hK hKs 0
    refine ⟨|C|, c, P, abs_nonneg _, hc, ?_⟩
    intro j p hp k hk
    obtain rfl : k = 0 := by omega
    exact ⟨(h j p hp).1.trans (bnd_le_abs C P c j), (h j p hp).2.trans (bnd_le_abs C P c j)⟩
  | succ N ih =>
    obtain ⟨C1, c1, P1, hC1, hc1, h1⟩ := ih
    obtain ⟨C2, c2, P2, hc2, h2⟩ := vjPsijMajor ν hν K hK hKs (N + 1)
    refine ⟨C1 + |C2|, min c1 c2, max P1 P2, by positivity, lt_min hc1 hc2, ?_⟩
    intro j p hp k hk
    rcases Nat.lt_or_ge k (N + 1) with hl | hl
    · obtain ⟨a, b⟩ := h1 j p hp k (by omega)
      have m := bnd_mono j hC1 (le_add_of_nonneg_right (abs_nonneg C2)) (le_max_left P1 P2)
        (min_le_left c1 c2) (C := C1) (P := P1) (c := c1)
      exact ⟨a.trans m, b.trans m⟩
    · obtain rfl : k = N + 1 := by omega
      have m := bnd_mono j (abs_nonneg C2) (le_add_of_nonneg_left hC1) (le_max_right P1 P2)
        (min_le_right c1 c2) (C := |C2|) (P := P2) (c := c2)
      exact ⟨(h2 j p hp).1.trans ((bnd_le_abs C2 P2 c2 j).trans m),
        (h2 j p hp).2.trans ((bnd_le_abs C2 P2 c2 j).trans m)⟩

theorem partial_maj {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set Chart}
    (hK : K ⊆ UU) (Ff : ℤ → Chart → E) (h5 : ∀ j, ContDiffOn ℝ 5 (Ff j) UU) (C c : ℝ) (P : ℕ)
    (hC : 0 ≤ C)
    (hb : ∀ j : ℤ, ∀ p ∈ K, ∀ k : ℕ, k ≤ 5 → ‖iteratedFDeriv ℝ k (Ff j) p‖ ≤ bnd C P c j) :
    Maj c K (fun j q => fderiv ℝ (fun x => Ff j (q.1, x)) q.2) := by
  let Φ : (Chart →L[ℝ] E) →L[ℝ] ((ℝ × ℝ) →L[ℝ] E) :=
    (ContinuousLinearMap.compL ℝ (ℝ × ℝ) Chart E).flip (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))
  have hΦ : ∀ L, Φ L = L.comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) := fun L => rfl
  have heq : ∀ j, ∀ q ∈ UU, fderiv ℝ (fun x => Ff j (q.1, x)) q.2 = Φ (fderiv ℝ (Ff j) q) := by
    intro j q hq
    rw [hΦ]
    have hd : DifferentiableAt ℝ (Ff j) q :=
      (((h5 j) q hq).differentiableWithinAt (by norm_num)).differentiableAt
        (isOpen_U.mem_nhds hq)
    exact partial_eq (Ff j) q.1 q.2 hd
  have hd4 : ∀ j, ContDiffOn ℝ 4 (fderiv ℝ (Ff j)) UU :=
    fun j => (h5 j).fderiv_of_isOpen isOpen_U (by norm_num)
  refine ⟨fun j => ?_, ‖Φ‖ * C, P, by positivity, ?_⟩
  · exact (Φ.contDiff.comp_contDiffOn (hd4 j)).congr (fun q hq => heq j q hq)
  · intro j p hp k hk
    have hpU : UU ∈ 𝓝 p := isOpen_U.mem_nhds (hK hp)
    have hev : (fun q => fderiv ℝ (fun x => Ff j (q.1, x)) q.2) =ᶠ[𝓝 p]
        (Φ ∘ fderiv ℝ (Ff j)) :=
      Filter.eventuallyEq_of_mem hpU (fun q hq => heq j q hq)
    have e := (hev.iteratedFDeriv ℝ k).eq_of_nhds
    rw [e]
    have hdf : ContDiffAt ℝ 4 (fderiv ℝ (Ff j)) p := ((hd4 j).contDiffAt hpU)
    refine (Φ.norm_iteratedFDeriv_comp_left (f := fderiv ℝ (Ff j)) (x := p) (N := 4) (n := k)
      hdf (by exact_mod_cast hk)).trans ?_
    rw [norm_iteratedFDeriv_fderiv, ← bnd_smul]
    exact mul_le_mul_of_nonneg_left (hb j p hp (k + 1) (by omega)) (by positivity)

def B1 : Mat3 →L[ℝ] (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : ((ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) ≃ₗ[ℝ] ((ℝ × ℝ) →L[ℝ] (ℝ × ℝ))).toLinearMap
      ∘ₗ (LinearMap.mk₂ ℝ merApply
        (fun m1 m2 v => by ext <;> simp [merApply] <;> ring)
        (fun c m v => by ext <;> simp [merApply] <;> ring)
        (fun m v1 v2 => by ext <;> simp [merApply] <;> ring)
        (fun c m v => by ext <;> simp [merApply] <;> ring)))

theorem B1_apply (m : Mat3) (v : ℝ × ℝ) : B1 m v = merApply m v := rfl

def trL : Mat3 →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := merTrace
      map_add' := fun a b => by simp [merTrace]; ring
      map_smul' := fun c a => by simp [merTrace]; ring }

theorem trL_apply (m : Mat3) : trL m = merTrace m := rfl

def toMerCLM : (ℝ × ℝ) →L[ℝ] Merid := LinearMap.toContinuousLinearMap toMerLE.toLinearMap

theorem toMerCLM_apply (v : ℝ × ℝ) : toMerCLM v = toMer v := rfl

theorem maj_main (as : ℝ) (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf) (ν : ℝ) (hν : 0 < ν)
    (A : ℝ → Mat3) (hA : IsAffElem as A) (K : Set Chart) (hK : IsCompact K) (hKU : K ⊆ UU) :
    ∃ c : ℝ, 0 < c ∧ Maj c K (fun j q => toMer (hTerm ν χf A j q)) ∧
      Maj c K (pTerm ν χf A) := by
  have hχ6 : ContDiff ℝ 6 χf := hχ.smooth.of_le (by simp)
  have hAy : ContDiffOn ℝ 6 (Ay ν χf A) (Ioi 0) := by
    unfold Ay
    have hc : ContDiffOn ℝ 6 (fun s : ℝ => χf (ν * s)) (Ioi 0) :=
      (hχ6.comp (contDiff_const.mul contDiff_id)).contDiffOn.mono (subset_univ _)
    exact hc.smul hA.smooth
  have hAyU : ContDiffOn ℝ 4 (fun p : Chart => Ay ν χf A p.1) UU :=
    ((hAy.of_le (by norm_num)).comp (contDiffOn_fst (𝕜 := ℝ) (n := 4) (s := UU))
      (fun p hp => hp.1))
  have Ma : Maj 0 K (fun _ q => Ay ν χf A q.1) := Maj.const hK hKU hAyU
  obtain ⟨C, c, P, hC, hc, hb⟩ := vpBound ν hν K hK hKU 5
  have MV : Maj c K (fun j q => Vj ν q.1 j q.2) :=
    ⟨fun j => (vjPsijContDiff ν hν j).1.of_le (by norm_num), C, P, hC,
      fun j p hp k hk => (hb j p hp k (by omega)).1⟩
  have MP : Maj c K (fun j q => psij ν q.1 j q.2) :=
    ⟨fun j => (vjPsijContDiff ν hν j).2.of_le (by norm_num), C, P, hC,
      fun j p hp k hk => (hb j p hp k (by omega)).2⟩
  have MTV := partial_maj hKU (fun j q => Vj ν q.1 j q.2) (fun j => (vjPsijContDiff ν hν j).1)
    C c P hC (fun j p hp k hk => (hb j p hp k hk).1)
  have MTP := partial_maj hKU (fun j q => psij ν q.1 j q.2) (fun j => (vjPsijContDiff ν hν j).2)
    C c P hC (fun j p hp k hk => (hb j p hp k hk).2)
  have M1 : Maj 0 K (fun _ (q : Chart) => q.2) := Maj.const hK hKU contDiff_snd.contDiffOn
  have hc0 : 0 ≤ cOf ν := by unfold cOf; positivity
  have M2 : Maj 0 K (fun (j : ℤ) (_ : Chart) => ((-((j : ℝ) * cOf ν), 0) : ℝ × ℝ)) :=
    Maj.constVec _ (cOf ν) 1 hc0 (fun j => by
      have : ‖((-((j : ℝ) * cOf ν), 0) : ℝ × ℝ)‖ = |(j : ℝ)| * cOf ν := by
        simp [Prod.norm_def, abs_mul, abs_of_nonneg hc0]
        positivity
      rw [this]
      unfold bnd
      simp only [neg_zero, zero_mul, Real.exp_zero, mul_one, pow_one]
      nlinarith [abs_nonneg (j : ℝ)])
  have Mx : Maj 0 K (fun j q => xj ν j q.2) := by
    have h := (M1.add hKU M2).mono (c' := 0) (by simp)
    have e : (fun (j : ℤ) (q : Chart) => q.2 + ((-((j : ℝ) * cOf ν), 0) : ℝ × ℝ)) =
        fun j q => xj ν j q.2 := by
      funext j q
      ext <;> simp [xj, sub_eq_add_neg]
    rwa [e] at h
  have MW := Maj.bil hKU B1 Ma Mx
  have T1 := Maj.bil hKU B1 Ma MV
  have T2 := Maj.bil hKU (-(ContinuousLinearMap.id ℝ ((ℝ × ℝ) →L[ℝ] (ℝ × ℝ)))) MTV MW
  have S := (Maj.add hKU T1 T2).compL hKU toMerCLM
  have Tr := Maj.compL hKU trL Ma
  have T3 := Maj.bil hKU (ContinuousLinearMap.mul ℝ ℝ) Tr MP
  have T4 := Maj.bil hKU (-(ContinuousLinearMap.id ℝ ((ℝ × ℝ) →L[ℝ] ℝ))) MTP MW
  have S2 := Maj.add hKU T3 T4
  refine ⟨min (0 + c) (c + (0 + 0)), lt_min (by simpa using hc) (by simpa using hc), ?_, ?_⟩
  · refine Maj.of_eq ?_ S
    funext j q
    simp [hTerm, B1_apply, toMerCLM_apply, sub_eq_add_neg]
  · refine Maj.of_eq ?_ S2
    funext j q
    simp [pTerm, trL_apply, B1_apply, sub_eq_add_neg]

end UnforcedLeray.Short.PartIIIb.Concrete.T56

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.PartIIIb.Concrete.T56

theorem latTermMajor (as : ℝ) (χf : ℝ → ℝ) : LatTermMajor as χf := by
  intro hχ ν hν A hA p hp
  have hs : 0 < p.1 := hp.1
  have hr : 0 < p.1 / 2 := by positivity
  have hsub : Metric.closedBall p (p.1 / 2) ⊆ UU := by
    intro q hq
    have h1 : dist q.1 p.1 ≤ p.1 / 2 := by
      have := Metric.mem_closedBall.mp hq
      simp only [Prod.dist_eq, max_le_iff] at this
      exact this.1
    have h2 := (abs_le.mp (by simpa [Real.dist_eq] using h1))
    exact ⟨by simp only [mem_Ioi]; linarith [h2.1], mem_univ _⟩
  obtain ⟨c, hc, ⟨_, C1, P1, hC1, hb1⟩, ⟨_, C2, P2, hC2, hb2⟩⟩ :=
    maj_main as χf hχ ν hν A hA _ (isCompact_closedBall p (p.1 / 2)) hsub
  refine ⟨Metric.closedBall p (p.1 / 2), Metric.closedBall_mem_nhds p hr, hsub,
    fun j => bnd C1 P1 c j + bnd C2 P2 c j, ?_, ?_⟩
  · have sm : ∀ (C : ℝ) (P : ℕ), Summable (fun j : ℤ => bnd C P c j) := by
      intro C P
      have := (gaussLatticeSummable P c hc).mul_left C
      refine this.congr (fun j => ?_)
      unfold bnd; ring
    exact (sm C1 P1).add (sm C2 P2)
  · intro j k hk x hx
    exact ⟨(hb1 j x hx k hk).trans (le_add_of_nonneg_right (bnd_nonneg hC2 _ _ _)),
      (hb2 j x hx k hk).trans (le_add_of_nonneg_left (bnd_nonneg hC1 _ _ _))⟩

end UnforcedLeray.Short.PartIIIb.Concrete
