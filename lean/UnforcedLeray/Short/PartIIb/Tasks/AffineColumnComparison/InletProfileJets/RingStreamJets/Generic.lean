import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_5_2_2_4

/-!
# Generic jet bounds for `ringStreamJetsFix` (helpers)
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb.RingJ

theorem zero_norm_iter (l : ℕ) (x : ℝ × (ℝ × ℝ)) :
    ‖iteratedFDeriv ℝ l (fun _ : ℝ × (ℝ × ℝ) => (0 : ℝ)) x‖ = 0 := by
  rcases Nat.eq_zero_or_pos l with h | h
  · subst h
    simp
  · rw [iteratedFDeriv_const_of_ne (Nat.pos_iff_ne_zero.mp h)]
    simp

theorem vanish_norm (f : ℝ × (ℝ × ℝ) → ℝ) (x : ℝ × (ℝ × ℝ)) (h : ∀ᶠ y in 𝓝 x, f y = 0)
    (l : ℕ) : ‖iteratedFDeriv ℝ l f x‖ = 0 := by
  have hh : f =ᶠ[𝓝 x] (fun _ : ℝ × (ℝ × ℝ) => (0 : ℝ)) := h
  have he := (hh.iteratedFDeriv (𝕜 := ℝ) l).eq_of_nhds
  rw [he, zero_norm_iter]

theorem dir_norm (φ : ℝ × (ℝ × ℝ) → ℝ) (hφ : ContDiff ℝ ∞ φ) (v : ℝ × (ℝ × ℝ)) (l : ℕ)
    (x : ℝ × (ℝ × ℝ)) :
    ‖iteratedFDeriv ℝ l (fun y => fderiv ℝ φ y v) x‖ ≤ ‖v‖ * ‖iteratedFDeriv ℝ (l + 1) φ x‖ := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ φ) := hφ.fderiv_right (by simp)
  have h1 := norm_iteratedFDeriv_clm_apply_const (f := fderiv ℝ φ) (c := v) (x := x) (N := ∞)
    (n := l) hd.contDiffAt (by exact_mod_cast le_top)
  rw [norm_iteratedFDeriv_fderiv] at h1
  exact h1

theorem dir_cd (φ : ℝ × (ℝ × ℝ) → ℝ) (hφ : ContDiff ℝ ∞ φ) (v : ℝ × (ℝ × ℝ)) :
    ContDiff ℝ ∞ (fun y => fderiv ℝ φ y v) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ φ) := hφ.fderiv_right (by simp)
  exact hd.clm_apply contDiff_const

theorem smulVec_norm {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : ℝ × (ℝ × ℝ) → ℝ) (hf : ContDiff ℝ ∞ f) (v : V) (l : ℕ) (x : ℝ × (ℝ × ℝ)) :
    ‖iteratedFDeriv ℝ l (fun y => f y • v) x‖ ≤ ‖v‖ * ‖iteratedFDeriv ℝ l f x‖ := by
  have e : (fun y => f y • v) = (ContinuousLinearMap.toSpanSingleton ℝ v) ∘ f := by
    funext y
    simp
  rw [e]
  have h := ContinuousLinearMap.norm_iteratedFDeriv_comp_left
    (ContinuousLinearMap.toSpanSingleton ℝ v) (f := f) (x := x) (N := ∞) (n := l)
    hf.contDiffAt (by exact_mod_cast le_top)
  rw [ContinuousLinearMap.norm_toSpanSingleton] at h
  exact h

theorem const_mul_norm (c : ℝ) (f : ℝ × (ℝ × ℝ) → ℝ) (hf : ContDiff ℝ ∞ f) (l : ℕ)
    (x : ℝ × (ℝ × ℝ)) :
    ‖iteratedFDeriv ℝ l (fun y => c * f y) x‖ ≤ |c| * ‖iteratedFDeriv ℝ l f x‖ := by
  have e : (fun y => c * f y) = (fun y => f y • c) := by
    funext y
    simp [mul_comm]
  rw [e]
  have h := smulVec_norm f hf c l x
  simpa [Real.norm_eq_abs] using h

theorem add_norm (f g : ℝ × (ℝ × ℝ) → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (l : ℕ)
    (x : ℝ × (ℝ × ℝ)) :
    ‖iteratedFDeriv ℝ l (fun y => f y + g y) x‖ ≤
      ‖iteratedFDeriv ℝ l f x‖ + ‖iteratedFDeriv ℝ l g x‖ := by
  have h : iteratedFDeriv ℝ l (f + g) x = iteratedFDeriv ℝ l f x + iteratedFDeriv ℝ l g x :=
    iteratedFDeriv_add_apply (hf.of_le (by exact_mod_cast le_top)).contDiffAt
      (hg.of_le (by exact_mod_cast le_top)).contDiffAt
  have e : (fun y => f y + g y) = f + g := rfl
  rw [e, h]
  exact norm_add_le _ _

theorem sub_norm (f g : ℝ × (ℝ × ℝ) → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (l : ℕ)
    (x : ℝ × (ℝ × ℝ)) :
    ‖iteratedFDeriv ℝ l (fun y => f y - g y) x‖ ≤
      ‖iteratedFDeriv ℝ l f x‖ + ‖iteratedFDeriv ℝ l g x‖ := by
  have h : iteratedFDeriv ℝ l (f - g) x = iteratedFDeriv ℝ l f x - iteratedFDeriv ℝ l g x :=
    iteratedFDeriv_sub_apply (hf.of_le (by exact_mod_cast le_top)).contDiffAt
      (hg.of_le (by exact_mod_cast le_top)).contDiffAt
  have e : (fun y => f y - g y) = f - g := rfl
  rw [e, h]
  exact (norm_sub_le _ _)

/-- Iterated derivatives of a continuous linear functional of order `≥ 2` vanish. -/
theorem clm_jet_ge_two' (L : ℝ × (ℝ × ℝ) →L[ℝ] ℝ) (m : ℕ) (x : ℝ × (ℝ × ℝ)) :
    iteratedFDeriv ℝ (m + 2) (⇑L) x = 0 := by
  have h := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := (L : ℝ × (ℝ × ℝ) → ℝ)) (x := x) (n := m + 1)
  have hf : fderiv ℝ (L : ℝ × (ℝ × ℝ) → ℝ) = fun _ => L := funext fun z => L.fderiv
  rw [hf, iteratedFDeriv_succ_const] at h
  simpa using h.symm

theorem clm_jet_one' (L : ℝ × (ℝ × ℝ) →L[ℝ] ℝ) (x : ℝ × (ℝ × ℝ)) :
    ‖iteratedFDeriv ℝ 1 (⇑L) x‖ ≤ ‖L‖ := by
  have h := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := (L : ℝ × (ℝ × ℝ) → ℝ)) (x := x) (n := 0)
  have hf : fderiv ℝ (L : ℝ × (ℝ × ℝ) → ℝ) = fun _ => L := funext fun z => L.fderiv
  rw [hf] at h
  simp only [norm_iteratedFDeriv_zero] at h
  exact h.symm.le

/-- Leibniz bound for a continuous linear functional times a smooth function. -/
theorem coord_mul_norm (L : ℝ × (ℝ × ℝ) →L[ℝ] ℝ) (f : ℝ × (ℝ × ℝ) → ℝ)
    (hf : ContDiff ℝ ∞ f) (l : ℕ) (x : ℝ × (ℝ × ℝ)) :
    ‖iteratedFDeriv ℝ l (fun y => L y * f y) x‖ ≤
      |L x| * ‖iteratedFDeriv ℝ l f x‖ + (l : ℝ) * ‖L‖ * ‖iteratedFDeriv ℝ (l - 1) f x‖ := by
  have hL : ContDiff ℝ ∞ (⇑L) := L.contDiff
  have hmul := norm_iteratedFDeriv_mul_le hL hf x (n := l) (by exact_mod_cast le_top)
  have h0 : ‖iteratedFDeriv ℝ 0 (⇑L) x‖ = |L x| := by
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
  have hsum : ∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) * ‖iteratedFDeriv ℝ i (⇑L) x‖ *
      ‖iteratedFDeriv ℝ (l - i) f x‖ ≤
      |L x| * ‖iteratedFDeriv ℝ l f x‖ + (l : ℝ) * ‖L‖ * ‖iteratedFDeriv ℝ (l - 1) f x‖ := by
    rcases l with _ | n
    · simp [h0]
    · rw [Finset.sum_range_succ']
      have hz : ∑ i ∈ Finset.range (n + 1),
          ((n + 1).choose (i + 1) : ℝ) * ‖iteratedFDeriv ℝ (i + 1) (⇑L) x‖ *
            ‖iteratedFDeriv ℝ (n + 1 - (i + 1)) f x‖
          = ((n + 1).choose 1 : ℝ) * ‖iteratedFDeriv ℝ 1 (⇑L) x‖ *
            ‖iteratedFDeriv ℝ (n + 1 - 1) f x‖ := by
        rw [Finset.sum_eq_single 0]
        · intro b hb hb0
          obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
          have : iteratedFDeriv ℝ (c + 1 + 1) (⇑L) x = 0 := clm_jet_ge_two' L c x
          simp [this]
        · intro h
          exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h
      rw [hz]
      have h1 : ‖iteratedFDeriv ℝ 1 (⇑L) x‖ ≤ ‖L‖ := clm_jet_one' L x
      have hc : ((n + 1).choose 1 : ℝ) * ‖iteratedFDeriv ℝ 1 (⇑L) x‖ *
            ‖iteratedFDeriv ℝ (n + 1 - 1) f x‖ ≤
          ((n + 1 : ℕ) : ℝ) * ‖L‖ * ‖iteratedFDeriv ℝ (n + 1 - 1) f x‖ := by
        have hch : ((n + 1).choose 1 : ℝ) = ((n + 1 : ℕ) : ℝ) := by simp
        rw [hch]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
      have h2 : ((n + 1).choose 0 : ℝ) * ‖iteratedFDeriv ℝ 0 (⇑L) x‖ *
            ‖iteratedFDeriv ℝ (n + 1 - 0) f x‖ = |L x| * ‖iteratedFDeriv ℝ (n + 1) f x‖ := by
        simp [h0]
      rw [h2]
      have hsimp : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [hsimp] at hc ⊢
      have hfin : ((n:ℝ) + 1) * ‖L‖ * ‖iteratedFDeriv ℝ (n + 1 - 1) f x‖ ≥ 0 := by
        apply mul_nonneg (mul_nonneg (by positivity) (norm_nonneg _)) (norm_nonneg _)
      have hn1 : n + 1 - 1 = n := by omega
      rw [hn1] at hc ⊢
      linarith
  exact hmul.trans hsum

end UnforcedLeray.Short.IIb.RingJ
