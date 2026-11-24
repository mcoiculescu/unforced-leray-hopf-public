import UnforcedLeray.Short.PartIIb.Sub.T11_6

/-!
# Part II-b, leaf `PerNice`: periodization of a compactly supported cut-off

Source of record: `the November 2 reference manuscript`, SP 1921-1938 (the
periodization used for the nice streams). The statement is `PerNice` of `Sub/T11_6.lean`, unchanged.

Proof. Given `ψ` smooth with compact support, put `ζ p = ∑' n : ℤ, ψ (p.1 + n c, p.2)`.
Since `ψ` vanishes outside a sup-norm ball of radius `A`, near any point `x0` only finitely many
translates `n` are nonzero (`pncNbhd`). Hence near `x0` the series is a finite sum of smooth
translates, which gives smoothness, the derivative formula (`fderiv_fun_sum`, translation invariance
`fderiv_comp_add_right`), periodicity (reindexing `n ↦ n + 1`) and compact support in `η`
(take `L = A + 1`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- A compactly supported `ψ` is bounded in the sup norm on its support. -/
lemma pncBound (ψ : ℝ × ℝ → ℝ) (hψc : HasCompactSupport ψ) :
    ∃ A : ℝ, ∀ x : ℝ × ℝ, ψ x ≠ 0 → ‖x‖ ≤ A := by
  obtain ⟨A, hA⟩ := hψc.isCompact.isBounded.exists_norm_le
  exact ⟨A, fun x hx => hA x (subset_tsupport ψ (Function.mem_support.mpr hx))⟩

/-- The translate `q ↦ ψ (q.1 + a, q.2)` is `q ↦ ψ (q + (a, 0))`. -/
lemma pncTranslate (ψ : ℝ × ℝ → ℝ) (a : ℝ) :
    (fun q : ℝ × ℝ => ψ (q.1 + a, q.2)) = fun q => ψ (q + (a, 0)) := by
  funext q
  congr 1
  ext <;> simp

/-- Each translate in the first variable is smooth. -/
lemma pncContDiff (c : ℝ) (ψ : ℝ × ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (n : ℤ) :
    ContDiff ℝ ∞ (fun q : ℝ × ℝ => ψ (q.1 + n * c, q.2)) := by
  exact hψ.comp (by fun_prop)

/-- `∇^⊥` commutes with translation in the first variable. -/
lemma pncPerpTranslate (ψ : ℝ × ℝ → ℝ) (a : ℝ) (p : ℝ × ℝ) (i : Fin 2) :
    perpGrad (fun q : ℝ × ℝ => ψ (q.1 + a, q.2)) p i = perpGrad ψ (p.1 + a, p.2) i := by
  rw [pncTranslate ψ a]
  have hd : fderiv ℝ (fun q : ℝ × ℝ => ψ (q + (a, 0))) p = fderiv ℝ ψ (p + (a, 0)) :=
    fderiv_comp_add_right _
  have hp : p + (a, 0) = (p.1 + a, p.2) := by ext <;> simp
  unfold perpGrad
  rw [hd, hp]

/-- Locally only finitely many translates are nonzero. -/
lemma pncNbhd (c : ℝ) (hc : 0 < c) (ψ : ℝ × ℝ → ℝ) (hψc : HasCompactSupport ψ) (x0 : ℝ × ℝ) :
    ∃ M : ℤ, ∀ᶠ q in 𝓝 x0, ∀ n : ℤ, M < n ∨ n < -M → ψ (q.1 + n * c, q.2) = 0 := by
  obtain ⟨A, hA⟩ := pncBound ψ hψc
  obtain ⟨M, hM⟩ := exists_int_gt ((A + |x0.1| + 1) / c)
  have hBM : A + |x0.1| + 1 < M * c := (div_lt_iff₀ hc).mp hM
  have hcont : Continuous (fun q : ℝ × ℝ => |q.1 - x0.1|) := by fun_prop
  have hev : ∀ᶠ q in 𝓝 x0, |q.1 - x0.1| < 1 :=
    hcont.continuousAt.eventually_lt continuousAt_const (by simp)
  refine ⟨M, ?_⟩
  filter_upwards [hev] with q hq
  intro n hn
  by_contra hne
  have h1 : ‖(q.1 + n * c, q.2)‖ ≤ A := hA _ hne
  have h2 : ‖q.1 + n * c‖ ≤ ‖(q.1 + n * c, q.2)‖ := norm_fst_le (q.1 + n * c, q.2)
  rw [Real.norm_eq_abs] at h2
  have hx := abs_le.mp (h2.trans h1)
  have hq' := abs_lt.mp hq
  have hx0a := neg_abs_le x0.1
  have hx0b := le_abs_self x0.1
  rcases hn with h | h
  · have hMn : (M : ℝ) < n := by exact_mod_cast h
    have h3 := mul_lt_mul_of_pos_right hMn hc
    linarith [hx.1, hx.2, hq'.1, hq'.2]
  · have hnM : (n : ℝ) < -M := by exact_mod_cast h
    have h3 := mul_lt_mul_of_pos_right hnM hc
    rw [neg_mul] at h3
    linarith [hx.1, hx.2, hq'.1, hq'.2]

/-- Near `x0` the series defining `ζ` is a finite sum over a window `S` of translates, and the
translates outside `S` vanish near `x0`. -/
lemma pncZetaEq (c : ℝ) (hc : 0 < c) (ψ : ℝ × ℝ → ℝ) (hψc : HasCompactSupport ψ) (x0 : ℝ × ℝ) :
    ∃ S : Finset ℤ,
      (fun q : ℝ × ℝ => ∑' n : ℤ, ψ (q.1 + n * c, q.2)) =ᶠ[𝓝 x0]
        (fun q => ∑ n ∈ S, ψ (q.1 + n * c, q.2)) ∧
      ∀ n ∉ S, (fun q : ℝ × ℝ => ψ (q.1 + n * c, q.2)) =ᶠ[𝓝 x0] (fun _ => (0 : ℝ)) := by
  obtain ⟨M, hM⟩ := pncNbhd c hc ψ hψc x0
  refine ⟨Finset.Icc (-M) M, ?_, ?_⟩
  · filter_upwards [hM] with q hq
    apply tsum_eq_sum
    intro n hn
    exact hq n (by rw [Finset.mem_Icc] at hn; omega)
  · intro n hn
    filter_upwards [hM] with q hq
    exact hq n (by rw [Finset.mem_Icc] at hn; omega)

/-- The perpendicular gradient of a locally finite sum of translates at `x0`. -/
lemma pncPerpFinite (c : ℝ) (ψ : ℝ × ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (ζ : ℝ × ℝ → ℝ)
    (x0 : ℝ × ℝ) (S : Finset ℤ)
    (hζS : ζ =ᶠ[𝓝 x0] (fun q => ∑ n ∈ S, ψ (q.1 + n * c, q.2))) (i : Fin 2) :
    perpGrad ζ x0 i = ∑ n ∈ S, perpGrad ψ (x0.1 + n * c, x0.2) i := by
  have hd : fderiv ℝ ζ x0
      = ∑ n ∈ S, fderiv ℝ (fun q : ℝ × ℝ => ψ (q.1 + n * c, q.2)) x0 := by
    rw [hζS.fderiv_eq]
    exact fderiv_fun_sum (fun n _ => (pncContDiff c ψ hψ n).differentiable (by simp) x0)
  have hcomp : ∀ j : Fin 2, perpGrad ζ x0 j
      = ∑ n ∈ S, perpGrad (fun q : ℝ × ℝ => ψ (q.1 + n * c, q.2)) x0 j := by
    intro j
    fin_cases j
    · simp [perpGrad, hd]
    · simp [perpGrad, hd, Finset.sum_neg_distrib]
  rw [hcomp i]
  exact Finset.sum_congr rfl fun n _ => pncPerpTranslate ψ _ x0 i

/-- Locally the tsum of perpendicular gradients is the finite sum over `S`. -/
lemma pncTsumPerp (c : ℝ) (ψ : ℝ × ℝ → ℝ) (x0 : ℝ × ℝ) (S : Finset ℤ)
    (hout : ∀ n ∉ S, (fun q : ℝ × ℝ => ψ (q.1 + n * c, q.2)) =ᶠ[𝓝 x0] (fun _ => (0 : ℝ)))
    (i : Fin 2) :
    ∑' n : ℤ, perpGrad ψ (x0.1 + n * c, x0.2) i = ∑ n ∈ S, perpGrad ψ (x0.1 + n * c, x0.2) i := by
  apply tsum_eq_sum
  intro n hn
  rw [← pncPerpTranslate ψ (n * c) x0 i]
  have h0 : fderiv ℝ (fun q : ℝ × ℝ => ψ (q.1 + n * c, q.2)) x0 = 0 := by
    rw [(hout n hn).fderiv_eq, fderiv_const_apply]
  fin_cases i
  · simp [perpGrad, h0]
  · simp [perpGrad, h0]

/-- **Leaf `PerNice`.** The periodization `ζ p = ∑' n : ℤ, ψ (p.1 + n c, p.2)` of a smooth
compactly supported `ψ` is a nice stream whose `∇^⊥` is the periodized `∇^⊥ψ`. -/
theorem perNice : UnforcedLeray.Short.IIb.PerNice := by
  unfold PerNice
  intro c ψ hc hψ hψc
  obtain ⟨A, hA⟩ := pncBound ψ hψc
  refine ⟨fun p => ∑' n : ℤ, ψ (p.1 + n * c, p.2), ⟨?_, ?_, ?_⟩, ?_⟩
  · -- smoothness, from the local finite representation
    rw [contDiff_iff_contDiffAt]
    intro x0
    obtain ⟨S, hS, -⟩ := pncZetaEq c hc ψ hψc x0
    exact (ContDiff.sum (s := S) fun n _ => pncContDiff c ψ hψ n).contDiffAt.congr_of_eventuallyEq hS
  · -- periodicity in `q`, by reindexing `n ↦ n + 1`
    intro p
    show ∑' n : ℤ, ψ ((p.1 + c) + n * c, p.2) = ∑' n : ℤ, ψ (p.1 + n * c, p.2)
    have key : ∑' n : ℤ, ψ (p.1 + ((n + 1 : ℤ) : ℝ) * c, p.2) = ∑' n : ℤ, ψ (p.1 + n * c, p.2) :=
      (Equiv.addRight (1 : ℤ)).tsum_eq (fun n : ℤ => ψ (p.1 + n * c, p.2))
    rw [← key]
    refine tsum_congr fun n => ?_
    have e : p.1 + c + (n : ℝ) * c = p.1 + ((n + 1 : ℤ) : ℝ) * c := by push_cast; ring
    rw [e]
  · -- compact support in `η`: `ζ p = 0` once `|p.2| ≥ A + 1`
    refine ⟨A + 1, fun p hp => ?_⟩
    show ∑' n : ℤ, ψ (p.1 + n * c, p.2) = 0
    have hz : ∀ n : ℤ, ψ (p.1 + n * c, p.2) = 0 := by
      intro n
      by_contra hne
      have h1 : ‖(p.1 + n * c, p.2)‖ ≤ A := hA _ hne
      have h2 : ‖p.2‖ ≤ ‖(p.1 + n * c, p.2)‖ := norm_snd_le (p.1 + n * c, p.2)
      rw [Real.norm_eq_abs] at h2
      linarith
    simp [hz]
  · -- the derivative formula
    intro p i
    obtain ⟨S, hζS, hout⟩ := pncZetaEq c hc ψ hψc p
    rw [pncPerpFinite c ψ hψ _ p S hζS i, pncTsumPerp c ψ p S hout i]

end UnforcedLeray.Short.IIb
