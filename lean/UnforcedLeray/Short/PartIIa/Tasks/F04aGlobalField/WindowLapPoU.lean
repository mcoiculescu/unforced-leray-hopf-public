import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F04_1

/-!
# Part II-a, task `PartII-a:F04/1/6`: partition of unity in the window centre

Proves the Prop `WindowLapPoU` (Sub F of `Sub/PartIIa_F04_1.lean`). A smooth partition of unity
`f k` on `ℝ` subordinate to the integer windows `(k-1, k+1)` splits a test function `ψ` supported in
`winSet τ₀` into a finite sum over the four integers `k` with `⌊τ₀⌋-1 ≤ k ≤ ⌊τ₀⌋+2`.
`lapT` commutes with multiplication by a function of `τ` alone.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open UnforcedLeray.PhaseSpace
open scoped ENNReal NNReal ContDiff Manifold

namespace UnforcedLeray.Short.PartIIa

theorem measurableSet_winSet' (τ : ℝ) : MeasurableSet (winSet τ) :=
  measurableSet_Ioo.prod MeasurableSet.univ

/-- The `τ`-cutoff of a function of `τ` alone has support in the strip over the support. -/
theorem tsupport_cut_fst (g : ℝ → ℝ) (s : Set ℝ) (h : tsupport g ⊆ s) :
    tsupport (fun p : ℝ × Space => g p.1) ⊆ s ×ˢ (univ : Set Space) := by
  have h1 : tsupport (fun p : ℝ × Space => g p.1) ⊆ Prod.fst ⁻¹' tsupport g :=
    closure_minimal (fun p hp => subset_tsupport g (show p.1 ∈ Function.support g from hp))
      ((isClosed_tsupport g).preimage continuous_fst)
  intro p hp
  exact ⟨h (h1 hp), mem_univ _⟩

/-- `lapT ψ` vanishes off the support of `ψ`. -/
theorem lapT_eq_zero_of_notMem {ψ : ℝ × Space → CVec3} {p : ℝ × Space} (hp : p ∉ tsupport ψ) :
    lapT ψ p = 0 := by
  have h1 : ∀ j : Fin 3, tsupport (dy j ψ) ⊆ tsupport ψ := fun j =>
    tsupport_fderiv_apply_subset ℝ (0, coordinateVector j)
  have h2 : ∀ j : Fin 3, tsupport (dy j (dy j ψ)) ⊆ tsupport ψ := fun j =>
    (tsupport_fderiv_apply_subset ℝ (0, coordinateVector j) : tsupport (dy j (dy j ψ)) ⊆ tsupport (dy j ψ)).trans (h1 j)
  show ∑ j : Fin 3, dy j (dy j ψ) p = 0
  refine Finset.sum_eq_zero (fun j _ => ?_)
  exact image_eq_zero_of_notMem_tsupport (f := dy j (dy j ψ)) (fun h => hp (h2 j h))

/-- The derivative `∂_{y_j}` of `c(τ) ψ` is `c(τ) ∂_{y_j} ψ` for a function `c` of `τ` alone. -/
theorem dy_cut_smul (c : ℝ → ℝ) (hc : ContDiff ℝ ∞ c) {ψ : ℝ × Space → CVec3}
    (hψ : ContDiff ℝ ∞ ψ) (j : Fin 3) :
    dy j (fun q => c q.1 • ψ q) = fun p => c p.1 • dy j ψ p := by
  funext p
  have hcd : DifferentiableAt ℝ (fun q : ℝ × Space => c q.1) p :=
    ((hc.differentiable (by simp)) p.1).comp p differentiableAt_fst
  have hv : ∀ v : Space, fderiv ℝ (fun q : ℝ × Space => c q.1) p (0, v) = 0 := by
    intro v
    have h : (fun q : ℝ × Space => c q.1) = c ∘ Prod.fst := rfl
    rw [h, fderiv_comp p ((hc.differentiable (by simp)) p.1) differentiableAt_fst]
    rw [ContinuousLinearMap.comp_apply, fderiv_fst]
    change fderiv ℝ c p.1 0 = 0
    exact map_zero _
  have hψd : DifferentiableAt ℝ ψ p := (hψ.differentiable (by simp)) p
  have hS := hcd.hasFDerivAt.smul hψd.hasFDerivAt
  show fderiv ℝ (fun q => c q.1 • ψ q) p (0, coordinateVector j) =
    c p.1 • fderiv ℝ ψ p (0, coordinateVector j)
  rw [show (fun q : ℝ × Space => c q.1 • ψ q) = ((fun q : ℝ × Space => c q.1) • ψ) from rfl,
    hS.fderiv]
  simp [hv]

theorem contDiff_dy (j : Fin 3) {ψ : ℝ × Space → CVec3} (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (dy j ψ) := by
  unfold dy
  exact (hψ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- `lapT` commutes with multiplication by a function of `τ` alone. -/
theorem lapT_cut_smul (c : ℝ → ℝ) (hc : ContDiff ℝ ∞ c) {ψ : ℝ × Space → CVec3}
    (hψ : ContDiff ℝ ∞ ψ) :
    lapT (fun q => c q.1 • ψ q) = fun p => c p.1 • lapT ψ p := by
  funext p
  show ∑ j : Fin 3, dy j (dy j (fun q => c q.1 • ψ q)) p =
    c p.1 • ∑ j : Fin 3, dy j (dy j ψ) p
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [dy_cut_smul c hc hψ j, dy_cut_smul c hc (contDiff_dy j hψ) j]

/-- Gluing a.e. equal window Laplacians against a test field supported in the window. -/
theorem ae_dotL_congr_of_restrict {Λ Λ' g : ℝ × Space → CVec3} {S : Set (ℝ × Space)}
    (hS : MeasurableSet S) (hΛ : Λ =ᵐ[volume.restrict S] Λ')
    (hg : ∀ p, p ∉ S → g p = 0) :
    (fun p => dotL (Λ p) (g p)) =ᵐ[volume] fun p => dotL (Λ' p) (g p) := by
  have h1 : ∀ᵐ p ∂(volume : Measure (ℝ × Space)), p ∈ S → Λ p = Λ' p :=
    (ae_restrict_iff' hS).1 hΛ
  filter_upwards [h1] with p hp
  by_cases hpS : p ∈ S
  · rw [hp hpS]
  · simp [hg p hpS]

theorem windowLapPoU : WindowLapPoU := by
  unfold WindowLapPoU
  intro ν W Λ Λk hk hΛ τ₀
  -- a smooth partition of unity in `τ`, subordinate to the windows `(k-1, k+1)`, `k ∈ ℤ`
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ, ℝ))
    (s := (univ : Set ℝ)) isClosed_univ (fun k : ℤ => Ioo ((k : ℝ) - 1) ((k : ℝ) + 1))
    (fun k => isOpen_Ioo) (by
      intro t _
      simp only [mem_iUnion, mem_Ioo]
      exact ⟨⌊t⌋, by linarith [Int.floor_le t], by linarith [Int.lt_floor_add_one t]⟩)
  obtain ⟨F, hF⟩ : ∃ F : Finset ℤ, ∀ k : ℤ, k ∈ F ↔ ⌊τ₀⌋ - 1 ≤ k ∧ k ≤ ⌊τ₀⌋ + 2 :=
    ⟨Finset.Icc (⌊τ₀⌋ - 1) (⌊τ₀⌋ + 2), fun k => Finset.mem_Icc⟩
  -- the partition is supported in the four windows meeting `winSet τ₀`
  have hzero : ∀ k : ℤ, k ∉ F → ∀ τ ∈ Ioo (τ₀ - 1) (τ₀ + 1), f k τ = 0 := by
    intro k hk τ hτ
    apply image_eq_zero_of_notMem_tsupport (f := fun τ => f k τ)
    intro hmem
    obtain ⟨h3, h4⟩ := hf k hmem
    obtain ⟨h1, h2⟩ := hτ
    apply hk
    rw [hF]
    have hA : (k : ℝ) < (⌊τ₀⌋ : ℝ) + 3 := by linarith [Int.lt_floor_add_one τ₀]
    have hB : (⌊τ₀⌋ : ℝ) - 2 < (k : ℝ) := by linarith [Int.floor_le τ₀]
    have hA' : k < ⌊τ₀⌋ + 3 := by exact_mod_cast hA
    have hB' : ⌊τ₀⌋ - 2 < k := by exact_mod_cast hB
    constructor <;> omega
  have hF1 : ∀ τ ∈ Ioo (τ₀ - 1) (τ₀ + 1), ∑ k ∈ F, f k τ = 1 := by
    intro τ hτ
    have hsupp : Function.support (fun k : ℤ => f k τ) ⊆ (F : Set ℤ) := by
      intro k hk'
      by_contra hkF
      exact (Function.mem_support.mp hk') (hzero k (fun h => hkF (Finset.mem_coe.mpr h)) τ hτ)
    rw [← f.sum_eq_one (mem_univ τ), finsum_eq_sum_of_support_subset (fun k : ℤ => f k τ) hsupp]
  have hpart : ∀ v : ℝ × Space → CVec3, (∀ p, p ∉ winSet τ₀ → v p = 0) →
      ∀ p, ∑ k ∈ F, f k p.1 • v p = v p := by
    intro v hv p
    by_cases hp : p ∈ winSet τ₀
    · rw [← Finset.sum_smul, hF1 p.1 hp.1, one_smul]
    · rw [hv p hp]
      simp
  unfold IsWindowLaplacian
  intro ψ hψ hψc hψs
  have hψ0 : ∀ p, p ∉ winSet τ₀ → ψ p = 0 := fun p hp =>
    image_eq_zero_of_notMem_tsupport (f := ψ) (fun h => hp (hψs h))
  have hL0 : ∀ p, p ∉ winSet τ₀ → lapT ψ p = 0 := fun p hp =>
    lapT_eq_zero_of_notMem (fun h => hp (hψs h))
  have hfsm : ∀ k : ℤ, ContDiff ℝ ∞ (fun τ : ℝ => f k τ) := fun k =>
    contMDiff_iff_contDiff.mp (f k).contMDiff
  have hψk : ∀ k : ℤ, ContDiff ℝ ∞ (fun p : ℝ × Space => f k p.1 • ψ p) := fun k =>
    ((hfsm k).comp contDiff_fst).smul hψ
  have hψkc : ∀ k : ℤ, HasCompactSupport (fun p : ℝ × Space => f k p.1 • ψ p) := fun k =>
    hψc.smul_left (f := fun p : ℝ × Space => f k p.1)
  have hψks : ∀ k : ℤ, tsupport (fun p : ℝ × Space => f k p.1 • ψ p) ⊆ winSet (k : ℝ) :=
    fun k => (tsupport_smul_subset_left (fun p : ℝ × Space => f k p.1) ψ).trans
      (tsupport_cut_fst (f k) (Ioo ((k : ℝ) - 1) ((k : ℝ) + 1)) (hf k))
  have hLk : ∀ k : ℤ, lapT (fun p : ℝ × Space => f k p.1 • ψ p) =
      fun p => f k p.1 • lapT ψ p := fun k =>
    lapT_cut_smul (fun τ => f k τ) (hfsm k) hψ
  have hI : ∀ k : ℤ,
      Integrable (fun p => dotL (W p) (ν • (f k p.1 • lapT ψ p))) ∧
      Integrable (fun p => dotL (Λk k p) (f k p.1 • ψ p)) ∧
      ∫ p, dotL (W p) (ν • (f k p.1 • lapT ψ p)) = ∫ p, dotL (Λk k p) (f k p.1 • ψ p) := by
    intro k
    obtain ⟨h1, h2, h3⟩ := hk k _ (hψk k) (hψkc k) (hψks k)
    rw [hLk k] at h1 h3
    exact ⟨h1, h2, h3⟩
  have hz : ∀ k : ℤ, ∀ p, p ∉ winSet (k : ℝ) → f k p.1 • ψ p = 0 := fun k p hp =>
    image_eq_zero_of_notMem_tsupport (f := fun p => f k p.1 • ψ p) (fun h => hp (hψks k h))
  have hae : ∀ k : ℤ, (fun p => dotL (Λ p) (f k p.1 • ψ p)) =ᵐ[volume]
      fun p => dotL (Λk k p) (f k p.1 • ψ p) :=
    fun k => ae_dotL_congr_of_restrict (measurableSet_winSet' _) (hΛ k) (hz k)
  have hIΛ : ∀ k : ℤ, Integrable (fun p => dotL (Λ p) (f k p.1 • ψ p)) :=
    fun k => (hI k).2.1.congr (hae k).symm
  have hsumψ : ∀ p, ∑ k ∈ F, f k p.1 • ψ p = ψ p := hpart ψ hψ0
  have hsumv : ∀ p, ∑ k ∈ F, ν • (f k p.1 • lapT ψ p) = ν • lapT ψ p := fun p => by
    rw [← Finset.smul_sum, hpart (lapT ψ) hL0 p]
  have hA : (fun p => dotL (W p) (ν • lapT ψ p)) =
      fun p => ∑ k ∈ F, dotL (W p) (ν • (f k p.1 • lapT ψ p)) := by
    funext p
    conv_lhs => rw [← hsumv p]
    rw [map_sum]
  have hB : (fun p => dotL (Λ p) (ψ p)) = fun p => ∑ k ∈ F, dotL (Λ p) (f k p.1 • ψ p) := by
    funext p
    conv_lhs => rw [← hsumψ p]
    rw [map_sum]
  refine ⟨?_, ?_, ?_⟩
  · rw [hA]
    exact integrable_finsetSum F (fun k _ => (hI k).1)
  · rw [hB]
    exact integrable_finsetSum F (fun k _ => hIΛ k)
  · rw [hA, hB, integral_finsetSum F (fun k _ => (hI k).1),
      integral_finsetSum F (fun k _ => hIΛ k)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    exact (hI k).2.2.trans (integral_congr_ae (hae k).symm)

end UnforcedLeray.Short.PartIIa
