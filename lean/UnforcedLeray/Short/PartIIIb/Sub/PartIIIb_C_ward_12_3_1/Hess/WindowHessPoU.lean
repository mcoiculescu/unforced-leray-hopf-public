import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.Hess.Defs
import UnforcedLeray.Short.PartIIa.Tasks.F04aGlobalField.WindowLapPoU

/-!
# Partition of unity in the window centre, Hessian version

Task `PartIII-b:C/ward/12/3/1/2/2/8`.  Proves `WindowHessPoU` (Hessian analogue of
`PartII-a` `windowLapPoU`).  A smooth partition of unity `f n` on `ℝ` subordinate to the integer
windows `(n-1, n+1)` splits a test function `ψ` supported in `winSet τ₀` into a finite sum over the
four integers `n` with `⌊τ₀⌋-1 ≤ n ≤ ⌊τ₀⌋+2`.  `ν ∂_j∂_k` commutes with multiplication by a
function of `τ` alone.  Source of record: `the November 2 reference manuscript`,
lines 1437-1441.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff Manifold

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.Short.PartIIa.Rep
open UnforcedLeray.Parabolic (PS IsSTTest sD2)
open UnforcedLeray.Short.PartIIa (WindowCutoff windowField windowLap winSet)

/-- A `y`-derivative does not enlarge the support. -/
private theorem hsPoU_dy_tsupport (j : Fin 3) (g : ℝ × Space → CVec3) :
    tsupport (dy j g) ⊆ tsupport g :=
  tsupport_fderiv_apply_subset ℝ (0, coordinateVector j)

/-- `ν∂_j∂_kψ` vanishes off the support of `ψ`. -/
private theorem hsPoU_hess_eq_zero (ν : ℝ) (j k : Fin 3) {ψ : ℝ × Space → CVec3}
    {p : ℝ × Space} (hp : p ∉ tsupport ψ) : nuHessT ν j k ψ p = 0 := by
  have h2 : tsupport (dy j (dy k ψ)) ⊆ tsupport ψ :=
    (hsPoU_dy_tsupport j (dy k ψ)).trans (hsPoU_dy_tsupport k ψ)
  have h0 : dy j (dy k ψ) p = 0 := image_eq_zero_of_notMem_tsupport (fun h => hp (h2 h))
  show ν • dy j (dy k ψ) p = 0
  rw [h0, smul_zero]

/-- `ν∂_j∂_k` commutes with multiplication by a function of `τ` alone. -/
private theorem hsPoU_hess_cut_smul (ν : ℝ) (j k : Fin 3) (c : ℝ → ℝ) (hc : ContDiff ℝ ∞ c)
    {ψ : ℝ × Space → CVec3} (hψ : ContDiff ℝ ∞ ψ) :
    nuHessT ν j k (fun q => c q.1 • ψ q) = fun p => c p.1 • nuHessT ν j k ψ p := by
  funext p
  have e1 : dy k (fun q => c q.1 • ψ q) = fun p => c p.1 • dy k ψ p :=
    UnforcedLeray.Short.PartIIa.dy_cut_smul c hc hψ k
  have e2 : dy j (fun q => c q.1 • dy k ψ q) = fun p => c p.1 • dy j (dy k ψ) p :=
    UnforcedLeray.Short.PartIIa.dy_cut_smul c hc (UnforcedLeray.Short.PartIIa.contDiff_dy k hψ) j
  show ν • dy j (dy k (fun q => c q.1 • ψ q)) p = c p.1 • (ν • dy j (dy k ψ)) p
  rw [e1, e2]
  show ν • (c p.1 • dy j (dy k ψ) p) = c p.1 • (ν • dy j (dy k ψ) p)
  exact smul_comm _ _ _

/-- **Partition of unity in `τ`** (source 1437-1441; Hessian analogue of `windowLapPoU`). -/
theorem windowHessPoU : WindowHessPoU := by
  unfold WindowHessPoU
  intro ν j k W H Hk hWin hΛ τ₀
  -- a smooth partition of unity in `τ`, subordinate to the windows `(n-1, n+1)`, `n ∈ ℤ`
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ, ℝ))
    (s := (univ : Set ℝ)) isClosed_univ (fun n : ℤ => Ioo ((n : ℝ) - 1) ((n : ℝ) + 1))
    (fun n => isOpen_Ioo) (by
      intro t _
      simp only [mem_iUnion, mem_Ioo]
      exact ⟨⌊t⌋, by linarith [Int.floor_le t], by linarith [Int.lt_floor_add_one t]⟩)
  obtain ⟨F, hF⟩ : ∃ F : Finset ℤ, ∀ n : ℤ, n ∈ F ↔ ⌊τ₀⌋ - 1 ≤ n ∧ n ≤ ⌊τ₀⌋ + 2 :=
    ⟨Finset.Icc (⌊τ₀⌋ - 1) (⌊τ₀⌋ + 2), fun n => Finset.mem_Icc⟩
  -- the partition is supported in the four windows meeting `winSet τ₀`
  have hzero : ∀ n : ℤ, n ∉ F → ∀ τ ∈ Ioo (τ₀ - 1) (τ₀ + 1), f n τ = 0 := by
    intro n hn τ hτ
    apply image_eq_zero_of_notMem_tsupport (f := fun τ => f n τ)
    intro hmem
    obtain ⟨h3, h4⟩ := hf n hmem
    obtain ⟨h1, h2⟩ := hτ
    apply hn
    rw [hF]
    have hA : (n : ℝ) < (⌊τ₀⌋ : ℝ) + 3 := by linarith [Int.lt_floor_add_one τ₀]
    have hB : (⌊τ₀⌋ : ℝ) - 2 < (n : ℝ) := by linarith [Int.floor_le τ₀]
    have hA' : n < ⌊τ₀⌋ + 3 := by exact_mod_cast hA
    have hB' : ⌊τ₀⌋ - 2 < n := by exact_mod_cast hB
    constructor <;> omega
  have hF1 : ∀ τ ∈ Ioo (τ₀ - 1) (τ₀ + 1), ∑ n ∈ F, f n τ = 1 := by
    intro τ hτ
    have hsupp : Function.support (fun n : ℤ => f n τ) ⊆ (F : Set ℤ) := by
      intro n hn'
      by_contra hnF
      exact (Function.mem_support.mp hn') (hzero n (fun h => hnF (Finset.mem_coe.mpr h)) τ hτ)
    rw [← f.sum_eq_one (mem_univ τ), finsum_eq_sum_of_support_subset (fun n : ℤ => f n τ) hsupp]
  have hpart : ∀ v : ℝ × Space → CVec3, (∀ p, p ∉ winSet τ₀ → v p = 0) →
      ∀ p, ∑ n ∈ F, f n p.1 • v p = v p := by
    intro v hv p
    by_cases hp : p ∈ winSet τ₀
    · rw [← Finset.sum_smul, hF1 p.1 hp.1, one_smul]
    · rw [hv p hp]
      simp
  unfold IsWindowHess
  intro ψ hψ hψc hψs
  have hψ0 : ∀ p, p ∉ winSet τ₀ → ψ p = 0 := fun p hp =>
    image_eq_zero_of_notMem_tsupport (f := ψ) (fun h => hp (hψs h))
  have hL0 : ∀ p, p ∉ winSet τ₀ → nuHessT ν j k ψ p = 0 := fun p hp =>
    hsPoU_hess_eq_zero ν j k (fun h => hp (hψs h))
  have hfsm : ∀ n : ℤ, ContDiff ℝ ∞ (fun τ : ℝ => f n τ) := fun n =>
    contMDiff_iff_contDiff.mp (f n).contMDiff
  have hψn : ∀ n : ℤ, ContDiff ℝ ∞ (fun p : ℝ × Space => f n p.1 • ψ p) := fun n =>
    ((hfsm n).comp contDiff_fst).smul hψ
  have hψnc : ∀ n : ℤ, HasCompactSupport (fun p : ℝ × Space => f n p.1 • ψ p) := fun n =>
    hψc.smul_left (f := fun p : ℝ × Space => f n p.1)
  have hψns : ∀ n : ℤ, tsupport (fun p : ℝ × Space => f n p.1 • ψ p) ⊆ winSet (n : ℝ) :=
    fun n => (tsupport_smul_subset_left (fun p : ℝ × Space => f n p.1) ψ).trans
      (UnforcedLeray.Short.PartIIa.tsupport_cut_fst (f n) (Ioo ((n : ℝ) - 1) ((n : ℝ) + 1)) (hf n))
  have hLn : ∀ n : ℤ, nuHessT ν j k (fun p : ℝ × Space => f n p.1 • ψ p) =
      fun p => f n p.1 • nuHessT ν j k ψ p := fun n =>
    hsPoU_hess_cut_smul ν j k (fun τ => f n τ) (hfsm n) hψ
  have hI : ∀ n : ℤ,
      Integrable (fun p => dotL (W p) (f n p.1 • nuHessT ν j k ψ p)) ∧
      Integrable (fun p => dotL (Hk n p) (f n p.1 • ψ p)) ∧
      ∫ p, dotL (W p) (f n p.1 • nuHessT ν j k ψ p) =
        ∫ p, dotL (Hk n p) (f n p.1 • ψ p) := by
    intro n
    obtain ⟨h1, h2, h3⟩ := hWin n _ (hψn n) (hψnc n) (hψns n)
    rw [hLn n] at h1 h3
    exact ⟨h1, h2, h3⟩
  have hz : ∀ n : ℤ, ∀ p, p ∉ winSet (n : ℝ) → f n p.1 • ψ p = 0 := fun n p hp =>
    image_eq_zero_of_notMem_tsupport (f := fun p => f n p.1 • ψ p) (fun h => hp (hψns n h))
  have hae : ∀ n : ℤ, (fun p => dotL (H p) (f n p.1 • ψ p)) =ᵐ[volume]
      fun p => dotL (Hk n p) (f n p.1 • ψ p) :=
    fun n => UnforcedLeray.Short.PartIIa.ae_dotL_congr_of_restrict
      (UnforcedLeray.Short.PartIIa.measurableSet_winSet' _) (hΛ n) (hz n)
  have hIH : ∀ n : ℤ, Integrable (fun p => dotL (H p) (f n p.1 • ψ p)) :=
    fun n => (hI n).2.1.congr (hae n).symm
  have hsumψ : ∀ p, ∑ n ∈ F, f n p.1 • ψ p = ψ p := hpart ψ hψ0
  have hsumv : ∀ p, ∑ n ∈ F, f n p.1 • nuHessT ν j k ψ p = nuHessT ν j k ψ p :=
    hpart (nuHessT ν j k ψ) hL0
  have hA : (fun p => dotL (W p) (nuHessT ν j k ψ p)) =
      fun p => ∑ n ∈ F, dotL (W p) (f n p.1 • nuHessT ν j k ψ p) := by
    funext p
    conv_lhs => rw [← hsumv p]
    rw [map_sum]
  have hB : (fun p => dotL (H p) (ψ p)) = fun p => ∑ n ∈ F, dotL (H p) (f n p.1 • ψ p) := by
    funext p
    conv_lhs => rw [← hsumψ p]
    rw [map_sum]
  refine ⟨?_, ?_, ?_⟩
  · rw [hA]
    exact integrable_finsetSum F (fun n _ => (hI n).1)
  · rw [hB]
    exact integrable_finsetSum F (fun n _ => hIH n)
  · rw [hA, hB, integral_finsetSum F (fun n _ => (hI n).1),
      integral_finsetSum F (fun n _ => hIH n)]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    exact (hI n).2.2.trans (integral_congr_ae (hae n).symm)

end UnforcedLeray.Short.PartIIIb.Concrete
