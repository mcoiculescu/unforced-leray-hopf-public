import Mathlib.Data.Set.Finite.List
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.Sub.PartIIIa_T21_2_7_2_1_2_1_3

/-!
# `PartIII-a` leaf (iii): `TimeJetXNormBdd`

Source of record: `the November 2 reference manuscript` (SP) lines 3060-3061.

Proof route. For each `j` the weak adjoint jets `Φ j` are in `AdjHkOn c m k (Ico t s)`, so they carry
cell-jet fields `D j r w` with `r ↦ xNorm (D j r w)` finite and locally bounded within `Ico t s`
(triangle inequality and the `Tendsto` of `AdjHkOn`). On the compact `Icc t (t + (s - t)/2) ⊆ Ico t s`
the finite sum `Σ_{(j, w) ∈ P} xNorm (D j r w)` over `j ≤ n` and `|w| ≤ k` is therefore bounded
(compactness through a finite subcover), and each term is at most this sum.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- A set-valued function locally bounded within `I` at every point of a compact `K ⊆ I` is bounded
on `K` (finite subcover of `K` by neighbourhoods on which the bound holds within `I`). -/
theorem uniform_of_local_bdd {I K : Set ℝ} {F : ℝ → ℝ≥0∞} (hK : IsCompact K) (hKI : K ⊆ I)
    (hloc : ∀ r ∈ K, ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ᶠ r' in 𝓝[I] r, F r' ≤ B) :
    ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ r ∈ K, F r ≤ B := by
  have hcov : ∀ r : K, ∃ u : Set ℝ, IsOpen u ∧ (r : ℝ) ∈ u ∧
      ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ r' ∈ u, r' ∈ I → F r' ≤ B := by
    rintro ⟨r, hr⟩
    obtain ⟨B, hB, hev⟩ := hloc r hr
    rw [eventually_nhdsWithin_iff, eventually_nhds_iff] at hev
    obtain ⟨u, hu, huo, hru⟩ := hev
    exact ⟨u, huo, hru, B, hB, fun r' h1 h2 => hu r' h1 h2⟩
  choose U hUo hUr B hB hUB using hcov
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover (fun i : K => U i) (fun i => hUo i)
    (fun r hr => Set.mem_iUnion.2 ⟨⟨r, hr⟩, hUr ⟨r, hr⟩⟩)
  refine ⟨∑ i ∈ T, B i, ?_, ?_⟩
  · exact ENNReal.sum_lt_top.2 (fun i _ => hB i)
  · intro r hr
    obtain ⟨i, hiT, hri⟩ := Set.mem_iUnion₂.1 (hT hr)
    exact (hUB i r hri (hKI hr)).trans (Finset.single_le_sum (f := B) (fun _ _ => bot_le) hiT)

theorem timeJetXNormBdd : UnforcedLeray.Short.IIIa.TimeJetXNormBdd := by
  intro c m t s Φ hts hΦ k n
  have hA : ∀ j : ℕ, ∃ D : ℝ → List (Fin 2) → ℝ × ℝ → ℂ,
      (∀ r ∈ Ico t s, IsCellJet c m k (Φ j r) (D r)) ∧
        ∀ w : List (Fin 2), w.length ≤ k → ∀ r ∈ Ico t s,
          Tendsto (fun r' => xNorm c (-m) (D r' w - D r w)) (𝓝[Ico t s] r) (𝓝 0) :=
    fun j => hΦ.1 j k
  choose D hDc hDT using hA
  have hWfin : {w : List (Fin 2) | w.length ≤ k}.Finite := List.finite_length_le (Fin 2) k
  have hPmem : ∀ p ∈ Finset.range (n + 1) ×ˢ hWfin.toFinset, p.2.length ≤ k := fun p hp =>
    (Set.Finite.mem_toFinset hWfin).1 (Finset.mem_product.1 hp).2
  have hloc : ∀ r ∈ Icc t (t + (s - t) / 2), ∃ B : ℝ≥0∞, B < ⊤ ∧
      ∀ᶠ r' in 𝓝[Ico t s] r, (∑ p ∈ Finset.range (n + 1) ×ˢ hWfin.toFinset,
        xNorm c (-m) (D p.1 r' p.2)) ≤ B := by
    intro r hr
    have hrI : r ∈ Ico t s := ⟨hr.1, by linarith [hr.2, hts]⟩
    have hterm : ∀ p ∈ Finset.range (n + 1) ×ˢ hWfin.toFinset,
        ∀ᶠ r' in 𝓝[Ico t s] r, xNorm c (-m) (D p.1 r' p.2) ≤ xNorm c (-m) (D p.1 r p.2) + 1 := by
      intro p hp
      have hpw : p.2.length ≤ k := hPmem p hp
      have hlt := (hDT p.1 p.2 hpw r hrI).eventually_lt_const (zero_lt_one : (0 : ℝ≥0∞) < 1)
      filter_upwards [hlt, self_mem_nhdsWithin] with r' hr1 hr'I
      have hm1 := ((hDc p.1 r' hr'I).memX p.2 hpw).aestronglyMeasurable
      have hm2 := ((hDc p.1 r hrI).memX p.2 hpw).aestronglyMeasurable
      have htri : xNorm c (-m) (D p.1 r' p.2) ≤
          xNorm c (-m) (D p.1 r' p.2 - D p.1 r p.2) + xNorm c (-m) (D p.1 r p.2) := by
        unfold xNorm
        have h := eLpNorm_add_le (hm1.sub hm2) hm2 (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        rwa [sub_add_cancel] at h
      calc xNorm c (-m) (D p.1 r' p.2)
          ≤ xNorm c (-m) (D p.1 r' p.2 - D p.1 r p.2) + xNorm c (-m) (D p.1 r p.2) := htri
        _ ≤ 1 + xNorm c (-m) (D p.1 r p.2) := add_le_add hr1.le le_rfl
        _ = xNorm c (-m) (D p.1 r p.2) + 1 := add_comm _ _
    have hall := (Filter.eventually_all_finset (Finset.range (n + 1) ×ˢ hWfin.toFinset)).2 hterm
    refine ⟨∑ p ∈ Finset.range (n + 1) ×ˢ hWfin.toFinset, (xNorm c (-m) (D p.1 r p.2) + 1), ?_, ?_⟩
    · rw [ENNReal.sum_lt_top]
      intro p hp
      have hfin : xNorm c (-m) (D p.1 r p.2) < ⊤ := by
        unfold xNorm
        exact ((hDc p.1 r hrI).memX p.2 (hPmem p hp)).eLpNorm_lt_top
      exact ENNReal.add_lt_top.2 ⟨hfin, ENNReal.one_lt_top⟩
    · filter_upwards [hall] with r' hr'
      exact Finset.sum_le_sum (fun p hp => hr' p hp)
  have hKI : Icc t (t + (s - t) / 2) ⊆ Ico t s := fun r hr =>
    ⟨hr.1, by linarith [hr.2, hts]⟩
  obtain ⟨Bt, hBt, hB⟩ := uniform_of_local_bdd (I := Ico t s) (K := Icc t (t + (s - t) / 2))
    (F := fun r' => ∑ p ∈ Finset.range (n + 1) ×ˢ hWfin.toFinset, xNorm c (-m) (D p.1 r' p.2))
    isCompact_Icc hKI hloc
  refine ⟨Bt.toReal, fun j hj => ⟨D j, hDc j, fun w hw r hr => ?_⟩⟩
  have hrK : r ∈ Icc t (t + (s - t) / 2) := ⟨hr.1.le, hr.2.le⟩
  have hmem : (j, w) ∈ Finset.range (n + 1) ×ˢ hWfin.toFinset :=
    Finset.mem_product.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le hj), (Set.Finite.mem_toFinset hWfin).2 hw⟩
  have hsum := Finset.single_le_sum (f := fun p : ℕ × List (Fin 2) => xNorm c (-m) (D p.1 r p.2))
    (fun _ _ => bot_le) hmem
  exact (hsum.trans (hB r hrK)).trans_eq (ENNReal.ofReal_toReal hBt.ne).symm

end UnforcedLeray.Short.IIIa
