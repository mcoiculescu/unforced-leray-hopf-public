import UnforcedLeray.Short.PartI.Sub.PartI_TrainHeatFixed
import UnforcedLeray.Short.PartI.Tasks.TrainHeatFixed.JointFromAgeJets.Calc

/-!
# Part I, task `PartI:HF/3`, target `jointFromAgeJets`: the full derivative from the age jets

Source of record: `the November 2 reference manuscript`, lines 427-435 (fixed
parameters; the derivative budget is not restricted). The Prop is `JointFromAgeJets` in
`Sub/PartI_TrainHeatFixed.lean` (A3, generic calculus).

Proof. Expand the `i`-th derivative of `(s, z) ↦ F s z` on the three coordinate words
`s, q, η` (`norm_iteratedFDeriv_le_sum3`, `3^i` words). Each word, after permutation (`dW_perm`,
symmetry of second derivatives), is the plane derivative of order `i - ℓ` of the slice
`z ↦ ∂_s^ℓ F(s, z)`, where `ℓ` is the number of `s`-letters. That slice derivative is
`ageJet ℓ (i - ℓ) F s z` by definition (`jet` is `iteratedFDeriv`). So each word term is at most
the sum over `ℓ`, and `K = 3^i`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Short.PartI.AgeDeriv
open UnforcedLeray.Cyl (Plane)

/-- One coordinate word: its value is at most the sum of the age-jet norms. -/
theorem jointFromAgeJets_word (i : ℕ) (F : ℝ → Plane → ℝ)
    (hF : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => F x.1 x.2) (Ioi 0 ×ˢ univ))
    (y : ℝ × Plane) (hy : 0 < y.1) (r : Fin i → Fin 3) :
    |iteratedFDeriv ℝ i (fun x : ℝ × Plane => F x.1 x.2) y (fun k => LL (r k))| ≤
      ∑ ℓ ∈ Finset.range (i + 1), ‖ageJet ℓ (i - ℓ) F y.1 y.2‖ := by
  rcases y with ⟨s, z⟩
  dsimp only at hy ⊢
  obtain ⟨lb, hlb⟩ : ∃ lb : List (Fin 3), lb = List.ofFn r := ⟨_, rfl⟩
  obtain ⟨ps, hps⟩ : ∃ ps : List (Fin 3), ps = lb.filter (fun c => c != 0) := ⟨_, rfl⟩
  obtain ⟨qs, hqs⟩ : ∃ qs : List (Fin 3), qs = lb.filter (fun c => !(c != 0)) := ⟨_, rfl⟩
  have hperm0 : lb.Perm (ps ++ qs) := by
    rw [hps, hqs]
    exact (List.filter_append_perm (fun c : Fin 3 => c != 0) lb).symm
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℕ, ℓ = qs.length := ⟨_, rfl⟩
  have hqs0 : qs = List.replicate ℓ 0 := by
    rw [hℓ, List.eq_replicate_iff]
    refine ⟨rfl, fun b hb => ?_⟩
    rw [hqs, List.mem_filter] at hb
    simpa using hb.2
  have hlen : ps.length + ℓ = i := by
    have h := hperm0.length_eq
    simp only [List.length_append, hlb, List.length_ofFn] at h
    rw [hℓ]
    omega
  have hw1 : (List.ofFn fun k => LL (r k)) = lb.map LL := by
    rw [hlb, List.map_ofFn]
    rfl
  have hperm1 : (lb.map LL).Perm (ps.map LL ++ List.replicate ℓ (LL 0)) := by
    have h := hperm0.map LL
    rw [List.map_append, hqs0, List.map_replicate] at h
    exact h
  have hmem : ((s, z) : ℝ × Plane) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) := ⟨hy, mem_univ _⟩
  have hchain : iteratedFDeriv ℝ i (fun x : ℝ × Plane => F x.1 x.2) (s, z)
      (fun k => LL (r k)) =
      dW (ps.map LL) (dW (List.replicate ℓ (LL 0)) (fun x : ℝ × Plane => F x.1 x.2)) (s, z) := by
    rw [← dW_ofFn_eq isOpen_halfPlane3 hF i (fun k => LL (r k)) (s, z) hmem, hw1,
      dW_perm isOpen_halfPlane3 hF hperm1 (s, z) hmem, dW_append]
  have hKU : ContDiffOn ℝ ∞ (dW (List.replicate ℓ (LL 0)) (fun x : ℝ × Plane => F x.1 x.2))
      (Ioi 0 ×ˢ (univ : Set (ℝ × ℝ))) :=
    dW_contDiffOn isOpen_halfPlane3 hF _
  obtain ⟨pv, hpv⟩ : ∃ pv : Fin 3 → ℝ × ℝ, pv = ![(0, 0), (1, 0), (0, 1)] := ⟨_, rfl⟩
  have hpsmap : ps.map LL = (ps.map pv).map (fun v => ((0 : ℝ), v)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro c hc
    rw [hps, List.mem_filter] at hc
    have hc0 : c ≠ 0 := by
      intro h
      simp [h] at hc
    fin_cases c
    · exact absurd rfl hc0
    · first | rfl | simp [LL, hpv]
    · first | rfl | simp [LL, hpv]
  have hnorm : ∀ v ∈ ps.map pv, ‖v‖ ≤ 1 := by
    intro v hv
    obtain ⟨c, _, rfl⟩ := List.mem_map.1 hv
    rw [hpv]
    fin_cases c <;> simp [Prod.norm_def]
  have hHc : ContDiffOn ℝ ∞ (fun z' : ℝ × ℝ => dW (List.replicate ℓ (LL 0))
      (fun x : ℝ × Plane => F x.1 x.2) (s, z')) univ := by
    have hf : ContDiffOn ℝ ∞ (fun z' : ℝ × ℝ => ((s : ℝ), z')) univ :=
      (contDiff_const.prodMk contDiff_id).contDiffOn
    exact hKU.comp hf (fun _ _ => ⟨hy, mem_univ _⟩)
  have hH : (fun z' : ℝ × ℝ => dW (List.replicate ℓ (LL 0))
      (fun x : ℝ × Plane => F x.1 x.2) (s, z')) =
      (fun z' : ℝ × ℝ => iteratedDeriv ℓ (fun r => F r z') s) := by
    funext z'
    exact dW_rep_s hF ℓ z' s hy
  rw [hH] at hHc
  rw [hchain, hpsmap, dW_plane_word hKU (ps.map pv) s hy z, hH]
  have hb := dW_plane_bound hHc (i - ℓ) (ps.map pv) z
    (by rw [List.length_map]; omega) (fun v hv => hnorm v hv)
  have hag : ‖iteratedFDeriv ℝ (i - ℓ) (fun z' : ℝ × ℝ => iteratedDeriv ℓ (fun r => F r z') s) z‖
      = ‖ageJet ℓ (i - ℓ) F s z‖ := rfl
  have hmemℓ : ℓ ∈ Finset.range (i + 1) := Finset.mem_range.2 (by omega)
  calc |dW (ps.map pv) (fun z' : ℝ × ℝ => iteratedDeriv ℓ (fun r => F r z') s) z|
      ≤ ‖iteratedFDeriv ℝ (i - ℓ) (fun z' : ℝ × ℝ => iteratedDeriv ℓ (fun r => F r z') s) z‖ := hb
    _ = ‖ageJet ℓ (i - ℓ) F s z‖ := hag
    _ ≤ ∑ ℓ' ∈ Finset.range (i + 1), ‖ageJet ℓ' (i - ℓ') F s z‖ :=
        Finset.single_le_sum (f := fun ℓ' => ‖ageJet ℓ' (i - ℓ') F s z‖)
          (fun _ _ => norm_nonneg _) hmemℓ

/-- **Target** `jointFromAgeJets`: the full derivative from the age jets (`JointFromAgeJets`). -/
theorem jointFromAgeJets : UnforcedLeray.Short.PartI.JointFromAgeJets := by
  intro i
  refine ⟨3 ^ i, by positivity, ?_⟩
  intro F hF y hy
  calc ‖iteratedFDeriv ℝ i (fun x : ℝ × Plane => F x.1 x.2) y‖
      ≤ ∑ r : Fin i → Fin 3, |iteratedFDeriv ℝ i (fun x : ℝ × Plane => F x.1 x.2) y
          (fun k => LL (r k))| := norm_iteratedFDeriv_le_sum3 _ i y
    _ ≤ ∑ r : Fin i → Fin 3, ∑ ℓ ∈ Finset.range (i + 1), ‖ageJet ℓ (i - ℓ) F y.1 y.2‖ :=
        Finset.sum_le_sum (fun r _ => jointFromAgeJets_word i F hF y hy r)
    _ = 3 ^ i * ∑ ℓ ∈ Finset.range (i + 1), ‖ageJet ℓ (i - ℓ) F y.1 y.2‖ := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end UnforcedLeray.Short.PartI
