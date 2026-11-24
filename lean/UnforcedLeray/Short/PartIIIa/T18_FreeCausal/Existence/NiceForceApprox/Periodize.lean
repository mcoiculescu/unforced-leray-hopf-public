import UnforcedLeray.Short.PartIIIa.Sub.T18_2_3

/-!
# Part III-a, task `PartIII-a:T18/2/3/4`: periodization (`nicePeriodize`)

Proves `NicePeriodize` (`Sub/T18_2_3.lean`; SP 3427-3440, source of record
`the November 2 reference manuscript`, lines 3427-3440).

Route. The reduction of `q` to the cell is `toIcoMod hc (-(c/2)) q` (Mathlib's reduction into
`Ico (-(c/2)) (c/2)`), and `G'(s,(q,η)) := G(s,(toIcoMod q, η))`.
* Periodicity and equality on the cell are `toIcoMod_add_right` and `toIcoMod_eq_self`.
* Vanishing: `a = α'`, `B = β'`, `R = R'`; the `s` and `η` coordinates are unchanged.
* Smoothness (`periodize_contDiff`), at each point `p0`. Choose `z` with `q0 - z c ∈ Ico`.
  - Interior case `q0 - z c > -c/2`: near `p0` the reduction is the translation `q ↦ q - z c`.
  - Cut case `q0 - z c = -c/2`: on `|q - q0| < δ` (with `δ ≤ c/2 - r'`, `δ ≤ c`) the reduced
    coordinate satisfies `r' < |toIcoMod q|`, so `G' = 0` near `p0` (support of `G` in `|q| ≤ r'`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Every real `q` differs from a point of `Ico (-(c/2)) (c/2)` by an integer multiple of `c`. -/
theorem periodize_exists_reduce {c : ℝ} (hc : 0 < c) (q : ℝ) :
    ∃ z : ℤ, q - (z : ℝ) * c ∈ Set.Ico (-(c / 2)) (c / 2) := by
  refine ⟨toIcoDiv hc (-(c / 2)) q, ?_⟩
  have h := sub_toIcoDiv_zsmul_mem_Ico hc (-(c / 2)) q
  rw [zsmul_eq_mul] at h
  have h2 : -(c / 2) + c = c / 2 := by ring
  rw [h2] at h
  exact h

/-- If `q - z c` already lies in `Ico (-(c/2)) (c/2)`, then it is the reduction of `q`. -/
theorem periodize_toIcoMod_eq {c : ℝ} (hc : 0 < c) (q : ℝ) (z : ℤ)
    (h : q - (z : ℝ) * c ∈ Set.Ico (-(c / 2)) (c / 2)) :
    toIcoMod hc (-(c / 2)) q = q - (z : ℝ) * c := by
  have h2 : -(c / 2) + c = c / 2 := by ring
  rw [toIcoMod_eq_iff, h2]
  refine ⟨h, z, ?_⟩
  rw [zsmul_eq_mul]
  ring

/-- Smoothness of the reduced field, for one scalar component `G : ℝ × (ℝ × ℝ) → ℂ` that is
smooth and vanishes wherever `|q| > r'` (with `r' < c/2`). -/
theorem periodize_contDiff {c r' : ℝ} (hc : 0 < c) (hr : r' < c / 2)
    (G : ℝ × (ℝ × ℝ) → ℂ) (hG : ContDiff ℝ ∞ G)
    (hG0 : ∀ (s : ℝ) (x : ℝ × ℝ), r' < |x.1| → G (s, x) = 0) :
    ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => G (p.1, (toIcoMod hc (-(c / 2)) p.2.1, p.2.2))) := by
  rw [contDiff_iff_contDiffAt]
  intro p0
  obtain ⟨z, hz⟩ := periodize_exists_reduce hc p0.2.1
  rcases (Set.mem_Ico.mp hz).1.lt_or_eq with hlt | heq
  · -- interior case: near `p0` the reduction is the translation `q ↦ q - z c`
    have hcont : Continuous fun p : ℝ × (ℝ × ℝ) => p.2.1 - (z : ℝ) * c := by fun_prop
    have hU : IsOpen ((fun p : ℝ × (ℝ × ℝ) => p.2.1 - (z : ℝ) * c) ⁻¹'
        Set.Ioo (-(c / 2)) (c / 2)) :=
      isOpen_Ioo.preimage hcont
    have hp0 : p0.2.1 - (z : ℝ) * c ∈ Set.Ioo (-(c / 2)) (c / 2) :=
      Set.mem_Ioo.mpr ⟨hlt, (Set.mem_Ico.mp hz).2⟩
    have hp0' : p0 ∈ (fun p : ℝ × (ℝ × ℝ) => p.2.1 - (z : ℝ) * c) ⁻¹'
        Set.Ioo (-(c / 2)) (c / 2) := hp0
    have hT : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => (p.1, (p.2.1 - (z : ℝ) * c, p.2.2))) := by
      fun_prop
    have hGc : ContDiff ℝ ∞
        (fun p : ℝ × (ℝ × ℝ) => G (p.1, (p.2.1 - (z : ℝ) * c, p.2.2))) :=
      hG.comp hT
    refine hGc.contDiffAt.congr_of_eventuallyEq ?_
    refine Filter.eventually_of_mem (hU.mem_nhds hp0') ?_
    intro p hp
    have hpI : p.2.1 - (z : ℝ) * c ∈ Set.Ico (-(c / 2)) (c / 2) :=
      Set.Ioo_subset_Ico_self (Set.mem_preimage.mp hp)
    show G (p.1, (toIcoMod hc (-(c / 2)) p.2.1, p.2.2)) = G (p.1, (p.2.1 - (z : ℝ) * c, p.2.2))
    rw [periodize_toIcoMod_eq hc p.2.1 z hpI]
  · -- cut case: `q0 - z c = -c/2`; `G'` vanishes on a neighbourhood of `p0`
    obtain ⟨δ, hδpos, hδ1, hδ2⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ c / 2 - r' ∧ δ ≤ c :=
      ⟨min (c / 2 - r') c, lt_min (by linarith) hc, min_le_left _ _, min_le_right _ _⟩
    have hq0eq : p0.2.1 - (z : ℝ) * c = -(c / 2) := heq.symm
    have hcont : Continuous fun p : ℝ × (ℝ × ℝ) => p.2.1 := by fun_prop
    have hU : IsOpen ((fun p : ℝ × (ℝ × ℝ) => p.2.1) ⁻¹'
        Set.Ioo (p0.2.1 - δ) (p0.2.1 + δ)) :=
      isOpen_Ioo.preimage hcont
    have hp0 : p0.2.1 ∈ Set.Ioo (p0.2.1 - δ) (p0.2.1 + δ) :=
      Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
    have hp0' : p0 ∈ (fun p : ℝ × (ℝ × ℝ) => p.2.1) ⁻¹' Set.Ioo (p0.2.1 - δ) (p0.2.1 + δ) :=
      hp0
    have key : ∀ q : ℝ, q ∈ Set.Ioo (p0.2.1 - δ) (p0.2.1 + δ) →
        r' < |toIcoMod hc (-(c / 2)) q| := by
      intro q hq
      obtain ⟨hq1, hq2⟩ := Set.mem_Ioo.mp hq
      rcases lt_or_ge q p0.2.1 with hlt' | hge'
      · -- `q` left of `q0`: reduce with the integer `z - 1`, the reduced value is near `c/2`
        have e1 : q - ((z - 1 : ℤ) : ℝ) * c = (q - p0.2.1) + c / 2 := by
          push_cast
          linear_combination hq0eq
        have hI : q - ((z - 1 : ℤ) : ℝ) * c ∈ Set.Ico (-(c / 2)) (c / 2) := by
          rw [e1]
          exact Set.mem_Ico.mpr ⟨by linarith, by linarith⟩
        rw [periodize_toIcoMod_eq hc q (z - 1) hI, e1]
        exact lt_of_lt_of_le (by linarith) (le_abs_self _)
      · -- `q` right of `q0`: reduce with the integer `z`, the reduced value is near `-c/2`
        have e2 : q - (z : ℝ) * c = (q - p0.2.1) - c / 2 := by
          linear_combination hq0eq
        have hI : q - (z : ℝ) * c ∈ Set.Ico (-(c / 2)) (c / 2) := by
          rw [e2]
          exact Set.mem_Ico.mpr ⟨by linarith, by linarith⟩
        rw [periodize_toIcoMod_eq hc q z hI, e2]
        exact lt_abs.mpr (Or.inr (by linarith))
    refine (contDiffAt_const :
      ContDiffAt ℝ ∞ (fun _ : ℝ × (ℝ × ℝ) => (0 : ℂ)) p0).congr_of_eventuallyEq ?_
    refine Filter.eventually_of_mem (hU.mem_nhds hp0') ?_
    intro p hp
    have hp' : p.2.1 ∈ Set.Ioo (p0.2.1 - δ) (p0.2.1 + δ) := Set.mem_preimage.mp hp
    show G (p.1, (toIcoMod hc (-(c / 2)) p.2.1, p.2.2)) = 0
    exact hG0 p.1 (toIcoMod hc (-(c / 2)) p.2.1, p.2.2) (key p.2.1 hp')

/-- **Periodization** (`PartIII-a:T18/2/3/4`; SP 3427-3440). Let `0 < c`, `r' < c/2` and let `G` be a
symmetric `C^∞` tensor field vanishing outside the box `α' ≤ s ≤ β'`, `|q| ≤ r'`, `|η| ≤ R'`
(`α' > 0`). Then there is a nice force `G'` (symmetric, `C^∞`, `c`-periodic in `q`, vanishing for
`s ∉ [a, B]`, `a > 0`, and `|η| > R`) with `G' = G` on `(ℝ × cell)` and `G' = 0` for `s < α'`.
Proof: `G'(s, (q, η)) = G(s, (toIcoMod hc (-c/2) q, η))`; the cell and periodicity clauses follow
from `toIcoMod` algebra, and smoothness is `periodize_contDiff`. -/
theorem nicePeriodize : UnforcedLeray.Short.IIIa.NicePeriodize := by
  unfold NicePeriodize
  intro c α' β' r' R' hc hα hr G hsym hsmooth hvan
  refine ⟨fun p i j => G (p.1, (toIcoMod hc (-(c / 2)) p.2.1, p.2.2)) i j, ?_, ?_, ?_⟩
  · unfold NiceForce
    refine ⟨?_, ?_, ?_, α', β', R', hα, ?_⟩
    · intro p i j
      exact hsym (p.1, (toIcoMod hc (-(c / 2)) p.2.1, p.2.2)) i j
    · intro i j
      exact periodize_contDiff hc hr (fun p => G p i j) (hsmooth i j)
        (fun s x h => hvan s x i j (Or.inr (Or.inr (Or.inl h))))
    · intro s x i j
      show G (s, (toIcoMod hc (-(c / 2)) (x.1 + c), x.2)) i j
          = G (s, (toIcoMod hc (-(c / 2)) x.1, x.2)) i j
      rw [toIcoMod_add_right hc]
    · intro s x i j h
      show G (s, (toIcoMod hc (-(c / 2)) x.1, x.2)) i j = 0
      rcases h with h1 | h2 | h3
      · exact hvan s (toIcoMod hc (-(c / 2)) x.1, x.2) i j (Or.inl h1)
      · exact hvan s (toIcoMod hc (-(c / 2)) x.1, x.2) i j (Or.inr (Or.inl h2))
      · exact hvan s (toIcoMod hc (-(c / 2)) x.1, x.2) i j (Or.inr (Or.inr (Or.inr h3)))
  · intro s x i j hx
    have hx' : x ∈ Set.Ico (-(c / 2)) (c / 2) ×ˢ (Set.univ : Set ℝ) := hx
    have hxI : x.1 ∈ Set.Ico (-(c / 2)) (c / 2) := (Set.mem_prod.mp hx').1
    have h2 : -(c / 2) + c = c / 2 := by ring
    have hfix : toIcoMod hc (-(c / 2)) x.1 = x.1 :=
      (toIcoMod_eq_self hc).mpr (by rw [h2]; exact hxI)
    show G (s, (toIcoMod hc (-(c / 2)) x.1, x.2)) i j = G (s, x) i j
    rw [hfix]
  · intro s x i j hs
    show G (s, (toIcoMod hc (-(c / 2)) x.1, x.2)) i j = 0
    exact hvan s (toIcoMod hc (-(c / 2)) x.1, x.2) i j (Or.inl hs)

end UnforcedLeray.Short.IIIa
