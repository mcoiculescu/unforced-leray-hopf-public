import UnforcedLeray.Loc.L03Evolution.Free
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# L3 helper: strong continuity of `S₀` on `Z` at `0` from its boundedness

`paper/main.tex` lines 292–300 (blueprint units B0712, B0713). The `Z`-valued Volterra
iteration of step L3 needs `S₀(t) g → g` in `Z = H²_div` as `t → 0⁺`. This file derives it
from the short-time bound `‖S₀(t)‖_{Z→Z} ≤ C` (`0 < t ≤ 1`) alone, by a Hilbert-space
argument:

* the set `G` of `g ∈ Z` with `S₀(t) g → g` is a closed subspace (uniform bound), and contains
  `S₀(t) Z` for every `t > 0` (continuity of `S₀ : X → Z` at positive times);
* `S₀(t) g → g` weakly in `Z`: tested against `ι_Z^* x`, the pairing is
  `⟪x, S₀(t) ι_Z g⟫_X → ⟪x, ι_Z g⟫_X`, and `ι_Z^*(X)` is dense in `Z` since `ι_Z` is injective;
* hence `Gᗮ = 0`, so `G = Z`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Loc.L03Evolution

open UnforcedLeray.Blueprint

/-- For a family of operators eventually bounded along `l`, the set of vectors `g` with
`A(t) g → g` along `l` is closed. -/
theorem isClosed_setOf_tendsto_self {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {l : Filter ℝ} {A : ℝ → E →L[ℝ] E} {C : ℝ} (hA : ∀ᶠ t in l, ‖A t‖ ≤ C) :
    IsClosed {g : E | Tendsto (fun t => A t g) l (𝓝 g)} := by
  refine isClosed_of_closure_subset fun g hg => ?_
  rw [Metric.mem_closure_iff] at hg
  show Tendsto (fun t => A t g) l (𝓝 g)
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨C', hC'0, hC'⟩ : ∃ C', 0 < C' ∧ C ≤ C' :=
    ⟨max C 0 + 1, by positivity, by linarith [le_max_left C 0]⟩
  obtain ⟨b, hb, hgb⟩ := hg (ε / (2 * (C' + 1))) (by positivity)
  have hb' : ∀ᶠ t in l, dist (A t b) b < ε / 2 :=
    Metric.tendsto_nhds.mp hb (ε / 2) (half_pos hε)
  filter_upwards [hb', hA] with t ht1 ht2
  have h1 : dist (A t g) (A t b) ≤ C' * dist g b := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (ht2.trans hC') (norm_nonneg _))
  have h2 : dist b g = dist g b := dist_comm _ _
  have hlt : (C' + 1) * dist g b < ε / 2 := by
    calc (C' + 1) * dist g b < (C' + 1) * (ε / (2 * (C' + 1))) :=
          mul_lt_mul_of_pos_left hgb (by linarith)
      _ = ε / 2 := by field_simp
  rw [add_mul, one_mul] at hlt
  calc dist (A t g) g ≤ dist (A t g) (A t b) + dist (A t b) b + dist b g :=
        dist_triangle4 _ _ _ _
    _ < ε := by linarith

/-- The adjoint `ι_Z^* : X → Z` of the inclusion `Z ⊂ X`. -/
def ιZadj : X →L[ℝ] Z := ContinuousLinearMap.adjoint ιZ

/-- `ι_Z^*(X)` is dense in `Z`: its orthogonal complement is `ker ι_Z = 0`. -/
theorem dense_range_ιZadj (u : Z) {ε : ℝ} (hε : 0 < ε) : ∃ x : X, ‖u - ιZadj x‖ < ε := by
  have hK : (LinearMap.range (ιZadj : X →ₗ[ℝ] Z))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    rw [Submodule.mem_orthogonal] at hw
    have h1 : inner ℝ (ιZadj (ιZ w)) w = 0 := hw _ (LinearMap.mem_range_self _ _)
    rw [ιZadj, ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq] at h1
    have h2 : ιZ w = 0 := by
      rw [← norm_eq_zero]
      nlinarith [norm_nonneg (ιZ w)]
    exact ιZ_injective (h2.trans (map_zero ιZ).symm)
  have htop := (Submodule.topologicalClosure_eq_top_iff (K := LinearMap.range (ιZadj : X →ₗ[ℝ] Z))).mpr hK
  have hu : u ∈ closure (LinearMap.range (ιZadj : X →ₗ[ℝ] Z) : Set Z) := by
    rw [← Submodule.topologicalClosure_coe, htop]
    exact Submodule.mem_top
  obtain ⟨v, hv, hdist⟩ := Metric.mem_closure_iff.mp hu ε hε
  obtain ⟨x, rfl⟩ := hv
  exact ⟨x, by rwa [dist_eq_norm] at hdist⟩

/-- The vectors of `Z` on which `S₀(t) → 1` as `t → 0⁺`, a submodule. -/
def goodSub (S : FreeEvolution) : Submodule ℝ Z where
  carrier := {g | Tendsto (fun t => S0ZZ S t g) (𝓝[>] 0) (𝓝 g)}
  add_mem' := by
    intro a b ha hb
    have ha' : Tendsto (fun t => S0ZZ S t a) (𝓝[>] 0) (𝓝 a) := ha
    have hb' : Tendsto (fun t => S0ZZ S t b) (𝓝[>] 0) (𝓝 b) := hb
    show Tendsto (fun t => S0ZZ S t (a + b)) (𝓝[>] 0) (𝓝 (a + b))
    simpa only [map_add] using ha'.add hb'
  zero_mem' := by
    show Tendsto (fun t => S0ZZ S t 0) (𝓝[>] 0) (𝓝 0)
    simp only [map_zero]
    exact tendsto_const_nhds
  smul_mem' := by
    intro c g hg
    have hg' : Tendsto (fun t => S0ZZ S t g) (𝓝[>] 0) (𝓝 g) := hg
    show Tendsto (fun t => S0ZZ S t (c • g)) (𝓝[>] 0) (𝓝 (c • g))
    simpa only [map_smul] using hg'.const_smul c

/-- **Strong continuity of `S₀` on `Z` at `0` from its short-time bound** (lines 292–300). -/
theorem tendsto_S0Z_of_bound {h : ℝ} {S : FreeEvolution} (hS : IsFreeEvolution h S)
    (hh : 0 ≤ h) (hb : ∃ C : ℝ, ∀ t, 0 < t → t ≤ 1 → ‖(S.S0Z t).comp ιZ‖ ≤ C) (g : Z) :
    Tendsto (fun t => S.S0Z t (ιZ g)) (𝓝[>] 0) (𝓝 g) := by
  obtain ⟨C, hC⟩ := hb
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1 one_pos le_rfl)
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖S0ZZ S t‖ ≤ C := by
    filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with t ht
    rw [S0ZZ_of_pos S ht.1]
    exact hC t ht.1 ht.2
  have hclosed : IsClosed (goodSub S : Set Z) := isClosed_setOf_tendsto_self hev
  -- `S₀(t) v ∈ G` for `t > 0`
  have hmem : ∀ t, 0 < t → ∀ v : Z, S0ZZ S t v ∈ goodSub S := by
    intro t ht v
    show Tendsto (fun s => S0ZZ S s (S0ZZ S t v)) (𝓝[>] 0) (𝓝 (S0ZZ S t v))
    have hc : ContinuousAt (fun s => S.S0Z (s + t) (ιZ v)) 0 := by
      have h1 : ContinuousAt (fun u => S.S0Z u (ιZ v)) (0 + t) :=
        (continuousOn_S0Z hS hh (ιZ v)).continuousAt (Ioi_mem_nhds (by linarith))
      exact h1.comp (f := fun s : ℝ => s + t) (continuous_add_const t).continuousAt
    have h2 : Tendsto (fun s => S.S0Z (s + t) (ιZ v)) (𝓝[>] 0) (𝓝 (S0ZZ S t v)) := by
      have h3 := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      have e : S.S0Z (0 + t) (ιZ v) = S0ZZ S t v := by
        rw [zero_add, S0ZZ_of_pos S ht, ContinuousLinearMap.comp_apply]
      rw [e] at h3
      exact h3
    refine h2.congr' (eventually_nhdsWithin_of_forall fun s hs => ?_)
    have hs' : (0 : ℝ) < s := hs
    show S.S0Z (s + t) (ιZ v) = S0ZZ S s (S0ZZ S t v)
    rw [← ContinuousLinearMap.comp_apply (S0ZZ S s), S0ZZ_comp_S0ZZ hS hh hs'.le ht.le,
      S0ZZ_of_pos S (by linarith : 0 < s + t), ContinuousLinearMap.comp_apply]
  -- `Gᗮ = 0`
  have horth : (goodSub S)ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro u hu
    rw [Submodule.mem_orthogonal] at hu
    -- the weak limit against `ι_Z^* x`
    have hkey : ∀ x : X, |inner ℝ (ιZadj x) u| ≤ ‖ιZadj x - u‖ * (C * ‖u‖) := by
      intro x
      have hlim : Tendsto (fun t => inner ℝ (ιZadj x) (S0ZZ S t u)) (𝓝[>] 0)
          (𝓝 (inner ℝ (ιZadj x) u)) := by
        have e0 : S.S0 0 (ιZ u) = ιZ u := by rw [S0_zero hS]; rfl
        have hS0 := (hS.strongly_continuous (ιZ u) 0 (mem_Ici.mpr le_rfl)).tendsto
        rw [e0] at hS0
        have hS0' := hS0.mono_left (nhdsWithin_mono (0 : ℝ) (Ioi_subset_Ici_self (a := (0 : ℝ))))
        have hin := Filter.Tendsto.inner (𝕜 := ℝ) (tendsto_const_nhds (x := x)) hS0'
        rw [ιZadj, ContinuousLinearMap.adjoint_inner_left]
        refine hin.congr' (eventually_nhdsWithin_of_forall fun t ht => ?_)
        have ht' : (0 : ℝ) < t := ht
        show inner ℝ x (S.S0 t (ιZ u)) = inner ℝ (ContinuousLinearMap.adjoint ιZ x) (S0ZZ S t u)
        rw [ContinuousLinearMap.adjoint_inner_left, ιZ_S0ZZ hS ht'.le]
      have hbd : ∀ᶠ t in 𝓝[>] (0 : ℝ),
          |inner ℝ (ιZadj x) (S0ZZ S t u)| ≤ ‖ιZadj x - u‖ * (C * ‖u‖) := by
        filter_upwards [hev, self_mem_nhdsWithin] with t ht1 ht2
        have hz : inner ℝ u (S0ZZ S t u) = 0 := by
          rw [real_inner_comm]
          exact hu _ (hmem t ht2 u)
        have hsplit : inner ℝ (ιZadj x) (S0ZZ S t u) =
            inner ℝ (ιZadj x - u) (S0ZZ S t u) := by
          rw [inner_sub_left, hz, sub_zero]
        rw [hsplit]
        refine (abs_real_inner_le_norm _ _).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right ht1 (norm_nonneg _))
      exact le_of_tendsto (hlim.abs) hbd
    -- conclude `‖u‖² ≤ ε (1 + C) ‖u‖` for every `ε`
    have hsq : ∀ ε > 0, ‖u‖ ^ 2 ≤ ε * ((1 + C) * ‖u‖) := by
      intro ε hε
      obtain ⟨x, hx⟩ := dense_range_ιZadj u hε
      have h1 : ‖u‖ ^ 2 = inner ℝ (u - ιZadj x) u + inner ℝ (ιZadj x) u := by
        rw [inner_sub_left, sub_add_cancel, real_inner_self_eq_norm_sq]
      have h2 : |inner ℝ (u - ιZadj x) u| ≤ ‖u - ιZadj x‖ * ‖u‖ := abs_real_inner_le_norm _ _
      have h3 := hkey x
      rw [norm_sub_rev] at h3
      have h4 : ‖u‖ ^ 2 ≤ ‖u - ιZadj x‖ * ((1 + C) * ‖u‖) := by
        rw [h1]
        have := abs_le.mp h2
        have := abs_le.mp h3
        nlinarith
      exact h4.trans (mul_le_mul_of_nonneg_right hx.le (by positivity))
    by_contra hne
    have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hne
    have := hsq (‖u‖ / (2 * (1 + C))) (by positivity)
    have e : ‖u‖ / (2 * (1 + C)) * ((1 + C) * ‖u‖) = ‖u‖ ^ 2 / 2 := by
      field_simp
    rw [e] at this
    nlinarith
  have htop : goodSub S = ⊤ := by
    have := (Submodule.topologicalClosure_eq_top_iff (K := goodSub S)).mpr horth
    rwa [IsClosed.submodule_topologicalClosure_eq hclosed] at this
  have hg : g ∈ goodSub S := htop ▸ Submodule.mem_top
  have hg' : Tendsto (fun t => S0ZZ S t g) (𝓝[>] 0) (𝓝 g) := hg
  refine hg'.congr' (eventually_nhdsWithin_of_forall fun t ht => ?_)
  show S0ZZ S t g = S.S0Z t (ιZ g)
  rw [S0ZZ_of_pos S ht, ContinuousLinearMap.comp_apply]

end UnforcedLeray.Loc.L03Evolution
