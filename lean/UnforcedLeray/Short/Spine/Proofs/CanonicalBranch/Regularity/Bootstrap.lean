import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.Bootstrap.Calc

/-!
# Spine: `StrongBootstrap`, time regularity (task `Spine:SP-CAN/4`, step 3; blueprint B0124)

Target (`Short/Spine/Sub/SP_CAN4.lean`): `GreenAll → ∀ V, IsXGjContinuous V → IsStrongOnPos V →
IsSmoothAllXGj V`. Source: `the November 2 reference manuscript` line 1086 and
1141-1145; old manuscript `paper/main.tex` 1879-1888.

Proof. Write `U_j(θ) = (I - D)^{j/2} V(θ)` (the witnesses of `IsXGjContinuous`) and
`G(θ) = -(L₀ V(θ) + θ⁻¹ D V(θ))` with `D V = V - (I - D)V` (`(I - D)V = U_2`). For each `j`
there is a bounded `M_j` on `XG` with `(I - D)^{j/2} L₀ f = M_j (I - D)^{j/2} f` (`BootOps.exists_M`),
so `(I - D)^{j/2} G = W_j := -(M_j U_j + θ⁻¹ (U_j - U_{j+2}))`. Integrating the strong equation and
applying `(I - D)^{j/2}` (`BootCalc.integral_IDpow`) gives `U_j' = W_j` on `(0, ∞)`. Induction on the
order `k`, for all `j` at once, then gives `U_j ∈ C^k(0, ∞; XG)` for every `k`
(`W_j` is `C^k` by the induction hypothesis at `j` and `j + 2`).

No `sorry`, `admit`, `axiom` or `native_decide`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology InnerProductSpace ComplexConjugate

namespace UnforcedLeray.Short.Spine

open UnforcedLeray.B0010 UnforcedLeray.B0123 UnforcedLeray.B0094
open UnforcedLeray.Short.Spine.BootOps UnforcedLeray.Short.Spine.BootCalc

theorem IDpow_index (s t : ℝ) (h : s = t) (x : XG) (hx : x ∈ (IDpow s).domain)
    (hy : x ∈ (IDpow t).domain) : IDpow s ⟨x, hx⟩ = IDpow t ⟨x, hy⟩ := by
  subst h
  rfl

theorem mem_domain_index (s t : ℝ) (h : s = t) (x : XG) (hx : x ∈ (IDpow s).domain) :
    x ∈ (IDpow t).domain := by
  subst h
  exact hx

/-- The vector field `G(θ) = -(L₀ V(θ) + θ⁻¹ (V(θ) - U₂(θ)))` of the strong equation. -/
def fieldG (V U2 : ℝ → XG) (t : ℝ) : XG :=
  -(B0012.L0 (V t) + ((t : ℂ)⁻¹) • (V t - U2 t))

/-- The vector field `W_j(θ) = -(M_j U_j(θ) + θ⁻¹ (U_j(θ) - U_{j+2}(θ)))` of `(I - D)^{j/2} G`. -/
def fieldW (M : XG →L[ℂ] XG) (U Uj2 : ℝ → XG) (t : ℝ) : XG :=
  -(M (U t) + ((t : ℂ)⁻¹) • (U t - Uj2 t))

theorem strongBootstrap : UnforcedLeray.Short.Spine.StrongBootstrap := by
  intro hE V hC hS
  unfold IsSmoothAllXGj
  unfold IsXGjContinuous at hC
  choose U hU hUc using hC
  unfold IsStrongOnPos at hS
  choose hD hQ using hS
  choose Mj hMj using fun j => exists_M j (hE j)
  -- `D V = V - (I - D) V` and `(I - D)^1 V = U_2`
  have hDsub : ∀ t : ℝ, ∀ ht : 0 < t, B0094.D ⟨V t, hD t ht⟩ = V t - U 2 t := by
    intro t ht
    obtain ⟨h2, e2⟩ := hU 2 t ht
    have h1 : V t ∈ (IDpow 1).domain := by
      rw [IDpow_one_domain]
      exact hD t ht
    have e1 : IDpow 1 ⟨V t, h1⟩ = U 2 t :=
      (IDpow_index 1 (((2 : ℕ) : ℝ) / 2) (by norm_num) (V t) h1 h2).trans e2
    have hD1 : IDpow 1 ⟨V t, h1⟩ = V t - B0094.D ⟨V t, hD t ht⟩ :=
      IDpow_one_apply ⟨V t, h1⟩ (hD t ht)
    rw [← e1, hD1]
    abel
  have hVdiff : ∀ t : ℝ, ∀ ht : 0 < t, HasDerivAt V (fieldG V (U 2) t) t := by
    intro t ht
    have h := hQ t ht
    rw [hDsub t ht] at h
    exact h
  have hVc : ContinuousOn V (Ioi 0) := fun t ht => (hVdiff t ht).continuousAt.continuousWithinAt
  have hGc : ContinuousOn (fieldG V (U 2)) (Ioi 0) := by
    have hinv : ContinuousOn (fun t : ℝ => ((t : ℂ))⁻¹) (Ioi 0) :=
      Complex.continuous_ofReal.continuousOn.inv₀
        (fun t ht => Complex.ofReal_ne_zero.2 (ne_of_gt ht))
    have h1 : ContinuousOn (fun t => B0012.L0 (V t)) (Ioi 0) :=
      B0012.L0.continuous.comp_continuousOn hVc
    have h2 : ContinuousOn (fun t : ℝ => ((t : ℂ))⁻¹ • (V t - U 2 t)) (Ioi 0) :=
      hinv.smul (hVc.sub (hUc 2))
    exact (h1.add h2).neg
  -- `(I - D)^{j/2} G = W_j`, with `G` in the graph domain of `(I - D)^{j/2}`
  have hGWj : ∀ j : ℕ, ∀ t : ℝ, 0 < t →
      ∃ ht : fieldG V (U 2) t ∈ (IDpow ((j : ℝ) / 2)).domain,
        IDpow ((j : ℝ) / 2) ⟨fieldG V (U 2) t, ht⟩ = fieldW (Mj j) (U j) (U (j + 2)) t := by
    intro j t ht
    obtain ⟨hxj, exj⟩ := hU j t ht
    obtain ⟨hxj2, exj2⟩ := hU (j + 2) t ht
    obtain ⟨h2, e2⟩ := hU 2 t ht
    have h1 : V t ∈ (IDpow 1).domain := by
      rw [IDpow_one_domain]
      exact hD t ht
    have eU2 : IDpow 1 ⟨V t, h1⟩ = U 2 t :=
      (IDpow_index 1 (((2 : ℕ) : ℝ) / 2) (by norm_num) (V t) h1 h2).trans e2
    have hxj' : V t ∈ (IDpow ((j : ℝ) / 2 + 1)).domain :=
      mem_domain_index _ _ (by push_cast; ring) (V t) hxj2
    have h₁ : IDpow 1 ⟨V t, h1⟩ ∈ (IDpow ((j : ℝ) / 2)).domain :=
      (IDpow_mem_domain_iff ((j : ℝ) / 2) 1 ⟨V t, h1⟩).2 hxj'
    have hU2mem : U 2 t ∈ (IDpow ((j : ℝ) / 2)).domain := by
      rw [← eU2]
      exact h₁
    have hcomp : IDpow ((j : ℝ) / 2) ⟨U 2 t, hU2mem⟩ = U (j + 2) t :=
      (IDpow_congr_val hU2mem h₁ eU2.symm).trans
        ((IDpow_comp_apply ((j : ℝ) / 2) 1 ⟨V t, h1⟩ h₁ hxj').trans
          ((IDpow_index _ _ (by push_cast; ring) (V t) hxj' hxj2).trans exj2))
    obtain ⟨hL0m, eL0⟩ := hMj j (V t) hxj
    have eL0' : IDpow ((j : ℝ) / 2) ⟨B0012.L0 (V t), hL0m⟩ = Mj j (U j t) := by
      rw [eL0, exj]
    have hsub : V t - U 2 t ∈ (IDpow ((j : ℝ) / 2)).domain := Submodule.sub_mem _ hxj hU2mem
    have hG : fieldG V (U 2) t ∈ (IDpow ((j : ℝ) / 2)).domain :=
      Submodule.neg_mem _ (Submodule.add_mem _ hL0m (Submodule.smul_mem _ _ hsub))
    refine ⟨hG, ?_⟩
    have e : (⟨fieldG V (U 2) t, hG⟩ : (IDpow ((j : ℝ) / 2)).domain)
        = -(⟨B0012.L0 (V t), hL0m⟩ + ((t : ℂ)⁻¹) •
            (⟨V t - U 2 t, hsub⟩ : (IDpow ((j : ℝ) / 2)).domain)) := rfl
    have e2' : IDpow ((j : ℝ) / 2) ⟨V t - U 2 t, hsub⟩
        = IDpow ((j : ℝ) / 2) ⟨V t, hxj⟩ - IDpow ((j : ℝ) / 2) ⟨U 2 t, hU2mem⟩ :=
      LinearPMap.map_sub (IDpow ((j : ℝ) / 2)) ⟨V t, hxj⟩ ⟨U 2 t, hU2mem⟩
    rw [exj, hcomp] at e2'
    rw [e, LinearPMap.map_neg, LinearPMap.map_add, LinearPMap.map_smul, eL0', e2']
    rfl
  -- Induction on the order `k`, for all `j` at once.
  have hind : ∀ k : ℕ, ∀ j : ℕ, ContDiffOn ℝ k (U j) (Ioi 0) := by
    intro k
    induction k with
    | zero =>
      intro j
      rw [Nat.cast_zero, contDiffOn_zero]
      exact hUc j
    | succ k ih =>
      intro j
      have hWsm : ContDiffOn ℝ k (fieldW (Mj j) (U j) (U (j + 2))) (Ioi 0) := by
        have h1 : ContDiffOn ℝ k (fun t => Mj j (U j t)) (Ioi 0) :=
          ((Mj j).restrictScalars ℝ).contDiff.comp_contDiffOn (ih j)
        have h2 : ContDiffOn ℝ k (fun t : ℝ => ((t : ℂ))⁻¹) (Ioi 0) :=
          (Complex.ofRealCLM.contDiff.contDiffOn).inv
            (fun t ht => Complex.ofReal_ne_zero.2 (ne_of_gt ht))
        have h3 : ContDiffOn ℝ k (fun t => U j t - U (j + 2) t) (Ioi 0) :=
          (ih j).sub (ih (j + 2))
        exact (h1.add (h2.smul h3)).neg
      have hderiv : ∀ t : ℝ, ∀ ht : 0 < t,
          HasDerivAt (U j) (fieldW (Mj j) (U j) (U (j + 2)) t) t :=
        fun t ht => hasDerivAt_IDpow ((j : ℝ) / 2) V (fieldG V (U 2))
          (fieldW (Mj j) (U j) (U (j + 2))) (U j) t ht
          (fun s hs => hVdiff s hs) hGc hWsm.continuousOn (hGWj j) (hU j)
      rw [Nat.cast_succ, contDiffOn_succ_iff_derivWithin isOpen_Ioi.uniqueDiffOn]
      refine ⟨fun t ht => (hderiv t ht).differentiableAt.differentiableWithinAt,
        fun h => absurd h (by simp), ?_⟩
      refine hWsm.congr (fun t ht => ?_)
      exact (hderiv t ht).hasDerivWithinAt.derivWithin (isOpen_Ioi.uniqueDiffOn t ht)
  intro j
  exact ⟨U j, fun t ht => hU j t ht, contDiffOn_infty.2 (fun k => hind k j)⟩

end UnforcedLeray.Short.Spine
