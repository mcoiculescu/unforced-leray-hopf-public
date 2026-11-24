import UnforcedLeray.Short.PartI.Sub.T04.APriori
import UnforcedLeray.Short.PartI.Tasks.TrainVorticityBounds.Linf

/-!
# Part I, task `PartI:T04/7`: the `L^∞` bound of the vorticity on `[0,T]`

Source of record: `the November 2 reference manuscript`, lines 286-288.

Finite-interval form of `train_vorticity_linf` (`Linf.lean`): the barrier comparison `linf_core`
gives the bound for `r ∈ [0,T)`; the endpoint `r = T` follows by continuity of `ω` on `[0,T]`
(`ContinuousWithinAt.closure_le`).  Then `ε → 0` (`linf_limit`) and `σ = ±1`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)

/-- **`L^∞` bound of the vorticity on `[0,T]`** (`APMaxPrinciple`, lines 286-288). -/
theorem apMaxPrinciple : APMaxPrinciple := by
  intro ν c T v p hν hc1 hcls M hM s hs z
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
  have hT : (0:ℝ) < T := hcls.pos
  have cl := hcls.classical
  obtain ⟨hcont, hC2, ⟨Mw, hMw⟩, hper⟩ :=
    curlRegularity c T v hc0 hT cl.smooth_v cl.periodic_v hcls.bounded
  obtain ⟨β0, hβ0⟩ := vfm_sup_bound hcls.bounded
  have hop : ∀ r ∈ Ioo (0:ℝ) T, ∀ w : Plane,
      vorticityOp ν v (fun t u => Cyl.curl (v t) u) r w = 0 :=
    fun r hr w => localVorticityEquation ν c T v p hν hc1 hT cl r hr w
  have hb : ∀ r ∈ Icc (0:ℝ) T, ∀ w : Plane, ‖v r w‖ ≤ |β0| :=
    fun r hr w => (hβ0 r hr w).trans (le_abs_self β0)
  have hM0 : ∀ w : Plane, |Cyl.curl (v 0) w| ≤ M := hM
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = |β0| + ν + 1 := ⟨_, rfl⟩
  have hK : |β0| + ν < K := by rw [hKdef]; linarith
  -- the comparison on `[0,T)`
  have hin : ∀ σ : ℝ, |σ| ≤ 1 → ∀ ε : ℝ, 0 < ε → ∀ r ∈ Ico (0:ℝ) T, ∀ w : Plane,
      σ * Cyl.curl (v r) w ≤ M + coshBarrier ε K 1 r w :=
    fun σ hσ ε hε =>
      linf_core parabolicMinPrinciple sechSupersolution ν c T |β0| M Mw K v
        (fun t u => Cyl.curl (v t) u) hν hc0 hT (abs_nonneg _) hK hb hcont hC2 hper hMw
        hop hM0 σ hσ ε hε
  -- the comparison on `[0,T]`, endpoint `T` by continuity in time
  have hkey : ∀ σ : ℝ, |σ| ≤ 1 → ∀ ε : ℝ, 0 < ε → ∀ r ∈ Icc (0:ℝ) T,
      σ * Cyl.curl (v r) z ≤ M + coshBarrier ε K 1 r z := by
    intro σ hσ ε hε r hr
    rcases eq_or_lt_of_le hr.2 with hrT | hrT
    · rw [hrT]
      have hcz : ContinuousOn (fun t => Cyl.curl (v t) z) (Icc 0 T) :=
        ContinuousOn.comp hcont (continuous_id.prodMk continuous_const).continuousOn
          (fun t ht => ⟨ht, mem_univ z⟩)
      have hcb : Continuous (fun t => coshBarrier ε K 1 t z) := by
        unfold coshBarrier
        fun_prop
      have hTcl : T ∈ closure (Ico (0:ℝ) T) := by
        rw [closure_Ico hT.ne]
        exact ⟨hT.le, le_rfl⟩
      have hf : ContinuousWithinAt (fun t => σ * Cyl.curl (v t) z) (Ico (0:ℝ) T) T :=
        (((continuousOn_const (c := σ)).mul hcz) T ⟨hT.le, le_rfl⟩).mono Ico_subset_Icc_self
      have hg : ContinuousWithinAt (fun t => M + coshBarrier ε K 1 t z) (Ico (0:ℝ) T) T :=
        (continuous_const.add hcb).continuousWithinAt
      exact ContinuousWithinAt.closure_le hTcl hf hg
        (fun y hy => hin σ hσ ε hε y ⟨hy.1, hy.2⟩ z)
    · exact hin σ hσ ε hε r ⟨hr.1, hrT⟩ z
  have hlim : ∀ σ : ℝ, |σ| ≤ 1 → σ * Cyl.curl (v s) z ≤ M := by
    intro σ hσ
    refine linf_limit _ M (Real.exp (K * s) * Real.cosh (1 * z.2)) ?_ ?_
    · exact mul_nonneg (Real.exp_pos _).le (Real.cosh_pos _).le
    · intro ε hε
      have e : coshBarrier ε K 1 s z = ε * (Real.exp (K * s) * Real.cosh (1 * z.2)) := by
        unfold coshBarrier
        ring
      rw [← e]
      exact hkey σ hσ ε hε s hs
  have h1 := hlim 1 (by norm_num)
  have h2 := hlim (-1) (by norm_num)
  rw [abs_le]
  constructor <;> linarith

end UnforcedLeray.Short.PartI
