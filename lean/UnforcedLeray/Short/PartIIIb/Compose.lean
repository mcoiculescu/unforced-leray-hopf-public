import UnforcedLeray.Short.PartIIIb.Return
import UnforcedLeray.Short.PartIIIb.MixedReturn

/-!
# Composition of Part III-b (lines 5785-5985): from the module results to the energy mode

Layer A (this file, algebra; every step is the source's own computation):

* `exactNormalForm`  : `D(I+H)T = D_N T - M R F_{LT} + M v_Q(T)` (`closure:exact-normal-form`,
  lines 5810-5818), from the Ward identity (`WardStressNormal`, 4300-4303) and the physical
  affine identity (`PhysAffineIdentity`, 5001-5008).
* `nearEq_of_return`  : a solution of the return system (`closure:exact-return-system`, lines
  5820-5833) satisfies `D_N T = M R F_{LT} - M v_Q(T)`.
* `energyField_of_return` : lines 5975-5985.  If `x = LT ≠ 0`, then `T' = (I+H)T ≠ 0`, `D T' = 0`,
  `b = -S T'` satisfies `T' = M b` and `b ≠ 0` (no injectivity of `M` is used).
* `blockSolution_iff` : the return system `V = 𝒫x + y, x = LV, y = 𝒬V` is the block system
  `x = (L𝒫)x + Ly, y = (𝒬𝒫)x + 𝒬y` of `closure:mixed-return` with
  `K = L𝒫, A = L, B = 𝒬𝒫, C = 𝒬` (lines 5826-5833).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set

namespace UnforcedLeray.Short.PartIIIb

namespace ReturnOps

variable {Vel Str Src Aff Gam : Type}
  [NormedAddCommGroup Vel] [NormedSpace ℝ Vel]
  [NormedAddCommGroup Str] [NormedSpace ℝ Str]
  [NormedAddCommGroup Src] [NormedSpace ℝ Src]
  [NormedAddCommGroup Aff] [NormedSpace ℝ Aff] [CompleteSpace Aff]
  [NormedAddCommGroup Gam] [NormedSpace ℝ Gam] [CompleteSpace Gam]
  (o : ReturnOps Vel Str Src Aff Gam)

/-- `closure:exact-normal-form` (lines 5810-5818). -/
theorem exactNormalForm (hW : o.WardStressNormal) (hA : o.PhysAffineIdentity) (T : Str) :
    o.D (T + o.Hop T) =
      o.DN T - o.M (o.R (o.FA (o.Lj T))) + o.M (o.vQ T) := by
  have h1 := hW T
  have h2 := hA (o.Lj T)
  have hH : o.Hop T = o.M (o.Yf T + o.hf T) - o.M (o.hA (o.Lj T)) := by
    simp [ReturnOps.Hop, map_sub, map_add]
  have hD : ∀ U : Str, o.D U = U + o.M (o.S U) := by
    intro U; simp [ReturnOps.D]
  have hDN : ∀ U : Str, o.DN U = U + o.M (o.SN U) := by
    intro U; simp [ReturnOps.DN]
  rw [map_add, hH, map_sub, h1, h2, hD T, hDN T]
  simp only [ReturnOps.vQ, ReturnOps.Sfar, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, map_add, map_sub]
  abel

/-- A solution of the return system solves the near equation with the affine force of its jet
(lines 5826-5833). -/
theorem nearEq_of_return (hN : o.IsNearInverse) (hG : o.IsGraphLift)
    (V : Gam) (x : Aff) (y : Gam) (hV : V = o.P x + y) (hx : x = o.Lg V) (hy : y = o.Q V) :
    o.DN (o.Tc V) = o.M (o.R (o.FA (o.Lj (o.Tc V)))) - o.M (o.vQ (o.Tc V)) := by
  obtain ⟨-, hL, hP, hQ⟩ := hG
  have hxT : x = o.Lj (o.Tc V) := by rw [hx, hL V]
  have hPx : o.Tc (o.P x) = o.DNinv (o.M (o.R (o.FA x))) := by
    have := congrArg Prod.fst (hP x)
    simpa [ReturnOps.Jlift] using this
  have hQV : o.Tc (o.Q V) = -(o.DNinv (o.M (o.vQ (o.Tc V)))) := by
    have := congrArg Prod.fst (hQ V)
    simpa [ReturnOps.Jlift] using this
  have hT : o.Tc V = o.DNinv (o.M (o.R (o.FA x))) - o.DNinv (o.M (o.vQ (o.Tc V))) := by
    conv_lhs => rw [hV, map_add, hPx, hy, hQV]
    abel
  have := congrArg o.DN hT
  rw [map_sub, hN.2, hN.2] at this
  rw [this, hxT]

/-- Lines 5975-5985: the nonzero energy field. -/
theorem energyField_of_return (hN : o.IsNearInverse) (hG : o.IsGraphLift)
    (hW : o.WardStressNormal) (hA : o.PhysAffineIdentity) (hH : o.HNilpotent)
    (V : Gam) (x : Aff) (y : Gam) (hV : V = o.P x + y) (hx : x = o.Lg V) (hy : y = o.Q V)
    (hx0 : x ≠ 0) :
    ∃ (T' : Str) (b : Vel), T' ≠ 0 ∧ o.D T' = 0 ∧ b = -(o.S T') ∧ T' = o.M b ∧ b ≠ 0 := by
  have hnear := o.nearEq_of_return hN hG V x y hV hx hy
  have hNF := o.exactNormalForm hW hA (o.Tc V)
  have hT0 : o.Tc V ≠ 0 := by
    intro h
    apply hx0
    have : x = o.Lj (o.Tc V) := by rw [hx, hG.2.1 V]
    rw [this, h, map_zero]
  have hker : o.D (o.Tc V + o.Hop (o.Tc V)) = 0 := by
    rw [hNF, hnear]; abel
  have hT'0 : o.Tc V + o.Hop (o.Tc V) ≠ 0 := by
    intro h
    apply hT0
    have h2 : o.Hop (o.Tc V + o.Hop (o.Tc V)) = o.Hop (o.Tc V) := by
      rw [map_add, hH]; simp
    rw [h, map_zero] at h2
    have h3 : o.Hop (o.Tc V) = 0 := h2.symm
    rw [h3, add_zero] at h
    exact h
  refine ⟨o.Tc V + o.Hop (o.Tc V), -(o.S (o.Tc V + o.Hop (o.Tc V))), hT'0, hker, rfl, ?_, ?_⟩
  · have hD : o.D (o.Tc V + o.Hop (o.Tc V)) =
        (o.Tc V + o.Hop (o.Tc V)) + o.M (o.S (o.Tc V + o.Hop (o.Tc V))) := by
      simp [ReturnOps.D]
    rw [hD] at hker
    rw [map_neg]
    exact eq_neg_of_add_eq_zero_left hker
  · intro hb
    apply hT'0
    have hD : o.D (o.Tc V + o.Hop (o.Tc V)) =
        (o.Tc V + o.Hop (o.Tc V)) + o.M (o.S (o.Tc V + o.Hop (o.Tc V))) := by
      simp [ReturnOps.D]
    rw [hD] at hker
    have : o.M (-(o.S (o.Tc V + o.Hop (o.Tc V)))) = 0 := by rw [hb, map_zero]
    rw [map_neg] at this
    have := neg_eq_zero.mp this
    rw [this, add_zero] at hker
    exact hker

/-- The return system is the block system of `closure:mixed-return`. -/
theorem blockSolution_of_return (x : Aff) (y : Gam) (V : Gam)
    (hV : V = o.P x + y) (hx : x = o.Lg V) (hy : y = o.Q V) :
    x = (o.Lg ∘L o.P) x + o.Lg y ∧ y = (o.Q ∘L o.P) x + o.Q y := by
  subst hV
  refine ⟨?_, ?_⟩
  · conv_lhs => rw [hx]
    simp
  · conv_lhs => rw [hy]
    simp

/-- Conversely a solution `(x, y)` of the block system gives a solution of the return system with
`V = 𝒫x + y`. -/
theorem return_of_blockSolution (x : Aff) (y : Gam)
    (h1 : x = (o.Lg ∘L o.P) x + o.Lg y) (h2 : y = (o.Q ∘L o.P) x + o.Q y) :
    x = o.Lg (o.P x + y) ∧ y = o.Q (o.P x + y) := by
  refine ⟨?_, ?_⟩
  · rw [map_add]; exact h1
  · rw [map_add]; exact h2

end ReturnOps

end UnforcedLeray.Short.PartIIIb

namespace UnforcedLeray.Short.PartIIIb

/-! ## Layer B: the closing argument (lines 5926-5985)

For the phase-locked sequence `ν_n` the source applies `closure:mixed-return` to the block
system with `E_n = 𝒜`, `X_n = 𝓔_{ν_n}`, `K = L𝒫`, `A = L`, `B = 𝒬𝒫`, `C = 𝒬`, `a = a_μ`,
`ℓ = Λ_{μ,ν}` and `R_n = L𝒫 - a_μ Λ_{μ,ν}` (lines 5888-5909), at `μ = μ_n(z)`. -/

theorem energy_modes_of_blocks (hMR : MixedReturnLemma)
    {Vel Str Src Aff Gam : ℕ → Type}
    [∀ n, NormedAddCommGroup (Vel n)] [∀ n, NormedSpace ℝ (Vel n)]
    [∀ n, NormedAddCommGroup (Str n)] [∀ n, NormedSpace ℝ (Str n)]
    [∀ n, NormedAddCommGroup (Src n)] [∀ n, NormedSpace ℝ (Src n)]
    [∀ n, NormedAddCommGroup (Aff n)] [∀ n, NormedSpace ℝ (Aff n)] [∀ n, CompleteSpace (Aff n)]
    [∀ n, NormedAddCommGroup (Gam n)] [∀ n, NormedSpace ℝ (Gam n)] [∀ n, CompleteSpace (Gam n)]
    (ops : ∀ n, ℝ → ReturnOps (Vel n) (Str n) (Src n) (Aff n) (Gam n))
    (hN : ∀ n, ∀ z ∈ Icc (-1 : ℝ) 1, (ops n z).IsNearInverse)
    (hG : ∀ n, ∀ z ∈ Icc (-1 : ℝ) 1, (ops n z).IsGraphLift)
    (hW : ∀ n, ∀ z ∈ Icc (-1 : ℝ) 1, (ops n z).WardStressNormal)
    (hA : ∀ n, ∀ z ∈ Icc (-1 : ℝ) 1, (ops n z).PhysAffineIdentity)
    (hH : ∀ n, ∀ z ∈ Icc (-1 : ℝ) 1, (ops n z).HNilpotent)
    (Rr : ∀ n, ℝ → Aff n →L[ℝ] Aff n) (M : ℝ)
    (hK : ∀ n, ∀ z ∈ Icc (-1 : ℝ) 1,
      (ops n z).Lg ∘L (ops n z).P = (ops n z).Lam.smulRight (ops n z).aMu + Rr n z)
    (cP : ∀ n, ContinuousOn (fun z => (ops n z).P) (Icc (-1) 1))
    (cLg : ∀ n, ContinuousOn (fun z => (ops n z).Lg) (Icc (-1) 1))
    (cQ : ∀ n, ContinuousOn (fun z => (ops n z).Q) (Icc (-1) 1))
    (ca : ∀ n, ContinuousOn (fun z => (ops n z).aMu) (Icc (-1) 1))
    (cl : ∀ n, ContinuousOn (fun z => (ops n z).Lam) (Icc (-1) 1))
    (cR : ∀ n, ContinuousOn (Rr n) (Icc (-1) 1))
    (hM : ∀ n, ∀ z ∈ Icc (-1 : ℝ) 1, ‖(ops n z).aMu‖ * ‖(ops n z).Lam‖ ≤ M)
    (hC : ∀ n, (⨆ z : Icc (-1 : ℝ) 1, ‖(ops n z).Q‖) < 1)
    (hsmall : Tendsto (fun n => (⨆ z : Icc (-1 : ℝ) 1, ‖Rr n z‖) +
        (⨆ z : Icc (-1 : ℝ) 1, ‖(ops n z).Lg‖ * ‖(ops n z).Q ∘L (ops n z).P‖) /
          (1 - ⨆ z : Icc (-1 : ℝ) 1, ‖(ops n z).Q‖)) atTop (𝓝 0))
    (hgain : TendstoUniformlyOn (fun n z => (ops n z).Lam (ops n z).aMu)
      (fun z => Real.exp (-z)) atTop (Icc (-1 : ℝ) 1)) :
    ∃ z : ℕ → ℝ, Tendsto z atTop (𝓝 0) ∧ ∀ᶠ n in atTop, z n ∈ Ioo (-1 : ℝ) 1 ∧
      ∃ (T' : Str n) (b : Vel n), T' ≠ 0 ∧ (ops n (z n)).D T' = 0 ∧
        b = -((ops n (z n)).S T') ∧ T' = (ops n (z n)).M b ∧ b ≠ 0 := by
  obtain ⟨z, hz0, hz⟩ := hMR Aff Gam (fun n z => (ops n z).Lg ∘L (ops n z).P)
    (fun n z => (ops n z).Lg) (fun n z => (ops n z).Q ∘L (ops n z).P) (fun n z => (ops n z).Q)
    (fun n z => (ops n z).aMu) (fun n z => (ops n z).Lam) Rr M
    (fun n => (cLg n).clm_comp (cP n)) cLg (fun n => (cQ n).clm_comp (cP n)) cQ ca cl cR hK hM
    hC hsmall hgain
  refine ⟨z, hz0, ?_⟩
  filter_upwards [hz] with n hn
  obtain ⟨hzn, x, hx0, y, h1, h2⟩ := hn
  have hzI : z n ∈ Icc (-1 : ℝ) 1 := Ioo_subset_Icc_self hzn
  obtain ⟨hxV, hyV⟩ := (ops n (z n)).return_of_blockSolution x y h1 h2
  refine ⟨hzn, ?_⟩
  exact (ops n (z n)).energyField_of_return (hN n _ hzI) (hG n _ hzI) (hW n _ hzI) (hA n _ hzI)
    (hH n _ hzI) ((ops n (z n)).P x + y) x y rfl hxV hyV hx0

end UnforcedLeray.Short.PartIIIb
