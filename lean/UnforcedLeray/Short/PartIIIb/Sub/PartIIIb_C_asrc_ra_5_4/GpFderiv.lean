import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# `gp54_fderiv`: the partial fibre derivative in `x` preserves `GP54` with one order lost

Source of record: `the November 2 reference manuscript` lines 4963-4981, 4978.
On the open set `U = Ioi 0 ×ˢ univ`, the fibre derivative is `fderiv f p` composed with the
inclusion `y ↦ (0, y)`, i.e. `L (fderiv ℝ f p)` for the fixed continuous linear map
`L T = T.comp (inr ℝ ℝ (ℝ × ℝ))`.  The bounds then follow from the bound on `f` one order higher
(`norm_iteratedFDeriv_fderiv`) and the composition bound on the left by `L`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gp54_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (κ ν : ℝ) (n : ℕ)
    (f : ℝ × (ℝ × ℝ) → E) (hf : GP54 κ ν (n + 1) f) :
    GP54 κ ν n (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ (fun y : ℝ × ℝ => f (p.1, y)) p.2) := by
  obtain ⟨hfC, hfB⟩ := hf
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  obtain ⟨L, hL⟩ : ∃ L : (ℝ × (ℝ × ℝ) →L[ℝ] E) →L[ℝ] (ℝ × ℝ →L[ℝ] E),
      ∀ T : ℝ × (ℝ × ℝ) →L[ℝ] E, L T = T.comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) :=
    ⟨(ContinuousLinearMap.compL ℝ (ℝ × ℝ) (ℝ × (ℝ × ℝ)) E).flip
        (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)), fun T => rfl⟩
  have hD : ContDiffOn ℝ (n : WithTop ℕ∞) (fderiv ℝ f) (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    hfC.fderiv_of_isOpen hU (by norm_cast)
  have hkey : ∀ q ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))),
      fderiv ℝ (fun y : ℝ × ℝ => f (q.1, y)) q.2 = L (fderiv ℝ f q) := by
    intro q hq
    have hdq : DifferentiableAt ℝ f (q.1, q.2) :=
      (hfC.differentiableOn (by norm_cast)).differentiableAt (hU.mem_nhds hq)
    have hd : HasFDerivAt (fun y : ℝ × ℝ => f (q.1, y))
        ((fderiv ℝ f (q.1, q.2)).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) q.2 :=
      hdq.hasFDerivAt.comp q.2 (hasFDerivAt_prodMk_right q.1 q.2)
    rw [hd.fderiv, hL]
  have hΦC : ContDiffOn ℝ (n : WithTop ℕ∞)
      (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ (fun y : ℝ × ℝ => f (p.1, y)) p.2)
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    (L.contDiff.comp_contDiffOn hD).congr (fun q hq => hkey q hq)
  refine ⟨hΦC, ?_⟩
  intro s0 s1 hs0 hs01
  obtain ⟨C, N, hC, hb⟩ := hfB s0 s1 hs0 hs01
  refine ⟨‖L‖ * C, N, mul_nonneg (norm_nonneg L) hC, ?_⟩
  intro m hm s hs x
  have hsU : (0 : ℝ) < s := lt_of_lt_of_le hs0 hs.1
  have hx : (s, x) ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := ⟨hsU, mem_univ x⟩
  have hev : (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ (fun y : ℝ × ℝ => f (p.1, y)) p.2)
      =ᶠ[𝓝 (s, x)] (fun p => L (fderiv ℝ f p)) :=
    Filter.eventually_of_mem (hU.mem_nhds hx) (fun q hq => hkey q hq)
  have heq := (Filter.EventuallyEq.iteratedFDeriv ℝ hev m).eq_of_nhds
  have hLc : ContDiffAt ℝ (n : WithTop ℕ∞) (fderiv ℝ f) (s, x) := hD.contDiffAt (hU.mem_nhds hx)
  have hmN : (m : WithTop ℕ∞) ≤ (n : WithTop ℕ∞) := by exact_mod_cast hm
  calc ‖iteratedFDeriv ℝ m (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ (fun y : ℝ × ℝ => f (p.1, y)) p.2)
        (s, x)‖
      = ‖iteratedFDeriv ℝ m (fun p => L (fderiv ℝ f p)) (s, x)‖ := by rw [heq]
    _ ≤ ‖L‖ * ‖iteratedFDeriv ℝ m (fderiv ℝ f) (s, x)‖ :=
        L.norm_iteratedFDeriv_comp_left hLc hmN
    _ = ‖L‖ * ‖iteratedFDeriv ℝ (m + 1) f (s, x)‖ := by rw [norm_iteratedFDeriv_fderiv]
    _ ≤ ‖L‖ * (C * (1 + sq2 x) ^ N * Real.exp (-(sq2 x) / (κ * ageA ν s1))) :=
        mul_le_mul_of_nonneg_left (hb (m + 1) (by omega) s hs x) (norm_nonneg L)
    _ = ‖L‖ * C * (1 + sq2 x) ^ N * Real.exp (-(sq2 x) / (κ * ageA ν s1)) := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
