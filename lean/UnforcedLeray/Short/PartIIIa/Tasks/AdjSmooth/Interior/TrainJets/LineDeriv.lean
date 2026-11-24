import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.Train.Defs

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa

/-- `PartIII-a:T21/2/7/2/1/1/2/16`: spatial lines and their derivatives are words (`TjLineDeriv`). -/
theorem tjLineDeriv : TjLineDeriv := by
  intro h hh a ha p hp
  have hs : (stDir a).1 = 0 := by
    revert ha
    fin_cases a <;> simp [stDir]
  have hℓmem : ∀ t : ℝ, p + t • stDir a ∈ tjU := by
    intro t
    refine ⟨?_, mem_univ _⟩
    have h1 : (p + t • stDir a).1 = p.1 := by simp [hs]
    show (0 : ℝ) ≤ (p + t • stDir a).1
    rw [h1]
    exact hp.1
  have hℓC : ContDiff ℝ ∞ (fun t : ℝ => p + t • stDir a) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hD : ∀ t : ℝ, HasDerivAt (fun s : ℝ => p + s • stDir a) (stDir a) t := by
    intro t
    simpa using (((hasDerivAt_id' t).smul_const (stDir a)).const_add p)
  have key : ∀ (G : ℝ × (ℝ × ℝ) → ℝ), ContDiffOn ℝ ∞ G tjU → ∀ t : ℝ,
      deriv (fun s : ℝ => G (p + s • stDir a)) t =
        fderivWithin ℝ G tjU (p + t • stDir a) (stDir a) := by
    intro G hG t
    have hd : HasFDerivWithinAt G (fderivWithin ℝ G tjU (p + t • stDir a)) tjU
        (p + t • stDir a) :=
      (hG.differentiableOn (by simp) _ (hℓmem t)).hasFDerivWithinAt
    have hmaps : MapsTo (fun s : ℝ => p + s • stDir a) univ tjU :=
      fun s _ => hℓmem s
    have hc := hd.comp_hasDerivWithinAt t (hD t).hasDerivWithinAt hmaps
    exact (hasDerivWithinAt_univ.1 hc).deriv
  have hall : ∀ j : ℕ, iteratedDeriv j (fun t : ℝ => h (p + t • stDir a)) =
      fun t : ℝ => tjW (List.replicate j a) h (p + t • stDir a) := by
    intro j
    induction j with
    | zero =>
      funext t
      simp
    | succ j ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      rw [List.replicate_succ]
      exact key _ (tjW_contDiffOn hh _) t
  refine ⟨hh.comp_contDiff hℓC (fun t => hℓmem t), fun j t => congrFun (hall j) t⟩

end UnforcedLeray.Short.IIIa
