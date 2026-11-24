import UnforcedLeray.Loc.L05EssentialRadius.Rellich

/-!
# Step L5 `EssentialRadiusStep`

`paper/main.tex` lines 331–347 (Section `sec:st18-329`), blueprint units B0714, B0715; the step
proposition is `UnforcedLeray.Blueprint.EssentialRadiusStep`
(`Blueprint/Localization/Linear.lean`, line 199).

The proof follows the manuscript:

1. (B0714 (a), line 332) multiplication by `U_* ∈ C₀` is compact `X → L²`: `C0MulCompact`
   (`L05EssentialRadius/Kernel.lean`), proved in `L05EssentialRadius/Rellich.lean`
   (`c0MulCompact`) by a small uniform tail of `U_*` and local compactness on balls, the latter
   obtained from heat smoothing (`‖f - e^{tΔ}f‖₂ ≤ C√t ‖f‖_{H¹}` and pointwise convergence of
   `e^{tΔ}fₙ` along a weakly null sequence) instead of a Rellich–Kondrachov theorem;
2. (B0714 (b), (c), lines 333–336) `-𝔓 div(U_* ⊗ f + f ⊗ U_*)` is an `H⁻¹` functional of size
   `‖U_* f‖₂` (`L05EssentialRadius/HMinusOne.lean`), so `S₀(r)𝓑_*` maps weakly null sequences
   to null sequences (`duhamelKernelNull_of`, `L05EssentialRadius/Kernel.lean`);
3. (B0714 (d), lines 336–340) the Duhamel formula, dominated convergence and the weakly-null
   criterion for compactness (`Infra/WeaklyNullCompact.lean`) give that `E(τ,s) - S₀(τ-s)` is
   compact (`L05EssentialRadius/Abstract.lean`, adapted from `Infra/CompactDuhamel`);
4. (B0715, lines 340–343) `𝓜ⁿ = E(n𝒯,0) = S₀(n𝒯) + compact` and `‖S₀(n𝒯)‖ ≤ C e^{-n𝒯/4}`.

The Calkin-algebra statement `r_ess(𝓜) ≤ e^{-𝒯/4}` of `loc:eq:essential-radius` is the
blueprint's real, Calkin-free `CalkinBound` (`Blueprint/Localization/Linear.lean`).

* `essentialRadiusStep_of` : `C0MulCompact → EssentialRadiusStep`;
* `essentialRadiusStep` : `EssentialRadiusStep`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Loc.L05

open UnforcedLeray.Blueprint

/-- **Step L5** (`paper/main.tex` lines 331–347, units B0714, B0715), conditional on the
multiplication compactness `C0MulCompact` (B0714 (a), line 332). -/
theorem essentialRadiusStep_of (hR : C0MulCompact) : EssentialRadiusStep := by
  intro D hD c S ev hc hS hev
  have hh : 0 < D.h := hD.background.h_pos
  have hP : 0 < D.period := hD.background.period_pos
  exact calkinBound_of_duhamelKernelNull hh.le hP.le hS hc hev
    (duhamelKernelNull_of hR hh hS hc)

/-- **Step L5** `EssentialRadiusStep` (`paper/main.tex` lines 331–347,
`loc:eq:essential-radius`; units B0714, B0715): for every unstable background package and every
coefficient map, free evolution and evolution family satisfying steps L1–L3, the monodromy
`𝓜 = E(𝒯,0)` has `‖𝓜ⁿ - Kₙ‖ ≤ C e^{-n𝒯/4}` with `Kₙ` compact. -/
theorem essentialRadiusStep : EssentialRadiusStep :=
  essentialRadiusStep_of c0MulCompact

#print axioms essentialRadiusStep

end UnforcedLeray.Loc.L05
