import UnforcedLeray.Short.PartIIIb.Concrete.SourceL
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.XmtSolenoidal
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.N0

/-!
# Part III-b, task `PartIII-b:C/srcL/11` (`sourceLTraceFree`)

`𝓛T` is trace free: for `s > 0` the trace of `𝓛T(s)` is the divergence
`∑ᵢ ∂ᵢ X^mt_i` of the receiver field at the point `(R/√s, 0, 0)`, which vanishes by
solenoidality (`xmtSolenoidal`).  The finiteness of `N₀` for the thin representative of `T` is
supplied by `sourceLN0`.  Source 4797-4800 of `the November 2 reference manuscript`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `𝓛T` is trace free (source 4797-4800). -/
theorem sourceLTraceFree (c mZ ρb γ ν ε μ : ℝ) (χo χy : ℝ → ℝ) :
    SourceLTraceFree c mZ ρb γ ν ε μ χo χy := by
  intro h hmZ hγ T s hs
  obtain ⟨C, k, hC⟩ := sourceLN0 mZ γ hmZ hγ
  have hfin : OldThinFinite c ν (thinRep T) :=
    (hC c ν ρb h.c_pos h.nu_pos h.nu_le T).1
  have hL : ∀ i j : Fin 3, LjFun c mZ ρb γ ν ε μ χo χy T s i j =
      fderiv ℝ (Xmt c ν ε μ χo χy (thinRep T)) ![ε⁻¹ / Real.sqrt s, 0, 0] (Pi.single j 1) i := by
    intro i j
    simp [LjFun, Lpt, hs]
  have hdiv := xmtSolenoidal c ν ε μ χo χy h (thinRep T) hfin ![ε⁻¹ / Real.sqrt s, 0, 0]
  rw [Fin.sum_univ_three] at hdiv
  rw [hL 0 0, hL 1 1, hL 2 2]
  exact hdiv

end UnforcedLeray.Short.PartIIIb.Concrete
