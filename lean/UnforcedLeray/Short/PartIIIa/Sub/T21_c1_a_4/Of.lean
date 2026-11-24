import UnforcedLeray.Short.PartIIIa.Sub.T21_c1_a

/-!
# `PartIII-a:T21/c1/a/4`: `SeedBiorth` from three leaf lemmas

Source: `the November 2 reference manuscript`
lines 603-610 (functional `eq:short-seed-functional`, `ell q = 1`).  Leaves:
* `SeedBiorthExt` : extension of the two sector identities from smooth compactly supported `f`
  to smooth `f` with Gaussian bound `exp(-|y|^2/8)` (cutoff `f chi(./R)`, dominated convergence);
* `SeedSectors` : the angular sectors `+-2` of `q = h e^{2i theta}` and `conj q`;
* `SeedEllSelf` : `seedEll h h = 1` (from `l q = 1` and `l f = seedEll h f` on `X_G`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ComplexConjugate ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **Leaf A** (lines 603-610).  Under the hypotheses of `SeedBiorth`, the two sector identities
of `lamP` (known for smooth compactly supported `f`) hold for every smooth `f` with Gaussian bound
`|f| <= C exp(-|y|^2/8)`.  Proof sketch: `f_R = f * chi(./R)`; `lamP = O(|y|^-2)` and the Gaussian
bound give dominated convergence on the left; on the right `seedEll h (angularSector f_R 2)`
converges because `h/k * r` is integrable against bounded profiles (`SeedFunctional`, Gaussian
bound on `h`) and `angularSector f_R 2 -> angularSector f 2` boundedly. -/
def SeedBiorthExt : Prop :=
  PartI.SeedFunctional →
  ∀ (lam : ℂ) (h : ℝ → ℂ) (hh : MemLp h 2 B0010.xGMeasure) (ℓ : B0010.XG →L[ℂ] ℂ),
    PartI.IsSeedXG lam (hh.toLp h) ℓ → ContDiff ℝ ∞ (PartI.seedPlanar h) →
    (∃ C : ℝ, ∀ y : ℝ × ℝ,
        ‖PartI.seedPlanar h (planeToC y)‖ ≤ C * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) →
    ∀ lamP : Fin 2 → ℝ × ℝ → ℂ, (∀ i, Continuous (lamP i)) →
      (∃ C : ℝ, ∀ i y, ‖lamP i y‖ ≤ C * (1 + |y.1| + |y.2|)⁻¹ ^ 2) →
      (∀ f : ℂ → ℂ, ContDiff ℝ ∞ f → HasCompactSupport f →
        ∫ y, lamP 0 y * f (planeToC y) =
            PartI.seedEll h (Planar.NUE.Polar.angularSector f 2) ∧
        ∫ y, lamP 1 y * f (planeToC y) =
            conj (PartI.seedEll h (fun r => conj (Planar.NUE.Polar.angularSector f (-2) r)))) →
      ∀ f : ℂ → ℂ, ContDiff ℝ ∞ f →
        (∃ C : ℝ, ∀ y : ℝ × ℝ, ‖f (planeToC y)‖ ≤ C * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) →
        ∫ y, lamP 0 y * f (planeToC y) =
            PartI.seedEll h (Planar.NUE.Polar.angularSector f 2) ∧
        ∫ y, lamP 1 y * f (planeToC y) =
            conj (PartI.seedEll h (fun r => conj (Planar.NUE.Polar.angularSector f (-2) r)))

/-- **Leaf B** (polar coordinates; `q = h(r) e^{2 i theta}`, lines 593-601).  For `r > 0`:
`q` has sector `2` equal to `h r` and sector `-2` zero; `conj q` has sector `2` zero and
sector `-2` equal to `conj (h r)`. -/
def SeedSectors : Prop :=
  ∀ (h : ℝ → ℂ) (r : ℝ), 0 < r →
    Planar.NUE.Polar.angularSector (PartI.seedPlanar h) 2 r = h r ∧
    Planar.NUE.Polar.angularSector (PartI.seedPlanar h) (-2) r = 0 ∧
    Planar.NUE.Polar.angularSector (fun y => conj (PartI.seedPlanar h y)) 2 r = 0 ∧
    Planar.NUE.Polar.angularSector (fun y => conj (PartI.seedPlanar h y)) (-2) r = conj (h r)

/-- **Leaf C** (lines 603-610): `seedEll h h = l(q) = 1`, using `l f = seedEll h f` on `X_G`
(`SeedFunctional`) and `ell_q` in `IsSeedXG` (the `X_G` element is a.e. equal to `h`). -/
def SeedEllSelf : Prop :=
  PartI.SeedFunctional →
  ∀ (lam : ℂ) (h : ℝ → ℂ) (hh : MemLp h 2 B0010.xGMeasure) (ℓ : B0010.XG →L[ℂ] ℂ),
    PartI.IsSeedXG lam (hh.toLp h) ℓ → PartI.seedEll h h = 1

theorem seedEll_congr (h f g : ℝ → ℂ) (hfg : ∀ r : ℝ, 0 < r → f r = g r) :
    PartI.seedEll h f = PartI.seedEll h g := by
  unfold PartI.seedEll
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro r hr
  simp only [hfg r hr]

theorem seedBiorth_of (hE : SeedBiorthExt) (hS : SeedSectors) (hC : SeedEllSelf) :
    SeedBiorth := by
  intro hSF lam h hh ℓ hIS hsm hG lamP hc hd hcl i j
  have hext := hE hSF lam h hh ℓ hIS hsm hG lamP hc hd hcl
  have hself := hC hSF lam h hh ℓ hIS
  have hq : Continuous (PartI.seedPlanar h) := hsm.continuous
  have hq0 : ContDiff ℝ ∞ (fun y => conj (PartI.seedPlanar h y)) :=
    (Complex.conjCLE.contDiff).comp hsm
  have hGq : ∃ C : ℝ, ∀ y : ℝ × ℝ,
      ‖(fun y => conj (PartI.seedPlanar h y)) (planeToC y)‖ ≤
        C * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by
    obtain ⟨C, hC⟩ := hG
    exact ⟨C, fun y => by simpa using hC y⟩
  have e0 := hext _ hsm hG
  have e1 := hext _ hq0 hGq
  have zero : PartI.seedEll h (fun _ => (0 : ℂ)) = 0 := by
    simp [PartI.seedEll]
  have s0 : PartI.seedEll h (Planar.NUE.Polar.angularSector (PartI.seedPlanar h) 2) = 1 := by
    rw [seedEll_congr h _ h (fun r hr => (hS h r hr).1)]; exact hself
  have s1 : PartI.seedEll h (fun r => conj
      (Planar.NUE.Polar.angularSector (PartI.seedPlanar h) (-2) r)) = 0 := by
    rw [seedEll_congr h _ (fun _ => 0) (fun r hr => by simp [(hS h r hr).2.1])]; exact zero
  have s2 : PartI.seedEll h (Planar.NUE.Polar.angularSector
      (fun y => conj (PartI.seedPlanar h y)) 2) = 0 := by
    rw [seedEll_congr h _ (fun _ => 0) (fun r hr => (hS h r hr).2.2.1)]; exact zero
  have s3 : PartI.seedEll h (fun r => conj (Planar.NUE.Polar.angularSector
      (fun y => conj (PartI.seedPlanar h y)) (-2) r)) = 1 := by
    rw [seedEll_congr h _ h (fun r hr => by simp [(hS h r hr).2.2.2])]; exact hself
  fin_cases i <;> fin_cases j <;> simp [e0.1, e0.2, e1.1, e1.2, s0, s1, s2, s3]
